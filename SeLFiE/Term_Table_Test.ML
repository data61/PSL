(*  Title:      PSL/LiFtEr/src/Term_Table_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to SeLFiE.
The overall work-flow is:
Proof.state            ==== pst_to_lifter_pst ================================================>               (* in Term_Table *)
   (Proof.state & term     ==== pst_n_trm_to_one_term ========================================>               (* in Term_Table *)
       (term                      ==== trm_to_trm_w_prnt =======================================>             (* in Unique_Node *)
        trm_w_prnt                ==== trm_w_prnt_to_utrm_w_prnt ===============================>             (* in Unique_Node *)
        utrm_w_prnt               ==== utrm_w_prnt_to_futrm_w_prnt =============================>             (* in Unique_Node *)
        futrm_w_prnt              ==== futrm_w_prnt_to_futrm_w_prnt_n_inner_path =====================>       (* in Unique_Node *)
        futrm_w_prnt_n_inner_path ==== futrm_w_prnt_n_inner_path_to_unodes ===========================>       (* in Unique_Node *)
        unodes                    ==== pst_n_trm_to_path_to_unode_table ===================================>  (* in Inner_Path_To_Unode and Outer_Path_To_Unode *)
        unode_table)
    )
*)

(*&&& and \<Longrightarrow> associate to the right*)
val _ = @{assert} (@{term "A &&& B &&& C"} = @{term "A &&& (B &&& C) "});
val _ = @{assert} (@{term "A \<Longrightarrow> B \<Longrightarrow> C"} = @{term "A \<Longrightarrow> (B \<Longrightarrow> C)"});

local

(** test utrm_w_prnt_to_utrm_w_prnt **)
structure TT = Term_Table;

(*FIXME: TODO: take a context as a parameter.*)
fun trm_to_inner_path_to_unode_table (trm:term) =
  let
    (*In this test we did not remove Trueprop.*)
    val trm_w_prnt                = UN.trm_to_trm_w_prnt @{context} trm;
    val utrm_w_prnt               = UN.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val futrm_w_prnt              = UN.utrm_w_prnt_to_futrm_w_prnt utrm_w_prnt;
    val futrm_w_prnt_n_inner_path = UN.futrm_w_prnt_to_futrm_w_prnt_n_inner_path futrm_w_prnt;
    val unique_nodes              = UN.futrm_w_prnt_n_inner_path_n_ctxt_to_unodes futrm_w_prnt_n_inner_path @{context};
    val term_table                = TT.unodes_to_unode_table unique_nodes: TT.inner_path_to_unode_table;
  in
    term_table: TT.inner_path_to_unode_table
  end;

val imp_xyz       = @{term "(x &&& w &&& ww) \<Longrightarrow> f (\<lambda>x. x w) z2 \<Longrightarrow> z1 &&& z2 &&& (z3 z4 z5 z6)"}: term;
val imp_xyz_table = trm_to_inner_path_to_unode_table imp_xyz: TT.inner_path_to_unode_table;

fun unode_wo_inner_path_table_n_inner_path_to_print (table, inner_path) =
  let
    val node       = Inner_Path_Table.lookup table inner_path: UN.unode option;
    val some_print = Option.map #print node      : string option;
  in
    some_print
  end;

in


val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, []     )     |> the) = ("x &&& w &&& ww \<Longrightarrow> f (\<lambda>x. x w) z2 \<Longrightarrow> z1 &&& z2 &&& z3 z4 z5 z6"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [0]    )     |> the) = ("Pure.imp"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [1]    )     |> the) = ("x &&& w &&& ww"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [1,3]  )     |> the) = ("ww"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3]    )     |> the) = ("z1 &&& z2 &&& z3 z4 z5 z6"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3,0]  )     |> the) = ("Pure.conjunction"))
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3,1])       |> the) = ("z1"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3,3])       |> the) = ("z3 z4 z5 z6"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3,3,0])     |> the) = ("HOL.Trueprop"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3,3,1])     |> the) = ("z3 z4 z5 z6"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3,3,1,0])   |> the) = ("z3"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3,3,1,1])   |> the) = ("z4"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [3,3,1,2])   |> the) = ("z5"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2])         |> the) = ("f (\<lambda>x. x w) z2"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2,0])       |> the) = ("HOL.Trueprop"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2,1]  )     |> the) = ("f (\<lambda>x. x w) z2"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2,1,0])     |> the) = ("f"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2,1,1])     |> the) = ("\<lambda>x. x w"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2,1,1,0])   |> the) = ("x w"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2,1,1,0,0]) |> the) = ("x"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2,1,1,0,1]) |> the) = ("w"));
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (imp_xyz_table, [2,1,2])     |> the) = ("z2"));

val _ = @{assert} ((Inner_Path_Table.lookup imp_xyz_table [2,1,2] |> the |> #print) = "z2");
val _ = @{assert} ((Inner_Path_Table.lookup imp_xyz_table [3,2]   |> the |> #print) = "z2");
val _ = @{assert} ((Inner_Path_Table.lookup imp_xyz_table [3,2,1] |> the |> #print) = "z2");
(*Should I care about the types? In this case, maybe we should ignore unode032.*)

val unode011    = Inner_Path_Table.lookup imp_xyz_table [1,1]      ;
val unode0111   = Inner_Path_Table.lookup imp_xyz_table [1,1,1]    ;
val unode021100 = Inner_Path_Table.lookup imp_xyz_table [2,1,1,0,0];

val _ = @{assert} ((Inner_Path_Table.lookup imp_xyz_table [1,1]      |> the |> #print) = "x");
val _ = @{assert} ((Inner_Path_Table.lookup imp_xyz_table [1,1,1]    |> the |> #print) = "x");
val _ = @{assert} ((Inner_Path_Table.lookup imp_xyz_table [2,1,1,0,0]|> the |> #print) = "x");

val a_imp_xyz       = @{term "(\<lambda>f. f w)"}: term;
val a_imp_xyz_table = trm_to_inner_path_to_unode_table a_imp_xyz: TT.inner_path_to_unode_table;

val sw  as (Abs trip)      = @{term "(\<lambda>w. s w)"}: term;
val ws_table = trm_to_inner_path_to_unode_table sw: TT.inner_path_to_unode_table;

val wfw       = @{term "(\<lambda>w. f w)"}: term;
val wfw_table = trm_to_inner_path_to_unode_table wfw: TT.inner_path_to_unode_table;

val all_x_f_x       = @{term "(\<And>x. f x)"}: term;
val all_x_f_x_table = trm_to_inner_path_to_unode_table all_x_f_x: TT.inner_path_to_unode_table;

val all_f_f_x       = @{term "(\<And>f. f x)"}: term;
val all_f_f_x_table = trm_to_inner_path_to_unode_table all_f_f_x: TT.inner_path_to_unode_table;

val sample_list = @{term "[1,2,3]"};
val sample_list_table = trm_to_inner_path_to_unode_table sample_list;
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (sample_list_table, [ ])|> the) = "[1, 2, 3]");
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (sample_list_table, [0])|> the) = "List.list.Cons");
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (sample_list_table, [1])|> the) = "Groups.one_class.one");
val _ = @{assert}((unode_wo_inner_path_table_n_inner_path_to_print (sample_list_table, [2])|> the) = "[2, 3]");

val var_of_type_list = @{term "xs::int list"};
val var_of_type_list_table = trm_to_inner_path_to_unode_table var_of_type_list;

end;