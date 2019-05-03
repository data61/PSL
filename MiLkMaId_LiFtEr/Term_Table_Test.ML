(*  Title:      PSL/MiLkMaId_LiFtEr/Term_Table_Test.ML
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

(*&&& and \<Longrightarrow> associate to the right*)
val _ = @{assert} (@{term "A &&& B &&& C"} = @{term "A &&& (B &&& C) "});
val _ = @{assert} (@{term "A \<Longrightarrow> B \<Longrightarrow> C"} = @{term "A \<Longrightarrow> (B \<Longrightarrow> C)"});

local

(** test utrm_w_prnt_to_utrm_w_prnt **)
structure UN = Unique_Node;
structure TT = Term_Table;

fun trm_to_unode_table (trm:term) =
  let
    val trm_w_prnt          = UN.trm_to_trm_w_prnt @{context} trm;
    val utrm_w_prnt         = UN.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val futrm_w_prnt        = UN.utrm_w_prnt_to_futrm_w_prnt utrm_w_prnt;
    val futrm_w_prnt_n_path = UN.futrm_w_prnt_to_futrm_w_prnt_n_path futrm_w_prnt;
    val unique_nodes        = UN.futrm_w_prnt_n_path_to_unique_nodes futrm_w_prnt_n_path;
    val term_table          = TT.unique_nodes_to_unode_table unique_nodes: TT.unode_table;
  in
    term_table: TT.unode_table
  end;

val imp_xyz       = @{term "(x &&& w &&& ww) \<Longrightarrow> f (\<lambda>x. x w) z2 \<Longrightarrow> z1 &&& z2 &&& (z3 z4 z5 z6)"}: term;
val imp_xyz_table = trm_to_unode_table imp_xyz: TT.unode_table;

fun unode_wo_path_table_n_path_to_print (table, path) =
  let
    val node       = One_Term.lookup table path  : UN.unique_node option;
    val some_print = Option.map #print node: UN.print option;
  in
    some_print
  end;

in

val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0]      )     |> the) = (LiFtEr_Util.Print "x &&& w &&& ww \<Longrightarrow> f (\<lambda>x. x w) z2 \<Longrightarrow> z1 &&& z2 &&& z3 z4 z5 z6"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,0]    )     |> the) = (LiFtEr_Util.Print "(\<Longrightarrow>)"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,1]    )     |> the) = (LiFtEr_Util.Print "x &&& w &&& ww"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,1,3]  )     |> the) = (LiFtEr_Util.Print "ww"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3]    )     |> the) = (LiFtEr_Util.Print "z1 &&& z2 &&& z3 z4 z5 z6"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3,0]  )     |> the) = (LiFtEr_Util.Print "(&&&)"))
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3,1])       |> the) = (LiFtEr_Util.Print "z1"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3,3])       |> the) = (LiFtEr_Util.Print "z3 z4 z5 z6"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3,3,0])     |> the) = (LiFtEr_Util.Print "Trueprop"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3,3,1])     |> the) = (LiFtEr_Util.Print "z3 z4 z5 z6"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3,3,1,0])   |> the) = (LiFtEr_Util.Print "z3"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3,3,1,1])   |> the) = (LiFtEr_Util.Print "z4"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3,3,1,2])   |> the) = (LiFtEr_Util.Print "z5"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1]  )     |> the) = (LiFtEr_Util.Print "f (\<lambda>x. x w) z2"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,0])     |> the) = (LiFtEr_Util.Print "f"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,1])     |> the) = (LiFtEr_Util.Print "\<lambda>x. x w"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,1,0])   |> the) = (LiFtEr_Util.Print "x w"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,1,0,0]) |> the) = (LiFtEr_Util.Print "x"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,1,0,1]) |> the) = (LiFtEr_Util.Print "w"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,2])     |> the) = (LiFtEr_Util.Print "z2"));

val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,2,1,2] |> the |> #print) = (LiFtEr_Util.Print "z2"));
val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,3,2]   |> the |> #print) = (LiFtEr_Util.Print "z2"));
val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,3,2,1] |> the |> #print) = (LiFtEr_Util.Print "z2"));
(*Should I care about the types? In this case, maybe we should ignore unode032.*)

val unode011    = One_Term.lookup imp_xyz_table [0,1,1]      ;
val unode0111   = One_Term.lookup imp_xyz_table [0,1,1,1]    ;
val unode021100 = One_Term.lookup imp_xyz_table [0,2,1,1,0,0];

val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,1,1]      |> the |> #print) = (LiFtEr_Util.Print "x"));
val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,1,1,1]    |> the |> #print) = (LiFtEr_Util.Print "x"));
val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,2,1,1,0,0]|> the |> #print) = (LiFtEr_Util.Print "x"));

val a_imp_xyz       = @{term "(\<lambda>f. f w)"}: term;
val a_imp_xyz_table = trm_to_unode_table a_imp_xyz: TT.unode_table;

val sw  as (Abs trip)      = @{term "(\<lambda>w. s w)"}: term;
val ws_table = trm_to_unode_table sw: TT.unode_table;

val wfw       = @{term "(\<lambda>w. f w)"}: term;
val wfw_table = trm_to_unode_table wfw: TT.unode_table;

val all_x_f_x       = @{term "(\<And>x. f x)"}: term;
val all_x_f_x_table = trm_to_unode_table all_x_f_x: TT.unode_table;

val all_f_f_x       = @{term "(\<And>f. f x)"}: term;
val all_f_f_x_table = trm_to_unode_table all_f_f_x: TT.unode_table;

val sample_list = @{term "[1,2,3]"};
val sample_list_table = trm_to_unode_table sample_list;
val _ = @{assert}((unode_wo_path_table_n_path_to_print (sample_list_table, [0  ])|> the) = (LiFtEr_Util.Print "[1, 2, 3]"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (sample_list_table, [0,0])|> the) = (LiFtEr_Util.Print "(#)"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (sample_list_table, [0,1])|> the) = (LiFtEr_Util.Print "1"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (sample_list_table, [0,2])|> the) = (LiFtEr_Util.Print "[2, 3]"));

val var_of_type_list = @{term "xs::int list"};
val var_of_type_list_table = trm_to_unode_table var_of_type_list;

end;