(*  Title:      PSL/MiLkMaId_LiFtEr/Term_Table_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
  term                === trm_to_trm_w_prnt ==========================> (* Unique_Node *)
  trm_w_prnt          === trm_w_prnt_to_utrm_w_prnt ==================> (* Unique_Node *)
  utrm_w_prnt         === utrm_w_prnt_to_futrm_w_prnt ================> (* Unique_Node *)
  futrm_w_prnt        === futrm_w_prnt_to_futrm_w_prnt_n_path ========> (* Unique_Node *)
  futrm_w_prnt_n_path === futrm_w_prnt_n_path_to_unique_nodes ========> (* Unique_Node *)
  unique_nodes        === unique_nodes_to_unique_nodes_w_auxiliary ===> (* Term_Table  *)
  nodes_w_auxiliary
*)

(*&&& and \<Longrightarrow> associate to the right*)
val _ = @{assert} (@{term "A &&& B &&& C"} = @{term "A &&& (B &&& C) "});
val _ = @{assert} (@{term "A \<Longrightarrow> B \<Longrightarrow> C"} = @{term "A \<Longrightarrow> (B \<Longrightarrow> C)"});

local

(** test utrm_w_prnt_to_utrm_w_prnt **)
structure UN = Unique_Node;
structure TT = Term_Table;

fun trm_to_unique_nodes (trm:term) =
  let
    val trm_w_prnt          = UN.trm_to_trm_w_prnt @{context} trm;
    val utrm_w_prnt         = UN.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val futrm_w_prnt        = UN.utrm_w_prnt_to_futrm_w_prnt utrm_w_prnt;
    val futrm_w_prnt_n_path = UN.futrm_w_prnt_to_futrm_w_prnt_n_path futrm_w_prnt;
    val unique_nodes        = UN.futrm_w_prnt_n_path_to_unique_nodes futrm_w_prnt_n_path;
    val term_table          = TT.unique_nodes_to_trm_table unique_nodes;
  in
    term_table
  end;

val imp_xyz       = @{term "(x &&& w &&& ww) \<Longrightarrow> f (\<lambda>x. x w) z2 \<Longrightarrow> z1 &&& z2 &&& z3"}: term;
val imp_xyz_table = trm_to_unique_nodes imp_xyz: TT.unode_table;

fun unode_wo_path_table_n_path_to_print (table, path) =
  let
    val node       = One_Term.lookup table path  : UN.unique_node_wo_path option;
    val some_print = Option.map #print node: UN.print option;
  in
    some_print
  end;

in

val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0]      ) |> the) = (Unique_Node.Print "x &&& w &&& ww \<Longrightarrow> f (\<lambda>x. x w) z2 \<Longrightarrow> z1 &&& z2 &&& z3"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,1]    ) |> the) = (Unique_Node.Print "x &&& w &&& ww"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,1,3]  ) |> the) = (Unique_Node.Print "ww"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3]    ) |> the) = (Unique_Node.Print "z1 &&& z2 &&& z3"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1]  ) |> the) = (Unique_Node.Print "f (\<lambda>x. x w) z2"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,1]) |> the) = (Unique_Node.Print "\<lambda>x. x w"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,1,0]) |> the) = (Unique_Node.Print "x w"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,2]) |> the) = (Unique_Node.Print "z2"));

val _ = @{assert}
((TT.unode_table_to_unode_n_print_table imp_xyz_table
  |> #print_table
  |> (fn tbl => Print_Table.lookup tbl (UN.Print "z2"))) =
 SOME [[0, 2, 1, 2], [0, 3, 2], [0, 3, 2, 1]]);

val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,2,1,2] |> the |> #print) = (UN.Print "z2"));
val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,3,2]   |> the |> #print) = (UN.Print "z2"));
val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,3,2,1] |> the |> #print) = (UN.Print "z2"));
(*Should I care about the types? In this case, maybe we should ignore unode032.*)

val x =
((TT.unode_table_to_unode_n_print_table imp_xyz_table
  |> #print_table
  |> (fn tbl => Print_Table.lookup tbl (UN.Print "x"))));

val unode011    = One_Term.lookup imp_xyz_table [0,1,1]      ;
val unode0111   = One_Term.lookup imp_xyz_table [0,1,1,1]    ;
val unode021100 = One_Term.lookup imp_xyz_table [0,2,1,1,0,0];

val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,1,1]      |> the |> #print) = (UN.Print "x"));;
val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,1,1,1]    |> the |> #print) = (UN.Print "x"));;
val _ = @{assert} ((One_Term.lookup imp_xyz_table [0,2,1,1,0,0]|> the |> #print) = (UN.Print "x"));;

val a_imp_xyz       = @{term "(\<lambda>f. f w)"}: term;
val a_imp_xyz_table = trm_to_unique_nodes a_imp_xyz: TT.unode_table;

val sw  as (Abs trip)      = @{term "(\<lambda>w. s w)"}: term;
val ws_table = trm_to_unique_nodes sw: TT.unode_table;

val wfw       = @{term "(\<lambda>w. f w)"}: term;
val wfw_table = trm_to_unique_nodes wfw: TT.unode_table;

val all_x_f_x       = @{term "(\<And>x. f x)"}: term;
val all_x_f_x_table = trm_to_unique_nodes all_x_f_x: TT.unode_table;

val all_f_f_x       = @{term "(\<And>f. f x)"}: term;
val all_f_f_x_table = trm_to_unique_nodes all_f_f_x: TT.unode_table;

end;