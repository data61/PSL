(*  Title:      PSL/Term_Table_Test.ML
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
val xy = @{term "x \<Longrightarrow> y"};

structure TT = Term_Table;

fun trm_to_unique_nodes (trm:term) =
  let
    val trm_w_prnt          = TT.trm_to_trm_w_prnt @{context} trm;
    val utrm_w_prnt         = TT.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val futrm_w_prnt        = TT.utrm_w_prnt_to_futrm_w_prnt utrm_w_prnt;
    val futrm_w_prnt_n_path = TT.futrm_w_prnt_to_futrm_w_prnt_n_path futrm_w_prnt;
    val unique_nodes        = TT.futrm_w_prnt_n_path_to_unique_nodes futrm_w_prnt_n_path;
    val term_table          = unique_nodes_to_trm_table unique_nodes;
  in
    term_table
  end;

val imp_xyz       = @{term "(x &&& w &&& ww) \<Longrightarrow> f x z \<Longrightarrow> z1 &&& z2 &&& z3"}: term;
val imp_xyz_table = trm_to_unique_nodes imp_xyz: TT.unique_node_wo_path One_Term.table;

fun unode_wo_path_table_n_path_to_print (table: TT.unique_node_wo_path One_Term.table, path) =
  let
    val node       = One_Term.lookup table path: TT.unique_node_wo_path option;
    val some_print = Option.map #print node    : TT.print option;
  in
    some_print
  end;

in
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0]      ) |> the) = (Unique_Node.Print "x &&& w &&& ww \<Longrightarrow> f x z \<Longrightarrow> z1 &&& z2 &&& z3"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,1]    ) |> the) = (Unique_Node.Print "x &&& w &&& ww"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,1,3]  ) |> the) = (Unique_Node.Print "ww"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,3]    ) |> the) = (Unique_Node.Print "z1 &&& z2 &&& z3"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1]  ) |> the) = (Unique_Node.Print "f x z"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,1]) |> the) = (Unique_Node.Print "x"));
val _ = @{assert}((unode_wo_path_table_n_path_to_print (imp_xyz_table, [0,2,1,2]) |> the) = (Unique_Node.Print "z"));

end;