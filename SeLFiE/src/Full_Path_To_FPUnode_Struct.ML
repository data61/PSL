(*  Title:      PSL/SeLFeE/src/Full_Path_To_FPUnode_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The overall work-flow is:
 Proof.state           ==== pst_to_location_n_term_list =========================================>            (* in Full_Path_To_Unode_Struct *)
 Proof.state * (location * term) list ==== pst_n_location_n_term_list_to_location_n_path_to_unode_table ====> (* in Full_Path_To_Unode_Struct *)
    (term * Proof.state  ==== trm_to_trm_w_prnt =======================================>                      (* in Unique_Node *)
     trm_w_prnt          ==== trm_w_prnt_to_utrm_w_prnt ===============================>                      (* in Unique_Node *)
     utrm_w_prnt         ==== utrm_w_prnt_to_futrm_w_prnt =============================>                      (* in Unique_Node *)
     futrm_w_prnt        ==== futrm_w_prnt_to_futrm_w_prnt_n_path =====================>                      (* in Unique_Node *)
     futrm_w_prnt_n_path ==== futrm_w_prnt_n_path_to_unodes ===========================>                      (* in Unique_Node *)
     unodes              ==== unodes_to_unode_table ===================================>                      (* in Term_Table  *)
     path_to_unode_table)
(location * path_to_unode_table) list ==== location_n_path_to_unode_table_list_to_location_n_full_path_to_fpunode_table_list =====> (* in Full_Path_To_Unode_Struct *)
    ((location * path_to_unode_table) ==== location_n_path_to_unode_table_to_full_path_to_fpunode_table ==========================> (* in Full_Path_To_Unode_Struct *)
      full_path_to_fpunode_table)
(location * full_path_to_fpunode_table) list ==== map snd =======================================================================> (* in Full_Path_To_Unode_Struct *)
 full_path_to_fpunode_table) list            ==== merge_full_path_to_fpunode_tables =============================================> (* in Full_Path_To_Unode_Struct *)
 full_path_to_fpunode_table
*)
structure Full_Path_To_Fpunode: FULL_PATH_TO_FPUNODE =
struct

type fpunode =
  {unode     : UN.unode,
   location  : location};

type full_path_to_fpunode_table = fpunode Full_Path_Table.table;

fun pst_to_location_n_term_list (pst:Proof.state) =
  let
    val chained_facts_trms = Isabelle_Utils.pstate_to_usings pst |> map Thm.prop_of: terms;
    val subgoals_trms      = Isabelle_Utils.pst_to_subgs pst                       : terms;
    datatype loc = Subg | Chained;
    fun add_loc (Subg:loc)    (i:int, trm:term) = (Subgoal i,      trm)
      | add_loc (Chained:loc) (i:int, trm:term) = (Chained_Fact i, trm);
    val chained_facts_pairs = Utils.add_index chained_facts_trms |> map (add_loc Chained): (location * term) list;
    val subgoals_pairs      = Utils.add_index subgoals_trms      |> map (add_loc Subg   ): (location * term) list;
    val result              = chained_facts_pairs @ subgoals_pairs;
  in
    result: (location * term) list
  end;

fun pst_n_location_n_term_list_to_location_n_path_to_unode_table (pst:Proof.state) (outer_pairs:(location * term) list) =
  let
    val ctxt = Proof.context_of pst: Proof.context;
    fun pst_n_location_n_term_list_to_location_n_path_to_unode_table'  [] acc = acc
      | pst_n_location_n_term_list_to_location_n_path_to_unode_table' ((loc, trm)::pairs:(location * term) list) acc =
        let
          val trm_w_prnt          = UN.trm_to_trm_w_prnt ctxt trm;
          val utrm_w_prnt         = UN.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
          val futrm_w_prnt        = UN.utrm_w_prnt_to_futrm_w_prnt utrm_w_prnt;
          val futrm_w_prnt_n_path = UN.futrm_w_prnt_to_futrm_w_prnt_n_path futrm_w_prnt;
          val unodes              = UN.futrm_w_prnt_n_path_to_unodes futrm_w_prnt_n_path;
          val path_to_unode_table = Term_Table.unodes_to_unode_table unodes: Term_Table.path_to_unode_table;
        in
          pst_n_location_n_term_list_to_location_n_path_to_unode_table' pairs ((loc, path_to_unode_table)::acc)
        end;
  in
    pst_n_location_n_term_list_to_location_n_path_to_unode_table' outer_pairs []
   : (location * Term_Table.path_to_unode_table) list
  end;

fun location_n_path_to_unode_table_to_full_path_to_fp_unode_table (loc:location, path_to_unode_table:Term_Table.path_to_unode_table) =
  let
    val path_unode_pairs                   = Path_Table.dest path_to_unode_table: (UN.path * UN.unode) list;
    fun unode_to_fp_unode (unode:UN.unode) = {unode = unode, location = loc}:fpunode;
    fun path_unode_pairs_to_full_path_fp_node_pair (path:UN.path, unode:UN.unode) =
        ((loc, path), unode_to_fp_unode unode): (full_path * fpunode);
    val full_path_fp_node_pairs     = map path_unode_pairs_to_full_path_fp_node_pair path_unode_pairs: (full_path * fpunode) list;
    val full_path_to_fp_unode_table = Full_Path_Table.make full_path_fp_node_pairs                   : full_path_to_fpunode_table;
  in
    full_path_to_fp_unode_table: full_path_to_fpunode_table
  end;

fun location_n_path_to_unode_table_list_to_location_n_full_path_to_fp_unode_table_list' [] _ = []
  | location_n_path_to_unode_table_list_to_location_n_full_path_to_fp_unode_table_list' ((loc, path_to_unode_table)::pairs) acc =
    let
      val full_path_to_fp_unode_table = location_n_path_to_unode_table_to_full_path_to_fp_unode_table (loc, path_to_unode_table):full_path_to_fpunode_table;
    in
      location_n_path_to_unode_table_list_to_location_n_full_path_to_fp_unode_table_list' pairs ((loc, full_path_to_fp_unode_table)::acc)
    end;

fun location_n_path_to_unode_table_list_to_location_n_full_path_to_fp_unode_table_list (pairs:(location * Term_Table.path_to_unode_table) list) =
    location_n_path_to_unode_table_list_to_location_n_full_path_to_fp_unode_table_list' pairs [];

fun eq_fp_unodes (fpn1:fpunode, fpn2:fpunode) =
  let
    val loc1             = #location fpn1;
    val loc2             = #location fpn2;
    val same_loc         = are_same_location loc1 loc2: bool;
    val fp_unode_to_path = #path o #unode: fpunode -> Unique_Node.path;
    val same_path        = apply2 fp_unode_to_path (fpn1, fpn2) |> uncurry Unique_Node.are_same_path: bool; 
  in
    same_loc andalso same_path
  end;

fun merge_full_path_to_fp_unode_tables (tables:full_path_to_fpunode_table list): full_path_to_fpunode_table =
  fold  (Full_Path_Table.merge eq_fp_unodes |> curry) tables Full_Path_Table.empty;

fun pst_to_full_path_to_fpunode_table (pst:Proof.state) : full_path_to_fpunode_table =
  let
    val loc_n_trm_list = pst_to_location_n_term_list pst: (location * term) list;
    val loc_path_to_unode_table_list           = pst_n_location_n_term_list_to_location_n_path_to_unode_table pst loc_n_trm_list                                : (location * Term_Table.path_to_unode_table) list;
    val loc_n_full_path_to_fpunode_table_list  = location_n_path_to_unode_table_list_to_location_n_full_path_to_fp_unode_table_list loc_path_to_unode_table_list: (location * full_path_to_fpunode_table) list;
    val full_path_to_fpunode_table_list        = map snd loc_n_full_path_to_fpunode_table_list                                                                  : full_path_to_fpunode_table list;
    val full_path_to_fpunode_table             = merge_full_path_to_fp_unode_tables full_path_to_fpunode_table_list                                             : full_path_to_fpunode_table;
  in
    full_path_to_fpunode_table: full_path_to_fpunode_table
  end;

fun fpunode_to_unode {unode,...} = unode;

fun fpunode_to_node {unode,...} = #node unode: UN.node;

fun fpunode2_to_unode2 (fpun1, fpun2) = apply2 fpunode_to_unode (fpun1, fpun2): (UN.unode * UN.unode);

fun fpunode2_to_node2 (fpun1, fpun2) = apply2 fpunode_to_node (fpun1, fpun2): (UN.node * UN.node);

end;