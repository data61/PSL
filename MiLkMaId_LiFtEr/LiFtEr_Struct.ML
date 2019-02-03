(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The syntax and interpreter of LiFtEr, Logical Feature Extractor for MiLkMaId.
*)
structure LiFtEr: LIFTER =
struct

open LiFtEr_Util;

structure UN = Unique_Node;
structure LU = LiFtEr_Util;
structure TT = Term_Table;

type abs_pstate_w_aux = TT.abs_pstate_w_aux;

datatype numb        = Nth         of int;
datatype subtrm      = Sub_Trm     of int;
datatype rule        = Rule        of int;
datatype subtrm_occ  = Sub_Trm_Occ of int;

datatype pattern     = Pttrn (*TODO*)
infix And Or Imply;
datatype assrt       =
(*quantifiers*)
  All_Ind                 of subtrm * assrt
| All_Arb                 of subtrm * assrt
| All_Sub_Trm             of subtrm * assrt
| All_Rule                of rule   * assrt
| All_Numb                of numb   * assrt
| Some_Ind                of subtrm * assrt
| Some_Arb                of subtrm * assrt
| Some_Sub_Trm            of subtrm * assrt
| Some_Rule               of rule   * assrt
| Some_Numb               of numb   * assrt (*n must be smaller than or equal to the argument number of the variable/constant that has the maximum argument number.*)
(*quantifiers for occurrences*)
| All_Sub_Trm_Occ         of subtrm_occ * subtrm * assrt
| Some_Sub_Trm_Occ        of subtrm_occ * subtrm * assrt
(*combinators*)
| And                     of assrt * assrt
| Or                      of assrt * assrt
| Not                     of assrt
| Imply                   of assrt * assrt
(*atomic about proof goal*)
| Are_Same_Numb           of numb       * numb
| Are_Same_Str            of subtrm_occ * subtrm_occ (*subtrm*)
| Is_In_Trm_Loc           of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 location-wise*)
| Is_In_Trm_Str           of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_In_Trm_Sem           of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 string-wise but modulo lambda-abstraction*)
| Is_Typ                  of subtrm_occ * hol_typ
| Is_In_Chained           of subtrm_occ
| Is_In_Fst_Subg          of subtrm_occ
| Is_In_Prems             of subtrm_occ
| Is_In_Cnclsn            of subtrm_occ
| Is_Atom                 of subtrm_occ
| Is_Cnst                 of subtrm_occ
| Is_Const_Of_Name        of subtrm_occ * string
| Is_Var                  of subtrm_occ
| Is_Free                 of subtrm_occ
| Is_Bound                of subtrm_occ (*corresponds to Bound in term*)
| Is_Lambda               of subtrm_occ (*lambda abstraction corresponding to Abs in Term*)
| Is_App                  of subtrm_occ (*function application corresponding to $ in Term*)
| Not_Fully_App           of subtrm_occ (*If subtrm is function application that is not fully applied returns true, otherwise returns false.*)
| Is_Less_Than            of numb       * numb (* nth_1 < nth_2 *)
| Is_Nth_Arg_Of           of subtrm_occ * numb * subtrm_occ
| Is_Nth_Ind              of subtrm     * numb
| Is_Nth_Arb              of subtrm     * numb
| Numb_Is                 of numb       * int
| Depth_Of_Sub_Trm_Occ_Is of subtrm_occ * numb
| Print_Is                of subtrm     * string
(* TODO: pattern *)
| Pattern                 of numb* subtrm * pattern (*In the definition of subtrm, the numb-th argument has this pattern.*)
(*syntax sugars*)
| All_Ind_Occ             of subtrm_occ * subtrm * assrt (*Probably with All_Ind  and All_Sub_Trm_Occ*)
| All_Arb_Occ             of subtrm_occ * subtrm * assrt (*Probably with All_Arb  and All_Sub_Trm_Occ*)
| Some_Ind_Occ            of subtrm_occ * subtrm * assrt (*Probably with Some_Ind and Some_Sub_Trm_Occ*)
| Some_Arb_Occ            of subtrm_occ * subtrm * assrt (*Probably with Some_Ind and Some_Sub_Trm_Occ*)
| Are_Diff_Numb           of numb       * numb           (*Not & Are_Same_Numb*)
| Are_Diff_Str            of subtrm_occ * subtrm_occ     (*Not & Are_Same_Str*)
| Has_Typ                 of subtrm_occ * hol_typ        (*Some_Sub_Trm, Is_In, & Is_Typ*)
| Is_At_Deepest           of subtrm_occ
| Is_More_Than            of numb       * numb           (*Not, Is_Less_Than, And, Are_Same_Numb*)
| For_Numb_N              of numb       * int * assrt    (*Some_Numb $ Numb_Is*)

datatype rule_name = Rule_Name of string;
type rule_names    = rule_name list;
type path          = UN.path;
type paths         = path  list;
type pathss        = paths list;

type location    = TT.location;
type path_n_loc  = path * location;
type path_n_locs = path_n_loc list;

datatype address =(*TODO: better name? id?*)
  Address_Subtrm     of (path * location) list
| Address_Subtrm_Occ of path  * location
| Address_Rule       of rule_name
| Address_Numb       of int;

fun dest_Address_Subtrm     (Address_Subtrm     path_n_loc_s) = SOME path_n_loc_s     : path_n_locs option
  | dest_Address_Subtrm      _                                = NONE                  : path_n_locs option;
fun dest_Address_Subtrm_Occ (Address_Subtrm_Occ path_n_loc )  = SOME path_n_loc       : path_n_loc  option
  | dest_Address_Subtrm_Occ  _                                = NONE                  : path_n_loc  option;
fun dest_Address_Rule       (Address_Rule       rname)        = SOME (rname:rule_name): rule_name   option
  | dest_Address_Rule        _                                = NONE                  : rule_name   option;
fun dest_Address_Numb       (Address_Numb i)                  = SOME (i: int)         : int         option
  | dest_Address_Numb        _                                = NONE                  : int         option;

type addresses = address list;(*TODO: better name?*)

type name_subspace = (int * address) list;

type name_subspaces = name_subspace list;

(*TIP: use functions from AList, such as AList.update, for name_space.*)
datatype name_space = Name_Space of
 {subtrm:     name_subspace,
  subtrm_occ: name_subspace,
  rule:       name_subspace,
  numb:       name_subspace};

type name_spaces = name_space list;

datatype name =
  Name_Nth        of numb
| Name_Subtrm     of subtrm
| Name_Rule       of rule
| Name_Subtrm_Occ of subtrm_occ;

datatype name_domains = Name_Domains of
  {ind_domain    : addresses,
   arb_domain    : addresses,
   subtrm_domain : addresses,
   numb_domain   : addresses,
   rule_domain   : addresses};

datatype name_domain =(*TODO: to be removed?*)
  Subtrm_Domain of addresses (*Subtrm_Domain for all of Ind, Arb, and Subtrm*)
| Rule_Domain   of addresses
| Numb_Domain   of addresses;

fun no_name_collision (Name_Space name_space: name_space) (name: name) =
  let
    fun fsts (xs:('a * 'b) list) = map fst xs: 'a list;
    fun is_in_fsts (x:int) (xs:(int * 'b) list) = xs |> fsts |> (fn ints => member (op =) ints x): bool ;
    fun is_in_numbs       (x:int) = #numb       name_space |> is_in_fsts x: bool;
    fun is_in_subtrms     (x:int) = #subtrm     name_space |> is_in_fsts x: bool;
    fun is_in_rules       (x:int) = #rule       name_space |> is_in_fsts x: bool;
    fun is_in_subtrm_occs (x:int) = #subtrm_occ name_space |> is_in_fsts x: bool;
    fun no_name_collision' (Name_Nth          (Nth         i):name) = is_in_numbs       i
     |  no_name_collision' (Name_Subtrm       (Sub_Trm     i):name) = is_in_subtrms     i
     |  no_name_collision' (Name_Rule         (Rule        i):name) = is_in_rules       i
     |  no_name_collision' (Name_Subtrm_Occ   (Sub_Trm_Occ i):name) = is_in_subtrm_occs i;
  in
    no_name_collision' name
  end;

(*TODO: check name collisions before evaluation.*)
val no_overlad = undefined: assrt -> bool;

fun eval (Name_Domains name_domains: name_domains, abs_pst_w_aux: abs_pstate_w_aux, assert: assrt, Ind_Mods mods:ind_mods) =
  let
    val {ind_domain, arb_domain, subtrm_domain, numb_domain, rule_domain} = name_domains;

    val empty_name_space = Name_Space
       {subtrm     = [],
        subtrm_occ = [],
        rule       = [],
        numb       = []};

    fun alist_add       (alist: (''a * 'a) list) (key:''a, value:'a) = AList.update (op =) (key, value) alist: (''a * 'a) list;
    fun alist_lookup_eq (alist: (''a * 'b) list) (key:''a)           = AList.lookup (op =) alist key;
    fun opt_equal (SOME x, SOME y) = x = y
      | opt_equal (     _,      _) = false: bool;

    fun name_space_n_numb_id_to_integer (Name_Space nspace) (Nth numb_id) =
      let
        val numb_name_space        = #numb nspace                                : name_subspace;
        val integer_address_option = alist_lookup_eq numb_name_space numb_id     : address option;
        val integer_option         = integer_address_option >>= dest_Address_Numb: int option;
      in
        integer_option
      end;

    fun name_space_n_subtrm_occ_id_to_path_n_loc (Name_Space nspace:name_space) (Sub_Trm_Occ occ_id:subtrm_occ) =
      let
        val subtrm_occ_name_space  = #subtrm_occ nspace                            : name_subspace;
        val occ_address_option     = alist_lookup_eq subtrm_occ_name_space occ_id  : address option;
        val occ_path_n_loc_option  = occ_address_option >>= dest_Address_Subtrm_Occ: path_n_loc option;
      in
        occ_path_n_loc_option:  path_n_loc option
      end;

    fun name_space_n_subtrm_id_to_path_n_locs (Name_Space nspace:name_space) (Sub_Trm subtrm_id:subtrm) =
      let
        val subtrm_name_space     = #subtrm nspace                              : name_subspace;
        val subtrm_address_option = alist_lookup_eq subtrm_name_space subtrm_id : address option;
        val subtrm_paths_option   = subtrm_address_option>>= dest_Address_Subtrm: path_n_locs option;
      in
        subtrm_paths_option: path_n_locs option
      end;

    type quantifier = (name_space -> bool) -> name_space list -> bool;

    val {ons, arbs, rules}        = mods                                                                                          : {ons: induct_on list, arbs: induct_arb list, rules: induct_rule};
    val subgoals                  = #subgoals abs_pst_w_aux                                                                       : TT.unode_aux_n_path_tables;
    val unode_aux_tables          = map #unode_aux_table subgoals                                                                 : TT.unode_aux_table list;
    fun unode_aux_table_n_path_to_print (unode_table:TT.unode_aux_table) (path:path) = One_Term.lookup unode_table path <$> #print: UN.print option;
    fun unode_aux_table_n_path_to_node  (unode_table:TT.unode_aux_table) (path:path) = One_Term.lookup unode_table path <$> #node : UN.node option;
    fun loc_to_unode_aux_n_path_table (TT.Nth_Subg     n:location) = try (nth (#subgoals abs_pst_w_aux)) n                        : TT.unode_aux_n_path_table option
      | loc_to_unode_aux_n_path_table (TT.Chained_Fact n:location) = try (nth (#usings   abs_pst_w_aux)) n                        : TT.unode_aux_n_path_table option;

    fun loc_to_unode_aux_table (loc:location) = loc_to_unode_aux_n_path_table loc <$> #unode_aux_table: TT.unode_aux_table option;

    fun path_n_loc_to_print (path:path, loc:location) = 
    let
      val unode_aux_table_option = loc_to_unode_aux_table loc                                : TT.unode_aux_table option;
      val path_to_print_option   = unode_aux_table_option <$> unode_aux_table_n_path_to_print: (path -> UN.print option) option;
      val print_option           = path_to_print_option   <*> SOME path |> Option.join       : UN.print option;
    in
      print_option
    end;

    fun path_n_loc_to_node  (path:path, loc:location) =
    let
      val unode_aux_table_option = loc_to_unode_aux_table loc                               : TT.unode_aux_table option;
      val path_to_node_option    = unode_aux_table_option <$> unode_aux_table_n_path_to_node: (path -> UN.node option) option;
      val node_option            = path_to_node_option <*> SOME path |> Option.join         : UN.node option;
    in
      node_option: UN.node option
    end;

    fun name_space_n_subtrm_occ_id_to_node (name_space:name_space) (Sub_Trm_Occ occ_id:subtrm_occ) =
      let
        val occ_path_n_loc_option = name_space_n_subtrm_occ_id_to_path_n_loc name_space (Sub_Trm_Occ occ_id): path_n_loc option;
        val node_option           = occ_path_n_loc_option <$> path_n_loc_to_node |> Option.join             : UN.node option;
      in
        node_option
      end;

    fun name_space_n_subtrm_id_to_print (name_space:name_space) (subtrm:subtrm) =
      let
        val subtrm_occ_path_n_locs_option  = name_space_n_subtrm_id_to_path_n_locs name_space subtrm: path_n_locs option;
        val subtrm_occ_a_path_n_loc_option = subtrm_occ_path_n_locs_option >>= try hd               : path_n_loc  option;
        val print_option                   = subtrm_occ_a_path_n_loc_option >>= path_n_loc_to_print : print option;
      in
        print_option
      end;

    fun loc_to_deepest_depth (loc:location) = abs_pst_w_aux;

    datatype address_type =
      ATyp_Subtrm
    | ATyp_Subtrm_Occ
    | ATyp_Rule
    | ATyp_Numb;

    fun update_name_space (Name_Space {subtrm_occ, rule, numb, ...}  : name_space) (new_subtrm    : name_subspace) ATyp_Subtrm     = Name_Space {subtrm = new_subtrm, subtrm_occ = subtrm_occ,     rule = rule,     numb = numb    }: name_space
      | update_name_space (Name_Space {subtrm, rule, numb, ...}      : name_space) (new_subtrm_occ: name_subspace) ATyp_Subtrm_Occ = Name_Space {subtrm = subtrm,     subtrm_occ = new_subtrm_occ, rule = rule,     numb = numb    }: name_space
      | update_name_space (Name_Space {subtrm, subtrm_occ, numb, ...}: name_space) (new_rule      : name_subspace) ATyp_Rule       = Name_Space {subtrm = subtrm,     subtrm_occ = subtrm_occ,     rule = new_rule, numb = numb    }: name_space
      | update_name_space (Name_Space {subtrm, subtrm_occ, rule, ...}: name_space) (new_numb      : name_subspace) ATyp_Numb       = Name_Space {subtrm = subtrm,     subtrm_occ = subtrm_occ,     rule = rule,     numb = new_numb}: name_space;

    fun get_new_name_subspaces (i:int) (domain:address list) (old_name_subspace:name_subspace) =
      let
        val new_name_subspace  = map (pair i) domain: name_subspace                 : name_subspace;
        val new_name_subspaces = map (alist_add old_name_subspace) new_name_subspace: name_subspaces;
      in
        new_name_subspaces
      end;

    fun is_nth_arg_of_induct_method (assrt:assrt) (subtrm:subtrm) (nth_numb:numb) (name_space:name_space) =
      let
        val numb                     = name_space_n_numb_id_to_integer name_space nth_numb           : int option;
        fun get_print_option (Is_Nth_Ind _) = numb >>= try (nth ons ) <$> LiFtEr_Util.dest_induct_on : print option
          | get_print_option (Is_Nth_Arb _) = numb >>= try (nth arbs) <$> LiFtEr_Util.dest_induct_arb: print option
          | get_print_option  _             = NONE                                                   : print option;
        val nth_print_option         = get_print_option assrt                                        : print option;
        val subtrm_print_option      = name_space_n_subtrm_id_to_print name_space subtrm             : print option;
        val tobe_compared            = Utils.mk_option_pair (nth_print_option, subtrm_print_option)  : (print * print) option;
        val result_option            = tobe_compared <$> uncurry LU.same_prints                      : bool option;
        val result                   = Utils.is_some_true result_option                              : bool;
      in
        result
      end;

    fun name_space_n_subtrm_occ_are_node_typ_of (name_space:name_space) (subtrm_occ:subtrm_occ) (node_typ:UN.node_typ) =
      let
        val node_option   = name_space_n_subtrm_occ_id_to_node name_space subtrm_occ: UN.node option;
        val result_option = node_option <$> UN.node_typ_to_checker node_typ         : bool option;
        val result        = Utils.is_some_true result_option                        : bool;
      in
        result
      end;

    fun eval'_quantifier' (inner:assrt) (index:int) (name_space:name_space) (name_subspace:name_subspace) (quantifier:quantifier) (domain: addresses) (add_typ:address_type) =
      let
        val new_subtrm_entries_in_name_space = get_new_name_subspaces index domain name_subspace      : name_subspaces;
        fun get_new_name_space new_subtrm    = update_name_space name_space new_subtrm add_typ        : name_space;
        val new_name_spaces                  = map get_new_name_space new_subtrm_entries_in_name_space: name_spaces;
      in
        quantifier (eval' inner) new_name_spaces
      end
    and eval'_subtrm_occ_quantifier (Sub_Trm_Occ occ_idx) (Sub_Trm trm_idx) (inner:assrt) (name_space as Name_Space {subtrm, subtrm_occ, ...}:name_space) (quantifier:quantifier) =
        let
          (*The domain of sub-term-occurrences depends on which sub-term we consider.*)
          val name_space_of_this_subtrm                  = AList.lookup (op =) subtrm trm_idx                                            : address option;
          fun dest_Address_Subtrm (Address_Subtrm paths) = SOME paths
            | dest_Address_Subtrm  _                     = NONE                                                                          : path_n_locs option;
          val path_n_locs                                = name_space_of_this_subtrm >>= dest_Address_Subtrm |> these                    : path_n_locs;
          val new_subtrm_occ_entries_in_name_space       = get_new_name_subspaces occ_idx (map Address_Subtrm_Occ path_n_locs) subtrm_occ: name_subspaces;
          fun get_new_name_space new_subtrm_occ          = update_name_space name_space new_subtrm_occ ATyp_Subtrm_Occ                   : name_space;
          val new_name_spaces                            = map get_new_name_space new_subtrm_occ_entries_in_name_space                   : name_spaces;
        in
          quantifier (eval' inner) new_name_spaces
        end
    (*code re-factoring using mutual recursion*)
    and
      (** eval' is the core function of LiFtEr's interpreter. **)
      (*Note that we never modify abs_pst_w_aux or name_domains.*)
      (*quantifiers*)
        eval' (All_Ind      ((Sub_Trm i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#subtrm name_space) forall ind_domain    ATyp_Subtrm
      | eval' (All_Arb      ((Sub_Trm i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#subtrm name_space) forall arb_domain    ATyp_Subtrm
      | eval' (All_Sub_Trm  ((Sub_Trm i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#subtrm name_space) forall subtrm_domain ATyp_Subtrm
      | eval' (All_Rule     ((Rule    i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#rule   name_space) forall rule_domain   ATyp_Rule
      | eval' (All_Numb     ((Nth     i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#numb   name_space) forall numb_domain   ATyp_Numb
      | eval' (Some_Ind     ((Sub_Trm i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#subtrm name_space) exists ind_domain    ATyp_Subtrm
      | eval' (Some_Arb     ((Sub_Trm i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#subtrm name_space) exists arb_domain    ATyp_Subtrm
      | eval' (Some_Sub_Trm ((Sub_Trm i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#subtrm name_space) exists subtrm_domain ATyp_Subtrm
      | eval' (Some_Rule    ((Rule    i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#rule   name_space) exists rule_domain   ATyp_Rule
      | eval' (Some_Numb    ((Nth     i), inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#numb   name_space) exists numb_domain   ATyp_Numb
      (*quantifiers for occurrences*)
      | eval' (All_Sub_Trm_Occ  (subtrm_occ, subtrm, assrt)) (name_space: name_space) = eval'_subtrm_occ_quantifier subtrm_occ subtrm assrt name_space forall
      | eval' (Some_Sub_Trm_Occ (subtrm_occ, subtrm, assrt)) (name_space: name_space) = eval'_subtrm_occ_quantifier subtrm_occ subtrm assrt name_space exists
      (*combinators*)
      | eval' (assrt1 And assrt2) name_space = eval' assrt1 name_space andalso eval' assrt2 name_space
      | eval' (assrt1 Or  assrt2) name_space = eval' assrt1 name_space orelse  eval' assrt2 name_space
      | eval' (Not assrt)            name_space = not (eval' assrt name_space)
      | eval' (assrt1 Imply assrt2) name_space =
          if   eval' assrt1 name_space
          then eval' assrt2 name_space
          else true
      | eval' (Are_Same_Numb (Nth n1, Nth n2)) (Name_Space ns:name_space) =
        let
          val numb_name_space = #numb ns                                                : name_subspace;
          val numb1_option    = alist_lookup_eq numb_name_space n1 >>= dest_Address_Numb: int option;
          val numb2_option    = alist_lookup_eq numb_name_space n2 >>= dest_Address_Numb: int option;
          val result          = opt_equal (numb1_option, numb2_option)                  : bool;
        in
          result
        end
      | eval' (Are_Same_Str (subtrm_occ1, subtrm_occ2)) (name_space:name_space) =
        let
          val occ1_occ2_path_n_loc_option  = Utils.mapPartial2 (name_space_n_subtrm_occ_id_to_path_n_loc name_space) (SOME (subtrm_occ1, subtrm_occ2)): (path_n_loc * path_n_loc) option;
          val occ1_occ2_print_option       = Utils.mapPartial2 path_n_loc_to_print occ1_occ2_path_n_loc_option                                        : (UN.print * UN.print) option;
          val result_option                = occ1_occ2_print_option <$> uncurry LU.same_prints                                                        : bool option;
          val result                       = Utils.is_some_true result_option                                                                         : bool;
        in
          result
        end
      | eval' (Is_In_Trm_Loc (subtrm_occ1, subtrm_occ2)) (name_space:name_space) =
        let
          val occ1_occ2_path_n_loc_option = Utils.mapPartial2 (name_space_n_subtrm_occ_id_to_path_n_loc name_space) (SOME (subtrm_occ1, subtrm_occ2)): (path_n_loc * path_n_loc) option;
          val occ1_occ2_path_option       = occ1_occ2_path_n_loc_option <$> apply2 fst                                                                    : (path * path) option;
          val occ1_occ2_loc_option        = occ1_occ2_path_n_loc_option <$> apply2 snd                                                                    : (location * location) option;
          val path1_is_under_path2_option = occ1_occ2_path_option <$> uncurry UN.path1_is_above_path2                                                     : bool option;
          val loc1_n_loc2_are_same        = occ1_occ2_loc_option <$> TT.same_location                                                                     : bool option;
          val result_pair                 = Utils.mk_option_pair (path1_is_under_path2_option, loc1_n_loc2_are_same)                                      : (bool * bool) option;
          val result                      = result_pair <$> (op =) |> Utils.is_some_true                                                                  : bool;
        in
          result
        end
      | eval' (Is_In_Trm_Str (subtrm_occ1, subtrm_occ2)) (name_space:name_space) =
        let
          val occ1_occ2_path_n_loc_option  = Utils.mapPartial2 (name_space_n_subtrm_occ_id_to_path_n_loc name_space) (SOME (subtrm_occ1, subtrm_occ2)): (path_n_loc * path_n_loc) option;
          val occ1_occ2_print_option       = Utils.mapPartial2 path_n_loc_to_print occ1_occ2_path_n_loc_option                                             : (UN.print * UN.print) option;
          val result_option                = occ1_occ2_print_option <$> uncurry LU.is_subprint_of                                                          : bool option;
          val result                       = Utils.is_some_true result_option                                                                              : bool;
        in
          result
        end
      | eval' (Is_In_Trm_Sem (Sub_Trm_Occ occ_idx_1, Sub_Trm_Occ occ_idx_2)) (Name_Space name_space:name_space) =
        let
        in true (*TODO*)
        end
      | eval' (Is_Typ (subtrm_occ:subtrm_occ, hol_typ:hol_typ)) (name_space:name_space) =
        let
          fun is_hol_typ_of Fun_Typ  (typ:typ) = Isabelle_Utils.is_fun_typ  typ
            | is_hol_typ_of List_Typ (typ:typ) = Isabelle_Utils.is_list_typ typ
            | is_hol_typ_of Nat_Typ  (typ:typ) = Isabelle_Utils.is_nat_typ  typ
            | is_hol_typ_of Int_Typ  (typ:typ) = Isabelle_Utils.is_int_typ  typ
            | is_hol_typ_of Set_Typ  (typ:typ) = Isabelle_Utils.is_set_typ  typ;
          val node_option     = name_space_n_subtrm_occ_id_to_node name_space subtrm_occ: UN.node option;
          val atomic_node_typ = node_option >>= UN.node_to_atoms_typ: typ option;
          val result          = atomic_node_typ <$> is_hol_typ_of hol_typ |> Utils.is_some_true: bool;
        in result
        end
      | eval' (Is_In_Chained (subtrm_occ:subtrm_occ)) (name_space:name_space) =
        let
          val subtrm_occ_path_n_loc_option = name_space_n_subtrm_occ_id_to_path_n_loc name_space subtrm_occ     : path_n_loc option;
          val subtrm_occ_loc_option        = subtrm_occ_path_n_loc_option <$> snd: location option              : location option;
          val result                       = subtrm_occ_loc_option <$> TT.in_chained_facts |> Utils.is_some_true: bool;
        in
          result
        end
      | eval' (Is_In_Fst_Subg (subtrm_occ:subtrm_occ)) (name_space:name_space) =
        let
          val subtrm_occ_path_n_loc_option = name_space_n_subtrm_occ_id_to_path_n_loc name_space subtrm_occ: path_n_loc option;
          val subtrm_occ_loc_option        = subtrm_occ_path_n_loc_option <$> snd: location option         : location option;
          val result                       = subtrm_occ_loc_option <$> TT.in_subgoals |> Utils.is_some_true: bool;
        in
          result
        end
      | eval' (Is_In_Prems (subtrm_occ:subtrm_occ)) (Name_Space name_space:name_space) =
        (* Should Is_In_Prems treated as a syntax-sugar based on
           Is_Nth_Arg_Of, Is_In_Trm_Loc, Some_Sub_Trm_Occ, Is_Const_Of_Name, Is_In_Trm_Loc? *)
        let
          val get_fresh_subtrm_occ_id = 1;(*TODO*)
          val get_fresh_subtrm_id = 1;(*TODO*)
          val desugared_assrt =(*TODO: FIXME*)
            Some_Sub_Trm (Sub_Trm 1(*TOOD*),
             (Some_Sub_Trm_Occ (Sub_Trm_Occ 1(*TODO*), Sub_Trm 1(*TODO*),
               (Some_Sub_Trm_Occ (Sub_Trm_Occ 2(*TODO*), Sub_Trm 1(*TODO*),
                Is_In_Cnclsn (Sub_Trm_Occ 1))))))
        in true (*TODO*)
        end
      | eval' (Is_In_Cnclsn (Sub_Trm_Occ occ_idx)) (Name_Space name_space:name_space) =
        let
        in true (*TODO*)
        end
      | eval' (Is_Const_Of_Name (subtrm_occ, const_name:string)) (name_space:name_space) =
        let
          val node_option   = name_space_n_subtrm_occ_id_to_node name_space subtrm_occ: UN.node option;
          val cname_option  = node_option >>= UN.dest_NC <$> fst                      : string option;
          val result        = opt_equal (cname_option, SOME const_name)               : bool;
        in
          result
        end
      | eval' (Is_Cnst   subtrm_occ) (name_space:name_space) = name_space_n_subtrm_occ_are_node_typ_of name_space subtrm_occ UN.Node_Typ_NC
      | eval' (Is_Var    subtrm_occ) (name_space:name_space) = name_space_n_subtrm_occ_are_node_typ_of name_space subtrm_occ UN.Node_Typ_NV
      | eval' (Is_Free   subtrm_occ) (name_space:name_space) = name_space_n_subtrm_occ_are_node_typ_of name_space subtrm_occ UN.Node_Typ_NF
      | eval' (Is_Bound  subtrm_occ) (name_space:name_space) = name_space_n_subtrm_occ_are_node_typ_of name_space subtrm_occ UN.Node_Typ_NB
      | eval' (Is_Lambda subtrm_occ) (name_space:name_space) = name_space_n_subtrm_occ_are_node_typ_of name_space subtrm_occ UN.Node_Typ_NL
      | eval' (Is_App    subtrm_occ) (name_space:name_space) = name_space_n_subtrm_occ_are_node_typ_of name_space subtrm_occ UN.Node_Typ_NA
      | eval' (Not_Fully_App subtrm_occ) (name_space:name_space) =
        let
          val subtrm_occ_path_n_loc_option = name_space_n_subtrm_occ_id_to_path_n_loc name_space subtrm_occ: path_n_loc option;
          val subtrm_occ_path_option       = subtrm_occ_path_n_loc_option <$> fst: path option                  : path option;
          val subtrm_occ_loc_option        = subtrm_occ_path_n_loc_option <$> snd: location option              : location option;
          val subtrm_occ_node              = subtrm_occ_path_n_loc_option >>= path_n_loc_to_node                : UN.node option;
          val is_NA                        = subtrm_occ_node <$> UN.is_NA |> Utils.is_some_true                 : bool;
          val func_path_option             = Utils.mk_option_pair (subtrm_occ_path_option, SOME [0]) <$> List.@ : path option;
          val func_path_loc_option         = Utils.mk_option_pair (func_path_option, subtrm_occ_loc_option)     : path_n_loc option;
          fun path_at_loc_has_n_children' (p:path) (loc:location) (acc:int) = case path_n_loc_to_node (p @ [acc], loc) of
              NONE => acc
            | SOME _ => path_at_loc_has_n_children' p loc (acc + 1);
          fun path_at_loc_has_n_children (p:path, loc:location) = path_at_loc_has_n_children' p loc 0         : int;
          val numb_of_funcs_children_option = func_path_loc_option <$> path_at_loc_has_n_children             : int option;
          val func_node_option              = func_path_loc_option >>= path_n_loc_to_node                     : UN.node option;
          val func_typ_option               = func_node_option >>= UN.node_to_atoms_typ                       : typ option;
          val numb_of_fun_typs_args         = func_typ_option <$> Isabelle_Utils.count_numb_of_args_of_fun_typ: int option;
          val same_numbs                    = opt_equal (numb_of_funcs_children_option, numb_of_fun_typs_args): bool;
        in
          is_NA andalso same_numbs
        end
      | eval' (Is_Less_Than (Nth numb1, Nth numb2)) (Name_Space nspace:name_space) =
        let
          val numb_name_space      = #numb nspace                                               : name_subspace;
          fun get_numb_option numb = alist_lookup_eq numb_name_space numb >>= dest_Address_Numb : int option;
          val numb1_option         = get_numb_option numb1                                      : int option;
          val numb2_option         = get_numb_option numb2                                      : int option;
          val numbs_option         = Utils.mk_option_pair (numb1_option, numb2_option)          : (int * int) option;
          val result_option        = numbs_option <$> Int.>                                     : bool option;
          val result               = Utils.is_some_true result_option                           : bool;
        in
          result
        end
      | eval' (Is_Nth_Arg_Of (func:subtrm_occ, Nth numb:numb, arg:subtrm_occ)) (name_space as Name_Space nspace) =
        let
          val path_n_loc_of_func_option      = name_space_n_subtrm_occ_id_to_path_n_loc name_space func            : path_n_loc option;
          val path_n_loc_of_arg_option       = name_space_n_subtrm_occ_id_to_path_n_loc name_space arg             : path_n_loc option;
          val numb_name_space                = #numb nspace                                                        : name_subspace;
          val numb_option                    = alist_lookup_eq numb_name_space numb >>= dest_Address_Numb          : int option;
          val numb_list_option               = numb_option <$> single                                              : int list option;
          val func_occ_path_option           = path_n_loc_of_func_option <$> fst                                   : path option;
          val init_of_path_to_func_option    = func_occ_path_option <$> Utils.init                                 : path option;
          val init_n_last_option             = Utils.mk_option_pair (init_of_path_to_func_option, numb_list_option): (path * path) option;
          val path_to_nth_arg_of_func_option = init_n_last_option <$> List.@                                       : path option;
          val arg_occ_path_option            = path_n_loc_of_arg_option  <$> fst                                   : path option;
          val are_same_paths                 = opt_equal (arg_occ_path_option, path_to_nth_arg_of_func_option)     : bool;
        in
          are_same_paths
        end
      | eval' (assrt as Is_Nth_Ind (subtrm:subtrm, numb)) (name_space:name_space) = is_nth_arg_of_induct_method assrt subtrm numb name_space
      | eval' (assrt as Is_Nth_Arb (subtrm:subtrm, numb)) (name_space:name_space) = is_nth_arg_of_induct_method assrt subtrm numb name_space
      | eval' (Numb_Is  (Nth numb, int:int)) (name_space:name_space) =
        let
          val numb_option   = name_space_n_numb_id_to_integer name_space (Nth numb): int option;
          val result        = opt_equal (numb_option, SOME int)                    : bool;
        in
         result
        end
      | eval' (Print_Is (subtrm:subtrm, string:string)) (name_space:name_space) =
        let
          val print_option        = name_space_n_subtrm_id_to_print name_space subtrm: print option;
          val print_string_option = print_option <$> UN.dest_Print                   : string option;
          val result              = opt_equal (print_string_option, SOME string)     : bool;
        in
          result
        end
      | eval' (Pattern (numb:numb, subtrm:subtrm, pttrn:pattern)) (name_space:name_space) = true (*TODO*)
      (*syntax sugars*)
      | eval' (All_Ind_Occ  (subtrm_occ:subtrm_occ, subtrm:subtrm, inner:assrt)) (name_space:name_space) = eval' (All_Ind (subtrm, (All_Sub_Trm_Occ (subtrm_occ, subtrm, inner))))   name_space
      | eval' (All_Arb_Occ  (subtrm_occ:subtrm_occ, subtrm:subtrm, inner:assrt)) (name_space:name_space) = eval' (All_Arb (subtrm, (All_Sub_Trm_Occ (subtrm_occ, subtrm, inner))))   name_space
      | eval' (Some_Ind_Occ (subtrm_occ:subtrm_occ, subtrm:subtrm, inner:assrt)) (name_space:name_space) = eval' (Some_Ind (subtrm, (Some_Sub_Trm_Occ (subtrm_occ, subtrm, inner)))) name_space
      | eval' (Some_Arb_Occ (subtrm_occ:subtrm_occ, subtrm:subtrm, inner:assrt)) (name_space:name_space) = eval' (Some_Arb (subtrm, (Some_Sub_Trm_Occ (subtrm_occ, subtrm, inner)))) name_space
      | eval' (Is_Atom subtrm_occ)                                               (name_space:name_space) = eval' (Is_Cnst subtrm_occ Or Is_Free subtrm_occ Or Is_Bound subtrm_occ)   name_space
      | eval' (Are_Diff_Numb (numb1, numb2))                                     (name_space:name_space) = eval' (Not (Are_Same_Numb (numb1, numb2)))                                name_space
      | eval' (Are_Diff_Str  (subtrm_occ1, subtrm_occ2))                         (name_space:name_space) = eval' (Not (Are_Same_Str (subtrm_occ1, subtrm_occ2)))                     name_space
      | eval' (Has_Typ       (subtrm_occ:subtrm_occ, hol_typ:hol_typ)) (name_space:name_space) =
        let
          val desugared_assert = ();
        in
          (*TODO*)true
        end
      | eval' (Is_At_Deepest (subtrm_occ:subtrm_occ)) (name_space:name_space) =
        (* TODO:
         * Treat Is_At_Deepest as a syntactic sugar for something based on Depth_Of_Sub_Trm_Occ_Is, Some_Sub_Trm, and Not.
         * We can introduce a new quantifier safely without polluting name_space for other (inner) assertions
         * because Is_At_Deepest is an atomic assertion.*)
        let
          val path_n_loc_option             = name_space_n_subtrm_occ_id_to_path_n_loc name_space subtrm_occ                  : path_n_loc option;
          val (path_option, loc_option)     = Utils.mk_options_pair path_n_loc_option                                         : (path option * location option);
          val subtrm_occs_depth_option      = path_option <$> length: int option                                              : int option;
          val unode_aux_n_path_table_option = loc_option <$> TT.abs_pstate_w_aux_n_loc_to_unode_aux_n_path_table abs_pst_w_aux: TT.unode_aux_n_path_table option;
          val unode_aux_table_option        = unode_aux_n_path_table_option <$> #unode_aux_table                              : TT.unode_aux_table option;
          val maximum_depth_option          = unode_aux_table_option >>= TT.unode_aux_table_to_depth: int option              : int option;
          val result                        = opt_equal (subtrm_occs_depth_option, maximum_depth_option)                      : bool;
        in
          result
        end
      | eval' (Is_More_Than  (numb1:numb, numb2:numb))          (name_space:name_space) = eval' (Not (Is_Less_Than (numb1, numb2)) And Not (Are_Same_Numb (numb1, numb2))) name_space
      | eval' (For_Numb_N    (numb:numb, int:int, inner:assrt)) (name_space:name_space) = eval' (Numb_Is (numb, int) And Some_Numb (numb, inner))                          name_space
  in
    eval' assert empty_name_space
  end;

end;