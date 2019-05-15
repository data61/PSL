(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The syntax and interpreter of LiFtEr, Logical Feature Extractor for MiLkMaId.
*)
structure LiFtEr: LIFTER =
struct

open Pattern LiFtEr_Util;

structure UN = Unique_Node;
structure LU = LiFtEr_Util;
structure TT = Term_Table;
structure PT = Print_Table;

type lifter_pst = TT.lifter_pst;

datatype numb    = Numb    of int;
datatype trm     = Trm     of int;
datatype rule    = Rule    of int;
datatype trm_occ = Trm_Occ of int;
datatype pattern = All_Only_Var | All_Const | Mixed;(*TODO: This is not final.*)

infix And Or Imply;

(* assrt *)
datatype assrt   =
(*quantifiers*)
  All_Ind                 of trm  * assrt
| All_Arb                 of trm  * assrt
| All_Trm                 of trm  * assrt
| All_Rule                of rule * assrt
| All_Numb                of numb * assrt
| Some_Ind                of trm  * assrt
| Some_Arb                of trm  * assrt
| Some_Trm                of trm  * assrt
| Some_Rule               of rule * assrt
| Some_Numb               of numb * assrt (*n must be smaller than or equal to the argument number of the variable/constant that has the maximum argument number.*)
(*quantifiers for occurrences*)
| All_Trm_Occ             of trm_occ * assrt
| Some_Trm_Occ            of trm_occ * assrt
(*combinators*)
| And                     of assrt * assrt
| Or                      of assrt * assrt
| Not                     of assrt
| True
| Imply                   of assrt * assrt
(*atomic about proof goal*)
| Is_Rule_Of              of rule    * trm_occ
| Trm_Occ_Is_Of_Trm       of trm_occ * trm
| Are_Same_Numb           of numb    * numb
| Are_Same_Str            of trm_occ * trm_occ (*trm*)
| Is_In_Trm_Loc           of trm_occ * trm_occ (*sub-tree-1 is within sub-tree-2 location-wise*)
| Is_In_Trm_Str           of trm_occ * trm_occ (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_Typ                  of trm_occ * hol_typ
| Is_In_Chained           of trm_occ
| Is_In_Fst_Subg          of trm_occ
| Is_In_Prems             of trm_occ
| Is_In_Cnclsn            of trm_occ
| Is_Atom                 of trm_occ
| Is_Cnst                 of trm_occ
| Is_Const_Of_Name        of trm_occ * string
| Is_Var                  of trm_occ
| Is_Free                 of trm_occ
| Is_Bound                of trm_occ (*corresponds to Bound in term*)
| Is_Lambda               of trm_occ (*lambda abstraction corresponding to Abs in Term*)
| Is_App                  of trm_occ (*function application corresponding to $ in Term*)
| Not_Fully_App           of trm_occ (*If trm is function application that is not fully applied returns true, otherwise returns false.*)
| Is_Less_Than            of numb    * numb (* nth_1 < nth_2 *)
| Is_Nth_Arg_Of           of trm_occ * numb * trm_occ
| Is_Nth_Ind              of trm     * numb (*Counting starts with 0.*)
| Is_Nth_Arb              of trm     * numb (*Counting starts with 0.*)
| Is_Int                  of numb    * int
| Is_At_Depth             of trm_occ * numb
| Is_Printed_As           of trm     * string
(* TODO: pattern *)
| Pattern                 of numb* trm_occ * pattern (*In the definition of trm, the numb-th argument has this pattern.*)
(*syntax sugars*)
| Are_Diff_Numb           of numb    * numb           (*Not & Are_Same_Numb*)
| Are_Diff_Str            of trm_occ * trm_occ        (*Not & Are_Same_Str*)
| Has_Typ                 of trm_occ * hol_typ        (*Some_Trm, Is_In, & Is_Typ*)
| Is_At_Deepest           of trm_occ
| Is_More_Than            of numb    * numb           (*Not, Is_Less_Than, And, Are_Same_Numb*)
| For_Numb_N              of numb    * int * assrt    (*Some_Numb $ Is_Int*)
| All_Trm_Occ_Of          of trm_occ * trm * assrt
| Some_Trm_Occ_Of         of trm_occ * trm * assrt

(* rule_name(s) *)
datatype rule_name = Rule_Name of string;
type rule_names    = rule_name list;

fun dest_Rule_Name (Rule_Name rname) = SOME rname

(* path(s/ss) *)
type path        = UN.path;
type paths       = path  list;
type pathss      = paths list;

type location    = TT.location;
type path_n_loc  = TT.path_n_loc;
type path_n_locs = TT.path_n_locs;

fun same_path_n_loc (path1, location1) (path2, location2) = path1 = path2 andalso location1 = location2;

(* id/name_space *)
datatype id =
  ID_Trm     of print
| ID_Trm_Occ of path_n_loc
| ID_Rule    of rule_name
| ID_Numb    of int;

fun print_id (ID_Trm (Print print))      = "ID_Trm " ^ print (*TODO*)
  | print_id (ID_Trm_Occ p_n_l)          = "ID_Trm_Occ"
  | print_id (ID_Rule (Rule_Name rname)) = "ID_Rule " ^ rname
  | print_id (ID_Numb int)               = "ID_Numb " ^ Int.toString int;

fun dest_ID_Trm     (ID_Trm     print)      = SOME print            : print      option
  | dest_ID_Trm      _                      = NONE                  : print      option;
fun dest_ID_Trm_Occ (ID_Trm_Occ path_n_loc) = SOME path_n_loc       : path_n_loc option
  | dest_ID_Trm_Occ  _                      = NONE                  : path_n_loc option;
fun dest_ID_Rule    (ID_Rule    rname)      = SOME (rname:rule_name): rule_name  option
  | dest_ID_Rule        _                   = NONE                  : rule_name  option;
fun dest_ID_Numb    (ID_Numb i)             = SOME (i: int)         : int        option
  | dest_ID_Numb     _                      = NONE                  : int        option;

type ids = id list;

type name_subspace = (int * id) list;

type name_subspaces = name_subspace list;

(*TIP: use functions from AList, such as AList.update, for name_space.*)
datatype name_space = Name_Space of
 {trm:     name_subspace,
  trm_occ: name_subspace,
  rule:    name_subspace,
  numb:    name_subspace};

type name_spaces = name_space list;

datatype name =
  Name_Numb    of numb
| Name_Trm     of trm
| Name_Rule    of rule
| Name_Trm_Occ of trm_occ;

datatype domain =
  Dom_Trm_Occ of path_n_locs 
| Dom_Trm     of prints
| Dom_On      of prints
| Dom_Arb     of prints
| Dom_Rule    of rule_names
| Dom_Numb    of ints;

datatype name_domains = Name_Domains of
  {trm_domain    : domain,
   trm_occ_domain: domain,
   on_domain     : domain,
   arb_domain    : domain,
   rule_domain   : domain,
   numb_domain   : domain};

val empty_domain (*TODO: This should not be used*) = Name_Domains
  {trm_domain     = Dom_Trm [],
   trm_occ_domain = Dom_Trm_Occ [],
   on_domain      = Dom_On [],
   arb_domain     = Dom_Arb [],
   numb_domain    = Dom_Rule [],
   rule_domain    = Dom_Numb []}: name_domains;

(*TODO: check name collisions before evaluation. Use no_name_collision.*)
val no_overlad = undefined: assrt -> bool;

fun pst_to_abs_lifter_pst (pst:Proof.state): lifter_pst =
  let
    (*TODO: use no_overload*)
    val no_overlad = undefined: assrt -> bool;
  in
    Term_Table.pst_to_lifter_pst pst
  end;

fun get_new_name_subspaces (i:int) (domain:ids) (old_name_subspace:name_subspace) =
  let
    val new_name_subspace  = map (pair i) domain: name_subspace                       : name_subspace;
    val new_name_subspaces = map (Utils.alist_add old_name_subspace) new_name_subspace: name_subspaces;
  in
    new_name_subspaces
  end;

datatype id_typ =
  IDTyp_Trm
| IDTyp_Trm_Occ
| IDTyp_On
| IDTyp_Arb
| IDTyp_Rule
| IDTyp_Numb;

(*Note that IDTyp_On and IDTyp_Arb have their own domains, but they share name_space with IDTyp_Trm*)
(*because induction terms and generalized terms are kind of terms.                                 *)
fun update_name_space (new_trm    : name_subspace) IDTyp_Trm     (Name_Space {trm_occ, rule, numb, ...}: name_space) = Name_Space {trm = new_trm, trm_occ = trm_occ,     rule = rule,     numb = numb    }: name_space
  | update_name_space (new_trm_occ: name_subspace) IDTyp_Trm_Occ (Name_Space {trm, rule, numb, ...}    : name_space) = Name_Space {trm = trm,     trm_occ = new_trm_occ, rule = rule,     numb = numb    }: name_space
  | update_name_space (new_trm    : name_subspace) IDTyp_On      (Name_Space {trm_occ, rule, numb, ...}: name_space) = Name_Space {trm = new_trm, trm_occ = trm_occ,     rule = rule,     numb = numb    }: name_space
  | update_name_space (new_trm    : name_subspace) IDTyp_Arb     (Name_Space {trm_occ, rule, numb, ...}: name_space) = Name_Space {trm = new_trm, trm_occ = trm_occ,     rule = rule,     numb = numb    }: name_space
  | update_name_space (new_rule   : name_subspace) IDTyp_Rule    (Name_Space {trm, trm_occ, numb, ...} : name_space) = Name_Space {trm = trm,     trm_occ = trm_occ,     rule = new_rule, numb = numb    }: name_space
  | update_name_space (new_numb   : name_subspace) IDTyp_Numb    (Name_Space {trm, trm_occ, rule, ...} : name_space) = Name_Space {trm = trm,     trm_occ = trm_occ,     rule = rule,     numb = new_numb}: name_space;

(*TODO: numb_domain should not rely on a magic number, 30.*)
val numb_domain = List.tabulate (30, I) |> Dom_Numb: domain;

fun ind_mods_to_on_domain   (LU.Ind_Mods {ons,...  }:LU.ind_mods) = map  LU.dest_induct_on                ons   |> Dom_On  : domain;
fun ind_mods_to_arb_domain  (LU.Ind_Mods {arbs,... }:LU.ind_mods) = map  LU.dest_induct_arb               arbs  |> Dom_Arb : domain;
fun ind_mods_to_rule_domain (LU.Ind_Mods {rules,...}:LU.ind_mods) = map (Rule_Name o LU.dest_induct_rule) rules |> Dom_Rule: domain;

fun pst_to_trm_domain (pst:Proof.state) =
  let
    val {subgoals, usings} = pst_to_abs_lifter_pst pst: lifter_pst;
    fun unode_n_path_tables_to_pathss (one_terms:TT.one_terms) =
        one_terms |> map #print_to_paths_table |> map Print_Table.keys                               :prints list;
    val subgoal_pathss = unode_n_path_tables_to_pathss subgoals                                      :prints list;
    val using_pathss   = unode_n_path_tables_to_pathss usings                                        :prints list;
    val prints         = (subgoal_pathss @ using_pathss) |> flat |> distinct (uncurry LU.same_prints):print list;
    val _ = tracing ("The cardinality of trm_domain is " ^ Int.toString (length prints) ^ ".");
    val result         = Dom_Trm prints                                                              :domain;
  in
    result: domain
  end;

fun pst_to_trm_occ_domain (pst:Proof.state) =
  let
    val {subgoals, usings} = pst_to_abs_lifter_pst pst: lifter_pst;
    datatype loc_typ = LTyp_Nth_Subg | LTyp_Chained_Fact;
    fun one_term_n_loc_typ_to_path_n_locs (term:TT.one_term) (acc:int) (loc_typ:loc_typ) =
        let
          val paths = #path_to_unode_aux_table term |> Path_Table.keys: UN.paths;
          fun loc_typ_n_int_to_location (LTyp_Nth_Subg    :loc_typ) (i:int) = TT.Nth_Subg     i
            | loc_typ_n_int_to_location (LTyp_Chained_Fact:loc_typ) (i:int) = TT.Chained_Fact i;
          val path_n_locs = map (fn path => (path, loc_typ_n_int_to_location loc_typ acc)) paths: TT.path_n_locs;
        in
          path_n_locs
        end;
    fun one_terms_n_loc_typ_to_path_n_locs ([]       :TT.one_terms)  _             _              acc                   = acc: path_n_locs list
      | one_terms_n_loc_typ_to_path_n_locs (trm::trms:TT.one_terms) (counter:int) (ltyp:loc_typ) (acc:path_n_locs list) =
        one_terms_n_loc_typ_to_path_n_locs (trms     :TT.one_terms) (counter + 1) (ltyp:loc_typ) (one_term_n_loc_typ_to_path_n_locs trm counter ltyp :: acc)
    val path_n_locs_in_subgoals = one_terms_n_loc_typ_to_path_n_locs subgoals 0 LTyp_Nth_Subg     [];
    val path_n_locs_in_chained  = one_terms_n_loc_typ_to_path_n_locs usings   0 LTyp_Chained_Fact [];
    val path_n_locs = flat (path_n_locs_in_subgoals @ path_n_locs_in_chained: path_n_locs list): path_n_locs
    val _ = tracing ("The cardinality of trm_occ_domain is " ^ Int.toString (length path_n_locs) ^ ".");
    val result = Dom_Trm_Occ path_n_locs: domain;
  in
    result: domain
  end;

fun pst_to_name_domains (pst:Proof.state) (ind_mods:LU.ind_mods): name_domains = Name_Domains
  {trm_domain     = pst_to_trm_domain       pst,
   trm_occ_domain = pst_to_trm_occ_domain   pst,
   on_domain      = ind_mods_to_on_domain   ind_mods,
   arb_domain     = ind_mods_to_arb_domain  ind_mods,
   rule_domain    = ind_mods_to_rule_domain ind_mods,
   numb_domain    = numb_domain};

fun no_name_collision (Name_Space name_space: name_space) (name: name) =
  let
    fun fsts (xs:('a * 'b) list) = map fst xs: 'a list;
    fun is_in_fsts (x:int) (xs:(int * 'b) list) = xs |> fsts |> (fn ints => member (op =) ints x): bool ;
    fun is_in_numbs    (x:int) = #numb       name_space |> is_in_fsts x: bool;
    fun is_in_trms     (x:int) = #trm     name_space |> is_in_fsts x: bool;
    fun is_in_rules    (x:int) = #rule       name_space |> is_in_fsts x: bool;
    fun is_in_trm_occs (x:int) = #trm_occ name_space |> is_in_fsts x: bool;
    fun no_name_collision' (Name_Numb    (Numb    i):name) = is_in_numbs    i
     |  no_name_collision' (Name_Trm     (Trm     i):name) = is_in_trms     i
     |  no_name_collision' (Name_Rule    (Rule    i):name) = is_in_rules    i
     |  no_name_collision' (Name_Trm_Occ (Trm_Occ i):name) = is_in_trm_occs i;
  in
    no_name_collision' name
  end;

(* eval *)
fun eval (pstate: Proof.state, assert: assrt, Ind_Mods mods:ind_mods) =
  let
    val _ = tracing "Start computing eval in LiFtEr_Struct.ML";
    val Name_Domains name_domains = pst_to_name_domains pstate (Ind_Mods mods):  name_domains;
    val lifter_pst                = Term_Table.pst_to_lifter_pst pstate       : lifter_pst;
    val {trm_domain, trm_occ_domain, on_domain, arb_domain, numb_domain, rule_domain} = name_domains;
    val ctxt                      = Proof.context_of pstate                   : Proof.context;
    val empty_name_space = Name_Space
       {trm     = [],
        trm_occ = [],
        rule    = [],
        numb    = []};

    val alist_lookup_eq = Utils.alist_lookup_eq;
    val opt_equal       = Utils.opt_equal;

    fun name_space_n_numb_id_to_integer (Name_Space nspace) (Numb numb_id) =
      let
        val numb_name_space   = #numb nspace                           : name_subspace;
        val integer_id_option = alist_lookup_eq numb_name_space numb_id: id option;
        val integer_option    = integer_id_option >>= dest_ID_Numb     : int option;
      in
        integer_option
      end;

    fun name_space_n_trm_occ_id_to_path_n_loc (Name_Space nspace:name_space) (Trm_Occ occ_id:trm_occ) =
      let
        val trm_occ_name_space    = #trm_occ nspace                          : name_subspace
        val occ_id_option         = alist_lookup_eq trm_occ_name_space occ_id: id option;
        val occ_path_n_loc_option = occ_id_option >>= dest_ID_Trm_Occ        : path_n_loc option;
      in
        occ_path_n_loc_option:  path_n_loc option
      end;

    fun name_space_n_trm_id_to_print (Name_Space nspace:name_space) (Trm trm_id:trm) =
      let
        val trm_name_space   = #trm nspace                          : name_subspace;
        val trm_id_option    = alist_lookup_eq trm_name_space trm_id: id option;
        val trm_paths_option = trm_id_option>>= dest_ID_Trm      : print option;
      in
        trm_paths_option: print option
      end;

    type quantifier = (name_space -> bool) -> name_space list -> bool;

    val {ons, arbs,...} = mods: {ons: induct_on list, arbs: induct_arb list, rules: induct_rule list};
    fun path_to_unode_aux_table_n_path_to_print (path_to_unode_aux_table:TT.path_to_unode_aux_table) (path:path) =
        Path_Table.lookup path_to_unode_aux_table path <$> #print: UN.print option;
    fun unode_aux_table_n_path_to_node  (path_to_unode_aux_table:TT.path_to_unode_aux_table) (path:path) =
        Path_Table.lookup path_to_unode_aux_table path <$> #node : UN.node option;
    fun loc_to_one_term (TT.Nth_Subg     n:location) = try (nth (#subgoals lifter_pst)) n: TT.one_term option
      | loc_to_one_term (TT.Chained_Fact n:location) = try (nth (#usings   lifter_pst)) n: TT.one_term option;

    fun loc_to_path_to_unode_aux_table (loc:location) = loc_to_one_term loc <$> #path_to_unode_aux_table
      : TT.path_to_unode_aux_table option;

    fun path_n_loc_to_print (path:path, loc:location) = 
    let
      val unode_aux_table_option = loc_to_path_to_unode_aux_table loc                                : TT.path_to_unode_aux_table option;
      val path_to_print_option   = unode_aux_table_option <$> path_to_unode_aux_table_n_path_to_print: (path -> UN.print option) option;
      val print_option           = path_to_print_option   <*> SOME path |> Option.join               : UN.print option;
    in
      print_option
    end;

    fun path_n_loc_to_node  (path:path, loc:location) =
    let
      val unode_aux_table_option = loc_to_path_to_unode_aux_table loc                       : TT.path_to_unode_aux_table option;
      val path_to_node_option    = unode_aux_table_option <$> unode_aux_table_n_path_to_node: (path -> UN.node option) option;
      val node_option            = path_to_node_option <*> SOME path |> Option.join         : UN.node option;
    in
      node_option: UN.node option
    end;

    fun name_space_n_trm_occ_id_to_node (name_space:name_space) (Trm_Occ occ_id:trm_occ) =
      let
        val occ_path_n_loc_option = name_space_n_trm_occ_id_to_path_n_loc name_space (Trm_Occ occ_id): path_n_loc option;
        val node_option           = occ_path_n_loc_option <$> path_n_loc_to_node |> Option.join      : UN.node option;
      in
        node_option
      end;

    fun name_space_n_trm_occ_id_to_cname (name_space:name_space) (trm_occ:trm_occ) =
      let
          val node_option   = name_space_n_trm_occ_id_to_node name_space trm_occ: UN.node option;
          val cname_option  = node_option >>= UN.dest_NC <$> fst                : string option;
      in
        cname_option: string option
      end;

    (*Note that IDTyp_Trm, IDTyp_On, and IDTyp_Arb share name_space.*)
    fun update_name_space (new_trm_occ: name_subspace) IDTyp_Trm_Occ (Name_Space {trm, rule, numb, ...}    : name_space) = Name_Space {trm = trm,     trm_occ = new_trm_occ, rule = rule,     numb = numb    }
      | update_name_space (new_rule   : name_subspace) IDTyp_Rule    (Name_Space {trm, trm_occ, numb, ...} : name_space) = Name_Space {trm = trm,     trm_occ = trm_occ,     rule = new_rule, numb = numb    }
      | update_name_space (new_numb   : name_subspace) IDTyp_Numb    (Name_Space {trm, trm_occ, rule, ...} : name_space) = Name_Space {trm = trm,     trm_occ = trm_occ,     rule = rule,     numb = new_numb}
      | update_name_space (new_trm    : name_subspace) _             (Name_Space {trm_occ, rule, numb, ...}: name_space) = Name_Space {trm = new_trm, trm_occ = trm_occ,     rule = rule,     numb = numb    }

    fun get_max_id (alist_int:(int * 'a) list) = map fst alist_int
                                              |> sort Int.compare
                                              |> try rev >>=  try hd
                                              |> (fn x => case x of SOME i => i | NONE => 0);

    fun name_subspace_to_fresh_id (sub_space:name_subspace) = get_max_id sub_space |> (curry (op +) 1);

    (*Note that IDTyp_Trm, IDTyp_On, and IDTyp_Arb share name_space.*)
    fun name_space_n_id_typ_to_fresh_id (Name_Space ns:name_space) IDTyp_Trm_Occ = #trm_occ ns |> name_subspace_to_fresh_id
      | name_space_n_id_typ_to_fresh_id (Name_Space ns:name_space) IDTyp_Rule    = #rule ns    |> name_subspace_to_fresh_id
      | name_space_n_id_typ_to_fresh_id (Name_Space ns:name_space) IDTyp_Numb    = #numb ns    |> name_subspace_to_fresh_id
      | name_space_n_id_typ_to_fresh_id (Name_Space ns:name_space) _             = #trm ns     |> name_subspace_to_fresh_id;

    fun get_new_name_subspaces (idx:int) (domain:domain) (old_name_subspace:name_subspace) =
      (*TODO: Double-check if we really have to pass domain around. Each assertion has a fixed domain.*)
      let
        val new_ids      = case domain of
            Dom_Trm     prints => map ID_Trm     prints
          | Dom_Trm_Occ paths  => map ID_Trm_Occ paths
          | Dom_On      prints => map ID_Trm     prints(*Because IDTyp_On shares a name_space with IDTyp_Trm.*)
          | Dom_Arb     prints => map ID_Trm     prints(*Because IDTyp_On shares a name_space with IDTyp_Trm.*)
          | Dom_Rule    rnames => map ID_Rule    rnames
          | Dom_Numb    numb   => map ID_Numb    numb                                     : ids;
        val new_name_subspace  = map (pair idx) new_ids                                   : name_subspace;
        val new_name_subspaces = map (Utils.alist_add old_name_subspace) new_name_subspace: name_subspaces;
      in
        new_name_subspaces: name_subspaces
      end;

    fun is_nth_arg_of_induct_method (assrt:assrt) (trm:trm) (nth_numb:numb) (name_space:name_space) =
      let
        val numb                     = name_space_n_numb_id_to_integer name_space nth_numb: int option;
        fun get_print_option (Is_Nth_Ind _) = numb >>= try (nth ons ) <$> dest_induct_on  : print option
          | get_print_option (Is_Nth_Arb _) = numb >>= try (nth arbs) <$> dest_induct_arb : print option
          | get_print_option  _             = NONE                                        : print option;
        val nth_print_option = get_print_option assrt                                     : print option;
        val trm_print_option = name_space_n_trm_id_to_print name_space trm                : print option;
        val tobe_compared    = Utils.mk_option_pair (nth_print_option, trm_print_option)  : (print * print) option;
        val result_option    = tobe_compared <$> uncurry same_prints                      : bool option;
        val result           = Utils.is_some_true result_option                           : bool;
      in
        result
      end;

    fun name_space_n_trm_occ_are_node_typ_of (name_space:name_space) (trm_occ:trm_occ) (node_typ:UN.node_typ) =
      let
        val node_option   = name_space_n_trm_occ_id_to_node name_space trm_occ: UN.node option;
        val result_option = node_option <$> UN.node_typ_to_checker node_typ   : bool option;
        val result        = Utils.is_some_true result_option                  : bool;
      in
        result
      end;

    val _ = tracing "Before calling the mutual recursive function in eval.";

    fun eval'_quantifier' (inner:assrt) (index:int) (name_space:name_space) (name_subspace:name_subspace) (quantifier:quantifier) (domain: domain) (add_typ:id_typ) =
      let
        val new_trm_entries_in_name_space        = get_new_name_subspaces index domain name_subspace     : name_subspaces;
        fun get_new_name_space new_name_subspace = update_name_space new_name_subspace add_typ name_space: name_space;
        val new_name_spaces                      = map get_new_name_space new_trm_entries_in_name_space  : name_spaces;
      in
        quantifier (eval' inner) new_name_spaces
      end
    and eval'_in_imp (trm_occ:trm_occ) (name_space:name_space) (nth_arg:int) =
        let
          val fresh_trm_occ_id = name_space_n_id_typ_to_fresh_id name_space IDTyp_Trm_Occ: int;
          val fresh_numb_id    = name_space_n_id_typ_to_fresh_id name_space IDTyp_Numb      : int;
          val meta_imp_occ     = Trm_Occ fresh_trm_occ_id                                   : trm_occ;
          val premise_occ      = Trm_Occ (fresh_trm_occ_id + 1)                             : trm_occ;
          val nth_arg_numb     = Numb fresh_numb_id                                         : numb;
          val desugared = Some_Trm_Occ (meta_imp_occ,
                              Is_Const_Of_Name (meta_imp_occ, "Pure.imp")
                            And
                              Some_Trm_Occ (premise_occ,
                                For_Numb_N (nth_arg_numb, nth_arg,
                                    Is_Nth_Arg_Of (premise_occ, nth_arg_numb, meta_imp_occ)
                                  And
                                    Is_In_Trm_Str (trm_occ, premise_occ)
                                )
                              )
                          );
        in eval' desugared name_space end
    (*code re-factoring using mutual recursion*)
    and
      (** eval' is the core function of LiFtEr's interpreter. **)
      (*Note that we never modify abs_pst_w_aux or name_domains.*)
      (*quantifiers*)
        eval' (All_Ind      (Trm     i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#trm  name_space) forall on_domain   IDTyp_On
      | eval' (All_Arb      (Trm     i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#trm  name_space) forall arb_domain  IDTyp_Arb
      | eval' (All_Trm      (Trm     i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#trm  name_space) forall trm_domain  IDTyp_Trm
      | eval' (All_Rule     (Rule    i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#rule name_space) forall rule_domain IDTyp_Rule
      | eval' (All_Numb     (Numb    i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#numb name_space) forall numb_domain IDTyp_Numb
      | eval' (Some_Ind     (Trm     i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#trm  name_space) exists on_domain   IDTyp_On
      | eval' (Some_Arb     (Trm     i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#trm  name_space) exists arb_domain  IDTyp_Arb
      | eval' (Some_Trm     (Trm     i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#trm  name_space) exists trm_domain  IDTyp_Trm
      | eval' (Some_Rule    (Rule    i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#rule name_space) exists rule_domain IDTyp_Rule
      | eval' (Some_Numb    (Numb    i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#numb name_space) exists numb_domain IDTyp_Numb
      (*quantifiers for occurrences*)
      | eval' (All_Trm_Occ  (Trm_Occ i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#trm_occ name_space) forall trm_occ_domain IDTyp_Trm_Occ
      | eval' (Some_Trm_Occ (Trm_Occ i, inner)) (NS as Name_Space name_space: name_space) = eval'_quantifier' inner i NS (#trm_occ name_space) exists trm_occ_domain IDTyp_Trm_Occ
      (*combinators*)
      | eval' (assrt1 And assrt2) name_space = eval' assrt1 name_space andalso eval' assrt2 name_space
      | eval' (assrt1 Or  assrt2) name_space = eval' assrt1 name_space orelse  eval' assrt2 name_space
      | eval' (Not assrt)            name_space = not (eval' assrt name_space)
      | eval'  True _ = true
      | eval' (assrt1 Imply assrt2) name_space =
          if   eval' assrt1 name_space
          then eval' assrt2 name_space
          else true
      | eval' (Is_Rule_Of (Rule rule_id:rule, trm_occ)) (Name_Space ns:name_space) =
        let
          val rule_name_subspace_option = try #rule ns: name_subspace option;
          val rule_id_option            = rule_name_subspace_option <$> AList.lookup (op =) <*> SOME rule_id |> Option.join: id option;
          val rule_name_option          = rule_id_option >>= dest_ID_Rule                                                  : rule_name option;
          val rule_name_string_option   = rule_name_option >>= dest_Rule_Name                                              : string option;
          val trm_occ_cname_option      = name_space_n_trm_occ_id_to_cname (Name_Space ns) trm_occ                         : string option;
          val option_pair               = Utils.mk_option_pair (trm_occ_cname_option, SOME ".induct")                      : (string * string) option;
          val trm_occ_rule_option       = option_pair <$> (op ^): string option;
          val result                    = opt_equal (trm_occ_rule_option, rule_name_string_option);
        in
          result
        end
      | eval' (Trm_Occ_Is_Of_Trm (trm_occ:trm_occ, Trm trm_id:trm)) (ns as Name_Space {trm, ...}:name_space) =
        let
          val trm_id_option      = AList.lookup (op =) trm trm_id                  : id option;
          val trm_print_option   = trm_id_option >>= dest_ID_Trm                   : print option;
          val trm_path_n_locs    = trm_print_option
                                  >>= try (TT.lifter_pst_n_print_to_path_n_locs lifter_pst)
                                   |> these                                        : path_n_locs;
          val trm_occ_path_n_loc = name_space_n_trm_occ_id_to_path_n_loc ns trm_occ: path_n_loc option;
          val euqals_occ_path_n_loc = trm_occ_path_n_loc <$> same_path_n_loc       :(path * location -> bool) option;
          val result                = euqals_occ_path_n_loc
                                  <$> Utils.flip exists trm_path_n_locs
                                   |> Utils.is_some_true                           : bool;
        in
          result
        end
      | eval' (Are_Same_Numb (Numb n1, Numb n2)) (Name_Space ns:name_space) =
        let
          val numb_name_space = #numb ns                                           : name_subspace;
          val numb1_option    = alist_lookup_eq numb_name_space n1 >>= dest_ID_Numb: int option;
          val numb2_option    = alist_lookup_eq numb_name_space n2 >>= dest_ID_Numb: int option;
          val result          = opt_equal (numb1_option, numb2_option)             : bool;
        in
          result
        end
      | eval' (Are_Same_Str (trm_occ1, trm_occ2)) (name_space:name_space) =
        let
          val occ1_occ2_path_n_loc_option  = Utils.mapPartial2 (name_space_n_trm_occ_id_to_path_n_loc name_space) (SOME (trm_occ1, trm_occ2)): (path_n_loc * path_n_loc) option;
          val occ1_occ2_print_option       = Utils.mapPartial2 path_n_loc_to_print occ1_occ2_path_n_loc_option                               : (UN.print * UN.print) option;
          val result_option                = occ1_occ2_print_option <$> uncurry same_prints                                                  : bool option;
          val result                       = Utils.is_some_true result_option                                                                : bool;
        in
          result
        end
      | eval' (Is_In_Trm_Loc (trm_occ1, trm_occ2)) (name_space:name_space) =
        let
          val occ1_occ2_path_n_loc_option = Utils.mapPartial2 (name_space_n_trm_occ_id_to_path_n_loc name_space) (SOME (trm_occ1, trm_occ2)): (path_n_loc * path_n_loc) option;
          val occ1_occ2_path_option       = occ1_occ2_path_n_loc_option <$> apply2 fst                                                      : (path * path) option;
          val occ1_occ2_loc_option        = occ1_occ2_path_n_loc_option <$> apply2 snd                                                      : (location * location) option;
          val path1_is_under_path2_option = occ1_occ2_path_option <$> uncurry UN.path1_is_above_path2                                       : bool option;
          val loc1_n_loc2_are_same        = occ1_occ2_loc_option <$> TT.same_location                                                       : bool option;
          val result_pair                 = Utils.mk_option_pair (path1_is_under_path2_option, loc1_n_loc2_are_same)                        : (bool * bool) option;
          val result                      = result_pair <$> (op =) |> Utils.is_some_true                                                    : bool;
        in
          result
        end
      | eval' (Is_In_Trm_Str (trm_occ1, trm_occ2)) (name_space:name_space) =
        let
          val occ1_occ2_path_n_loc_option  = Utils.mapPartial2 (name_space_n_trm_occ_id_to_path_n_loc name_space) (SOME (trm_occ1, trm_occ2)): (path_n_loc * path_n_loc) option;
          val occ1_occ2_print_option       = Utils.mapPartial2 path_n_loc_to_print occ1_occ2_path_n_loc_option                               : (UN.print * UN.print) option;
          val result_option                = occ1_occ2_print_option <$> uncurry is_subprint_of                                               : bool option;
          val result                       = Utils.is_some_true result_option                                                                : bool;
          val _ = tracing (if is_none result_option then "None" else "Some");
          val _ = tracing (if result then "result is True" else "result is False");
        in
          result
        end
      | eval' (Is_Typ (trm_occ:trm_occ, hol_typ:hol_typ)) (name_space:name_space) =
        let
          fun is_hol_typ_of Fun_Typ  (typ:typ) = Isabelle_Utils.is_fun_typ  typ
            | is_hol_typ_of List_Typ (typ:typ) = Isabelle_Utils.is_list_typ typ
            | is_hol_typ_of Nat_Typ  (typ:typ) = Isabelle_Utils.is_nat_typ  typ
            | is_hol_typ_of Int_Typ  (typ:typ) = Isabelle_Utils.is_int_typ  typ
            | is_hol_typ_of Set_Typ  (typ:typ) = Isabelle_Utils.is_set_typ  typ;
          val node_option     = name_space_n_trm_occ_id_to_node name_space trm_occ: UN.node option;
          val atomic_node_typ = node_option >>= UN.node_to_atoms_typ: typ option;
          val result          = atomic_node_typ <$> is_hol_typ_of hol_typ |> Utils.is_some_true: bool;
        in result
        end
      | eval' (Is_In_Chained (trm_occ:trm_occ)) (name_space:name_space) =
        let
          val trm_occ_path_n_loc_option = name_space_n_trm_occ_id_to_path_n_loc name_space trm_occ        : path_n_loc option;
          val trm_occ_loc_option        = trm_occ_path_n_loc_option <$> snd: location option              : location option;
          val result                    = trm_occ_loc_option <$> TT.in_chained_facts |> Utils.is_some_true: bool;
        in
          result
        end
      | eval' (Is_In_Fst_Subg (trm_occ:trm_occ)) (name_space:name_space) =
        let
          val trm_occ_path_n_loc_option = name_space_n_trm_occ_id_to_path_n_loc name_space trm_occ   : path_n_loc option;
          val trm_occ_loc_option        = trm_occ_path_n_loc_option <$> snd: location option         : location option;
          val result                    = trm_occ_loc_option <$> TT.in_subgoals |> Utils.is_some_true: bool;
        in
          result
        end
      | eval' (Is_In_Prems  (trm_occ:trm_occ)) (name_space:name_space) = eval'_in_imp trm_occ name_space 1(*TODO:FIXME: not always true*)
      | eval' (Is_In_Cnclsn (trm_occ:trm_occ)) (name_space:name_space) = eval'_in_imp trm_occ name_space 2(*TODO:FIXME: not always true*)
      | eval' (Is_Const_Of_Name (trm_occ, const_name:string)) (name_space:name_space) =
        let
          val cname_option = name_space_n_trm_occ_id_to_cname name_space trm_occ: string option;
          val result       = opt_equal (cname_option, SOME const_name)          : bool;
        in
          result
        end
      | eval' (Is_Cnst   trm_occ) (name_space:name_space) = name_space_n_trm_occ_are_node_typ_of name_space trm_occ UN.Node_Typ_NC
      | eval' (Is_Var    trm_occ) (name_space:name_space) = name_space_n_trm_occ_are_node_typ_of name_space trm_occ UN.Node_Typ_NV
      | eval' (Is_Free   trm_occ) (name_space:name_space) = name_space_n_trm_occ_are_node_typ_of name_space trm_occ UN.Node_Typ_NF
      | eval' (Is_Bound  trm_occ) (name_space:name_space) = name_space_n_trm_occ_are_node_typ_of name_space trm_occ UN.Node_Typ_NB
      | eval' (Is_Lambda trm_occ) (name_space:name_space) = name_space_n_trm_occ_are_node_typ_of name_space trm_occ UN.Node_Typ_NL
      | eval' (Is_App    trm_occ) (name_space:name_space) = name_space_n_trm_occ_are_node_typ_of name_space trm_occ UN.Node_Typ_NA
      | eval' (Not_Fully_App trm_occ) (name_space:name_space) =
        let
          val trm_occ_path_n_loc_option = name_space_n_trm_occ_id_to_path_n_loc name_space trm_occ        : path_n_loc option;
          val trm_occ_path_option       = trm_occ_path_n_loc_option <$> fst: path option                  : path option;
          val trm_occ_loc_option        = trm_occ_path_n_loc_option <$> snd: location option              : location option;
          val trm_occ_node              = trm_occ_path_n_loc_option >>= path_n_loc_to_node                : UN.node option;
          val is_NA                     = trm_occ_node <$> UN.is_NA |> Utils.is_some_true                 : bool;
          val func_path_option          = Utils.mk_option_pair (trm_occ_path_option, SOME [0]) <$> List.@ : path option;
          val func_path_loc_option      = Utils.mk_option_pair (func_path_option, trm_occ_loc_option)     : path_n_loc option;
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
      | eval' (Is_Less_Than (Numb numb1, Numb numb2)) (Name_Space nspace:name_space) =
        let
          val numb_name_space      = #numb nspace                                         : name_subspace;
          fun get_numb_option numb = alist_lookup_eq numb_name_space numb >>= dest_ID_Numb: int option;
          val numb1_option         = get_numb_option numb1                                : int option;
          val numb2_option         = get_numb_option numb2                                : int option;
          val numbs_option         = Utils.mk_option_pair (numb1_option, numb2_option)    : (int * int) option;
          val result_option        = numbs_option <$> Int.>                               : bool option;
          val result               = Utils.is_some_true result_option                     : bool;
        in
          result
        end
      | eval' (Is_Nth_Arg_Of (func:trm_occ, Numb numb:numb, arg:trm_occ)) (name_space as Name_Space nspace) =
        let
          val path_n_loc_of_func_option      = name_space_n_trm_occ_id_to_path_n_loc name_space func               : path_n_loc option;
          val path_n_loc_of_arg_option       = name_space_n_trm_occ_id_to_path_n_loc name_space arg                : path_n_loc option;
          val numb_name_space                = #numb nspace                                                        : name_subspace;
          val numb_option                    = alist_lookup_eq numb_name_space numb >>= dest_ID_Numb               : int option;
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
      | eval' (assrt as Is_Nth_Ind (trm:trm, numb)) (name_space:name_space) = is_nth_arg_of_induct_method assrt trm numb name_space (*Counting starts with 0.*)
      | eval' (assrt as Is_Nth_Arb (trm:trm, numb)) (name_space:name_space) = is_nth_arg_of_induct_method assrt trm numb name_space (*Counting starts with 0.*)
      | eval' (Is_Int  (Numb numb, int:int)) (name_space:name_space) =
        let
          val numb_option         = name_space_n_numb_id_to_integer name_space (Numb numb): int option;
          val are_same_int_option = opt_equal (numb_option, SOME int)                     : bool;
        in
         are_same_int_option
        end
      | eval' (Is_At_Depth (trm_occ:trm_occ, numb:numb)) (name_space:name_space) =
        let
          val path_n_loc_option        = name_space_n_trm_occ_id_to_path_n_loc name_space trm_occ: path_n_loc option;
          val (path_option, _)         = Utils.mk_options_pair path_n_loc_option              : (path option * location option);
          val trm_occs_depth_option    = path_option <$> length: int option                   : int option;
          val int_at_numb_option       = name_space_n_numb_id_to_integer name_space numb      : int option;
          val are_same_int_option      = opt_equal (trm_occs_depth_option, int_at_numb_option): bool;
        in
          are_same_int_option
        end
      | eval' (Is_Printed_As (trm:trm, string:string)) (name_space:name_space) =
        let
          val print_option        = name_space_n_trm_id_to_print name_space trm : print option;
          val print_string_option = print_option <$> dest_print                 : string option;
          val result              = opt_equal (print_string_option, SOME string): bool;
        in
          result
        end
      | eval' (Pattern (Numb numb:numb, trm_occ:trm_occ, pttrn:pattern)) (name_space as Name_Space nspace:name_space) =
        let
          val numb_name_space      = #numb nspace                                         : name_subspace;
          fun get_numb_option numb = alist_lookup_eq numb_name_space numb >>= dest_ID_Numb: int option;(*TODO: remove code-duplication with other clauses.*)
          val numb_option          = get_numb_option numb                                 : int option;
          val cname_option         = name_space_n_trm_occ_id_to_cname name_space trm_occ  : string option;
          val input_pair_option    = Utils.mk_option_pair (cname_option, numb_option)     : (string * int) option;
          val result_option        = case pttrn of
            All_Only_Var => Option.map (uncurry (is_nth_all_Only_Var ctxt)) input_pair_option: bool option
          | All_Const    => Option.map (uncurry (is_nth_all_Only_Var ctxt)) input_pair_option: bool option
          | Mixed        => SOME true;
        in is_some result_option end (*TODO: improve this clause.*)
      (*syntax sugars*)
      | eval' (Is_Atom trm_occ)                                  (name_space:name_space) = eval' (Is_Cnst trm_occ Or Is_Free trm_occ Or Is_Bound trm_occ)   name_space
      | eval' (Are_Diff_Numb (numb1, numb2))                     (name_space:name_space) = eval' (Not (Are_Same_Numb (numb1, numb2)))                                name_space
      | eval' (Are_Diff_Str  (trm_occ1, trm_occ2))               (name_space:name_space) = eval' (Not (Are_Same_Str (trm_occ1, trm_occ2)))                     name_space
      | eval' (Has_Typ       (trm_occ:trm_occ, hol_typ:hol_typ)) (name_space:name_space) =
        let
          val desugared_assert = ();
        in
          (*TODO*)true
        end
      | eval' (Is_At_Deepest (trm_occ:trm_occ)) (name_space:name_space) =
        (* TODO:
         * Treat Is_At_Deepest as a syntactic sugar for something based on Is_At_Depth, Some_Trm_Occ, and Not.
         * We can introduce a new quantifier safely without polluting name_space for other (inner) assertions
         * because Is_At_Deepest is an atomic assertion.*)
        let
          val path_n_loc_option         = name_space_n_trm_occ_id_to_path_n_loc name_space trm_occ: path_n_loc option;
          val (path_option, loc_option) = Utils.mk_options_pair path_n_loc_option                       : (path option * location option);
          val trm_occs_depth_option     = path_option <$> length: int option                            : int option;
          val one_term_option           = loc_option <$> TT.lifter_pst_n_loc_to_one_term lifter_pst     : TT.one_term option;
          val unode_aux_table_option    = one_term_option <$> #path_to_unode_aux_table                  : TT.path_to_unode_aux_table option;
          val maximum_depth_option      = unode_aux_table_option >>= TT.path_to_unode_aux_table_to_depth: int option;
          val result                    = opt_equal (trm_occs_depth_option, maximum_depth_option)       : bool;
        in
          result
        end
      | eval' (Is_More_Than   (numb1:numb, numb2:numb))          (name_space:name_space) = eval' (Not (Is_Less_Than (numb1, numb2)) And Not (Are_Same_Numb (numb1, numb2))) name_space
      | eval' (For_Numb_N     (numb:numb, int:int, inner:assrt)) (name_space:name_space) = eval' (Some_Numb (numb, Is_Int (numb, int) And inner))                          name_space
      | eval' (All_Trm_Occ_Of (trm_occ, trm, assrt)) (name_space:name_space) =
        eval' (All_Trm_Occ    (trm_occ,
                                  Trm_Occ_Is_Of_Trm (trm_occ, trm)
                                Imply
                                  assrt)) name_space
      | eval' (Some_Trm_Occ_Of (trm_occ, trm, assrt)) (name_space:name_space) =
        eval' (Some_Trm_Occ (trm_occ,
                                  Trm_Occ_Is_Of_Trm (trm_occ, trm)
                                And
                                  assrt)) name_space
  in
    eval' assert empty_name_space
  end;

end;