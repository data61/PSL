(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The syntax and interpreter of LiFtEr, Logical Feature Extractor for MiLkMaId.
*)
structure LiFtEr: LIFTER =
struct

type abs_pstate_w_aux = Term_Table.abs_pstate_w_aux;

datatype numb       = Nth         of int;
datatype subtrm     = Sub_Trm     of int;
datatype rule       = Rule        of int;
datatype subtrm_occ = Sub_Trm_Occ of int;
datatype hol_typ    = Fun | List | Nat | Set | Rec;(*commonly used HOL types*)
datatype pattern    = Pttrn (*TODO*)
datatype assrt      =
(*quantifiers*)
  All_Ind        of subtrm * assrt
| All_Arb        of subtrm * assrt
| All_Sub_Trm    of subtrm * assrt
| All_Rule       of rule   * assrt
| All_Nth        of numb   * assrt
| Some_Ind       of subtrm * assrt
| Some_Arb       of subtrm * assrt
| Some_Sub_Trm   of subtrm * assrt
| Some_Rule      of rule   * assrt
| Some_Nth       of numb   * assrt (*n must be smaller than or equal to the argument number of the variable/constant that has the maximum argument number.*)
(*quantifiers for occurrences*)
| All_Sub_Trm_Occ  of subtrm_occ * subtrm * assrt
| Some_Sub_Trm_Occ of subtrm_occ * subtrm * assrt
(*combinators*)
| And            of assrt * assrt
| Or             of assrt * assrt
| Not            of assrt
| Imply          of assrt * assrt
(*atomic about proof goal*)
| Is_Numb_Arg_Of of subtrm_occ * numb * subtrm_occ (*sub-tree-1 is the numb-th argument of sub-tree-2*)
| Are_Same_Nth   of numb       * numb
| Are_Same_Str   of subtrm_occ * subtrm_occ (*subtrm*)
| Is_In_Trm_Loc  of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 location-wise*)
| Is_In_Trm_Str  of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_In_Trm_Sem  of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 string-wise but modulo lambda-abstraction*)
| Is_Typ         of subtrm_occ * typ
| Is_At_Deepest  of subtrm_occ
| Is_In_Chained  of subtrm_occ
| Is_In_Fst_Subg of subtrm_occ
| Is_In_Prems    of subtrm_occ
| Is_In_Cnclsn   of subtrm_occ
| Is_Atom        of subtrm_occ
| Is_Cnst        of subtrm_occ
| Is_Var         of subtrm_occ
| Is_Free        of subtrm_occ
| Is_Bound       of subtrm_occ (*corresponds to Bound in term*)
| Is_Lambda      of subtrm_occ (*lambda abstraction corresponding to Abs in Term*)
| Is_App         of subtrm_occ (*function application corresponding to $ in Term*)
| Not_Fully_App  of subtrm_occ (*If subtrm is function application that is not fully applied returns true, otherwise returns false.*)
| Is_Nth_Arg_Of  of subtrm_occ * numb * subtrm_occ
| Less           of numb       * numb (* nth_1 < nth_2 *)
| Is_Nth_Ind     of subtrm     * numb
| Is_Nth_Arb     of subtrm     * numb
(* TODO: pattern *)
| Pattern        of numb * subtrm * pattern (*In the definition of subtrm, the nth argument has this pattern.*)
(*syntax sugars*)
| All_Ind_Occ    of subtrm_occ * subtrm * assrt (*Probably with All_Ind  and All_Sub_Trm_Occ*)
| All_Arb_Occ    of subtrm_occ * subtrm * assrt (*Probably with All_Arb  and All_Sub_Trm_Occ*)
| Some_Ind_Occ   of subtrm_occ * subtrm * assrt (*Probably with Some_Ind and Some_Sub_Trm_Occ*)
| Some_Arb_Occ   of subtrm_occ * subtrm * assrt (*Probably with Some_Ind and Some_Sub_Trm_Occ*)
| Are_Diff_Nth   of numb       * numb           (*Not & Are_Same_Nth*)
| Are_Diff_Str   of numb       * numb           (*Not & Are_Same_Str*)
| Has_Typ        of subtrm_occ * typ            (*Some_Sub_Trm, Is_In, & Is_Typ*)
| Not_Deepest    of subtrm_occ                  (*Not & Is_At_Deepest*)

datatype rule_name  = Rule_Name of string;
type rule_names     = rule_name list;
type path           = Unique_Node.path;
type paths          = Unique_Node.path  list;
type pathss         = Unique_Node.paths list;

(*TIP: use functions from AList, such as AList.update, for name_space.*)
datatype name_space = Name_Space of
 {subtrm:     (int * paths    ) list,
  subtrm_occ: (int * path     ) list,
  rule:       (int * rule_name) list,
  numb:       (int * int      ) list};

type name_spaces = name_space list;

datatype name_subspace =
  Name_Space_Subtrm     of (int * paths    ) list
| Name_Space_Subtrm_occ of (int * path     ) list
| Name_Space_Rule       of (int * rule_name) list
| Name_Space_Numb       of (int * int      ) list;

datatype name =
  Name_Nth        of numb
| Name_Subtrm     of subtrm
| Name_Rule       of rule
| Name_Subtrm_Occ of subtrm_occ;

datatype name_domains = Name_Domains of
  {ind_domain    : pathss,
   ind_occ_domain: paths,
   arb_domain    : pathss,
   arb_occ_domain: paths,
   subtrm_domain : pathss,
   numb_domain   : ints,
   rule_domain   : rule_names};

datatype name_domain =
  Ind_Domain     of pathss
| Ind_Occ_Domain of paths
| Arb_Domain     of pathss
| Arb_Occ_Domain of paths
| Subtrm_Domain  of pathss
| Rule_Domain    of rule_names;

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

fun eval (Name_Domains name_domains: name_domains, abs_pst_w_aux, assert) = (*TODO*)
  let
    val {ind_domain, ind_occ_domain, arb_domain, arb_occ_domain, subtrm_domain, numb_domain, rule_domain} = name_domains;
    val empty_name_space = Name_Space
       {subtrm     = [],
        subtrm_occ = [],
        rule       = [],
        numb       = []};

    fun alist_add (alist: (int * 'a) list) (key:int, value:'a) = AList.update (op =) (key, value) alist: (int * 'a) list;

    fun update_subtrm_in_name_space (Name_Space {subtrm_occ, rule, numb, ...}: name_space) (new_subtrm: (int * paths) list) =
        Name_Space {subtrm = new_subtrm, subtrm_occ = subtrm_occ, rule = rule, numb = numb}: name_space;

    fun update_subtrm_occ_in_name_space (Name_Space {subtrm, rule, numb, ...}: name_space) (new_subtrm_occ: (int * path) list) =
        Name_Space {subtrm = subtrm, subtrm_occ = new_subtrm_occ, rule = rule, numb = numb}: name_space;

    fun update_rule_in_name_space (Name_Space {subtrm, subtrm_occ, numb, ...}: name_space) (new_rule: (int * rule_name) list) =
        Name_Space {subtrm = subtrm, subtrm_occ = subtrm_occ, rule = new_rule, numb = numb}: name_space;

    fun update_numb_in_name_space (Name_Space {subtrm, subtrm_occ, rule, ...}: name_space) (new_numb: (int * int) list) =
        Name_Space {subtrm = subtrm, subtrm_occ = subtrm_occ, rule = rule, numb = new_numb}: name_space;

    fun get_fields_for_name_spaces (i:int) (domain:'a list) (old_field:(int * 'a) list) =
      let
        val new_field = map (pair i) domain;
      in
        map (alist_add old_field) new_field
      end;

    datatype quantifier = Universal | Existential;

    fun how_to_aggregate (quantifier:quantifier) = case quantifier of Universal => forall | Existential => exists
                                                 :(name_space -> bool) -> name_space list -> bool;
    (*code refactoring using mutual recursion*)
    fun eval'_subtrm_quantifier (assrt:assrt) (index:int) (name_space as Name_Space {subtrm, ...}:name_space) (quantifier:quantifier) (domain: pathss) =
        let
          val new_subtrm_entries_in_name_space       = get_fields_for_name_spaces index domain subtrm         : (int * paths) list list;
          fun get_new_name_space new_subtrm          = update_subtrm_in_name_space name_space new_subtrm      : name_space;
          val new_name_spaces                        = map get_new_name_space new_subtrm_entries_in_name_space: name_spaces;
          fun eval_for_name_spaces (nss:name_spaces) = how_to_aggregate quantifier (eval' assrt) nss          : bool;
        in
          eval_for_name_spaces new_name_spaces
        end
    and eval'_rule_quantifier (assrt:assrt) (index:int) (name_space as Name_Space {rule, ...}:name_space) (quantifier:quantifier) (domain: rule_names) =
        let
          val new_rule_entries_in_name_space         = get_fields_for_name_spaces index domain rule           : (int * rule_name) list list;
          fun get_new_name_space new_rule            = update_rule_in_name_space name_space new_rule          : name_space;
          val new_name_spaces                        = map get_new_name_space new_rule_entries_in_name_space  : name_spaces;
          fun eval_for_name_spaces (nss:name_spaces) = how_to_aggregate quantifier (eval' assrt) nss          : bool;
        in
          eval_for_name_spaces new_name_spaces
        end
    and eval'_nth_quantifier (assrt:assrt) (index:int) (name_space as Name_Space {numb, ...}:name_space) (quantifier:quantifier) (domain: ints) =
        let
          val new_numb_entries_in_name_space         = get_fields_for_name_spaces index domain numb           : (int * int) list list;
          fun get_new_name_space new_numb            = update_numb_in_name_space name_space new_numb          : name_space;
          val new_name_spaces                        = map get_new_name_space new_numb_entries_in_name_space  : name_spaces;
          fun eval_for_name_spaces (nss:name_spaces) = how_to_aggregate quantifier (eval' assrt) nss          : bool;
        in
          eval_for_name_spaces new_name_spaces
        end
    and eval'_subtrm_occ_quantifier (Sub_Trm_Occ occ_idx) (Sub_Trm trm_idx) (assrt:assrt) (name_space as Name_Space {subtrm, subtrm_occ, ...}:name_space) (quantifier:quantifier) =
        let
          (*The domain of sub-term-occurrences depends on which sub-term we consider.*)
          val subtrm_occ_domain                      = AList.lookup (op =) subtrm trm_idx |> these                    : paths(*TODO:better error handling*);
          val new_subtrm_occ_entries_in_name_space   = get_fields_for_name_spaces occ_idx subtrm_occ_domain subtrm_occ:(int * path) list list;
          fun get_new_name_space new_subtrm_occ      = update_subtrm_occ_in_name_space name_space new_subtrm_occ      : name_space;
          val new_name_spaces                        = map get_new_name_space new_subtrm_occ_entries_in_name_space    : name_spaces;
          fun eval_for_name_spaces (nss:name_spaces) = how_to_aggregate quantifier (eval' assrt) nss                  : bool;
        in
          eval_for_name_spaces new_name_spaces
        end
    (*Note that we never modify abs_pst_w_aux or name_domains.*)
    and
      (*quantifiers*)
        eval' (All_Ind      ((Sub_Trm i), inner)) (name_space: name_space) = eval'_subtrm_quantifier inner i name_space Universal   ind_domain
      | eval' (All_Arb      ((Sub_Trm i), inner)) (name_space: name_space) = eval'_subtrm_quantifier inner i name_space Universal   arb_domain
      | eval' (All_Sub_Trm  ((Sub_Trm i), inner)) (name_space: name_space) = eval'_subtrm_quantifier inner i name_space Universal   subtrm_domain
      | eval' (All_Rule     ((Rule    i), inner)) (name_space: name_space) = eval'_rule_quantifier   inner i name_space Universal   rule_domain
      | eval' (All_Nth      ((Nth     i), inner)) (name_space: name_space) = eval'_nth_quantifier    inner i name_space Universal   numb_domain
      | eval' (Some_Ind     ((Sub_Trm i), inner)) (name_space: name_space) = eval'_subtrm_quantifier inner i name_space Existential ind_domain
      | eval' (Some_Arb     ((Sub_Trm i), inner)) (name_space: name_space) = eval'_subtrm_quantifier inner i name_space Existential arb_domain
      | eval' (Some_Sub_Trm ((Sub_Trm i), inner)) (name_space: name_space) = eval'_subtrm_quantifier inner i name_space Existential subtrm_domain
      | eval' (Some_Rule    ((Rule    i), inner)) (name_space: name_space) = eval'_rule_quantifier   inner i name_space Existential rule_domain
      | eval' (Some_Nth     ((Nth     i), inner)) (name_space: name_space) = eval'_nth_quantifier    inner i name_space Existential numb_domain
      (*quantifiers for occurrences*)
      | eval' (All_Sub_Trm_Occ  (subtrm_occ, subtrm, assrt)) (name_space: name_space) = eval'_subtrm_occ_quantifier subtrm_occ subtrm assrt name_space Universal
      | eval' (Some_Sub_Trm_Occ (subtrm_occ, subtrm, assrt)) (name_space: name_space) = eval'_subtrm_occ_quantifier subtrm_occ subtrm assrt name_space Existential
      (*combinators*)
      | eval' (And (assrt1, assrt2)) name_space = eval' assrt1 name_space andalso eval' assrt2 name_space
      | eval' (Or (assrt1, assrt2))  name_space = eval' assrt1 name_space orelse  eval' assrt2 name_space
      | eval' (Not assrt)            name_space = not (eval' assrt name_space)
      | eval' (Imply (assrt1, assrt2)) name_space =
          if   eval' assrt1 name_space
          then eval' assrt2 name_space
          else true
      | eval' _ _  = true (*TODO*)
  in
    eval' assert empty_name_space
  end;

end;