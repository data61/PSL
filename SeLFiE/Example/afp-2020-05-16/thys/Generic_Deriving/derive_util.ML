signature DERIVE_UTIL =
sig
  type ctr_info = (string * (string * typ list) list) list

  type rep_type_info =
    {repname : string,
     rep_type : typ,
     tFrees_mapping : (typ * typ) list,
     from_info : Function_Common.info option,
     to_info : Function_Common.info option}

  type comb_type_info =
    {combname : string,
     combname_full : string,
     comb_type : typ,
     ctr_type : typ,
     inConst : term,
     inConst_free : term,
     inConst_type : typ,
     rep_type_instantiated : typ}

  type type_info =
     {tname : string,
     uses_metadata : bool,
     tfrees : (typ * sort) list,
     mutual_tnames : string list,
     mutual_Ts : typ list,
     mutual_ctrs : ctr_info,
     mutual_sels : (string * string list list) list,
     is_rec : bool,
     is_mutually_rec : bool,
     rep_info : rep_type_info,
     comb_info : comb_type_info option,
     iso_thm : thm option}

  type class_info =
    {classname : string,
     class : sort,
     params : (class * (string * typ)) list option,
     class_law : thm option,
     class_law_const : term option,
     ops : term list option,
     transfer_law : (string * thm list) list option,
     axioms : thm list option,
     axioms_def : thm option,
     class_def : thm option,
     equivalence_thm : thm option}

  type instance_info =
    {defs : thm list}

  val is_typeT : typ -> bool
  val insert_application : term -> term -> term
  val add_tvars : string -> string list -> string
  val replace_tfree : string list -> string -> string -> string
  val ctrs_arguments : ctr_info -> typ list
  val collect_tfrees : ctr_info -> (typ * sort) list
  val collect_tfree_names : ctr_info -> string list
  val combs_to_list : term -> term list
  val get_tvar : typ list -> typ
  val not_instantiated : theory -> string -> class -> bool
  (* version of add_fun that doesn't throw away info *)
  val add_fun' : (binding * typ option * mixfix) list ->
    Specification.multi_specs -> Function_Common.function_config ->
    local_theory -> (Function_Common.info * Proof.context)
  val add_conversion_info : Function_Common.info -> Function_Common.info -> type_info -> type_info
  val add_iso_info : thm option -> type_info -> type_info
  val has_class_law : string -> theory -> bool
  val zero_tvarsT : typ -> typ
  val zero_tvars : term -> term
  val get_superclasses : sort -> string -> theory -> string list
  val tagged_function_termination_tac : Proof.context -> Function.info * local_theory
  val get_mapping_function : Proof.context -> typ -> term
  val is_polymorphic : typ -> bool

  (* determines all mutual recursive types of a given BNF-least-fixpoint-type *)
  val mutual_recursive_types : string -> Proof.context -> string list * typ list
  val freeify_tvars : typ -> typ
  (* delivers a full type from a type name by instantiating the type-variables of that
   type with different variables of a given sort, also returns the chosen variables
   as second component *)
  val typ_and_vs_of_typname : theory -> string -> sort -> typ * (string * sort) list

  val constr_terms : Proof.context -> string -> term list
end

structure Derive_Util : DERIVE_UTIL =
struct

type ctr_info = (string * (string * typ list) list) list

type rep_type_info =
  {repname : string,
   rep_type : typ,
   tFrees_mapping : (typ * typ) list,
   from_info : Function_Common.info option,
   to_info : Function_Common.info option}

type comb_type_info =
  {combname : string,
   combname_full : string,
   comb_type : typ,
   ctr_type : typ,
   inConst : term,
   inConst_free : term,
   inConst_type : typ,
   rep_type_instantiated : typ}

type type_info =
  {tname : string,
   uses_metadata : bool,
   tfrees : (typ * sort) list,
   mutual_tnames : string list,
   mutual_Ts : typ list,
   mutual_ctrs : ctr_info,
   mutual_sels : (string * string list list) list,
   is_rec : bool,
   is_mutually_rec : bool,
   rep_info : rep_type_info,
   comb_info : comb_type_info option,
   iso_thm : thm option}

type class_info =
    {classname : string,
     class : sort,
     params : (class * (string * typ)) list option,
     class_law : thm option,
     class_law_const : term option,
     ops : term list option,
     transfer_law : (string * thm list) list option,
     axioms : thm list option,
     axioms_def : thm option,
     class_def : thm option,
     equivalence_thm : thm option}

type instance_info =
    {defs : thm list}

val is_typeT = fn (Type _) => true | _ => false

fun insert_application (t1 $ t2) t3 = insert_application t1 (insert_application t2 t3) |
    insert_application t         t3 = t $ t3

fun add_tvars tname tvar_names =
      let
        fun zip_tvars [] = "" |
            zip_tvars [x] = x |
            zip_tvars (x::xs) = x ^ ", " ^ (zip_tvars xs)
      in
        case tvar_names of [] => tname | xs => "(" ^ zip_tvars xs ^ ") " ^ tname
      end

(* replace tfree by replacement_name if it occurs in tfree_names *)
fun replace_tfree tfree_names replacement_name tfree =
  (case List.find (curry (op =) tfree) tfree_names
        of SOME _ => replacement_name
         | NONE => tfree)

(* Operations on constructor information *)
val ctrs_arguments = (map (fn l => map snd (snd l))) #> flat #> flat
fun collect_tfrees ctrs = map (fn (t,s) => (TFree (t,s),s))
                              (fold Term.add_tfreesT (ctrs_arguments ctrs) [])
fun collect_tfree_names ctrs = fold Term.add_tfree_namesT (ctrs_arguments ctrs) []

fun not_instantiated thy tname class =
  null (Thm.thynames_of_arity thy (tname, class))

fun combs_to_list t =
  let
    fun
      combs_to_list_aux (t1 $ t2) = t2 :: (combs_to_list_aux t1) |
      combs_to_list_aux t = [t]
  in
    rev (combs_to_list_aux t)
  end

fun get_tvar ts =
  case ts of
    [] => TFree ("'a", \<^sort>\<open>type\<close>) |
    (t::ts) =>
      case t of T as TFree _ => T |
                Type (_,xs) => get_tvar (xs@ts) |
                _ => get_tvar ts

fun add_fun' binding specs config lthy =
  let
    fun pat_completeness_auto ctxt =
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt
    fun prove_termination lthy =
      Function.prove_termination NONE (Function_Common.termination_prover_tac false lthy) lthy
  in
    lthy |>
    (Function.add_function binding specs config) pat_completeness_auto |> snd
    |> prove_termination
  end

fun add_conversion_info from_info to_info (ty_info : type_info) =
  let
    val {tname, uses_metadata, tfrees,  mutual_tnames, mutual_Ts, mutual_ctrs, mutual_sels, is_rec, is_mutually_rec, rep_info, comb_info, iso_thm} = ty_info
    val {repname, rep_type, tFrees_mapping, ...} = rep_info
  in
   {tname = tname, uses_metadata = uses_metadata, tfrees = tfrees,  mutual_tnames = mutual_tnames, mutual_Ts = mutual_Ts,
    mutual_ctrs = mutual_ctrs, mutual_sels = mutual_sels, is_rec = is_rec, is_mutually_rec = is_mutually_rec,
    rep_info = {repname = repname, rep_type = rep_type, tFrees_mapping = tFrees_mapping, from_info = SOME from_info, to_info =  SOME to_info}
    , comb_info = comb_info, iso_thm = iso_thm} : type_info
  end
fun add_iso_info iso_thm (ty_info : type_info) =
  let
    val {tname, uses_metadata, tfrees,  mutual_tnames, mutual_Ts, mutual_ctrs, mutual_sels, is_rec, is_mutually_rec, rep_info, comb_info, ...} = ty_info
  in
   {tname = tname, uses_metadata = uses_metadata, tfrees = tfrees,  mutual_tnames = mutual_tnames, mutual_Ts = mutual_Ts,
    mutual_ctrs = mutual_ctrs, mutual_sels = mutual_sels, is_rec = is_rec, is_mutually_rec = is_mutually_rec,
    rep_info = rep_info, comb_info = comb_info, iso_thm = iso_thm} : type_info
  end

fun has_class_law classname thy =
let
  val class = Syntax.parse_sort (Proof_Context.init_global thy) classname |> hd
in
  is_some (Class.rules thy class |> fst)
end

fun
  zero_tvarsT (Type (s,ts)) = Type (s, map zero_tvarsT ts) |
  zero_tvarsT (TVar ((n,_),s)) = TVar ((n,0),s) |
  zero_tvarsT T = T

fun zero_tvars t = map_types zero_tvarsT t

fun
  unique [] = [] |
  unique (x::xs) =
      let fun remove (_,[]) = []
            | remove (x,y::ys) = if x = y
                                      then remove(x,ys)
                                      else y::remove(x,ys)
      in
        x::unique(remove(x,xs))
      end

fun get_superclasses class classname thy =
let
  val all_classes = (Class.these_params thy class) |> map (snd #> fst)
  val superclasses = filter (curry (op =) classname #> not) all_classes
in
  unique superclasses
end

fun tagged_function_termination_tac ctxt =
  let
    val prod_simp_thm = @{thm size_tagged_prod_simp}
    fun measure_tac ctxt = Function_Relation.relation_infer_tac ctxt
      ((Const (\<^const_name>\<open>measure\<close>,dummyT)) $ (Const (\<^const_name>\<open>size\<close>,dummyT)))
    fun prove_termination ctxt = auto_tac (Simplifier.add_simp prod_simp_thm ctxt)
  in
    Function.prove_termination NONE ((HEADGOAL (measure_tac ctxt)) THEN (prove_termination ctxt)) ctxt
  end

fun get_mapping_function lthy T =
let
  val map_thms = BNF_GFP_Rec_Sugar.map_thms_of_type lthy T
  val map_const = Thm.full_prop_of (hd map_thms) |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
                  |> strip_comb |> fst |> dest_Const |> apsnd (K dummyT) |> Const
in
  map_const
end

fun is_polymorphic T = not (null (Term.add_tfreesT T []))

(* Code copied from generator_aux.ML in AFP entry Deriving by Sternagel and Thiemann *)

fun typ_and_vs_of_typname thy typ_name sort =
  let
    val ar = Sign.arity_number thy typ_name
    val sorts = map (K sort) (1 upto ar)
    val ty_vars = Name.invent_names (Name.make_context [typ_name]) "a" sorts
    val ty = Type (typ_name,map TFree ty_vars)
  in (ty,ty_vars) end

val freeify_tvars = map_type_tvar (TFree o apfst fst)

fun mutual_recursive_types tyco lthy =
      (case BNF_FP_Def_Sugar.fp_sugar_of lthy tyco of
        SOME sugar =>
          if Sign.arity_number (Proof_Context.theory_of lthy) tyco -
            BNF_Def.live_of_bnf (#fp_bnf sugar) > 0
          then error "only datatypes without dead type parameters are supported"
          else if #fp sugar = BNF_Util.Least_FP then
            sugar |> #fp_res |> #Ts |> `(map (fst o dest_Type))
            ||> map freeify_tvars
          else error "only least fixpoints are supported"
      | NONE => error ("type " ^ quote tyco ^ " does not appear to be a new style datatype"))

(* Code copied from bnf_access.ML in AFP entry Deriving by Sternagel and Thiemann *)

fun constr_terms lthy = BNF_FP_Def_Sugar.fp_sugar_of lthy
  #> the #> #fp_ctr_sugar #> #ctr_sugar #> #ctrs

end

structure Type_Data = Theory_Data
(
  type T = Derive_Util.type_info Symreltab.table;
  val empty = Symreltab.empty;
  val extend = I;
  fun merge data : T = Symreltab.merge (K true) data;
);

structure Class_Data = Theory_Data
(
  type T = Derive_Util.class_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

structure Instance_Data = Theory_Data
(
  type T = Derive_Util.instance_info Symreltab.table;
  val empty = Symreltab.empty;
  val extend = I;
  fun merge data : T = Symreltab.merge (K true) data;
);