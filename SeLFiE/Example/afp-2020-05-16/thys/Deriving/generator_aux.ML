(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)
signature GENERATOR_AUX =
sig
  val alist_to_string : (string * 'a)list -> string

  (* put a string in sub-script *)
  val sub : string -> string

  (* put a type-name in sub-script *)
  val subT : string -> typ -> string

  (* [a,..,n] -> _{a_.._n} *)
  val ints_to_subscript : int list -> string

  (* drop last element of a non-empty list *)
  val drop_last : 'a list -> 'a list

  (* rename old types to new types in term, typ-lists (fst and snd components) are assumed to be distinct *)
  val rename_types : (typ * typ) list -> term -> term

  (* \<lambda> x1 ... xn.t *)
  val lambdas : term list -> term -> term

  (* thm[OF _(NONE) foo (SOME foo) ...] *)
  val OF_option : thm -> thm option list -> thm

  (* aim: treat a possible empty conjunction and handle each subcase
     by a specific tactic (indexed from 0 onwards) *)
  val conjI_tac : thm list ->
    Proof.context -> 'a list -> (Proof.context -> int -> tactic) -> tactic

  (* check whether a given type is of a given sort *)
  val is_class_instance : theory -> string -> sort -> bool

  val mk_case_tac :
    Proof.context ->
    term option list list ->
    thm ->
    (int -> Proof.context * thm list * (string * cterm) list -> tactic) ->
    tactic

  (*type-inference after replacing all schematic type-variables by dummyT*)
  val infer_type : Proof.context -> term -> term

  (* like old prove_multi, but in non-blocking future-verion *)
  val prove_multi_future : Proof.context -> string list -> term list -> term list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> thm list

  (* determines all mutual recursive types of a given BNF-least-fixpoint-type *)
  val mutual_recursive_types : string -> Proof.context -> string list * typ list

  (* a fold over types, differentiating mutual recursive types and other type-constructors *)
  val recursor :
    (string -> 'info) * (* accessing the information of a datatype *)
    ('info -> bool list) * (* which arguments are used of a datatype *)
    string list -> (* information on used arguments and recursive types *)
    bool -> (*recursion over all types (or only used types)*)
    (typ -> 'a) -> (* how to treat TFrees *)
    (typ -> 'a) -> (* how to treat TVars *)
    (typ -> 'a) -> (* how to treat recursive case *)
    ((typ * 'a option) list * 'info -> 'a) -> (* how to treat non-rec.-case; NONE result for unused types, if all = false *)
    typ -> 'a

  (* split global list of induction hypotheses according to list of argument types *)
  val split_IHs : (string -> 'info) * ('info -> bool list) * string list -> typ list -> thm list -> thm list list

  (* a standard tactic to solve proof obligation with recursion on types:
     variables and rec.-cases are handled via IHs and preconditions,
     for non-rec.-type constructors  a partial soundness thm has to be generated from the info *)
  val std_recursor_tac : (string -> 'info) * ('info -> bool list) * string list ->
    typ list ->
    ('info -> thm) ->
    thm list -> typ -> thm list -> Proof.context -> tactic

  (* delivers a full type from a type name by instantiating the type-variables of that
   type with different variables of a given sort, also returns the chosen variables
   as second component *)
  val typ_and_vs_of_typname : theory -> string -> sort -> typ * (string * sort) list

  (* similar to typ_and_vs_of_typname, but only for used types the sort contraint will be enforced *)
  val typ_and_vs_of_used_typname : string -> bool list -> string list -> typ * (string * string list) list

  val freeify_tvars : typ -> typ

  val add_used_tycos : Proof.context -> string -> string list -> string list

  val type_parameters : typ -> Proof.context -> (string * sort) list * typ list

  val define_overloaded : (string * term) -> local_theory -> thm * local_theory

  val define_overloaded_generic : (Attrib.binding * term) -> local_theory -> thm * local_theory

  val mk_id : typ -> term

  val mk_def : typ -> string -> term -> term

  val mk_infer_const : string -> Proof.context -> term -> term

  val ind_case_to_idxs : 'a list list -> int -> int * int

  val create_partial :
    'a ->
    (typ -> bool) ->
    (local_theory -> string -> bool list) ->
    (local_theory -> string -> term) ->
    (local_theory -> string -> 'a -> term) ->
    string list ->
    (local_theory -> string -> 'a) ->
    typ ->
    local_theory -> term

  val create_map :
    (typ -> term) -> (*default operation*)
    (string * typ -> 'a -> term) -> (*recursive occurrences of operation*)
    'a -> (*initial state*)
    (typ -> bool) -> (*early abort*)
    (local_theory -> string -> bool list) -> (*used positions*)
    (local_theory -> string -> term) -> (*map function*)
    (local_theory -> string -> 'a -> term) -> (*partial operation*)
    string list -> (*mutually recursive types*)
    (local_theory -> string -> 'a) -> (*next state function*)
    typ -> (*type for which map should be created*)
    local_theory -> term

end

structure Generator_Aux : GENERATOR_AUX =
struct

fun alist_to_string al = map fst al |> commas |> enclose "(" ")"

fun typ_and_vs_of_used_typname typ_name used_pos sort =
  let
    val sorts = map (fn b => if b then sort else @{sort type}) used_pos
    val ty_vars = Name.invent_names (Name.make_context [typ_name]) "a" sorts
    val ty = Type (typ_name,map TFree ty_vars)
  in
    (ty,ty_vars)
  end

fun is_class_instance thy tname class =
  Sorts.has_instance (Sign.classes_of thy) tname class

fun conjI_tac conj_thms ctxt xs tac =
  if null xs then all_tac
  else
    (K (Method.try_intros_tac ctxt conj_thms [])
    THEN_ALL_NEW (fn k' =>
      Subgoal.SUBPROOF (fn {context = ctxt', ...} => tac ctxt' (k' - 1)) ctxt k'))
    1

fun mk_id T =
  let val x = Free ("x", T)
  in lambda x x end

local
  fun create_gen mk_comp dfun mk_p x early_abort up mfun pfun tycos read T lthy =
    let
      fun create x (T as (Type (tyco, Ts))) =
            if early_abort T then mk_id dummyT
            else if member (op =) tycos tyco then mk_p (tyco, T) x
            else
              let
                val x' = read lthy tyco
                val ts = (up lthy tyco ~~ Ts) |> map (fn (used, T) =>
                  if used then create x' T else dfun dummyT)
              in mk_comp (pfun lthy tyco x, list_comb (mfun lthy tyco, ts)) end
        | create _ _ = mk_id dummyT
    in create x T end
in
  fun create_partial x = create_gen HOLogic.mk_comp mk_id ((K o K) (mk_id dummyT)) x
  fun create_map dfun mk_p x = create_gen snd dfun mk_p x
end

fun drop_last [] = raise Empty
  | drop_last (x::xs) =
      let
        fun init _ [] = []
          | init x (y::ys) = x :: init y ys
      in init x xs end

fun rename_types [] t = t
  | rename_types ((t1, t2) :: ts) t =
      if t1 = t2 then rename_types ts t
      else
        let val swap = [(t1, t2), (t2, t1)]
        in
          rename_types
            (map (apfst (typ_subst_atomic swap)) ts)
            (subst_atomic_types swap t)
        end

fun sub s = Symbol.explode s |> map (fn c => "\<^sub>" ^ c) |> implode

fun subT name T = name ^ sub
      (case T of
        TVar (xi, _) => Term.string_of_vname xi
      | TFree (x, _) => x
      | Type (tyco, _) => tyco)

val ints_to_subscript = sub o foldr1 (fn (x, y) => x ^ "_" ^ y) o map string_of_int

fun ind_case_to_idxs cTys=
  let
    fun number n (i, j) ((_ :: xs) :: ys) = (n, (i, j)) :: number (n+1) (i, j+1) (xs :: ys)
      | number n (i, _) ([] :: ys) = number n (i+1, 0) ys
      | number _ _ [] = []
  in AList.lookup (op =) (number 0 (0, 0) cTys) #> the end

(*recursively compute free type variables that are actually used by a given ((co)data)type, i.e.,
are not (indirect) phantom types.*)
fun add_used_tfrees ctxt =
      let
        val thy = Proof_Context.theory_of ctxt

        fun err_schematic T =
              error ("illegal schematic type variable " ^ quote (Syntax.string_of_typ ctxt T))

        fun add _ (T as TVar _) = err_schematic T
          | add _ (TFree (x, _)) = insert (op =) x
          | add skip (Type (tyco, Ts)) =
              if member (op =) skip tyco then I
              else
                (case BNF_FP_Def_Sugar.fp_sugar_of ctxt tyco of
                  NONE => fold (add skip) Ts
                | SOME _ => (*(co)datatype*)
                  BNF_LFP_Compat.the_spec thy tyco
                  |>> map TFree |>> (fn x => x ~~ Ts) ||> map snd ||> flat
                  |> uncurry (map o typ_subst_atomic)
                  |> fold (add (insert (op =) tyco skip)))
      in add [] end

(*collect all Type(constructor) names occurring in a given type*)
fun add_tycos (Type (tyco, Ts)) = insert (op =) tyco #> fold add_tycos Ts
  | add_tycos _ = I

(*starting from a (co)datatype "tyco", collect all Type(constructor) names that are
involved in its construction*)
fun add_used_tycos ctxt tyco =
      (case BNF_FP_Def_Sugar.fp_sugar_of ctxt tyco of
        NONE => I
      | SOME sugar => #fp_ctr_sugar sugar |> #ctrXs_Tss |> flat |> fold add_tycos)

fun infer_type ctxt =
      map_types (map_type_tvar (K dummyT))
      #> singleton (Type_Infer_Context.infer_types ctxt)

val lambdas = fold_rev lambda

fun mk_def T c rhs = Logic.mk_equals (Const (c, T), rhs)

fun OF_option thm thms = thm OF map (the_default @{lemma "P \<Longrightarrow> P" by simp}) thms

fun typ_and_vs_of_typname thy typ_name sort =
  let
    val ar = Sign.arity_number thy typ_name
    val sorts = map (K sort) (1 upto ar)
    val ty_vars = Name.invent_names (Name.make_context [typ_name]) "a" sorts
    val ty = Type (typ_name,map TFree ty_vars)
  in (ty,ty_vars) end


(* code copied from HOL/SPARK/TOOLS *)
fun define_overloaded_generic (binding,eq) lthy =
  let
    val ((c, _), rhs) = eq |> Syntax.check_term lthy |>
      Logic.dest_equals |>> dest_Free;
    val ((_, (_, thm)), lthy') = Local_Theory.define
      ((Binding.name c, NoSyn), (binding, rhs)) lthy
    val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy');
    val thm' = singleton (Proof_Context.export lthy' ctxt_thy) thm
  in (thm', lthy')
end

fun define_overloaded (name,eq) = define_overloaded_generic ((Binding.name name, @{attributes [code]}),eq)


fun mk_case_tac ctxt insts thm sub_case_tac =
  (DETERM o Induct.cases_tac ctxt false insts (SOME thm) []
  THEN_ALL_NEW (fn i =>
    Subgoal.SUBPROOF (fn {context = ctxt, prems = hyps, params = params, ...} =>
      sub_case_tac (i-1) (ctxt, hyps, params)) ctxt i))
  1

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

fun type_parameters T lthy =
      let
        val tfrees = T |> dest_Type |> snd |> map dest_TFree
        val used_tfrees = (*type parameters of type tyco that are used (maintain original order)*)
          inter (op =) (add_used_tfrees lthy T []) (map fst tfrees)
          |> map (fn a => TFree (a, AList.lookup (op =) tfrees a |> the))
      in (tfrees, used_tfrees) end

fun sum_list xs = fold (curry (op +)) xs 0

fun mk_infer_const name ctxt c = infer_type ctxt (Const (name, dummyT) $ c)

fun prove_multi_future ctxt = Goal.prove_common ctxt (SOME ~1)

fun recursor rec_info all free tvar r typ (T as Type (tyco,Ts)) =
      if member (op =) (#3 rec_info) tyco then r T
      else
        let
          val (get_info,get_used,_) = rec_info
          val info = get_info tyco
          val up = get_used info
          val recs = (if all then map (pair true) Ts else up ~~ Ts) |> map (fn (b, T) =>
            if b then (T, SOME (recursor rec_info all free tvar r typ T)) else (T, NONE))
        in typ (recs, info) end
  | recursor _ _ free _ _ _ (T as TFree _) = free T
  | recursor _ _ _ tvar _ _ (T as TVar _) = tvar T

(* use the recursor to compute the number of IHs, in order to split them *)
fun num_IHs rec_info = recursor rec_info true (K 0) (K 0) (K 1)
      (fn (xs, _) => sum_list (map (the o snd) xs))

fun split_IHs rec_info (ty :: tys : typ list) (IHs : thm list) : thm list list =
      let
        val n = num_IHs rec_info ty
        val _ = if n > length IHs then error "split IH error: too few" else ()
      in
        take n IHs :: split_IHs rec_info tys (drop n IHs)
      end
  | split_IHs _ [] [] = []
  | split_IHs _ [] (_ :: _) = error "split IH error: too many"

fun std_recursor_tac rec_info used_tfrees info_to_pthm assms = recursor rec_info false
      (* TFrees via pre_condition and blast *)
      (fn T => fn IH => fn ctxt =>
          if null IH then
            (resolve_tac ctxt [nth assms (find_index (equal T) used_tfrees)] THEN_ALL_NEW blast_tac ctxt) 1
          else error "error 1 in distributing IHs in recursor_tac")
      (* TVars may not occur *)
      (fn ty => error ("error in recursor_tac for " ^ @{make_string} ty))
      (* recursive case via IH and blast *)
      (K (fn IHs => fn ctxt =>
        if length IHs = 1 then
          (resolve_tac ctxt [hd IHs] THEN_ALL_NEW blast_tac ctxt) 1
        else error "error 2 in distributing IHs in recursor_tac"))
      (* non-rec.-case distributed IHs and invokes partial soundness thm *)
      (fn (tys_tactics, info) => fn IH => fn ctxt =>
        let
          val IHs = split_IHs rec_info (map fst tys_tactics) IH
          val tactics = tys_tactics ~~ IHs |> map_filter (fn ((_, tac_opt), IH) =>
            Option.map (fn f => f IH) tac_opt)
          val pthm = info_to_pthm info
        in
          HEADGOAL (
            resolve_tac ctxt [pthm]
            THEN_ALL_NEW (fn k => Subgoal.SUBPROOF (fn {prems, context = ctxt', ...} =>
              Method.insert_tac ctxt' prems 1
              THEN (nth tactics (k - 1) ctxt')) ctxt k))
        end)

end
