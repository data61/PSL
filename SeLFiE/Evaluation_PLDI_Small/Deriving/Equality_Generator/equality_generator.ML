(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)
signature EQUALITY_GENERATOR =
sig

  type info =
   {map : term,                    (* take % x. x, if there is no map *)
    pequality : term,                  (* partial equality *)
    equality : term,                   (* full equality *)
    equality_def : thm option,         (* definition of equality, important for nesting *)
    map_comp : thm option,         (* compositionality of map, important for nesting *)
    partial_equality_thm : thm,       (* partial version of equality thm *)
    equality_thm : thm,               (* equality acomp \<Longrightarrow> \<dots> \<Longrightarrow> equality (full_comp acomp \<dots>) *)
    used_positions : bool list}

  (* registers @{term equality_of :: "some_type :: linorder equality"}
     where some_type must just be a type without type-arguments *)
  val register_equality_of : string -> local_theory -> local_theory

  val register_foreign_equality :
    typ -> (* type-constant without type-variables *)
    term -> (* equality for type *)
    thm -> (* equality thm for provided equality *)
    local_theory -> local_theory



  val register_foreign_partial_and_full_equality :
    string -> (* long type name *)
    term -> (* map function, should be \<lambda>x. x, if there is no map *)
    term -> (* partial equality of type ('a => order, 'b)ty => ('a,'b)ty => order,
      where 'a is used, 'b is unused *)
    term -> (* (full) equality of type ('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> ('a,'b)ty \<Rightarrow> ('a,'b)ty \<Rightarrow> order,
      where 'a is used, 'b is unused *)
    thm option -> (* comp_def, should be full_comp = pcomp o map acomp ..., important for nesting *)
    thm option -> (* map compositionality, important for nesting *)
    thm -> (* partial eq thm for full equality *)
    thm -> (* full thm: equality a-comp => equality (full_comp a-comp) *)
    bool list -> (*used positions*)
    local_theory -> local_theory

  datatype equality_type = EQ | BNF

  val generate_equalitys_from_bnf_fp :
    string ->                 (* name of type *)
    local_theory ->
    ((term * thm list) list * (* partial equalitys + simp-rules *)
    (term * thm) list) *      (* non-partial equality + def_rule *)
    local_theory

  val generate_equality :
    equality_type ->
    string -> (* name of type *)
    local_theory -> local_theory

  val get_info : Proof.context -> string -> info option

  (* ensures that the info will be available on later requests *)
  val ensure_info : equality_type -> string -> local_theory -> local_theory

end

structure Equality_Generator : EQUALITY_GENERATOR =
struct

open Generator_Aux

datatype equality_type = BNF | EQ

val debug = false
fun debug_out s = if debug then writeln s else ()

val boolT = @{typ bool}
fun compT T = T --> T --> boolT
val orderify = map_atyps (fn T => T --> boolT)
fun pcompT T = orderify T --> T --> boolT

type info =
 {map : term,
  pequality : term,
  equality : term,
  equality_def : thm option,
  map_comp : thm option,
  partial_equality_thm : thm,
  equality_thm : thm,
  used_positions : bool list};

structure Data = Generic_Data (
  type T = info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (fn (info1 : info, info2 : info) => #equality info1 = #equality info2);
);

fun add_info T info = Data.map (Symtab.update_new (T, info))

val get_info = Context.Proof #> Data.get #> Symtab.lookup

fun the_info ctxt tyco =
     (case get_info ctxt tyco of
        SOME info => info
      | NONE => error ("no equality information available for type " ^ quote tyco))

fun declare_info tyco m p c c_def m_comp p_thm c_thm used_pos =
  Local_Theory.declaration {syntax = false, pervasive = false} (fn phi =>
    add_info tyco
     {map = Morphism.term phi m,
      pequality = Morphism.term phi p,
      equality = Morphism.term phi c,
      equality_def = Option.map (Morphism.thm phi) c_def,
      map_comp = Option.map (Morphism.thm phi) m_comp,
      partial_equality_thm = Morphism.thm phi p_thm,
      equality_thm = Morphism.thm phi c_thm,
      used_positions = used_pos})

fun register_foreign_partial_and_full_equality tyco m p c c_def m_comp eq_thm c_thm =
  declare_info tyco m p c c_def m_comp eq_thm c_thm

val mk_equality = mk_infer_const @{const_name equality}
val mk_pequality = mk_infer_const @{const_name pequality}

fun default_comp T = absdummy T (absdummy T @{term True}) (*%_ _. True*)

fun register_foreign_equality T comp comp_thm lthy =
  let
    val tyco = (case T of Type (tyco, []) => tyco | _ => error "expected type constant with no arguments")
    val eq = @{thm equalityD2} OF [comp_thm]
  in
    register_foreign_partial_and_full_equality
      tyco (HOLogic.id_const T) comp comp NONE NONE eq comp_thm [] lthy
  end

fun register_equality_of tyco lthy =
  let
    val (T,_) = typ_and_vs_of_typname (Proof_Context.theory_of lthy) tyco @{sort type}
    val comp = HOLogic.eq_const T
    val comp_thm = Thm.instantiate' [SOME (Thm.ctyp_of lthy T)]
      [] @{thm eq_equality}
  in register_foreign_equality T comp comp_thm lthy end


fun generate_equalitys_from_bnf_fp tyco lthy =
  let
    val (tycos, Ts) = mutual_recursive_types tyco lthy
    val _ = map (fn tyco => "generating equality for type " ^ quote tyco) tycos
      |> cat_lines |> writeln
    val (tfrees, used_tfrees) = type_parameters (hd Ts) lthy
    val used_positions = map (member (op =) used_tfrees o TFree) tfrees
    val cs = map (subT "eq") used_tfrees
    val comp_Ts = map compT used_tfrees
    val arg_comps = map Free (cs ~~ comp_Ts)
    val dep_tycos = fold (add_used_tycos lthy) tycos []

    val XTys = Bnf_Access.bnf_types lthy tycos
    val inst_types = typ_subst_atomic (XTys ~~ Ts)
    val cTys = map (map (map inst_types)) (Bnf_Access.constr_argument_types lthy tycos)

    val map_simps = Bnf_Access.map_simps lthy tycos
    val case_simps = Bnf_Access.case_simps lthy tycos
    val maps = Bnf_Access.map_terms lthy tycos
    val map_comp_thms = Bnf_Access.map_comps lthy tycos

    val t_ixs = 0 upto (length Ts - 1)

    val compNs =
      (*TODO: clashes in presence of same type names in different theories*)
      map (Long_Name.base_name) tycos
      |> map (fn s => "equality_" ^ s)

    fun gen_vars prefix = map (fn (i, pty) => Free (prefix ^ ints_to_subscript [i], pty))
      (t_ixs ~~ Ts)

    (* primrec definitions of partial equalitys *)

    fun mk_pcomp (tyco, T) = ("partial_equality_" ^ Long_Name.base_name tyco, pcompT T)

    fun constr_terms lthy =
      Bnf_Access.constr_terms lthy
      #> map (apsnd (map freeify_tvars o fst o strip_type) o dest_Const)

    fun generate_pcomp_eqs lthy (tyco, T) =
      let
        val constrs = constr_terms lthy tyco

        fun comp_arg T x y =
          let
            val m = Generator_Aux.create_map default_comp (K o Free o mk_pcomp) () (K false)
              (#used_positions oo the_info) (#map oo the_info) (K o #pequality oo the_info)
              tycos ((K o K) ()) T lthy
            val p = Generator_Aux.create_partial () (K false)
              (#used_positions oo the_info) (#map oo the_info) (K o #pequality oo the_info)
              tycos ((K o K) ()) T lthy
          in p $ (m $ x) $ y |> infer_type lthy end

        fun generate_eq lthy (c_T as (cN, Ts)) =
          let
            val arg_Ts' = map orderify Ts
            val c = Const (cN, arg_Ts' ---> orderify T)
            val (y, (xs, ys)) = Name.variant "y" (Variable.names_of lthy) |>> Free o rpair T
              ||> (fn ctxt => Name.invent_names ctxt "x" (arg_Ts' @ Ts) |> map Free)
              ||> chop (length Ts)
            val k = find_index (curry (op =) c_T) constrs
            val cases = constrs |> map_index (fn (i, (_, Ts')) =>
              if i < k then fold_rev absdummy Ts' @{term False}
              else if k < i then fold_rev absdummy Ts' @{term False}
              else
                @{term list_all_eq} $ HOLogic.mk_list boolT (@{map 3} comp_arg Ts xs ys)
                |> lambdas ys)
            val lhs = Free (mk_pcomp (tyco, T)) $ list_comb (c, xs) $ y
            val rhs = list_comb (singleton (Bnf_Access.case_consts lthy) tyco, cases) $ y
          in HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)) |> infer_type lthy end
      in map (generate_eq lthy) constrs end

    val eqs = map (generate_pcomp_eqs lthy) (tycos ~~ Ts) |> flat
    val bindings = tycos ~~ Ts |> map mk_pcomp
      |> map (fn (name, T) => (Binding.name name, SOME T, NoSyn))

    val ((pcomps, pcomp_simps), lthy) = Local_Theory.subtarget_result
      (fn phi => fn (pcomps, _, pcomp_simps) => (map (Morphism.term phi) pcomps, map (Morphism.fact phi) pcomp_simps))
      (BNF_LFP_Rec_Sugar.primrec false [] bindings
        (map (fn t => ((Binding.empty_atts, t), [], [])) eqs)) lthy

    (* definitions of equalitys via partial equalitys and maps *)

    fun generate_comp_def tyco lthy =
      let
        val cs = map (subT "eq") used_tfrees
        val arg_Ts = map compT used_tfrees
        val args = map Free (cs ~~ arg_Ts)
        val (pcomp, m) = AList.lookup (op =) (tycos ~~ (pcomps ~~ maps)) tyco |> the
        val ts = tfrees |> map TFree |> map (fn T =>
          AList.lookup (op =) (used_tfrees ~~ args) T |> the_default (default_comp T))
        val rhs = HOLogic.mk_comp (pcomp, list_comb (m, ts)) |> infer_type lthy
        val abs_def = lambdas args rhs
        val name = "equality_" ^ Long_Name.base_name tyco
        val ((comp, (_, prethm)), lthy) =
          Local_Theory.define ((Binding.name name, NoSyn), (Binding.empty_atts, abs_def)) lthy
        val eq = Logic.mk_equals (list_comb (comp, args), rhs)
        val thm = Goal.prove lthy (map (fst o dest_Free) args) [] eq (K (unfold_tac lthy [prethm]))
      in
        Local_Theory.note ((Binding.name (name ^ "_def"), []), [thm]) lthy
        |>> the_single o snd
        |>> `(K comp)
      end

    val ((comps, comp_defs), lthy) = Local_Theory.subtarget_result
      (fn phi => fn (comps, comp_defs) => (map (Morphism.term phi) comps, map (Morphism.thm phi) comp_defs))
      (fold_map generate_comp_def tycos #>> split_list) lthy

    (* alternative simp-rules for equalitys *)

    val full_comps = map (list_comb o rpair arg_comps) comps

    fun generate_comp_simps (tyco, T) lthy =
      let
        val constrs = constr_terms lthy tyco

        fun comp_arg T x y =
          let
            fun create_comp (T as TFree _) =
                  AList.lookup (op =) (used_tfrees ~~ arg_comps) T
                  |> the_default (HOLogic.id_const dummyT)
              | create_comp (Type (tyco, Ts)) =
                  (case AList.lookup (op =) (tycos ~~ comps) tyco of
                    SOME c => list_comb (c, arg_comps)
                  | NONE =>
                      let
                        val {equality = c, used_positions = up, ...} = the_info lthy tyco
                        val ts = (up ~~ Ts) |> map_filter (fn (b, T) =>
                          if b then SOME (create_comp T) else NONE)
                      in list_comb (c, ts) end)
              | create_comp T =
                  error ("unexpected schematic variable " ^ quote (Syntax.string_of_typ lthy T))
            val comp = create_comp T
          in comp $ x $ y |> infer_type lthy end

        fun generate_eq_thm lthy (c_T as (_, Ts)) =
          let
            val (xs, ctxt) = Variable.names_of lthy
              |> fold_map (fn T => Name.variant "x" #>> Free o rpair T) Ts
            fun mk_const (c, Ts) = Const (c, Ts ---> T)
            val comp_const = AList.lookup (op =) (tycos ~~ comps) tyco |> the
            val lhs = list_comb (comp_const, arg_comps) $ list_comb (mk_const c_T, xs)
            val k = find_index (curry (op =) c_T) constrs

            fun mk_eq c ys rhs =
              let
                val y = list_comb (mk_const c, ys)
                val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs $ y, rhs))
              in (ys, eq |> infer_type lthy) end

            val ((ys, eqs), _) = fold_map (fn (i, c as (_, Ts')) => fn ctxt =>
              let
                val (ys, ctxt) = fold_map (fn T => Name.variant "y" #>> Free o rpair T) Ts' ctxt
              in
                (if i < k then mk_eq c ys @{term False}
                else if k < i then mk_eq c ys @{term False}
                else
                  @{term list_all_eq} $ HOLogic.mk_list boolT (@{map 3} comp_arg Ts xs ys)
                  |> mk_eq c ys,
                ctxt)
              end) (tag_list 0 constrs) ctxt
              |> apfst (apfst flat o split_list)

            val dep_comp_defs = map_filter (#equality_def o the_info lthy) dep_tycos
            val dep_map_comps = map_filter (#map_comp o the_info lthy) dep_tycos
            val thms = prove_multi_future lthy (map (fst o dest_Free) (xs @ ys) @ cs) [] eqs
              (fn {context = ctxt, ...} =>
                Goal.conjunction_tac 1
                THEN unfold_tac ctxt
                  (@{thms id_apply o_def} @
                    flat case_simps @
                    flat pcomp_simps @
                    dep_map_comps @ comp_defs @ dep_comp_defs @ flat map_simps))
          in thms end

        val thms = map (generate_eq_thm lthy) constrs |> flat
        val simp_thms = map (Local_Defs.unfold lthy @{thms list_all_eq_unfold}) thms

        val name = "equality_" ^ Long_Name.base_name tyco
      in
        lthy
        |> Local_Theory.note ((Binding.name (name ^ "_simps"), @{attributes [simp, code]}), simp_thms)
        |> snd
        |> (fn lthy => (thms, lthy))
      end

    val (comp_simps, lthy) = Local_Theory.subtarget_result
      (fn phi => map (Morphism.fact phi))
      (fold_map generate_comp_simps (tycos ~~ Ts)) lthy

    (* partial theorems *)

    val set_funs = Bnf_Access.set_terms lthy tycos
    val x_vars = gen_vars "x"
    val free_names = map (fst o dest_Free) (x_vars @ arg_comps)
    val xi_vars = map_index (fn (i, _) =>
      map_index (fn (j, pty) => Free ("x" ^ ints_to_subscript [i, j], pty)) used_tfrees) Ts

    fun mk_eq_thm' mk_eq' = map_index (fn (i, ((set_funs, x), xis)) =>
      let
        fun create_cond ((set_t, xi), c) =
          let
            val rhs = mk_eq' lthy c $ xi |> HOLogic.mk_Trueprop
            val lhs = HOLogic.mk_mem (xi, set_t $ x) |> HOLogic.mk_Trueprop
          in Logic.all xi (Logic.mk_implies (lhs, rhs)) end

        val used_sets = map (the o AList.lookup (op =) (map TFree tfrees ~~ set_funs)) used_tfrees
        val conds = map create_cond (used_sets ~~ xis ~~ arg_comps)
        val concl = mk_eq' lthy (nth full_comps i) $ x |> HOLogic.mk_Trueprop
      in Logic.list_implies (conds, concl) |> infer_type lthy end) (set_funs ~~ x_vars ~~ xi_vars)

    val induct_thms = Bnf_Access.induct_thms lthy tycos
    val set_simps = Bnf_Access.set_simps lthy tycos
    val case_thms = Bnf_Access.case_thms lthy tycos
    val distinct_thms = Bnf_Access.distinct_thms lthy tycos
    val inject_thms = Bnf_Access.inject_thms lthy tycos

    val rec_info = (the_info lthy, #used_positions, tycos)
    val split_IHs = split_IHs rec_info

    val unknown_value = false (* effect of choosing false / true not yet visible *)

    fun induct_tac ctxt f =
      ((DETERM o Induction.induction_tac ctxt false
        (map (fn x => [SOME (NONE, (x, unknown_value))]) x_vars) [] [] (SOME induct_thms) [])
      THEN_ALL_NEW (fn i =>
        Subgoal.SUBPROOF (fn {context = ctxt, prems = prems, params = iparams, ...} =>
          f (i - 1) ctxt prems iparams) ctxt i)) 1

    val recursor_tac = std_recursor_tac rec_info used_tfrees
      (fn info => #partial_equality_thm info)

    fun instantiate_IHs IHs pre_conds = map (fn IH =>
      OF_option IH (replicate (Thm.nprems_of IH - length pre_conds) NONE @ map SOME pre_conds)) IHs


    (* partial eq-theorem *)
    val _ = debug_out "Partial equality"
    val eq_thms' = mk_eq_thm' mk_pequality

    fun eq_solve_tac i ctxt IH_prems xs =
      let
        val (i, j) = ind_case_to_idxs cTys i
        val k = length IH_prems - length arg_comps
        val pre_conds = drop k IH_prems
        val IH = take k IH_prems
        val comp_simps = nth comp_simps i
        val case_thm = nth case_thms i
        val distinct_thms = nth distinct_thms i
        val inject_thms = nth inject_thms i
        val set_thms = nth set_simps i
      in
        (* after induction *)
        resolve_tac ctxt @{thms pequalityI} 1
        THEN Subgoal.FOCUS (fn focus =>
          let
            val y = #params focus |> hd
            val yt = y |> snd |> Thm.term_of
            val ctxt = #context focus
            val pre_cond = map (fn pre_cond => Local_Defs.unfold ctxt set_thms pre_cond) pre_conds
            val IH = instantiate_IHs IH pre_cond
            val xs_tys = map (fastype_of o Thm.term_of o snd) xs
            val IHs = split_IHs xs_tys IH

            fun sub_case_tac j' (ctxt, y_simp, _) =
              if j = j' then
                unfold_tac ctxt (y_simp @ comp_simps)
                THEN unfold_tac ctxt @{thms list_all_eq}
                THEN unfold_tac ctxt (@{thms in_set_simps} @ inject_thms @ @{thms refl_True})
                THEN conjI_tac @{thms conj_weak_cong} ctxt xs (fn ctxt' => fn k =>
                  resolve_tac ctxt @{thms pequalityD} 1
                  THEN recursor_tac pre_cond (nth xs_tys k) (nth IHs k) ctxt')
              else
                (* different constructors *)
                unfold_tac ctxt (y_simp @ distinct_thms @ comp_simps @ @{thms bool.simps})
          in
            mk_case_tac ctxt [[SOME yt]] case_thm sub_case_tac
          end
        ) ctxt 1
      end

    val eq_thms' = prove_multi_future lthy free_names [] eq_thms' (fn {context = ctxt, ...} =>
      induct_tac ctxt eq_solve_tac)
    val _ = debug_out (@{make_string} eq_thms')

    (* total theorems *)
    fun mk_eq_sym_trans_thm mk_eq_sym_trans compI2 compE2 thms' =
      let
        val conds = map (fn c => mk_eq_sym_trans lthy c |> HOLogic.mk_Trueprop) arg_comps
        val thms = map (fn i =>
           mk_eq_sym_trans lthy (nth full_comps i)
           |> HOLogic.mk_Trueprop
           |> (fn concl => Logic.list_implies (conds,concl)))
           t_ixs
        val thms = prove_multi_future lthy free_names [] thms (fn {context = ctxt, ...} =>
          ALLGOALS Goal.conjunction_tac
          THEN Method.intros_tac ctxt (@{thm conjI} :: compI2 :: thms') []
          THEN ALLGOALS (eresolve_tac ctxt [compE2]))
      in thms end

    val eq_thms = mk_eq_sym_trans_thm mk_equality @{thm equalityI2} @{thm equalityD2} eq_thms'


    val _ = debug_out "full equality thms"
    fun mk_comp_thm (i, e) =
      let
        val conds = map (fn c => mk_equality lthy c |> HOLogic.mk_Trueprop) arg_comps
        val nearly_thm = e

        val thm =
           mk_equality lthy (nth full_comps i)
           |> HOLogic.mk_Trueprop
           |> (fn concl => Logic.list_implies (conds, concl))
      in
        Goal.prove_future lthy free_names [] thm
          (K (resolve_tac lthy [nearly_thm] 1 THEN ALLGOALS (assume_tac lthy)))
      end
    val comp_thms = map_index mk_comp_thm eq_thms

    val (_, lthy) = fold_map (fn (thm, cname) =>
      Local_Theory.note ((Binding.name cname, []), [thm])) (comp_thms ~~ compNs) lthy

    val _ = debug_out (@{make_string} comp_thms)

    val (_, lthy) = fold_map (fn (thm, cname) =>
      Local_Theory.note ((Binding.name (cname ^ "_pointwise"), []), [thm])) (eq_thms' ~~ compNs) lthy

  in
    ((pcomps ~~ pcomp_simps, comps ~~ comp_defs), lthy)
    ||> fold (fn (((((((tyco, map), pcomp), comp), comp_def), map_comp) , peq_thm), comp_thm) =>
          declare_info tyco map pcomp comp (SOME comp_def) (SOME map_comp)
            peq_thm comp_thm used_positions)
         (tycos ~~ maps ~~ pcomps ~~ comps ~~ comp_defs ~~ map_comp_thms ~~ eq_thms' ~~ comp_thms)
  end

fun generate_equality gen_type tyco lthy =
  let
    val _ = is_some (get_info lthy tyco)
      andalso error ("type " ^ quote tyco ^ " does already have a equality")
  in
    case gen_type of
      BNF => generate_equalitys_from_bnf_fp tyco lthy |> snd
    | EQ => register_equality_of tyco lthy
  end

fun ensure_info gen_type tyco lthy =
  (case get_info lthy tyco of
    SOME _ => lthy
  | NONE => generate_equality gen_type tyco lthy)

fun generate_equality_cmd tyco param = Named_Target.theory_map (
  if param = "eq" then generate_equality EQ tyco
  else if param = "" then generate_equality BNF tyco
  else error ("unknown parameter, expecting no parameter for BNF-datatypes, " ^
         "or \"eq\" for types where the built-in equality \"=\" should be used."))

val _ =
  Theory.setup
    (Derive_Manager.register_derive "equality" "generate an equality function, options are () and (eq)" generate_equality_cmd)

end
