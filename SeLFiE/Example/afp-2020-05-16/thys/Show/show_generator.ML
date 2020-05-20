(*  Title:       Show
    Author:      Christian Sternagel <c.sternagel@gmail.com>
    Author:      René Thiemann <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel <c.sternagel@gmail.com>
    Maintainer:  René Thiemann <rene.thiemann@uibk.ac.at>

Generate/register show functions for arbitrary types.

Precedence is used to determine parenthesization of subexpressions. In the automatically generated
functions 0 means "no parentheses" and 1 means "parenthesize". 
*)

signature SHOW_GENERATOR =
sig

(*generate show functions for the given datatype*)
val generate_showsp : string -> local_theory -> local_theory

val register_foreign_partial_and_full_showsp :
  string ->     (*type name*)
  int ->        (*default precedence for type parameters*)
  term ->       (*partial show function*)
  term ->       (*show function*)
  thm option -> (*definition of show function via partial show function*)
  term ->       (*map function*)
  thm option -> (*compositionality theorem of map function*)
  bool list ->  (*indicate which positions of type parameters are used*)
  thm ->        (*show law intro rule*)
  local_theory -> local_theory

(*for type constants (i.e., nullary type constructors) partial and full show functions
coincide and no other information is necessary.*)
val register_foreign_showsp : typ -> term -> thm -> local_theory -> local_theory

(*automatically derive a "show" class instance for the given datatype*)
val show_instance : string -> theory -> theory

end

structure Show_Generator : SHOW_GENERATOR =
struct

open Generator_Aux

val mk_prec = HOLogic.mk_number @{typ nat}
val prec0 = mk_prec 0
val prec1 = mk_prec 1
val showS = @{sort "show"}
val showsT = @{typ "shows"}
fun showspT T = @{typ nat} --> T --> showsT
val showsify_typ = map_atyps (K showsT)
val showsify = map_types showsify_typ
fun show_law_const T = Const (@{const_name show_law}, showspT T --> T --> HOLogic.boolT)
fun shows_prec_const T = Const (@{const_name shows_prec}, showspT T)
fun shows_list_const T = Const (@{const_name shows_list}, HOLogic.listT T --> showsT)
fun showsp_list_const T = Const (@{const_name showsp_list}, showspT T --> showspT (HOLogic.listT T))
val dest_showspT = binder_types #> tl #> hd

type info =
  {prec : int,
   pshowsp : term,
   showsp : term,
   show_def : thm option,
   map : term,
   map_comp : thm option,
   used_positions : bool list,
   show_law_intro : thm}

structure Data = Generic_Data
  (type T = info Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (fn (info1, info2) => #pshowsp info1 = #pshowsp info2))

fun add_info tyco info = Data.map (Symtab.update_new (tyco, info))
val get_info = Context.Proof #> Data.get #> Symtab.lookup

fun the_info ctxt tyco =
  (case get_info ctxt tyco of
    SOME info => info
  | NONE => error ("no show function available for type " ^ quote tyco))

fun declare_info tyco p pshow show show_def m m_comp used_pos law_thm =
  Local_Theory.declaration {syntax = false, pervasive = false} (fn phi =>
    add_info tyco
      {prec = p,
       pshowsp = Morphism.term phi pshow,
       showsp = Morphism.term phi show,
       show_def = Option.map (Morphism.thm phi) show_def,
       map = Morphism.term phi m,
       map_comp = Option.map (Morphism.thm phi) m_comp,
       used_positions = used_pos,
       show_law_intro = Morphism.thm phi law_thm})

val register_foreign_partial_and_full_showsp = declare_info

fun register_foreign_showsp T show =
  let val tyco = (case T of Type (tyco, []) => tyco | _ => error "expected type constant")
  in register_foreign_partial_and_full_showsp tyco 0 show show NONE (HOLogic.id_const T) NONE [] end

fun shows_string c =
  @{const "shows_string"} $ HOLogic.mk_string (Long_Name.base_name c)

fun mk_shows_parens _ [t] = t
  | mk_shows_parens p ts = Library.foldl1 HOLogic.mk_comp
      (@{const shows_pl} $ p :: separate @{const shows_space} ts @ [@{const shows_pr} $ p])

fun simp_only_tac ctxt ths =
  CHANGED o full_simp_tac (clear_simpset (put_simpset HOL_basic_ss ctxt) addsimps ths)

fun generate_showsp tyco lthy =
  let
    val (tycos, Ts) = mutual_recursive_types tyco lthy
    val _ = map (fn tyco => "generating show function for type " ^ quote tyco) tycos
      |> cat_lines |> writeln

    val maps = Bnf_Access.map_terms lthy tycos
    val map_simps = Bnf_Access.map_simps lthy tycos
    val map_comps = Bnf_Access.map_comps lthy tycos

    val (tfrees, used_tfrees) = type_parameters (hd Ts) lthy
    val used_positions = map (member (op =) used_tfrees o TFree) tfrees
    val ss = map (subT "show") used_tfrees
    val show_Ts = map showspT used_tfrees
    val arg_shows = map Free (ss ~~ show_Ts)
    val dep_tycos = fold (add_used_tycos lthy) tycos []

    fun mk_pshowsp (tyco, T) =
      ("pshowsp_" ^ Long_Name.base_name tyco, showspT T |> showsify_typ)
    fun default_show T = absdummy T (mk_id @{typ string})

    fun constr_terms lthy = Bnf_Access.constr_terms lthy #> map (apsnd (fst o strip_type) o dest_Const)

    (* primrec definitions of partial show functions *)

    fun generate_pshow_eqs lthy (tyco, T) =
      let
        val constrs = constr_terms lthy tyco
          |> map (fn (c, Ts) =>
               let val Ts' = map showsify_typ Ts
               in (Const (c, Ts' ---> T) |> showsify, Ts') end)

        fun shows_arg (x, T) =
          let
            val m = Generator_Aux.create_map default_show
              (fn (tyco, T) => fn p => Free (mk_pshowsp (tyco, T)) $ p) prec1
              (equal @{typ "shows"})
              (#used_positions oo the_info) (#map oo the_info)
              (curry (op $) o #pshowsp oo the_info)
              tycos (mk_prec o #prec oo the_info) T lthy
            val pshow = Generator_Aux.create_partial prec1 (equal @{typ "shows"})
              (#used_positions oo the_info) (#map oo the_info)
              (curry (op $) o #pshowsp oo the_info)
              tycos (mk_prec o #prec oo the_info) T lthy
          in pshow $ (m $ Free (x, T)) |> infer_type lthy end

        fun generate_eq lthy (c, arg_Ts) =
          let
            val (p, xs) = Name.variant "p" (Variable.names_of lthy) |>> Free o rpair @{typ nat}
              ||> (fn ctxt => Name.invent_names ctxt "x" arg_Ts)
            val lhs = Free (mk_pshowsp (tyco, T)) $ p $ list_comb (c, map Free xs)
            val rhs = shows_string (dest_Const c |> fst) :: map shows_arg xs
              |> mk_shows_parens p
          in HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)) end
      in map (generate_eq lthy) constrs end

    val eqs = map (generate_pshow_eqs lthy) (tycos ~~ Ts) |> flat
    val bindings = tycos ~~ Ts |> map mk_pshowsp
      |> map (fn (name, T) => (Binding.name name, T |> showsify_typ |> SOME, NoSyn))

    val ((pshows, pshow_simps), lthy) = Local_Theory.subtarget_result
      (fn phi => fn (pshows, _, pshow_simps) => (map (Morphism.term phi) pshows, map (Morphism.fact phi) pshow_simps))
      (BNF_LFP_Rec_Sugar.primrec false [] bindings
        (map (fn t => ((Binding.empty_atts, t), [], [])) eqs)) lthy

    (* definitions of show functions via partial show functions and map *)

    fun generate_show_defs tyco lthy =
      let
        val ss = map (subT "show") used_tfrees
        val arg_Ts = map showspT used_tfrees
        val arg_shows = map Free (ss ~~ arg_Ts)
        val p = Name.invent (Variable.names_of lthy) "p" 1 |> the_single |> Free o rpair @{typ nat}
        val (pshow, m) = AList.lookup (op =) (tycos ~~ (pshows ~~ maps)) tyco |> the
        val ts = tfrees |> map TFree |> map (fn T =>
          AList.lookup (op =) (used_tfrees ~~ map (fn x => x $ prec1) arg_shows) T
          |> the_default (default_show T))
        val args = arg_shows @ [p]
        val rhs = HOLogic.mk_comp (pshow $ p, list_comb (m, ts)) |> infer_type lthy
        val abs_def = fold_rev lambda args rhs
        val name = "showsp_" ^ Long_Name.base_name tyco
        val ((showsp, (_, prethm)), lthy) =
          Local_Theory.define ((Binding.name name, NoSyn), (Binding.empty_atts, abs_def)) lthy
        val eq = Logic.mk_equals (list_comb (showsp, args), rhs)
        val thm = Goal.prove_future lthy (map (fst o dest_Free) args) [] eq (K (unfold_tac lthy [prethm]))
      in
        Local_Theory.note ((Binding.name (name ^ "_def"), []), [thm]) lthy
        |>> the_single o snd
        |>> `(K showsp)
      end

    val ((shows, show_defs), lthy) = Local_Theory.subtarget_result
      (fn phi => fn (shows, show_defs) => (map (Morphism.term phi) shows, map (Morphism.thm phi) show_defs))
      (fold_map generate_show_defs tycos #>> split_list) lthy

    (* alternative simp-rules for show functions *)

    fun generate_show_simps (tyco, T) lthy =
      let
        val constrs = constr_terms lthy tyco |> map (apsnd (map freeify_tvars))
          |> map (fn (c, Ts) => (Const (c, Ts ---> T), Ts))

        fun shows_arg (x, T) =
          let
            fun create_show (T as TFree _) = AList.lookup (op =) (used_tfrees ~~ arg_shows) T |> the
              | create_show (Type (tyco, Ts)) =
                  (case AList.lookup (op =) (tycos ~~ shows) tyco of
                    SOME show_const => list_comb (show_const, arg_shows)
                  | NONE =>
                    let
                      val {showsp = s, used_positions = up, ...} = the_info lthy tyco
                      val ts = (up ~~ Ts) |> map_filter (fn (b, T) =>
                        if b then SOME (create_show T) else NONE)
                    in list_comb (s, ts) end)
              | create_show T =
                  error ("unexpected schematic variable " ^ quote (Syntax.string_of_typ lthy T))

            val show = create_show T |> infer_type lthy
          in show $ prec1 $ Free (x, T) end

        fun generate_eq_thm lthy (c, arg_Ts) =
          let
            val (p, xs) = Name.variant "p" (Variable.names_of lthy) |>> Free o rpair @{typ nat}
              ||> (fn ctxt => Name.invent_names ctxt "x" arg_Ts)
            val show_const = AList.lookup (op =) (tycos ~~ shows) tyco |> the
            val lhs = list_comb (show_const, arg_shows) $ p $ list_comb (c, map Free xs)
            val rhs = shows_string (dest_Const c |> fst) :: map shows_arg xs
              |> mk_shows_parens p
            val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)) |> infer_type lthy
            val dep_show_defs = map_filter (#show_def o the_info lthy) dep_tycos
            val dep_map_comps = map_filter (#map_comp o the_info lthy) dep_tycos
            val thm = Goal.prove_future lthy (fst (dest_Free p) :: map fst xs @ ss) [] eq
              (fn {context = ctxt, ...} => unfold_tac ctxt
                (@{thms id_def o_def} @
                  flat pshow_simps @
                  dep_map_comps @ show_defs @ dep_show_defs @ flat map_simps))
          in thm end

       val thms = map (generate_eq_thm lthy) constrs
       val name = "showsp_" ^ Long_Name.base_name tyco
      in
        lthy
        |> Local_Theory.note ((Binding.name (name ^ "_simps"), @{attributes [simp, code]}), thms)
        |> apfst snd
      end

    val (show_simps, lthy) = Local_Theory.subtarget_result
      (fn phi => map (Morphism.fact phi))
      (fold_map generate_show_simps (tycos ~~ Ts)) lthy

    (* show law theorems *)

    val induct_thms = Bnf_Access.induct_thms lthy tycos
    val set_simps = Bnf_Access.set_simps lthy tycos
    val sets = Bnf_Access.set_terms lthy tycos

    fun generate_show_law_thms (tyco, x) =
      let
        val sets = AList.lookup (op =) (tycos ~~ sets) tyco |> the
        val used_sets = map (the o AList.lookup (op =) (map TFree tfrees ~~ sets)) used_tfrees
        fun mk_prem ((show, set), T) =
          let
            (*val y = singleton (Name.variant_list [fst x]) "y" |> Free o rpair T*)
            val y = Free (subT "x" T, T)
            val lhs = HOLogic.mk_mem (y, set $ Free x) |> HOLogic.mk_Trueprop
            val rhs = show_law_const T $ show $ y |> HOLogic.mk_Trueprop
          in Logic.all y (Logic.mk_implies (lhs, rhs)) end
        val prems = map mk_prem (arg_shows ~~ used_sets ~~ used_tfrees)
        val (show_const, T) = AList.lookup (op =) (tycos ~~ (shows ~~ Ts)) tyco |> the
        val concl = show_law_const T $ list_comb (show_const, arg_shows) $ Free x
          |> HOLogic.mk_Trueprop
      in Logic.list_implies (prems, concl) |> infer_type lthy end

    val xs = Name.invent_names (Variable.names_of lthy) "x" Ts
    val show_law_prethms = map generate_show_law_thms (tycos ~~ xs)

    val rec_info = (the_info lthy, #used_positions, tycos)
    val split_IHs = split_IHs rec_info

    val recursor_tac = std_recursor_tac rec_info used_tfrees #show_law_intro
  
    fun show_law_tac ctxt xs =
      let
        val constr_Ts = tycos
          |> map (#ctrXs_Tss o #fp_ctr_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of ctxt)

        val ind_case_to_idxs = 
          let
            fun number n (i, j) ((_ :: xs) :: ys) = (n, (i, j)) :: number (n + 1) (i, j + 1) (xs :: ys)
              | number n (i, _) ([] :: ys) = number n (i + 1, 0) ys
              | number _ _ [] = []
          in AList.lookup (op =) (number 0 (0, 0) constr_Ts) #> the end

        fun instantiate_IHs IHs assms = map (fn IH =>
          OF_option IH (replicate (Thm.nprems_of IH - length assms) NONE @ map SOME assms)) IHs

        fun induct_tac ctxt f =
          (DETERM o Induction.induction_tac ctxt false
            (map (fn x => [SOME (NONE, (x, false))]) xs) [] [] (SOME induct_thms) [])
          THEN_ALL_NEW (fn st =>
            Subgoal.SUBPROOF (fn {context = ctxt, prems, params, ...} =>
              f ctxt (st - 1) prems params) ctxt st)

        (*do not use full "show_law_simps" here, since otherwise too many
          subgoals might be solved (so that the number of subgoals does no longer
          match the number of IHs)*)
        val show_law_simps_less = @{thms
          shows_string_append shows_pl_append shows_pr_append shows_space_append}

        fun o_append_intro_tac ctxt f = HEADGOAL (
          K (Method.try_intros_tac ctxt @{thms o_append} [])
          THEN_ALL_NEW K (unfold_tac ctxt show_law_simps_less)
          THEN_ALL_NEW (fn i => Subgoal.SUBPROOF (fn {context = ctxt', ...} =>
              f (i - 1) ctxt') ctxt i))

        fun solve_tac ctxt case_num prems params =
          let
            val (i, _) = ind_case_to_idxs case_num (*(constructor number, argument number)*)
            val k = length prems - length used_tfrees
            val (IHs, assms) = chop k prems
          in
            resolve_tac ctxt @{thms show_lawI} 1
            THEN Subgoal.FOCUS (fn {context = ctxt, ...} =>
              let
                val assms = map (Local_Defs.unfold ctxt (nth set_simps i)) assms
                val Ts = map (fastype_of o Thm.term_of o snd) params
                val IHs = instantiate_IHs IHs assms |> split_IHs Ts
              in
                unfold_tac ctxt (nth show_simps i)
                THEN o_append_intro_tac ctxt (fn i => fn ctxt' =>
                  resolve_tac ctxt' @{thms show_lawD} 1
                  THEN recursor_tac assms (nth Ts i) (nth IHs i) ctxt')
              end) ctxt 1
          end
      in induct_tac ctxt solve_tac end

    val show_law_thms = prove_multi_future lthy (map fst xs @ ss) [] show_law_prethms
      (fn {context = ctxt, ...} =>
        HEADGOAL (show_law_tac ctxt (map Free xs)))

    val (show_law_thms, lthy) = Local_Theory.subtarget_result Morphism.fact
      (fold_map (fn (tyco, thm) =>
      let val name = Long_Name.base_name tyco
      in
        Local_Theory.note
          ((Binding.name ("show_law_" ^ name), @{attributes [show_law_intros]}), [thm])
        #> apfst (the_single o snd)
      end) (tycos ~~ show_law_thms)) lthy
  in
    lthy
    |> fold (fn ((((((tyco, pshow), show), show_def), m), m_comp), law_thm) =>
         declare_info tyco 1 pshow show (SOME show_def) m (SOME m_comp) used_positions law_thm)
       (tycos ~~ pshows ~~ shows ~~ show_defs ~~ maps ~~ map_comps ~~ show_law_thms)
  end

fun ensure_info tyco lthy =
    (case get_info lthy tyco of
      SOME _ => lthy
    | NONE => generate_showsp tyco lthy)


(* proving show instances *)

fun dest_showsp showsp =
  dest_Const showsp
  ||> (
    binder_types #> chop_prefix (fn T => T <> @{typ nat})
    #>> map (freeify_tvars o dest_showspT)
    ##> map (dest_TFree o freeify_tvars) o snd o dest_Type o hd o tl)

fun show_instance tyco thy =
  let
    val _ = Sorts.has_instance (Sign.classes_of thy) tyco showS
      andalso error ("type " ^ quote tyco ^ " is already an instance of class \"show\"")
    val _ = writeln ("deriving \"show\" instance for type " ^ quote tyco)
    val thy = Named_Target.theory_map (ensure_info tyco) thy
    val lthy = Named_Target.theory_init thy
    val {showsp, ...} = the_info lthy tyco
    val (showspN, (used_tfrees, tfrees)) = dest_showsp showsp
    val tfrees' = tfrees
      |> map (fn (x, S) =>
        if member (op =) used_tfrees (TFree (x, S)) then (x, showS)
        else (x, S))
    val used_tfrees' = map (dest_TFree #> fst #> rpair showS #> TFree) used_tfrees
    val T = Type (tyco, map TFree tfrees')
    val arg_Ts = map showspT used_tfrees'
    val showsp' = Const (showspN, arg_Ts ---> showspT T)
    val shows_prec_def = Logic.mk_equals
      (shows_prec_const T, list_comb (showsp', map shows_prec_const used_tfrees'))
    val shows_list_def = Logic.mk_equals
      (shows_list_const T, showsp_list_const T $ shows_prec_const T $ prec0)
    val name = Long_Name.base_name tyco
    val ((shows_prec_thm, shows_list_thm), lthy) =
      Class.instantiation ([tyco], tfrees', showS) thy
      |> Generator_Aux.define_overloaded_generic
        ((Binding.name ("shows_prec_" ^ name ^ "_def"), @{attributes [code]}), shows_prec_def)
      ||>> Generator_Aux.define_overloaded_generic
        ((Binding.name ("shows_list_" ^ name ^ "_def"), @{attributes [code]}), shows_list_def)
  in
    Class.prove_instantiation_exit (fn ctxt =>
      let
        val show_law_intros = Named_Theorems.get ctxt @{named_theorems "show_law_intros"}
        val show_law_simps = Named_Theorems.get ctxt @{named_theorems "show_law_simps"}
        val show_append_tac = resolve_tac ctxt @{thms show_lawD}
          THEN' REPEAT_ALL_NEW (resolve_tac ctxt show_law_intros)
          THEN_ALL_NEW (
            resolve_tac ctxt @{thms show_lawI}
            THEN' simp_only_tac ctxt show_law_simps)
      in
        Class.intro_classes_tac ctxt []
        THEN unfold_tac ctxt [shows_prec_thm, shows_list_thm]
        THEN REPEAT1 (HEADGOAL show_append_tac)
     end) lthy
  end

val _ =
  Theory.setup
    (Derive_Manager.register_derive "show" "generate show instance" (K o show_instance))

end
