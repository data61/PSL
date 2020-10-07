(* Version: Isabelle2012 *)

signature TYCON =
sig
  val add_tycon_cmd:
      (string * (string * string option) list * binding * mixfix *
       (binding * (bool * binding option * string) list * mixfix) list) list
      -> theory -> theory

  val add_tycon:
      (string * (string * sort) list * binding * mixfix *
       (binding * (bool * binding option * typ) list * mixfix) list) list
      -> theory -> theory
end

structure Tycon : TYCON =
struct

val TC_simp =
  @{lemma "f \<equiv> g \<Longrightarrow> f TYPE('a::{}) = g TYPE('a)" by simp}

fun mk_appT T U = Type (@{type_name app}, [T, U])

fun dest_appT (Type (@{type_name app}, [T, U])) = (T, U)
  | dest_appT T = raise TYPE ("dest_appT", [T], [])

open HOLCF_Library

fun first  (x,_,_) = x
fun second (_,x,_) = x

val beta_ss =
  simpset_of (put_simpset HOL_basic_ss @{context}
    addsimps @{thms simp_thms} addsimprocs [@{simproc beta_cfun_proc}])

fun is_cpo thy T = Sign.of_sort thy (T, @{sort cpo})

(******************************************************************************)
(****************************** defining tycons *******************************)
(******************************************************************************)

fun define_singleton_type
    (typ : binding * (string * sort) list * mixfix)
    (thy : theory) : (string * Typedef.info) * theory =
  let
    val set = @{term "UNIV :: unit set"}
    val opt_morphs = NONE
    fun tac ctxt = resolve_tac ctxt [UNIV_witness] 1
    val _ = writeln ("Defining type " ^ Binding.print (first typ))
  in
    thy
    |> Named_Target.theory_map_result (apsnd o Typedef.transform_info)
      (Typedef.add_typedef {overloaded = false} typ set opt_morphs tac)
  end    

(******************************************************************************)
(************************** building types and terms **************************)
(******************************************************************************)

infixr 6 ->>
infixr -->>

val udomT = @{typ udom}
val deflT = @{typ "udom defl"}
val udeflT = @{typ "udom u defl"}

fun mk_DEFL T =
  Const (@{const_name defl}, Term.itselfT T --> deflT) $ Logic.mk_type T

fun dest_DEFL (Const (@{const_name defl}, _) $ t) = Logic.dest_type t
  | dest_DEFL t = raise TERM ("dest_DEFL", [t])

fun mk_LIFTDEFL T =
  Const (@{const_name liftdefl}, Term.itselfT T --> udeflT) $ Logic.mk_type T

fun dest_LIFTDEFL (Const (@{const_name liftdefl}, _) $ t) = Logic.dest_type t
  | dest_LIFTDEFL t = raise TERM ("dest_LIFTDEFL", [t])

fun tc_const T =
  Const (@{const_name tc}, Term.itselfT T --> deflT ->> deflT)

fun mk_TC T = tc_const T $ Logic.mk_type T

fun argumentTs (Type (@{type_name app}, [T, Type (_, Ts)])) = Ts @ [T]
  | argumentTs (Type (_, Ts)) = Ts
  | argumentTs T = []

fun mk_u_defl t = mk_capply (@{const "u_defl"}, t)

fun emb_const T = Const (@{const_name emb}, T ->> udomT)
fun prj_const T = Const (@{const_name prj}, udomT ->> T)
fun coerce_const (T, U) = mk_cfcomp (prj_const U, emb_const T)

fun isodefl_const T =
  Const (@{const_name isodefl}, (T ->> T) --> deflT --> HOLogic.boolT)

fun isodefl'_const T =
  Const (@{const_name isodefl'}, (T ->> T) --> udeflT --> HOLogic.boolT)

fun mk_deflation t =
  Const (@{const_name deflation}, Term.fastype_of t --> boolT) $ t

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t)

fun mk_eqs (t, u) = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u))

(******************************************************************************)
(****************************** isomorphism info ******************************)
(******************************************************************************)

fun deflation_abs_rep (info : Domain_Take_Proofs.iso_info) : thm =
  let
    val abs_iso = #abs_inverse info
    val rep_iso = #rep_inverse info
    val thm = @{thm deflation_abs_rep} OF [abs_iso, rep_iso]
  in
    Drule.zero_var_indexes thm
  end

(******************************************************************************)
(*************** fixed-point definitions and unfolding theorems ***************)
(******************************************************************************)

fun mk_projs []      _ = []
  | mk_projs (x::[]) t = [(x, t)]
  | mk_projs (x::xs) t = (x, mk_fst t) :: mk_projs xs (mk_snd t)

fun add_fixdefs
    (spec : (binding * term) list)
    (thy : theory) : (thm list * thm list * thm) * theory =
  let
    val binds = map fst spec
    val (lhss, rhss) = ListPair.unzip (map (dest_eqs o snd) spec)
    val functional = lambda_tuple lhss (mk_tuple rhss)
    val fixpoint = mk_fix (mk_cabs functional)

    (* project components of fixpoint *)
    val projs = mk_projs lhss fixpoint

    (* convert parameters to lambda abstractions *)
    fun mk_eqn (lhs, rhs) =
        case lhs of
          Const (@{const_name Rep_cfun}, _) $ f $ (x as Free _) =>
            mk_eqn (f, big_lambda x rhs)
        | f $ Const (@{const_name Pure.type}, T) =>
            mk_eqn (f, Abs ("t", T, rhs))
        | Const _ => Logic.mk_equals (lhs, rhs)
        | _ => raise TERM ("lhs not of correct form", [lhs, rhs])
    val eqns = map mk_eqn projs

    (* register constant definitions *)
    val (fixdef_thms, thy) =
      (Global_Theory.add_defs false o map Thm.no_attributes)
        (map (Binding.suffix_name "_def") binds ~~ eqns) thy

    (* prove applied version of definitions *)
    fun prove_proj (lhs, rhs) =
      let
        fun tac ctxt = rewrite_goals_tac ctxt fixdef_thms THEN
          simp_tac (put_simpset beta_ss ctxt) 1
        val goal = Logic.mk_equals (lhs, rhs)
      in Goal.prove_global thy [] [] goal (tac o #context) end
    val proj_thms = map prove_proj projs

    (* mk_tuple lhss == fixpoint *)
    fun pair_equalI (thm1, thm2) = @{thm Pair_equalI} OF [thm1, thm2]
    val tuple_fixdef_thm = foldr1 pair_equalI proj_thms

    val cont_thm =
      let
        val ctxt = Proof_Context.init_global thy
        val prop = mk_trp (mk_cont functional)
        val rules = Named_Theorems.get ctxt @{named_theorems cont2cont}
        val tac = REPEAT_ALL_NEW (match_tac ctxt (rev rules)) 1
      in
        Goal.prove_global thy [] [] prop (K tac)
      end

    val tuple_unfold_thm =
      (@{thm def_cont_fix_eq} OF [tuple_fixdef_thm, cont_thm])
      |> Local_Defs.unfold (Proof_Context.init_global thy) @{thms split_conv}

    fun mk_unfold_thms [] _ = []
      | mk_unfold_thms (n::[]) thm = [(n, thm)]
      | mk_unfold_thms (n::ns) thm = let
          val thmL = thm RS @{thm Pair_eqD1}
          val thmR = thm RS @{thm Pair_eqD2}
        in (n, thmL) :: mk_unfold_thms ns thmR end
    val unfold_binds = map (Binding.suffix_name "_unfold") binds

    (* register unfold theorems *)
    val (unfold_thms, thy) =
      (Global_Theory.add_thms o map (Thm.no_attributes o apsnd Drule.zero_var_indexes))
        (mk_unfold_thms unfold_binds tuple_unfold_thm) thy
  in
    ((proj_thms, unfold_thms, cont_thm), thy)
  end

(******************************************************************************)
(****************** deflation combinators and map functions *******************)
(******************************************************************************)

fun defl_of_typ
    (thy : theory)
    (rules' : (term * term) list)
    (T : typ) : term =
  let
    val defl_simps = Global_Theory.get_thms thy "domain_defl_simps"
    val rules = map (Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq) defl_simps
    fun proc1 t =
      (case dest_DEFL t of
        TFree (a, _) => SOME (Free ("d" ^ Library.unprefix "'" a, deflT))
      | _ => NONE) handle TERM _ => NONE
    fun proc2 t =
      (case dest_LIFTDEFL t of
        TFree (a, _) => SOME (Free ("p" ^ Library.unprefix "'" a, udeflT))
      | _ => NONE) handle TERM _ => NONE
  in
    Pattern.rewrite_term thy (rules @ rules') [proc1, proc2] (mk_DEFL T)
  end

(******************************************************************************)
(********************* declaring definitions and theorems *********************)
(******************************************************************************)

fun define_const
    (bind : binding, rhs : term)
    (thy : theory)
    : (term * thm) * theory =
  let
    val typ = Term.fastype_of rhs
    val (const, thy) = Sign.declare_const_global ((bind, typ), NoSyn) thy
    val eqn = Logic.mk_equals (const, rhs)
    val def = Thm.no_attributes (Binding.suffix_name "_def" bind, eqn)
    val (def_thm, thy) = yield_singleton (Global_Theory.add_defs false) def thy
  in
    ((const, def_thm), thy)
  end

fun add_qualified_thm name (dbind, thm) =
    yield_singleton Global_Theory.add_thms
      ((Binding.qualify_name true dbind name, thm), [])

(******************************************************************************)
(*************************** defining map functions ***************************)
(******************************************************************************)

fun define_map_functions
    (spec : (binding * Domain_Take_Proofs.iso_info) list)
    (thy : theory) =
  let

    (* retrieve components of spec *)
    val dbinds = map fst spec
    val iso_infos = map snd spec
    val dom_eqns = map (fn x => (#absT x, #repT x)) iso_infos
    val rep_abs_consts = map (fn x => (#rep_const x, #abs_const x)) iso_infos

    fun mapT T =
      map (fn T => T ->> T) (filter (is_cpo thy) (argumentTs T)) -->> (T ->> T)

    (* declare map functions *)
    fun declare_map_const (tbind, (lhsT, _)) thy =
      let
        val map_type = mapT lhsT
        val map_bind = Binding.suffix_name "_map" tbind
      in
        Sign.declare_const_global ((map_bind, map_type), NoSyn) thy
      end
    val (map_consts, thy) = thy |>
      fold_map declare_map_const (dbinds ~~ dom_eqns)

    (* defining equations for map functions *)
    local
      fun unprime a = Library.unprefix "'" a
      fun mapvar T = Free (unprime (fst (dest_TFree T)), T ->> T)
      fun map_lhs (map_const, lhsT) =
        (lhsT, list_ccomb (map_const, map mapvar (filter (is_cpo thy) (argumentTs lhsT))))
      val tab1 = map map_lhs (map_consts ~~ map fst dom_eqns)
      val Ts = (argumentTs o fst o hd) dom_eqns
      val tab = (Ts ~~ map mapvar Ts) @ tab1
      fun mk_map_spec (((rep_const, abs_const), _), (lhsT, rhsT)) =
        let
          val lhs = Domain_Take_Proofs.map_of_typ thy tab lhsT
          val body = Domain_Take_Proofs.map_of_typ thy tab rhsT
          val rhs = mk_cfcomp (abs_const, mk_cfcomp (body, rep_const))
        in mk_eqs (lhs, rhs) end
    in
      val map_specs =
          map mk_map_spec (rep_abs_consts ~~ map_consts ~~ dom_eqns)
    end

    (* register recursive definition of map functions *)
    val map_binds = map (Binding.suffix_name "_map") dbinds
    val ((map_apply_thms, map_unfold_thms, map_cont_thm), thy) =
      add_fixdefs (map_binds ~~ map_specs) thy

    (* prove deflation theorems for map functions *)
    val deflation_abs_rep_thms = map deflation_abs_rep iso_infos
    val deflation_map_thm =
      let
        fun unprime a = Library.unprefix "'" a
        fun mk_f T = Free (unprime (fst (dest_TFree T)), T ->> T)
        fun mk_assm T = mk_trp (mk_deflation (mk_f T))
        fun mk_goal (map_const, (lhsT, _)) =
          let
            val Ts = argumentTs lhsT
            val map_term = list_ccomb (map_const, map mk_f (filter (is_cpo thy) Ts))
          in mk_deflation map_term end
        val assms = (map mk_assm o filter (is_cpo thy) o argumentTs o fst o hd) dom_eqns
        val goals = map mk_goal (map_consts ~~ dom_eqns)
        val goal = mk_trp (foldr1 HOLogic.mk_conj goals)
        val adm_rules =
          @{thms adm_conj adm_subst [OF _ adm_deflation]
                 cont2cont_fst cont2cont_snd cont_id}
        val bottom_rules =
          @{thms fst_strict snd_strict deflation_bottom simp_thms}
        val tuple_rules =
          @{thms split_def fst_conv snd_conv}
        val deflation_rules =
          @{thms conjI deflation_ID}
          @ deflation_abs_rep_thms
          @ Domain_Take_Proofs.get_deflation_thms thy
      in
        Goal.prove_global thy [] assms goal (fn {prems, context = ctxt, ...} =>
         EVERY
          [rewrite_goals_tac ctxt map_apply_thms,
           resolve_tac ctxt [map_cont_thm RS @{thm cont_fix_ind}] 1,
           REPEAT (resolve_tac ctxt adm_rules 1),
           simp_tac (put_simpset HOL_basic_ss ctxt addsimps bottom_rules) 1,
           simp_tac (put_simpset HOL_basic_ss ctxt addsimps tuple_rules) 1,
           REPEAT (eresolve_tac ctxt @{thms conjE} 1),
           REPEAT (resolve_tac ctxt (deflation_rules @ prems) 1 ORELSE assume_tac ctxt 1)])
      end
    fun conjuncts [] _ = []
      | conjuncts (n::[]) thm = [(n, thm)]
      | conjuncts (n::ns) thm = let
          val thmL = thm RS @{thm conjunct1}
          val thmR = thm RS @{thm conjunct2}
        in (n, thmL):: conjuncts ns thmR end
    val deflation_map_binds = dbinds |>
        map (Binding.prefix_name "deflation_" o Binding.suffix_name "_map")
    val (deflation_map_thms, thy) = thy |>
      (Global_Theory.add_thms o map (Thm.no_attributes o apsnd Drule.zero_var_indexes))
        (conjuncts deflation_map_binds deflation_map_thm)

(*
    (* register indirect recursion in theory data *)
    local
      fun register_map (dname, args) =
        Domain_Take_Proofs.add_rec_type (dname, args)
      val dnames = map (fst o dest_Type o fst) dom_eqns
      fun args (T, _) = case T of Type (_, Ts) => map (is_cpo thy) Ts | _ => []
      val argss = map args dom_eqns
    in
      val thy =
          fold register_map (dnames ~~ argss) thy
    end
*)

    (* register deflation theorems *)
    val thy = fold Domain_Take_Proofs.add_deflation_thm deflation_map_thms thy

    val result =
      {
        map_consts = map_consts,
        map_apply_thms = map_apply_thms,
        map_unfold_thms = map_unfold_thms,
        map_cont_thm = map_cont_thm,
        deflation_map_thms = deflation_map_thms
      }
  in
    (result, thy)
  end

(******************************************************************************)
(******************************* main function ********************************)
(******************************************************************************)

fun domain_isomorphism
    (param : string)
    (doms : ((string * sort) list * binding * mixfix * typ *
             (binding * binding) option) list)
    (thy: theory)
    : (Domain_Take_Proofs.iso_info list
       * Domain_Take_Proofs.take_induct_info) * theory =
  let
    (* this theory is used just for parsing *)
    val tmp_thy = thy |>
      Sign.add_types_global (map (fn (tvs, tbind, mx, _, _) =>
        (tbind, length tvs, mx)) doms)

    (* declare arities in temporary theory *)
    val tmp_thy =
      let
        fun arity (vs, tbind, _, _, _) =
          (Sign.full_name thy tbind, map snd vs, @{sort "tycon"})
      in
        fold Axclass.arity_axiomatization (map arity doms) tmp_thy
      end

    (* check bifiniteness of right-hand sides *)
    fun check_rhs (_, _, _, rhs, _) =
      if Sign.of_sort tmp_thy (rhs, @{sort "domain"}) then ()
      else error ("Type not of sort domain: " ^
        quote (Syntax.string_of_typ_global tmp_thy rhs))
    val _ = map check_rhs doms

    (* domain equations *)
    val paramT = TFree (param, @{sort domain})
    fun mk_tc_eqn (vs, tbind, _, rhs, _) =
      (Type (Sign.full_name tmp_thy tbind, map TFree vs), rhs)
    val tc_eqns = map mk_tc_eqn doms
    fun mk_dom_eqn (vs, tbind, _, rhs, _) =
      (mk_appT paramT (Type (Sign.full_name tmp_thy tbind, map TFree vs)), rhs)
    val dom_eqns = map mk_dom_eqn doms

    (* check for valid type parameters *)
    val (tyvars, _, _, _, _) = hd doms
    val _ = map (fn (tvs, tname, _, _, _) =>
      let val full_tname = Sign.full_name tmp_thy tname
      in
        (case duplicates (op =) (map fst tvs) of
          [] =>
            if eq_set (op =) (tyvars, tvs) then (full_tname, tvs)
            else error ("Mutually recursive domains must have same type parameters")
        | dups => error ("Duplicate parameter(s) for domain " ^ Binding.print tname ^
            " : " ^ commas dups))
      end) doms
    val dbinds = map (fn (_, dbind, _, _, _) => dbind) doms
    val morphs = map (fn (_, _, _, _, morphs) => morphs) doms

    (* determine deflation combinator arguments *)
    val tcs : typ list = map fst tc_eqns
    val param_defl = Free ("d" ^ Library.unprefix "'" param, deflT)
    val lhsTs : typ list = map fst dom_eqns
    val defl_rec = Free ("t", mk_tupleT (map (K deflT) lhsTs))
    val defl_rews = mk_projs (map (fn T => mk_capply (mk_TC T, param_defl)) tcs) defl_rec

    fun defl_body (_, _, _, rhsT, _) = defl_of_typ tmp_thy defl_rews rhsT
    val functional = Term.lambda defl_rec (mk_tuple (map defl_body doms))

    val tfrees = Term.add_tfrees functional []
    val frees = map fst (Term.add_frees functional [])
    fun get_defl_flags (vs, _, _, _, _) =
      let
        fun argT v = TFree v
        fun mk_d v = "d" ^ Library.unprefix "'" (fst v)
        fun mk_p v = "p" ^ Library.unprefix "'" (fst v)
        val args = maps (fn v => [(mk_d v, mk_DEFL (argT v)), (mk_p v, mk_LIFTDEFL (argT v))]) vs
        val typeTs = map argT (filter (member (op =) tfrees) vs)
        val defl_args = map snd (filter (member (op =) frees o fst) args)
      in
        (typeTs, defl_args)
      end
    val defl_flagss = map get_defl_flags doms

    (* declare deflation combinator constants *)
    fun declare_defl_const ((typeTs, defl_args), (_, tbind, _, _, _)) thy =
      let
        val defl_bind = Binding.suffix_name "_defl" tbind
        val defl_type =
          map Term.itselfT typeTs ---> map fastype_of defl_args -->> deflT ->> deflT
      in
        Sign.declare_const_global ((defl_bind, defl_type), NoSyn) thy
      end
    val (defl_consts, thy) =
      fold_map declare_defl_const (defl_flagss ~~ doms) thy
    val (_, tmp_thy) =
      fold_map declare_defl_const (defl_flagss ~~ doms) tmp_thy

    (* defining equations for type combinators *)
    fun mk_defl_term (defl_const, (typeTs, defl_args)) =
      let
        val type_args = map Logic.mk_type typeTs
      in
        list_ccomb (list_comb (defl_const, type_args), defl_args @ [param_defl])
      end
    val defl_terms = map mk_defl_term (defl_consts ~~ defl_flagss)
    val defl_rews = map fst defl_rews ~~ defl_terms
    fun mk_defl_spec (lhsT, rhsT) =
      mk_eqs (defl_of_typ tmp_thy defl_rews lhsT,
              defl_of_typ tmp_thy defl_rews rhsT)
    val defl_specs = map mk_defl_spec dom_eqns

    (* register recursive definition of deflation combinators *)
    val defl_binds = map (Binding.suffix_name "_defl") dbinds
    val ((defl_apply_thms, defl_unfold_thms, defl_cont_thm), thy) =
      add_fixdefs (defl_binds ~~ defl_specs) thy

    (* define tycons using deflation combinators *)
    fun make_tycondef ((vs, tbind, mx, _, _), tc) thy =
      let
        val spec = (tbind, vs, mx)
        val ((full_tname, info), thy) = define_singleton_type spec thy
        val newT = #abs_type (#1 info)
        val lhs_tfrees = map dest_TFree (snd (dest_Type newT))
        val tc_eqn = Logic.mk_equals (tc_const newT, Abs ("", Term.itselfT newT, tc))
        val ((_, (_, tc_ldef)), lthy) = thy
          |> Class.instantiation ([full_tname], lhs_tfrees, @{sort tycon})
          |> Specification.definition NONE [] []
              ((Binding.prefix_name "tc_" (Binding.suffix_name "_def" tbind), []), tc_eqn)
        val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
        val tc_def = singleton (Proof_Context.export lthy ctxt_thy) tc_ldef
        val thy = lthy
          |> Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt [])
        (* declare domain_defl_simps *)
        val attr = @{attributes [domain_defl_simps]}
          |> map (Attrib.attribute_global thy)
        val tc_thm = Drule.zero_var_indexes (tc_def RS TC_simp)
        val tc_thm_bind = Binding.prefix_name "TC_" tbind
        val (_, thy) = thy |> Global_Theory.add_thm ((tc_thm_bind, tc_thm), attr)
      in
        (tc_def, thy)
      end
    fun mk_defl_term (defl_const, (typeTs, defl_args)) =
      let
        val type_args = map Logic.mk_type typeTs
      in
        list_ccomb (list_comb (defl_const, type_args), defl_args)
      end
    val defl_terms = map mk_defl_term (defl_consts ~~ defl_flagss)
    val (tc_defs, thy) = fold_map make_tycondef (doms ~~ defl_terms) thy

    (* prove DEFL equations *)
    fun mk_DEFL_eq_thm (lhsT, rhsT) =
      let
        val goal = mk_eqs (mk_DEFL lhsT, mk_DEFL rhsT)
        val DEFL_simps = Global_Theory.get_thms thy "domain_defl_simps"
        fun tac ctxt =
          rewrite_goals_tac ctxt (map mk_meta_eq DEFL_simps @ tc_defs)
          THEN TRY (resolve_tac ctxt defl_unfold_thms 1)
      in
        Goal.prove_global thy [] [] goal (tac o #context)
      end
    val DEFL_eq_thms = map mk_DEFL_eq_thm dom_eqns

    (* register DEFL equations *)
    val DEFL_eq_binds = map (Binding.prefix_name "DEFL_eq_") dbinds
    val (_, thy) = thy |>
      (Global_Theory.add_thms o map Thm.no_attributes)
        (DEFL_eq_binds ~~ DEFL_eq_thms)

    (* define rep/abs functions *)
    fun mk_rep_abs ((tbind, _), (lhsT, rhsT)) thy =
      let
        val rep_bind = Binding.suffix_name "_rep" tbind
        val abs_bind = Binding.suffix_name "_abs" tbind
        val ((rep_const, rep_def), thy) =
            define_const (rep_bind, coerce_const (lhsT, rhsT)) thy
        val ((abs_const, abs_def), thy) =
            define_const (abs_bind, coerce_const (rhsT, lhsT)) thy
      in
        (((rep_const, abs_const), (rep_def, abs_def)), thy)
      end
    val ((rep_abs_consts, rep_abs_defs), thy) = thy
      |> fold_map mk_rep_abs (dbinds ~~ morphs ~~ dom_eqns)
      |>> ListPair.unzip

    (* prove isomorphism and isodefl rules *)
    fun mk_iso_thms ((tbind, DEFL_eq), (rep_def, abs_def)) thy =
      let
        fun make thm =
            Drule.zero_var_indexes (thm OF [DEFL_eq, abs_def, rep_def])
        val rep_iso_thm = make @{thm domain_rep_iso}
        val abs_iso_thm = make @{thm domain_abs_iso}
        val isodefl_thm = make @{thm isodefl_abs_rep}
        val thy = thy
          |> snd o add_qualified_thm "rep_iso" (tbind, rep_iso_thm)
          |> snd o add_qualified_thm "abs_iso" (tbind, abs_iso_thm)
          |> snd o add_qualified_thm "isodefl_abs_rep" (tbind, isodefl_thm)
      in
        (((rep_iso_thm, abs_iso_thm), isodefl_thm), thy)
      end
    val ((iso_thms, isodefl_abs_rep_thms), thy) =
      thy
      |> fold_map mk_iso_thms (dbinds ~~ DEFL_eq_thms ~~ rep_abs_defs)
      |>> ListPair.unzip

    (* collect info about rep/abs *)
    val iso_infos : Domain_Take_Proofs.iso_info list =
      let
        fun mk_info (((lhsT, rhsT), (repC, absC)), (rep_iso, abs_iso)) =
          {
            repT = rhsT,
            absT = lhsT,
            rep_const = repC,
            abs_const = absC,
            rep_inverse = rep_iso,
            abs_inverse = abs_iso
          }
      in
        map mk_info (dom_eqns ~~ rep_abs_consts ~~ iso_thms)
      end

    (* definitions and proofs related to map functions *)
    val (map_info, thy) =
        define_map_functions (dbinds ~~ iso_infos) thy
    val { map_consts, map_apply_thms, map_cont_thm, ...} = map_info

    (* prove isodefl rules for map functions *)
    val isodefl_thm =
      let
        fun unprime a = Library.unprefix "'" a
        fun mk_d T = Free ("d" ^ unprime (fst (dest_TFree T)), deflT)
        fun mk_p T = Free ("p" ^ unprime (fst (dest_TFree T)), udeflT)
        fun mk_f T = Free ("f" ^ unprime (fst (dest_TFree T)), T ->> T)
        fun mk_assm t =
          case try dest_LIFTDEFL t of
            SOME T => mk_trp (isodefl'_const T $ mk_f T $ mk_p T)
          | NONE =>
            let val T = dest_DEFL t
            in mk_trp (isodefl_const T $ mk_f T $ mk_d T) end
        fun mk_goal (map_const, ((T, _), defl_term)) =
          let
            val Ts = argumentTs T
            val map_term = list_ccomb (map_const, map mk_f (filter (is_cpo thy) Ts))
            val rews1 = map mk_DEFL Ts ~~ map mk_d Ts
            val rews2 = map mk_LIFTDEFL Ts ~~ map mk_p Ts
            val rews3 = [((mk_TC o snd o dest_appT) T, defl_term)]
            val rews = rews1 @ rews2 @ rews3
            val defl_term = defl_of_typ thy rews T
          in isodefl_const T $ map_term $ defl_term end
        val assms = (map mk_assm o snd o hd) defl_flagss
          @ [mk_trp (isodefl_const paramT $ mk_f paramT $ mk_d paramT)]
        val goals = map mk_goal (map_consts ~~ (dom_eqns ~~ defl_terms))
        val goal = mk_trp (foldr1 HOLogic.mk_conj goals)
        val adm_rules =
          @{thms adm_conj adm_isodefl cont2cont_fst cont2cont_snd cont_id}
        val bottom_rules =
          @{thms fst_strict snd_strict isodefl_bottom simp_thms}
        val tuple_rules =
          @{thms split_def fst_conv snd_conv}
        val map_ID_thms = Domain_Take_Proofs.get_map_ID_thms thy
        val map_ID_simps = map (fn th => th RS sym) map_ID_thms
        val isodefl_rules =
          @{thms conjI isodefl_ID_DEFL isodefl_LIFTDEFL}
          @ isodefl_abs_rep_thms
          @ Global_Theory.get_thms thy "domain_isodefl"
      in
        Goal.prove_global thy [] assms goal (fn {prems, context = ctxt, ...} =>
         EVERY
          [rewrite_goals_tac ctxt (defl_apply_thms @ map_apply_thms),
           resolve_tac ctxt [@{thm cont_parallel_fix_ind} OF [defl_cont_thm, map_cont_thm]] 1,
           REPEAT (resolve_tac ctxt adm_rules 1),
           simp_tac (put_simpset HOL_basic_ss ctxt addsimps bottom_rules) 1,
           simp_tac (put_simpset HOL_basic_ss ctxt addsimps tuple_rules) 1,
           simp_tac (put_simpset HOL_basic_ss ctxt addsimps map_ID_simps) 1,
           REPEAT (eresolve_tac ctxt @{thms conjE} 1),
           REPEAT (resolve_tac ctxt (isodefl_rules @ prems) 1 ORELSE assume_tac ctxt 1)])
      end
    val isodefl_binds = map (Binding.prefix_name "isodefl_") dbinds
    val isodefl_attr = @{attributes [domain_isodefl]}
      |> map (Attrib.attribute_global thy)
    fun conjuncts [] _ = []
      | conjuncts (n::[]) thm = [(n, thm)]
      | conjuncts (n::ns) thm = let
          val thmL = thm RS @{thm conjunct1}
          val thmR = thm RS @{thm conjunct2}
        in (n, thmL):: conjuncts ns thmR end
    val (isodefl_thms, thy) = thy |>
      (Global_Theory.add_thms o map (rpair isodefl_attr o apsnd Drule.zero_var_indexes))
        (conjuncts isodefl_binds isodefl_thm)

    (* prove map_ID theorems *)
    fun prove_map_ID_thm
        (((map_const, (lhsT, _)), DEFL_thm), isodefl_thm) =
      let
        val Ts = argumentTs lhsT
        fun is_cpo T = Sign.of_sort thy (T, @{sort cpo})
        val lhs = list_ccomb (map_const, map mk_ID (filter is_cpo Ts))
        val goal = mk_eqs (lhs, mk_ID lhsT)
        fun tac ctxt = EVERY
          [resolve_tac ctxt @{thms isodefl_DEFL_imp_ID} 1,
           stac ctxt @{thm DEFL_app} 1,
           stac ctxt DEFL_thm 1,
           resolve_tac ctxt [isodefl_thm] 1,
           REPEAT (resolve_tac ctxt @{thms isodefl_ID_DEFL isodefl_LIFTDEFL} 1)]
      in
        Goal.prove_global thy [] [] goal (tac o #context)
      end
    val map_ID_binds = map (Binding.suffix_name "_map_ID") dbinds
    val map_ID_thms =
      map prove_map_ID_thm
        (map_consts ~~ dom_eqns ~~ tc_defs ~~ isodefl_thms)
    val (_, thy) = thy |>
      (Global_Theory.add_thms o map (rpair [Domain_Take_Proofs.map_ID_add]))
        (map_ID_binds ~~ map_ID_thms)

    (* definitions and proofs related to take functions *)
    val (take_info, thy) =
        Domain_Take_Proofs.define_take_functions
          (dbinds ~~ iso_infos) thy
    val { take_consts, chain_take_thms, take_0_thms, take_Suc_thms, ...} =
        take_info

    (* least-upper-bound lemma for take functions *)
    val lub_take_lemma =
      let
        val lhs = mk_tuple (map mk_lub take_consts)
        fun is_cpo T = Sign.of_sort thy (T, @{sort cpo})
        fun mk_map_ID (map_const, (lhsT, _)) =
          list_ccomb (map_const, map mk_ID (filter is_cpo (argumentTs lhsT)))
        val rhs = mk_tuple (map mk_map_ID (map_consts ~~ dom_eqns))
        val goal = mk_trp (mk_eq (lhs, rhs))
        val map_ID_thms = Domain_Take_Proofs.get_map_ID_thms thy
        val start_rules =
            @{thms lub_Pair [symmetric] ch2ch_Pair} @ chain_take_thms
            @ @{thms prod.collapse split_def}
            @ map_apply_thms @ map_ID_thms
        val rules0 =
            @{thms iterate_0 Pair_strict} @ take_0_thms
        val rules1 =
            @{thms iterate_Suc prod_eq_iff fst_conv snd_conv}
            @ take_Suc_thms
        fun tac ctxt =
            EVERY
            [simp_tac (put_simpset HOL_basic_ss ctxt addsimps start_rules) 1,
             simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms fix_def2}) 1,
             resolve_tac ctxt @{thms lub_eq} 1,
             resolve_tac ctxt @{thms nat.induct} 1,
             simp_tac (put_simpset HOL_basic_ss ctxt addsimps rules0) 1,
             asm_full_simp_tac (put_simpset beta_ss ctxt addsimps rules1) 1]
      in
        Goal.prove_global thy [] [] goal (tac o #context)
      end

    (* prove lub of take equals ID *)
    fun prove_lub_take (((dbind, take_const), map_ID_thm), (lhsT, _)) thy =
      let
        val n = Free ("n", natT)
        val goal = mk_eqs (mk_lub (lambda n (take_const $ n)), mk_ID lhsT)
        fun tac ctxt =
            EVERY
            [resolve_tac ctxt @{thms trans} 1,
             resolve_tac ctxt [map_ID_thm] 2,
             cut_facts_tac [lub_take_lemma] 1,
             REPEAT (eresolve_tac ctxt @{thms Pair_inject} 1), assume_tac ctxt 1]
        val lub_take_thm = Goal.prove_global thy [] [] goal (tac o #context)
      in
        add_qualified_thm "lub_take" (dbind, lub_take_thm) thy
      end
    val (lub_take_thms, thy) =
        fold_map prove_lub_take
          (dbinds ~~ take_consts ~~ map_ID_thms ~~ dom_eqns) thy

    (* prove additional take theorems *)
    val (take_info2, thy) =
        Domain_Take_Proofs.add_lub_take_theorems
          (dbinds ~~ iso_infos) take_info lub_take_thms thy

    fun fmapU_const T =
      let val U = mk_appT udomT T
      in Const (@{const_name fmapU}, (udomT ->> udomT) ->> (U ->> U)) end

    (* instantiate prefunctor class *)
    fun inst_prefunctor (map_const, ((lhsT, _), tbind)) thy =
      let
        val (_, tyconT) = dest_appT lhsT
        val (full_tname, Ts) = dest_Type tyconT
        val lhs_tfrees = map dest_TFree Ts
        val argTs = filter (is_cpo thy) Ts
        val U = mk_appT udomT tyconT
        val mapT = map (fn T => T ->> T) argTs -->> (udomT ->> udomT) ->> (U ->> U)
        val mapC = Const (fst (dest_Const map_const), mapT)
        val fmap_rhs = list_ccomb (mapC, map mk_ID argTs)
        val fmap_eqn = Logic.mk_equals (fmapU_const tyconT, fmap_rhs)
        val fmap_def_bind = tbind
          |> Binding.suffix_name "_def"
          |> Binding.prefix_name "fmapU_"
        val ((_, (_, fmap_ldef)), lthy) = thy
          |> Class.instantiation ([full_tname], lhs_tfrees, @{sort prefunctor})
          |> Specification.definition NONE [] [] ((fmap_def_bind, []), fmap_eqn)
        val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy)
        val fmap_def = singleton (Proof_Context.export lthy ctxt_thy) fmap_ldef
        fun tacf ctxt = EVERY
          [Class.intro_classes_tac ctxt [],
           rewrite_goals_tac ctxt (fmap_def :: tc_defs),
           resolve_tac ctxt isodefl_thms 1,
           REPEAT (resolve_tac ctxt @{thms isodefl_ID_DEFL isodefl_LIFTDEFL isodefl_cast} 1)]
        val thy = lthy
          |> Class.prove_instantiation_exit tacf
      in
        (fmap_def, thy)
      end
    val (fmap_defs, thy) = fold_map inst_prefunctor
      (map_consts ~~ (dom_eqns ~~ dbinds)) thy
  in
    ((iso_infos, take_info2), thy)
  end

(******************************************************************************)
(****************************** top-level command *****************************)
(******************************************************************************)

(* ----- calls for building new thy and thms -------------------------------- *)

type info =
     Domain_Take_Proofs.iso_info list * Domain_Take_Proofs.take_induct_info

fun add_arity ((b, sorts, mx), sort) thy : theory =
  thy
  |> Sign.add_types_global [(b, length sorts, mx)]
  |> Axclass.arity_axiomatization (Sign.full_name thy b, sorts, sort)

fun gen_add_tycon
    (prep_sort : theory -> 'a -> sort)
    (prep_typ : theory -> (string * sort) list -> 'b -> typ)
    (arg_sort : bool -> sort)
    (raw_specs : (string * (string * 'a) list * binding * mixfix *
               (binding * (bool * binding option * 'b) list * mixfix) list) list)
    (thy : theory) =
  let
    val dtnvs0 : (binding * (string * sort) list * mixfix) list =
        map (fn (a, vs, dbind, mx, _) =>
            (dbind, map (apsnd (prep_sort thy)) vs, mx)) raw_specs

    val dtnvs : (binding * typ list * mixfix) list =
      let
        fun prep_tvar (a, s) = TFree (a, prep_sort thy s)
      in
        map (fn (a, vs, dbind, mx, _) =>
                (dbind, map prep_tvar vs, mx)) raw_specs
      end

    fun thy_arity (dbind, tvars, mx) =
      ((dbind, map (snd o dest_TFree) tvars, mx), @{sort tycon})

    (* this theory is used just for parsing and error checking *)
    val tmp_thy = thy
      |> fold (add_arity o thy_arity) dtnvs

    val dbinds : binding list =
        map (fn (_,_,dbind,_,_) => dbind) raw_specs
    val raw_rhss :
        (binding * (bool * binding option * 'b) list * mixfix) list list =
        map (fn (_,_,_,_,cons) => cons) raw_specs
    val dtnvs' : (string * typ list) list =
        map (fn (dbind, vs, _) => (Sign.full_name thy dbind, vs)) dtnvs

    val all_cons = map (Binding.name_of o first) (flat raw_rhss)
    val _ =
      case duplicates (op =) all_cons of 
        [] => false | dups => error ("Duplicate constructors: " 
                                      ^ commas_quote dups)
    val all_sels =
      (map Binding.name_of o map_filter second o maps second) (flat raw_rhss)
    val _ =
      case duplicates (op =) all_sels of
        [] => false | dups => error("Duplicate selectors: "^commas_quote dups)

    fun test_dupl_tvars s =
      case duplicates (op =) (map(fst o dest_TFree)s) of
        [] => false | dups => error("Duplicate type arguments: " 
                                    ^commas_quote dups)
    val _ = exists test_dupl_tvars (map snd dtnvs')

    val param : string * sort =
      let val all_params = map #1 raw_specs
      in
        case distinct (op =) all_params of
          [param] => (param, @{sort domain})
        | _ => error "Mutually recursive domains must have same type parameter"
      end

    val sorts : (string * sort) list =
      let val all_sorts = map (map dest_TFree o snd) dtnvs'
      in
        case distinct (eq_set (op =)) all_sorts of
          [sorts] => sorts
        | _ => error "Mutually recursive domains must have same type parameters"
      end

    val sorts' : (string * sort) list = param :: sorts

    (* a lazy argument may have an unpointed type *)
    (* unless the argument has a selector function *)
    fun check_pcpo (lazy, sel, T) =
      let val sort = arg_sort (lazy andalso is_none sel) in
        if Sign.of_sort tmp_thy (T, sort) then ()
        else error ("Constructor argument type is not of sort " ^
                    Syntax.string_of_sort_global tmp_thy sort ^ ": " ^
                    Syntax.string_of_typ_global tmp_thy T)
      end

    (* test for free type variables, illegal sort constraints on rhs,
       non-pcpo-types and invalid use of recursive type
       replace sorts in type variables on rhs *)
    val rec_tab = Domain_Take_Proofs.get_rec_tab thy
    fun check_rec _ (T as TFree (v,_))  =
        if AList.defined (op =) sorts' v then T
        else error ("Free type variable " ^ quote v ^ " on rhs.")
      | check_rec no_rec (T as Type (s, Ts)) =
        (case AList.lookup (op =) dtnvs' s of
          NONE =>
            let val no_rec' =
                  if no_rec = NONE then
                    if Symtab.defined rec_tab s then NONE else SOME s
                  else no_rec
            in Type (s, map (check_rec no_rec') Ts) end
        | SOME typevars =>
          if typevars <> Ts
          then error ("Recursion of type " ^ 
                      quote (Syntax.string_of_typ_global tmp_thy T) ^ 
                      " with different arguments")
          else (case no_rec of
                  NONE => T
                | SOME c =>
                  error ("Illegal indirect recursion of type " ^ 
                         quote (Syntax.string_of_typ_global tmp_thy T) ^
                         " under type constructor " ^ quote c)))
      | check_rec _ (TVar _) = error "extender:check_rec"

    fun prep_arg (lazy, sel, raw_T) =
      let
        val T = prep_typ tmp_thy sorts raw_T
(*
        val _ = check_rec NONE T
*)
        val _ = check_pcpo (lazy, sel, T)
      in (lazy, sel, T) end
    fun prep_con (b, args, mx) = (b, map prep_arg args, mx)
    fun prep_rhs cons = map prep_con cons
    val rhss : (binding * (bool * binding option * typ) list * mixfix) list list =
        map prep_rhs raw_rhss

    fun mk_arg_typ (lazy, _, T) = if lazy then mk_upT T else T
    fun mk_con_typ (_, args, _) =
        if null args then oneT else foldr1 mk_sprodT (map mk_arg_typ args)
    fun mk_rhs_typ cons = foldr1 mk_ssumT (map mk_con_typ cons)

    val repTs : typ list = map mk_rhs_typ rhss

    val doms : ((string * sort) list * binding * mixfix * typ * (binding * binding) option) list =
      map (fn ((tbind, vs, mx), repT) => (vs, tbind, mx, repT, NONE)) (dtnvs0 ~~ repTs)
    val ((iso_infos, take_info), thy) = domain_isomorphism (fst param) doms thy

    val (constr_infos, thy) =
        thy
          |> fold_map (fn ((dbind, cons), info) =>
                Domain_Constructors.add_domain_constructors dbind cons info)
             (dbinds ~~ rhss ~~ iso_infos)

    val (_, thy) =
        Domain_Induction.comp_theorems
          dbinds take_info constr_infos thy
  in
    thy
  end

fun rep_arg lazy = if lazy then @{sort predomain} else @{sort "domain"}

fun read_sort thy (SOME s) = Syntax.read_sort_global thy s
  | read_sort thy NONE = Sign.defaultS thy

(* Adapted from src/HOL/Tools/Datatype/datatype_data.ML *)
fun read_typ thy sorts str =
  let
    val ctxt = Proof_Context.init_global thy
      |> fold (Variable.declare_typ o TFree) sorts
  in Syntax.read_typ ctxt str end

fun cert_typ sign sorts raw_T =
  let
    val T = Type.no_tvars (Sign.certify_typ sign raw_T)
      handle TYPE (msg, _, _) => error msg
    val sorts' = Term.add_tfreesT T sorts
    val _ =
      case duplicates (op =) (map fst sorts') of
        [] => ()
      | dups => error ("Inconsistent sort constraints for " ^ commas dups)
  in T end

val add_tycon =
    gen_add_tycon (K I) cert_typ rep_arg

val add_tycon_cmd =
    gen_add_tycon read_sort read_typ rep_arg


(** outer syntax **)

val dest_decl : (bool * binding option * string) parser =
  @{keyword "("} |-- Scan.optional (@{keyword "lazy"} >> K true) false --
    (Parse.binding >> SOME) -- (@{keyword "::"} |-- Parse.typ)  --| @{keyword ")"} >> Scan.triple1
    || @{keyword "("} |-- @{keyword "lazy"} |-- Parse.typ --| @{keyword ")"}
    >> (fn t => (true,NONE,t))
    || Parse.typ >> (fn t => (false,NONE,t))

val cons_decl =
  Parse.binding -- Scan.repeat dest_decl -- Parse.opt_mixfix

val tycon_decl =
  (Parse.type_ident --| @{keyword "\<cdot>"} -- Parse.type_args_constrained --
    Parse.binding -- Parse.opt_mixfix) --
    (@{keyword "="} |-- Parse.enum1 "|" cons_decl)

val tycons_decl =
  Parse.and_list1 tycon_decl

fun mk_tycon
    (doms : ((((string * (string * string option) list) * binding) * mixfix) *
             ((binding * (bool * binding option * string) list) * mixfix) list) list ) =
  let
    val specs : (string * (string * string option) list * binding * mixfix *
                 (binding * (bool * binding option * string) list * mixfix) list) list =
        map (fn ((((a, vs), t), mx), cons) =>
                (a, vs, t, mx, map (fn ((c, ds), mx) => (c, ds, mx)) cons)) doms
  in
    add_tycon_cmd specs
  end

val _ =
  Outer_Syntax.command @{command_keyword tycondef}
    "define recursive type constructors (HOLCF)"
    (tycons_decl >> (Toplevel.theory o mk_tycon))

end
