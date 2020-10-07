fun prove_in_set ctxt t =
  let
    val cterm = Thm.cterm_of ctxt
    fun prove _ _ [] = raise TERM ("prove_in_set", [t])
      | prove x prefix (y::xs) =
          if x aconv y then
            let
              val ty = fastype_of x
              val cty = Thm.ctyp_of ctxt ty
            in
              @{thm insertI1}
              |> Thm.instantiate' [SOME cty] (map (SOME o cterm) [x, HOLogic.mk_set ty xs])
              |> fold (fn x => fn thm => 
                 (thm RS @{thm insertI2}) |> Thm.instantiate' [] [SOME (cterm x)]) prefix
            end
          else
            prove x (y :: prefix) xs
  in
    case t of
      Const (@{const_name Set.member}, _) $ x $ xs =>
        prove x [] (xs |> HOLogic.dest_set)
    | _ => raise TERM ("prove_in_set", [t])
  end

fun prove_in_list ctxt x xs =
  let
    val cterm = Thm.cterm_of ctxt
    fun prove _ _ [] = raise TERM ("prove_in_list", x :: xs)
      | prove x prefix (y::xs) =
          if x aconv y then
            let
              val ty = fastype_of x
              val cty = Thm.ctyp_of ctxt ty
            in
              @{thm list.set_intros(1)}
              |> Thm.instantiate' [SOME cty] (map (SOME o cterm) [x, HOLogic.mk_list ty xs])
              |> fold (fn x => fn thm => 
                 (thm RS @{thm list.set_intros(2)}) |> Thm.instantiate' [] [SOME (cterm x)]) prefix
            end
          else
            prove x (y :: prefix) xs
  in
    prove x [] xs
  end

fun eval_inverse_permutation_of_list_conv wf_thm ctxt ct =
  let
    fun err () = raise CTERM ("eval_inverse_permutation_of_list_conv", [ct])
    val t = Thm.term_of ct
    fun mk_eq xs (x, y) =
      let
        val xy = HOLogic.mk_prod (x, y)
        val thm = prove_in_list ctxt xy (HOLogic.dest_list xs)
      in
        @{thm eq_reflection} OF [@{thm inverse_permutation_of_list_unique} OF [wf_thm, thm]]
      end
    fun aux xs y =
      let
        val xs' = xs |> HOLogic.dest_list |> map HOLogic.dest_prod
      in
        case get_first (fn (x,y') => if y aconv y' then SOME x else NONE) xs' of
          NONE => err ()
        | SOME x => mk_eq xs (x, y)
      end
  in
    case t of
      Const (@{const_name inverse_permutation_of_list}, _) $ xs $ x => aux xs x
    | _ => err ()
  end

local
open Preference_Profiles
open Randomised_Social_Choice
open Preference_Profiles_Cmd

fun mk_permutation_term sigma = 
  let
    val altT = sigma |> hd |> fst |> fastype_of
  in
    sigma |> map HOLogic.mk_prod |> HOLogic.mk_list (HOLogic.mk_prodT (altT, altT))
  end

fun prepare_orbit_intro_thms_single ctxt sds_an_thm (p : info) ((x,y), sigma) =
  let
    val {wf_raw_thm = wf_raw_thm, def_thm = def_thm, ...} = p
    val cterm = Thm.cterm_of ctxt
    val sigma_term = mk_permutation_term sigma
    val thm = (@{thm an_sds_automorphism_aux} OF [wf_raw_thm, def_thm, sds_an_thm])
              |> Thm.instantiate' [] (map (SOME o cterm) [sigma_term, x, y])
  in
    thm
  end

fun prepare_orbit_intro_thms ctxt sds_an_thm (p : info) =
  let
    val {raw = p_raw, ...} = p
  in
    derive_orbit_equations p_raw
    |> map (prepare_orbit_intro_thms_single ctxt sds_an_thm p)
  end

fun get_agents_alts_term ({wf_thm, ...} : info) =
  let
    val agents :: alts :: _ = wf_thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> strip_comb |> snd
  in
    (agents, alts)
  end

in

val dest_wf_thm =
  Thm.concl_of #> HOLogic.dest_Trueprop #> Term.dest_comb #> snd

fun gen_derive_orbit_equations lthy sds_an_thm ps =
  let
    val lthy0 = lthy
    val infos = map (fn p => get_info p lthy) ps
    val (altT, agentT) = infos |> hd |> #raw |> (fn x => (altT x, agentT x))
    val sdsT = sdsT agentT altT

    val (sds, sds_an_thm, lthy) =
      case sds_an_thm of
        SOME sds_an_thm => (dest_wf_thm sds_an_thm, sds_an_thm, lthy)
      | NONE => 
          let
            val ([sds], lthy) = Variable.variant_fixes ["sds"] lthy0
            val sds = Free (sds, sdsT)
            val lthy = Variable.declare_term sds lthy
            val (agents_term, alts_term) = get_agents_alts_term (hd infos)
            val sds_an_const = Const (@{const_name an_sds}, HOLogic.mk_setT agentT --> 
              HOLogic.mk_setT altT --> sdsT --> HOLogic.boolT)
            val sds_an_prop = HOLogic.mk_Trueprop (sds_an_const $ agents_term $ alts_term $ sds)
            val ([sds_an_thm], lthy) = Assumption.add_assumes [Thm.cterm_of lthy sds_an_prop] lthy
          in
            (sds, sds_an_thm, lthy)
          end

    val intros = map (prepare_orbit_intro_thms lthy sds_an_thm) infos
    val goals = map (map (fn x => (Thm.concl_of x, []))) intros
    val bindings = infos |> map 
      (fn info => Binding.qualify true (Binding.name_of (#binding info)) (Binding.name "orbits"))
    val lthy = lthy addsimps @{thms multiset_add_ac insert_commute}

    val before_proof = 
      let
        fun tac ctxt = 
          ALLGOALS (resolve_tac ctxt (List.concat intros))
          THEN distinct_subgoals_tac
      in
        Method.Basic (SIMPLE_METHOD o tac)
      end

    fun afterqed (thmss : thm list list) lthy =
      let
        val thmss = burrow (Proof_Context.export lthy lthy0) thmss
        val thmss_aux = map2 (fn bdg => fn thms => ((bdg, []), [(thms, [])])) bindings thmss
      in
        Local_Theory.notes thmss_aux lthy0
        |> snd
      end
  in
    Proof.theorem NONE afterqed goals lthy
    |> Proof.refine_singleton before_proof
  end

fun derive_orbit_equations_cmd wf_thm ps lthy =
  gen_derive_orbit_equations lthy wf_thm (map (Syntax.read_term lthy) ps)

val optional_thm_parser = 
  Scan.option (Args.parens Parse.thm)

val optional_thms_parser = 
  Scan.option (Args.parens Parse.thms1)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword derive_orbit_equations}
    "automatically derives the orbit equations for preference profiles"
    ((optional_thm_parser -- Scan.repeat1 Parse.term) >> 
     (fn (wf_thm, ps) => fn ctxt => 
        let
          val wf_thm = Option.map (hd o Proof_Context.get_fact ctxt o fst) wf_thm
        in
          derive_orbit_equations_cmd wf_thm ps ctxt
        end))

fun gen_prepare_ex_post_conditions find_losers sds (info : info) lthy =
  let
    val {raw = p, wf_raw_thm, def_thm, ...} = info
    val losers = find_losers p
    val cterm = Thm.cterm_of lthy
    fun prep (x,y,i) = 
      (@{thm ex_post_efficient_aux} OF [wf_raw_thm, def_thm])
      |> Thm.instantiate' [] (map (SOME o cterm) [i, x, y, sds])
  in
    map prep losers
  end

val prepare_find_ex_post_conditions = 
  gen_prepare_ex_post_conditions pareto_losers

fun prepare_ex_post_conditions xs =
  gen_prepare_ex_post_conditions 
    (fn p => map_filter (fn (p', x) => if p = p' then find_pareto_witness p x else NONE) xs)

fun gen_prepare_sdeff_conditions find_supports sds (info : info) lthy =
  let
    val {raw = p, wf_raw_thm, def_thm, ...} = info
    val altT = altT p
    val supports = find_supports p
    val cterm = Thm.cterm_of lthy
    fun prep (supp,lott,i) = 
      let
        val supp_list = HOLogic.mk_list altT supp
        val supp_set = HOLogic.mk_set altT supp
        val lott = 
          lott
          |> map (HOLogic.mk_prod o apsnd (Rat_Utils.mk_rat_number @{typ Real.real}))
          |> HOLogic.mk_list (HOLogic.mk_prodT (altT, @{typ Real.real}))
      in
        (@{thm SD_inefficient_support_aux} OF [wf_raw_thm, def_thm])
        |> Thm.instantiate' [] (map (SOME o cterm) [supp_list, supp_set, lott, i, sds])
    end
  in
    map prep supports
  end

val prepare_find_sdeff_conditions = 
  gen_prepare_sdeff_conditions find_minimal_inefficient_supports

fun prepare_sdeff_conditions_from_wits ss = 
  gen_prepare_sdeff_conditions 
    (fn p => map_filter (
      fn (p', x, SOME y) => if p = p' then SOME (mk_support_witness p (x,y)) else NONE
        | _ => NONE) ss)

fun gen_derive_support_conditions providers sds_thms ps lthy =
  let
    val lthy0 = lthy
    val infos = map (fn p => get_info p lthy) ps
    val (altT, agentT) = infos |> hd |> #raw |> (fn x => (altT x, agentT x))
    val sdsT = sdsT agentT altT

    val (sds, sds_thms, lthy) =
      case sds_thms of
        SOME sds_thms => (dest_wf_thm (hd sds_thms), sds_thms, lthy)
      | NONE =>
          let
            val ([sds], lthy) = Variable.variant_fixes ["sds"] lthy0
            val sds = Free (sds, sdsT)
            val lthy = Variable.declare_term sds lthy
          in
            (sds, [], lthy)
          end

    val intros = map (fn info => List.concat (map (fn p => p sds info lthy) providers)) infos
    val goals = map (map (fn x => (Thm.concl_of x, []))) intros
    val bindings = infos |> map 
      (fn info => Binding.qualify true (Binding.name_of (#binding info)) (Binding.name "support"))

    val before_proof = 
      let
        fun tac ctxt = 
          ALLGOALS (resolve_tac ctxt (List.concat intros))
          THEN distinct_subgoals_tac
      in
        Method.Basic (SIMPLE_METHOD o tac)
      end

    fun get_first_default f xs default =
      case get_first f xs of
        NONE => default
      | SOME y => y

    fun postproc lthy thm =
      thm 
        |> (fn thm => thm RS @{thm HOL.mp})
        |> (fn thm => get_first_default (fn thm' => try (Thm.implies_elim thm) thm') sds_thms thm)
        |> Local_Defs.unfold lthy 
             (map (fn thm => thm RS @{thm eq_reflection}) @{thms Set.bex_simps disj_False_right})

    fun afterqed (thmss : thm list list) lthy =
      let
        val thmss = 
          thmss |> burrow (Proof_Context.export lthy lthy0 o map (postproc lthy))
        val thmss_aux = map2 (fn bdg => fn thms => ((bdg, []), [(thms, [])])) bindings thmss
      in
        Local_Theory.notes thmss_aux lthy0
        |> snd
      end
  in
    Proof.theorem NONE afterqed goals lthy
    |> Proof.refine_singleton before_proof
  end

fun gen_derive_support_conditions_cmd providers wf_thms ts lthy = 
  gen_derive_support_conditions providers wf_thms (map (Syntax.read_term lthy) ts) lthy

val derive_support_conditions_cmd = 
  gen_derive_support_conditions_cmd [prepare_find_ex_post_conditions, prepare_find_sdeff_conditions]

val derive_ex_post_conditions_cmd =
  gen_derive_support_conditions_cmd [prepare_find_ex_post_conditions]

fun find_inefficient_supports p =
  map (fn (x,_,_) => ([x], NONE)) (pareto_losers p) @
  map (fn (x,y,_) => (x, SOME y)) (find_minimal_inefficient_supports p)

fun find_sd_inefficient_supports_cmd ts lthy =
  let
    val ps = ts |> map (Syntax.read_term lthy #> (fn p => get_info p lthy))
    fun pretty_lott lott = Pretty.block [Pretty.str "witness:", Pretty.brk 1,
      Pretty.list "[" "]" 
        (map (fn (x,y) => Pretty.block 
          [Syntax.pretty_term lthy x, Pretty.str ":",
            Pretty.brk 1, Pretty.str (Rat.string_of_rat y)]) lott)]
    fun pretty (p, supp, lott) =
      Pretty.block ([
        Syntax.pretty_term lthy p, Pretty.brk 1,
        Pretty.list "[" "]" (map (Syntax.pretty_term lthy) supp)] @
        the_default [] (Option.map (fn x => [Pretty.brk 1, pretty_lott x]) lott))
  in
    maps (fn p => (map (fn (x,y) => (#term p,x,y)) 
      (find_inefficient_supports (#raw p)))) ps
    |> map (single o pretty)
    |> Library.separate [Pretty.keyword2 " and", Pretty.brk 1]
    |> (fn xs => [Pretty.keyword1 "prove_inefficient_supports", Pretty.fbrk] :: xs)
    |> flat
    |> Pretty.block
    |> Pretty.string_of
    |> Output.information o Active.sendback_markup_command
  end

fun prove_sd_inefficient_supports_cmd thm xs lthy =
  let
    val ts = map (fst o fst) xs
    val read = Syntax.read_term lthy
    val ts' = map read ts
    val ps = map (fn t => #raw (get_info t lthy)) ts'
    val supps = map (map read o snd o fst) xs
    val lotts = map (Option.map (map (apfst read)) o snd) xs
  in
    gen_derive_support_conditions_cmd 
      [prepare_sdeff_conditions_from_wits 
         (map_filter (fn ((_, [_]), _) => NONE | ((x,y),z) => SOME (x,y,z)) (ps ~~ supps ~~ lotts)),
       prepare_ex_post_conditions 
         (map_filter (fn (p, [x]) => SOME (p,x) | _ => NONE) (ps ~~ supps))]
      thm ts lthy
  end

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword derive_support_conditions}
    "automatically derive ex-post- and SD-Efficiency conditions for the support of preference profiles"
    (optional_thms_parser -- Scan.repeat1 Parse.term >> 
      (fn (thms, ts) => fn ctxt =>
         let
           val thms = Option.map (maps (Proof_Context.get_fact ctxt o fst)) thms
         in
           derive_support_conditions_cmd thms ts ctxt
         end));

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword derive_ex_post_conditions}
    "automatically derive zero-ness conditions for the Pareto losers"
    (optional_thm_parser -- Scan.repeat1 Parse.term >> 
      (fn (thm, ts) => fn ctxt =>
         let
           val thm = Option.map (Proof_Context.get_fact ctxt o fst) thm
         in
           derive_ex_post_conditions_cmd thm ts ctxt
         end));


val parse_rat =
  (Parse.int -- Scan.optional (Args.$$$ "/" |-- Parse.int) 1) >> Rat.make

val parse_support = Args.bracks (Parse.list1 Parse.term)

val parse_lottery = Args.bracks (Parse.list1 (Parse.term --| Args.colon -- parse_rat))

val _ =
  Outer_Syntax.local_theory @{command_keyword find_inefficient_supports}
    "automatically find SD-inefficient supports using linear programming"
    (Scan.repeat1 Parse.term >> (* TODO: is local_theory the right approach here? *)
      (fn ts => fn ctxt => 
         let
           val _ = find_sd_inefficient_supports_cmd ts ctxt
         in
           ctxt
         end));
  
val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword prove_inefficient_supports}
    "prove ex-post- or SD-inefficient supports (using witness lotteries for the latter)"
    (optional_thms_parser -- Parse.and_list1 (Parse.term -- parse_support -- 
       Scan.option (Args.$$$ "witness" |-- Args.colon |-- parse_lottery)) >> 
      (fn (thms, ts) => fn ctxt =>
         let
           val thms = Option.map (maps (Proof_Context.get_fact ctxt o fst)) thms
         in
           prove_sd_inefficient_supports_cmd thms ts ctxt
         end));




(* TODO: Move *)
fun pref_classes [] = [] 
  | pref_classes (xs :: xss) =
    let
      fun go _ acc2 [] = acc2
        | go acc1 acc2 (xs :: xss) = go (xs @ acc1) (rev acc1 :: acc2) xss
    in
      rev (go xs [] xss)
    end

fun combine_all f xs =
  let
    fun go acc [] = acc
      | go acc (x::xs) = 
          go (map (fn y => f (x, y)) xs @ map (fn y => f (y, x)) xs @ acc) xs
  in
    go [] xs
  end



fun prepare_strategyproofness_intro_thms ctxt dist_limit sds_san_thm (ps : info list) =
  let
    val altT = ps |> hd |> #raw |> altT
    val manipulations = 
      combine_all (fn (p1, p2) => (p1, p2, find_manipulations (#raw p1, #raw p2))) ps
    val manipulations =
      case dist_limit of
        NONE => manipulations
      | SOME l =>
          map (fn (p1, p2, ms) => (p1, p2, filter (fn x => #3 x <= l) ms)) manipulations
    (* For Debugging/extracting witnesses only *)
(*    val pretty_term_list = map (Pretty.quote o Syntax.pretty_term ctxt) #> Pretty.list "[" "]"
    val pretty_perm = 
      map (fn (a,b) => Pretty.block [Pretty.str "(", Pretty.quote (Syntax.pretty_term ctxt a), 
        Pretty.str ",", Pretty.quote (Syntax.pretty_term ctxt b), Pretty.str ")"])
      #> Pretty.list "[" "]"
    val foo =
      manipulations |> map (fn (p1 : info, p2 : info, ms) =>
        ms 
        |> map (fn (i, j, _, sigma) =>
          [Pretty.str "(", Binding.pretty (#binding p1), Pretty.str ",",
           Binding.pretty (#binding p2), Pretty.str ",",
           Pretty.quote (Syntax.pretty_term ctxt i), Pretty.str ",",
           Pretty.list "[" "]" (map pretty_term_list (the (AList.lookup op aconv (#raw p1) i))), Pretty.str ",",
           Pretty.list "[" "]" (map pretty_term_list (
            map (map (apply_reverse_permutation op aconv sigma)) (the (AList.lookup op aconv (#raw p2) j)))), Pretty.str ",",
           pretty_perm sigma, Pretty.str ")"]
          |> Pretty.block
          ))
        |> flat |> Pretty.list "[" "]" |> Pretty.writeln
*)
    fun mk_binding (p1, p2) =
      Binding.qualify true 
        (Binding.name_of (#binding p1) ^ "_" ^ Binding.name_of (#binding p2)) 
        (Binding.name "strategyproofness")
    fun mk_intro (p1, p2) (i, j, _, sigma) = 
      let
        val {wf_raw_thm = wf_raw_thm1, def_thm = def_thm1, raw = raw1, ...} = p1
        val {wf_raw_thm = wf_raw_thm2, def_thm = def_thm2, ...} = p2
        val sigma' = map (fn (a,b) => (b,a)) sigma
        val ps = AList.lookup op aconv raw1 i |> the |> pref_classes
                 |> map (HOLogic.mk_list altT) 
                 |> HOLogic.mk_set (HOLogic.listT altT)
        val insts = [i, j, mk_permutation_term sigma', ps]
      in
          (@{thm strategyproof_aux'} OF [wf_raw_thm1, def_thm1, wf_raw_thm2, def_thm2, sds_san_thm])
          |> Thm.instantiate' [] (map (SOME o Thm.cterm_of ctxt) insts)
      end
  in
    map (fn (p1, p2, xs) => (mk_binding (p1, p2), map (mk_intro (p1, p2)) xs)) manipulations
      : (binding * thm list) list
  end

fun gen_derive_strategyproofness_conditions lthy dist_limit sds_san_thm ps =
  let
    val lthy0 = lthy
    val infos = map (fn p => get_info p lthy) ps
    val (altT, agentT) = infos |> hd |> #raw |> (fn x => (altT x, agentT x))
    val sdsT = sdsT agentT altT

    val (sds, sds_san_thm, lthy) =
      case sds_san_thm of
        SOME sds_san_thm => (dest_wf_thm sds_san_thm, sds_san_thm, lthy)
      | NONE => 
          let
            val ([sds], lthy) = Variable.variant_fixes ["sds"] lthy0
            val sds = Free (sds, sdsT)
            val lthy = Variable.declare_term sds lthy
            val (agents_term, alts_term) = get_agents_alts_term (hd infos)
            val sds_san_const = Const (@{const_name strategyproof_an_sds},
               HOLogic.mk_setT agentT --> HOLogic.mk_setT altT --> sdsT --> HOLogic.boolT)
            val sds_san_prop = HOLogic.mk_Trueprop (sds_san_const $ agents_term $ alts_term $ sds)
            val ([sds_san_thm], lthy) = Assumption.add_assumes [Thm.cterm_of lthy sds_san_prop] lthy
          in
            (sds, sds_san_thm, lthy)
          end

    val intros = prepare_strategyproofness_intro_thms lthy dist_limit sds_san_thm infos
    val goals = map (map (fn x => (Thm.concl_of x, [])) o snd) intros
    val bindings = map fst intros
    val lthy = lthy addsimps 
      @{thms multiset_add_ac insert_commute insert_eq_iff multiset_Diff_single_normalize}

    val before_proof = 
      let
        fun tac ctxt = 
          ALLGOALS (resolve_tac ctxt (List.concat (map snd intros)))
          THEN distinct_subgoals_tac
      in
        Method.Basic (SIMPLE_METHOD o tac)
      end

    fun postproc lthy thm =
      let
        val perm_thm = thm RS @{thm HOL.conjunct1}
      in
        (thm RS @{thm HOL.conjunct2})
        |> Local_Defs.unfold lthy 
           @{thms Set.bex_simps Set.ball_simps HOL.simp_thms list.map sum_list.Cons sum_list.Nil
                  add_0_right less_or_eq_real}
        |> Conv.fconv_rule (Conv.top_sweep_conv 
             (eval_inverse_permutation_of_list_conv perm_thm) lthy)
      end

    fun afterqed (thmss : thm list list) lthy =
      let
        val thmss = burrow (Proof_Context.export lthy lthy0 o map (postproc lthy)) thmss
        val thmss_aux = map2 (fn bdg => fn thms => ((bdg, []), [(thms, [])])) bindings thmss
      in
        Local_Theory.notes thmss_aux lthy0
        |> snd
      end
  in
    Proof.theorem NONE afterqed goals lthy
    |> Proof.refine_singleton before_proof
  end

fun derive_strategyproofness_conditions_cmd dist_limit sds_san_thm ps lthy =
  gen_derive_strategyproofness_conditions lthy dist_limit sds_san_thm (map (Syntax.read_term lthy) ps)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword derive_strategyproofness_conditions}
    "automatically derives the conditions arising from strategy-proofness for preference profiles"
    ((optional_thm_parser -- Scan.option (Args.$$$ "distance" |-- Args.colon |-- Parse.int) 
        -- Scan.repeat1 Parse.term) >> 
     (fn ((wf_thm, dist_limit), ps) => fn ctxt => 
        let
          val wf_thm = Option.map (hd o Proof_Context.get_fact ctxt o fst) wf_thm
        in
          derive_strategyproofness_conditions_cmd dist_limit wf_thm ps ctxt
        end))


end
