(*
  File:   landau_simprocs.ML
  Author: Manuel Eberl <eberlm@in.tum.de>

  Simprocs for Landau symbols. 
*)
signature LANDAU =
sig
  val landau_const_names : string list
  val dest_landau : term -> term * term * term

  val lift_landau_conv : conv -> conv
  val lift_landau_simproc : 
    (Proof.context -> cterm -> thm option) -> Proof.context -> cterm -> thm option

  val cancel_factor_conv : Proof.context -> cterm -> thm
  val cancel_factor_simproc : Proof.context -> cterm -> thm option

  val simplify_landau_sum_conv : Proof.context -> conv
  val simplify_landau_sum_simproc : Proof.context -> cterm -> thm option

  val simplify_landau_product_conv : Proof.context -> conv
  val simplify_landau_product_simproc : Proof.context -> cterm -> thm option

  val simplify_landau_real_prod_prop_conv : Proof.context -> conv
  val simplify_landau_real_prod_prop_simproc : Proof.context -> cterm -> thm option

  val landau_sum_limit : int Config.T

end

structure Landau: LANDAU =
struct

val landau_sum_limit = Attrib.setup_config_int @{binding landau_sum_limit} (K 3)

fun landau_simprocs ctxt = map (Simplifier.the_simproc ctxt) 
  ["Landau_Simprocs.simplify_landau_product"]

val landau_const_names =
  [@{const_name "bigo"},@{const_name "smallo"},@{const_name "bigomega"},
   @{const_name "smallomega"},@{const_name "bigtheta"}]

fun get_landau_id (t as Const (s, _)) = 
      let
        val i = find_index (fn s' => s = s') landau_const_names
      in
        if i < 0 then raise TERM ("get_landau_id", [t]) else i
      end
  | get_landau_id t = raise TERM ("get_landau_id", [t])

fun get_landau_symbol_thm t = nth @{thms landau_symbols} (get_landau_id t)

fun get_bigtheta_cong t = nth @{thms landau_bigtheta_meta_congs} (get_landau_id t)

fun dest_landau (t as Const (s, T) $ fltr $ f) =
      if member op= landau_const_names s then
        (Const (s, T), fltr, f) 
      else 
        raise TERM ("dest_landau", [t])
  | dest_landau t = raise TERM ("dest_landau", [t])

fun dest_bigtheta (Const (@{const_name bigtheta}, _) $ fltr $ a) = (fltr, a)
  | dest_bigtheta t = raise TERM ("dest_bigtheta", [t])

fun dest_member (Const (@{const_name Set.member}, _) $ a $ b) = (a, b)
  | dest_member t = raise TERM ("dest_member", [t])

(* Turn a conversion that rewrites a Landau symbol L(f) into a conversion that 
   rewrites f \<in> L(g) *)
fun lift_landau_conv conv ct = 
  case Thm.term_of ct of
    (Const (@{const_name "Set.member"}, _) $ _ $ _) => ct |> (
      Conv.rewrs_conv @{thms landau_flip[THEN eq_reflection]}
      then_conv (Conv.arg_conv conv)
      then_conv Conv.rewrs_conv @{thms landau_flip[THEN eq_reflection]})
  | _ => conv ct

fun lift_landau_simproc simproc ctxt = 
  let
    fun conv ct = 
      case simproc ctxt ct of
        NONE => raise CTERM ("lift_landau_simproc", [ct])
      | SOME thm => thm
  in
    try (lift_landau_conv conv)
  end


datatype operator = MULT | DIVIDE
datatype 'a breadcrumb = LEFT of 'a | RIGHT of 'a

fun inverse T = Const (@{const_name Fields.inverse}, T --> T)
fun mult T = Const (@{const_name Groups.times}, T --> T --> T)
fun divide T = Const (@{const_name Rings.divide_class.divide}, T --> T --> T)

fun map_crumb f (LEFT x) = LEFT (f x)
  | map_crumb f (RIGHT x) = RIGHT (f x)

fun reconstruct_crumbs T crumbs =
  let
    fun binop MULT (SOME x) (SOME y) = SOME (mult T $ x $ y)
      | binop DIVIDE (SOME x) (SOME y) = SOME (divide T $ x $ y)
      | binop _ x NONE = x
      | binop MULT NONE y = y
      | binop DIVIDE NONE (SOME y) = SOME (inverse T $ y)
    fun go t [] = t
      | go t (LEFT (opr,r) :: crumbs) = go (binop opr t (SOME r)) crumbs
      | go t (RIGHT (opr,l) :: crumbs) = go (binop opr (SOME l) t) crumbs
  in
    go NONE crumbs
  end

(* Pick a leaf in the arithmetic tree (i.e. a summand), remove it and return both it and the 
   remaining tree (NONE if it is empty). Return a list of all possible results *)
fun pick_leaf t T =
  let 
    fun go ((Const (@{const_name "Groups.times"}, _)) $ a $ b) neg crumbs acc =
            acc |> go b neg (RIGHT (MULT,a) :: crumbs) |> go a neg (LEFT (MULT,b) :: crumbs)
        | go ((Const (@{const_name "Rings.divide_class.divide"}, _)) $ a $ b) neg crumbs acc =
            acc |> go b (not neg) (RIGHT (DIVIDE,a) :: crumbs) |> go a neg (LEFT (DIVIDE,b) :: crumbs)
        | go a neg crumbs acc =
            let
              val a = if neg then inverse T $ a else a
            in
              (a, reconstruct_crumbs T crumbs, rev (map (map_crumb fst) crumbs)) :: acc
            end
  in
    go t false [] []
  end

local
  fun commute_conv MULT = Conv.rewr_conv @{thm mult.commute[THEN eq_reflection]}
    | commute_conv DIVIDE = Conv.rewr_conv @{thm divide_inverse'[THEN eq_reflection]}
  fun assoc_conv MULT = Conv.rewr_conv @{thm mult.assoc[THEN eq_reflection]}
    | assoc_conv DIVIDE = Conv.rewr_conv @{thm times_divide_eq_right[symmetric, THEN eq_reflection]}
  fun to_mult_conv MULT = Conv.all_conv
    | to_mult_conv DIVIDE = Conv.rewr_conv @{thm divide_inverse[THEN eq_reflection]}
  fun extract_middle_conv MULT = Conv.rewr_conv @{thm mult.left_commute[THEN eq_reflection]}
    | extract_middle_conv DIVIDE = Conv.rewr_conv @{thm extract_divide_middle[THEN eq_reflection]}
  fun repeat_conv 0 _ = Conv.all_conv
    | repeat_conv n conv = conv then_conv repeat_conv (n - 1) conv
  val eliminate_double_inverse_conv = Conv.rewr_conv @{thm inverse_inverse_eq[THEN eq_reflection]}
in
fun extract_leaf_conv path =
  let
    fun count_inversions [] acc = acc div 2
      | count_inversions (RIGHT DIVIDE :: xs) acc = count_inversions xs (acc+1)
      | count_inversions (_ :: xs) acc = count_inversions xs acc

    val l_conv = Conv.fun_conv o Conv.arg_conv
    val r_conv = Conv.arg_conv
    fun go [] = Conv.all_conv
      | go [LEFT oper] = to_mult_conv oper
      | go [RIGHT oper] = commute_conv oper
      | go (LEFT oper :: path) = l_conv (go path) then_conv assoc_conv oper
      | go (RIGHT oper :: path) = r_conv (go path) then_conv extract_middle_conv oper
  in
    go path then_conv 
      repeat_conv (count_inversions path 0) (l_conv eliminate_double_inverse_conv)
  end
end

fun filterT T = Type (@{type_name Filter.filter}, [T])

fun cancel_factor_conv' ctxt ct = 
  let
    val t = Thm.term_of ct
    val (f, (L, fltr, g)) = dest_member t ||> dest_landau
    val landau_symbol_thm = get_landau_symbol_thm L

    fun dest_abs t =
      case t of
        Abs a => a
      | _ => raise CTERM ("cancel_factor_simproc", [ct])
    val ((x_name1, S, f_body), (x_name2, _, g_body)) = (dest_abs f, dest_abs g)
    val T = Term.fastype_of f |> Term.dest_funT |> snd
    fun abs x body = Abs (x, S, body)

    fun mk_eventually_nonzero t =
      Const (@{const_name eventually_nonzero}, filterT S --> (S --> T) --> HOLogic.boolT) $ 
        fltr $  t

    val (f_leaves, g_leaves) = (pick_leaf f_body T, pick_leaf g_body T)
    fun cancel' (t, rest1, path1) (_, rest2, path2) = 
      let
        val prop = HOLogic.mk_Trueprop (mk_eventually_nonzero (abs x_name1 t))
        fun tac {context = ctxt, ...} = 
          let
            val simps = Named_Theorems.get ctxt @{named_theorems eventually_nonzero_simps}
          in
            ALLGOALS (Simplifier.asm_full_simp_tac (ctxt addsimps simps))
          end
        fun do_cancel thm =
          let
            val thms = map (fn thm' => thm' OF [landau_symbol_thm, thm] RS @{thm eq_reflection})
                         @{thms landau_mult_cancel_simps}
          in
            ct |> (
              Conv.fun_conv (Conv.arg_conv (Conv.abs_conv (K (extract_leaf_conv path1)) ctxt))
              then_conv (Conv.arg_conv (Conv.arg_conv (Conv.abs_conv (K (extract_leaf_conv path2)) ctxt)))
              then_conv (Conv.rewrs_conv thms)
            )
          end
      in
        Option.map do_cancel (try (fn () => Goal.prove ctxt [] [] prop tac) ())
      end
    fun not_one (Const (@{const_name Groups.one}, _)) = false
      | not_one _ = true
    fun cancel (leaf1 as (t1, _, _)) (leaf2 as (t2, _, _)) = 
      if t1 = t2 andalso not_one t1 then cancel' leaf1 leaf2 else NONE
  in
    case (get_first (fn leaf1 => get_first (cancel leaf1) g_leaves) f_leaves) of
      NONE => raise CTERM ("cancel_factor_conv", [ct])
    | SOME thm => thm
  end

fun cancel_factor_conv ctxt = 
  Conv.fun_conv (Conv.arg_conv Thm.eta_long_conversion)
  then_conv Conv.arg_conv (Conv.arg_conv Thm.eta_long_conversion)
  then_conv cancel_factor_conv' ctxt

val cancel_factor_simproc = try o cancel_factor_conv

val plus_absorb_thms1 = @{thms landau_symbols[THEN landau_symbol.plus_absorb1]}
val plus_absorb_thms2 = @{thms landau_symbols[THEN landau_symbol.plus_absorb2]}
val minus_absorb_thms1 = @{thms landau_symbols[THEN landau_symbol.diff_absorb1]}
val minus_absorb_thms2 = @{thms landau_symbols[THEN landau_symbol.diff_absorb2]}

val sum_term_size =
  let
    fun go acc (Const (@{const_name "Groups.plus"}, _) $ l $ r) = go (go acc l) r
      | go acc (Const (@{const_name "Groups.minus"}, _) $ l $ r) = go (go acc l) r
      | go acc _ = acc + 1
  in
    go 0
  end

local
  fun mk_smallo fltr S T = 
    Const (@{const_name smallo}, filterT S --> (S --> T) --> HOLogic.mk_setT (S --> T)) $ fltr
  fun mk_member T = Const (@{const_name Set.member}, T --> HOLogic.mk_setT T --> HOLogic.boolT)
  fun mk_in_smallo fltr S T f g = mk_member (S --> T) $ f $ (mk_smallo fltr S T $ g)
in
  fun simplify_landau_sum_simproc ctxt ct =
    let
      val t = Thm.term_of ct
      val (L, fltr, f) = dest_landau t
      val L_name = dest_Const L |> fst
      val (x_name, S, f_body) = 
        case f of
          Abs a => a
        | _ => raise CTERM ("simplify_landau_sum_conv", [ct])
      val limit = Config.get ctxt landau_sum_limit
      val _ = 
        if limit < 0 orelse sum_term_size f_body <= limit then ()
        else raise CTERM ("simplify_landau_sum_conv", [ct])

      val T = Term.fastype_of f |> Term.dest_funT |> snd
      fun abs t = Abs (x_name, S, t)

      val (minus, l, r) =
        case f_body of
          Const (@{const_name "Groups.plus"}, _) $ l $ r => (false, abs l, abs r)
        | Const (@{const_name "Groups.minus"}, _) $ l $ r => (true, abs l, abs r)
        | _ => raise CTERM ("simplify_landau_sum_simproc", [ct])

      fun mk_absorb_thm absorb_thms thm =
        let 
          fun go (s :: ss) (thm :: thms) = if s = L_name then thm else go ss thms
            | go _ _ = raise CTERM ("simplify_landau_sum_conv", [ct])
        in
          (thm RS go landau_const_names absorb_thms) RS @{thm eq_reflection}
        end

      val absorb_thms1 = if minus then minus_absorb_thms1 else plus_absorb_thms1
      val absorb_thms2 = if minus then minus_absorb_thms2 else plus_absorb_thms2
      
      fun eliminate (absorb_thms, l, r) = 
        let
          fun tac {context = ctxt, ...} =
                Simplifier.asm_full_simp_tac ctxt 1
                THEN TRY (resolve_tac ctxt @{thms TrueI} 1)
          val prop = HOLogic.mk_Trueprop (mk_in_smallo fltr S T l r)
        in
          case try (fn () => Goal.prove ctxt [] [] prop tac) () of
            NONE => NONE
          | SOME thm => SOME (mk_absorb_thm absorb_thms thm)
              
        end
    in
      get_first eliminate [(absorb_thms1, l, r), (absorb_thms2, r, l)]
    end
      handle TERM _ => NONE | CTERM _ => NONE
end

fun simplify_landau_sum_conv ctxt ct =
  case simplify_landau_sum_simproc ctxt ct of
    SOME thm => thm
  | NONE => raise CTERM ("simplify_landau_sum_conv", [ct])


fun changed_conv conv ct = 
  let
    val thm = conv ct
    fun is_reflexive (ct1, ct2) = Envir.beta_eta_contract ct1 aconv Envir.beta_eta_contract ct2
  in
    if is_reflexive (Logic.dest_equals (Thm.prop_of thm)) then
      raise CTERM ("changed_conv", [ct])
    else
      thm
    handle TERM _ => thm
  end

fun landau_conv conv ctxt = changed_conv (fn ct =>
  let 
    val t = Thm.term_of ct
    val (L as (Const (_, T)), fltr, f) = dest_landau t
    val cong = get_bigtheta_cong L
    val ct' = Const (@{const_name bigtheta}, T) $ fltr $ f |> Thm.cterm_of ctxt
  in
    conv ct' RS cong
  end)
  

fun simplify_landau_product_conv ctxt ct =
  let
    val ctxt1 = put_simpset HOL_basic_ss ctxt addsimps @{thms bigtheta_factors_eq}
    val ctxt2 = ctxt addsimps @{thms landau_simps} delsimprocs (landau_simprocs ctxt)
    val ctxt3 = put_simpset HOL_basic_ss ctxt addsimps @{thms bigtheta_factors_eq[symmetric]}
    val conv = 
      Simplifier.rewrite ctxt1 
      then_conv Simplifier.asm_full_rewrite ctxt2
      then_conv Simplifier.rewrite ctxt3
  in
    landau_conv (changed_conv conv) ctxt ct
  end

val simplify_landau_product_simproc = try o simplify_landau_product_conv



fun reify_prod_bigtheta_conv ctxt =
  let
    val ss = simpset_of (ctxt addsimps @{thms eventually_nonzero_simps eventually_nonneg_primfun})
    val set_subgoaler = Simplifier.set_subgoaler (asm_full_simp_tac o put_simpset ss)
    fun put_ss thms ctxt = put_simpset HOL_basic_ss ctxt addsimps thms
    val ctxt_transforms = 
      [
        set_subgoaler o put_ss 
          @{thms set_divide_inverse eventually_nonzero_simps 
            bigtheta_mult_eq_set_mult bigtheta_inverse_eq_set_inverse bigtheta_divide_eq_set_divide 
            bigtheta_pow_eq_set_pow landau_product_preprocess 
            mult_1_left mult_1_right inverse_1 set_powr_mult power_one},
        put_ss @{thms BIGTHETA_CONST'_tag mult_1_left mult_1_right inverse_1 power_one},
        put_ss @{thms BIGTHETA_FUN_tag mult_1_left mult_1_right inverse_1 power_one},
        put_ss @{thms BIGTHETA_CONST_fold mult_1_left mult_1_right inverse_1 power_one},
        put_ss @{thms bigtheta_factors_eq[symmetric] eval_inverse_primfun[symmetric]
          eval_powr_primfun[symmetric] inverse_primfun.simps powr_primfun.simps},
        put_ss @{thms LANDAU_PROD'_fold append.simps mult_1_left mult_1_right minus_minus power_one}
      ]
    val convs = map (fn f => Simplifier.rewrite (f ctxt)) ctxt_transforms
  in 
    Conv.try_conv (Conv.arg_conv Thm.eta_long_conversion)
    then_conv Conv.rewr_conv @{thm BIGTHETA_CONST_tag[THEN eq_reflection]}
    then_conv Conv.every_conv convs
  end

fun reify_landau_prod_prop_conv ctxt ct = 
  let
    val t = Thm.term_of ct
    val (f, t) = dest_member t
    val (L as (Const (_, T)), fltr, g) = dest_landau t
    val cong = nth @{thms landau_symbols[THEN landau_prod_meta_cong]} (get_landau_id L)
    fun mk_thm f = Const (@{const_name bigtheta}, T) $ fltr $ f |>
      Thm.cterm_of ctxt |> reify_prod_bigtheta_conv ctxt
    val (thm1, thm2) = (mk_thm f, mk_thm g)
    val thm = cong OF [thm1, thm2]
  in
    thm
  end

fun simplify_landau_real_prod_prop_conv ctxt = 
  let
    val ctxt' = put_simpset HOL_ss ctxt addsimps 
      @{thms list.map inverse_primfun.simps minus_minus append.simps}
  in
    Conv.try_conv (Conv.rewrs_conv (@{thms bigomega_iff_bigo[THEN eq_reflection] 
      smallomega_iff_smallo[THEN eq_reflection]}))
    then_conv reify_landau_prod_prop_conv ctxt
    then_conv Simplifier.rewrite ctxt'
    then_conv Conv.rewrs_conv @{thms LANDAU_PROD_iff[THEN eq_reflection]} 
  end

val simplify_landau_real_prod_prop_simproc = try o simplify_landau_real_prod_prop_conv


end
