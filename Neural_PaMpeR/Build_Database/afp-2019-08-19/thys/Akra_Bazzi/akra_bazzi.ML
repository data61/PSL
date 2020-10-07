(*  Title:      akra_bazzi.ML
    Author:     Manuel Eberl, TU Muenchen
*)

signature AKRA_BAZZI =
sig
  val master_theorem_tac : string option -> bool -> thm option -> term option -> term option -> 
    term option -> Proof.context -> int -> tactic

  val master_theorem_function_tac : bool -> Proof.context -> int -> tactic
  val akra_bazzi_term_tac : Proof.context -> int -> tactic
  val akra_bazzi_sum_tac : Proof.context -> int -> tactic

  val akra_bazzi_relation_tac : Proof.context -> int -> tactic
  val akra_bazzi_measure_tac : Proof.context -> int -> tactic
  val akra_bazzi_termination_tac : Proof.context -> int -> tactic

  val setup_master_theorem : Context.generic * Token.T list -> 
    (Proof.context -> Method.method) * (Context.generic * Token.T list)
end

structure Akra_Bazzi: AKRA_BAZZI =
struct

fun changed_conv conv ct = 
  let 
    val thm = conv ct
  in
    if Thm.is_reflexive thm then raise CTERM ("changed_conv", [ct]) else thm
  end

fun rewrite_tac ctxt thms =
  CONVERSION (Conv.repeat_conv (changed_conv (Conv.bottom_conv 
    (K (Conv.try_conv (Conv.rewrs_conv (map (fn thm => thm RS @{thm eq_reflection}) thms)))) ctxt)))

val term_preps = @{thms akra_bazzi_termination_simps}
fun get_term_intros ctxt = Named_Theorems.get ctxt @{named_theorems "akra_bazzi_term_intros"}

val master_intros = 
  @{thms master_theorem_function.master1_automation 
      master_theorem_function.master1_bigo_automation master_theorem_function.master1_automation'
      master_theorem_function.master1_bigo_automation' master_theorem_function.master2_1_automation 
      master_theorem_function.master2_1_automation' master_theorem_function.master2_2_automation
      master_theorem_function.master2_2_automation' master_theorem_function.master2_3_automation
      master_theorem_function.master2_3_automation' master_theorem_function.master3_automation 
      master_theorem_function.master3_automation'}

fun get_intros NONE b = if not b then master_intros else 
  @{thms master_theorem_function.master1_automation master_theorem_function.master1_bigo_automation
         master_theorem_function.master1_automation' master_theorem_function.master2_1_automation 
      master_theorem_function.master2_1_automation'}
|   get_intros (SOME "1") _ = @{thms master_theorem_function.master1_automation 
      master_theorem_function.master1_bigo_automation master_theorem_function.master1_automation'
      master_theorem_function.master1_bigo_automation'}
|   get_intros (SOME "2.1") _ = @{thms master_theorem_function.master2_1_automation 
      master_theorem_function.master2_1_automation'}
|   get_intros (SOME "2.2") _ = @{thms master_theorem_function.master2_2_automation
      master_theorem_function.master2_2_automation'}
|   get_intros (SOME "2.3") _ = @{thms master_theorem_function.master2_3_automation
      master_theorem_function.master2_3_automation'}
|   get_intros (SOME "3") _ = @{thms master_theorem_function.master3_automation 
      master_theorem_function.master3_automation'}
|   get_intros _ _ = error "invalid Master theorem case"

val allowed_consts =
  [@{term "(+) :: nat => nat => nat"}, @{term "Suc :: nat => nat"},
   @{term "(+) :: real => real => real"}, @{term "(-) :: real => real => real"},
   @{term "uminus :: real => real"}, @{term "(*) :: real => real => real"}, 
   @{term "(/) :: real => real => real"}, @{term "inverse :: real => real"},
   @{term "(powr) :: real => real => real"}, @{term "real_of_nat"}, @{term "real :: nat => real"},
   @{term "Num.numeral :: num => real"}, @{term "Num.Bit0"}, @{term "Num.Bit1"},
   @{term "0 :: real"}, @{term "1 :: real"}, @{term "Num.One"}, @{term "Num.BitM"},
   @{term "Num.numeral :: num => nat"}, @{term "0 :: nat"}, @{term "1 :: nat"},
   @{term "atLeastAtMost :: real => real => real set"}, 
   @{term "greaterThanAtMost :: real => real => real set"},
   @{term "atLeastLessThan :: real => real => real set"},
   @{term "greaterThanLessThan :: real => real => real set"},
   @{term "(=) :: real => real => bool"}, @{term "(\<le>) :: real => real => bool"},
   @{term "(<) :: real => real => bool"}, @{term "(\<in>) :: real => real set => bool"},
   @{term "(=) :: nat => nat => bool"}, @{term "(\<le>) :: nat => nat => bool"},
   @{term "(<) :: nat => nat => bool"}, @{term "Trueprop"},
   @{term "HOL.Not"}, @{term "HOL.conj"}, @{term "HOL.disj"}, @{term "HOL.implies"}]

fun contains_only_numerals t =
  let 
    fun go (s $ t) = let val _ = go s in go t end
      | go (Const c) = if member (op =) allowed_consts (Const c) then
            ()
          else
            raise TERM ("contains_only_numerals", [Const c])
      | go t = raise TERM ("contains_only_numerals", [t])
    val _ = go t
  in
    true
  end
    handle TERM _ => false

fun dest_nat_number t =
  case HOLogic.dest_number t of
    (ty, n) => if ty = @{typ "Nat.nat"} then n  else raise TERM ("dest_nat_number", [t])

fun num_to_Suc n =
let 
  fun go acc 0 = acc
    | go acc n = go (@{term "Suc :: Nat.nat => Nat.nat"} $ acc) (n - 1)
in  
  go @{term "0 :: Nat.nat"} n
end



(* Termination *)

datatype breadcrumb = Fst | Snd

(* extract all natural number types from a product type *)
fun pick_natT_leaf T =
  let
    fun go crumbs T acc =
      case try HOLogic.dest_prodT T of 
        SOME (T1, T2) => acc |> go (Snd :: crumbs) T2 |> go (Fst :: crumbs) T1
      | NONE => if T = HOLogic.natT then crumbs :: acc else acc
  in
    go [] T []
  end

fun breadcrumb Fst = fst
  | breadcrumb Snd = snd

(* construct an extractor function using fst/snd from a path in a product type *)
fun mk_extractor T crumbs =
  let
    fun aux c f (T', acc) =
      let
        val T'' = HOLogic.dest_prodT T' |> f
      in
         (T'', Const (c, T' --> T'') $ acc)
      end
    fun go [] (_, acc) = Abs ("n", T, acc)
      | go (Fst :: crumbs) acc = acc |> aux @{const_name fst} fst |> go crumbs
      | go (Snd :: crumbs) acc = acc |> aux @{const_name snd} snd |> go crumbs
  in
    go (rev crumbs) (T, Bound 0)
  end

fun extract_from_prod [] t = t
  | extract_from_prod (c :: cs) t = extract_from_prod cs t |> HOLogic.dest_prod |> breadcrumb c

fun ANY' tacs n = fold (curry op APPEND) (map (fn t => t n) tacs) no_tac

(* find recursion variable, set up a measure function for it and apply it to prove termination *)
fun akra_bazzi_relation_tac ctxt =
  case Proof_Context.lookup_fact ctxt "local.termination" of
    SOME {thms = [thm], ...} =>
      let
        val prems = Thm.prems_of thm
        val relT = prems |> hd |> dest_comb |> snd |> dest_comb |> snd |> dest_Var |> snd 
        val T = relT |> HOLogic.dest_setT |> HOLogic.dest_prodT |> fst
        val prems = prems |> tl |> map Term.strip_all_body
        val calls = prems |> map (Logic.strip_imp_concl #> HOLogic.dest_Trueprop #> 
                      dest_comb #> fst #> dest_comb #> snd #> HOLogic.dest_prod #> fst)
        val leaves = pick_natT_leaf T
        val calls = map (fn path => (path, map (extract_from_prod path) calls)) leaves
        val calls = calls |> filter (snd #> filter is_Bound #> null) |> map fst
        val measureC = Const (@{const_name Wellfounded.measure}, (T --> HOLogic.natT) --> relT)
        fun mk_relation f = measureC $ f
        val relations = map (mk_relation o mk_extractor T) calls
      in
        (ANY' (map (Function_Relation.relation_tac ctxt o K) relations)
         THEN' resolve_tac ctxt @{thms wf_measure})
        THEN_ALL_NEW (rewrite_tac ctxt @{thms measure_prod_conv measure_prod_conv'})
      end
  | _ => K no_tac

val measure_postproc_simps = 
  @{thms arith_simps of_nat_0 of_nat_1 of_nat_numeral
         Suc_numeral of_nat_Suc}

(* prove that the measure decreases in a recursive call by showing that the recursive call is
   an Akra-Bazzi term. Apply simple post-processing to make the numbers less ugly *)
fun akra_bazzi_measure_tac ctxt = 
  rewrite_tac ctxt term_preps
  THEN' eresolve_tac ctxt @{thms akra_bazzi_term_measure}
  THEN' resolve_tac ctxt (get_term_intros ctxt)
  THEN_ALL_NEW rewrite_tac ctxt measure_postproc_simps
  
(* prove termination of an Akra-Bazzi function *)
fun akra_bazzi_termination_tac ctxt = 
  akra_bazzi_relation_tac ctxt
  THEN_ALL_NEW akra_bazzi_measure_tac ctxt



(* General preprocessing *)
    
fun nat_numeral_conv ctxt ct =
let 
  val t = Thm.term_of ct
  val prop = Logic.mk_equals (t, num_to_Suc (dest_nat_number t))
  fun tac {context = ctxt, prems = _ } = 
    SOLVE (Local_Defs.unfold_tac ctxt @{thms eval_nat_numeral BitM.simps One_nat_def} 
    THEN resolve_tac ctxt @{thms Pure.reflexive} 1);
in  
  case try (fn () => Goal.prove ctxt [] [] prop tac) () of
    NONE => raise CTERM ("nat_numeral_conv", [ct])
  | SOME thm => thm
end

fun akra_bazzi_sum_conv ctxt ct =
  case Thm.term_of ct of 
    (Const (@{const_name sum}, _) $ _ $ 
      (Const (@{const_name Set_Interval.ord_class.lessThan}, _) $ _)) => 
        Conv.arg_conv (Conv.arg_conv (nat_numeral_conv ctxt)) ct
    | _ => raise CTERM ("akra_bazzi_sum_conv", [ct])

fun akra_bazzi_sum_tac ctxt i =
let 
  fun conv ctxt = Conv.try_conv (akra_bazzi_sum_conv ctxt)
  val thms = @{thms eval_akra_bazzi_sum eval_akra_bazzi_sum' 
                    mult_1_left mult_1_right add_0_left add_0_right}
in
  CHANGED (CONVERSION (Conv.top_conv conv ctxt) i THEN 
           REPEAT (EqSubst.eqsubst_tac ctxt [0] thms i))
end

fun akra_bazzi_term_tac ctxt = 
  rewrite_tac ctxt term_preps
  THEN' (resolve_tac ctxt (get_term_intros ctxt))

fun akra_bazzi_terms_tac ctxt = 
  REPEAT_ALL_NEW (fn i => DETERM (resolve_tac ctxt @{thms akra_bazzi_termsI'} i))
  THEN_ALL_NEW akra_bazzi_term_tac ctxt


fun analyze_terminal ctxt f x inv t_orig t acc =
let 
  val thy = Proof_Context.theory_of ctxt
  val patvar = ("x",1)
  val pat = Term.betapply (f, Var (patvar, HOLogic.natT))
  fun match t =
    let
      val matcher = Pattern.first_order_match thy (pat, t) (Vartab.empty, Vartab.empty)
      val x' = Vartab.lookup (snd matcher) patvar |> the |> snd
    in
      if Term.exists_subterm (fn x' => x = x') x' then x' else raise Pattern.MATCH
    end
  fun add_term t (acc, acc_inv, call) =
    if inv then (acc, t :: acc_inv, call) else (t :: acc, acc_inv, call)
  fun go t (acc, acc_inv, call) =
    let
      val call' = match t
    in
      case call of
        NONE => (acc, acc_inv, SOME call')
      | SOME _ => raise TERM ("Non-linear occurrence of recursive call", [t_orig])
    end
      handle Pattern.MATCH => add_term t (acc, acc_inv, call)
in
  go t acc
end;

fun mk_prod [] = @{term "1 :: real"}
|   mk_prod (x::xs) = 
      fold (fn x => fn acc => @{term "(*) :: real => real => real"} $ x $ acc) xs x

fun mk_quot (xs, []) = mk_prod xs
  | mk_quot ([], ys) = @{term "inverse :: real => real"} $ mk_prod ys
  | mk_quot (xs, ys) = @{term "(/) :: real => real => real"} $ mk_prod xs $ mk_prod ys

fun analyze_prod ctxt f x minus t (acc1, acc2) =
let 
  fun go inv (oper $ t1 $ t2) acc =
        if oper = @{term "(*) :: real => real => real"} then
          go inv t1 (go inv t2 acc)
        else if oper = @{term "(/) :: real => real => real"} then
          go inv t1 (go (not inv) t2 acc)
        else
          analyze_terminal ctxt f x inv t (oper $ t1 $ t2) acc
  |   go inv (oper $ t') acc =
        if oper = @{term "inverse :: real => real"} then
          go (not inv) t' acc
        else
          analyze_terminal ctxt f x inv t (oper $ t') acc
  |   go inv t' acc = analyze_terminal ctxt f x inv t t' acc
in
  case go false t ([], [], NONE) of
    (_, _, NONE) => (acc1, (if minus then @{term "uminus :: real => real"} $ t else t) :: acc2)
  | (xs, ys, SOME call) => 
      let 
        val r = mk_quot (xs, ys)
        val r' = (if minus then @{term "uminus :: real => real"} $ r else r, call)
      in
        (r' :: acc1, acc2)
      end
end

fun mk_sum [] = @{term "0 :: real"}
  | mk_sum (x::xs) = 
      let 
        fun go (f $ x) acc =
              if f = @{term "uminus :: real => real"} then
                @{term "(-) :: real => real => real"} $ acc $ x
              else
                @{term "(+) :: real => real => real"} $ acc $ (f $ x)
          | go x acc = @{term "(+) :: real => real => real"} $ acc $ x
      in  
        fold go xs x
      end
  

fun analyze_sum ctxt f x t =
  let 
    fun go minus (oper $ t1 $ t2) acc =
          if oper = @{term "(+) :: real => real => real"} then
            go minus t1 (go minus t2 acc)
          else if oper = @{term "(-) :: real => real => real"} then
            go minus t1 (go (not minus) t2 acc)
          else analyze_prod ctxt f x minus (oper $ t1 $ t2) acc
    |   go minus (oper $ t) acc =
          if oper = @{term "uminus :: real => real"} then
            go (not minus) t acc
          else
            analyze_prod ctxt f x minus (oper $ t) acc
    |   go minus t acc = analyze_prod ctxt f x minus t acc
  in
    case go false t ([],[]) of
      (xs,ys) => (xs, mk_sum ys)
  end

fun extract_coeff ctxt t =
  let 
    val thy = Proof_Context.theory_of ctxt
    val t' = Raw_Simplifier.rewrite_term thy 
                 @{thms akra_bazzi_termination_simps[THEN eq_reflection]} [] t
    fun aux thm =
      let 
        val (tmp, pat) = thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> Term.dest_comb
        val var = tmp |> Term.dest_comb |> snd |> Term.dest_Var |> fst
        val (_, insts) = Pattern.first_order_match thy (pat, t') (Vartab.empty, Vartab.empty)
        val coeff = Option.map snd (Vartab.lookup insts var)
      in 
        coeff
      end
        handle Pattern.MATCH => NONE
  in
    case get_first aux (get_term_intros ctxt) of
      NONE => raise TERM ("extract_coeff", [t'])
    | SOME coeff => coeff
  end

fun get_var_name (Free (x, _)) = x
  | get_var_name (Var ((x,_),_)) = x
  | get_var_name t = raise TERM ("get_var_name", [t])

fun analyze_call ctxt f x t =
  let
    val (ts, g) = analyze_sum ctxt f x t
    val k = length ts
    val a_coeffs = HOLogic.mk_list HOLogic.realT (map fst ts)
    fun abstract t = Abs (get_var_name x, HOLogic.natT, abstract_over (x, t))
    val ts = map (abstract o snd) ts
    val b_coeffs = HOLogic.mk_list HOLogic.realT (map (extract_coeff ctxt) ts)
    val ts = HOLogic.mk_list (HOLogic.natT --> HOLogic.natT) ts
  in
    {k = HOLogic.mk_nat k, a_coeffs = a_coeffs, b_coeffs = b_coeffs, ts = ts, g = abstract g}
  end

fun instantiate_akra_bazzi ctxt ts = 
    map (Thm.instantiate' [] (map (Option.map (Thm.cterm_of ctxt)) ts))

fun analyze_equation ctxt f eq funvar = 
  let 
    val rhs = eq |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
    val {k, a_coeffs, b_coeffs, ts, g} = analyze_call ctxt f funvar rhs
  in
    {k = k, a_coeffs = a_coeffs, b_coeffs = b_coeffs, ts = ts, f = f, g = g}
  end

fun akra_bazzi_instantiate_tac ctxt f eq x0 x1 funvar p' =
  let 
    val {k, a_coeffs, b_coeffs, ts, g, ...} = analyze_equation ctxt f eq funvar
    val insts =
      ([SOME x0, SOME x1, SOME k, SOME a_coeffs, SOME b_coeffs, SOME ts, SOME f, SOME g] @
        (filter Option.isSome [p']))
  in
    resolve_tac ctxt o instantiate_akra_bazzi ctxt insts
  end

(*
val code_simp_tac = 
  Code_Simp.static_tac {consts = [@{const_name arith_consts}], ctxt = @{context}, simpset = NONE}


fun eval_real_numeral_conv ctxt ct =
  case Thm.term_of ct of
    @{term "Pure.imp"} $ _ $ _ => Conv.implies_concl_conv (eval_real_numeral_conv ctxt) ct
  | _ =>
      let
        val t = Thm.term_of ct
        val prop = Logic.mk_equals (t, @{term "Trueprop True"})
        val ctxt' = put_simpset (simpset_of @{context}) ctxt
        fun tac ({context = ctxt, ...}) =
          Local_Defs.unfold_tac ctxt @{thms greaterThanLessThan_iff}
          THEN (SOLVE (Simplifier.full_simp_tac ctxt' 1) ORELSE code_simp_tac ctxt 1)
      in
        if contains_only_numerals t then
          case try (fn () => Goal.prove ctxt [] [] prop tac) () of
            SOME thm => thm
          | NONE => raise CTERM ("eval_real_numeral_conv", [ct]) 
        else
          raise CTERM ("eval_real_numeral_conv", [ct])
      end *)


fun eval_numeral_tac ctxt =
  SUBGOAL (fn (goal, i) => 
    if contains_only_numerals (Logic.strip_imp_concl goal) then
      Eval_Numeral.eval_numeral_tac ctxt i
    else
      all_tac)
  
fun unfold_simps ctxt = 
  rewrite_tac ctxt @{thms eval_akra_bazzi_le_list_ex eval_length of_nat_numeral 
           of_nat_0 of_nat_1 numeral_One}


(* Applying the locale intro rule *)

fun master_theorem_function_tac simp ctxt = 
  resolve_tac ctxt @{thms master_theorem_functionI}
  THEN_ALL_NEW ((fn i => TRY (REPEAT_ALL_NEW (match_tac ctxt @{thms ball_set_intros}) i))
    THEN_ALL_NEW ((fn i => TRY (akra_bazzi_terms_tac ctxt i))
      THEN_ALL_NEW (fn i =>
        unfold_simps ctxt i
        THEN TRY (akra_bazzi_sum_tac ctxt i)
        THEN unfold_simps ctxt i
        THEN (if simp then TRY (eval_numeral_tac ctxt i) else all_tac)
      )
    )
  )


(* Pre-processing of Landau bound in goal and post-processing of Landau bounds in premises *)

fun goal_conv conv ct = 
  case Thm.term_of ct of
    (Const (@{const_name "Pure.imp"}, _) $ _ $ _) => Conv.arg_conv (goal_conv conv) ct
  | _ => conv ct

fun rewrs_conv' thms = 
  goal_conv (Conv.arg_conv (Conv.arg_conv (Conv.rewrs_conv thms)))

fun preprocess_tac ctxt =
  CONVERSION (rewrs_conv' @{thms CLAMP})
  THEN' rewrite_tac ctxt @{thms propagate_CLAMP CLAMP_aux}
  THEN' rewrite_tac ctxt @{thms CLAMP_postproc}
  THEN' CONVERSION (rewrs_conv' @{thms UNCLAMP'})

fun rewrs_goal_conv thms = 
  goal_conv (Conv.arg_conv (Conv.arg_conv (Conv.rewrs_conv thms)))

fun rewrs_conv thms ctxt = 
  Conv.repeat_conv (changed_conv (Conv.bottom_conv (K (Conv.try_conv (Conv.rewrs_conv thms))) ctxt))

fun postprocess_tac ctxt = TRY o (
    CONVERSION (rewrs_goal_conv @{thms CLAMP})
    THEN' rewrite_tac ctxt @{thms CLAMP_aux}
    THEN' rewrite_tac ctxt @{thms CLAMP_postproc}
    THEN' CONVERSION (rewrs_conv @{thms MASTER_BOUND_postproc[THEN eq_reflection]} ctxt)
    THEN' CONVERSION (rewrs_conv @{thms MASTER_BOUND_UNCLAMP[THEN eq_reflection]} ctxt)
    THEN' CONVERSION (rewrs_goal_conv @{thms UNCLAMP}))


(* The main tactic *)

fun intros_tac ctxt thms = DETERM o TRY o REPEAT_ALL_NEW (DETERM o match_tac ctxt thms)

fun master_theorem_tac' caseno simp f eq funvar x0 x1 p' ctxt =
    (
      preprocess_tac ctxt
      THEN' akra_bazzi_instantiate_tac ctxt f eq x0 x1 funvar p' (get_intros caseno (p' <> NONE))
      THEN' DETERM o master_theorem_function_tac simp ctxt)
    THEN_ALL_NEW intros_tac ctxt @{thms ball_set_intros akra_bazzi_p_rel_intros}
  THEN_ALL_NEW (DETERM o (
        unfold_simps ctxt
        THEN' TRY o akra_bazzi_sum_tac ctxt
        THEN' unfold_simps ctxt
        THEN' postprocess_tac ctxt
        THEN' (if simp then TRY o eval_numeral_tac ctxt else K all_tac)
        THEN' intros_tac ctxt @{thms allI ballI conjI impI}
        THEN_ALL_NEW (TRY o eresolve_tac ctxt @{thms atLeastLessThanE})))

fun find_function goal = 
  case goal |> Logic.strip_imp_concl |> HOLogic.dest_Trueprop of
      @{term "Set.member :: (nat => real) => _ set => bool"} $ f $ _ => f
    | _ => raise TERM ("find_function", [goal])

val leq_nat = @{term "(<=) :: nat => nat => bool"}
val less_nat = @{term "(<) :: nat => nat => bool"}

fun find_x1 var eq =
  let
    fun get_x1 prem =
      case prem |> HOLogic.dest_Trueprop of
        rel $ x1 $ x =>
          if x = var andalso rel = leq_nat then
            SOME x1
          else if x = var andalso rel = less_nat then
            SOME (@{term "Suc"} $ x1)
          else
            NONE
      | _ => NONE
  in
    get_first get_x1 (Thm.prems_of eq) 
  end
  handle TERM _ => NONE

fun analyze_funeq pat var ctxt eq = 
  let
    val lhs = eq |> Thm.concl_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
    val matcher = Thm.first_order_match (Thm.cterm_of ctxt lhs, pat)
    val eq = Thm.instantiate matcher eq
  in
    case find_x1 var eq of
      NONE => NONE
    | SOME _ => SOME eq
  end
    handle Pattern.MATCH => NONE

fun find_funeq ctxt f = 
  let
    val n = ("n", 0)
    val n' = Var (n, HOLogic.natT)
    val pat = Thm.cterm_of ctxt (Term.betapply (f, n'))
    fun get_function_info (Abs (_, _, body)) = get_function_info body
      | get_function_info (t as f $ _) =
          (Function.get_info ctxt t handle Empty => get_function_info f)
      | get_function_info t = Function.get_info ctxt t
    val {simps = simps, ...} = get_function_info f
      handle List.Empty => raise TERM ("Could not obtain function info record.", [f])
    val simps = 
      case simps of
        SOME simps => simps
      | NONE => raise TERM ("Function has no simp rules.", [f])
  in
    case get_first (analyze_funeq pat n' ctxt) simps of
      SOME s => (s, n')
    | NONE => raise TERM ("Could not determine recurrence from simp rules.", [f])
end

fun master_theorem_tac caseno simp eq x0 x1 p' ctxt =
  SUBGOAL (fn (goal, i) => Subgoal.FOCUS (fn {context = ctxt, ...} =>
    let
      val f = find_function goal
      val (eq, funvar) =
        case eq of
          SOME eq => (
            let
              val n = Var (("n", 0), HOLogic.natT)
            in
              case (analyze_funeq (Thm.cterm_of ctxt (f $ n)) n ctxt eq) of
                SOME eq => (eq, n)
              | NONE => raise TERM ("", [])
            end
              handle TERM _ => raise TERM (
                "Could not determine recursion variable from recurrence theorem.",
                [Thm.prop_of eq]))
        | NONE => find_funeq ctxt f
      val x0 = Option.getOpt (x0, @{term "0::nat"})
      val x1 = if Option.isSome x1 then x1 else find_x1 funvar eq
      val x1 =
        case x1 of
          SOME x1 => x1
        | NONE => raise TERM ("Could not determine x1 from recurrence theorem", 
                              [goal, Thm.prop_of eq, funvar])
      val p' = if caseno = NONE orelse caseno = SOME "1" orelse caseno = SOME "2.1" then p' else NONE
    in
      HEADGOAL (master_theorem_tac' caseno simp f eq funvar x0 x1 p' ctxt)
    end
  ) ctxt i) 
    handle TERM _ => K no_tac


fun read_term_with_type ctxt T = Syntax.check_term ctxt o Type.constraint T o Syntax.parse_term ctxt

fun parse_assoc key scan = Scan.lift (Args.$$$ key -- Args.colon) -- scan >> snd

val parse_param = 
  let 
    fun term_with_type T = 
      Scan.peek (fn context => Args.embedded_inner_syntax >> 
        read_term_with_type (Context.proof_of context) T);
  in 
    parse_assoc "recursion" Attrib.thm >> (fn x => (SOME x, NONE, NONE, NONE)) ||
    parse_assoc "x0" (term_with_type HOLogic.natT) >> (fn x => (NONE, SOME x, NONE, NONE)) ||
    parse_assoc "x1" (term_with_type HOLogic.natT) >> (fn x => (NONE, NONE, SOME x, NONE)) ||
    parse_assoc "p'" (term_with_type HOLogic.realT) >> (fn x => (NONE, NONE, NONE, SOME x))
  end

val parse_params =
  let 
    fun add_option NONE y = y
      | add_option x _ = x
    fun go (a,b,c,d) (a',b',c',d') = 
      (add_option a a', add_option b b', add_option c c', add_option d d')
  in
    Scan.repeat parse_param >> (fn xs => fold go xs (NONE, NONE, NONE, NONE))
  end

val setup_master_theorem = 
  Scan.option (Scan.lift (Parse.number || Parse.float_number))
  -- Scan.lift (Args.parens (Args.$$$ "nosimp") >> K false || Scan.succeed true)
  -- parse_params
  >>
    (fn ((caseno, simp), (thm, x0, x1, p')) => fn ctxt => 
      let 
        val _ =
          case caseno of
            SOME caseno =>
              if member (op =) ["1","2.1","2.2","2.3","3"] caseno then
                ()
              else
                cat_error "illegal Master theorem case: " caseno
          | NONE => () 
      in
        SIMPLE_METHOD' (master_theorem_tac caseno simp thm x0 x1 p' ctxt)
      end)
   
end;
