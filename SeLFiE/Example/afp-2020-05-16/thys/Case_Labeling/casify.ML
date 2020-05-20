signature CASIFY =
sig
  datatype options = Options of { simp_all_cases: bool, split_right_only: bool,
    protect_subgoals: bool }

  val hyp_subst_tac: Proof.context -> int -> tactic
  val SPLIT_subst_tac: Proof.context -> int -> tactic
  val extract_cases_tac: context_tactic
  val prepare_labels_tac: Proof.context -> int -> tactic
  val split_bind_all_tac: {right_only: bool, simp_all_cases: bool} -> Proof.context -> int -> tactic
  val casify_tac: options -> context_tactic
  val casify_options: options -> options parser
  val casify_method_setup: options -> (Proof.context -> Method.method) context_parser
end

structure Casify : CASIFY =
struct

val bind_unnamedN = "case"
val case_premsN = "prems"
val case_unnamedN = "unnamed"

datatype 'a prg_ctxt = Block of (string * 'a list)
datatype 'a prg_concl = Prg_Concl of ((string * 'a) option * term)

fun dest_var (Const (@{const_name Case_Labeling.VAR}, _) $ t) = Util.dest_tuple t
  | dest_var t = raise TERM ("dest_var", [t])

val dest_vars = HOLogic.dest_list #> maps dest_var

val dest_ct =
  let
    fun mk_block na ic vs =
      let val (_, idx) = HOLogic.dest_number ic
      in (idx, Block (HOLogic.dest_string na, dest_vars vs)) end

    fun dest_block (Const (@{const_name Pair}, _) $ na $ (Const (@{const_name Pair}, _) $ ic $ vs)) =
          mk_block na ic vs
      | dest_block t = raise TERM ("dest_block", [t])
  in HOLogic.dest_list #> rev #> map dest_block end

fun dest_VC (Const (@{const_name Case_Labeling.VC}, _) $ ct $ t) = (dest_ct ct, t)
  | dest_VC t = ([], t)

fun try_dest_Trueprop t = case try HOLogic.dest_Trueprop t of
    NONE => t
  | SOME t' => t'

fun dest_BIND (Const (@{const_name Case_Labeling.BIND}, _) $ na $ ic $ t) =
    let
      val s = HOLogic.dest_string na
      val (_, n) = HOLogic.dest_number ic
    in (SOME (s,n), t) end
  | dest_BIND t = (NONE, t)

fun dest_SPLIT (Const (@{const_name Case_Labeling.SPLIT}, _) $ t $ u) = (t,u)
  | dest_SPLIT t = raise TERM ("dest_SPLIT", [t])

fun dest_Bound (Bound i) = [i]
  | dest_Bound t = raise TERM ("dest_bound", [t])

fun dest_HIER (Const (@{const_name Case_Labeling.HIER},_) $ ct $ t) =
      (SOME (length (HOLogic.dest_list ct)), t)
  | dest_HIER t = (NONE, t)

fun parse_label prop =
  let
    val vars = Term.strip_all_vars prop
    val ((prems, label), _) = prop
      |> (Logic.strip_horn o Term.strip_all_body)
      ||> try_dest_Trueprop
      ||>> dest_VC
  in { vars=vars, label=label, prems=prems} end

fun parse_prem prop =
  let
    val vars = Term.strip_all_vars prop
    val (prems, (hier, concl)) = prop
      |> (Logic.strip_horn o Term.strip_all_body)
      ||> try_dest_Trueprop
      ||> dest_HIER
    val prop' = Logic.list_all (vars, Logic.list_implies (prems, HOLogic.mk_Trueprop concl))
  in (hier, prop') end

fun strip_prg_ctxt n ((params, t), _) =
  let
    fun lookup_delete eq y =
      let
        fun aux _ [] = error ("Term is not a parameter: " ^ @{make_string} y)
          | aux acc ((k,v) :: xs) =
              if eq (k, y) then (v, rev acc @ xs)
              else aux ((k,v) :: acc) xs
      in aux [] end

    fun upd_label_vars ps [] = [(~n, Block (case_unnamedN, map snd ps))]
      | upd_label_vars ps [(n, Block (s,vs))] =
          let
            val (vs', ps') = fold_map (lookup_delete (op aconv)) vs ps
          in [(n, Block (s, vs' @ map snd ps'))] end
      | upd_label_vars ps ((n, Block (s,vs)) :: ct) =
          let val (vs', ps') = fold_map (lookup_delete (op aconv)) vs ps
          in (n, Block (s,vs')) :: upd_label_vars ps' ct end

    val build_param_map = map (fn (s,(s', T)) => (Free (s',T), {fix= (s,T), abs=(s',T)}))

    val (asms, (label, concl)) = t
      |> Logic.strip_horn
      ||> try_dest_Trueprop
      ||> dest_VC

    val prg_ctxt = upd_label_vars (build_param_map params) label

    val ctxt_len = length prg_ctxt
    val asms' = map (parse_prem #> apfst (the_default ctxt_len)) asms
  in
    (prg_ctxt, (asms', concl))
  end

fun strip_prg_ctxts xs =
  let val n = length xs in map_index (fn (i,x) => strip_prg_ctxt (n - i) x) xs end

datatype ('a,'b) precase = Precase of
 {fixes: (binding * typ) list,
  assumes: ('b * term list) list,
  binds: (indexname * term option) list,
  cases: ('a * ('a,'b) precase) list}

fun bindings args = map (apfst Binding.name) args

fun coalesce_order ord = sort (Util.fst_ord ord) #> AList.coalesce (is_equal o ord)

fun unique_names xs = fst (fold_map (Util.infst Name.variant) xs Name.context)

fun build_precase (prg_ctxt, (prems, t))=
  let
    val sorted_prems = prems
      |> map (apsnd (fn t => (fst (dest_BIND (try_dest_Trueprop t)), t)))
      |> sort (prod_ord int_ord (prod_ord (option_ord (prod_ord fast_string_ord int_ord)) (K EQUAL)))

    fun drop_labels (Const (@{const_name "Case_Labeling.BIND"}, _) $ _ $ _ $ t ) = drop_labels t
      | drop_labels (t1 $ t2) = drop_labels t1 $ drop_labels t2
      | drop_labels (Abs (x,T,t)) = Abs (x,T, drop_labels t)
      | drop_labels t = t

    (* XXX integrate with drop_labels, to save a second pass *)
    fun find_binds (t as Const (@{const_name "Case_Labeling.BIND"}, _) $ _ $ _ $ _) =
        ( case dest_BIND t of
          (NONE, t) => find_binds t
        | (SOME (s,n), t) => (n,(s,t)) :: find_binds t)
      | find_binds (t1 $ t2) = find_binds t1 @ find_binds t2
      | find_binds (Abs (_,_,t)) = find_binds t
      | find_binds _ = []

    fun has_loose_bounds t = case loose_bnos t of
        [] => false
      | _ :: _ => (warning "loose bounds in term"; true) (*XXX*)

    fun unique_binds _ [] = []
      | unique_binds acc ((s,x) :: xs) =
          (case AList.lookup (op=) acc s of
            NONE => ((s,0), x) :: unique_binds ((s,0) :: acc) xs
          | SOME n => ((s,n+1), x) :: unique_binds (AList.update (op=) (s,n+1) acc) xs
          )

    fun mk_precase _ _ [] [] = []
      | mk_precase _ _ [] (_::_) = error "premise with a too long HIERarchy label"
      | mk_precase n abs_ofixes (bl :: prg_ctxt) prems =
          let
            val (m, Block (s, vars)) = bl
            val fixes = map #fix vars
            val params = map #abs vars
            val (prems1, prems2) = chop_prefix (fn (m,_) => m = n) prems

            val abs_fixes = abs_ofixes o fold_rev Term.absfree params

            val prems' = prems1
              |> map (fn (_, (x,t)) => (swap (the_default (case_premsN, ~1) x), t))
              |> coalesce_order (prod_ord int_ord string_ord)
              |> map (apfst snd)
              |> unique_names

            val assumes = map (apsnd (map abs_fixes)) prems'

            val fixes' = bindings fixes

            val binds =
              let
                val prem_bs = maps find_binds (maps snd prems')
                val (concl_cases, concl_bs) = case prg_ctxt of
                    [] => ([(bind_unnamedN, abs_fixes t)], find_binds t)
                  | (_::_) => ([],[])
                val bs = concl_bs @ prem_bs
                  |> sort (prod_ord int_ord (prod_ord string_ord Term_Ord.fast_term_ord))
                  |> map snd
                  |> map (apsnd abs_fixes)
                  |> filter_out (has_loose_bounds o snd)
              in
                concl_cases @ bs
                |> unique_binds []
                |> map (apsnd SOME)
              end

            val precase = Precase {
              fixes = fixes',
              assumes = assumes,
              binds = binds,
              cases = mk_precase (n+1) abs_fixes prg_ctxt prems2 }
          in [((m,s), precase)] end
  in mk_precase 1 drop_labels prg_ctxt sorted_prems end

fun merge_precases precases =
  let
    val _ = precases : ((int * string) * (int * string, string) precase) list (*XXX*)
    fun merge_p (_, []) = error "empty case" (*XXX*)
      | merge_p (s, Precase {fixes, assumes, binds, cases} :: pcs) =
        let
          fun sel_cases (Precase {cases, ...}) = cases
          val cases' = merge_precases (cases @ maps sel_cases pcs)
        in (s, Rule_Cases.Case {fixes = fixes, assumes = assumes, binds = binds, cases = cases'}) end
    val cases = precases
      |> coalesce_order (prod_ord int_ord string_ord)
      |> map (apfst snd)
      |> unique_names
      |> map merge_p
  in cases end

fun mk_cases' ctxt = Thm.prems_of
  #> map (fn t => Variable.focus NONE t ctxt)
  #> strip_prg_ctxts
  #> maps build_precase
  #> merge_precases
  #> map (apsnd SOME)

fun normalize_conv cv ctxt ct = Conv.bottom_conv (fn ctxt => Conv.try_conv (
  cv then_conv normalize_conv cv ctxt
  )) ctxt ct

fun prepare_labels_tac ctxt =
  let
    val suc_numeral_simps = @{thms
      Suc_numeral_simps[THEN eq_reflection]
      append.simps[THEN eq_reflection]}
    val app_simps = @{thms append.simps[THEN eq_reflection]}
    val suc_to_num_conv = normalize_conv (Conv.rewrs_conv (suc_numeral_simps @ app_simps))
    val label_fun_conv = Conv.fun_conv o suc_to_num_conv
    fun label_conv ctxt ct =
      (case Thm.term_of ct of
       Const (@{const_name Case_Labeling.BIND}, _) $ _ $ _ $ _ => label_fun_conv ctxt ct
      | Const (@{const_name Case_Labeling.HIER}, _) $ _ $ _ => label_fun_conv ctxt ct
      | Const (@{const_name Case_Labeling.VC}, _) $ _ $ _ => label_fun_conv ctxt ct
      | _ => Conv.no_conv ct)
    fun norm_labels_conv ctxt ct =
      Conv.bottom_conv (Conv.try_conv o label_conv) ctxt ct
  in
    CONVERSION (norm_labels_conv ctxt)
  end

fun extract_cases_tac (ctxt, st) =
  let val tac = unfold_tac ctxt @{thms LABEL_simps}
  in CONTEXT_CASES (mk_cases' ctxt st) tac (ctxt, st) end


(* Splits the nth \<forall> into its components and simplifies any case_prod over this variable*)

structure Splitsubst = Hypsubst
(
  val dest_Trueprop = HOLogic.dest_Trueprop
  val dest_eq = dest_SPLIT
  val dest_imp = HOLogic.dest_imp
  val eq_reflection = @{thm SPLIT_reflection}
  val rev_eq_reflection = @{thm rev_SPLIT_reflection}
  val imp_intr         = @{thm impI}
  val rev_mp           = @{thm rev_mp}
  val subst            = @{thm SPLIT_subst}
  val sym              = @{thm SPLIT_sym}
  val thin_refl        = @{thm SPLIT_thin_refl}
)

val hyp_subst_tac = Splitsubst.hyp_subst_tac

fun SPLIT_subst_tac ctxt =
  REPEAT_ALL_NEW (REPEAT_ALL_NEW (ematch_tac ctxt @{thms SPLIT_prodE}) THEN' Splitsubst.hyp_subst_tac ctxt)

local
val case_prod_th = @{thm split_conv[THEN eq_reflection]}

fun case_prod_conv ctxt =
  Conv.forall_conv (fn (x, ctxt) =>
  Conv.forall_conv (fn (y, ctxt) => fn ct =>
    let
      val insts = [NONE, SOME x, SOME y]
      val typ_insts = map (Option.map Thm.ctyp_of_cterm) insts
      val th = Thm.instantiate' typ_insts insts case_prod_th
    in Conv.bottom_conv (fn _ => Conv.try_conv (Conv.rewr_conv th)) ctxt ct end
  ) ctxt) ctxt

in

fun split_nth_all_conv {right_only:bool} =
  let
    val desc_conv = if right_only then Conv.try_conv else Conv.repeat_conv
    fun conv ctxt 0 ct =
          desc_conv (
            Conv.rewr_conv @{thm split_paired_all}
            then_conv case_prod_conv ctxt
            then_conv Conv.try_conv (conv ctxt 1)
          ) ct
      | conv ctxt n ct =
          Conv.forall_conv (fn (_, ctxt) => conv ctxt (n - 1)) ctxt ct
  in conv end

fun split_bind_all_conv right_only ctxt ct =
  let
    val {vars, label, prems} = parse_label (Thm.term_of ct)

    val nvars = length vars
    val bv_ts = label |> map (fn x => case x of (_, Block (_, vs)) => vs) |> flat

    val sv_ts = prems
      |> map_filter (try dest_SPLIT)
      |> map snd
      |> maps Util.dest_tuple

    val lvars = bv_ts @ sv_ts
      |> maps dest_Bound
      |> sort_distinct int_ord
      |> map (fn n => nvars - n - 1)
  in Conv.every_conv (map (split_nth_all_conv right_only ctxt) lvars) ct end

fun RAWCONV cv i st = Seq.single (Conv.gconv_rule cv i st)

fun split_bind_all_tac {right_only: bool, simp_all_cases: bool} ctxt =
  let
    val rewr_tac = if simp_all_cases
      then Raw_Simplifier.rewrite_goal_tac ctxt [case_prod_th] else K all_tac
  in
    RAWCONV (split_bind_all_conv {right_only = right_only} ctxt) THEN' rewr_tac
  end

end

datatype options = Options of { simp_all_cases: bool, split_right_only: bool, protect_subgoals: bool}

fun casify_tac (Options { simp_all_cases, split_right_only, protect_subgoals }) (ctxt, st) =
  let
    fun inst_disambig ct = Thm.instantiate ([], [((("n", 0), @{typ nat}), ct)]) @{thm DISAMBIG_I}
    fun disambig_tac i =
      if protect_subgoals
      then match_tac ctxt [inst_disambig (Thm.cterm_of ctxt (HOLogic.mk_number @{typ nat} i))]
      else K all_tac
    val prep_tac = DETERM (ALLGOALS (fn i => EVERY'
      [ prepare_labels_tac ctxt,
        split_bind_all_tac { simp_all_cases = simp_all_cases, right_only = split_right_only } ctxt,
        TRY o SPLIT_subst_tac ctxt,
        disambig_tac i
        ] i
      ))
  in (ctxt, st) |> (prep_tac THEN_CONTEXT extract_cases_tac) end

local

fun set_simp_all_cases simp_all_cases
    (Options { simp_all_cases = _, split_right_only, protect_subgoals}) =
  Options { simp_all_cases = simp_all_cases, split_right_only = split_right_only,
    protect_subgoals = protect_subgoals }

fun set_protect_subgoals protect_subgoals
    (Options { simp_all_cases, split_right_only, protect_subgoals = _}) =
  Options { simp_all_cases = simp_all_cases, split_right_only = split_right_only,
    protect_subgoals = protect_subgoals }

fun set_split_right_only split_right_only
    (Options { simp_all_cases, split_right_only = _, protect_subgoals}) =
  Options { simp_all_cases = simp_all_cases, split_right_only = split_right_only,
    protect_subgoals = protect_subgoals }

val options = map (fn (s,f) => Args.parens (Args.$$$ s) >> K f)
  [ ("simp", set_simp_all_cases true),
    ("no_simp", set_simp_all_cases false),
    ("disambig_subgoals", set_protect_subgoals true),
    ("no_disambig_subgoals", set_protect_subgoals false),
    ("split_right_only", set_split_right_only true),
    ("no_split_right_only", set_split_right_only false)
  ]

fun scan_alt scans = fold (fn scan1 => fn scan2 => scan1 || scan2) scans Scan.fail

in

fun casify_options def = Scan.repeat (scan_alt options)
  >> (fn xs => fold (fn f => fn x => f x) xs def)

end

fun casify_method_setup def =
  Scan.lift (casify_options def) >>
    (fn opt => fn _ => Util.SIMPLE_METHOD_CASES (casify_tac opt))

end
