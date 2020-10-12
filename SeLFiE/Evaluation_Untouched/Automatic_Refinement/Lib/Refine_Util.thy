section "General Utilities"
theory Refine_Util
imports Refine_Util_Bootstrap1 Mpat_Antiquot Mk_Term_Antiquot
begin
definition conv_tag where "conv_tag n x == x" 
  \<comment> \<open>Used internally for @{text "pat_conv"}-conversion\<close>

lemma shift_lambda_left: "(f \<equiv> \<lambda>x. g x) \<Longrightarrow> (\<And>x. f x \<equiv> g x)" by simp
  
ML \<open>
  infix 0 THEN_ELSE' THEN_ELSE_COMB'
  infix 1 THEN_ALL_NEW_FWD THEN_INTERVAL
  infix 2 ORELSE_INTERVAL
  infix 3 ->>

  signature BASIC_REFINE_UTIL = sig
    include BASIC_REFINE_UTIL
    (* Resolution with matching *)
    val RSm: Proof.context -> thm -> thm -> thm

    val is_Abs: term -> bool
    val is_Comb: term -> bool
    val has_Var: term -> bool

    val is_TFree: typ -> bool

    val is_def_thm: thm -> bool

    (* Tacticals *)
    type tactic' = int -> tactic
    type itactic = int -> int -> tactic

    val IF_EXGOAL: (int -> tactic) -> tactic'
    val COND': (term -> bool) -> tactic'
    val CONCL_COND': (term -> bool) -> tactic'
    
    val THEN_ELSE': tactic' * (tactic' * tactic') -> tactic'
    val THEN_ELSE_COMB': 
      tactic' * ((tactic'*tactic'->tactic') * tactic' * tactic') -> tactic'

    val INTERVAL_FWD: tactic' -> int -> int -> tactic
    val THEN_ALL_NEW_FWD: tactic' * tactic' -> tactic'
    val REPEAT_ALL_NEW_FWD: tactic' -> tactic'
    val REPEAT_DETERM': tactic' -> tactic'
    val REPEAT': tactic' -> tactic'
    val ALL_GOALS_FWD': tactic' -> tactic'
    val ALL_GOALS_FWD: tactic' -> tactic

    val APPEND_LIST': tactic' list -> tactic'

    val SINGLE_INTERVAL: itactic -> tactic'
    val THEN_INTERVAL: itactic * itactic -> itactic
    val ORELSE_INTERVAL: itactic * itactic -> itactic

    val CAN': tactic' -> tactic'

    val NTIMES': tactic' -> int -> tactic'

    (* Only consider results that solve subgoal. If none, return all results unchanged. *)
    val TRY_SOLVED': tactic' -> tactic'

    (* Case distinction with tactics. Generalization of THEN_ELSE to lists. *)
    val CASES': (tactic' * tactic) list -> tactic'

    (* Tactic that depends on subgoal term structure *)
    val WITH_subgoal: (term -> tactic') -> tactic'
    (* Tactic that depends on subgoal's conclusion term structure *)
    val WITH_concl: (term -> tactic') -> tactic'

    (* Tactic version of Variable.trade. Import, apply tactic, and export results.
      One effect is that schematic variables in the goal are fixed, and thus cannot 
      be instantiated by the tactic.
    *)
    val TRADE: (Proof.context -> tactic') -> Proof.context -> tactic'


    (* Tactics *)
    val fo_rtac: thm -> Proof.context -> tactic'
    val fo_resolve_tac: thm list -> Proof.context -> tactic'
    val rprems_tac: Proof.context -> tactic'
    val rprem_tac: int -> Proof.context -> tactic'
    val elim_all_tac: Proof.context -> thm list -> tactic

    val prefer_tac: int -> tactic

    val insert_subgoal_tac: cterm -> tactic'
    val insert_subgoals_tac: cterm list -> tactic'

    val eqsubst_inst_tac: Proof.context -> bool -> int list 
      -> ((indexname * Position.T) * string) list -> thm -> int -> tactic

    val eqsubst_inst_meth: (Proof.context -> Proof.method) context_parser

    (* Parsing *)
    val ->> : 'a context_parser *('a * Context.generic -> 'b * Context.generic)
      -> 'b context_parser

  end

  signature REFINE_UTIL = sig
    include BASIC_REFINE_UTIL

    val order_by: ('a * 'a -> order) -> ('b -> 'a) -> 'b list -> 'b list
    val build_res_net: thm list -> (int * thm) Net.net

    (* Terms *)
    val fo_matchp: theory -> cterm -> term -> term list option
    val fo_matches: theory -> cterm -> term -> bool

    val anorm_typ: typ -> typ
    val anorm_term: term -> term

    val import_cterms: bool -> cterm list -> Proof.context -> 
      cterm list * Proof.context

    val subsume_sort: ('a -> term) -> theory -> 'a list -> 'a list
    val subsume_sort_gen: ('a -> term) -> Context.generic 
      -> 'a list -> 'a list

    val mk_compN1: typ list -> int -> term -> term -> term
    val mk_compN: int -> term -> term -> term

    val dest_itselfT: typ -> typ
    val dummify_tvars: term -> term

    (* a\<equiv>\<lambda>x. f x  \<mapsto>  a ?x \<equiv> f ?x *)
    val shift_lambda_left: thm -> thm
    val shift_lambda_leftN: int -> thm -> thm

    (* Left-Bracketed Structures *)

    (* Map [] to z, and [x1,...,xN] to f(...f(f(x1,x2),x3)...) *)
    val list_binop_left: 'a -> ('a * 'a -> 'a) -> 'a list -> 'a
    (* Map [] to z, [x] to i x, [x1,...,xN] to f(...f(f(x1,x2),x3)...), thread state *)
    val fold_binop_left: ('c -> 'b * 'c) -> ('a -> 'c -> 'b * 'c) -> ('b * 'b -> 'b) 
          -> 'a list -> 'c -> 'b * 'c

    (* Tuples, handling () as empty tuple *)      
    val strip_prodT_left: typ -> typ list
    val list_prodT_left: typ list -> typ
    val mk_ltuple: term list -> term
    (* Fix a tuple of new frees *)
    val fix_left_tuple_from_Ts: string -> typ list -> Proof.context -> term * Proof.context

    (* HO-Patterns with tuples *)
    (* Lambda-abstraction over list of terms, recognizing tuples *)
    val lambda_tuple: term list -> term -> term
    (* Instantiate tuple-types in specified variables *)
    val instantiate_tuples: Proof.context -> (indexname*typ) list -> thm -> thm
    (* Instantiate tuple-types in variables from given term *)
    val instantiate_tuples_from_term_tac: Proof.context -> term -> tactic
    (* Instantiate tuple types in variables of subgoal *)
    val instantiate_tuples_subgoal_tac: Proof.context -> tactic'




    (* Rules *)
    val abs_def: Proof.context -> thm -> thm

    (* Rule combinators *)
    
    (* Iterate rule on theorem until it fails *)  
    val repeat_rule: (thm -> thm) -> thm -> thm
    (* Apply rule on theorem and assert that theorem was changed *)
    val changed_rule: (thm -> thm) -> thm -> thm
    (* Try rule on theorem, return theorem unchanged if rule fails *)
    val try_rule: (thm -> thm) -> thm -> thm
    (* Singleton version of Variable.trade *)
    val trade_rule: (Proof.context -> thm -> thm) -> Proof.context -> thm -> thm
    (* Combine with first matching theorem *)
    val RS_fst: thm -> thm list -> thm
    (* Instantiate first matching theorem *)
    val OF_fst: thm list -> thm list -> thm


    (* Conversion *)
    val trace_conv: conv
    val monitor_conv: string -> conv -> conv
    val monitor_conv': string -> (Proof.context -> conv) -> Proof.context -> conv

    val fixup_vars: cterm -> thm -> thm
    val fixup_vars_conv: conv -> conv
    val fixup_vars_conv': (Proof.context -> conv) -> Proof.context -> conv

    val pat_conv': cterm -> (string -> Proof.context -> conv) -> Proof.context
      -> conv
    val pat_conv: cterm -> (Proof.context -> conv) -> Proof.context -> conv

    val HOL_concl_conv: (Proof.context -> conv) -> Proof.context -> conv

    val import_conv: (Proof.context -> conv) -> Proof.context -> conv

    val fix_conv: Proof.context -> conv -> conv
    val ite_conv: conv -> conv -> conv -> conv

    val cfg_trace_f_tac_conv: bool Config.T
    val f_tac_conv: Proof.context -> (term -> term) -> tactic -> conv

    (* Conversion combinators to choose first matching position *)
    (* Try argument, then function *)
    val fcomb_conv: conv -> conv
    (* Descend over function or abstraction *)
    val fsub_conv: (Proof.context -> conv) -> Proof.context -> conv 
    (* Apply to topmost matching position *)
    val ftop_conv: (Proof.context -> conv) -> Proof.context -> conv


    (* Parsing *)
    val parse_bool_config: string -> bool Config.T -> bool context_parser
    val parse_paren_list: 'a context_parser -> 'a list context_parser
    val parse_paren_lists: 'a context_parser -> 'a list list context_parser

    (* 2-step configuration parser *)
    (* Parse boolean config, name or no_name. *)
    val parse_bool_config': string -> bool Config.T -> Token.T list -> (bool Config.T * bool) * Token.T list
    (* Parse optional (p1,...,pn). Empty list if nothing parsed. *)
    val parse_paren_list': 'a parser -> Token.T list -> 'a list * Token.T list
    (* Apply list of (config,value) pairs *)
    val apply_configs: ('a Config.T * 'a) list -> Proof.context -> Proof.context


  end


  structure Refine_Util: REFINE_UTIL = struct
    open Basic_Refine_Util

    fun RSm ctxt thA thB = let
      val (thA, ctxt') = ctxt
        |> Variable.declare_thm thA
        |> Variable.declare_thm thB
        |> yield_singleton (apfst snd oo Variable.import true) thA
      val thm = thA RS thB
      val thm = singleton (Variable.export ctxt' ctxt) thm
        |> Drule.zero_var_indexes
    in 
      thm
    end

    fun is_Abs (Abs _) = true | is_Abs _ = false
    fun is_Comb (_$_) = true | is_Comb _ = false

    fun has_Var (Var _) = true
      | has_Var (Abs (_,_,t)) = has_Var t
      | has_Var (t1$t2) = has_Var t1 orelse has_Var t2
      | has_Var _ = false

    fun is_TFree (TFree _) = true
      | is_TFree _ = false

    fun is_def_thm thm = case thm |> Thm.prop_of of
      Const (@{const_name "Pure.eq"},_)$_$_ => true | _ => false


    type tactic' = int -> tactic
    type itactic = int -> int -> tactic

    (* Fail if subgoal does not exist *)
    fun IF_EXGOAL tac i st = if i <= Thm.nprems_of st then
      tac i st
    else no_tac st;

    fun COND' P = IF_EXGOAL (fn i => fn st => 
      (if P (Thm.prop_of st |> curry Logic.nth_prem i) then
      all_tac st else no_tac st) 
      handle TERM _ => no_tac st
      | Pattern.MATCH => no_tac st
    )

    (* FIXME: Subtle difference between Logic.concl_of_goal and this:
         concl_of_goal converts loose bounds to frees!
    *)
    fun CONCL_COND' P = COND' (strip_all_body #> Logic.strip_imp_concl #> P)

    fun (tac1 THEN_ELSE' (tac2,tac3)) x = tac1 x THEN_ELSE (tac2 x,tac3 x);  

    (* If first tactic succeeds, combine its effect with "comb tac2", 
      otherwise use tac_else. Example: 
        tac1 THEN_ELSE_COMB ((THEN_ALL_NEW),tac2,tac_else)  *)
    fun (tac1 THEN_ELSE_COMB' (comb,tac2,tac_else)) i st = let
      val rseq = tac1 i st
    in
      case seq_is_empty rseq of
        (true,_) => tac_else i st
      | (false,rseq) => comb (K(K( rseq )), tac2) i st

    end

    (* Apply tactic to subgoals in interval, in a forward manner, skipping over
      emerging subgoals *)
    fun INTERVAL_FWD tac l u st =
      if l>u then all_tac st 
      else (tac l THEN (fn st' => let
          val ofs = Thm.nprems_of st' - Thm.nprems_of st;
        in
          if ofs < ~1 then raise THM (
            "INTERVAL_FWD: Tac solved more than one goal",~1,[st,st'])
          else INTERVAL_FWD tac (l+1+ofs) (u+ofs) st'
        end)) st;

    (* Apply tac2 to all subgoals emerged from tac1, in forward manner. *)
    fun (tac1 THEN_ALL_NEW_FWD tac2) i st =
      (tac1 i 
        THEN (fn st' => INTERVAL_FWD tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st) st')
      ) st;

    fun REPEAT_ALL_NEW_FWD tac =
      tac THEN_ALL_NEW_FWD (TRY o (fn i => REPEAT_ALL_NEW_FWD tac i));

    (* Repeat tac on subgoal. Determinize each step. 
       Stop if tac fails or subgoal is solved. *)
    fun REPEAT_DETERM' tac i st = let
      val n = Thm.nprems_of st 
    in
      REPEAT_DETERM (COND (has_fewer_prems n) no_tac (tac i)) st
    end

    fun REPEAT' tac i st = let
      val n = Thm.nprems_of st 
    in
      REPEAT (COND (has_fewer_prems n) no_tac (tac i)) st
    end

    (* Apply tactic to all goals in a forward manner.
      Newly generated goals are ignored.
    *)
    fun ALL_GOALS_FWD' tac i st =
      (tac i THEN (fn st' => 
        let
          val i' = i + Thm.nprems_of st' + 1 - Thm.nprems_of st;
        in
          if i' <= Thm.nprems_of st' then
            ALL_GOALS_FWD' tac i' st'
          else
            all_tac st'
        end
      )) st;

    fun ALL_GOALS_FWD tac = ALL_GOALS_FWD' tac 1;

    fun APPEND_LIST' tacs = fold_rev (curry (op APPEND')) tacs (K no_tac);

    fun SINGLE_INTERVAL tac i = tac i i

    fun ((tac1:itactic) THEN_INTERVAL (tac2:itactic)) = 
      (fn i => fn j => fn st =>
        ( tac1 i j
          THEN (fn st' => tac2 i (j + Thm.nprems_of st' - Thm.nprems_of st) st')
        ) st
      ):itactic

    fun tac1 ORELSE_INTERVAL tac2 = (fn i => fn j => tac1 i j ORELSE tac2 i j)

    (* Fail if tac fails, otherwise do nothing *)
    fun CAN' tac i st = 
      case tac i st |> Seq.pull of
        NONE => Seq.empty
      | SOME _ => Seq.single st

    (* Repeat tactic n times *)
    fun NTIMES' _ 0 _ st = Seq.single st
      | NTIMES' tac n i st = (tac THEN' NTIMES' tac (n-1)) i st

    (* Resolve with rule. Use first-order unification.
      From cookbook, added exception handling *)
    fun fo_rtac thm = Subgoal.FOCUS (fn {context = ctxt, concl, ...} => 
    let
      val concl_pat = Drule.strip_imp_concl (Thm.cprop_of thm)
      val insts = Thm.first_order_match (concl_pat, concl)
    in
      resolve_tac ctxt [Drule.instantiate_normalize insts thm] 1
    end handle Pattern.MATCH => no_tac )

    fun fo_resolve_tac thms ctxt = 
      FIRST' (map (fn thm => fo_rtac thm ctxt) thms);

    (* Resolve with premises. Copied and adjusted from Goal.assume_rule_tac. *)
    fun rprems_tac ctxt = Goal.norm_hhf_tac ctxt THEN' CSUBGOAL (fn (goal, i) =>
      let
        fun non_atomic (Const (@{const_name Pure.imp}, _) $ _ $ _) = true
          | non_atomic (Const (@{const_name Pure.all}, _) $ _) = true
          | non_atomic _ = false;

        val ((_, goal'), ctxt') = Variable.focus_cterm NONE goal ctxt;
        val goal'' = Drule.cterm_rule 
          (singleton (Variable.export ctxt' ctxt)) goal';
        val Rs = filter (non_atomic o Thm.term_of) 
          (Drule.strip_imp_prems goal'');

        val ethms = Rs |> map (fn R =>
          (Simplifier.norm_hhf ctxt (Thm.trivial R)));
      in eresolve_tac ctxt ethms i end
      );

    (* Resolve with premise. Copied and adjusted from Goal.assume_rule_tac. *)
    fun rprem_tac n ctxt = Goal.norm_hhf_tac ctxt THEN' CSUBGOAL (fn (goal, i) =>
      let
        val ((_, goal'), ctxt') = Variable.focus_cterm NONE goal ctxt;
        val goal'' = Drule.cterm_rule 
          (singleton (Variable.export ctxt' ctxt)) goal';

        val R = nth (Drule.strip_imp_prems goal'') (n - 1)
        val rl = Simplifier.norm_hhf ctxt (Thm.trivial R)
      in
        eresolve_tac ctxt [rl] i
      end
      );

    fun elim_all_tac ctxt thms = ALLGOALS (REPEAT_ALL_NEW (ematch_tac ctxt thms))

    fun prefer_tac i = defer_tac i THEN PRIMITIVE (Thm.permute_prems 0 ~1)

    fun order_by ord f = sort (ord o apply2 f)

    (* CLONE from tactic.ML *)
    local
      (*insert one tagged rl into the net*)
      fun insert_krl (krl as (_,th)) =
        Net.insert_term (K false) (Thm.concl_of th, krl);
    in
      (*build a net of rules for resolution*)
      fun build_res_net rls =
        fold_rev insert_krl (tag_list 1 rls) Net.empty;
    end

    fun insert_subgoals_tac cts i = PRIMITIVE (
      Thm.permute_prems 0 (i - 1)
      #> fold_rev Thm.implies_intr cts
      #> Thm.permute_prems 0 (~i + 1)
    )

    fun insert_subgoal_tac ct i = insert_subgoals_tac [ct] i

  local
    (* Substitution with dynamic instantiation of parameters.
       By Lars Noschinski. *)
    fun eqsubst_tac' ctxt asm =
      if asm then EqSubst.eqsubst_asm_tac ctxt else EqSubst.eqsubst_tac ctxt

    fun subst_method inst_tac tac =
      Args.goal_spec --
      Scan.lift (Args.mode "asm" -- Scan.optional (Args.parens (Scan.repeat Parse.nat)) [0]) --
      Scan.optional (Scan.lift
        (Parse.and_list1 
          (Parse.position Args.var -- (Args.$$$ "=" |-- Parse.!!! Args.embedded_inner_syntax)) --|
          Args.$$$ "in")) [] --
      Attrib.thms >>
      (fn (((quant, (asm, occL)), insts), thms) => fn ctxt => METHOD 
        (fn facts =>
          if null insts then 
            quant (Method.insert_tac ctxt facts THEN' tac ctxt asm occL thms)
          else
            (case thms of
              [thm] => quant (
                Method.insert_tac ctxt facts THEN' inst_tac ctxt asm occL insts thm)
            | _ => error "Cannot have instantiations with multiple rules")));

  in
    fun eqsubst_inst_tac ctxt asm occL insts thm = 
      Subgoal.FOCUS (
        fn {context=ctxt,...} => let
          val ctxt' = ctxt |> Proof_Context.set_mode Proof_Context.mode_schematic  (* FIXME !? *)
          val thm' = thm |> Rule_Insts.read_instantiate ctxt' insts []
        in eqsubst_tac' ctxt asm occL [thm'] 1 end
      ) ctxt


    val eqsubst_inst_meth = subst_method eqsubst_inst_tac eqsubst_tac'
  end

    (* Match pattern against term, and return list of values for non-dummy
      variables. A variable is considered dummy if its name starts with 
      an underscore (_)*)
    fun fo_matchp thy cpat t = let
      fun ignore (Var ((name,_),_)) = String.isPrefix "_" name
        | ignore _ = true;

      val pat = Thm.term_of cpat;
      val pvars = fold_aterms (
        fn t => fn l => if is_Var t andalso not (ignore t)
          then t::l else l
      ) pat [] |> rev
      val inst = Pattern.first_order_match thy (pat,t) 
        (Vartab.empty,Vartab.empty);
    in SOME (map (Envir.subst_term inst) pvars) end 
    handle Pattern.MATCH => NONE;

    val fo_matches = is_some ooo fo_matchp


    fun anorm_typ ty = let
      val instT = Term.add_tvarsT ty []
      |> map_index (fn (i,(n,s)) => (n,TVar (("t"^string_of_int i,0),s)))
      val ty = Term.typ_subst_TVars instT ty;
    in ty end;

    fun anorm_term t = let
      val instT = Term.add_tvars t []
      |> map_index (fn (i,(n,s)) => (n,TVar (("t"^string_of_int i,0),s)))
      val t = Term.subst_TVars instT t;
      val inst = Term.add_vars t []
      |> map_index (fn (i,(n,s)) => (n,Var (("v"^string_of_int i,0),s)))
      val t = Term.subst_Vars inst t;
    in t end;

    fun import_cterms is_open cts ctxt = let
      val ts = map Thm.term_of cts
      val (ts', ctxt') = Variable.import_terms is_open ts ctxt
      val cts' = map (Thm.cterm_of ctxt) ts'
    in (cts', ctxt') end


    (* Order a list of items such that more specific items come
       before less specific ones. The term to be compared is
       extracted by a function that is given as parameter.
    *)
    fun subsume_sort f thy items = let
      val rhss = map (Envir.beta_eta_contract o f) items
      fun freqf thy net rhs = Net.match_term net rhs 
        |> filter (fn p => Pattern.matches thy (p,rhs))
        |> length

      val net = fold 
        (fn rhs => Net.insert_term_safe (op =) (rhs,rhs)) rhss Net.empty 

      val freqs = map (freqf thy net) rhss

      val res = freqs ~~ items 
        |> sort (rev_order o int_ord o apply2 fst)
        |> map snd
  
    in res end

    fun subsume_sort_gen f = subsume_sort f o Context.theory_of

    fun mk_comp1 env (f, g) =
      let
        val fT = fastype_of1 (env, f);
        val gT = fastype_of1 (env, g);
        val compT = fT --> gT --> domain_type gT --> range_type fT;
      in Const ("Fun.comp", compT) $ f $ g end;

    fun mk_compN1 _   0 f g = f$g
      | mk_compN1 env 1 f g = mk_comp1 env (f, g)
      | mk_compN1 env n f g = let
          val T = fastype_of1 (env, g) |> domain_type
          val g = incr_boundvars 1 g $ Bound 0
          val env = T::env
        in
          Abs ("x"^string_of_int n,T,mk_compN1 env (n-1) f g)
        end

    val mk_compN = mk_compN1 []    

    fun abs_def ctxt = Local_Defs.meta_rewrite_rule ctxt #> Drule.abs_def

    fun trace_conv ct = (tracing (@{make_string} ct); Conv.all_conv ct);

    fun monitor_conv msg conv ct = let
      val _ = tracing (msg ^ " (gets): " ^ @{make_string} ct);
      val res = conv ct 
        handle exc =>
         (if Exn.is_interrupt exc then Exn.reraise exc
          else tracing (msg ^ " (raises): " ^ @{make_string} exc);
          Exn.reraise exc)
      val _ = tracing (msg ^ " (yields): " ^ @{make_string} res);
    in res end

    fun monitor_conv' msg conv ctxt ct = monitor_conv msg (conv ctxt) ct

    fun fixup_vars ct thm = let
      val lhs = Thm.lhs_of thm
      val inst = Thm.first_order_match (lhs,ct)
      val thm' = Thm.instantiate inst thm
    in thm' end

    fun fixup_vars_conv conv ct = fixup_vars ct (conv ct)

    fun fixup_vars_conv' conv ctxt = fixup_vars_conv (conv ctxt)

    local
      fun tag_ct ctxt name ct = let
        val t = Thm.term_of ct;
        val ty = fastype_of t;
        val t' = Const (@{const_name conv_tag},@{typ unit}-->ty-->ty)
          $Free (name,@{typ unit})$t;
        val ct' = Thm.cterm_of ctxt t';
      in ct' end

      fun mpat_conv pat ctxt ct = let
        val (tym,tm) = Thm.first_order_match (pat,ct);
        val tm' = map (fn (pt as ((name, _), _),ot) => (pt, tag_ct ctxt name ot)) tm;
        val ct' = Thm.instantiate_cterm (tym,tm') pat;
        val rthm =
          Goal.prove_internal ctxt []
            (Thm.cterm_of ctxt (Logic.mk_equals (apply2 Thm.term_of (ct, ct'))))
            (K (simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms conv_tag_def}) 1))
        |> Goal.norm_result ctxt
      in 
        fixup_vars ct rthm 
      end handle Pattern.MATCH 
        => raise (CTERM ("mpat_conv: No match",[pat,ct]));

      fun tag_conv cnv ctxt ct = case Thm.term_of ct of
        Const (@{const_name conv_tag},_)$Free(name,_)$_ => (
          (Conv.rewr_conv (@{thm conv_tag_def}) then_conv (cnv name) ctxt) ct)
      | _ => Conv.all_conv ct;

      fun all_tag_conv cnv = Conv.bottom_conv (tag_conv cnv);
    in 
      (* Match against pattern, and apply parameter conversion to matches of
         variables prefixed by hole_prefix.
      *)
      fun pat_conv' cpat cnv ctxt = 
        mpat_conv cpat ctxt
        then_conv (all_tag_conv cnv ctxt);

      fun pat_conv cpat conv = pat_conv' cpat 
        (fn name => case name of "HOLE" => conv | _ => K Conv.all_conv);
    end

    fun HOL_concl_conv cnv = Conv.params_conv ~1 
      (fn ctxt => Conv.concl_conv ~1 (
        HOLogic.Trueprop_conv (cnv ctxt)));


    fun import_conv conv ctxt ct = let
      val (ct',ctxt') = yield_singleton (import_cterms true) ct ctxt
      val res = conv ctxt' ct'
      val res' = singleton (Variable.export ctxt' ctxt) res |> fixup_vars ct
    in res' end


    fun fix_conv ctxt conv ct = let
      val thm = conv ct
      val eq = Logic.mk_equals (Thm.term_of ct, Thm.term_of ct) |> head_of
    in if (Thm.term_of (Thm.lhs_of thm) aconv Thm.term_of ct)
      then thm
      else thm RS Thm.trivial (Thm.mk_binop (Thm.cterm_of ctxt eq) ct (Thm.rhs_of thm))
    end

    fun ite_conv cv cv1 cv2 ct =
      let 
        val eq1 = SOME (cv ct) 
          handle THM _ => NONE
            | CTERM _ => NONE
            | TERM _ => NONE
            | TYPE _ => NONE;
        val res = case eq1 of
          NONE => cv2 ct
        | SOME eq1 => let val eq2 = cv1 (Thm.rhs_of eq1) in 
            if Thm.is_reflexive eq1 then eq2
            else if Thm.is_reflexive eq2 then eq1
            else Thm.transitive eq1 eq2
          end
      in res end

      val cfg_trace_f_tac_conv = 
        Attrib.setup_config_bool @{binding trace_f_tac_conv} (K false)

      (* Transform term and prove equality to original by tactic *)
      fun f_tac_conv ctxt f tac ct = let
        val t = Thm.term_of ct
        val t' = f t
        val goal = Logic.mk_equals (t,t')
        val _ = if Config.get ctxt cfg_trace_f_tac_conv then
          tracing (Syntax.string_of_term ctxt goal)
        else ()

        val goal = Thm.cterm_of ctxt goal

        val thm = Goal.prove_internal ctxt [] goal (K tac)
      in
        thm
      end

    (* Apply function to result and context *)
    fun (p->>f) ctks = let
      val (res,(context,tks)) = p ctks
      val (res,context) = f (res, context)
    in
      (res,(context,tks))
    end

    fun parse_bool_config name cfg = (
      Scan.lift (Args.$$$ name)
        ->> (apsnd (Config.put_generic cfg true) #>> K true)
      || 
      Scan.lift (Args.$$$ ("no_"^name))
        ->> (apsnd (Config.put_generic cfg false) #>> K false)
      )

    fun parse_paren_list p = 
      Scan.lift (
        Args.$$$ "(") |-- Parse.enum1' "," p --| Scan.lift (Args.$$$ ")"
      )

    fun parse_paren_lists p = Scan.repeat (parse_paren_list p)

    val _ = Theory.setup
      (Method.setup @{binding fo_rule} 
        (Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (
          fo_resolve_tac thms ctxt))) 
        "resolve using first-order matching"
     #>
      Method.setup @{binding rprems} 
        (Scan.lift (Scan.option Parse.nat) >> (fn i => fn ctxt => 
          SIMPLE_METHOD' (
            case i of
              NONE => rprems_tac ctxt
            | SOME i => rprem_tac i ctxt
          ))
        )
        "resolve with premises"
      #> Method.setup @{binding elim_all}
         (Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD (elim_all_tac ctxt thms)))
         "repeteadly apply elimination rules to all subgoals"
      #> Method.setup @{binding subst_tac} eqsubst_inst_meth
         "single-step substitution (dynamic instantiation)"
      #> Method.setup @{binding clarsimp_all} (
           Method.sections Clasimp.clasimp_modifiers >> K (fn ctxt => SIMPLE_METHOD (
             CHANGED_PROP (ALLGOALS (Clasimp.clarsimp_tac ctxt))))
         ) "simplify and clarify all subgoals")



    


      (* Filter alternatives that solve a subgoal. 
        If no alternative solves goal, return result sequence unchanged *)
      fun TRY_SOLVED' tac i st = let
        val res = tac i st
        val solved = Seq.filter (fn st' => Thm.nprems_of st' < Thm.nprems_of st) res
      in 
        case Seq.pull solved of
          SOME _ => solved
        | NONE => res  
      end
    
      local
        fun CASES_aux [] = no_tac
          | CASES_aux ((tac1, tac2)::cs) = tac1 1 THEN_ELSE (tac2, CASES_aux cs)    
      in
        (* 
          Accepts a list of pairs of (pattern_tac', worker_tac), and applies
          worker_tac to results of first successful pattern_tac'.
        *)
        val CASES' = SELECT_GOAL o CASES_aux
      end    

      (* TODO/FIXME: There seem to be no guarantees when eta-long forms are introduced by unification.
        So, we have to expect eta-long forms everywhere, which may be a problem when matching terms
        syntactically.
      *)
      fun WITH_subgoal tac = 
        CONVERSION Thm.eta_conversion THEN' 
        IF_EXGOAL (fn i => fn st => tac (nth (Thm.prems_of st) (i - 1)) i st)
  
      fun WITH_concl tac = 
        CONVERSION Thm.eta_conversion THEN' 
        IF_EXGOAL (fn i => fn st => 
          tac (Logic.concl_of_goal (Thm.prop_of st) i) i st
        )

      fun TRADE tac ctxt i st = let
        val orig_ctxt = ctxt
        val (st,ctxt) = yield_singleton (apfst snd oo Variable.import true) st ctxt
        val seq = tac ctxt i st
          |> Seq.map (singleton (Variable.export ctxt orig_ctxt))
      in
        seq
      end

      (* Try argument, then function *)
      fun fcomb_conv conv = let open Conv in
        arg_conv conv else_conv fun_conv conv
      end
  
      (* Descend over function or abstraction *)
      fun fsub_conv conv ctxt = let 
        open Conv 
      in
        fcomb_conv (conv ctxt) else_conv
        abs_conv (conv o snd) ctxt else_conv
        no_conv
      end
  
      (* Apply to topmost matching position *)
      fun ftop_conv conv ctxt ct = 
        (conv ctxt else_conv fsub_conv (ftop_conv conv) ctxt) ct
  
      (* Iterate rule on theorem until it fails *)  
      fun repeat_rule n thm = case try n thm of
        SOME thm => repeat_rule n thm
      | NONE => thm
  
      (* Apply rule on theorem and assert that theorem was changed *)
      fun changed_rule n thm = let
        val thm' = n thm
      in
        if Thm.eq_thm_prop (thm, thm') then raise THM ("Same",~1,[thm,thm'])
        else thm'
      end

      (* Try rule on theorem *)
      fun try_rule n thm = case try n thm of
        SOME thm => thm | NONE => thm

      fun trade_rule f ctxt thm = 
        singleton (Variable.trade (map o f) ctxt) thm

      fun RS_fst thm thms = let
        fun r [] = raise THM ("RS_fst, no matches",~1,thm::thms)
          | r (thm'::thms) = case try (op RS) (thm,thm') of
              NONE => r thms | SOME thm => thm
  
      in
        r thms
      end

      fun OF_fst thms insts = let
        fun r [] = raise THM ("OF_fst, no matches",length thms,thms@insts)
          | r (thm::thms) = case try (op OF) (thm,insts) of
              NONE => r thms | SOME thm => thm
      in
        r thms
      end

      (* Map [] to z, and [x1,...,xN] to f(...f(f(x1,x2),x3)...) *)
      fun list_binop_left z f = let
        fun r [] = z
          | r [T] = T
          | r (T::Ts) = f (r Ts,T)
      in
        fn l => r (rev l)
      end    

      (* Map [] to z, [x] to i x, [x1,...,xN] to f(...f(f(x1,x2),x3)...), thread state *)
      fun fold_binop_left z i f = let
        fun r [] ctxt = z ctxt
          | r [T] ctxt = i T ctxt
          | r (T::Ts) ctxt = let 
              val (Ti,ctxt) = i T ctxt
              val (Tsi,ctxt) = r Ts ctxt
            in
              (f (Tsi,Ti),ctxt)
            end
      in
        fn l => fn ctxt => r (rev l) ctxt
      end    

  
  
      fun strip_prodT_left (Type (@{type_name Product_Type.prod},[A,B])) = strip_prodT_left A @ [B]
        | strip_prodT_left (Type (@{type_name Product_Type.unit},[])) = []
        | strip_prodT_left T = [T]
  
      val list_prodT_left = list_binop_left HOLogic.unitT HOLogic.mk_prodT

      (* Make tuple with left-bracket structure *)
      val mk_ltuple = list_binop_left HOLogic.unit HOLogic.mk_prod


  
      (* Fix a tuple of new frees *)
      fun fix_left_tuple_from_Ts name = fold_binop_left
        (fn ctxt => (@{term "()"},ctxt))
        (fn T => fn ctxt => let 
            val (x,ctxt) = yield_singleton Variable.variant_fixes name ctxt
            val x = Free (x,T)
          in 
            (x,ctxt)
          end)
        HOLogic.mk_prod  

      (* Replace all type-vars by dummyT *)
      val dummify_tvars = map_types (map_type_tvar (K dummyT))

      fun dest_itselfT (Type (@{type_name itself},[A])) = A
        | dest_itselfT T = raise TYPE("dest_itselfT",[T],[])


      fun shift_lambda_left thm = thm RS @{thm shift_lambda_left}
      fun shift_lambda_leftN i = funpow i shift_lambda_left
  

      (* TODO: Naming should be without ' for basic parse, and with ' for context_parser! *)
      fun parse_bool_config' name cfg =
           (Args.$$$ name #>> K (cfg,true))
        || (Args.$$$ ("no_"^name) #>> K (cfg,false))  
  
      fun parse_paren_list' p = Scan.optional (Args.parens (Parse.enum1 "," p)) []
  
      fun apply_configs l ctxt = fold (fn (cfg,v) => fn ctxt => Config.put cfg v ctxt) l ctxt
      
      fun lambda_tuple [] t = t
        | lambda_tuple (@{mpat "(?a,?b)"}::l) t = let
            val body = lambda_tuple (a::b::l) t
          in
            @{mk_term "case_prod ?body"}
          end
        | lambda_tuple (x::l) t = lambda x (lambda_tuple l t)
  
      fun get_tuple_inst ctxt (iname,T) = let
        val (argTs,T) = strip_type T
  
        fun cr (Type (@{type_name prod},[T1,T2])) ctxt = let
              val (x1,ctxt) = cr T1 ctxt
              val (x2,ctxt) = cr T2 ctxt
            in
              (HOLogic.mk_prod (x1,x2), ctxt)
            end
          | cr T ctxt = let
              val (name, ctxt) = yield_singleton Variable.variant_fixes "x" ctxt
            in
              (Free (name,T),ctxt)
            end
  
        val ctxt = Variable.set_body false ctxt (* Prevent generation of skolem-names *)

        val (args,ctxt) = fold_map cr argTs ctxt
        fun fl (@{mpat "(?x,?y)"}) = fl x @ fl y
          | fl t = [t]
  
        val fargs = flat (map fl args)
        val fTs = map fastype_of fargs
  
        val v = Var (iname,fTs ---> T)
        val v = list_comb (v,fargs)
        val v = lambda_tuple args v
      in 
        Thm.cterm_of ctxt v
      end
  
      fun instantiate_tuples ctxt inTs = let
        val inst = inTs ~~ map (get_tuple_inst ctxt) inTs
      in
        Thm.instantiate ([],inst)
      end
  
      val _ = COND'
  
      fun instantiate_tuples_from_term_tac ctxt t st = let
        val vars = Term.add_vars t []
      in
        PRIMITIVE (instantiate_tuples ctxt vars) st
      end
  
      fun instantiate_tuples_subgoal_tac ctxt = WITH_subgoal (fn t => K (instantiate_tuples_from_term_tac ctxt t))

  end

  structure Basic_Refine_Util: BASIC_REFINE_UTIL = Refine_Util
  open Basic_Refine_Util

\<close>

attribute_setup zero_var_indexes = \<open>
  Scan.succeed (Thm.rule_attribute [] (K Drule.zero_var_indexes))
\<close> "Set variable indexes to zero, renaming to avoid clashes"

end
