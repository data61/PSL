
section \<open>Circus syntax\<close>

theory Circus_Syntax
imports Denotational_Semantics
keywords "alphabet" "state" "channel" "nameset" "chanset" "schema" "action" and
  "circus_process" :: thy_defn
begin

abbreviation list_select::"['r \<Rightarrow> 'a list] \<Rightarrow> ('r \<Rightarrow> 'a)" where
"list_select Sel \<equiv> hd o Sel"

abbreviation list_update::"[('a list \<Rightarrow> 'a list) \<Rightarrow> 'r \<Rightarrow> 'r]
                         \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'r \<Rightarrow> 'r" where
"list_update Upd \<equiv> \<lambda> e. Upd (\<lambda> l. (e (hd l))#(tl l))"

abbreviation list_update_const::"[('a list \<Rightarrow> 'a list) \<Rightarrow> 'r \<Rightarrow> 'r]
                                \<Rightarrow> 'a \<Rightarrow> 'r relation" where
"list_update_const Upd \<equiv> \<lambda> e. \<lambda> (A, A'). A' = Upd (\<lambda> l. e#(tl l)) A"

abbreviation update_const::"[('a \<Rightarrow> 'a) \<Rightarrow> 'r \<Rightarrow> 'r]
                                \<Rightarrow> 'a \<Rightarrow> 'r relation" where
"update_const Upd \<equiv> \<lambda> e. \<lambda> (A, A'). A' = Upd (\<lambda> _. e) A"

syntax
  "_synt_assign" :: "id \<Rightarrow> 'a \<Rightarrow> 'b relation"  ("_ := _")


ML \<open>
structure VARs_Data = Proof_Data
(
  type T = {State_vars: string list, Alpha_vars: string list}
  fun init _ : T = {State_vars = [], Alpha_vars = []}
)
\<close>

nonterminal circus_action and circus_schema

syntax
  "_circus_action" :: "'a => circus_action"  ("_")   (* FIXME unused!? *)
  "_circus_schema" :: "'a => circus_schema"  ("_")

parse_translation \<open>
  let
    fun antiquote_tr ctxt =
      let
        val {State_vars=sv, Alpha_vars=av} = VARs_Data.get ctxt

        fun get_selector x =
          let val c = Consts.intern (Proof_Context.consts_of ctxt) x
          in
                if member (=) av x then SOME (Const ("Circus_Syntax.list_select", dummyT) $ (Syntax.const c)) else
                  if member (=) sv x then SOME (Syntax.const c) else NONE end;

        fun get_update x =
          let val c = Consts.intern (Proof_Context.consts_of ctxt) x
          in
                if member (=) av x then SOME (Const ("Circus_Syntax.list_update_const", dummyT) $ (Syntax.const (c^Record.updateN))) else
                  if member (=) sv x then SOME (Const ("Circus_Syntax.update_const", dummyT) $ (Syntax.const (c^Record.updateN))) else NONE end;

        fun print text =  (fn x => let val _ = writeln text; in x end);

        val rel_op_type = @{typ "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<times> 'c \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'c \<Rightarrow> bool"};

        fun tr i (t as Free (x, _)) =
              (case get_selector x of
                SOME c =>  c $ Bound (i + 1)
              | NONE =>
                  (case try (unsuffix "'") x of
                    SOME y =>
                      (case get_selector y of SOME c => c $ Bound i | NONE => t)
                  | NONE => t))
          | tr i (t as (Const ("_synt_assign", _) $ Free (x, _) $ r)) =
              (case get_update x of
                SOME c =>  c $ (tr i r) $ (Const ("Product_Type.Pair", dummyT) $ Bound (i + 1) $ Bound i)
              | NONE => t)
(*          | tr i (t as (Const (c, rel_op_type) $ l $ r)) = print c
              ((Syntax.const @{const_name case_prod} $
                Abs ("B", dummyT, Abs ("B'", dummyT, Const (c, rel_op_type)))) $ tr i l $ tr i r)
                  $ (Const ("Product_Type.Pair", dummyT) $ Bound (i + 1) $ Bound i)*)
          | tr i (t $ u) = tr i t $ tr i u
          | tr i (Abs (x, T, t)) = Abs (x, T, tr (i + 1) t)
          | tr _ a = a;
      in tr 0 end;

    fun quote_tr ctxt [t] =
          Syntax.const @{const_name case_prod} $
            Abs ("A", dummyT, Abs ("A'", dummyT, antiquote_tr ctxt (Term.incr_boundvars 2 t)))
      | quote_tr _ ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_circus_schema"}, quote_tr)] end
\<close>


ML \<open>
fun get_fields (SOME ({fields, parent, ...}: Record.info)) thy =
  (case parent of
       SOME ( _,y) => fields @ get_fields (Record.get_info thy y) thy
     | NONE => fields)
  | get_fields NONE _ = []


val dummy = Term.dummy_pattern dummyT;
fun mk_eq (l, r) = HOLogic.Trueprop $ ((HOLogic.eq_const dummyT) $ l $ r)

fun add_datatype (params, binding) constr_specs thy =
  let
    val ([dt_name], thy') = thy
      |> BNF_LFP_Compat.add_datatype [BNF_LFP_Compat.Keep_Nesting]
        [((binding, params, NoSyn), constr_specs)];
    val constr_names =
      map fst (the_single (map (#3 o snd)
        (#descr (BNF_LFP_Compat.the_info thy' [BNF_LFP_Compat.Keep_Nesting] dt_name))));
    fun constr (c, Ts) = (Const (c, dummyT), length Ts);
    val constrs = map #1 constr_specs ~~ map constr (constr_names ~~ map #2 constr_specs);
   in ((dt_name, constrs), thy') end;

fun define_channels (params, binding) typesyn channels thy =
  case typesyn of
  NONE =>
  let
    val dt_binding = Binding.suffix_name "_channels" binding;

    val constr_specs = map (fn (b, opt_T) => (b, the_list opt_T, NoSyn)) channels;
    val ((dt_name, constrs), thy1) =
      add_datatype (params, dt_binding) constr_specs thy;

    val T = Type (dt_name, []);

    val fun_name = "ev_eq" ^ "_" ^ Long_Name.base_name dt_name;

    val ev_equ = Free (fun_name, T --> T --> HOLogic.boolT);

    val eqs = map_product (fn (_, (c, n)) => (fn (_, (c1,n1)) =>
      let
        val t = Term.list_comb (c, replicate n dummy);
        val t1 = Term.list_comb (c1, replicate n1 dummy);
      in (if c = c1 then mk_eq ((ev_equ $ t $ t1), @{term True}) else mk_eq ((ev_equ $ t $ t1), @{term False})) end)) constrs constrs;

  fun case_tac x ctxt =
    resolve_tac ctxt [Thm.instantiate' [] [SOME x]
      (#exhaust (BNF_LFP_Compat.the_info (Proof_Context.theory_of ctxt) [BNF_LFP_Compat.Keep_Nesting] dt_name))];

  fun proof ctxt = (Class.intro_classes_tac ctxt [] THEN
                      Subgoal.FOCUS (fn {context = ctxt', params = [(_, x)], ...} =>
                                        (case_tac x ctxt') 1
                                            THEN auto_tac ctxt') ctxt 1 THEN
                      Subgoal.FOCUS (fn {context = ctxt', params = [(_, x), (_, y)], ...} =>
                                        ((case_tac x ctxt') THEN_ALL_NEW (case_tac y ctxt')) 1
                                            THEN auto_tac ctxt') ctxt 1);

 val thy2 =
      thy1
      |> Class.instantiation ([dt_name], params, @{sort ev_eq})
      |> Local_Theory.subtarget (Function_Fun.add_fun [(Binding.name fun_name, NONE, NoSyn)]
           (map (fn t => ((Binding.empty_atts, t), [], [])) eqs) Function_Fun.fun_config)
      |> Class.prove_instantiation_exit (fn ctxt => proof ctxt);
  in
    ((dt_name, constrs), thy2)
  end
  | (SOME typn) =>
  let
    val dt_binding = Binding.suffix_name "_channels" binding;

    val (dt_name, thy1) =
            thy
            |> Named_Target.theory_init
            |> (fn ctxt => Typedecl.abbrev (dt_binding, map fst params, NoSyn) (Proof_Context.read_typ ctxt typn) ctxt);

   val thy2 = thy1 |> Local_Theory.exit_global;
  in
    ((dt_name, []), thy2)
  end;

fun define_chanset binding channel_constrs (name, chans) thy  =
  let
    val constrs =
       filter (fn (b, _) => exists (fn a => a = Binding.name_of b) chans) channel_constrs;
    val bad_chans =
      filter_out (fn a => exists (fn (b, _) => a = Binding.name_of b) channel_constrs) chans;
    val _ = null bad_chans orelse
      error ("Bad elements " ^ commas_quote bad_chans ^ " in chanset: " ^ quote (Binding.print name));
    val base_name = Binding.name_of name;
    val cs = map (fn (_, (c, n)) => Term.list_comb (c, replicate n (Const (@{const_name undefined}, dummyT)))) constrs;
    val chanset_eq = mk_eq ((Free (base_name, dummyT)), (HOLogic.mk_set dummyT cs));
  in
      thy
      |> Named_Target.theory_init
      |> Specification.definition (SOME (Binding.qualify_name true binding base_name, NONE, NoSyn))
          [] [] (Binding.empty_atts, chanset_eq)
      |> snd |> Local_Theory.exit_global
  end;

fun define_nameset binding (rec_binding, alphabet) (ns_binding, names) thy  =
  let
    val all_selectors = get_fields (Record.get_info thy (Sign.full_name thy rec_binding)) thy
    val bad_names =
      filter_out (fn a => exists (fn (b, _) => String.isSuffix a b) all_selectors) names;
    val _ = null bad_names orelse
      error ("Bad elements " ^ commas_quote bad_names ^ " in nameset: " ^ quote (Binding.print ns_binding));
    val selectors =
       filter (fn (b, _) => exists (fn a => String.isSuffix a b) names) all_selectors;
    val updates = map (fn x => (fst x, ((suffix Record.updateN) o fst) x)) selectors;
    val selectors' = map (fn x => (fst x, Const(fst x, dummyT))) selectors;
    val updates' = map (fn (x, y) => (x, Const(y, dummyT))) updates;
    val l =
       map (fn (b, _) => Binding.name_of b) alphabet;
    val formulas = map2 (fn (nx, x) =>
                           fn (ny, y) =>
                             if (exists (fn b => String.isSuffix b nx) l)
                             then Abs ("A", dummyT, (Const("Circus_Syntax.list_update", dummyT) $ x)
                                          $ (Abs ("_", dummyT, (Const("Circus_Syntax.list_select", dummyT) $ y) $ (Bound 1))))
                             else Abs ("A", dummyT, x $ (Abs ("_", dummyT, y $ (Bound 1))))) updates' selectors';
    val base_name = Binding.name_of ns_binding;
    fun comp [a] = a $ (Bound 1) $ (Bound 0)
      | comp (a::l) = a $ (Bound 1) $ (comp l);
    val nameset_eq = mk_eq ((Free (base_name, dummyT)), (Abs ("_", dummyT, (Abs ("_", dummyT, comp formulas)))));
  in
      thy
      |> Named_Target.theory_init
      |> Specification.definition (SOME (Binding.qualify_name true binding base_name, NONE, NoSyn))
          [] [] (Binding.empty_atts, nameset_eq)
      |> snd |> Local_Theory.exit_global
  end;


fun define_schema binding (ex_binding, expr) (alph_bind, alpha, state) thy =
  let
      val fields_names = (map (fn (x, T) => (Binding.name_of x, T)) (alpha @ state));
      val alpha' = (map (fn (x, T) => (Binding.name_of x, T)) alpha);
      val state' = (map (fn (x, T) => (Binding.name_of x, T)) state);
      val all_selectors = get_fields (Record.get_info thy (Sign.full_name thy alph_bind)) thy
      val base_name = Binding.name_of ex_binding;
      val ctxt = Proof_Context.init_global thy;
      val term =
        Syntax.read_term
          (ctxt
            |> VARs_Data.put ({State_vars=(map fst state'), Alpha_vars=(map fst alpha')})
            |> Config.put Syntax.root @{nonterminal circus_schema}) expr;
      val sc_eq = mk_eq ((Free (base_name, dummyT)), term);
  in
    thy
    |> Named_Target.theory_init
    |> Specification.definition (SOME (Binding.qualify_name true binding base_name, NONE, NoSyn))
        [] [] (Binding.empty_atts, sc_eq)
    |> snd
    |> Local_Theory.exit_global
  end;


fun define_action binding (ex_binding, expr) alph_bind chan_bind thy =
  let
    val base_name = Binding.name_of ex_binding;
    val ctxt = Proof_Context.init_global thy;
    val actT = "Circus_Actions.action";
    val action_eq =
      mk_eq
        ((Free (base_name,
          Type (actT, [(Proof_Context.read_type_name {proper=true, strict=false} ctxt (Sign.full_name thy chan_bind)),
            (Proof_Context.read_type_name {proper=true, strict=false} ctxt (Sign.full_name thy alph_bind))]))),
        (Syntax.parse_term ctxt expr));
  in
    thy
    |> Named_Target.theory_init
    |> Specification.definition (SOME (Binding.qualify_name true binding base_name, NONE, NoSyn))
        [] [] (Binding.empty_atts, action_eq)
    |> snd
    |> Local_Theory.exit_global
  end;



fun define_expr binding (alph_bind, alpha, state) chan_bind (ex_binding, (is_schema, expr)) =
  if is_schema then define_schema binding (ex_binding, expr) (alph_bind, alpha, state)
  else define_action binding (ex_binding, expr) alph_bind chan_bind;



fun prep_field prep_typ (b: binding, raw_T) ctxt =
  let
    val T = prep_typ ctxt raw_T;
    val ctxt' = Variable.declare_typ T ctxt;
  in ((b, T), ctxt') end;

fun prep_constr prep_typ (b: binding, raw_T) ctxt =
  let
    val T = Option.map (prep_typ ctxt) raw_T;
    val ctxt' = fold Variable.declare_typ (the_list T) ctxt;
  in ((b, T), ctxt') end;


fun gen_circus_process prep_constraint prep_typ
    (raw_params, binding) raw_alphabet raw_state (typesyn, raw_channels) namesets chansets
    exprs act thy =
  let
    val ctxt = Proof_Context.init_global thy;


    (* internalize arguments *)

    val params = map (prep_constraint ctxt) raw_params;
    val ctxt0 = fold (Variable.declare_typ o TFree) params ctxt;

    val (alphabet, ctxt1) = fold_map (prep_field prep_typ) raw_alphabet ctxt0;
    val (state, ctxt2) = fold_map (prep_field prep_typ) raw_state ctxt1;
    val (channels, ctxt3) = fold_map (prep_constr prep_typ) raw_channels ctxt2;

    val params' = map (Proof_Context.check_tfree ctxt3) params;


    (* type definitions *)

    val fields =
      map (fn (b, T) => (b, T, NoSyn)) (map (apsnd HOLogic.listT) alphabet @ state);

    val thy1 = thy
      |> not (null fields) ?
        Record.add_record {overloaded = false}
          (params', Binding.suffix_name "_alphabet" binding) NONE fields;
    val (channel_constrs, thy2) =
      if not (null channels) orelse is_some typesyn
      then apfst snd (define_channels (params', binding) typesyn channels thy1)
      else ([], thy1);
    val thy3 = thy2
      |> not (null chansets) ? fold (define_chanset binding channel_constrs) chansets
      |> not (null namesets) ?
        fold (define_nameset binding ((Binding.suffix_name "_alphabet" binding), alphabet)) namesets
      |> not (null exprs) ?
        fold (define_expr binding ((Binding.suffix_name "_alphabet" binding), alphabet, state)
          (Binding.suffix_name "_channels" binding)) exprs
      |> define_action binding (binding, act)
        (Binding.suffix_name "_alphabet" binding) (Binding.suffix_name "_channels" binding);
  in
    thy3
  end;

fun circus_process x = gen_circus_process (K I) Syntax.check_typ x;
fun circus_process_cmd x = gen_circus_process (apsnd o Typedecl.read_constraint) Syntax.read_typ x;


local

val fields =
  @{keyword "["} |-- Parse.enum1 "," (Parse.binding -- (@{keyword "::"} |-- Parse.!!! Parse.typ))
    --| @{keyword  "]"};

val constrs =
  (@{keyword  "["} |-- Parse.enum1 "," (Parse.binding -- Scan.option Parse.typ) --| @{keyword  "]"}) >> pair NONE
  || Parse.typ >> (fn b => (SOME b, []));

val names =
  @{keyword "["} |-- Parse.enum1 "," Parse.name --| @{keyword  "]"};

in

val _ =
  Outer_Syntax.command @{command_keyword circus_process} "Circus process specification"
    ((Parse.type_args_constrained -- Parse.binding --| @{keyword  "="}) --
      Scan.optional (@{keyword "alphabet"} |-- Parse.!!! (@{keyword  "="} |-- fields)) [] --
      Scan.optional (@{keyword "state"} |-- Parse.!!! (@{keyword  "="} |-- fields)) [] --
      Scan.optional (@{keyword "channel"} |-- Parse.!!! (@{keyword  "="} |-- constrs)) (NONE, []) --
      Scan.repeat (@{keyword "nameset"} |-- Parse.!!! ((Parse.binding --| @{keyword "="}) -- names)) --
      Scan.repeat (@{keyword "chanset"} |-- Parse.!!! ((Parse.binding --| @{keyword "="}) -- names)) --
      Scan.repeat ((@{keyword "schema"} |-- Parse.!!! ((Parse.binding --| @{keyword "="}) -- (Parse.term >> pair true))) ||
                   (@{keyword "action"} |-- Parse.!!! ((Parse.binding --| @{keyword "="}) -- (Parse.term >> pair false)))) --
      (Parse.where_ |-- Parse.!!! Parse.term)
        >> (fn (((((((a, b), c), d), e), f), g), h) =>
          Toplevel.theory (circus_process_cmd a b c d e f g h)));

end;
\<close>

end
