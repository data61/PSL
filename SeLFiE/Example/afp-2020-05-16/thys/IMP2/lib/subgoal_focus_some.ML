(*
  Generalized version of Subgoal.FOCUS, where the premises to be be focused 
    on can be selected by a filter function. This generalizes the 
    do_prems from bool to Proof.context -> cterm -> bool

  Author: Peter Lammich. Derived from subgoal_focus.ML.  
*)

signature SUBGOAL_FOCUS_SOME = sig
  type focus =
   {context: Proof.context, params: (string * cterm) list, prems: thm list, asms: (bool * cterm) list,
    concl: cterm, schematics: ((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list}

  type prem_filter = Proof.context -> cterm -> bool  
    
  val focus_params: Proof.context -> int -> binding list option -> thm -> focus * thm
  val focus_params_fixed: Proof.context -> int -> binding list option -> thm -> focus * thm
  val focus_prems: Proof.context -> int -> binding list option -> thm -> focus * thm
  val focus: Proof.context -> int -> binding list option -> thm -> focus * thm
  val focus_some_prems: prem_filter -> Proof.context -> int -> binding list option -> thm -> focus * thm
  
  val retrofit: Proof.context -> Proof.context -> (string * cterm) list -> (bool * cterm) list ->
    int -> thm -> thm -> thm Seq.seq
  
  val FOCUS_PARAMS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PARAMS_FIXED: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_PREMS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS: (focus -> tactic) -> Proof.context -> int -> tactic
  val FOCUS_SOME_PREMS: prem_filter -> (focus -> tactic) -> Proof.context -> int -> tactic
  
end


structure Subgoal_Focus_Some : SUBGOAL_FOCUS_SOME = struct

  type focus =
   {context: Proof.context, params: (string * cterm) list, prems: thm list, asms: (bool * cterm) list,
    concl: cterm, schematics: ((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list}

  type prem_filter = Proof.context -> cterm -> bool  
    

fun partition P l = (filter P l, filter_out P l)
fun invert_perm l = tag_list 0 l |> map swap |> order_list

fun gen_focus (do_prems, do_concl) ctxt i bindings raw_st =
  let
    val st = raw_st
      |> Thm.transfer (Proof_Context.theory_of ctxt)
      |> Raw_Simplifier.norm_hhf_protect ctxt;
    val ((schematic_types, [st']), ctxt1) = Variable.importT [st] ctxt;
    val ((params, goal), ctxt2) = Variable.focus_cterm bindings (Thm.cprem_of st' i) ctxt1;

    val (asms, concl) = (Drule.strip_imp_prems goal, Drule.strip_imp_concl goal)
    val asms = map (`(do_prems ctxt2)) asms
    val fasms = filter fst asms |> map snd
    val nasms = filter_out fst asms |> map snd
    
    val concl = Drule.list_implies (nasms, concl)
    
    val text = fasms @ (if do_concl then [concl] else []);

    val (inst, ctxt3) = Variable.import_inst true (map Thm.term_of text) ctxt2;
    val schematic_terms = map (apsnd (Thm.cterm_of ctxt3)) (#2 inst);

    val schematics = (schematic_types, schematic_terms);
    val asms' = map (apsnd (Thm.instantiate_cterm schematics)) asms;
    val fasms' = filter fst asms' |> map snd
    val concl' = Thm.instantiate_cterm schematics concl;
    val (prems, context) = Assumption.add_assumes fasms' ctxt3;
  in
    ({context = context, params = params, prems = prems,
      asms = asms', concl = concl', schematics = schematics}, Goal.init concl')
  end;

  val focus_params = gen_focus (K (K false), false);
  val focus_params_fixed = gen_focus (K (K false), true);
  val focus_prems = gen_focus (K (K true), false);
  val focus = gen_focus (K (K true), true);
  fun focus_some_prems flt = gen_focus (flt,false)

  
  
(*
     B [?'b, ?y]
  ----------------
  B ['b, y params]
*)
fun lift_import idx params th ctxt =
  let
    val ((_, [th']), ctxt') = Variable.importT [th] ctxt;

    val Ts = map Thm.typ_of_cterm params;
    val ts = map Thm.term_of params;

    val prop = Thm.full_prop_of th';
    val concl_vars = Term.add_vars (Logic.strip_imp_concl prop) [];
    val vars = rev (Term.add_vars prop []);
    val (ys, ctxt'') = Variable.variant_fixes (map (Name.clean o #1 o #1) vars) ctxt';

    fun var_inst v y =
      let
        val ((x, i), T) = v;
        val (U, args) =
          if member (op =) concl_vars v then (T, [])
          else (Ts ---> T, ts);
        val u = Free (y, U);
        in ((Var v, list_comb (u, args)), (u, Var ((x, i + idx), U))) end;
    val (inst1, inst2) =
      split_list (map (apply2 (apply2 (Thm.cterm_of ctxt))) (map2 var_inst vars ys));

    val th'' = Thm.instantiate ([], map (apfst (Term.dest_Var o Thm.term_of)) inst1) th';
  in ((inst2, th''), ctxt'') end;
  
  
(*
       [x, A x]
          :
       B x ==> C
  ------------------
  [!!x. A x ==> B x]
          :
          C
*)
fun lift_subgoals ctxt params asms th =
  let
    fun lift ct = fold_rev (Thm.all_name ctxt) params (Drule.list_implies (asms, ct));
    val unlift =
      fold (Thm.elim_implies o Thm.assume) asms o
      Drule.forall_elim_list (map #2 params) o Thm.assume;
    val subgoals = map lift (Drule.strip_imp_prems (Thm.cprop_of th));
    val th' = fold (Thm.elim_implies o unlift) subgoals th;
  in (subgoals, th') end;

fun retrofit ctxt1 ctxt0 params all_asms i st1 st0 =
  let
    val asms = filter fst all_asms |> map snd
    
    val perm = tag_list 0 all_asms |> partition (fst o snd) |> op @ |> map fst
    val perm = invert_perm perm
    
    val idx = Thm.maxidx_of st0 + 1;
    val ps = map #2 params;
    val ((subgoal_inst, st2), ctxt2) = lift_import idx ps st1 ctxt1;
    val (subgoals, st3) = lift_subgoals ctxt2 params asms st2;
        
    val result = st3
      |> Goal.conclude 
      |> Drule.implies_intr_list asms
      |> Drule.rearrange_prems perm
      |> Drule.forall_intr_list ps
      |> Drule.implies_intr_list subgoals
      |> fold_rev (Thm.forall_intr o #1) subgoal_inst
      |> fold (Thm.forall_elim o #2) subgoal_inst
      |> Thm.adjust_maxidx_thm idx
      |> singleton (Variable.export ctxt2 ctxt0);
      
  in
    Thm.bicompose (SOME ctxt0) {flatten = true, match = false, incremented = false}
      (false, result, Thm.nprems_of st1) i st0
  end;
  
  
  

fun GEN_FOCUS flags tac ctxt i st =
  if Thm.nprems_of st < i then Seq.empty
  else
    let val (args as {context = ctxt', params, asms, ...}, st') =
      gen_focus flags (ctxt |> Variable.set_bound_focus true) i NONE st;
    in Seq.lifts (retrofit ctxt' ctxt params asms i) (tac args st') st end;

val FOCUS_PARAMS = GEN_FOCUS (K (K false), false);
val FOCUS_PARAMS_FIXED = GEN_FOCUS (K (K false), true);
val FOCUS_PREMS = GEN_FOCUS (K (K true), false);
val FOCUS = GEN_FOCUS (K (K true), true);
fun FOCUS_SOME_PREMS flt = GEN_FOCUS (flt, true);

end


