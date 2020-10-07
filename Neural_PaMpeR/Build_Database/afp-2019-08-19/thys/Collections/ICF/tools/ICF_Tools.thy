section \<open>General ML-level tools\<close>
theory ICF_Tools
imports Main
begin

lemma meta_same_imp_rule: "(\<lbrakk>PROP P; PROP P\<rbrakk> \<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow> PROP Q)"
  by rule
(* TODO: Replace by distinct_prems_rl *)

ML \<open>
  infix 0 ##;

  fun (f ## g) (a,b) = (f a, g b)

  signature ICF_TOOLS = sig
    (* Generic *)
    val gen_variant: (string -> bool) -> string -> string
    val map_option: ('a -> 'b) -> 'a option -> 'b option

    val parse_cpat: cterm context_parser

    val rename_cterm: (cterm * cterm) ->
      ((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list
    val renames_cterm: (cterm * cterm) -> bool

    val import_cterm: cterm -> Proof.context -> cterm * Proof.context
    val inst_meta_cong: Proof.context -> cterm -> thm

    (*
    val thms_from_main: string -> thm list
    val thm_from_main: string -> thm
    *)

    val sss_add: thm list -> Proof.context -> Proof.context

    val changed_conv: conv -> conv
    val repeat_top_sweep_conv: (Proof.context -> conv) -> Proof.context -> conv

    val rem_dup_prems: Proof.context -> thm -> thm

    (* Definition Theorems *)
    val dest_def_eq: term -> term * term
    val norm_def_thm: thm -> thm
    val dthm_lhs: thm -> term
    val dthm_rhs: thm -> term
    val dthm_params: thm -> term list
    val dthm_head: thm -> term

    val dt_lhs: term -> term
    val dt_rhs: term -> term
    val dt_params: term -> term list
    val dt_head: term -> term

    val chead_of: cterm -> cterm
    val chead_of_thm: thm -> cterm

    (* Simple definition: name\<equiv>term, fixes variables *)
    val define_simple: string -> term -> local_theory 
      -> ((term * thm) * local_theory)

    (* Wrapping stuff inside local theory context *)
    val wrap_lthy_result_global: (local_theory -> 'a * local_theory) ->
        (morphism -> 'a -> 'b) -> theory -> 'b * theory
    val wrap_lthy_global: (local_theory -> local_theory) -> theory -> theory
    val wrap_lthy_result_local: (local_theory -> 'a * local_theory) ->
        (morphism -> 'a -> 'b) -> local_theory -> 'b * local_theory
    val wrap_lthy_local: (local_theory -> local_theory) -> 
        local_theory -> local_theory

    (* Wrapped versions of simple definition *)
    val define_simple_global: string -> term -> theory 
      -> ((term * thm) * theory)
    val define_simple_local: string -> term -> local_theory 
      -> ((term * thm) * local_theory)

    (* Revert abbreviations matching pattern (TODO/FIXME: HACK) *)
    val revert_abbrevs: string -> theory -> theory

  end;

  structure ICF_Tools: ICF_TOOLS = struct
    fun gen_variant decl s = let
      fun search s = if not (decl s) then s else search (Symbol.bump_string s);
    in
      if not (decl s) then s 
      else search (Symbol.bump_init s)
    end;    


    val parse_cpat =
      Args.context --
        Scan.lift Args.embedded_inner_syntax >> (fn (ctxt, str) => 
          Proof_Context.read_term_pattern ctxt str
          |> Thm.cterm_of ctxt 
        );


    (* Renaming first-order match *)
    fun rename_cterm (ct1,ct2) = (
      Thm.first_order_match (ct2,ct1);
      Thm.first_order_match (ct1,ct2));

    val renames_cterm = can rename_cterm;

    fun import_cterm ct ctxt = let
      val (t', ctxt') = yield_singleton (Variable.import_terms true) 
        (Thm.term_of ct) ctxt;
      val ct' = Thm.cterm_of ctxt' t';
    in (ct', ctxt') end

  (* Get theorem by name, that is visible in HOL.Main. Moreover, the
    theory of this theorem will be HOL.Main, which is required to avoid
    non-trivial theory merges as they may occur when using thm-antiquotation.
    (cf. post 
      https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2012-August/msg00175.html 
    on Isabelle mailing list)
  *)(*
  fun thms_from_main name = let
    val xthmref = Facts.named name;
    val thy = @{theory Main};
    val name = Facts.name_of_ref xthmref
    |> Global_Theory.intern_fact thy;
    val name = case name of "_" => "Pure.asm_rl" | name => name;

    val fs = Global_Theory.facts_of thy;
    val thms = Facts.lookup (Context.Theory thy) fs name
    |> the |> #2 |> map (Thm.transfer thy);
  in thms end

  fun thm_from_main name = thms_from_main name |> Facts.the_single (name, Position.none)
*)
    (* Unfold with simpset 
    fun unfold_ss ss = let
      val simple_prover =
        SINGLE o (fn ss => ALLGOALS (resolve_tac (Raw_Simplifier.prems_of ss)));
    in Raw_Simplifier.rewrite_thm (true,false,false) simple_prover ss end;
    *)

    local
      fun sss_add_single thm ss = let
        val simps = Raw_Simplifier.dest_ss (simpset_of ss) |> #simps |> map #2;
        val ess = ss delsimps simps;
        val thm' = simplify ss thm;

        val new_simps = simps
          |> map (simplify 
              (ess addsimps [thm']));
        val ss' = ess addsimps (thm'::new_simps)
      in ss' end
    in
      val sss_add = fold sss_add_single
    end

    local
      open Conv;
    in
      fun changed_conv cnv = (fn (ct:cterm) => let
        val thm = cnv ct
      in
        if Thm.is_reflexive thm then 
          raise THM ("changed_conv: Not changed",~1,[thm])
        else thm
      end)

      fun repeat_top_sweep_conv cnv ctxt = 
        repeat_conv (changed_conv (top_sweep_conv cnv ctxt));
    end

    (* Remove duplicate premises (stable) *)
    fun rem_dup_prems ctxt thm = let
      val prems = Thm.prems_of thm;
      val perm = prems
      |> tag_list 0 
      |> map swap 
      |> Termtab.make_list
      |> Termtab.dest 
      |> map snd
      |> sort (int_ord o apply2 hd)
      |> flat;

      val thm' = Drule.rearrange_prems perm thm
        |> Conv.fconv_rule 
             (Raw_Simplifier.rewrite ctxt true @{thms meta_same_imp_rule});
    in thm' end;

    fun dest_def_eq (Const (@{const_name Pure.eq},_)$l$r) = (l,r)
    | dest_def_eq (Const (@{const_name HOL.Trueprop},_)
                    $(Const (@{const_name HOL.eq},_)$l$r)) = (l,r)
    | dest_def_eq t = raise TERM ("No definitional equation",[t]);

    fun norm_def_thm thm =
      case Thm.concl_of thm of
        (Const (@{const_name Pure.eq},_)$_$_) => thm
      | _ => thm RS eq_reflection;

    val dt_lhs = dest_def_eq #> fst;
    val dt_rhs = dest_def_eq #> snd;
    val dt_params = dt_lhs #> strip_comb #> snd;
    val dt_head = dt_lhs #> head_of;

    val dthm_lhs = Thm.concl_of #> dt_lhs;
    val dthm_rhs = Thm.concl_of #> dt_rhs;
    val dthm_params = Thm.concl_of #> dt_params;
    val dthm_head = Thm.concl_of #> dt_head;

    (* Head of function application (cterm) *)
    fun chead_of ct = case Thm.term_of ct of
      (_$_) => chead_of (Thm.dest_fun ct)
      | _ => ct;

    val chead_of_thm = norm_def_thm #> Thm.lhs_of #> chead_of;

    val meta_cong_rl = @{thm "eq_reflection"}
        OF @{thms "arg_cong"} OF @{thms "meta_eq_to_obj_eq"}

    fun inst_meta_cong ctxt ct = let
      val (ct, ctxt') = import_cterm ct ctxt;
      val mc_thm = meta_cong_rl;
      val fpat = mc_thm |> Thm.cprop_of |> Drule.strip_imp_concl 
        |> Thm.dest_arg1 |> chead_of;
      val inst = infer_instantiate ctxt [(#1 (dest_Var (Thm.term_of fpat)), ct)] mc_thm;
      val inst' = singleton (Variable.export ctxt' ctxt) inst;
    in inst' end


    (* Define name\<equiv>rhs, generate _def theorem. *)
    fun define_simple name rhs lthy = let 
      (* Import type variables *)
      val (rhs,lthy) = yield_singleton Variable.importT_terms rhs lthy;
      val ((ft,(_,def_thm)),lthy) 
        = Local_Theory.define ((Binding.name name,NoSyn),
         ((Binding.name (Thm.def_name name),[]),rhs)) lthy;
    in ((ft,def_thm),lthy) end;

    fun wrap_lthy_result_global f rmap thy = let
      val lthy = Named_Target.theory_init thy;
      val (r,lthy) = f lthy;
      val (r,thy) = Local_Theory.exit_result_global rmap (r,lthy);
    in
      (r,thy)
    end

    fun wrap_lthy_global f = wrap_lthy_result_global (pair () o f) (K I) #> #2;

    fun wrap_lthy_result_local f rmap lthy = let
      val (_, lthy) = Local_Theory.open_target lthy;
      val (r,lthy) = f lthy;
      val m = Local_Theory.target_morphism lthy;
      val lthy = Local_Theory.close_target lthy;
      val r = rmap m r;
    in
      (r,lthy)
    end

    fun wrap_lthy_local f = wrap_lthy_result_local (pair () o f) (K I) #> #2;



    (* Define name\<equiv>rhs, yielding constant *)
    fun define_simple_global name rhs thy = let
      val lthy = Named_Target.theory_init thy;
      val (r,lthy) = define_simple name rhs lthy;
      fun map_res m (t,thm) = (Morphism.term m t,Morphism.thm m thm);
      val (r,thy) = Local_Theory.exit_result_global (map_res) (r,lthy);
    in (r,thy) end;

    (* Define name\<equiv>rhs, yielding constant *)
    fun define_simple_local name rhs lthy = let
      val (_, lthy) = Local_Theory.open_target lthy;
      val (r,lthy) = define_simple name rhs lthy;
      val m = Local_Theory.target_morphism lthy;
      val lthy = Local_Theory.close_target lthy;
      fun map_res m (t,thm) = (Morphism.term m t,Morphism.thm m thm);
      val (r,lthy) = (map_res m r,lthy);
    in (r,lthy) end;

    fun map_option _ NONE = NONE
      | map_option f (SOME a) = SOME (f a);


    fun revert_abbrevs mpat thy = let
      val ctxt = Proof_Context.init_global thy;
      val match_prefix = if Long_Name.is_qualified mpat then mpat
        else Long_Name.qualify (Context.theory_name thy) mpat;
      val {const_space, constants, ...} = Sign.consts_of thy |> Consts.dest;
      val names = 
      Name_Space.extern_entries true ctxt const_space constants
      |> map_filter (fn
          ((name, _), (_, SOME _)) =>
            if Long_Name.qualifier name = match_prefix then SOME name else NONE
        | _ => NONE)
      val _ = if null names then 
        warning ("ICF_Tools.revert_abbrevs: No names with prefix: " 
          ^ match_prefix) 
      else ();
    in fold (Sign.revert_abbrev "") names thy end


  end;

\<close>

attribute_setup rem_dup_prems = \<open>
  Scan.succeed (Thm.rule_attribute [] (ICF_Tools.rem_dup_prems o Context.proof_of))
\<close> "Remove duplicate premises"

method_setup dup_subgoals = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (PRIMITIVE (ICF_Tools.rem_dup_prems ctxt)))
\<close> "Remove duplicate subgoals"


end
