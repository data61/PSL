open Derive_Util

signature DERIVE_LAWS =
sig
  (* prove the iso theorem*)
  val prove_isomorphism : type_info -> Proof.context -> thm option * Proof.context
  val prove_instance_tac : typ -> class_info -> instance_info -> type_info -> Proof.context -> tactic
  val prove_equivalence_law : class_info -> instance_info -> Proof.context -> thm
  val prove_combinator_instance : (thm list list -> local_theory -> Proof.context) -> local_theory -> Proof.state
end

structure Derive_Laws : DERIVE_LAWS =
struct

fun get_class_info thy classname = Symtab.lookup (Class_Data.get thy) classname

fun prove_isomorphism type_info lthy =
let
  val tname_short = Long_Name.base_name (#tname type_info)
  val from_info = the (#from_info (#rep_info type_info))
  val to_info = the (#to_info (#rep_info type_info))

  val from_f = hd (#fs from_info)
  val to_f = hd (#fs to_info)

  val from_induct = hd (the (#inducts from_info))
  val to_induct = hd (the (#inducts to_info))

  val iso_thm =
  HOLogic.mk_Trueprop (Const (\<^const_name>\<open>Derive.iso\<close>, dummyT) $ from_f $ to_f)
    |> Syntax.check_term lthy
  val induct_tac_to = (Induct_Tacs.induct_tac lthy [[SOME "b"]] (SOME [to_induct]) 2)
  val induct_tac_from = (Induct_Tacs.induct_tac lthy [[SOME "a"]] (SOME [from_induct]) 1)

  val iso_thm_proved = Goal.prove lthy [] [] iso_thm
                        (fn _ => (resolve_tac lthy [@{thm Derive.iso_intro}] 1) THEN
                                 induct_tac_to THEN induct_tac_from THEN
                                 (ALLGOALS (asm_full_simp_tac lthy)))

  val ((_,thms),lthy') = Local_Theory.note ((Binding.name ("conversion_iso_" ^ tname_short),[]), [iso_thm_proved]) lthy
  val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy')
  val thm = singleton (Proof_Context.export lthy' ctxt_thy) (hd thms)
in
  (SOME thm, lthy')
end

fun prove_equivalence_law cl_info inst_info ctxt =
let
  val class = #class cl_info
  val classname = #classname cl_info
  val class_law = the (#class_law cl_info)
  val op_defs = #defs inst_info
  val axioms = the (#axioms cl_info)
  val axioms_def = the_list (#axioms_def cl_info) 
  val class_def = the (#class_def cl_info)
  
  val ops_raw = map (Thm.full_prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst #> strip_comb #> fst) op_defs
  val ops = map (dest_Const #> apsnd (K dummyT) #> Const) ops_raw
  val class_law_const = Thm.full_prop_of class_law |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst |> strip_comb |> fst
  val class_law_const_dummy = dest_Const class_law_const |> apsnd (K dummyT) |> Const
  val axioms_thms = map (Local_Defs.unfold ctxt (class_def :: axioms_def)) axioms
  val superclasses = get_superclasses class classname (Proof_Context.theory_of ctxt)
  val superclass_laws = map (get_class_info (Proof_Context.theory_of ctxt) #> the #> #equivalence_thm #> the) superclasses

  val t = list_comb (class_law_const_dummy,ops) |> HOLogic.mk_Trueprop |> Syntax.check_term ctxt
in
  Goal.prove ctxt [] [] t
  (fn _ => (Local_Defs.unfold_tac ctxt [class_law])
           THEN (HEADGOAL (Method.insert_tac ctxt (axioms_thms@superclass_laws)))
           THEN (HEADGOAL (asm_full_simp_tac ctxt)))
end  

fun prove_instance_tac T cl_info inst_info ty_info ctxt =
let
  val transfer_thms = the (#transfer_law cl_info) |> map snd |> flat
  val iso_thm = the (#iso_thm ty_info)
  val ops = map (Thm.full_prop_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq #> fst #> strip_comb #> fst) (#defs inst_info)
  val op_defs = #defs inst_info
  val class_law = the (#class_law cl_info)
  val equivalence_thm = the (#equivalence_thm cl_info)

  val class_law_const = Thm.full_prop_of class_law |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst |> strip_comb |> fst

  val ops = map (dest_Const #> apsnd (K dummyT) #> Const) ops
  val class_law_const_dummy = dest_Const class_law_const |> apsnd (K dummyT) |> Const

  val class_law_inst =
    HOLogic.mk_Trueprop (list_comb (class_law_const_dummy, ops))
    |> singleton (Type_Infer_Context.infer_types ctxt)
    |> (fn t => subst_TVars ([(Term.add_tvar_names t [] |> hd,T)]) t )

  val transfer_thm_inst = (hd transfer_thms) OF [iso_thm,equivalence_thm]
  
  val class_law_inst_proved = Goal.prove ctxt [] [] class_law_inst
                              (fn _ => (Local_Defs.unfold_tac ctxt op_defs)
                                       THEN (Proof_Context.fact_tac ctxt [transfer_thm_inst] 1))

  val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of ctxt)
  val class_law_inst_def = singleton (Proof_Context.export ctxt ctxt_thy) class_law_inst_proved
  val class_law_unfolded = Local_Defs.unfold ctxt [class_law] class_law_inst_def

  val class_tac = Class.intro_classes_tac ctxt []
                  THEN (ALLGOALS (Method.insert_tac ctxt [class_law_unfolded]))
                  THEN (ALLGOALS (blast_tac ctxt))
in
  class_tac
end

fun prove_combinator_instance after_qed lthy =
  let
    fun class_tac thms ctxt = Class.intro_classes_tac ctxt []
                  THEN (ALLGOALS (Method.insert_tac ctxt thms))
                  THEN (ALLGOALS (blast_tac ctxt))
    fun prove_class_laws_manually st ctxt =
      let
        val thm = #goal (Proof.simple_goal st)
        val goal = (Class.intro_classes_tac ctxt []) thm |> Seq.hd
        val goals = Thm.prems_of goal
        val goals_formatted = (map single (goals ~~ (replicate (length goals) [])))
        fun prove_class thms = 
          let
            val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of ctxt)
            val thms' = (Proof_Context.export ctxt ctxt_thy) (flat thms)
          in
            Class.prove_instantiation_exit (class_tac thms') ctxt
          end
        fun after_qed' thms _ =  prove_class thms |> Named_Target.theory_init |> after_qed []
        val st' = Proof.theorem NONE after_qed' goals_formatted ctxt 
      in
        st'
      end
    
    val st = Class.instantiation_instance I lthy
  in
    prove_class_laws_manually st lthy
  end


end