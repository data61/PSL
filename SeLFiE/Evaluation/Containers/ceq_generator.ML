(* Author:  René Thiemann, UIBK *)
(* This generator was written as part of the IsaFoR/CeTA formalization. *)
signature CEQ_GENERATOR =
sig

  (* creates a conditional equality by using the equality-functions of the Equality_Generator,
     also is_ceq (a1,..,an)ty = is_ceq a1 \<and> ... \<and> is_ceq an
     is generated. *) 
  val ceq_instance_via_equality : string -> theory -> theory
    
  (* creates a conditional equality by implementing it as "Some (op =)". 
     Hence, "is_ceq ty" will always be satisfied. *)
  val ceq_instance_via_eq : string -> theory -> theory
  
  (* derives a trivial instance (None) for class ceq *)
  val derive_no_ceq : string -> theory -> theory

end

structure Ceq_Generator : CEQ_GENERATOR =
struct

open Generator_Aux
open Containers_Generator

val ceqS = @{sort ceq};
val ceqN = @{const_name ceq};
fun eqT T = T --> T --> @{typ bool};
fun ceqT T = Type (@{type_name option}, [eqT T])
fun ceq_const T = Const (ceqN, T);

val generator_type = Equality_Generator.BNF

fun dest_comp ctxt tname =
  (case Equality_Generator.get_info ctxt tname of
    SOME {equality = e, equality_thm = e_thm, ...} =>
      let
        val Ts = fastype_of e |> strip_type |> fst |> `((fn x => x - 2) o length) |> uncurry take
      in (e, e_thm, Ts) end
  | NONE => error ("no equality info for type " ^ quote tname))

fun mk_ID_ceq eq_var = 
  let
    val ty = fastype_of eq_var
    val oty = Type (@{type_name option}, [ty])
    val ceq = Const (ceqN, oty)
    val ID_cc = Const (@{const_name ID}, oty --> oty) $ ceq
  in 
    ID_cc
  end

fun mk_ceq_rhs c [] = mk_Some c
  | mk_ceq_rhs c (T :: Ts) = 
      let
        val eq = ceq_const T
        val ideq = mk_ID_ceq eq
        val tname = T |> binder_types |> hd |> dest_TVar |> fst |> fst 
        val arg_comp = Free ("eq_" ^ tname, T) 
        val caseT = Const (@{const_name case_option}, dummyT) 
          $ Const (@{const_name None}, dummyT)
          $ lambda arg_comp (mk_ceq_rhs (c $ arg_comp) Ts)
          $ ideq
      in 
        caseT
      end

  
fun mk_ceq_def T rhs =
  Logic.mk_equals (Const (ceqN, ceqT T), rhs)

fun ceq_tac ctxt tname Ts = 
  let
    val (_, c_thm, _) = dest_comp ctxt tname
  in
    unfold_tac ctxt @{thms ID_def id_def} 
    THEN REPEAT_DETERM_N (length Ts) (
      Splitter.split_asm_tac ctxt @{thms option.splits} 1 THEN
      unfold_tac ctxt @{thms option.simps}) 
    THEN unfold_tac ctxt @{thms option.simps} 
    THEN resolve_tac ctxt @{thms equality_subst} 1 THEN assume_tac ctxt 1 
    THEN REPEAT_DETERM (dresolve_tac ctxt @{thms ceq_equality} 1) 
    THEN (resolve_tac ctxt [c_thm] THEN_ALL_NEW assume_tac ctxt) 1
  end
    
fun ceq_instance_via_equality tname thy =
  let
    val thy = Named_Target.theory_map (Equality_Generator.ensure_info generator_type tname) thy
    val _ = writeln ("deriving \"ceq\" instance for type " ^ quote tname)

    val (main_ty, xs) = typ_and_vs_of_typname thy tname ceqS
    val (Ts, (eq_thm, lthy)) =
      Class.instantiation ([tname], xs, ceqS) thy
      |> (fn ctxt =>
        let
          val (c, _, Ts) = dest_comp ctxt tname
          val typ_mapping = all_tys c (map TFree xs)
          val eq_def = mk_ceq_def dummyT (mk_ceq_rhs c Ts) |> typ_mapping
        in
          (Ts, define_overloaded_generic
           ((Binding.name ("ceq_" ^ Long_Name.base_name tname ^ "_def"),
            @{attributes [code]}),
            eq_def) ctxt)
        end)
    val thy = Class.prove_instantiation_exit (fn ctxt =>
      Class.intro_classes_tac ctxt []
      THEN unfold_tac ctxt [eq_thm]
      THEN resolve_tac ctxt @{thms equality_imp_eq} 1
      THEN ceq_tac ctxt tname Ts) lthy
    val info = Equality_Generator.get_info (Named_Target.theory_init thy) tname |> the
    val used = #used_positions info
    
    (* is_ceq (a1,..,an)ty = (is_ceq a1 \<and> ... ) -thm *)
    fun mk_is_ceq ty = mk_is_c_dots ty @{const_name is_ceq}
    val main_is_ceq = mk_is_ceq main_ty
    val param_tys = dest_Type main_ty |> snd   
    val filtered_tys = used ~~ param_tys |> filter fst |> map snd
    val param_is_ceq = map mk_is_ceq filtered_tys
    val is_ceq_thm_trm = HOLogic.mk_Trueprop (case param_is_ceq of 
        [] => main_is_ceq
      | _ => HOLogic.mk_eq (main_is_ceq,HOLogic_list_conj param_is_ceq))
    val is_ceq_thm = Goal.prove (Proof_Context.init_global thy) [] [] is_ceq_thm_trm 
      (fn {context = ctxt, prems = _} => 
        simp_tac (Splitter.add_split @{thm option.split} ctxt 
          addsimps (eq_thm :: @{thms ID_Some ID_None is_ceq_def})
        ) 1
      )
    val thy = register_is_c_dots_lemma @{const_name is_ceq} (Long_Name.base_name tname) 
      is_ceq_thm thy
  in
    thy
  end

fun mk_some_equality ty = mk_Some (Const (@{const_name "HOL.eq"}, eqT ty))

fun ceq_instance_via_eq tname thy = 
  let
    val base_name = Long_Name.base_name tname
    val _ = writeln ("deriving \"ceq\" instance for type " ^ 
      quote tname ^ " via \"=\"")
    val (ty,vs) = typ_and_vs_of_typname thy tname @{sort type}
    val ceq_rhs = mk_some_equality ty
    val ceq_ty = Term.fastype_of ceq_rhs
    val ceq_def = mk_def ceq_ty ceqN ceq_rhs
    val (ceq_thm,lthy) = Class.instantiation ([tname],vs,ceqS) thy
      |> (define_overloaded ("ceq_" ^ base_name ^ "_def", ceq_def))
     
    val thy = Class.prove_instantiation_exit (fn ctxt => 
      Class.intro_classes_tac ctxt [] 
      THEN unfold_tac ctxt [ceq_thm]
      THEN unfold_tac ctxt @{thms option.simps prod.simps}
      THEN resolve_tac ctxt @{thms sym} 1 THEN assume_tac ctxt 1
      ) lthy
    val thy = derive_is_c_dots_lemma ty @{const_name is_ceq} 
      [ceq_thm, @{thm is_ceq_def}] base_name thy

  in thy end

fun mk_none_ceq ty = Const (@{const_name None}, Type (@{type_name option}, [eqT ty]))

val derive_no_ceq = derive_none ceqN ceqS mk_none_ceq
  
fun ceq_instance tname param thy =
  let
    val _ = is_class_instance thy tname ceqS
      andalso error ("type " ^ quote tname ^ " is already an instance of class \"ceq\"")
  in
    if param = "" then ceq_instance_via_equality tname thy
    else if param = "no" then derive_no_ceq tname thy
    else if param = "eq" then ceq_instance_via_eq tname thy 
    else error "unknown parameter, supported are (no parameter), \"eq\", and \"no\"" 
  end

val _ = Theory.setup
 (Derive_Manager.register_derive "ceq" 
    "generate a conditional equality function; options are (), (no), and (eq)" ceq_instance)

end
