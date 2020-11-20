(* Author:  René Thiemann, UIBK *)
(* This generator was written as part of the IsaFoR/CeTA formalization. *)
signature CCOMPARE_GENERATOR =
sig

  (* creates a conditional comparator by using the comparator of the Comparator_Generator,
     also is_ccompare (a1,..,an)ty = is_ccompare a1 \<and> ... \<and> is_ccompare an
     is generated. *) 
  val ccompare_instance_via_comparator : string -> theory -> theory
    
  (* creates a conditional comparator by demanding that the type is already a member of class compare. 
     Hence, "is_ccompare ty" will always be satisfied. *)
  val ccompare_instance_via_compare : string -> theory -> theory
  
  (* derives a trivial instance (None) for class ccompare *)
  val derive_no_ccompare : string -> theory -> theory

end

structure CCompare_Generator : CCOMPARE_GENERATOR =
struct

open Generator_Aux
open Containers_Generator

val ccmpS = @{sort ccompare};
val ccmpN = @{const_name ccompare};
fun cmpT T = T --> T --> @{typ order};
fun ccmpT T = Type (@{type_name option}, [cmpT T])
fun ccmp_const T = Const (ccmpN, T);

val generator_type = Comparator_Generator.BNF

fun dest_comp ctxt tname =
  (case Comparator_Generator.get_info ctxt tname of
    SOME {comp = c, comp_thm = c_thm, ...} =>
      let
        val Ts = fastype_of c |> strip_type |> fst |> `((fn x => x - 2) o length) |> uncurry take
      in (c, c_thm, Ts) end
  | NONE => error ("no order info for type " ^ quote tname))

fun mk_ID_ccompare eq_var = 
  let
    val ty = fastype_of eq_var
    val oty = Type (@{type_name option}, [ty])
    val ccompare = Const (ccmpN, oty)
    val ID_cc = Const (@{const_name ID}, oty --> oty) $ ccompare
  in 
    ID_cc
  end

fun mk_ccmp_rhs c [] = mk_Some c
  | mk_ccmp_rhs c (T :: Ts) = 
      let
        val cmp = ccmp_const T
        val idcmp = mk_ID_ccompare cmp
        val tname = T |> binder_types |> hd |> dest_TVar |> fst |> fst 
        val arg_comp = Free ("comp_" ^ tname, T) 
        val caseT = Const (@{const_name case_option}, dummyT) 
          $ Const (@{const_name None}, dummyT)
          $ lambda arg_comp (mk_ccmp_rhs (c $ arg_comp) Ts)
          $ idcmp
      in 
        caseT
      end

  
fun mk_ccmp_def T rhs =
  Logic.mk_equals (Const (ccmpN, ccmpT T), rhs)

fun ccompare_tac ctxt tname Ts = 
  let
    val (_, c_thm, _) = dest_comp ctxt tname
  in
    unfold_tac ctxt @{thms ID_def id_def} 
    THEN REPEAT_DETERM_N (length Ts) (
      Splitter.split_asm_tac ctxt @{thms option.splits} 1 THEN
      unfold_tac ctxt @{thms option.simps}) 
    THEN unfold_tac ctxt @{thms option.simps} 
    THEN resolve_tac ctxt @{thms comparator_subst} 1 THEN assume_tac ctxt 1 
    THEN REPEAT_DETERM (dresolve_tac ctxt @{thms ccompare} 1) 
    THEN (resolve_tac ctxt [c_thm] THEN_ALL_NEW assume_tac ctxt) 1
  end
    
fun ccompare_instance_via_comparator tname thy =
  let
    val thy = Named_Target.theory_map (Comparator_Generator.ensure_info generator_type tname) thy
    val _ = writeln ("deriving \"ccompare\" instance for type " ^ quote tname)

    val (main_ty, xs) = typ_and_vs_of_typname thy tname ccmpS
    val (Ts, (cmp_thm, lthy)) =
      Class.instantiation ([tname], xs, ccmpS) thy
      |> (fn ctxt =>
        let
          val (c, _, Ts) = dest_comp ctxt tname
          val typ_mapping = all_tys c (map TFree xs)
          val cmp_def = mk_ccmp_def dummyT (mk_ccmp_rhs c Ts) |> typ_mapping
        in
          (Ts, define_overloaded_generic
           ((Binding.name ("ccompare_" ^ Long_Name.base_name tname ^ "_def"),
            @{attributes [code]}),
            cmp_def) ctxt)
        end)
    val thy = Class.prove_instantiation_exit (fn ctxt =>
      Class.intro_classes_tac ctxt []
      THEN unfold_tac ctxt [cmp_thm]
      THEN ccompare_tac ctxt tname Ts) lthy
    val info = Comparator_Generator.get_info (Named_Target.theory_init thy) tname |> the
    val used = #used_positions info
    
    (* is_ccompare (a1,..,an)ty = (is_ccompare a1 \<and> ... ) -thm *)
    fun mk_is_ccompare ty = mk_is_c_dots ty @{const_name is_ccompare}
    val main_is_ccompare = mk_is_ccompare main_ty
    val param_tys = dest_Type main_ty |> snd   
    val filtered_tys = used ~~ param_tys |> filter fst |> map snd
    val param_is_ccompare = map mk_is_ccompare filtered_tys
    val is_ccompare_thm_trm = HOLogic.mk_Trueprop (case param_is_ccompare of 
        [] => main_is_ccompare
      | _ => HOLogic.mk_eq (main_is_ccompare,HOLogic_list_conj param_is_ccompare))
    val is_ccompare_thm = Goal.prove (Proof_Context.init_global thy) [] [] is_ccompare_thm_trm 
      (fn {context = ctxt, prems = _} => 
        simp_tac (Splitter.add_split @{thm option.split} ctxt 
          addsimps (cmp_thm :: @{thms ID_Some ID_None is_ccompare_def})
        ) 1
      )
    val thy = register_is_c_dots_lemma @{const_name is_ccompare} (Long_Name.base_name tname) 
      is_ccompare_thm thy
  in
    thy
  end

fun mk_some_compare ty = mk_Some (Const (@{const_name "compare"}, cmpT ty))

fun ccompare_instance_via_compare tname thy = 
  let
    val base_name = Long_Name.base_name tname
    val _ = writeln ("deriving \"ccompare_order\" instance for type " ^ 
      quote tname ^ " via compare_order")
    val (ty,vs) = typ_and_vs_of_typname thy tname @{sort compare}
    val ccompare_rhs = mk_some_compare ty
    val ccompare_ty = Term.fastype_of ccompare_rhs
    val ccompare_def = mk_def ccompare_ty ccmpN ccompare_rhs
    val (ccompare_thm,lthy) = Class.instantiation ([tname],vs,ccmpS) thy
      |> (define_overloaded ("ccompare_" ^ base_name ^ "_def", ccompare_def))
     
    val thy = Class.prove_instantiation_exit (fn ctxt => 
      Class.intro_classes_tac ctxt [] 
      THEN unfold_tac ctxt [ccompare_thm]
      THEN unfold_tac ctxt @{thms option.simps prod.simps}
      THEN resolve_tac ctxt @{thms compare_subst} 1 THEN assume_tac ctxt 1
      ) lthy
    val thy = derive_is_c_dots_lemma ty @{const_name is_ccompare} 
      [ccompare_thm, @{thm is_ccompare_def}] base_name thy

  in thy end

fun mk_none_ccompare ty = Const (@{const_name None}, Type (@{type_name option}, [cmpT ty]))

val derive_no_ccompare = derive_none ccmpN ccmpS mk_none_ccompare
  
fun ccompare_instance tname param thy =
  let
    val _ = is_class_instance thy tname ccmpS
      andalso error ("type " ^ quote tname ^ " is already an instance of class \"ccompare\"")
  in
    if param = "" then ccompare_instance_via_comparator tname thy
    else if param = "no" then derive_no_ccompare tname thy
    else if param = "compare" then ccompare_instance_via_compare tname thy 
    else error "unknown parameter, supported are (no parameter), \"compare\", and \"no\"" 
  end

val _ = Theory.setup
 (Derive_Manager.register_derive "ccompare" 
    "generate a conditional comparator; options are (), (no), and (compare)" (ccompare_instance))

end
