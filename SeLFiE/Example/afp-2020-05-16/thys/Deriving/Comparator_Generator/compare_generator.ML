(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
signature COMPARE_GENERATOR =
sig
(* derives a compare-instance for a given class. depending on the comparator_type, this will
   just be comparator_of (via linorder), or it will be a comparator constructed for BNF datatypes *)
val compare_instance : Comparator_Generator.comparator_type -> string -> theory -> theory

(* derives an instance for class compare_order via linorder, 
   where the main comparator will be comparator_of *)
val compare_order_instance_via_comparator_of : string -> theory -> theory

(* derives an instance for class compare_order via compare, where 
   the orders are defined via le_of_comp and lt_of_comp *)
val compare_order_instance_via_compare : string -> theory -> theory
end

structure Compare_Generator : COMPARE_GENERATOR =
struct

open Generator_Aux

val cmpS = @{sort compare};
val cmpoS = @{sort compare_order};
val cmpN = @{const_name compare};
val lessN = @{const_name less}
val less_eqN = @{const_name less_eq}
val linordS = @{sort linorder}
fun cmpT T = T --> T --> @{typ order};
fun ordT T = T --> T --> @{typ bool};
fun cmp_const T = Const (cmpN, T);
fun cmp_of_const T = Const (@{const_name comparator_of}, T);


fun dest_comp ctxt tname =
  (case Comparator_Generator.get_info ctxt tname of
    SOME {comp = c, comp_thm = c_thm, ...} =>
      let
        val Ts = fastype_of c |> strip_type |> fst |> `((fn x => x - 2) o length) |> uncurry take
      in (c, c_thm, Ts) end
  | NONE => error ("no order info for type " ^ quote tname))

fun all_tys comp free_types =
  let
    val Ts = fastype_of comp |> strip_type |> fst |> drop_last |> List.last |> dest_Type |> snd
  in rename_types (Ts ~~ free_types) end

fun mk_cmp_rhs c Ts =
  list_comb (c, map cmp_const Ts)

fun mk_cmp_rhs_comparator_of c Ts =
  list_comb (c, map cmp_of_const Ts)


fun mk_cmp_def T rhs =
  Logic.mk_equals (Const (@{const_name compare}, cmpT T), rhs)

fun mk_ord_def T strict rhs =
  Logic.mk_equals (
    Const (if strict then lessN else less_eqN, ordT T),
    Const (if strict then @{const_name lt_of_comp} else @{const_name le_of_comp}, cmpT T --> ordT T) $ rhs)
  
fun mk_binop_def binop T rhs =
  Logic.mk_equals (Const (binop, T --> T --> @{typ bool}), rhs)

fun comparator_tac ctxt tname =
  let val (_, c_thm, _) = dest_comp ctxt tname
  in (resolve_tac ctxt [c_thm] THEN_ALL_NEW resolve_tac ctxt @{thms comparator_compare}) 1 end

fun comparator_tac_comparator_of ctxt tname i =
  let val (_, c_thm, _) = dest_comp ctxt tname
  in (resolve_tac ctxt [c_thm] THEN_ALL_NEW resolve_tac ctxt @{thms comparator_of}) i end

fun compare_instance gen_type tname thy =
  let
    val _ = is_class_instance thy tname cmpS
      andalso error ("type " ^ quote tname ^ " is already an instance of class \"compare\"")
    val _ = writeln ("deriving \"compare\" instance for type " ^ quote tname)
    val thy = Named_Target.theory_map (Comparator_Generator.ensure_info gen_type tname) thy
    val {used_positions = us, ...} = the (Comparator_Generator.get_info 
        (Named_Target.theory_init thy) tname) 

    val (_, xs) = typ_and_vs_of_used_typname tname us cmpS
    val (cmp_thm, lthy) =
      Class.instantiation ([tname], xs, cmpS) thy
      |> (fn ctxt =>
        let
          val (c, _, Ts) = dest_comp ctxt tname
          val typ_mapping = all_tys c (map TFree xs)
          val cmp_def = mk_cmp_def dummyT (mk_cmp_rhs c Ts) |> typ_mapping
        in
          Generator_Aux.define_overloaded_generic
           ((Binding.name ("compare_" ^ Long_Name.base_name tname ^ "_def"),
            @{attributes [code, compare_simps]}),
            cmp_def) ctxt
        end)
  in
    Class.prove_instantiation_exit (fn ctxt =>
      Class.intro_classes_tac ctxt []
      THEN unfold_tac ctxt [cmp_thm]
      THEN comparator_tac ctxt tname) lthy
  end
  
fun linorder_instance gen_type tname thy =
  let
    val _ = is_class_instance thy tname linordS
      andalso error ("type " ^ quote tname ^ " is already an instance of class \"linorder\"")
    val _ = writeln ("deriving \"linorder\" instance for type " ^ quote tname)
    val thy = Named_Target.theory_map (Comparator_Generator.ensure_info gen_type tname) thy
    val {used_positions = us, ...} = the (Comparator_Generator.get_info 
        (Named_Target.theory_init thy) tname) 

    val (_, xs) = typ_and_vs_of_used_typname tname us linordS
    val ((less_thm, (less_eq_thm, lthy))) =
      Class.instantiation ([tname], xs, linordS) thy
      |> (fn ctxt =>
        let
          val (c, _, Ts) = dest_comp ctxt tname
          val typ_mapping = all_tys c (map TFree xs)
          val cmp = mk_cmp_rhs_comparator_of c Ts
          val less_def = mk_ord_def dummyT true cmp |> typ_mapping |> infer_type ctxt
          val less_eq_def = mk_ord_def dummyT false cmp |> typ_mapping
          val base_name = Long_Name.base_name tname
        in
          (ctxt 
          |> Generator_Aux.define_overloaded_generic
            ((Binding.name ("less_" ^ base_name ^ "_def"), @{attributes [code]}), less_def)            
          ||> Generator_Aux.define_overloaded_generic
            ((Binding.name ("less_eq_" ^ base_name ^ "_def"), @{attributes [code]}), less_eq_def))

        end)
    fun linear_tac ctxt i = 
      resolve_tac ctxt [nth @{thms linorder_axiomsD} (i - 1)] i
      THEN resolve_tac ctxt @{thms comparator.linorder} i
      THEN comparator_tac_comparator_of ctxt tname i
  in
    Class.prove_instantiation_exit ( fn ctxt => 
      Class.intro_classes_tac ctxt []
      THEN unfold_tac ctxt [less_thm, less_eq_thm]
      THEN linear_tac ctxt 5
      THEN linear_tac ctxt 4
      THEN linear_tac ctxt 3
      THEN linear_tac ctxt 2
      THEN linear_tac ctxt 1
      THEN auto_tac ctxt 
    ) lthy
  end


fun compare_instance_param tname param =  
  let
    val gen_type = if param = "" then Comparator_Generator.BNF
      else if param = "linorder" then Comparator_Generator.Linorder
      else error "unknown parameter for compare instance"
  in compare_instance gen_type tname end

fun linorder_instance_param tname param =  
  let
    val gen_type = if param = "" then Comparator_Generator.BNF
      else if param = "linorder" then Comparator_Generator.Linorder
      else error "unknown parameter for compare instance"
  in linorder_instance gen_type tname end


(*if "tname" not yet instance of "compare", instantiate*)
fun maybe_instantiate_compare gen_type tname thy =
  if is_class_instance thy tname cmpS then thy
  else compare_instance gen_type tname thy

fun compare_order_instance_via_compare tname thy =
  let
    val gen_type = Comparator_Generator.BNF
    val thy = maybe_instantiate_compare gen_type tname thy
    val {used_positions = us, ...} = the (Comparator_Generator.get_info 
      (Named_Target.theory_init thy) tname)
    val (T, xs) = typ_and_vs_of_used_typname tname us cmpS
    
    val cmp = cmp_const (cmpT T)
    val (le_thm, less_thm, lthy) =
      Class.instantiation ([tname], xs, cmpoS) thy
      |> (fn lthy =>
        let 
          val less_def = mk_binop_def @{const_name less} T 
            (Const (@{const_name lt_of_comp}, cmpT T --> T --> T --> @{typ bool}) $ cmp)
          val le_def = mk_binop_def @{const_name less_eq} T 
            (Const (@{const_name le_of_comp}, cmpT T --> T --> T --> @{typ bool}) $ cmp)
          val (less_thm, lthy) =  Generator_Aux.define_overloaded 
            ("less_" ^ Long_Name.base_name tname ^ "_def", less_def) lthy
          val (le_thm, lthy) = Generator_Aux.define_overloaded 
            ("less_eq_" ^ Long_Name.base_name tname ^ "_def", le_def) lthy         
        in (le_thm, less_thm, lthy) end)
  in
    Class.prove_instantiation_exit (fn ctxt =>
      Class.intro_classes_tac ctxt []
      THEN unfold_tac ctxt [le_thm]
      THEN unfold_tac ctxt [less_thm]) lthy
  end

fun compare_order_instance_via_comparator_of tname thy =
  let
    val gen_type = Comparator_Generator.Linorder
    val thy = maybe_instantiate_compare gen_type tname thy
    val xs = Generator_Aux.typ_and_vs_of_typname thy tname cmpS |> snd
    val lthy = Class.instantiation ([tname], xs, cmpoS) thy
  in
    Class.prove_instantiation_exit (fn ctxt =>
      Class.intro_classes_tac ctxt []
      THEN unfold_tac ctxt (Named_Theorems.get ctxt @{named_theorems compare_simps})
      THEN resolve_tac ctxt @{thms le_lt_comparator_of(1)} 1
      THEN resolve_tac ctxt @{thms le_lt_comparator_of(2)} 1) lthy
  end
  
fun compare_order_instance tname param thy =
  let
    val _ = is_class_instance thy tname cmpoS
      andalso error ("type " ^ quote tname ^ " is already an instance of class \"compare_order\"")
    val _ = writeln ("deriving \"compare_order\" instance for type " ^ quote tname)
  in
    if param = "" then compare_order_instance_via_compare tname thy
    else if param = "linorder" then compare_order_instance_via_comparator_of tname thy
    else error "unknown parameter, supported are (no parameter) and \"linorder\""
  end

val _ =
  Theory.setup
    (Derive_Manager.register_derive 
      "compare" 
      "register types in class compare, options: (linorder) or ()" 
      compare_instance_param
    #> Derive_Manager.register_derive 
      "compare_order" 
      "register types in class compare_order, options: (linorder) or ()" 
      compare_order_instance
    #> Derive_Manager.register_derive 
      "linorder" 
      "register types in class linorder, options: (linorder) or ()" 
      linorder_instance_param)

end
