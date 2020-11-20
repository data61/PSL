(* Author:  René Thiemann, UIBK *)
(* The generators have been written as part of the IsaFoR/CeTA formalization. *)

signature CONTAINERS_GENERATOR = 
sig 

  val mk_is_c_dots : typ -> string -> term 
  
  (*                        const     sort    choices            *)
  val derive_set_map_impl : string -> sort -> (string * term) list 
    -> string -> string -> theory -> theory

  (*                const_name, sort, mk_none,         typ_name *)
  val derive_none : string -> sort -> (typ -> term) -> string -> theory -> theory

  (*                             const_name  base_name *)
  val register_is_c_dots_lemma : string -> string -> thm -> theory -> theory

  (*                           typ    const_name  defs      base_name *)
  val derive_is_c_dots_lemma : typ -> string -> thm list -> string -> theory -> theory

  val mk_Some : term -> term

  (* p1 /\ ... /\ pn *)
  val HOLogic_list_conj : term list -> term

  val all_tys : term -> typ list -> term -> term
  
  val is_class_instance : theory -> string -> sort -> bool
end

structure Containers_Generator : CONTAINERS_GENERATOR =
struct 

open Generator_Aux

fun is_class_instance thy tname class =
  Proof_Context.read_type_name {proper = true, strict = true} (Proof_Context.init_global thy) tname
  |> (fn T => Sign.of_sort thy (T, class))

fun all_tys comp free_types =
  let
    val Ts = fastype_of comp |> strip_type |> fst |> drop_last |> List.last |> dest_Type |> snd
  in rename_types (Ts ~~ free_types) end

fun HOLogic_list_conj [] = @{term True}
  | HOLogic_list_conj [x] = x
  | HOLogic_list_conj (x :: xs) = HOLogic.mk_conj (x, HOLogic_list_conj xs)

fun mk_Some t = 
  let
    val ty = fastype_of t
  in
    Const (@{const_name Some}, ty --> Type (@{type_name option}, [ty])) $ t
  end

fun mk_set_map_impl choices ty choice thy = 
  let 
    val smi = case AList.lookup (op =) choices choice of
      SOME smi => smi
    | NONE => if choice = "" then error "you must provide some constant as parameter"
        else Syntax.read_term (Proof_Context.init_global thy) choice
    val smi_ty = fastype_of smi
    val pty = Type (@{type_name phantom},[ty,smi_ty])
    val ph = Const (@{const_name phantom}, smi_ty --> pty)
    val res = ph $ smi
  in res
end

fun derive_set_map_impl smi_const smi_sort choices typ_name choice thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val smi_name = Long_Name.base_name smi_const
    val _ = writeln ("use " ^ choice ^ " as " ^ smi_name ^ " for type " ^ base_name)
    val (ty,vs) = Generator_Aux.typ_and_vs_of_typname thy typ_name @{sort type}
    val set_map_impl_rhs = mk_set_map_impl choices ty choice thy
    val set_map_impl_ty = Term.fastype_of set_map_impl_rhs
    val set_map_impl_def = Generator_Aux.mk_def set_map_impl_ty smi_const set_map_impl_rhs
    val (_,lthy) = Class.instantiation ([typ_name],vs,smi_sort) thy
      |> Generator_Aux.define_overloaded (smi_name ^ "_" ^ base_name ^ "_def", set_map_impl_def)     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt []) lthy
    val _ = writeln ("registered " ^ base_name ^ " in class " ^ smi_name)  
  in thy' end

fun derive_none const sort mk_none typ_name thy = 
  let
    val base_name = Long_Name.base_name typ_name
    val const_name = Long_Name.base_name const
    val sort_name = hd sort |> Long_Name.base_name
    val _ = writeln ("use None as trivial implementation of " ^ sort_name ^ " for type " ^ base_name)
    val (ty,vs) = Generator_Aux.typ_and_vs_of_typname thy typ_name @{sort type}
    val none_rhs = mk_none ty
    val none_ty = Term.fastype_of none_rhs
    val const_def = Generator_Aux.mk_def none_ty const none_rhs
    val (none_thm,lthy) = Class.instantiation ([typ_name],vs,sort) thy
      |> Generator_Aux.define_overloaded (const_name ^ "_" ^ base_name ^ "_def", const_def)
     
    val thy' = Class.prove_instantiation_exit (fn ctxt => Class.intro_classes_tac ctxt []
      THEN unfold_tac ctxt [none_thm]
      THEN (REPEAT (force_tac ctxt 1))) lthy
    val _ = writeln ("registered " ^ base_name ^ " in class " ^ sort_name)    
  in thy' end
 
fun mk_is_c_dots ty dots = 
  let 
    val ity = Type (@{type_name itself}, [ty])
    val it = Const (@{const_name Pure.type},ity)
    val res = Const (dots, ity --> @{typ bool}) $ it
  in res
end

fun register_is_c_dots_lemma const_name base_name thm thy = let
      val name = Long_Name.base_name const_name ^ "_" ^ base_name
      val lthy_map = Local_Theory.note ((Binding.name name, 
          @{attributes [simp,code_post]}), [thm]) #> #2
      val thy' = Named_Target.theory_map lthy_map thy
      val _ = writeln ("derived " ^ name ^ "-lemma")
    in thy'
end

fun derive_is_c_dots_lemma ty const_name defs base_name thy  = let
      val is_c_dots = HOLogic.mk_Trueprop (mk_is_c_dots ty const_name)
      val thm = Goal.prove_future (Proof_Context.init_global thy) [] [] is_c_dots (fn {prems = _, context = ctxt} => 
        unfold_tac ctxt (defs @ @{thms ID_Some option.simps})
        THEN blast_tac ctxt 1
      )
    in register_is_c_dots_lemma const_name base_name thm thy
end

end
