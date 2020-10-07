(*  Title:      nominal_atoms/ML
    Authors:    Brian Huffman, Christian Urban

    Command for defining concrete atom types.

    At the moment, only single-sorted atom types
    are supported.
*)

signature ATOM_DECL =
sig
  val add_atom_decl: (binding * (binding option)) -> theory -> theory
end;

structure Atom_Decl : ATOM_DECL =
struct

val simp_attr = Attrib.internal (K Simplifier.simp_add)

fun atom_decl_set (str : string) : term =
  let
    val a = Free ("a", @{typ atom});
    val s = Const (@{const_name "Sort"}, @{typ "string => atom_sort list => atom_sort"})
              $ HOLogic.mk_string str $ HOLogic.nil_const @{typ "atom_sort"};
  in
    HOLogic.mk_Collect ("a", @{typ atom}, HOLogic.mk_eq (mk_sort_of a, s))
  end

fun add_atom_decl (name : binding, arg : binding option) (thy : theory) =
  let
    val str = Sign.full_name thy name;

    (* typedef *)
    val set = atom_decl_set str;
    fun tac ctxt = resolve_tac ctxt @{thms exists_eq_simple_sort} 1;
    val ((full_tname, info as ({Rep_name, Abs_name, ...}, {type_definition, ...})), thy) =
      thy
      |> Named_Target.theory_map_result (apsnd o Typedef.transform_info)
        (Typedef.add_typedef {overloaded = false} (name, [], NoSyn) set NONE tac);

    (* definition of atom and permute *)
    val newT = #abs_type (fst info);
    val RepC = Const (Rep_name, newT --> @{typ atom});
    val AbsC = Const (Abs_name, @{typ atom} --> newT);
    val a = Free ("a", newT);
    val p = Free ("p", @{typ perm});
    val atom_eqn =
      HOLogic.mk_Trueprop (HOLogic.mk_eq (mk_atom a, RepC $ a));
    val permute_eqn =
      HOLogic.mk_Trueprop (HOLogic.mk_eq
        (mk_perm p a, AbsC $ (mk_perm p (RepC $ a))));
    val atom_def_name =
      Binding.prefix_name "atom_" (Binding.suffix_name "_def" name);
    val sort_thm_name =
      Binding.prefix_name "atom_" (Binding.suffix_name "_sort" name);
    val permute_def_name =
      Binding.prefix_name "permute_" (Binding.suffix_name "_def" name);

    (* at class instance *)
    val lthy =
      Class.instantiation ([full_tname], [], @{sort at}) thy;
    val ((_, (_, permute_ldef)), lthy) =
      Specification.definition NONE [] [] ((permute_def_name, []), permute_eqn) lthy;
    val ((_, (_, atom_ldef)), lthy) =
      Specification.definition NONE [] [] ((atom_def_name, []), atom_eqn) lthy;
    val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy);
    val permute_def = singleton (Proof_Context.export lthy ctxt_thy) permute_ldef;
    val atom_def = singleton (Proof_Context.export lthy ctxt_thy) atom_ldef;
    val class_thm = @{thm at_class} OF [type_definition, atom_def, permute_def];
    val sort_thm = @{thm at_class_sort} OF [type_definition, atom_def]
    val thy = lthy
      |> snd o (Local_Theory.note ((sort_thm_name, [simp_attr]), [sort_thm]))
      |> Class.prove_instantiation_instance (fn ctxt => resolve_tac ctxt [class_thm] 1)
      |> Local_Theory.exit_global;
  in
    thy
  end;

(** outer syntax **)
val _ =
  Outer_Syntax.command @{command_keyword atom_decl}
    "declaration of a concrete atom type"
      ((Parse.binding -- Scan.option (Args.parens (Parse.binding))) >>
        (Toplevel.theory o add_atom_decl))

end;
