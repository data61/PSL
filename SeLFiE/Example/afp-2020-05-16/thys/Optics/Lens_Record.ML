signature LENS_UTILS =
sig
  val add_alphabet_cmd : {overloaded: bool} ->
     (string * string option) list * binding ->
       string option -> (binding * string * mixfix) list -> theory -> theory
end;

structure Lens_Utils : LENS_UTILS =
struct

(* We set up the following syntactic entities that correspond to various parts of Isabelle syntax
  and names that we depend on. These code would need to be updated if the names of the Isabelle
  and lens theories and/or theorems change. *)

val FLDLENS = "FLDLENS"
val BASELENS = "BASELENS"
val base_lensN = "base\<^sub>L"
val child_lensN = "more\<^sub>L"
val all_lensN = "all\<^sub>L"
val base_moreN = "base_more"
val bij_lens_suffix = "_bij_lens"
val vwb_lens_suffix = "_vwb_lens"
val sym_lens_suffix = "_sym_lens"
val indepsN = "indeps"
val sublensN = "sublenses"
val quotientN = "quotients"
val compositionN = "compositions"
val Trueprop = @{const_name Trueprop}
val HOLeq = @{const_name HOL.eq}
val bij_lens = @{const_name bij_lens}
val vwb_lens = @{const_name vwb_lens}
val sym_lens = @{const_name sym_lens}
val lens_indep = @{const_name lens_indep}
val lens_plus = @{const_name lens_plus}
val lens_quotient = @{const_name lens_quotient}
val lens_comp = @{const_name lens_comp}
val id_lens = @{const_name id_lens}
val sublens = @{const_name sublens}
val lens_equiv = @{const_name lens_equiv}
val lens_suffix = "\<^sub>v"
val lens_defsN = "lens_defs"
val lens_defs = (Binding.empty, [Token.make_src (lens_defsN, Position.none) []])
val alpha_splitsN = "alpha_splits"
val alpha_splits = [Token.make_src (alpha_splitsN, Position.none) []]
val equivN = "equivs"
val splits_suffix = ".splits"
val defs_suffix = ".defs"
val prod_case_eq_ifN = "prod.case_eq_if"
val slens_view = "view"
val slens_coview = "coview"

(* The following code is adapted from the record package. We generate a record, but also create
   lenses for each field and prove properties about them. *)

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));

fun read_fields raw_fields ctxt =
  let
    val Ts = Syntax.read_typs ctxt (map (fn (_, raw_T, _) => raw_T) raw_fields);
    val fields = map2 (fn (x, _, mx) => fn T => (x, T, mx)) raw_fields Ts;
    val ctxt' = fold Variable.declare_typ Ts ctxt;
  in (fields, ctxt') end;

fun add_record_cmd overloaded (raw_params, binding) raw_parent raw_fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, ctxt3) = read_fields raw_fields ctxt2;
    val params' = map (Proof_Context.check_tfree ctxt3) params;
  in thy |> Record.add_record overloaded (params', binding) parent fields end;

(* Construct a theorem and proof that a given field lens is very well-behaved *)

fun lens_proof tname x thy =
  let open Simplifier; open Global_Theory in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ (Const (vwb_lens, dummyT) $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ x, dummyT))]))
      (fn {context = context, prems = _}
                           => EVERY [ Locale.intro_locales_tac {strict = true, eager = true} context []
                                    , PARALLEL_ALLGOALS (asm_simp_tac 
                                                          (fold add_simp (get_thm thy (x ^ "_def") :: get_thms thy (tname ^ ".defs"))
                                                                         context))])
  end

fun lens_sym_proof tname thy =
  let open Simplifier; open Global_Theory in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ (Const (sym_lens, dummyT) $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ all_lensN, dummyT))]))
      (fn {context = context, prems = _}
                           => EVERY [ Classical.rule_tac context [@{thm sym_lens.intro}] [] 1
                                    , PARALLEL_ALLGOALS (asm_simp_tac 
                                                          (fold add_simp (@{thms slens.defs} @ get_thms thy (tname ^ ".defs"))
                                                                         context))])
  end


fun prove_lens_goal tname thy ctx =
  let open Simplifier; open Global_Theory in
  auto_tac (fold add_simp (get_thms thy lens_defsN @ 
                           get_thms thy (tname ^ splits_suffix) @ 
                           [get_thm thy prod_case_eq_ifN]) ctx)
end

fun prove_indep tname thy = 
  let open Simplifier; open Global_Theory in
  (fn {context, prems = _} =>
          EVERY [auto_tac (add_simp @{thm lens_indep_vwb_iff} context)
                ,prove_lens_goal tname thy context])
end

fun prove_sublens tname thy = 
  let open Simplifier; open Global_Theory in
  (fn {context, prems = _} =>
          EVERY [auto_tac (add_simp @{thm sublens_iff_sublens'} context)
                ,prove_lens_goal tname thy context])
end

fun prove_quotient tname thy = 
  let open Simplifier; open Global_Theory in
  (fn {context, prems = _} =>
          EVERY [prove_lens_goal tname thy context])
end


fun prove_equiv tname thy = 
  let open Simplifier; open Global_Theory in
  (fn {context, prems = _} =>
          EVERY [auto_tac (add_simp @{thm lens_equiv_iff_lens_equiv'} context)
                ,prove_lens_goal tname thy context])
end
 
(* Constrct a proof that base + more is a bijective lens *)

fun lens_bij_proof tname thy =
  let open Simplifier; open Global_Theory in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ (Const (bij_lens, dummyT) $ 
                (Const (lens_plus, dummyT) $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                                           $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ child_lensN, dummyT)))]))
      (fn {context = context, prems = _}
                           => EVERY [ Locale.intro_locales_tac {strict = true, eager = true} context []
                                    , auto_tac (fold add_simp (get_thms thy lens_defsN @ [get_thm thy prod_case_eq_ifN])
                                                                         context)])
  end

(* Construct a theorem and proof that two lenses, x and y, are independent. Since some lenses exist
   both with the source type as the record extension, and in the context of the extended record
   we need two versions of this function. The first shows it for the lenses on the extension, and
   thus uses an "intro_locales" as a means to discharge the individual lens laws of the vwb_lens
   locale. *)

fun indep_proof tname thy (x, y) =
  let open Simplifier; open Global_Theory in
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (lens_indep, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ y, dummyT)
                )]))
      (prove_indep tname thy)
  end

fun equiv_more_proof tname pname thy fs =
  let open Simplifier; open Global_Theory; open Context; open Term in
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (lens_equiv, dummyT)
                $ Const (pname ^ "." ^ child_lensN, dummyT)
                $ foldr1 (fn (x, y) => Const (lens_plus, dummyT) $ x $ y) 
                         (map (fn n => Const (theory_name thy ^ "." ^ tname ^ "." ^ n, dummyT)) (fs @ [child_lensN]))
                )]))
      (prove_equiv tname thy)
  end

fun equiv_base_proof tname parent thy fs =
  let open Simplifier; open Global_Theory; open Context; open Term in
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (lens_equiv, dummyT)
                $ Const (theory_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                $ foldr1 (fn (x, y) => Const (lens_plus, dummyT) $ x $ y) 
                         ((case parent of NONE => [] | SOME (_, pname) => [Const (pname ^ "." ^ base_lensN, dummyT)]) @ 
                          map (fn n => Const (theory_name thy ^ "." ^ tname ^ "." ^ n, dummyT)) fs)
                )]))
      (prove_equiv tname thy)
  end

fun equiv_partition_proof tname thy =
  let open Simplifier; open Global_Theory; open Context; open Term in
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (lens_equiv, dummyT)
                $ ( Const (lens_plus, dummyT) 
                  $ Const (theory_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                  $ Const (theory_name thy ^ "." ^ tname ^ "." ^ child_lensN, dummyT))
                $ Const (id_lens, dummyT)
                )]))
      (prove_equiv tname thy)
  end

(* Prove a theorem that every child lens is a sublens of the parent. *)

fun sublens_proof tname pname thy y x =
  let open Simplifier; open Global_Theory in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (sublens, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
                $ Const (pname ^ "." ^ y, dummyT)
                )]))
      (prove_sublens tname thy)
end

fun quotient_proof tname thy x =
  let open Simplifier; open Global_Theory in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (HOLeq, dummyT)
                $ (Const (lens_quotient, dummyT) 
                   $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
                   $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                  )
                $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
                )]))
      (prove_quotient tname thy)
end

fun composition_proof tname thy x =
  let open Simplifier; open Global_Theory in
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (HOLeq, dummyT)
                $ (Const (lens_comp, dummyT) 
                   $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
                   $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ base_lensN, dummyT)
                  )
                $ Const (Context.theory_name thy ^ "." ^ tname ^ "." ^ x, dummyT)
                )]))
      (prove_quotient tname thy)
end


fun pairWith _ [] = []
  | pairWith x (y :: ys) = [(x, y), (y, x)] @ pairWith x ys;

fun pairings [] = []
  | pairings (x :: xs) = pairWith x xs @ pairings xs;

(* Finally we have the function that actually constructs the record, lenses for each field,
   independence proofs, and also sublens proofs. *)

fun add_alphabet_cmd _ (raw_params, binding) raw_parent raw_fields thy =
  let
    open Simplifier; open Global_Theory
    val tname = Binding.name_of binding
    val fields = map (fn (x, y, z) => (Binding.suffix_name lens_suffix x, y, z)) raw_fields
    val lnames = map (fn (x, _, _) => Binding.name_of x) raw_fields
    val (parent, _) = read_parent raw_parent (Proof_Context.init_global thy);
    fun ldef x = (x, x ^ " = " ^ FLDLENS ^ " " ^ x ^ lens_suffix)
    val pname = case parent of SOME (_,r) => r | NONE => "";
    val plchild =
      case parent of
        SOME (_, _) => child_lensN |
        NONE => ""
    val bldef = (base_lensN, base_lensN ^ " = " ^ BASELENS ^ " " ^ tname);
    val mldef = (child_lensN, child_lensN ^ " = " ^ FLDLENS ^ " more"); 
    val sldef = (all_lensN, all_lensN ^ " \<equiv> \<lparr> " ^ slens_view ^ " = " ^ base_lensN ^ ", " ^ slens_coview ^ " = " ^ child_lensN ^ " \<rparr>");
    val plnames = if (raw_parent = NONE) then [] else lnames  @ [child_lensN];
    fun pindeps thy = map (fn thm => @{thm sublens_pres_indep} OF [thm]) (get_thms thy sublensN)
                    @ map (fn thm => @{thm sublens_pres_indep'} OF [thm]) (get_thms thy sublensN)
 in thy     (* Add a new record for the new alphabet lenses *)
         |> add_record_cmd {overloaded = false} (raw_params, binding) raw_parent fields
            (* Add the record definition theorems to lens_defs *)
         |> Named_Target.theory_map (snd o Specification.theorems_cmd "" [((Binding.empty, []), [(Facts.named (tname ^ defs_suffix), snd lens_defs)])] [] false)
            (* Add the record splitting theorems to the alpha_splits set for proof automation *)
         |> Named_Target.theory_map (snd o Specification.theorems_cmd "" [((Binding.empty, []), [(Facts.named (tname ^ splits_suffix), alpha_splits)])] [] false)
            (* Add definitions for each of the lenses corresponding to each record field in-situ *)
         |> Sign.qualified_path false binding
         |> Named_Target.theory_map
              (fold (fn (n, d) => snd o Specification.definition_cmd (SOME (Binding.make (n, Position.none), NONE, NoSyn)) [] [] (lens_defs, d) true) (map ldef lnames @ [bldef, mldef]))
            (* Add definition of the underlying symmetric lens *)
         |> Named_Target.theory_map
              (fold (fn (n, d) => Specification.abbreviation_cmd Syntax.mode_default (SOME (Binding.make (n, Position.none), NONE, NoSyn)) [] d true) [sldef])
            (* Add a vwb lens proof for each field lens *)
         |> fold (fn x => fn thy => snd (add_thm ((Binding.make (x ^ vwb_lens_suffix, Position.none), lens_proof tname x thy), [Simplifier.simp_add]) thy)) (lnames @ [base_lensN, child_lensN])
            (* Add a bij lens proof for the base and more lenses *)
         |> (fn thy => snd (add_thm ((Binding.make (base_moreN ^ bij_lens_suffix, Position.none), lens_bij_proof tname thy), [Simplifier.simp_add]) thy))
            (* Add sublens proofs *)
         |> (fn thy => snd (add_thmss [((Binding.make (sublensN, Position.none), map (sublens_proof tname pname thy plchild) plnames @ map (sublens_proof tname (Context.theory_name thy ^ "." ^ tname) thy base_lensN) lnames), [Simplifier.simp_add])] thy))
            (* Add quotient proofs *)
         |> (fn thy => snd (add_thmss [((Binding.make (quotientN, Position.none), map (quotient_proof tname thy) lnames), [Simplifier.simp_add])] thy))
            (* Add composition proofs *)
         |> (fn thy => snd (add_thmss [((Binding.make (compositionN, Position.none), map (composition_proof tname thy) lnames), [Simplifier.simp_add])] thy))
            (* Add independence proofs for each pairing of lenses *)
         |> (fn thy => snd (add_thmss
              [((Binding.make (indepsN, Position.none), map (indep_proof tname thy) (pairings (lnames @ [child_lensN]) @ pairings [base_lensN, child_lensN]) (*@ map (parent_indep_proof_1 tname pname thy plchild) plnames @ map (parent_indep_proof_2 tname pname thy plchild) plnames *) @ pindeps thy), [Simplifier.simp_add])] thy))
            (* Add equivalence properties *)
         |> (fn thy => snd (add_thmss
              [((Binding.make (equivN, Position.none), (if (raw_parent = NONE) then [] else [equiv_more_proof tname pname thy lnames]) @ [equiv_base_proof tname parent thy lnames, equiv_partition_proof tname thy]), [Simplifier.simp_add])] thy))
            (* Add a symmetric lens proof for the base and more lenses *)
         |> (fn thy => snd (add_thm ((Binding.make (all_lensN ^ sym_lens_suffix, Position.none), lens_sym_proof tname thy), [Simplifier.simp_add]) thy)) 
         |> Sign.parent_path
  end;

val _ =
  Outer_Syntax.command @{command_keyword alphabet} "define record with lenses"
    (Parse_Spec.overloaded -- (Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding)
    >> (fn ((overloaded, x), (y, z)) =>
        Toplevel.theory (add_alphabet_cmd {overloaded = overloaded} x y z)));
end