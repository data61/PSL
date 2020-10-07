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
val child_lens_suffix = "_child_lens"
val vwb_lens_suffix = "_vwb_lens"
val indeps_suffix = "_indeps"
val pl_indeps_suffix = "_pl_indeps"
val sublens_suffix = "_sublenses"
val Trueprop = "HOL.Trueprop"
val imp = "Pure.imp"
val lens_laws_thy = "Lens_Laws"
val lens_algebra_thy = "Lens_Algebra"
val sublens_thy = "Lens_Order"
val vwb_lens = lens_laws_thy ^ ".vwb_lens"
val lens_indep = lens_laws_thy ^ ".lens_indep"
val lens_comp = lens_algebra_thy ^ ".lens_comp"
val sublens = sublens_thy ^ ".sublens"
val lens_suffix = "\<^sub>v"
val ext_suffix = "\<^sub>a"
val lens_defs = (Binding.empty, [Token.make_src ("lens_defs", Position.none) []])
val alpha_splits = [Token.make_src ("alpha_splits", Position.none) []]
val splits_suffix = ".splits"

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

fun lens_proof x thy =
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ (Const (vwb_lens, dummyT) $ Const (Context.theory_name thy ^ "." ^ x, dummyT))]))
      (fn {context = context, prems = _}
         => EVERY [ Locale.intro_locales_tac {strict = true, eager = true} context []
                  , PARALLEL_ALLGOALS (asm_simp_tac (Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def")) context))])

(* Child lenses correspond to the field where a record extension may reside. This function constructs 
  a theorem that a given child lens field is very well-behaved *)

fun lens_child_proof thy x =
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ (Const (vwb_lens, dummyT) $ Const (Context.theory_name thy ^ "." ^ x, dummyT))]))
      (fn {context = context, prems = _} =>
          EVERY [ PARALLEL_ALLGOALS
                    (asm_simp_tac (Simplifier.add_simp @{thm comp_vwb_lens} (Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def")) context)))])

(* Construct a theorem and proof that two lenses, x and y, are independent. Since some lenses exist
   both with the source type as the record extension, and in the context of the extended record
   we need two versions of this function. The first shows it for the lenses on the extension, and
   thus uses an "intro_locales" as a means to discharge the individual lens laws of the vwb_lens
   locale. *)

fun indep_proof thy (x, y) =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (lens_indep, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ x, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ y, dummyT)
                )]))
      (fn {context = context, prems = _}
         => EVERY [ Locale.intro_locales_tac {strict = true, eager = true} context []
                  , PARALLEL_ALLGOALS
                      (asm_simp_tac (Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def"))
                                    (Simplifier.add_simp (Global_Theory.get_thm thy (y ^ "_def"))
                       context)))])

(* The next function is similar, but does not unfold locales instead relying on existing independence
   proofs. The reason for this is that we when invoking this we have already proved that the lenses
   on the extension record are independent, here we just apply preservation of independence of 
   the lenses through composition. *)

fun pl_indep_proof thy (x, y) =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (lens_indep, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ x, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ y, dummyT)
                )]))
      (fn {context = context, prems = _}
                           => EVERY [ PARALLEL_ALLGOALS
                                        (asm_simp_tac (Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def"))
                                                      (Simplifier.add_simp (Global_Theory.get_thm thy (y ^ "_def"))
                                         context)))])

(* The following two functions construct contigent independence proofs for the child lenses: if
  two lenses are independent, then the composition of the two lenses with the child lens from
  their parent must also be independent. *)

fun parent_indep_proof_1 thy y x =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const ("Pure.all", dummyT) $ (Abs ("x", dummyT, (
                Const (imp, dummyT) $
                (Const (Trueprop, dummyT)
                $ ( Const (lens_indep, dummyT)
                  $ Bound 0
                  $ Const (y, dummyT)
                  )
                )
              $
                (Const (Trueprop, dummyT)
                $ ( Const (lens_indep, dummyT)
                  $ Bound 0
                  $ Const (Context.theory_name thy ^ "." ^ x, dummyT)
                  )
                ))))
              ]))
      (fn {context = context, prems = _} =>
          EVERY [(auto_tac (Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def")) context))])

fun parent_indep_proof_2 thy y x =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const ("Pure.all", dummyT) $ (Abs ("x", dummyT, (
                Const (imp, dummyT) $
                (Const (Trueprop, dummyT)
                $ ( Const (lens_indep, dummyT)
                  $ Const (y, dummyT)
                  $ Bound 0
                  )
                )
              $
                (Const (Trueprop, dummyT)
                $ ( Const (lens_indep, dummyT)
                  $ Const (Context.theory_name thy ^ "." ^ x, dummyT)
                  $ Bound 0
                  )
                ))))
              ]))
      (fn {context, prems = _} =>
          EVERY [(auto_tac (Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def")) context))])

(* Prove a theorem that every child lens is a sublens of the parent. *)

fun sublens_proof thy y x =
      Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types
              (Proof_Context.init_global thy)
              [ Const (Trueprop, dummyT)
              $ ( Const (sublens, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ x, dummyT)
                $ Const (y, dummyT)
                )]))
      (fn {context, prems = _} =>
          EVERY [ PARALLEL_ALLGOALS
                    (asm_simp_tac (Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def")) context))])

fun pairWith _ [] = []
  | pairWith x (y :: ys) = [(x, y), (y, x)] @ pairWith x ys;

fun pairings [] = []
  | pairings (x :: xs) = pairWith x xs @ pairings xs;

(* Finally we have the function that actually constructs the record, lenses for each field,
   independence proofs, and also sublens proofs. *)

fun add_alphabet_cmd _ (raw_params, binding) raw_parent raw_fields thy =
  let
    val tname = Binding.name_of binding
    val fields = map (fn (x, y, z) => (Binding.suffix_name lens_suffix x, y, z)) raw_fields
    val lnames = map (fn (x, _, _) => Binding.name_of x) raw_fields
    val (parent, _) = read_parent raw_parent (Proof_Context.init_global thy);
    fun ldef_name x = if (raw_parent = NONE) then x else x ^ ext_suffix
    val ldefs = map (fn x => (ldef_name x) ^ " = " ^ FLDLENS ^ " " ^ x ^ lens_suffix) lnames
    val mpldef =
      case parent of
        SOME (_,r) => tname ^ child_lens_suffix ^ " = " ^ lens_comp ^ " " ^ tname ^ child_lens_suffix ^ ext_suffix ^ " " ^ r ^ child_lens_suffix |
        NONE => ""
    val plchild =
      case parent of
        SOME (_, r) => r ^ child_lens_suffix |
        NONE => ""
    val pldefs =
      case parent of
        SOME (_,r) => map (fn x => x ^ " = " ^ lens_comp ^ " " ^ x ^ ext_suffix ^ " " ^ r ^ child_lens_suffix) lnames @ [mpldef] |
        NONE => [];
    val mldef_name =  if (raw_parent = NONE) then tname ^ child_lens_suffix else tname ^ child_lens_suffix ^ ext_suffix
    val mldef = mldef_name ^ " = " ^ FLDLENS ^ " more";
    val plnames = if (raw_parent = NONE) then [] else lnames  @ [tname ^ child_lens_suffix];
 in thy     (* Add a new record for the new alphabet lenses *)
         |> add_record_cmd {overloaded = false} (raw_params, binding) NONE fields
            (* Add the record splitting theorems to the alpha_splits set for proof automation *)
         |> Named_Target.theory_map (snd o Specification.theorems_cmd "" [((Binding.empty, []), [(Facts.named (tname ^ splits_suffix), alpha_splits)])] [] false)
            (* Add definitions for each of the lenses corresponding to each record field in-situ *)
         |> Named_Target.theory_map
              (fold (fn x => snd o Specification.definition_cmd NONE [] [] (lens_defs, x) true) (ldefs @ [mldef]))
            (* Add definitions for each of the lenses corresponding to each record field augmented with the parent's child lens *)
         |> Named_Target.theory_map
              (fold (fn x => snd o Specification.definition_cmd NONE [] [] (lens_defs, x) true) pldefs)
            (* Add a vwb lens proof for each in-situ lens (i.e. on the record extension) *)
         |> fold (fn x => fn thy => snd (Global_Theory.add_thm ((Binding.make (x ^ vwb_lens_suffix, Position.none), lens_proof x thy), [Simplifier.simp_add]) thy)) ((map ldef_name lnames) @ [mldef_name])
            (* Add independence proofs for each pairing of lenses *)
         |> (fn thy => snd (Global_Theory.add_thmss
              [((Binding.make (Binding.name_of binding ^ indeps_suffix, Position.none), map (indep_proof thy) (pairings ((map ldef_name lnames) @ [mldef_name])) @ map (parent_indep_proof_1 thy plchild) plnames @ map (parent_indep_proof_2 thy plchild) plnames), [Simplifier.simp_add])] thy))
         |> fold (fn x => fn thy => snd (Global_Theory.add_thm ((Binding.make (x ^ vwb_lens_suffix, Position.none), lens_child_proof thy x), [Simplifier.simp_add]) thy)) plnames
         |> (fn thy => snd (Global_Theory.add_thmss
              [((Binding.make (Binding.name_of binding ^ pl_indeps_suffix, Position.none), map (pl_indep_proof thy) (pairings (plnames))), [Simplifier.simp_add])] thy))
         |> (fn thy => snd (Global_Theory.add_thmss [((Binding.make (Binding.name_of binding ^ sublens_suffix, Position.none), map (sublens_proof thy plchild) plnames), [Simplifier.simp_add])] thy))
  end;

val _ =
  Outer_Syntax.command @{command_keyword alphabet} "define record with lenses"
    (Parse_Spec.overloaded -- (Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding)
    >> (fn ((overloaded, x), (y, z)) =>
        Toplevel.theory (add_alphabet_cmd {overloaded = overloaded} x y z)));
end