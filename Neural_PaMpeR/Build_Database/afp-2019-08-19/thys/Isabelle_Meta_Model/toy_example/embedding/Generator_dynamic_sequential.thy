(******************************************************************************
 * Citadelle
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

section\<open>Dynamic Meta Embedding with Reflection\<close>

theory Generator_dynamic_sequential
imports Printer
        "../../isabelle_home/src/HOL/Isabelle_Main2"
(*<*)
  keywords (* Toy language *)
           "Between"
           "Attributes" "Operations" "Constraints"
           "Role"
           "Ordered" "Subsets" "Union" "Redefines" "Derived" "Qualifier"
           "Existential" "Inv" "Pre" "Post"
           "self"
           "Nonunique" "Sequence_"

           (* Isabelle syntax *)
           "output_directory"
           "THEORY" "IMPORTS" "SECTION" "SORRY" "no_dirty"
           "deep" "shallow" "syntax_print" "skip_export"
           "generation_semantics"
           "flush_all"

           (* Isabelle semantics (parameterizing the semantics of Toy language) *)
           "design" "analysis" "oid_start"

       and (* Toy language *)
           "Enum"
           "Abstract_class" "Class"
           "Association" "Composition" "Aggregation"
           "Abstract_associationclass" "Associationclass"
           "Context"
           "End" "Instance" "BaseType" "State" "PrePost"

           (* Isabelle syntax *)
           "generation_syntax"

           :: thy_decl
(*>*)
begin

text\<open>In the ``dynamic'' solution: the exportation is automatically handled inside Isabelle/jEdit.
Inputs are provided using the syntax of the Toy Language, and in output
we basically have two options:
\begin{itemize}
\item The first is to generate an Isabelle file for inspection or debugging.
The generated file can interactively be loaded in Isabelle/jEdit, or saved to the hard disk.
This mode is called the ``deep exportation'' mode or shortly the ``deep'' mode.
The aim is to maximally automate the process one is manually performing in
@{file \<open>Generator_static.thy\<close>}.
\item On the other hand, it is also possible to directly execute
in Isabelle/jEdit the generated file from the random access memory.
This mode corresponds to the ``shallow reflection'' mode or shortly ``shallow'' mode.
\end{itemize}
In both modes, the reflection is necessary since the main part used by both
was defined at Isabelle side.
As a consequence, experimentations in ``deep'' and ``shallow'' are performed
without leaving the editing session, in the same as the one the meta-compiler is actually running.\<close>

apply_code_printing_reflect \<open>
  val stdout_file = Unsynchronized.ref ""
\<close> text\<open>This variable is not used in this theory (only in @{file \<open>Generator_static.thy\<close>}),
       but needed for well typechecking the reflected SML code.\<close>

code_reflect' open META
   functions (* executing the compiler as monadic combinators for deep and shallow *)
             fold_thy_deep fold_thy_shallow

             (* printing the HOL AST to (shallow Isabelle) string *)
             write_file

             (* manipulating the compiling environment *)
             compiler_env_config_reset_all
             compiler_env_config_update
             oidInit
             D_output_header_thy_update
             map2_ctxt_term
             check_export_code

             (* printing the TOY AST to (deep Isabelle) string *)
             isabelle_apply isabelle_of_compiler_env_config

subsection\<open>Interface Between the Reflected and the Native\<close>

ML\<open>
 val To_string0 = META.meta_of_logic
\<close>

ML\<open>
structure From = struct
 val string = META.SS_base o META.ST
 val binding = string o Binding.name_of
 (*fun term ctxt s = string (XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt s)))*)
 val internal_oid = META.Oid o Code_Numeral.natural_of_integer
 val option = Option.map
 val list = List.map
 fun pair f1 f2 (x, y) = (f1 x, f2 y)
 fun pair3 f1 f2 f3 (x, y, z) = (f1 x, f2 y, f3 z)

 structure Pure = struct
 val indexname = pair string Code_Numeral.natural_of_integer
 val class = string
 val sort = list class
 fun typ e = (fn
     Type (s, l) => (META.Type o pair string (list typ)) (s, l)
   | TFree (s, s0) => (META.TFree o pair string sort) (s, s0)
   | TVar (i, s0) => (META.TVar o pair indexname sort) (i, s0)
  ) e
 fun term e = (fn
     Const (s, t) => (META.Const o pair string typ) (s, t)
   | Free (s, t) => (META.Free o pair string typ) (s, t)
   | Var (i, t) => (META.Var o pair indexname typ) (i, t)
   | Bound i => (META.Bound o Code_Numeral.natural_of_integer) i
   | Abs (s, ty, t) => (META.Abs o pair3 string typ term) (s, ty, t)
   | op $ (term1, term2) => (META.App o pair term term) (term1, term2)
  ) e
 end

 fun toy_ctxt_term thy expr =
   META.T_pure (Pure.term (Syntax.read_term (Proof_Context.init_global thy) expr))
end
\<close>

ML\<open>fun List_mapi f = META.mapi (f o Code_Numeral.integer_of_natural)\<close>

ML\<open>
structure Ty' = struct
fun check l_oid l =
  let val Mp = META.map_prod
      val Me = String.explode
      val Mi = String.implode
      val Ml = map in
  META.check_export_code
    (writeln o Mi)
    (warning o Mi)
    (fn s => writeln (Markup.markup (Markup.bad ()) (Mi s)))
    (error o To_string0)
    (Ml (Mp I Me) l_oid)
    ((META.SS_base o META.ST) l)
  end
end
\<close>

subsection\<open>Binding of the Reflected API to the Native API\<close>

ML\<open>
structure META_overload = struct
  val of_semi__typ = META.of_semi_typ To_string0
  val of_semi__term = META.of_semi_terma To_string0
  val of_semi__term' = META.of_semi_term To_string0
  val fold = fold
end
\<close>

ML\<open>
structure Bind_Isabelle = struct
fun To_binding s = Binding.make (s, Position.none)
val To_sbinding = To_binding o To_string0

fun semi__method_simp g f = Method.Basic (fn ctxt => SIMPLE_METHOD (g (asm_full_simp_tac (f ctxt))))
val semi__method_simp_one = semi__method_simp (fn f => f 1)
val semi__method_simp_all = semi__method_simp (CHANGED_PROP o PARALLEL_ALLGOALS)

datatype semi__thm' = Thms_single' of thm
                    | Thms_mult' of thm list

fun semi__thm_attribute ctxt = let open META open META_overload val S = fn Thms_single' t => t
                                                         val M = fn Thms_mult' t => t in
 fn Thm_thm s => Thms_single' (Proof_Context.get_thm ctxt (To_string0 s))
  | Thm_thms s => Thms_mult' (Proof_Context.get_thms ctxt (To_string0 s))
  | Thm_THEN (e1, e2) =>
      (case (semi__thm_attribute ctxt e1, semi__thm_attribute ctxt e2) of
         (Thms_single' e1, Thms_single' e2) => Thms_single' (e1 RSN (1, e2))
       | (Thms_mult' e1, Thms_mult' e2) => Thms_mult' (e1 RLN (1, e2)))
  | Thm_simplified (e1, e2) =>
      Thms_single' (asm_full_simplify (clear_simpset ctxt addsimps [S (semi__thm_attribute ctxt e2)])
                                      (S (semi__thm_attribute ctxt e1)))
  | Thm_OF (e1, e2) =>
      Thms_single' ([S (semi__thm_attribute ctxt e2)] MRS (S (semi__thm_attribute ctxt e1)))
  | Thm_where (nth, l) =>
      Thms_single' (Rule_Insts.where_rule
                      ctxt
                      (List.map (fn (var, expr) =>
                                   (((To_string0 var, 0), Position.none), of_semi__term expr)) l)
                      []
                      (S (semi__thm_attribute ctxt nth)))
  | Thm_symmetric e1 =>
      let val e2 = S (semi__thm_attribute ctxt (Thm_thm (From.string "sym"))) in
        case semi__thm_attribute ctxt e1 of
          Thms_single' e1 => Thms_single' (e1 RSN (1, e2))
        | Thms_mult' e1 => Thms_mult' (e1 RLN (1, [e2]))
      end
  | Thm_of (nth, l) =>
      Thms_single' (Rule_Insts.of_rule
                     ctxt
                     (List.map (SOME o of_semi__term) l, [])
                     []
                     (S (semi__thm_attribute ctxt nth)))
end

fun semi__thm_attribute_single ctxt s = case (semi__thm_attribute ctxt s) of Thms_single' t => t

fun semi__thm_mult ctxt =
  let fun f thy = case (semi__thm_attribute ctxt thy) of Thms_mult' t => t
                                                  | Thms_single' t => [t] in
  fn META.Thms_single thy => f thy
   | META.Thms_mult thy => f thy
  end

fun semi__thm_mult_l ctxt l = List.concat (map (semi__thm_mult ctxt) l)

fun semi__method_simp_only l ctxt = clear_simpset ctxt addsimps (semi__thm_mult_l ctxt l)
fun semi__method_simp_add_del_split (l_add, l_del, l_split) ctxt =
  fold Splitter.add_split (semi__thm_mult_l ctxt l_split)
                          (ctxt addsimps (semi__thm_mult_l ctxt l_add)
                                delsimps (semi__thm_mult_l ctxt l_del))

fun semi__method expr = let open META open Method open META_overload in case expr of
    Method_rule o_s => Basic (fn ctxt =>
      METHOD (HEADGOAL o Classical.rule_tac
                           ctxt
                           (case o_s of NONE => []
                                      | SOME s => [semi__thm_attribute_single ctxt s])))
  | Method_drule s => Basic (fn ctxt => drule ctxt 0 [semi__thm_attribute_single ctxt s])
  | Method_erule s => Basic (fn ctxt => erule ctxt 0 [semi__thm_attribute_single ctxt s])
  | Method_elim s => Basic (fn ctxt => elim ctxt [semi__thm_attribute_single ctxt s])
  | Method_intro l => Basic (fn ctxt => intro ctxt (map (semi__thm_attribute_single ctxt) l))
  | Method_subst (asm, l, s) => Basic (fn ctxt =>
      SIMPLE_METHOD' ((if asm then EqSubst.eqsubst_asm_tac else EqSubst.eqsubst_tac)
                        ctxt
                        (map (fn s => case Int.fromString (To_string0 s) of
                                        SOME i => i) l)
                        [semi__thm_attribute_single ctxt s]))
  | Method_insert l => Basic (fn ctxt => insert (semi__thm_mult_l ctxt l))
  | Method_plus t => Combinator ( no_combinator_info
                                , Repeat1
                                , [Combinator (no_combinator_info, Then, List.map semi__method t)])
  | Method_option t => Combinator ( no_combinator_info
                                  , Try
                                  , [Combinator (no_combinator_info, Then, List.map semi__method t)])
  | Method_or t => Combinator (no_combinator_info, Orelse, List.map semi__method t)
  | Method_one (Method_simp_only l) => semi__method_simp_one (semi__method_simp_only l)
  | Method_one (Method_simp_add_del_split l) => semi__method_simp_one (semi__method_simp_add_del_split l)
  | Method_all (Method_simp_only l) => semi__method_simp_all (semi__method_simp_only l)
  | Method_all (Method_simp_add_del_split l) => semi__method_simp_all (semi__method_simp_add_del_split l)
  | Method_auto_simp_add_split (l_simp, l_split) =>
      Basic (fn ctxt => SIMPLE_METHOD (auto_tac (fold (fn (f, l) => fold f l)
              [(Simplifier.add_simp, semi__thm_mult_l ctxt l_simp)
              ,(Splitter.add_split, List.map (Proof_Context.get_thm ctxt o To_string0) l_split)]
              ctxt)))
  | Method_rename_tac l => Basic (K (SIMPLE_METHOD' (Tactic.rename_tac (List.map To_string0 l))))
  | Method_case_tac e =>
      Basic (fn ctxt => SIMPLE_METHOD' (Induct_Tacs.case_tac ctxt (of_semi__term e) [] NONE))
  | Method_blast n =>
      Basic (case n of NONE => SIMPLE_METHOD' o blast_tac
                     | SOME lim => fn ctxt => SIMPLE_METHOD' (depth_tac ctxt (Code_Numeral.integer_of_natural lim)))
  | Method_clarify => Basic (fn ctxt => (SIMPLE_METHOD' (fn i => CHANGED_PROP (clarify_tac ctxt i))))
  | Method_metis (l_opt, l) =>
      Basic (fn ctxt => (METHOD oo Metis_Tactic.metis_method)
                          ( (if l_opt = [] then NONE else SOME (map To_string0 l_opt), NONE)
                          , map (semi__thm_attribute_single ctxt) l)
                          ctxt)
end

fun then_tactic l = let open Method in
  (Combinator (no_combinator_info, Then, map semi__method l), (Position.none, Position.none))
end

fun local_terminal_proof o_by = let open META in case o_by of
   Command_done => Proof.local_done_proof
 | Command_sorry => Proof.local_skip_proof true
 | Command_by l_apply => Proof.local_terminal_proof (then_tactic l_apply, NONE)
end

fun global_terminal_proof o_by = let open META in case o_by of
   Command_done => Proof.global_done_proof
 | Command_sorry => Proof.global_skip_proof true
 | Command_by l_apply => Proof.global_terminal_proof (then_tactic l_apply, NONE)
end

fun proof_show_gen f (thes, thes_when) st = st
  |> Proof.proof
       (SOME ( Method.Source [Token.make_string ("-", Position.none)]
             , (Position.none, Position.none)))
  |> Seq.the_result ""
  |> f
  |> Proof.show_cmd
       (thes_when = [])
       NONE
       (K I)
       []
       (if thes_when = [] then [] else [(Binding.empty_atts, map (fn t => (t, [])) thes_when)])
       [(Binding.empty_atts, [(thes, [])])]
       true
  |> snd

val semi__command_state = let open META_overload in
  fn META.Command_apply_end l => (fn st => st |> Proof.apply_end (then_tactic l)
                                              |> Seq.the_result "")
end

val semi__command_proof = let open META_overload
                        val thesis = "?thesis"
                        fun proof_show f = proof_show_gen f (thesis, []) in
  fn META.Command_apply l => (fn st => st |> Proof.apply (then_tactic l)
                                          |> Seq.the_result "")
   | META.Command_using l => (fn st =>
       let val ctxt = Proof.context_of st in
       Proof.using [map (fn s => ([ s], [])) (semi__thm_mult_l ctxt l)] st
       end)
   | META.Command_unfolding l => (fn st =>
       let val ctxt = Proof.context_of st in
       Proof.unfolding [map (fn s => ([s], [])) (semi__thm_mult_l ctxt l)] st
       end)
   | META.Command_let (e1, e2) =>
       proof_show (Proof.let_bind_cmd [([of_semi__term e1], of_semi__term e2)])
   | META.Command_have (n, b, e, e_pr) => proof_show (fn st => st
       |> Proof.have_cmd true NONE (K I) [] []
                         [( (To_sbinding n, if b then [[Token.make_string ("simp", Position.none)]] else [])
                          , [(of_semi__term e, [])])]
                         true
       |> snd
       |> local_terminal_proof e_pr)
   | META.Command_fix_let (l, l_let, o_exp, _) =>
       proof_show_gen ( fold (fn (e1, e2) =>
                                Proof.let_bind_cmd [([of_semi__term e1], of_semi__term e2)])
                             l_let
                      o Proof.fix_cmd (List.map (fn i => (To_sbinding i, NONE, NoSyn)) l))
                      ( case o_exp of NONE => thesis | SOME (l_spec, _) =>
                         (String.concatWith (" \<Longrightarrow> ")
                                            (List.map of_semi__term l_spec))
                      , case o_exp of NONE => [] | SOME (_, l_when) => List.map of_semi__term l_when)
end

fun semi__theory in_theory in_local = let open META open META_overload in (*let val f = *)fn
  Theory_datatype (Datatype (n, l)) => in_local
   (BNF_FP_Def_Sugar.co_datatype_cmd
      BNF_Util.Least_FP
      BNF_LFP.construct_lfp
      (Ctr_Sugar.default_ctr_options_cmd,
       [( ( ( (([], To_sbinding n), NoSyn)
            , List.map (fn (n, l) => ( ( (To_binding "", To_sbinding n)
                                       , List.map (fn s => (To_binding "", of_semi__typ s)) l)
                                     , NoSyn)) l)
          , (To_binding "", To_binding "", To_binding ""))
        , [])]))
| Theory_type_synonym (Type_synonym (n, v, l)) => in_theory
   (fn thy =>
     let val s_bind = To_sbinding n in
     (snd o Typedecl.abbrev_global
              (s_bind, map To_string0 v, NoSyn)
              (Isabelle_Typedecl.abbrev_cmd0 (SOME s_bind) thy (of_semi__typ l))) thy
     end)
| Theory_type_notation (Type_notation (n, e)) => in_local
   (Specification.type_notation_cmd true ("", true) [(To_string0 n, Mixfix (Input.string (To_string0 e), [], 1000, Position.no_range))])
| Theory_instantiation (Instantiation (n, n_def, expr)) => in_theory
   (fn thy =>
     let val name = To_string0 n
         val tycos =
           [ let val Term.Type (s, _) = (Isabelle_Typedecl.abbrev_cmd0 NONE thy name) in s end ] in
    thy
    |> Class.instantiation (tycos, [], Syntax.read_sort (Proof_Context.init_global thy) "object")
    |> fold_map (fn _ => fn thy =>
        let val ((_, (_, ty)), thy) = Specification.definition_cmd
                                       NONE [] []
                                       ((To_binding (To_string0 n_def ^ "_" ^ name ^ "_def"), [])
                                         , of_semi__term expr) false thy in
         (ty, thy)
        end) tycos
    |-> Class.prove_instantiation_exit_result (map o Morphism.thm) (fn ctxt => fn thms =>
         Class.intro_classes_tac ctxt [] THEN ALLGOALS (Proof_Context.fact_tac ctxt thms))
    |-> K I
     end)
| Theory_overloading (Overloading (n_c, e_c, n, e)) => in_theory
   (fn thy => thy
    |> Overloading.overloading_cmd [(To_string0 n_c, of_semi__term e_c, true)]
    |> snd o Specification.definition_cmd NONE [] [] ((To_sbinding n, []), of_semi__term e) false
    |> Local_Theory.exit_global)
| Theory_consts (Consts (n, ty, symb)) => in_theory
   (Sign.add_consts_cmd [( To_sbinding n
                        , of_semi__typ ty
                        , Mixfix (Input.string ("(_) " ^ To_string0 symb), [], 1000, Position.no_range))])
| Theory_definition def => in_local
    let val (def, e) = case def of
        Definition e => (NONE, e)
      | Definition_where1 (name, (abbrev, prio), e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix (Input.string ("(1" ^ of_semi__term abbrev ^ ")"), [], Code_Numeral.integer_of_natural prio, Position.no_range)), e)
      | Definition_where2 (name, abbrev, e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix (Input.string ("(" ^ of_semi__term abbrev ^ ")"), [], 1000, Position.no_range)), e) in
    (snd o Specification.definition_cmd def [] [] (Binding.empty_atts, of_semi__term e) false)
    end
| Theory_lemmas (Lemmas_simp_thm (simp, s, l)) => in_local
   (fn lthy => (snd o Specification.theorems Thm.theoremK
      [((To_sbinding s, List.map (fn s => Attrib.check_src lthy [Token.make_string (s, Position.none)])
                          (if simp then ["simp", "code_unfold"] else [])),
        List.map (fn x => ([semi__thm_attribute_single lthy x], [])) l)]
      []
      false) lthy)
| Theory_lemmas (Lemmas_simp_thms (s, l)) => in_local
   (fn lthy => (snd o Specification.theorems Thm.theoremK
      [((To_sbinding s, List.map (fn s => Attrib.check_src lthy [Token.make_string (s, Position.none)])
                          ["simp", "code_unfold"]),
        List.map (fn x => (Proof_Context.get_thms lthy (To_string0 x), [])) l)]
      []
      false) lthy)
| Theory_lemma (Lemma (n, l_spec, l_apply, o_by)) => in_local
   (fn lthy =>
           Specification.theorem_cmd true Thm.theoremK NONE (K I)
             Binding.empty_atts [] [] (Element.Shows [((To_sbinding n, [])
                                                       ,[((String.concatWith (" \<Longrightarrow> ")
                                                             (List.map of_semi__term l_spec)), [])])])
             false lthy
        |> fold (semi__command_proof o META.Command_apply) l_apply
        |> global_terminal_proof o_by)
| Theory_lemma (Lemma_assumes (n, l_spec, concl, l_apply, o_by)) => in_local
   (fn lthy => lthy
        |> Specification.theorem_cmd true Thm.theoremK NONE (K I)
             (To_sbinding n, [])
             []
             (List.map (fn (n, (b, e)) =>
                         Element.Assumes [( ( To_sbinding n
                                            , if b then [[Token.make_string ("simp", Position.none)]] else [])
                                          , [(of_semi__term e, [])])])
                       l_spec)
             (Element.Shows [(Binding.empty_atts, [(of_semi__term concl, [])])])
             false
        |> fold semi__command_proof l_apply
        |> (case map_filter (fn META.Command_let _ => SOME []
                              | META.Command_have _ => SOME []
                              | META.Command_fix_let (_, _, _, l) => SOME l
                              | _ => NONE)
                            (rev l_apply) of
              [] => global_terminal_proof o_by
            | _ :: l => let val arg = (NONE, true) in fn st => st
              |> local_terminal_proof o_by
              |> fold (fn l => fold semi__command_state l o Proof.local_qed arg) l
              |> Proof.global_qed arg end))
| Theory_axiomatization (Axiomatization (n, e)) => in_theory
   (#2 o Specification.axiomatization_cmd [] [] [] [((To_sbinding n, []), of_semi__term e)])
| Theory_section _ => in_theory I
| Theory_text _ => in_theory I
| Theory_ML (SML ml) =>
    in_theory (Code_printing.reflect_ml (Input.source false (of_semi__term' ml)
                                                            (Position.none, Position.none)))
| Theory_setup (Setup ml) =>
    in_theory (Isar_Cmd.setup (Input.source false (of_semi__term' ml)
                                                  (Position.none, Position.none)))
| Theory_thm (Thm thm) => in_local
   (fn lthy =>
    let val () =
      writeln
        (Pretty.string_of
          (Proof_Context.pretty_fact lthy ("", List.map (semi__thm_attribute_single lthy) thm))) in
    lthy
    end)
| Theory_interpretation (Interpretation (n, loc_n, loc_param, o_by)) => in_local
   (fn lthy => lthy
    |> Interpretation.interpretation_cmd ( [ ( (To_string0 loc_n, Position.none)
                                         , ( (To_string0 n, true)
                                           , (if loc_param = [] then
                                               Expression.Named []
                                             else
                                               Expression.Positional (map (SOME o of_semi__term)
                                                                          loc_param), [])))]
                                     , [])
    |> global_terminal_proof o_by)
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
end

end

structure Bind_META = struct open Bind_Isabelle

fun all_meta aux ret = let open META open META_overload in fn
  META_semi_theories thy =>
    ret o (case thy of
       Theories_one thy => semi__theory I Named_Target.theory_map thy
     | Theories_locale (data, l) => fn thy => thy
       |> (   Expression.add_locale_cmd
                (To_sbinding (META.holThyLocale_name data))
                Binding.empty
                ([], [])
                (List.concat
                  (map
                    (fn (fixes, assumes) => List.concat
                      [ map (fn (e,ty) => Element.Fixes [( To_binding (of_semi__term e)
                                                         , SOME (of_semi__typ ty)
                                                         , NoSyn)]) fixes
                      , case assumes of NONE => []
                                      | SOME (n, e) => [Element.Assumes [( (To_sbinding n, [])
                                                                         , [(of_semi__term e, [])])]]])
                    (META.holThyLocale_header data)))
           #> snd)
       |> fold (fold (semi__theory Local_Theory.background_theory
                                   (fn f => fn lthy => lthy
                                     |> Local_Theory.new_group
                                     |> f
                                     |> Local_Theory.reset_group))) l
       |> Local_Theory.exit_global)
| META_boot_generation_syntax _ => ret o I
| META_boot_setup_env _ => ret o I
| META_all_meta_embedding meta => fn thy =>
  aux
    (map2_ctxt_term
      (fn T_pure x => T_pure x
        | e =>
          let fun aux e = case e of
            T_to_be_parsed (s, _) => SOME let val t = Syntax.read_term (Proof_Context.init_global thy)
                                                                       (To_string0 s) in
                                          (t, Term.add_frees t [])
                                          end
          | T_lambda (a, e) =>
            Option.map
              (fn (e, l_free) =>
               let val a = To_string0 a
                   val (t, l_free) = case List.partition (fn (x, _) => x = a) l_free of
                                       ([], l_free) => (Term.TFree ("'a", ["HOL.type"]), l_free)
                                     | ([(_, t)], l_free) => (t, l_free) in
               (lambda (Term.Free (a, t)) e, l_free)
               end)
              (aux e)
          | _ => NONE in
          case aux e of
            NONE => error "nested pure expression not expected"
          | SOME (e, _) => META.T_pure (From.Pure.term e)
          end) meta) thy
end

end
\<close>
(*<*)
subsection\<open>Directives of Compilation for Target Languages\<close>

ML\<open>
structure Deep0 = struct

fun apply_hs_code_identifiers ml_module thy =
  let fun mod_hs (fic, ml_module) = Code_Symbol.Module (fic, [("Haskell", SOME ml_module)]) in
  fold (Code_Target.set_identifiers o mod_hs)
    (map (fn x => (Context.theory_name x, ml_module))
         (* list of .hs files that will be merged together in "ml_module" *)
         ( thy
           :: (* we over-approximate the set of compiler files *)
              Context.ancestors_of thy)) thy end

val default_key = ""

structure Export_code_env = struct
  structure Isabelle = struct
    val function = "write_file"
    val argument_main = "main"
  end

  structure Haskell = struct
    val function = "Function"
    val argument = "Argument"
    val main = "Main"
    structure Filename = struct
      fun hs_function ext = function ^ "." ^ ext
      fun hs_argument ext = argument ^ "." ^ ext
      fun hs_main ext = main ^ "." ^ ext
    end
  end

  structure OCaml = struct
    val make = "write"
    structure Filename = struct
      fun function ext = "function." ^ ext
      fun argument ext = "argument." ^ ext
      fun main_fic ext = "main." ^ ext
      fun makefile ext = make ^ "." ^ ext
    end
  end

  structure Scala = struct
    structure Filename = struct
      fun function ext = "Function." ^ ext
      fun argument ext = "Argument." ^ ext
    end
  end

  structure SML = struct
    val main = "Run"
    structure Filename = struct
      fun function ext = "Function." ^ ext
      fun argument ext = "Argument." ^ ext
      fun stdout ext = "Stdout." ^ ext
      fun main_fic ext = main ^ "." ^ ext
    end
  end

  datatype file_input = File
                      | Directory
end

fun compile l cmd =
  let val (l, rc) = fold (fn cmd => (fn (l, 0) =>
                                         let val {out, err, rc, ...} = Bash.process cmd in
                                         ((out, err) :: l, rc) end
                                     | x => x)) l ([], 0)
      val l = rev l in
  if rc = 0 then
    (l, Isabelle_System.bash_output cmd)
  else
    let val () = fold (fn (out, err) => K (warning err; writeln out)) l () in
    error "Compilation failed"
    end
  end

val check =
  fold (fn (cmd, msg) => fn () =>
    let val (out, rc) = Isabelle_System.bash_output cmd in
    if rc = 0 then
      ()
    else
      ( writeln out
      ; error msg)
    end)

val compiler = let open Export_code_env in
  [ let val ml_ext = "hs" in
    ( "Haskell", ml_ext, Directory, Haskell.Filename.hs_function
    , check [("ghc --version", "ghc is not installed (required for compiling a Haskell project)")]
    , (fn mk_fic => fn ml_module => fn mk_free => fn thy =>
        File.write (mk_fic ("Main." ^ ml_ext))
          (String.concatWith "; " [ "import qualified Unsafe.Coerce"
                         , "import qualified " ^ Haskell.function
                         , "import qualified " ^ Haskell.argument
                         , "main :: IO ()"
                         , "main = " ^ Haskell.function ^ "." ^ Isabelle.function ^
                           " (Unsafe.Coerce.unsafeCoerce " ^ Haskell.argument ^ "." ^
                           mk_free (Proof_Context.init_global thy)
                                   Isabelle.argument_main ([]: (string * string) list) ^
                           ")"]))
    , fn tmp_export_code => fn tmp_file =>
        compile [ "mv " ^ tmp_file ^ "/" ^ Haskell.Filename.hs_argument ml_ext ^ " " ^
                          Path.implode tmp_export_code
                , "cd " ^ Path.implode tmp_export_code ^
                  " && ghc -outputdir _build " ^ Haskell.Filename.hs_main ml_ext ]
                (Path.implode (Path.append tmp_export_code (Path.make [Haskell.main]))))
    end
  , let val ml_ext = "ml" in
    ( "OCaml", ml_ext, File, OCaml.Filename.function
    , check [("ocp-build -version", "ocp-build is not installed (required for compiling an OCaml project)")
            ,("ocamlopt -version", "ocamlopt is not installed (required for compiling an OCaml project)")]
    , fn mk_fic => fn ml_module => fn mk_free => fn thy =>
        let val () =
          File.write
            (mk_fic (OCaml.Filename.makefile "ocp"))
            (String.concat
              [ "comp += \"-g\" link += \"-g\" "
              , "begin generated = true begin library \"nums\" end end "
              , "begin program \"", OCaml.make, "\" sort = true files = [ \"", OCaml.Filename.function ml_ext
              , "\" \"", OCaml.Filename.argument ml_ext
              , "\" \"", OCaml.Filename.main_fic ml_ext
              , "\" ]"
              , "requires = [\"nums\"] "
              , "end" ]) in
        File.write (mk_fic (OCaml.Filename.main_fic ml_ext))
          ("let _ = Function." ^ ml_module ^ "." ^ Isabelle.function ^
           " (Obj.magic (Argument." ^ ml_module ^ "." ^
           mk_free (Proof_Context.init_global thy)
                   Isabelle.argument_main
                   ([]: (string * string) list) ^ "))")
        end
    , fn tmp_export_code => fn tmp_file =>
        compile
          [ "mv " ^ tmp_file ^ " " ^
              Path.implode (Path.append tmp_export_code (Path.make [OCaml.Filename.argument ml_ext]))
          , "cd " ^ Path.implode tmp_export_code ^
            " && ocp-build -init -scan -no-bytecode 2>&1" ]
          (Path.implode (Path.append tmp_export_code (Path.make [ "_obuild"
                                                                , OCaml.make
                                                                , OCaml.make ^ ".asm"]))))
    end
  , let val ml_ext = "scala"
        val ml_module = Unsynchronized.ref ("", "") in
    ( "Scala", ml_ext, File, Scala.Filename.function
    , check [("scala -e 0", "scala is not installed (required for compiling a Scala project)")]
    , (fn _ => fn ml_mod => fn mk_free => fn thy =>
        ml_module := (ml_mod, mk_free (Proof_Context.init_global thy)
                                      Isabelle.argument_main
                                      ([]: (string * string) list)))
    , fn tmp_export_code => fn tmp_file =>
        let val l = File.read_lines (Path.explode tmp_file)
            val (ml_module, ml_main) = Unsynchronized.! ml_module
            val () =
              File.write_list
               (Path.append tmp_export_code (Path.make [Scala.Filename.argument ml_ext]))
               (List.map
                 (fn s => s ^ "\n")
                 ("object " ^ ml_module ^ " { def main (__ : Array [String]) = " ^
                  ml_module ^ "." ^ Isabelle.function ^ " (" ^ ml_module ^ "." ^ ml_main ^ ")"
                  :: l @ ["}"])) in
        compile []
          ("scala -nowarn " ^ Path.implode (Path.append tmp_export_code
                                                        (Path.make [Scala.Filename.argument ml_ext])))
        end)
    end
  , let val ml_ext_thy = "thy"
        val ml_ext_ml = "ML" in
    ( "SML", ml_ext_ml, File, SML.Filename.function
    , check [ let val isa = "isabelle" in
              ( Path.implode (Path.expand (Path.append (Path.variable "ISABELLE_HOME") (Path.make ["bin", isa]))) ^ " version"
              , isa ^ " is not installed (required for compiling a SML project)")
              end ]
    , fn mk_fic => fn ml_module => fn mk_free => fn thy =>
         let val esc_star = "*"
             fun ml l =
               List.concat
               [ [ "ML{" ^ esc_star ]
               , map (fn s => s ^ ";") l
               , [ esc_star ^ "}"] ]
             val () =
               let val fic = mk_fic (SML.Filename.function ml_ext_ml) in
               (* replace ("\\" ^ "<") by ("\\\060") in 'fic' *)
               File.write_list fic
                 (map (fn s =>
                         (if s = "" then
                           ""
                         else
                           String.concatWith "\\"
                             (map (fn s =>
                                     let val l = String.size s in
                                     if l > 0 andalso String.sub (s,0) = #"<" then
                                       "\\060" ^ String.substring (s, 1, String.size s - 1)
                                     else
                                       s end)
                                  (String.fields (fn c => c = #"\\") s))) ^ "\n")
                      (File.read_lines fic))
               end in
         File.write_list (mk_fic (SML.Filename.main_fic ml_ext_thy))
           (map (fn s => s ^ "\n") (List.concat
             [ [ "theory " ^ SML.main
               , "imports Main"
               , "begin"
               , "declare [[ML_print_depth = 500]]"
                 (* any large number so that @{make_string} displays all the expression *) ]
             , ml [ "val stdout_file = Unsynchronized.ref (File.read (Path.make [\"" ^
                      SML.Filename.stdout ml_ext_ml ^ "\"]))"
                  , "use \"" ^ SML.Filename.argument ml_ext_ml ^ "\"" ]
             , ml let val arg = "argument" in
                  [ "val " ^ arg ^ " = XML.content_of (YXML.parse_body (@{make_string} (" ^
                    ml_module ^ "." ^
                    mk_free (Proof_Context.init_global thy)
                            Isabelle.argument_main
                            ([]: (string * string) list) ^ ")))"
                  , "use \"" ^ SML.Filename.function ml_ext_ml ^ "\""
                  , "ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags) (Input.source false (\"let open " ^
                      ml_module ^ " in " ^ Isabelle.function ^ " (\" ^ " ^ arg ^
                      " ^ \") end\") (Position.none, Position.none) )" ]
                  end
             , [ "end" ]]))
         end
    , fn tmp_export_code => fn tmp_file =>
        let
            val stdout_file = Isabelle_System.create_tmp_path "stdout_file" "thy"
            val () = File.write (Path.append tmp_export_code (Path.make [SML.Filename.stdout ml_ext_ml]))
                                (Path.implode (Path.expand stdout_file))
            val (l, (_, exit_st)) =
              compile
                [ "mv " ^ tmp_file ^ " " ^ Path.implode (Path.append tmp_export_code
                                                           (Path.make [SML.Filename.argument ml_ext_ml]))
                , "cd " ^ Path.implode tmp_export_code ^
                  " && echo 'use_thy \"" ^ SML.main ^ "\";' | " ^
                  Path.implode (Path.expand (Path.append (Path.variable "ISABELLE_HOME") (Path.make ["bin", "isabelle"]))) ^
                  " console" ]
                "true"
            val stdout =
              case try File.read stdout_file of
                SOME s => let val () = File.rm stdout_file in s end
              | NONE => "" in
            (l, (stdout, if List.exists (fn (err, _) =>
                              List.exists (fn "*** Error" => true | _ => false)
                                (String.tokens (fn #"\n" => true | _ => false) err)) l then
                           let val () = fold (fn (out, err) => K (warning err; writeln out)) l () in
                           1
                           end
                         else exit_st))
        end)
    end ]
end

structure Find = struct
fun ext ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, ext, _, _, _, _, _) => ext

fun export_mode ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, mode, _, _, _, _) => mode

fun function ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, f, _, _, _) => f

fun check_compil ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, build, _, _) => build

fun init ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, _, build, _) => build

fun build ml_compiler =
  case List.find (fn (ml_compiler0, _, _, _, _, _, _) => ml_compiler0 = ml_compiler) compiler of
    SOME (_, _, _, _, _, _, build) => build
end

end
\<close>

ML\<open>
structure Deep = struct

fun absolute_path filename thy =
  Path.implode (Path.append (Resources.master_directory thy) (Path.explode filename))

fun export_code_tmp_file seris g =
  fold
    (fn ((ml_compiler, ml_module), export_arg) => fn f => fn g =>
      f (fn accu =>
        let val tmp_name = Context.theory_name @{theory} in
        (if Deep0.Find.export_mode ml_compiler = Deep0.Export_code_env.Directory then
           Isabelle_System.with_tmp_dir tmp_name
         else
           Isabelle_System.with_tmp_file tmp_name (Deep0.Find.ext ml_compiler))
          (fn filename =>
             g (((((ml_compiler, ml_module), Path.implode filename), export_arg) :: accu)))
        end))
    seris
    (fn f => f [])
    (g o rev)

fun mk_path_export_code tmp_export_code ml_compiler i =
  Path.append tmp_export_code (Path.make [ml_compiler ^ Int.toString i])

fun export_code_cmd' seris tmp_export_code f_err filename_thy raw_cs thy =
  export_code_tmp_file seris
    (fn seris =>
      let val mem_scala = List.exists (fn ((("Scala", _), _), _) => true | _ => false) seris
          val thy' (* FIXME unused *) = Isabelle_Code_Target.export_code_cmd
        false
        (if mem_scala then Deep0.Export_code_env.Isabelle.function :: raw_cs else raw_cs)
        ((map o apfst o apsnd) SOME seris)
        (let val v = Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.argument thy in
         if mem_scala then Code_printing.apply_code_printing v else v end) in
      List_mapi
        (fn i => fn seri => case seri of (((ml_compiler, _), filename), _) =>
          let val (l, (out, err)) =
                Deep0.Find.build
                  ml_compiler
                  (mk_path_export_code tmp_export_code ml_compiler i)
                  filename
              val _ = f_err seri err in
          (l, out)
          end) seris
      end)

fun mk_term ctxt s =
  fst (Scan.pass (Context.Proof ctxt) Args.term (Token.explode0 (Thy_Header.get_keywords' ctxt) s))

fun mk_free ctxt s l =
  let val t_s = mk_term ctxt s in
  if Term.is_Free t_s then s else
    let val l = (s, "") :: l in
    mk_free ctxt (fst (hd (Term.variant_frees t_s l))) l
    end
  end

val list_all_eq = fn x0 :: xs =>
  List.all (fn x1 => x0 = x1) xs

end
\<close>

subsection\<open>Saving the History of Meta Commands\<close>

ML\<open>
fun p_gen f g =  f "[" "]" g
              (*|| f "{" "}" g*)
              || f "(" ")" g
fun paren f = p_gen (fn s1 => fn s2 => fn f => Parse.$$$ s1 |-- f --| Parse.$$$ s2) f
fun parse_l f = Parse.$$$ "[" |-- Parse.!!! (Parse.list f --| Parse.$$$ "]")
fun parse_l' f = Parse.$$$ "[" |-- Parse.list f --| Parse.$$$ "]"
fun parse_l1' f = Parse.$$$ "[" |-- Parse.list1 f --| Parse.$$$ "]"
fun annot_ty f = Parse.$$$ "(" |-- f --| Parse.$$$ "::" -- Parse.binding --| Parse.$$$ ")"
\<close>

ML\<open>
structure Generation_mode = struct

datatype internal_deep = Internal_deep of
    (string * (string list (* imports *) * string (* import optional (bootstrap) *))) option
  * ((bstring (* compiler *) * bstring (* main module *) ) * Token.T list) list (* seri_args *)
  * bstring option (* filename_thy *)
  * Path.T (* tmp dir export_code *)
  * bool (* true: skip preview of code exportation *)

datatype 'a generation_mode = Gen_deep of unit META.compiler_env_config_ext
                                        * internal_deep
                            | Gen_shallow of unit META.compiler_env_config_ext
                                           * 'a (* theory init *)
                            | Gen_syntax_print of int option

structure Data_gen = Theory_Data
  (type T = theory generation_mode list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Parse.args --| @{keyword ")"}) []

val parse_scheme =
  @{keyword "design"} >> K META.Gen_only_design || @{keyword "analysis"} >> K META.Gen_only_analysis

val parse_sorry_mode =
  Scan.optional (  @{keyword "SORRY"} >> K (SOME META.Gen_sorry)
                || @{keyword "no_dirty"} >> K (SOME META.Gen_no_dirty)) NONE

val parse_deep =
     Scan.optional (@{keyword "skip_export"} >> K true) false
  -- Scan.optional (((Parse.$$$ "(" -- @{keyword "THEORY"}) |-- Parse.name -- ((Parse.$$$ ")"
                   -- Parse.$$$ "(" -- @{keyword "IMPORTS"}) |-- parse_l' Parse.name -- Parse.name)
                   --| Parse.$$$ ")") >> SOME) NONE
  -- Scan.optional (@{keyword "SECTION"} >> K true) false
  -- parse_sorry_mode
  -- (* code_expr_inP *) parse_l1' (@{keyword "in"} |-- (Parse.name
        -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
        -- code_expr_argsP))
  -- Scan.optional
       ((Parse.$$$ "(" -- @{keyword "output_directory"}) |-- Parse.name --| Parse.$$$ ")" >> SOME)
       NONE

val parse_semantics =
  let val z = 0 in
      Scan.optional
        (paren (@{keyword "generation_semantics"}
               |-- paren (parse_scheme
                          -- Scan.optional ((Parse.$$$ "," -- @{keyword "oid_start"}) |-- Parse.nat)
                                           z)))
              (META.Gen_default, z)
  end

val mode =
  let fun mk_env output_disable_thy output_header_thy oid_start design_analysis sorry_mode dirty =
    META.compiler_env_config_empty
    output_disable_thy
    (From.option (From.pair From.string (From.pair (From.list From.string) From.string))
                 output_header_thy)
    (META.oidInit (From.internal_oid oid_start))
    design_analysis
    (sorry_mode, dirty) in

     @{keyword "deep"} |-- parse_semantics -- parse_deep >>
     (fn ( (design_analysis, oid_start)
         , ( ((((skip_exportation, output_header_thy), output_disable_thy), sorry_mode), seri_args)
           , filename_thy)) =>
       fn ctxt =>
         Gen_deep ( mk_env (not output_disable_thy)
                           output_header_thy
                           oid_start
                           design_analysis
                           sorry_mode
                           (Config.get ctxt quick_and_dirty)
                  , Internal_deep ( output_header_thy
                                  , seri_args
                                  , filename_thy
                                  , Isabelle_System.create_tmp_path "deep_export_code" ""
                                  , skip_exportation)))
  || @{keyword "shallow"} |-- parse_semantics -- parse_sorry_mode >>
     (fn ((design_analysis, oid_start), sorry_mode) =>
       fn ctxt =>
       Gen_shallow ( mk_env true
                            NONE
                            oid_start
                            design_analysis
                            sorry_mode
                            (Config.get ctxt quick_and_dirty)
                   , ()))
  || (@{keyword "syntax_print"} |-- Scan.optional (Parse.number >> SOME) NONE) >>
     (fn n => K (Gen_syntax_print (case n of NONE => NONE | SOME n => Int.fromString n)))
  end


fun f_command l_mode =
  Toplevel.theory (fn thy =>
  let val (l_mode, thy) = META.mapM
  (fn Gen_shallow (env, ()) => let val thy0 = thy in
                               fn thy => (Gen_shallow (env, thy0), thy) end
    | Gen_syntax_print n => (fn thy => (Gen_syntax_print n, thy))
    | Gen_deep (env, Internal_deep ( output_header_thy
                                   , seri_args
                                   , filename_thy
                                   , tmp_export_code
                                   , skip_exportation)) => fn thy =>
        let val _ =
              warning ("After closing Isabelle/jEdit, we may still need to remove this directory (by hand): " ^
                       Path.implode (Path.expand tmp_export_code))
            val seri_args' = List_mapi (fn i => fn ((ml_compiler, ml_module), export_arg) =>
              let val tmp_export_code = Deep.mk_path_export_code tmp_export_code ml_compiler i
                  fun mk_fic s = Path.append tmp_export_code (Path.make [s])
                  val () = Deep0.Find.check_compil ml_compiler ()
                  val () = Isabelle_System.mkdirs tmp_export_code in
              ((( (ml_compiler, ml_module)
                , Path.implode (if Deep0.Find.export_mode ml_compiler = Deep0.Export_code_env.Directory then
                                  tmp_export_code
                                else
                                  mk_fic (Deep0.Find.function ml_compiler (Deep0.Find.ext ml_compiler))))
                , export_arg), mk_fic)
              end) seri_args
            val thy' (* FIXME unused *) = Isabelle_Code_Target.export_code_cmd
                      (List.exists (fn (((("SML", _), _), _), _) => true | _ => false) seri_args')
                      [Deep0.Export_code_env.Isabelle.function]
                      (List.map ((apfst o apsnd) SOME o fst) seri_args')
                      (Code_printing.apply_code_printing
                        (Deep0.apply_hs_code_identifiers Deep0.Export_code_env.Haskell.function thy))
            val () = fold (fn ((((ml_compiler, ml_module), _), _), mk_fic) => fn _ =>
              Deep0.Find.init ml_compiler mk_fic ml_module Deep.mk_free thy) seri_args' () in
        (Gen_deep (env, Internal_deep ( output_header_thy
                                      , seri_args
                                      , filename_thy
                                      , tmp_export_code
                                      , skip_exportation)), thy) end)
  let val ctxt = Proof_Context.init_global thy in
      map (fn f => f ctxt) l_mode
  end
  thy in
  Data_gen.map (Symtab.map_default (Deep0.default_key, l_mode) (fn _ => l_mode)) thy
  end)

fun update_compiler_config f =
  Data_gen.map
    (Symtab.map_entry
      Deep0.default_key
      (fn l_mode =>
        map (fn Gen_deep (env, d) => Gen_deep (META.compiler_env_config_update f env, d)
              | Gen_shallow (env, thy) => Gen_shallow (META.compiler_env_config_update f env, thy)
              | Gen_syntax_print n => Gen_syntax_print n) l_mode))
end
\<close>

subsection\<open>Factoring All Meta Commands Together\<close>

setup\<open>ML_Antiquotation.inline @{binding mk_string} (Scan.succeed
"(fn ctxt => fn x => ML_Pretty.string_of_polyml (ML_system_pretty (x, FixedInt.fromInt (Config.get ctxt (ML_Print_Depth.print_depth)))))")
\<close>

ML\<open>

fun exec_deep (env, output_header_thy, seri_args, filename_thy, tmp_export_code, l_obj) thy0 =
  let open Generation_mode in
  let val of_arg = META.isabelle_of_compiler_env_config META.isabelle_apply I in
  let fun def s = Named_Target.theory_map (snd o Specification.definition_cmd NONE [] [] (Binding.empty_atts, s) false) in
  let val name_main = Deep.mk_free (Proof_Context.init_global thy0)
                                   Deep0.Export_code_env.Isabelle.argument_main [] in
  thy0
  |> def (String.concatWith " "
          (  "(" (* polymorphism weakening needed by export_code *)
              ^ name_main ^ " :: (_ \<times> abr_string option) compiler_env_config_scheme)"
          :: "="
          :: To_string0
               (of_arg (META.compiler_env_config_more_map
                         (fn () => (l_obj, From.option
                                             From.string
                                             (Option.map (fn filename_thy =>
                                                            Deep.absolute_path filename_thy thy0)
                                                         filename_thy)))
                         env))
          :: []))
  |> Deep.export_code_cmd' seri_args
                           tmp_export_code
                           (fn (((_, _), msg), _) => fn err => if err <> 0 then error msg else ())
                           filename_thy
                           [name_main]
  |> (fn l =>
       let val (l_warn, l) = (map fst l, map snd l) in
       if Deep.list_all_eq l then
         (List.concat l_warn, hd l)
       else
         error "There is an extracted language which does not produce a similar Isabelle content as the others"
       end)
  |> (fn (l_warn, s) =>
       let val () = writeln
         (case (output_header_thy, filename_thy) of
            (SOME _, SOME _) => s
          | _ => String.concat (map ( (fn s => s ^ "\n")
                                    o Active.sendback_markup_command
                                    o trim_line)
             (String.tokens (fn c => c = #"\t") s))) in
       fold (fn (out, err) => K ( writeln (Markup.markup Markup.keyword2 err)
                                ; case trim_line out of
                                    "" => ()
                                  | out => writeln (Markup.markup Markup.keyword1 out)))
            l_warn
            () end)

  end end end end

fun outer_syntax_command0 mk_string cmd_spec cmd_descr parser get_all_meta_embed =
  let open Generation_mode in
  Outer_Syntax.command cmd_spec cmd_descr
    (parser >> (fn name =>
      Toplevel.theory (fn thy =>
        let val (env, thy) =
        META.mapM

          let val get_all_meta_embed = get_all_meta_embed name in
          fn Gen_syntax_print n =>
               (fn thy =>
                  let val _ = writeln
                                (mk_string
                                  (Proof_Context.init_global
                                    (case n of NONE => thy
                                             | SOME n => Config.put_global ML_Print_Depth.print_depth n thy))
                                  name) in
                  (Gen_syntax_print n, thy)
                  end)
           | Gen_deep (env, Internal_deep ( output_header_thy
                                          , seri_args
                                          , filename_thy
                                          , tmp_export_code
                                          , skip_exportation)) =>
              (fn thy0 =>
                let val l_obj = get_all_meta_embed thy0 in
                thy0 |> (if skip_exportation then
                           K ()
                         else
                           exec_deep ( META.d_output_header_thy_update (fn _ => NONE) env
                                     , output_header_thy
                                     , seri_args
                                     , NONE
                                     , tmp_export_code
                                     , l_obj))
                     |> K (Gen_deep ( META.fold_thy_deep l_obj env
                                    , Internal_deep ( output_header_thy
                                                    , seri_args
                                                    , filename_thy
                                                    , tmp_export_code
                                                    , skip_exportation)), thy0)
                end)
           | Gen_shallow (env, thy0) => fn thy =>
             let fun aux (env, thy) x =
                  META.fold_thy_shallow
                   (fn f => f () handle ERROR e =>
                     ( warning "Shallow Backtracking: (true) Isabelle declarations occurring among the META-simulated ones are ignored (if any)"
                       (* TODO automatically determine if there is such Isabelle declarations,
                               for raising earlier a specific error message *)
                     ; error e))
                   (fn _ => fn _ => thy0)
                   (fn l => fn (env, thy) =>
                     Bind_META.all_meta (fn x => fn thy => aux (env, thy) [x]) (pair env) l thy)
                   x
                   (env, thy)
                 val (env, thy) = aux (env, thy) (get_all_meta_embed thy) in
             (Gen_shallow (env, thy0), thy)
             end
          end

          (case Symtab.lookup (Data_gen.get thy) Deep0.default_key of SOME l => l
                                                                    | _ => [Gen_syntax_print NONE])
          thy
        in
        Data_gen.map (Symtab.update (Deep0.default_key, env)) thy end)))
  end

fun outer_syntax_command mk_string cmd_spec cmd_descr parser get_all_meta_embed =
 outer_syntax_command0 mk_string cmd_spec cmd_descr parser (fn a => fn thy => [get_all_meta_embed a thy])

\<close>

subsection\<open>Parameterizing the Semantics of Embedded Languages\<close>

ML\<open>
val () = let open Generation_mode in
  Outer_Syntax.command @{command_keyword generation_syntax} "set the generating list"
    ((   mode >> (fn x => SOME [x])
      || parse_l' mode >> SOME
      || @{keyword "deep"} -- @{keyword "flush_all"} >> K NONE) >>
    (fn SOME x => f_command x
      | NONE =>
      Toplevel.theory (fn thy =>
        let val l = case Symtab.lookup (Data_gen.get thy) Deep0.default_key of SOME l => l | _ => []
            val l = List.concat (List.map (fn Gen_deep x => [x] | _ => []) l)
            val _ = case l of [] => warning "Nothing to perform." | _ => ()
            val thy =
        fold
          (fn (env, Internal_deep (output_header_thy, seri_args, filename_thy, tmp_export_code, _)) => fn thy0 =>
            thy0 |> let val (env, l_exec) = META.compiler_env_config_reset_all env in
                    exec_deep (env, output_header_thy, seri_args, filename_thy, tmp_export_code, l_exec) end
                 |> K thy0)
          l
          thy
        in
        thy end)))
end
\<close>

subsection\<open>Common Parser for Toy\<close>

ML\<open>
structure TOY_parse = struct
  datatype ('a, 'b) use_context = TOY_context_invariant of 'a
                                | TOY_context_pre_post of 'b

  fun optional f = Scan.optional (f >> SOME) NONE
  val colon = Parse.$$$ ":"
  fun repeat2 scan = scan ::: Scan.repeat1 scan

  fun xml_unescape s = (XML.content_of (YXML.parse_body s), Position.none)
                       |> Symbol_Pos.explode |> Symbol_Pos.implode |> From.string

  fun outer_syntax_command2 mk_string cmd_spec cmd_descr parser v_true v_false get_all_meta_embed =
    outer_syntax_command mk_string cmd_spec cmd_descr
      (optional (paren @{keyword "shallow"}) -- parser)
      (fn (is_shallow, use) => fn thy =>
         get_all_meta_embed
           (if is_shallow = NONE then
              ( fn s =>
                  META.T_to_be_parsed ( From.string s
                                     , xml_unescape s)
              , v_true)
            else
              (From.toy_ctxt_term thy, v_false))
           use)

  (* *)

  val ident_dot_dot = let val f = Parse.sym_ident >> (fn "\<bullet>" => "\<bullet>" | _ => Scan.fail "Syntax error") in
                      f -- f end
  val ident_star = Parse.sym_ident (* "*" *)

  (* *)

  val unlimited_natural =  ident_star >> (fn "*" => META.Mult_star
                                           | "\<infinity>" => META.Mult_infinity
                                           | _ => Scan.fail "Syntax error")
                        || Parse.number >> (fn s => META.Mult_nat
                                                      (case Int.fromString s of
                                                         SOME i => Code_Numeral.natural_of_integer i
                                                       | NONE => Scan.fail "Syntax error"))
  val term_base =
       Parse.number >> (META.ToyDefInteger o From.string)
    || Parse.float_number >> (META.ToyDefReal o (From.pair From.string From.string o
         (fn s => case String.tokens (fn #"." => true
                                       | _ => false) s of [l1,l2] => (l1,l2)
                                                        | _ => Scan.fail "Syntax error")))
    || Parse.string >> (META.ToyDefString o From.string)

  val multiplicity = parse_l' (unlimited_natural -- optional (ident_dot_dot |-- unlimited_natural))

  fun toy_term x =
   (   term_base >> META.ShallB_term
    || Parse.binding >> (META.ShallB_str o From.binding)
    || @{keyword "self"} |-- Parse.nat >> (fn n => META.ShallB_self (From.internal_oid n))
    || paren (Parse.list toy_term) >> (* untyped, corresponds to Set, Sequence or Pair *)
                                      (* WARNING for Set: we are describing a finite set *)
                                      META.ShallB_list) x

  val name_object = optional (Parse.list1 Parse.binding --| colon) -- Parse.binding

  val type_object_weak =
    let val name_object = Parse.binding >> (fn s => (NONE, s)) in
                    name_object -- Scan.repeat (Parse.$$$ "<" |-- Parse.list1 name_object) >>
    let val f = fn (_, s) => META.ToyTyCore_pre (From.binding s) in
    fn (s, l) => META.ToyTyObj (f s, map (map f) l)
    end
    end

  val type_object = name_object -- Scan.repeat (Parse.$$$ "<" |-- Parse.list1 name_object) >>
    let val f = fn (_, s) => META.ToyTyCore_pre (From.binding s) in
    fn (s, l) => META.ToyTyObj (f s, map (map f) l)
    end

  val category =
       multiplicity
    -- optional (@{keyword "Role"} |-- Parse.binding)
    -- Scan.repeat (   @{keyword "Ordered"} >> K META.Ordered0
                    || @{keyword "Subsets"} |-- Parse.binding >> K META.Subsets0
                    || @{keyword "Union"} >> K META.Union0
                    || @{keyword "Redefines"} |-- Parse.binding >> K META.Redefines0
                    || @{keyword "Derived"} -- Parse.$$$ "=" |-- Parse.term >> K META.Derived0
                    || @{keyword "Qualifier"} |-- Parse.term >> K META.Qualifier0
                    || @{keyword "Nonunique"} >> K META.Nonunique0
                    || @{keyword "Sequence_"} >> K META.Sequence) >>
    (fn ((l_mult, role), l) =>
       META.Toy_multiplicity_ext (l_mult, From.option From.binding role, l, ()))

  val type_base =   Parse.reserved "Void" >> K META.ToyTy_base_void
                 || Parse.reserved "Boolean" >> K META.ToyTy_base_boolean
                 || Parse.reserved "Integer" >> K META.ToyTy_base_integer
                 || Parse.reserved "UnlimitedNatural" >> K META.ToyTy_base_unlimitednatural
                 || Parse.reserved "Real" >> K META.ToyTy_base_real
                 || Parse.reserved "String" >> K META.ToyTy_base_string

  fun use_type_gen type_object v =
     ((* collection *)
      Parse.reserved "Set" |-- use_type >>
        (fn l => META.ToyTy_collection (META.Toy_multiplicity_ext ([], NONE, [META.Set], ()), l))
   || Parse.reserved "Sequence" |-- use_type >>
        (fn l => META.ToyTy_collection (META.Toy_multiplicity_ext ([], NONE, [META.Sequence], ()), l))
   || category -- use_type >> META.ToyTy_collection

      (* pair *)
   || Parse.reserved "Pair" |--
      (   use_type -- use_type
      || Parse.$$$ "(" |-- use_type --| Parse.$$$ "," -- use_type --| Parse.$$$ ")") >> META.ToyTy_pair

      (* base *)
   || type_base

      (* raw HOL *)
   || Parse.sym_ident (* "\<acute>" *) |-- Parse.typ --| Parse.sym_ident (* "\<acute>" *) >>
        (META.ToyTy_raw o xml_unescape)

      (* object type *)
   || type_object >> META.ToyTy_object

   || ((Parse.$$$ "(" |-- Parse.list (   (Parse.binding --| colon >> (From.option From.binding o SOME))
                                      -- (   Parse.$$$ "(" |-- use_type --| Parse.$$$ ")"
                                          || use_type_gen type_object_weak) >> META.ToyTy_binding
                                      ) --| Parse.$$$ ")"
        >> (fn ty_arg => case rev ty_arg of
              [] => META.ToyTy_base_void
            | ty_arg => fold (fn x => fn acc => META.ToyTy_pair (x, acc))
                             (tl ty_arg)
                             (hd ty_arg)))
       -- optional (colon |-- use_type))
      >> (fn (ty_arg, ty_out) => case ty_out of NONE => ty_arg
                                              | SOME ty_out => META.ToyTy_arrow (ty_arg, ty_out))
   || (Parse.$$$ "(" |-- use_type --| Parse.$$$ ")" >> (fn s => META.ToyTy_binding (NONE, s)))) v
  and use_type x = use_type_gen type_object x

  val use_prop =
   (optional (optional (Parse.binding >> From.binding) --| Parse.$$$ ":") >> (fn NONE => NONE
                                                                               | SOME x => x))
   -- Parse.term --| optional (Parse.$$$ ";") >> (fn (n, e) => fn from_expr =>
                                                  META.ToyProp_ctxt (n, from_expr e))

  (* *)

  val association_end =
       type_object
    -- category
    --| optional (Parse.$$$ ";")

  val association = optional @{keyword "Between"} |-- Scan.optional (repeat2 association_end) []

  val invariant =
         optional @{keyword "Constraints"}
     |-- Scan.optional (@{keyword "Existential"} >> K true) false
     --| @{keyword "Inv"}
     --  use_prop

  structure Outer_syntax_Association = struct
    fun make ass_ty l = META.Toy_association_ext (ass_ty, META.ToyAssRel l, ())
  end

  (* *)

  val context =
    Scan.repeat
      ((   optional (@{keyword "Operations"} || Parse.$$$ "::")
        |-- Parse.binding
        -- use_type
        --| optional (Parse.$$$ "=" |-- Parse.term || Parse.term)
        -- Scan.repeat
              (      (@{keyword "Pre"} || @{keyword "Post"})
                  -- use_prop >> TOY_context_pre_post
               || invariant >> TOY_context_invariant)
        --| optional (Parse.$$$ ";")) >>
              (fn ((name_fun, ty), expr) => fn from_expr =>
                META.Ctxt_pp
                  (META.Toy_ctxt_pre_post_ext
                    ( From.binding name_fun
                    , ty
                    , From.list (fn TOY_context_pre_post (pp, expr) =>
                                     META.T_pp (if pp = "Pre" then
                                                  META.ToyCtxtPre
                                                else
                                                  META.ToyCtxtPost, expr from_expr)
                                 | TOY_context_invariant (b, expr) =>
                                     META.T_invariant (META.T_inv (b, expr from_expr))) expr
                    , ())))
       ||
       invariant >> (fn (b, expr) => fn from_expr => META.Ctxt_inv (META.T_inv (b, expr from_expr))))

  val class =
        optional @{keyword "Attributes"}
    |-- Scan.repeat (Parse.binding --| colon -- use_type
                     --| optional (Parse.$$$ ";"))
    -- context

  datatype use_classDefinition = TOY_class | TOY_class_abstract
  datatype ('a, 'b) use_classDefinition_content = TOY_class_content of 'a | TOY_class_synonym of 'b

  structure Outer_syntax_Class = struct
    fun make from_expr abstract ty_object attribute oper =
      META.Toy_class_raw_ext
        ( ty_object
        , From.list (From.pair From.binding I) attribute
        , From.list (fn f => f from_expr) oper
        , abstract
        , ())
  end

  (* *)

  val term_object = parse_l (   optional (    Parse.$$$ "("
                                          |-- Parse.binding
                                          --| Parse.$$$ ","
                                          -- Parse.binding
                                          --| Parse.$$$ ")"
                                          --| (Parse.sym_ident >> (fn "|=" => Scan.succeed
                                                                    | _ => Scan.fail "")))
                             -- Parse.binding
                             -- (    Parse.$$$ "="
                                 |-- toy_term))

  val list_attr' = term_object >> (fn res => (res, [] : binding list))
  fun object_cast e =
    (   annot_ty term_object
     -- Scan.repeat (    (Parse.sym_ident >> (fn "->" => Scan.succeed
                                               | "\<leadsto>" => Scan.succeed
                                               | "\<rightarrow>" => Scan.succeed
                                               | _ => Scan.fail ""))
                     |-- (   Parse.reserved "toyAsType"
                             |-- Parse.$$$ "("
                             |-- Parse.binding
                             --| Parse.$$$ ")"
                          || Parse.binding)) >> (fn ((res, x), l) => (res, rev (x :: l)))) e
  val object_cast' = object_cast >> (fn (res, l) => (res, rev l))

  fun get_toyinst l _ =
    META.ToyInstance (map (fn ((name,typ), (l_attr, is_cast)) =>
        let val f = map (fn ((pre_post, attr), data) =>
                              ( From.option (From.pair From.binding From.binding) pre_post
                              , ( From.binding attr
                                , data)))
            val l_attr =
              fold
                (fn b => fn acc => META.ToyAttrCast (From.binding b, acc, []))
                is_cast
                (META.ToyAttrNoCast (f l_attr)) in
        META.Toy_instance_single_ext
          (From.option From.binding name, From.option From.binding typ, l_attr, ()) end) l)

  val parse_instance = (Parse.binding >> SOME)
                     -- optional (@{keyword "::"} |-- Parse.binding) --| @{keyword "="}
                     -- (list_attr' || object_cast')

  (* *)

  datatype state_content =
    ST_l_attr of (((binding * binding) option * binding) * META.toy_data_shallow) list * binding list
  | ST_binding of binding

  val state_parse = parse_l' (   object_cast >> ST_l_attr
                              || Parse.binding >> ST_binding)

  fun mk_state thy =
    map (fn ST_l_attr l =>
              META.ToyDefCoreAdd
                (case get_toyinst (map (fn (l_i, l_ty) =>
                                         ((NONE, SOME (hd l_ty)), (l_i, rev (tl l_ty)))) [l])
                                  thy of
                   META.ToyInstance [x] => x)
          | ST_binding b => META.ToyDefCoreBinding (From.binding b))

  (* *)

  datatype state_pp_content = ST_PP_l_attr of state_content list
                            | ST_PP_binding of binding

  val state_pp_parse = state_parse >> ST_PP_l_attr
                       || Parse.binding >> ST_PP_binding

  fun mk_pp_state thy = fn ST_PP_l_attr l => META.ToyDefPPCoreAdd (mk_state thy l)
                         | ST_PP_binding s => META.ToyDefPPCoreBinding (From.binding s)
end
\<close>

subsection\<open>Setup of Meta Commands for Toy: Enum\<close>

ML\<open>
val () =
  outer_syntax_command @{mk_string} @{command_keyword Enum} ""
    (Parse.binding -- parse_l1' Parse.binding)
    (fn (n1, n2) =>
      K (META.META_enum (META.ToyEnum (From.binding n1, From.list From.binding n2))))
\<close>

subsection\<open>Setup of Meta Commands for Toy: (abstract) Class\<close>

ML\<open>
local
  open TOY_parse

  fun mk_classDefinition abstract cmd_spec =
    outer_syntax_command2 @{mk_string} cmd_spec "Class generation"
      (   Parse.binding --| Parse.$$$ "=" -- TOY_parse.type_base >> TOY_class_synonym
       ||    type_object
          -- class >> TOY_class_content)
      (curry META.META_class_raw META.Floor1)
      (curry META.META_class_raw META.Floor2)
      (fn (from_expr, META_class_raw) =>
       fn TOY_class_content (ty_object, (attribute, oper)) =>
            META_class_raw (Outer_syntax_Class.make
                             from_expr
                             (abstract = TOY_class_abstract)
                             ty_object
                             attribute
                             oper)
        | TOY_class_synonym (n1, n2) =>
            META.META_class_synonym (META.ToyClassSynonym (From.binding n1, n2)))
in
val () = mk_classDefinition TOY_class @{command_keyword Class}
val () = mk_classDefinition TOY_class_abstract @{command_keyword Abstract_class}
end
\<close>

subsection\<open>Setup of Meta Commands for Toy: Association, Composition, Aggregation\<close>

ML\<open>
local
  open TOY_parse

  fun mk_associationDefinition ass_ty cmd_spec =
    outer_syntax_command @{mk_string} cmd_spec ""
      (   repeat2 association_end
       ||     optional Parse.binding
          |-- association)
      (fn l => fn _ =>
        META.META_association (Outer_syntax_Association.make ass_ty l))
in
val () = mk_associationDefinition META.ToyAssTy_association @{command_keyword Association}
val () = mk_associationDefinition META.ToyAssTy_composition @{command_keyword Composition}
val () = mk_associationDefinition META.ToyAssTy_aggregation @{command_keyword Aggregation}
end
\<close>

subsection\<open>Setup of Meta Commands for Toy: (abstract) Associationclass\<close>

ML\<open>

local
  open TOY_parse

  datatype use_associationClassDefinition = TOY_associationclass | TOY_associationclass_abstract

  fun mk_associationClassDefinition abstract cmd_spec =
    outer_syntax_command2 @{mk_string} cmd_spec ""
      (   type_object
       -- association
       -- class
       -- optional (Parse.reserved "aggregation" || Parse.reserved "composition"))
      (curry META.META_ass_class META.Floor1)
      (curry META.META_ass_class META.Floor2)
      (fn (from_expr, META_ass_class) =>
       fn (((ty_object, l_ass), (attribute, oper)), assty) =>
          META_ass_class
            (META.ToyAssClass
              ( Outer_syntax_Association.make
                  (case assty of SOME "aggregation" => META.ToyAssTy_aggregation
                               | SOME "composition" => META.ToyAssTy_composition
                               | _ => META.ToyAssTy_association)
                  l_ass
              , Outer_syntax_Class.make
                  from_expr
                  (abstract = TOY_associationclass_abstract)
                  ty_object
                  attribute
                  oper)))
in
val () = mk_associationClassDefinition TOY_associationclass @{command_keyword Associationclass}
val () = mk_associationClassDefinition TOY_associationclass_abstract @{command_keyword Abstract_associationclass}
end
\<close>

subsection\<open>Setup of Meta Commands for Toy: Context\<close>

ML\<open>
local
 open TOY_parse
in
val () =
  outer_syntax_command2 @{mk_string} @{command_keyword Context} ""
    (optional (Parse.list1 Parse.binding --| colon)
     -- Parse.binding
     -- context)
    (curry META.META_ctxt META.Floor1)
    (curry META.META_ctxt META.Floor2)
    (fn (from_expr, META_ctxt) =>
    (fn ((l_param, name), l) =>
    META_ctxt
      (META.Toy_ctxt_ext
        ( case l_param of NONE => [] | SOME l => From.list From.binding l
        , META.ToyTyObj (META.ToyTyCore_pre (From.binding name), [])
        , From.list (fn f => f from_expr) l
        , ()))))
end
\<close>

subsection\<open>Setup of Meta Commands for Toy: End\<close>

ML\<open>
val () =
  outer_syntax_command0 @{mk_string} @{command_keyword End} "Class generation"
    (Scan.optional ( Parse.$$$ "[" -- Parse.reserved "forced" -- Parse.$$$ "]" >> K true
                    || Parse.$$$ "!" >> K true) false)
    (fn b => fn _ =>
       if b then
         [META.META_flush_all META.ToyFlushAll]
       else
         [])
\<close>

subsection\<open>Setup of Meta Commands for Toy: BaseType, Instance, State\<close>

ML\<open>
val () =
  outer_syntax_command @{mk_string} @{command_keyword BaseType} ""
    (parse_l' TOY_parse.term_base)
    (K o META.META_def_base_l o META.ToyDefBase)

local
  open TOY_parse
in
val () =
  outer_syntax_command @{mk_string} @{command_keyword Instance} ""
    (Scan.optional (parse_instance -- Scan.repeat (optional @{keyword "and"} |-- parse_instance) >>
                                                                        (fn (x, xs) => x :: xs)) [])
    (META.META_instance oo get_toyinst)

val () =
  outer_syntax_command @{mk_string} @{command_keyword State} ""
    (TOY_parse.optional (paren @{keyword "shallow"}) -- Parse.binding --| @{keyword "="}
     -- state_parse)
     (fn ((is_shallow, name), l) => fn thy =>
      META.META_def_state
        ( if is_shallow = NONE then META.Floor1 else META.Floor2
        , META.ToyDefSt (From.binding name, mk_state thy l)))
end
\<close>

subsection\<open>Setup of Meta Commands for Toy: PrePost\<close>

ML\<open>
local
  open TOY_parse
in
val () =
  outer_syntax_command @{mk_string} @{command_keyword PrePost} ""
    (TOY_parse.optional (paren @{keyword "shallow"})
     -- TOY_parse.optional (Parse.binding --| @{keyword "="})
     -- state_pp_parse
     -- TOY_parse.optional state_pp_parse)
    (fn (((is_shallow, n), s_pre), s_post) => fn thy =>
      META.META_def_pre_post
        ( if is_shallow = NONE then META.Floor1 else META.Floor2
        , META.ToyDefPP ( From.option From.binding n
                       , mk_pp_state thy s_pre
                       , From.option (mk_pp_state thy) s_post)))
end
(*val _ = print_depth 100*)
\<close>
(*>*)
end
