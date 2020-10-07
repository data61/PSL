(*
 * Copyright 2017, Data61/CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

section "Displaying Phantom Types for Word Operations"

theory Word_Type_Syntax
imports "HOL-Word.Word"
begin

ML \<open>
structure Word_Syntax =
struct

  val show_word_types = Attrib.setup_config_bool @{binding show_word_types} (K true)

  fun tr' cnst ctxt typ ts = if Config.get ctxt show_word_types then
      case (Term.binder_types typ, Term.body_type typ) of
        ([Type (@{type_name "word"}, [S])], Type (@{type_name "word"}, [T])) =>
          list_comb
            (Syntax.const cnst $ Syntax_Phases.term_of_typ ctxt S $ Syntax_Phases.term_of_typ ctxt T
            , ts)
        | _ => raise Match
  else raise Match

end
\<close>


syntax
  "_Ucast" :: "type \<Rightarrow> type \<Rightarrow> logic" ("(1UCAST/(1'(_ \<rightarrow> _')))")
translations
  "UCAST('s \<rightarrow> 't)" => "CONST ucast :: ('s word \<Rightarrow> 't word)"
typed_print_translation
  \<open> [(@{const_syntax ucast}, Word_Syntax.tr' @{syntax_const "_Ucast"})] \<close>


syntax
  "_Scast" :: "type \<Rightarrow> type \<Rightarrow> logic" ("(1SCAST/(1'(_ \<rightarrow> _')))")
translations
  "SCAST('s \<rightarrow> 't)" => "CONST scast :: ('s word \<Rightarrow> 't word)"
typed_print_translation
  \<open> [(@{const_syntax scast}, Word_Syntax.tr' @{syntax_const "_Scast"})] \<close>


syntax
  "_Revcast" :: "type \<Rightarrow> type \<Rightarrow> logic" ("(1REVCAST/(1'(_ \<rightarrow> _')))")
translations
  "REVCAST('s \<rightarrow> 't)" => "CONST revcast :: ('s word \<Rightarrow> 't word)"
typed_print_translation
  \<open> [(@{const_syntax revcast}, Word_Syntax.tr' @{syntax_const "_Revcast"})] \<close>

(* Further candidates for showing word sizes, but with different arities:
   slice, word_cat, word_split, word_rcat, word_rsplit *)

end
