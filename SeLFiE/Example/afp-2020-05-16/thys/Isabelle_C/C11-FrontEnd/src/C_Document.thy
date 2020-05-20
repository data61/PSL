(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

section \<open>Interface: Ontology Document\<close>

theory C_Document
  imports C_Command
begin

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Thy/thy_output.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Thy/thy_output.ML
    Author:     Makarius

Theory document output.
*)
\<open>
structure C_Thy_Output =
struct

(* output document source *)

val output_symbols = single o Latex.symbols_output;

fun output_comment ctxt (kind, syms) =
  (case kind of
    Comment.Comment =>
      Input.cartouche_content syms
      |> output_document (ctxt |> Config.put Document_Antiquotation.thy_output_display false)
          {markdown = false}
      |> Latex.enclose_body "%\n\\isamarkupcmt{" "%\n}"
  | Comment.Cancel =>
      Symbol_Pos.cartouche_content syms
      |> output_symbols
      |> Latex.enclose_body "%\n\\isamarkupcancel{" "}"
  | Comment.Latex =>
      [Latex.symbols (Symbol_Pos.cartouche_content syms)]
  | Comment.Marker => [])
and output_comment_document ctxt (comment, syms) =
  (case comment of
    SOME kind => output_comment ctxt (kind, syms)
  | NONE => [Latex.symbols syms])
and output_document_text ctxt syms =
  Comment.read_body syms |> maps (output_comment_document ctxt)
and output_document ctxt {markdown} source =
  let
    val pos = Input.pos_of source;
    val syms = Input.source_explode source;

    val output_antiquotes =
      maps (Document_Antiquotation.evaluate (output_document_text ctxt) ctxt);

    fun output_line line =
      (if Markdown.line_is_item line then [Latex.string "\\item "] else []) @
        output_antiquotes (Markdown.line_content line);

    fun output_block (Markdown.Par lines) =
          Latex.block (separate (Latex.string "\n") (map (Latex.block o output_line) lines))
      | output_block (Markdown.List {kind, body, ...}) =
          Latex.environment_block (Markdown.print_kind kind) (output_blocks body)
    and output_blocks blocks = separate (Latex.string "\n\n") (map output_block blocks);
  in
    if Toplevel.is_skipped_proof (Toplevel.presentation_state ctxt) then []
    else if markdown andalso exists (Markdown.is_control o Symbol_Pos.symbol) syms
    then
      let
        val ants = Antiquote.parse_comments pos syms;
        val reports = Antiquote.antiq_reports ants;
        val blocks = Markdown.read_antiquotes ants;
        val _ = Context_Position.reports ctxt (reports @ Markdown.reports blocks);
      in output_blocks blocks end
    else
      let
        val ants = Antiquote.parse_comments pos (trim (Symbol.is_blank o Symbol_Pos.symbol) syms);
        val reports = Antiquote.antiq_reports ants;
        val _ = Context_Position.reports ctxt (reports @ Markdown.text_reports ants);
      in output_antiquotes ants end
  end;


(* output tokens with formal comments *)

local

val output_symbols_antiq =
  (fn Antiquote.Text syms => output_symbols syms
    | Antiquote.Control {name = (name, _), body, ...} =>
        Latex.string (Latex.output_symbols [Symbol.encode (Symbol.Control name)]) ::
          output_symbols body
    | Antiquote.Antiq {body, ...} =>
        Latex.enclose_body "%\n\\isaantiq\n" "{}%\n\\endisaantiq\n" (output_symbols body));

fun output_comment_symbols ctxt {antiq} (comment, syms) =
  (case (comment, antiq) of
    (NONE, false) => output_symbols syms
  | (NONE, true) =>
      Antiquote.parse_comments (#1 (Symbol_Pos.range syms)) syms
      |> maps output_symbols_antiq
  | (SOME comment, _) => output_comment ctxt (comment, syms));

fun output_body ctxt antiq bg en syms =
  Comment.read_body syms
  |> maps (output_comment_symbols ctxt {antiq = antiq})
  |> Latex.enclose_body bg en;

in

fun output_token ctxt tok =
  let
    fun output antiq bg en =
      output_body ctxt antiq bg en (Input.source_explode (C_Token.input_of tok));
  in
    (case C_Token.kind_of tok of
      Token.Comment NONE => []
    | Token.Comment (SOME Comment.Marker) => []
    | Token.Command => output false "\\isacommand{" "}"
    | Token.Keyword =>
        if Symbol.is_ascii_identifier (C_Token.content_of tok)
        then output false "\\isakeyword{" "}"
        else output false "" ""
    | Token.String => output false "{\\isachardoublequoteopen}" "{\\isachardoublequoteclose}"
    | Token.Alt_String => output false "{\\isacharbackquoteopen}" "{\\isacharbackquoteclose}"
    | Token.Verbatim => output true "{\\isacharverbatimopen}" "{\\isacharverbatimclose}"
    | Token.Cartouche => output false "{\\isacartoucheopen}" "{\\isacartoucheclose}"
    | _ => output false "" "")
  end handle ERROR msg => error (msg ^ Position.here (C_Token.pos_of tok));


end;
end;
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Thy/document_antiquotations.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Thy/document_antiquotations.ML
    Author:     Makarius

Miscellaneous document antiquotations.
*)
\<open>
structure C_Document_Antiquotations =
struct

(* quasi-formal text (unchecked) *)

local

fun report_text ctxt text =
  let val pos = Input.pos_of text in
    Context_Position.reports ctxt
      [(pos, Markup.language_text (Input.is_delimited text)),
       (pos, Markup.raw_text)]
  end;

fun prepare_text ctxt =
  Input.source_content #> #1 #> Document_Antiquotation.prepare_lines ctxt;

val theory_text_antiquotation =
  Thy_Output.antiquotation_raw_embedded \<^binding>\<open>C_theory_text\<close> (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let
        val keywords = C_Thy_Header.get_keywords' ctxt;

        val _ = report_text ctxt text;
        val _ =
          Input.source_explode text
          |> C_Token.tokenize keywords {strict = true}
          |> maps (C_Token.reports keywords)
          |> Context_Position.reports_text ctxt;
      in
        prepare_text ctxt text
        |> C_Token.explode0 keywords
        |> maps (C_Thy_Output.output_token ctxt)
        |> Thy_Output.isabelle ctxt
      end);

in

val _ =
  Theory.setup theory_text_antiquotation;

end;

(* C text *)

local

fun c_text name c =
  Thy_Output.antiquotation_verbatim_embedded name (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let val _ = C_Module.eval_in text (SOME (Context.Proof ctxt)) (c text)
      in #1 (Input.source_content text) end);

in

val _ = Theory.setup
 (c_text \<^binding>\<open>C\<close> (C_Module.c_enclose "" "") #>
  c_text \<^binding>\<open>C_text\<close> (K C_Lex.read_init));

end;

end;
\<close>

end
