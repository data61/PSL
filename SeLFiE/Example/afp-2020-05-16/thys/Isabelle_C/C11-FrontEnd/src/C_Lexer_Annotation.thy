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

section \<open>Annotation Language: Parsing Combinator\<close>

theory C_Lexer_Annotation
  imports C_Lexer_Language
begin

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/keyword.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Isar/keyword.ML
    Author:     Makarius

Isar keyword classification.
*)
\<open>
structure C_Keyword =
struct

(** keyword classification **)

(* kinds *)


val command_kinds =
  [Keyword.diag, Keyword.document_heading, Keyword.document_body, Keyword.document_raw,
                             Keyword.thy_begin, Keyword.thy_end, Keyword.thy_load, Keyword.thy_decl,
    Keyword.thy_decl_block, Keyword.thy_defn, Keyword.thy_stmt, Keyword.thy_goal,
                      Keyword.thy_goal_defn, Keyword.thy_goal_stmt, Keyword.qed, Keyword.qed_script,
    Keyword.qed_block, Keyword.qed_global, Keyword.prf_goal, Keyword.prf_block, Keyword.next_block,
                                             Keyword.prf_open, Keyword.prf_close, Keyword.prf_chain,
    Keyword.prf_decl, Keyword.prf_asm, Keyword.prf_asm_goal, Keyword.prf_script,
                                              Keyword.prf_script_goal, Keyword.prf_script_asm_goal];


(* specifications *)


type entry =
 {pos: Position.T,
  id: serial,
  kind: string,
  files: string list,  (*extensions of embedded files*)
  tags: string list};

fun check_spec pos ((kind, files), tags) : entry =
  if not (member (op =) command_kinds kind) then
    error ("Unknown annotation syntax keyword kind " ^ quote kind)
  else if not (null files) andalso kind <> Keyword.thy_load then
    error ("Illegal specification of files for " ^ quote kind)
  else {pos = pos, id = serial (), kind = kind, files = files, tags = tags};


(** keyword tables **)

(* type keywords *)

datatype keywords = Keywords of
 {minor: Scan.lexicon,
  major: Scan.lexicon,
  commands: entry Symtab.table};

fun minor_keywords (Keywords {minor, ...}) = minor;
fun major_keywords (Keywords {major, ...}) = major;

fun make_keywords (minor, major, commands) =
  Keywords {minor = minor, major = major, commands = commands};

fun map_keywords f (Keywords {minor, major, commands}) =
  make_keywords (f (minor, major, commands));



(* build keywords *)

val empty_keywords =
  make_keywords (Scan.empty_lexicon, Scan.empty_lexicon, Symtab.empty);

fun empty_keywords' minor =
  make_keywords (minor, Scan.empty_lexicon, Symtab.empty);

fun merge_keywords
  (Keywords {minor = minor1, major = major1, commands = commands1},
    Keywords {minor = minor2, major = major2, commands = commands2}) =
  make_keywords
   (Scan.merge_lexicons (minor1, minor2),
    Scan.merge_lexicons (major1, major2),
    Symtab.merge (K true) (commands1, commands2));

val add_keywords0 =
  fold
    (fn ((name, pos), force_minor, spec as ((kind, _), _)) =>
      map_keywords (fn (minor, major, commands) =>
        let val extend = Scan.extend_lexicon (Symbol.explode name)
            fun update spec = Symtab.update (name, spec)
        in
          if force_minor then
            (extend minor, major, update (check_spec pos spec) commands)
          else if kind = "" orelse kind = Keyword.before_command
                            orelse kind = Keyword.quasi_command then
            (extend minor, major, commands)
          else
            (minor, extend major, update (check_spec pos spec) commands)
        end));

val add_keywords = add_keywords0 o map (fn (cmd, spec) => (cmd, false, spec))
val add_keywords_minor = add_keywords0 o map (fn (cmd, spec) => (cmd, true, spec))


(* keyword status *)

fun is_command (Keywords {commands, ...}) = Symtab.defined commands;
fun dest_commands (Keywords {commands, ...}) = Symtab.keys commands;


(* command keywords *)

fun lookup_command (Keywords {commands, ...}) = Symtab.lookup commands;

fun command_markup keywords name =
  lookup_command keywords name
  |> Option.map (fn {pos, id, ...} =>
      Markup.properties (Position.entity_properties_of false id pos)
        (Markup.entity Markup.command_keywordN name));


fun command_files keywords name path =
  (case lookup_command keywords name of
    NONE => []
  | SOME {kind, files, ...} =>
      if kind <> Keyword.thy_load then []
      else if null files then [path]
      else map (fn ext => Path.ext ext path) files);


(* command categories *)

fun command_category ks =
  let
    val tab = Symtab.make_set ks;
    fun pred keywords name =
      (case lookup_command keywords name of
        NONE => false
      | SOME {kind, ...} => Symtab.defined tab kind);
  in pred end;




val is_theory_end = command_category [Keyword.thy_end];








val is_proof_asm = command_category [Keyword.prf_asm, Keyword.prf_asm_goal];
val is_improper = command_category [ Keyword.qed_script
                                   , Keyword.prf_script
                                   , Keyword.prf_script_goal
                                   , Keyword.prf_script_asm_goal];


end;
\<close>

text \<open> Notes:
  \<^item> The next structure contains a duplicated copy of the type
  \<^ML_type>\<open>Token.T\<close>, since it is not possible to set an arbitrary
  \<^emph>\<open>slot\<close> value in \<^ML_structure>\<open>Token\<close>.

  \<^item> Parsing priorities in C and HOL slightly differ, see for instance
  \<^ML>\<open>Token.explode\<close>.
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/token.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Isar/token.ML
    Author:     Markus Wenzel, TU Muenchen

Outer token syntax for Isabelle/Isar.
*)
\<open>
structure C_Token =
struct

(** tokens **)

(* token kind *)

val immediate_kinds' = fn Token.Command => 0
                        | Token.Keyword => 1
                        | Token.Ident => 2
                        | Token.Long_Ident => 3
                        | Token.Sym_Ident => 4
                        | Token.Var => 5
                        | Token.Type_Ident => 6
                        | Token.Type_Var => 7
                        | Token.Nat => 8
                        | Token.Float => 9
                        | Token.Space => 10
                        | _ => ~1

val delimited_kind =
  (fn Token.String => true
    | Token.Alt_String => true
    | Token.Verbatim => true
    | Token.Cartouche => true
    | Token.Comment _ => true
    | _ => false);


(* datatype token *)

(*The value slot assigns an (optional) internal value to a token,
  usually as a side-effect of special scanner setup (see also
  args.ML).  Note that an assignable ref designates an intermediate
  state of internalization -- it is NOT meant to persist.*)

datatype T = Token of (Symbol_Pos.text * Position.range) * (Token.kind * string) * slot

and slot =
  Slot |
  Value of value option |
  Assignable of value option Unsynchronized.ref

and value =
  Source of T list |
  Literal of bool * Markup.T |
  Name of Token.name_value * morphism |
  Typ of typ |
  Term of term |
  Fact of string option * thm list |  (*optional name for dynamic fact, i.e. fact "variable"*)
  Attribute of morphism -> attribute |
  Declaration of declaration |
  Files of Token.file Exn.result list;

type src = T list;


(* position *)

fun pos_of (Token ((_, (pos, _)), _, _)) = pos;
fun end_pos_of (Token ((_, (_, pos)), _, _)) = pos;

fun adjust_offsets adjust (Token ((x, range), y, z)) =
  Token ((x, apply2 (Position.adjust_offsets adjust) range), y, z);


(* stopper *)

fun mk_eof pos = Token (("", (pos, Position.none)), (Token.EOF, ""), Slot);
val eof = mk_eof Position.none;

fun is_eof (Token (_, (Token.EOF, _), _)) = true
  | is_eof _ = false;

val not_eof = not o is_eof;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_pos_of (List.last toks))) is_eof;


(* kind of token *)

fun kind_of (Token (_, (k, _), _)) = k;
fun is_kind k (Token (_, (k', _), _)) = k = k';

val is_command = is_kind Token.Command;

fun keyword_with pred (Token (_, (Token.Keyword, x), _)) = pred x
  | keyword_with _ _ = false;

val is_command_modifier = keyword_with (fn x => x = "private" orelse x = "qualified");

fun ident_with pred (Token (_, (Token.Ident, x), _)) = pred x
  | ident_with _ _ = false;

fun is_ignored (Token (_, (Token.Space, _), _)) = true
  | is_ignored (Token (_, (Token.Comment NONE, _), _)) = true
  | is_ignored _ = false;

fun is_proper (Token (_, (Token.Space, _), _)) = false
  | is_proper (Token (_, (Token.Comment _, _), _)) = false
  | is_proper _ = true;

fun is_comment (Token (_, (Token.Comment _, _), _)) = true
  | is_comment _ = false;

fun is_informal_comment (Token (_, (Token.Comment NONE, _), _)) = true
  | is_informal_comment _ = false;

fun is_formal_comment (Token (_, (Token.Comment (SOME _), _), _)) = true
  | is_formal_comment _ = false;

fun is_document_marker (Token (_, (Token.Comment (SOME Comment.Marker), _), _)) = true
  | is_document_marker _ = false;

fun is_begin_ignore (Token (_, (Token.Comment NONE, "<"), _)) = true
  | is_begin_ignore _ = false;

fun is_end_ignore (Token (_, (Token.Comment NONE, ">"), _)) = true
  | is_end_ignore _ = false;

fun is_error (Token (_, (Token.Error _, _), _)) = true
  | is_error _ = false;

fun is_error' (Token (_, (Token.Error msg, _), _)) = SOME msg
  | is_error' _ = NONE;

fun content_of (Token (_, (_, x), _)) = x;
fun content_of' (Token (_, (_, _), Value (SOME (Source l)))) =
                    map (fn Token ((_, (pos, _)), (_, x), _) => (x, pos)) l
  | content_of' _ = [];

val is_stack1 = fn Token (_, (Token.Sym_Ident, _), Value (SOME (Source l))) =>
                        forall (fn tok => content_of tok = "+") l
                 | _ => false;

val is_stack2 = fn Token (_, (Token.Sym_Ident, _), Value (SOME (Source l))) =>
                        forall (fn tok => content_of tok = "@") l
                 | _ => false;

val is_stack3 = fn Token (_, (Token.Sym_Ident, _), Value (SOME (Source l))) =>
                        forall (fn tok => content_of tok = "&") l
                 | _ => false;


(* blanks and newlines -- space tokens obey lines *)

fun is_space (Token (_, (Space, _), _)) = true
  | is_space _ = false;

fun is_blank (Token (_, (Space, x), _)) = not (String.isSuffix "\n" x)
  | is_blank _ = false;

fun is_newline (Token (_, (Space, x), _)) = String.isSuffix "\n" x
  | is_newline _ = false;


(* range of tokens *)

fun range_of (toks as tok :: _) =
      let val pos' = end_pos_of (List.last toks)
      in Position.range (pos_of tok, pos') end
  | range_of [] = Position.no_range;

val core_range_of =
  drop_prefix is_ignored #> drop_suffix is_ignored #> range_of;


(* token content *)

fun content_of (Token (_, (_, x), _)) = x;
fun source_of (Token ((source, _), _, _)) = source;

fun input_of (Token ((source, range), (kind, _), _)) =
  Input.source (delimited_kind kind) source range;

fun inner_syntax_of tok =
  let val x = content_of tok
  in if YXML.detect x then x else Syntax.implode_input (input_of tok) end;


(* markup reports *)

local

val token_kind_markup =
 fn Token.Var => (Markup.var, "")
  | Token.Type_Ident => (Markup.tfree, "")
  | Token.Type_Var => (Markup.tvar, "")
  | Token.String => (Markup.string, "")
  | Token.Alt_String => (Markup.alt_string, "")
  | Token.Verbatim => (Markup.verbatim, "")
  | Token.Cartouche => (Markup.cartouche, "")
  | Token.Comment _ => (Markup.ML_comment, "")
  | Token.Error msg => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

fun keyword_reports tok = map (fn markup => ((pos_of tok, markup), ""));

fun command_markups keywords x =
  if C_Keyword.is_theory_end keywords x then [Markup.keyword2 |> Markup.keyword_properties]
  else
    (if C_Keyword.is_proof_asm keywords x then [Markup.keyword3]
     else if C_Keyword.is_improper keywords x then [Markup.keyword1, Markup.improper]
     else [Markup.keyword1])
    |> map Markup.command_properties;

fun keyword_markup (important, keyword) x =
  if important orelse Symbol.is_ascii_identifier x then keyword else Markup.delimiter;

fun command_minor_markups keywords x =
  if C_Keyword.is_theory_end keywords x then [Markup.keyword2 |> Markup.keyword_properties]
  else
    (if C_Keyword.is_proof_asm keywords x then [Markup.keyword3]
     else if C_Keyword.is_improper keywords x then [Markup.keyword1, Markup.improper]
     else if C_Keyword.is_command keywords x then [Markup.keyword1]
     else [keyword_markup (false, Markup.keyword2 |> Markup.keyword_properties) x]);

in

fun completion_report tok =
  if is_kind Token.Keyword tok
  then map (fn m => ((pos_of tok, m), "")) (Completion.suppress_abbrevs (content_of tok))
  else [];

fun reports keywords tok =
  if is_command tok then
    keyword_reports tok (command_markups keywords (content_of tok))
  else if is_stack1 tok orelse is_stack2 tok orelse is_stack3 tok then
    keyword_reports tok [Markup.keyword2 |> Markup.keyword_properties]
  else if is_kind Token.Keyword tok then
    keyword_reports tok (command_minor_markups keywords (content_of tok))
  else
    let
      val pos = pos_of tok;
      val (m, text) = token_kind_markup (kind_of tok);
      val delete = #2 (Symbol_Pos.explode_delete (source_of tok, pos));
    in ((pos, m), text) :: map (fn p => ((p, Markup.delete), "")) delete end;

fun markups keywords = map (#2 o #1) o reports keywords;

end;


(* unparse *)

fun unparse' (Token ((source0, _), (kind, x), _)) =
  let
    val source =
      \<comment> \<open> We are computing a reverse function of \<^ML>\<open>Symbol_Pos.implode_range\<close>
          taking into account consecutive \<^ML>\<open>Symbol.DEL\<close> symbols potentially appearing
          at the beginning, or at the end of the string.

          As remark, \<^ML>\<open>Symbol_Pos.explode_delete\<close>
          will remove any potentially consecutive \<^ML>\<open>Symbol.DEL\<close> symbols.
          This is why it is not used here.\<close>
      case Symbol.explode source0 of
        x :: xs =>
          if x = Symbol.DEL then
            case rev xs of x' :: xs => if x' = Symbol.DEL then implode (rev xs) else source0
                         | _ => source0
          else
           source0
      | _ => source0
  in
    case kind of
      Token.String => Symbol_Pos.quote_string_qq source
    | Token.Alt_String => Symbol_Pos.quote_string_bq source
    | Token.Verbatim => enclose "{*" "*}" source
    | Token.Cartouche => cartouche source
    | Token.Comment NONE => enclose "(*" "*)" source
    | Token.EOF => ""
    | _ => x
  end;

fun text_of tok =
  let
    val k = Token.str_of_kind (kind_of tok);
    val ms = markups C_Keyword.empty_keywords tok;
    val s = unparse' tok;
  in
    if s = "" then (k, "")
    else if size s < 40 andalso not (exists_string (fn c => c = "\n") s)
    then (k ^ " " ^ Markup.markups ms s, "")
    else (k, Markup.markups ms s)
  end;



(** associated values **)

(* inlined file content *)

fun file_source (file: Token.file) =
  let
    val text = cat_lines (#lines file);
    val end_pos = fold Position.advance (Symbol.explode text) (#pos file);
  in Input.source true text (Position.range (#pos file, end_pos)) end;

fun get_files (Token (_, _, Value (SOME (Files files)))) = files
  | get_files _ = [];

fun put_files [] tok = tok
  | put_files files (Token (x, y, Slot)) = Token (x, y, Value (SOME (Files files)))
  | put_files _ tok = raise Fail ("Cannot put inlined files here" ^ Position.here (pos_of tok));


(* access values *)



(* reports of value *)



(* name value *)



(* maxidx *)



(* fact values *)



(* transform *)



(* static binding *)

(*1st stage: initialize assignable slots*)
fun init_assignable tok =
  (case tok of
    Token (x, y, Slot) => Token (x, y, Assignable (Unsynchronized.ref NONE))
  | Token (_, _, Value _) => tok
  | Token (_, _, Assignable r) => (r := NONE; tok));

(*2nd stage: assign values as side-effect of scanning*)
fun assign v tok =
  (case tok of
    Token (x, y, Slot) => Token (x, y, Value v)
  | Token (_, _, Value _) => tok
  | Token (_, _, Assignable r) => (r := v; tok));

fun evaluate mk eval arg =
  let val x = eval arg in (assign (SOME (mk x)) arg; x) end;

(*3rd stage: static closure of final values*)
fun closure (Token (x, y, Assignable (Unsynchronized.ref v))) = Token (x, y, Value v)
  | closure tok = tok;


(* pretty *)



(* src *)







(** scanners **)

open Basic_Symbol_Pos;

val err_prefix = "Annotation lexical error: ";

fun !!! msg = Symbol_Pos.!!! (fn () => err_prefix ^ msg);


(* scan stack *)

fun scan_stack is_stack = Scan.optional (Scan.one is_stack >> content_of') []


(* scan symbolic idents *)

val scan_symid =
  Scan.many1 (Symbol.is_symbolic_char o Symbol_Pos.symbol) ||
  Scan.one (Symbol.is_symbolic o Symbol_Pos.symbol) >> single;

fun is_symid str =
  (case try Symbol.explode str of
    SOME [s] => Symbol.is_symbolic s orelse Symbol.is_symbolic_char s
  | SOME ss => forall Symbol.is_symbolic_char ss
  | _ => false);

fun ident_or_symbolic "begin" = false
  | ident_or_symbolic ":" = true
  | ident_or_symbolic "::" = true
  | ident_or_symbolic s = Symbol_Pos.is_identifier s orelse is_symid s;


(* scan verbatim text *)

val scan_verb =
  $$$ "*" --| Scan.ahead (~$$ "}") ||
  Scan.one (fn (s, _) => s <> "*" andalso Symbol.not_eof s) >> single;

val scan_verbatim =
  Scan.ahead ($$ "{" -- $$ "*") |--
    !!! "unclosed verbatim text"
      ((Symbol_Pos.scan_pos --| $$ "{" --| $$ "*") --
        (Scan.repeats scan_verb -- ($$ "*" |-- $$ "}" |-- Symbol_Pos.scan_pos)));

val recover_verbatim =
  $$$ "{" @@@ $$$ "*" @@@ Scan.repeats scan_verb;


(* scan cartouche *)

val scan_cartouche =
  Symbol_Pos.scan_pos --
    ((Symbol_Pos.scan_cartouche err_prefix >> Symbol_Pos.cartouche_content) -- Symbol_Pos.scan_pos);


(* scan space *)

fun space_symbol (s, _) = Symbol.is_blank s andalso s <> "\n";

val scan_space =
  Scan.many1 space_symbol @@@ Scan.optional ($$$ "\n") [] ||
  Scan.many space_symbol @@@ $$$ "\n";


(* scan comment *)

val scan_comment =
  Symbol_Pos.scan_pos -- (Symbol_Pos.scan_comment_body err_prefix -- Symbol_Pos.scan_pos);



(** token sources **)

local

fun token_leq ((_, syms1), (_, syms2)) = length syms1 <= length syms2;

fun token k ss =
  Token ((Symbol_Pos.implode ss, Symbol_Pos.range ss), (k, Symbol_Pos.content ss), Slot);

fun token' (mk_value, k) ss =
  if mk_value then
    Token ( (Symbol_Pos.implode ss, Symbol_Pos.range ss)
          , (k, Symbol_Pos.content ss)
          , Value (SOME (Source (map (fn (s, pos) =>
                                       Token (("", (pos, Position.none)), (k, s), Slot))
                                     ss))))
  else
    token k ss;

fun token_t k = token' (true, k)

fun token_range k (pos1, (ss, pos2)) =
  Token (Symbol_Pos.implode_range (pos1, pos2) ss, (k, Symbol_Pos.content ss), Slot);

fun scan_token keywords = !!! "bad input"
  (Symbol_Pos.scan_string_qq err_prefix >> token_range Token.String ||
    Symbol_Pos.scan_string_bq err_prefix >> token_range Token.Alt_String ||
    scan_verbatim >> token_range Token.Verbatim ||
    scan_cartouche >> token_range Token.Cartouche ||
    scan_comment >> token_range (Token.Comment NONE) ||
    Comment.scan_outer >> (fn (k, ss) => token (Token.Comment (SOME k)) ss) ||
    scan_space >> token Token.Space ||
    Scan.repeats1 ($$$ "+") >> token_t Token.Sym_Ident ||
    Scan.repeats1 ($$$ "@") >> token_t Token.Sym_Ident ||
    Scan.repeats1 ($$$ "&") >> token_t Token.Sym_Ident ||
    (Scan.max token_leq
      (Scan.max token_leq
        (Scan.literal (C_Keyword.major_keywords keywords) >> pair Token.Command)
        (Scan.literal (C_Keyword.minor_keywords keywords) >> pair Token.Keyword))
      (Lexicon.scan_longid >> pair Token.Long_Ident ||
        Scan.max
          token_leq
          (C_Lex.scan_ident >> pair Token.Ident)
          (Lexicon.scan_id >> pair Token.Ident) ||
        Lexicon.scan_var >> pair Token.Var ||
        Lexicon.scan_tid >> pair Token.Type_Ident ||
        Lexicon.scan_tvar >> pair Token.Type_Var ||
        Symbol_Pos.scan_float >> pair Token.Float ||
        Symbol_Pos.scan_nat >> pair Token.Nat ||
        scan_symid >> pair Token.Sym_Ident)) >> uncurry (token' o pair false));

fun recover msg =
  (Symbol_Pos.recover_string_qq ||
    Symbol_Pos.recover_string_bq ||
    recover_verbatim ||
    Symbol_Pos.recover_cartouche ||
    Symbol_Pos.recover_comment ||
    Scan.one (Symbol.not_eof o Symbol_Pos.symbol) >> single)
  >> (single o token (Token.Error msg));

in

fun make_source keywords {strict} =
  let
    val scan_strict = Scan.bulk (scan_token keywords);
    val scan = if strict then scan_strict else Scan.recover scan_strict recover;
  in Source.source Symbol_Pos.stopper scan end;


end;


(* explode *)

fun tokenize keywords strict syms =
  Source.of_list syms |> make_source keywords strict |> Source.exhaust;

fun explode keywords pos text =
  Symbol_Pos.explode (text, pos) |> tokenize keywords {strict = false};

fun explode0 keywords = explode keywords Position.none;


(* print name in parsable form *)



(* make *)




(** parsers **)

type 'a parser = T list -> 'a * T list;
type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list);


(* read body -- e.g. antiquotation source *)

fun read_with_commands'0 keywords syms =
  Source.of_list syms
  |> make_source keywords {strict = false}
  |> Source.filter (not o is_proper)
  |> Source.exhaust

fun read_with_commands' keywords scan syms =
  Source.of_list syms
  |> make_source keywords {strict = false}
  |> Source.filter is_proper
  |> Source.source
       stopper
       (Scan.recover
         (Scan.bulk scan)
         (fn msg =>
           Scan.one (not o is_eof)
           >> (fn tok => [C_Scan.Right
                           let
                             val msg = case is_error' tok of SOME msg0 => msg0 ^ " (" ^ msg ^ ")"
                                                           | NONE => msg
                           in ( msg
                              , [((pos_of tok, Markup.bad ()), msg)]
                              , tok)
                           end])))
  |> Source.exhaust;

fun read_antiq' keywords scan = read_with_commands' keywords (scan >> C_Scan.Left);

(* wrapped syntax *)

local
fun make src pos = Token.make src pos |> #1
fun make_default text pos = make ((~1, 0), text) pos
fun explode keywords pos text =
  case Token.explode keywords pos text of [tok] => tok
                                        | _ => make_default text pos
in
fun syntax' f =
  I #> map
   (fn tok0 as Token ((source, (pos1, pos2)), (kind, x), _) =>
    if is_stack1 tok0 orelse is_stack2 tok0 orelse is_stack3 tok0 then
      make_default source pos1
    else if is_eof tok0 then
      Token.eof
    else if delimited_kind kind then
      explode Keyword.empty_keywords pos1 (unparse' tok0)
    else
      let
        val tok1 =
          explode
            ((case kind of
                Token.Keyword => Keyword.add_keywords [((x, Position.none), Keyword.no_spec)]
              | Token.Command => Keyword.add_keywords [( (x, Position.none)
                                                       , ((Keyword.thy_decl, []), []))]
              | _ => I)
               Keyword.empty_keywords)
            pos1
            source
      in
        if Token.kind_of tok1 = kind then
          tok1
        else
          make ( ( immediate_kinds' kind
                 , case Position.distance_of (pos1, pos2) of NONE => 0 | SOME i => i)
               , source)
               pos1
      end)
    #> f
    #> apsnd (map (fn tok => Token ( (Token.source_of tok, Token.range_of [tok])
                                   , (Token.kind_of tok, Token.content_of tok)
                                   , Slot)))
end
end;

type 'a c_parser = 'a C_Token.parser;
type 'a c_context_parser = 'a C_Token.context_parser;
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/parse.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Isar/parse.ML
    Author:     Markus Wenzel, TU Muenchen

Generic parsers for Isabelle/Isar outer syntax.
*)
\<open>
signature C_PARSE =
sig
  type T
  type src = T list
  type 'a parser = T list -> 'a * T list
  type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list)
(**)
  val C_source: Input.source parser
  val star: string parser
(**)
  val group: (unit -> string) -> (T list -> 'a) -> T list -> 'a
  val !!! : (T list -> 'a) -> T list -> 'a
  val !!!! : (T list -> 'a) -> T list -> 'a
  val not_eof: T parser
  val token: 'a parser -> T parser
  val range: 'a parser -> ('a * Position.range) parser
  val position: 'a parser -> ('a * Position.T) parser
  val input: 'a parser -> Input.source parser
  val inner_syntax: 'a parser -> string parser
  val command: string parser
  val keyword: string parser
  val short_ident: string parser
  val long_ident: string parser
  val sym_ident: string parser
  val dots: string parser
  val minus: string parser
  val term_var: string parser
  val type_ident: string parser
  val type_var: string parser
  val number: string parser
  val float_number: string parser
  val string: string parser
  val string_position: (string * Position.T) parser
  val alt_string: string parser
  val verbatim: string parser
  val cartouche: string parser
  val eof: string parser
  val command_name: string -> string parser
  val keyword_with: (string -> bool) -> string parser
  val keyword_markup: bool * Markup.T -> string -> string parser
  val keyword_improper: string -> string parser
  val $$$ : string -> string parser
  val reserved: string -> string parser
  val underscore: string parser
  val maybe: 'a parser -> 'a option parser
  val maybe_position: ('a * Position.T) parser -> ('a option * Position.T) parser
  val opt_keyword: string -> bool parser
  val opt_bang: bool parser
  val begin: string parser
  val opt_begin: bool parser
  val nat: int parser
  val int: int parser
  val real: real parser
  val enum_positions: string -> 'a parser -> ('a list * Position.T list) parser
  val enum1_positions: string -> 'a parser -> ('a list * Position.T list) parser
  val enum: string -> 'a parser -> 'a list parser
  val enum1: string -> 'a parser -> 'a list parser
  val and_list: 'a parser -> 'a list parser
  val and_list1: 'a parser -> 'a list parser
  val enum': string -> 'a context_parser -> 'a list context_parser
  val enum1': string -> 'a context_parser -> 'a list context_parser
  val and_list': 'a context_parser -> 'a list context_parser
  val and_list1': 'a context_parser -> 'a list context_parser
  val list: 'a parser -> 'a list parser
  val list1: 'a parser -> 'a list parser
  val properties: Properties.T parser
  val name: string parser
  val name_range: (string * Position.range) parser
  val name_position: (string * Position.T) parser
  val binding: binding parser
  val embedded: string parser
  val embedded_input: Input.source parser
  val embedded_position: (string * Position.T) parser
  val text: string parser
  val path: string parser
  val path_binding: (string * Position.T) parser
  val session_name: (string * Position.T) parser
  val theory_name: (string * Position.T) parser
  val liberal_name: string parser
  val parname: string parser
  val parbinding: binding parser
  val class: string parser
  val sort: string parser
  val type_const: string parser
  val arity: (string * string list * string) parser
  val multi_arity: (string list * string list * string) parser
  val type_args: string list parser
  val type_args_constrained: (string * string option) list parser
  val typ: string parser
  val mixfix: mixfix parser
  val mixfix': mixfix parser
  val opt_mixfix: mixfix parser
  val opt_mixfix': mixfix parser
  val syntax_mode: Syntax.mode parser
  val where_: string parser
  val const_decl: (string * string * mixfix) parser
  val const_binding: (binding * string * mixfix) parser
  val params: (binding * string option * mixfix) list parser
  val vars: (binding * string option * mixfix) list parser
  val for_fixes: (binding * string option * mixfix) list parser
  val ML_source: Input.source parser
  val document_source: Input.source parser
  val document_marker: Input.source parser
  val const: string parser
  val term: string parser
  val prop: string parser
  val literal_fact: string parser
  val propp: (string * string list) parser
  val termp: (string * string list) parser
  val private: Position.T parser
  val qualified: Position.T parser
  val target: (string * Position.T) parser
  val opt_target: (string * Position.T) option parser
  val args: T list parser
  val args1: (string -> bool) -> T list parser
  val attribs: src list parser
  val opt_attribs: src list parser
  val thm_sel: Facts.interval list parser
  val thm: (Facts.ref * src list) parser
  val thms1: (Facts.ref * src list) list parser
  val options: ((string * Position.T) * (string * Position.T)) list parser
end;

structure C_Parse: C_PARSE =
struct
type T = C_Token.T
type src = T list
type 'a parser = T list -> 'a * T list
type 'a context_parser = Context.generic * T list -> 'a * (Context.generic * T list)
structure Token =
struct
  open Token
  open C_Token
end

(** error handling **)

(* group atomic parsers (no cuts!) *)

fun group s scan = scan || Scan.fail_with
  (fn [] => (fn () => s () ^ " expected,\nbut end-of-input was found")
    | tok :: _ =>
        (fn () =>
          (case Token.text_of tok of
            (txt, "") =>
              s () ^ " expected,\nbut " ^ txt ^ Position.here (Token.pos_of tok) ^
              " was found"
          | (txt1, txt2) =>
              s () ^ " expected,\nbut " ^ txt1 ^ Position.here (Token.pos_of tok) ^
              " was found:\n" ^ txt2)));


(* cut *)

fun cut kind scan =
  let
    fun get_pos [] = " (end-of-input)"
      | get_pos (tok :: _) = Position.here (Token.pos_of tok);

    fun err (toks, NONE) = (fn () => kind ^ get_pos toks)
      | err (toks, SOME msg) =
          (fn () =>
            let val s = msg () in
              if String.isPrefix kind s then s
              else kind ^ get_pos toks ^ ": " ^ s
            end);
  in Scan.!! err scan end;

fun !!! scan = cut "Annotation syntax error" scan;
fun !!!! scan = cut "Corrupted annotation syntax in presentation" scan;



(** basic parsers **)

(* tokens *)

fun RESET_VALUE atom = (*required for all primitive parsers*)
  Scan.ahead (Scan.one (K true)) -- atom >> (fn (arg, x) => (Token.assign NONE arg; x));


val not_eof = RESET_VALUE (Scan.one Token.not_eof);

fun token atom = Scan.ahead not_eof --| atom;

fun range scan = (Scan.ahead not_eof >> (Token.range_of o single)) -- scan >> Library.swap;
fun position scan = (Scan.ahead not_eof >> Token.pos_of) -- scan >> Library.swap;
fun input atom = Scan.ahead atom |-- not_eof >> Token.input_of;
fun inner_syntax atom = Scan.ahead atom |-- not_eof >> Token.inner_syntax_of;

fun kind k =
  group (fn () => Token.str_of_kind k)
    (RESET_VALUE (Scan.one (Token.is_kind k) >> Token.content_of));

val command = kind Token.Command;
val keyword = kind Token.Keyword;
val short_ident = kind Token.Ident;
val long_ident = kind Token.Long_Ident;
val sym_ident = kind Token.Sym_Ident;
val term_var = kind Token.Var;
val type_ident = kind Token.Type_Ident;
val type_var = kind Token.Type_Var;
val number = kind Token.Nat;
val float_number = kind Token.Float;
val string = kind Token.String;
val alt_string = kind Token.Alt_String;
val verbatim = kind Token.Verbatim;
val cartouche = kind Token.Cartouche;
val eof = kind Token.EOF;

fun command_name x =
  group (fn () => Token.str_of_kind Token.Command ^ " " ^ quote x)
    (RESET_VALUE (Scan.one (fn tok => Token.is_command tok andalso Token.content_of tok = x)))
  >> Token.content_of;

fun keyword_with pred = RESET_VALUE (Scan.one (Token.keyword_with pred) >> Token.content_of);

fun keyword_markup markup x =
  group (fn () => Token.str_of_kind Token.Keyword ^ " " ^ quote x)
    (Scan.ahead not_eof -- keyword_with (fn y => x = y))
  >> (fn (tok, x) => (Token.assign (SOME (Token.Literal markup)) tok; x));

val keyword_improper = keyword_markup (true, Markup.improper);
val $$$ = keyword_markup (false, Markup.quasi_keyword);

fun reserved x =
  group (fn () => "reserved identifier " ^ quote x)
    (RESET_VALUE (Scan.one (Token.ident_with (fn y => x = y)) >> Token.content_of));

val dots = sym_ident :-- (fn "\<dots>" => Scan.succeed () | _ => Scan.fail) >> #1;

val minus = sym_ident :-- (fn "-" => Scan.succeed () | _ => Scan.fail) >> #1;

val underscore = sym_ident :-- (fn "_" => Scan.succeed () | _ => Scan.fail) >> #1;
fun maybe scan = underscore >> K NONE || scan >> SOME;
fun maybe_position scan = position (underscore >> K NONE) || scan >> apfst SOME;

val nat = number >> (#1 o Library.read_int o Symbol.explode);
val int = Scan.optional (minus >> K ~1) 1 -- nat >> op *;
val real = float_number >> Value.parse_real || int >> Real.fromInt;

fun opt_keyword s = Scan.optional ($$$ "(" |-- !!! (($$$ s >> K true) --| $$$ ")")) false;
val opt_bang = Scan.optional ($$$ "!" >> K true) false;

val begin = $$$ "begin";
val opt_begin = Scan.optional (begin >> K true) false;


(* enumerations *)

fun enum1_positions sep scan =
  scan -- Scan.repeat (position ($$$ sep) -- !!! scan) >>
    (fn (x, ys) => (x :: map #2 ys, map (#2 o #1) ys));
fun enum_positions sep scan =
  enum1_positions sep scan || Scan.succeed ([], []);

fun enum1 sep scan = scan ::: Scan.repeat ($$$ sep |-- !!! scan);
fun enum sep scan = enum1 sep scan || Scan.succeed [];

fun enum1' sep scan = scan ::: Scan.repeat (Scan.lift ($$$ sep) |-- scan);
fun enum' sep scan = enum1' sep scan || Scan.succeed [];

fun and_list1 scan = enum1 "and" scan;
fun and_list scan = enum "and" scan;

fun and_list1' scan = enum1' "and" scan;
fun and_list' scan = enum' "and" scan;

fun list1 scan = enum1 "," scan;
fun list scan = enum "," scan;

val properties = $$$ "(" |-- !!! (list (string -- ($$$ "=" |-- string)) --| $$$ ")");


(* names and embedded content *)

val name =
  group (fn () => "name")
    (short_ident || long_ident || sym_ident || number || string);

val name_range = input name >> Input.source_content_range;
val name_position = input name >> Input.source_content;

val string_position = input string >> Input.source_content;

val binding = name_position >> Binding.make;

val embedded =
  group (fn () => "embedded content")
    (cartouche || string || short_ident || long_ident || sym_ident ||
      term_var || type_ident || type_var || number);

val embedded_input = input embedded;
val embedded_position = embedded_input >> Input.source_content;

val text = group (fn () => "text") (embedded || verbatim);

val path = group (fn () => "file name/path specification") embedded;
val path_binding = group (fn () => "path binding (strict file name)") (position embedded);

val session_name = group (fn () => "session name") name_position;
val theory_name = group (fn () => "theory name") name_position;

val liberal_name = keyword_with Token.ident_or_symbolic || name;

val parname = Scan.optional ($$$ "(" |-- name --| $$$ ")") "";
val parbinding = Scan.optional ($$$ "(" |-- binding --| $$$ ")") Binding.empty;


(* type classes *)

val class = group (fn () => "type class") (inner_syntax embedded);

val sort = group (fn () => "sort") (inner_syntax embedded);

val type_const = group (fn () => "type constructor") (inner_syntax embedded);

val arity = type_const -- ($$$ "::" |-- !!!
  (Scan.optional ($$$ "(" |-- !!! (list1 sort --| $$$ ")")) [] -- sort)) >> Scan.triple2;

val multi_arity = and_list1 type_const -- ($$$ "::" |-- !!!
  (Scan.optional ($$$ "(" |-- !!! (list1 sort --| $$$ ")")) [] -- sort)) >> Scan.triple2;


(* types *)

val typ = group (fn () => "type") (inner_syntax embedded);

fun type_arguments arg =
  arg >> single ||
  $$$ "(" |-- !!! (list1 arg --| $$$ ")") ||
  Scan.succeed [];

val type_args = type_arguments type_ident;
val type_args_constrained = type_arguments (type_ident -- Scan.option ($$$ "::" |-- !!! sort));


(* mixfix annotations *)

local

val mfix = input (string || cartouche);

val mixfix_ =
  mfix -- !!! (Scan.optional ($$$ "[" |-- !!! (list nat --| $$$ "]")) [] -- Scan.optional nat 1000)
    >> (fn (sy, (ps, p)) => fn range => Mixfix (sy, ps, p, range));

val structure_ = $$$ "structure" >> K Structure;

val binder_ =
  $$$ "binder" |-- !!! (mfix -- ($$$ "[" |-- nat --| $$$ "]" -- nat || nat >> (fn n => (n, n))))
    >> (fn (sy, (p, q)) => fn range => Binder (sy, p, q, range));

val infixl_ = $$$ "infixl"
              |-- !!! (mfix -- nat >> (fn (sy, p) => fn range => Infixl (sy, p, range)));
val infixr_ = $$$ "infixr"
              |-- !!! (mfix -- nat >> (fn (sy, p) => fn range => Infixr (sy, p, range)));
val infix_ = $$$ "infix"
              |-- !!! (mfix -- nat >> (fn (sy, p) => fn range => Infix (sy, p, range)));

val mixfix_body = mixfix_ || structure_ || binder_ || infixl_ || infixr_ || infix_;

fun annotation guard body =
  Scan.trace ($$$ "(" |-- guard (body --| $$$ ")"))
    >> (fn (mx, toks) => mx (Token.range_of toks));

fun opt_annotation guard body = Scan.optional (annotation guard body) NoSyn;

in

val mixfix = annotation !!! mixfix_body;
val mixfix' = annotation I mixfix_body;
val opt_mixfix = opt_annotation !!! mixfix_body;
val opt_mixfix' = opt_annotation I mixfix_body;

end;


(* syntax mode *)

val syntax_mode_spec =
  ($$$ "output" >> K ("", false)) || name -- Scan.optional ($$$ "output" >> K false) true;

val syntax_mode =
  Scan.optional ($$$ "(" |-- !!! (syntax_mode_spec --| $$$ ")")) Syntax.mode_default;


(* fixes *)

val where_ = $$$ "where";

val const_decl = name -- ($$$ "::" |-- !!! typ) -- opt_mixfix >> Scan.triple1;
val const_binding = binding -- ($$$ "::" |-- !!! typ) -- opt_mixfix >> Scan.triple1;

val param_mixfix = binding -- Scan.option ($$$ "::" |-- typ) -- mixfix' >> (single o Scan.triple1);

val params =
  (binding -- Scan.repeat binding) -- Scan.option ($$$ "::" |-- !!! (Scan.ahead typ -- embedded))
    >> (fn ((x, ys), T) =>
        (x, Option.map #1 T, NoSyn) :: map (fn y => (y, Option.map #2 T, NoSyn)) ys);

val vars = and_list1 (param_mixfix || params) >> flat;

val for_fixes = Scan.optional ($$$ "for" |-- !!! vars) [];


(* embedded source text *)

val ML_source = input (group (fn () => "ML source") text);
val document_source = input (group (fn () => "document source") text);

val document_marker =
  group (fn () => "document marker")
    (RESET_VALUE (Scan.one Token.is_document_marker >> Token.input_of));


(* terms *)

val const = group (fn () => "constant") (inner_syntax embedded);
val term = group (fn () => "term") (inner_syntax embedded);
val prop = group (fn () => "proposition") (inner_syntax embedded);

val literal_fact = inner_syntax (group (fn () => "literal fact") (alt_string || cartouche));


(* patterns *)

val is_terms = Scan.repeat1 ($$$ "is" |-- term);
val is_props = Scan.repeat1 ($$$ "is" |-- prop);

val propp = prop -- Scan.optional ($$$ "(" |-- !!! (is_props --| $$$ ")")) [];
val termp = term -- Scan.optional ($$$ "(" |-- !!! (is_terms --| $$$ ")")) [];


(* target information *)

val private = position ($$$ "private") >> #2;
val qualified = position ($$$ "qualified") >> #2;

val target = ($$$ "(" -- $$$ "in") |-- !!! (name_position --| $$$ ")");
val opt_target = Scan.option target;


(* arguments within outer syntax *)

local

val argument_kinds =
 [Token.Ident, Token.Long_Ident, Token.Sym_Ident, Token.Var, Token.Type_Ident, Token.Type_Var,
  Token.Nat, Token.Float, Token.String, Token.Alt_String, Token.Cartouche, Token.Verbatim];

fun arguments is_symid =
  let
    fun argument blk =
      group (fn () => "argument")
        (Scan.one (fn tok =>
          let val kind = Token.kind_of tok in
            member (op =) argument_kinds kind orelse
            Token.keyword_with is_symid tok orelse
            (blk andalso Token.keyword_with (fn s => s = ",") tok)
          end));

    fun args blk x = Scan.optional (args1 blk) [] x
    and args1 blk x =
      (Scan.repeats1 (Scan.repeat1 (argument blk) || argsp "(" ")" || argsp "[" "]")) x
    and argsp l r x = (token ($$$ l) ::: !!! (args true @@@ (token ($$$ r) >> single))) x;
  in (args, args1) end;

in

val args = #1 (arguments Token.ident_or_symbolic) false;
fun args1 is_symid = #2 (arguments is_symid) false;

end;


(* attributes *)

val attrib = token liberal_name ::: !!! args;
val attribs = $$$ "[" |-- list attrib --| $$$ "]";
val opt_attribs = Scan.optional attribs [];


(* theorem references *)

val thm_sel = $$$ "(" |-- list1
 (nat --| minus -- nat >> Facts.FromTo ||
  nat --| minus >> Facts.From ||
  nat >> Facts.Single) --| $$$ ")";

val thm =
  $$$ "[" |-- attribs --| $$$ "]" >> pair (Facts.named "") ||
  (literal_fact >> Facts.Fact ||
    name_position -- Scan.option thm_sel >> Facts.Named) -- opt_attribs;

val thms1 = Scan.repeat1 thm;


(* options *)

val option_name = group (fn () => "option name") name_position;
val option_value = group (fn () => "option value") ((token real || token name) >> Token.content_of);

val option =
  option_name :-- (fn (_, pos) =>
    Scan.optional ($$$ "=" |-- !!! (position option_value)) ("true", pos));

val options = $$$ "[" |-- list1 option --| $$$ "]";


(** C basic parsers **)

(* embedded source text *)

val C_source = input (group (fn () => "C source") text);

(* AutoCorres (MODIFIES) *)

val star = sym_ident :-- (fn "*" => Scan.succeed () | _ => Scan.fail) >> #1;

end;

structure C_Parse_Native: C_PARSE =
struct
open Token
open Parse

(** C basic parsers **)

(* embedded source text *)

val C_source = input (group (fn () => "C source") text);

(* AutoCorres (MODIFIES) *)

val star = sym_ident :-- (fn "*" => Scan.succeed () | _ => Scan.fail) >> #1;
end;
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Thy/thy_header.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Thy/thy_header.ML
    Author:     Makarius

Static theory header information.
*)
\<open>
structure C_Thy_Header =
struct
val bootstrap_keywords =
  C_Keyword.empty_keywords' (Keyword.minor_keywords (Thy_Header.get_keywords @{theory}))

(* theory data *)

structure Data = Theory_Data
(
  type T = C_Keyword.keywords;
  val empty = bootstrap_keywords;
  val extend = I;
  val merge = C_Keyword.merge_keywords;
);

val add_keywords = Data.map o C_Keyword.add_keywords;
val add_keywords_minor = Data.map o C_Keyword.add_keywords_minor;

val get_keywords = Data.get;
val get_keywords' = get_keywords o Proof_Context.theory_of;

end
\<close>

end
