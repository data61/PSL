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

section \<open>Core Language: Lexing Support, with Filtered Annotations (without Annotation Lexing)\<close>

theory C_Lexer_Language
  imports Main
begin

text \<open>
The part implementing the C lexer might resemble to the implementation of the ML one, but the C
syntax is much complex: for example, the preprocessing of directives is implemented with several
parsing layers. Also, we will see that the way antiquotations are handled in C is slightly different
than in ML (especially in the execution part).

Overall, the next ML structures presented here in this theory are all aligned with
\<^file>\<open>~~/src/Pure/ROOT.ML\<close>, and are thus accordingly sorted in the same order
(except for \<^file>\<open>~~/src/Pure/ML/ml_options.ML\<close> which is early included in the boot
process).

This theory will stop at \<^file>\<open>~~/src/Pure/ML/ml_lex.ML\<close>. It is basically situated
in the phase 1 of the bootstrap process (of \<^file>\<open>~~/src/Pure/ROOT.ML\<close>), i.e., the
part dealing with how to get some C tokens from a raw string:
\<^ML_text>\<open>Position.T -> string -> token list\<close>.
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/General/scan.ML\<close>\<close> \<open>
structure C_Scan =
struct
datatype ('a, 'b) either = Left of 'a | Right of 'b

fun opt x = Scan.optional x [];
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/General/symbol.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/General/symbol.ML
    Author:     Makarius

Generalized characters with infinitely many named symbols.
*)
\<open>
structure C_Symbol =
struct
fun is_ascii_quasi "_" = true
  | is_ascii_quasi "$" = true
  | is_ascii_quasi _ = false;

fun is_identletter s =
  Symbol.is_ascii_letter s orelse is_ascii_quasi s

fun is_ascii_oct s =
  Symbol.is_char s andalso Char.ord #"0" <= ord s andalso ord s <= Char.ord #"7";

fun is_ascii_digit1 s =
  Symbol.is_char s andalso Char.ord #"1" <= ord s andalso ord s <= Char.ord #"9";

fun is_ascii_letdig s =
  Symbol.is_ascii_letter s orelse Symbol.is_ascii_digit s orelse is_ascii_quasi s;

fun is_ascii_identifier s =
  size s > 0 andalso forall_string is_ascii_letdig s;

val is_ascii_blank_no_line =
  fn " " => true | "\t" => true | "\^K" => true | "\f" => true
    | _ => false;
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/General/position.ML\<close>\<close> \<open>
structure C_Position =
struct
type reports_text = Position.report_text list
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/General/symbol_pos.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/General/symbol_pos.ML
    Author:     Makarius

Symbols with explicit position information.
*)
\<open>
structure C_Basic_Symbol_Pos =   (*not open by default*)
struct
open Basic_Symbol_Pos;

fun one f = Scan.one (f o Symbol_Pos.symbol)
fun many f = Scan.many (f o Symbol_Pos.symbol)
fun many1 f = Scan.many1 (f o Symbol_Pos.symbol)
val one' = Scan.single o one
fun scan_full !!! mem msg scan =
  scan --| (Scan.ahead (one' (not o mem)) || !!! msg Scan.fail)
fun this_string s =
  (fold (fn s0 => uncurry (fn acc => one (fn s1 => s0 = s1) >> (fn x => x :: acc)))
        (Symbol.explode s)
   o pair [])
  >> rev
val one_not_eof = Scan.one (Symbol.not_eof o #1)
fun unless_eof scan = Scan.unless scan one_not_eof >> single
val repeats_one_not_eof = Scan.repeats o unless_eof
val newline =   $$$ "\n"
             || $$$ "\^M" @@@ $$$ "\n"
             || $$$ "\^M"
val repeats_until_nl = repeats_one_not_eof newline
end

structure C_Symbol_Pos =
struct

(* basic scanners *)

val !!! = Symbol_Pos.!!!

fun !!!! text scan =
  let
    fun get_pos [] = " (end-of-input)"
      | get_pos ((_, pos) :: _) = Position.here pos;

    fun err ((_, syms), msg) = fn () =>
      text () ^ get_pos syms ^
      Markup.markup Markup.no_report (" at " ^ Symbol.beginning 10 (map Symbol_Pos.symbol syms)) ^
      (case msg of NONE => "" | SOME m => "\n" ^ m ());
  in Scan.!! err scan end;

val $$ = Symbol_Pos.$$

val $$$ = Symbol_Pos.$$$

val ~$$$ = Symbol_Pos.~$$$


(* scan string literals *)

local

val char_code =
  Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) --
  Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) --
  Scan.one (Symbol.is_ascii_digit o Symbol_Pos.symbol) :|--
  (fn (((a, pos), (b, _)), (c, _)) =>
    let val (n, _) = Library.read_int [a, b, c]
    in if n <= 255 then Scan.succeed [(chr n, pos)] else Scan.fail end);

fun scan_str q err_prefix stop =
  $$$ "\\" |-- !!! (fn () => err_prefix ^ "bad escape character in string")
    ($$$ q || $$$ "\\" || char_code) ||
  Scan.unless stop
              (Scan.one (fn (s, _) => s <> q andalso s <> "\\" andalso Symbol.not_eof s)) >> single;

fun scan_strs q err_prefix err_suffix stop =
  Scan.ahead ($$ q) |--
    !!! (fn () => err_prefix ^ "unclosed string literal within " ^ err_suffix)
      ((Symbol_Pos.scan_pos --| $$$ q)
       -- (Scan.repeats (scan_str q err_prefix stop) -- ($$$ q |-- Symbol_Pos.scan_pos)));

in

fun scan_string_qq_multi err_prefix stop = scan_strs "\"" err_prefix "the comment delimiter" stop;
fun scan_string_bq_multi err_prefix stop = scan_strs "`" err_prefix "the comment delimiter" stop;
fun scan_string_qq_inline err_prefix =
  scan_strs "\"" err_prefix "the same line" C_Basic_Symbol_Pos.newline;
fun scan_string_bq_inline err_prefix =
  scan_strs "`" err_prefix "the same line" C_Basic_Symbol_Pos.newline;

end;


(* nested text cartouches *)

fun scan_cartouche_depth stop =
  Scan.repeat1 (Scan.depend (fn (depth: int option) =>
    (case depth of
      SOME d =>
        $$ Symbol.open_ >> pair (SOME (d + 1)) ||
          (if d > 0 then
            Scan.unless stop
                        (Scan.one (fn (s, _) => s <> Symbol.close andalso Symbol.not_eof s))
            >> pair depth ||
            $$ Symbol.close >> pair (if d = 1 then NONE else SOME (d - 1))
          else Scan.fail)
    | NONE => Scan.fail)));

fun scan_cartouche err_prefix err_suffix stop =
  Scan.ahead ($$ Symbol.open_) |--
    !!! (fn () => err_prefix ^ "unclosed text cartouche within " ^ err_suffix)
      (Scan.provide is_none (SOME 0) (scan_cartouche_depth stop));

fun scan_cartouche_multi err_prefix stop =
  scan_cartouche err_prefix "the comment delimiter" stop;
fun scan_cartouche_inline err_prefix =
  scan_cartouche err_prefix "the same line" C_Basic_Symbol_Pos.newline;


(* C-style comments *)

local
val par_l = "/"
val par_r = "/"

val scan_body1 = $$$ "*" --| Scan.ahead (~$$$ par_r)
val scan_body2 = Scan.one (fn (s, _) => s <> "*" andalso Symbol.not_eof s) >> single
val scan_cmt =
  Scan.depend (fn (d: int) => $$$ par_l @@@ $$$ "*" >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => $$$ "*" @@@ $$$ par_r >> pair (d - 1)) ||
  Scan.lift scan_body1 ||
  Scan.lift scan_body2;

val scan_cmts = Scan.pass 0 (Scan.repeats scan_cmt);

in

fun scan_comment err_prefix =
  Scan.ahead ($$ par_l -- $$ "*") |--
    !!! (fn () => err_prefix ^ "unclosed comment")
      ($$$ par_l @@@ $$$ "*" @@@ scan_cmts @@@ $$$ "*" @@@ $$$ par_r)
  || $$$ "/" @@@ $$$ "/" @@@ C_Basic_Symbol_Pos.repeats_until_nl;

fun scan_comment_no_nest err_prefix =
  Scan.ahead ($$ par_l -- $$ "*") |--
    !!! (fn () => err_prefix ^ "unclosed comment")
      ($$$ par_l @@@ $$$ "*" @@@ Scan.repeats (scan_body1 || scan_body2) @@@ $$$ "*" @@@ $$$ par_r)
  || $$$ "/" @@@ $$$ "/" @@@ C_Basic_Symbol_Pos.repeats_until_nl;

val recover_comment =
  $$$ par_l @@@ $$$ "*" @@@ Scan.repeats (scan_body1 || scan_body2);

end
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/General/antiquote.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/General/antiquote.ML
    Author:     Makarius

Antiquotations within plain text.
*)
\<open>
structure C_Antiquote =
struct

(* datatype antiquote *)

type antiq = { explicit: bool
             , start: Position.T
             , stop: Position.T option
             , range: Position.range
             , body: Symbol_Pos.T list
             , body_begin: Symbol_Pos.T list
             , body_end: Symbol_Pos.T list }

(* scan *)

open C_Basic_Symbol_Pos;

local

val err_prefix = "Antiquotation lexical error: ";

val par_l = "/"
val par_r = "/"

val scan_body1 = $$$ "*" --| Scan.ahead (~$$$ par_r)
val scan_body1' = $$$ "*" @@@ $$$ par_r
val scan_body2 = Scan.one (fn (s, _) => s <> "*" andalso Symbol.not_eof s) >> single

val scan_antiq_body_multi =
  Scan.trace (C_Symbol_Pos.scan_string_qq_multi err_prefix scan_body1' ||
              C_Symbol_Pos.scan_string_bq_multi err_prefix scan_body1') >> #2 ||
  C_Symbol_Pos.scan_cartouche_multi err_prefix scan_body1' ||
  scan_body1 ||
  scan_body2;

val scan_antiq_body_multi_recover =
  scan_body1 ||
  scan_body2;

val scan_antiq_body_inline =
  Scan.trace (C_Symbol_Pos.scan_string_qq_inline err_prefix ||
              C_Symbol_Pos.scan_string_bq_inline err_prefix) >> #2 ||
  C_Symbol_Pos.scan_cartouche_inline err_prefix ||
  unless_eof newline;

val scan_antiq_body_inline_recover =
  unless_eof newline;

fun control_name sym = (case Symbol.decode sym of Symbol.Control name => name);

fun scan_antiq_multi scan =
  Symbol_Pos.scan_pos
  -- (Scan.trace ($$ par_l |-- $$ "*" |-- scan)
      -- Symbol_Pos.scan_pos
      -- Symbol_Pos.!!! (fn () => err_prefix ^ "missing closing antiquotation")
                        (Scan.repeats scan_antiq_body_multi
                         -- Symbol_Pos.scan_pos
                         -- ($$$ "*" @@@ $$$ par_r)
                         -- Symbol_Pos.scan_pos))

fun scan_antiq_multi_recover scan =
  Symbol_Pos.scan_pos
  -- ($$ par_l |-- $$ "*" |-- scan -- Symbol_Pos.scan_pos --
      (Scan.repeats scan_antiq_body_multi_recover
       -- Symbol_Pos.scan_pos -- ($$ "*" |-- $$ par_r |-- Symbol_Pos.scan_pos)))

fun scan_antiq_inline scan =
  (Symbol_Pos.scan_pos -- Scan.trace ($$ "/" |-- $$ "/" |-- scan)
  -- Symbol_Pos.scan_pos
  -- Scan.repeats scan_antiq_body_inline -- Symbol_Pos.scan_pos)

fun scan_antiq_inline_recover scan =
  (Symbol_Pos.scan_pos --| $$ "/" --| $$ "/" -- scan
  -- Symbol_Pos.scan_pos
  -- Scan.repeats scan_antiq_body_inline_recover -- Symbol_Pos.scan_pos)

in

val scan_control =
  Scan.option (Scan.one (Symbol.is_control o Symbol_Pos.symbol)) --
  Symbol_Pos.scan_cartouche err_prefix >>
    (fn (opt_control, body) =>
      let
        val (name, range) =
          (case opt_control of
            SOME (sym, pos) => ((control_name sym, pos), Symbol_Pos.range ((sym, pos) :: body))
          | NONE => (("cartouche", #2 (hd body)), Symbol_Pos.range body));
      in {name = name, range = range, body = body} end) ||
  Scan.one (Symbol.is_control o Symbol_Pos.symbol) >>
    (fn (sym, pos) =>
      {name = (control_name sym, pos), range = Symbol_Pos.range [(sym, pos)], body = []});

val scan_antiq =
  scan_antiq_multi ($$$ "@" >> K true || scan_body1 >> K false)
  >> (fn (pos1, (((explicit, body_begin), pos2), (((body, pos3), body_end), pos4))) =>
      {explicit = explicit,
       start = Position.range_position (pos1, pos2),
       stop = SOME (Position.range_position (pos3, pos4)),
       range = Position.range (pos1, pos4),
       body = body,
       body_begin = body_begin,
       body_end = body_end}) ||
  scan_antiq_inline ($$$ "@" >> K true || $$$ "*" >> K false)
  >> (fn ((((pos1, (explicit, body_begin)), pos2), body), pos3) => 
      {explicit = explicit,
       start = Position.range_position (pos1, pos2),
       stop = NONE,
       range = Position.range (pos1, pos3),
       body = body,
       body_begin = body_begin,
       body_end = []})

val scan_antiq_recover =
  scan_antiq_multi_recover ($$$ "@" >> K true || scan_body1 >> K false)
    >> (fn (_, ((explicit, _), _)) => explicit)
  ||
  scan_antiq_inline_recover ($$$ "@" >> K true || $$$ "*" >> K false)
   >> (fn ((((_, explicit), _), _), _) => explicit)

end;

end;
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_options.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/ML/ml_options.ML
    Author:     Makarius

ML configuration options.
*)
\<open>
structure C_Options =
struct

(* source trace *)

val lexer_trace = Attrib.setup_config_bool @{binding C_lexer_trace} (K false);
val parser_trace = Attrib.setup_config_bool @{binding C_parser_trace} (K false);
val ML_verbose = Attrib.setup_config_bool @{binding C_ML_verbose} (K true);
val starting_env = Attrib.setup_config_string @{binding C_starting_env} (K "empty");
val starting_rule = Attrib.setup_config_string @{binding C_starting_rule} (K "translation_unit");

end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_lex.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/ML/ml_lex.ML
    Author:     Makarius

Lexical syntax for Isabelle/ML and Standard ML.
*)
\<open>
structure C_Lex =
struct

open C_Scan;
open C_Basic_Symbol_Pos;


(** keywords **)

val keywords =
 ["(",
  ")",
  "[",
  "]",
  "->",
  ".",
  "!",
  "~",
  "++",
  "--",
  "+",
  "-",
  "*",
  "/",
  "%",
  "&",
  "<<",
  ">>",
  "<",
  "<=",
  ">",
  ">=",
  "==",
  "!=",
  "^",
  "|",
  "&&",
  "||",
  "?",
  ":",
  "=",
  "+=",
  "-=",
  "*=",
  "/=",
  "%=",
  "&=",
  "^=",
  "|=",
  "<<=",
  ">>=",
  ",",
  ";",
  "{",
  "}",
  "...",
  (**)
  "_Alignas",
  "_Alignof",
  "__alignof",
  "alignof",
  "__alignof__",
  "__asm",
  "asm",
  "__asm__",
  "_Atomic",
  "__attribute",
  "__attribute__",
  "auto",
  "_Bool",
  "break",
  "__builtin_offsetof",
  "__builtin_types_compatible_p",
  "__builtin_va_arg",
  "case",
  "char",
  "_Complex",
  "__complex__",
  "__const",
  "const",
  "__const__",
  "continue",
  "default",
  "do",
  "double",
  "else",
  "enum",
  "__extension__",
  "extern",
  "float",
  "for",
  "_Generic",
  "goto",
  "if",
  "__imag",
  "__imag__",
  "__inline",
  "inline",
  "__inline__",
  "int",
  "__int128",
  "__label__",
  "long",
  "_Nonnull",
  "__nonnull",
  "_Noreturn",
  "_Nullable",
  "__nullable",
  "__real",
  "__real__",
  "register",
  "__restrict",
  "restrict",
  "__restrict__",
  "return",
  "short",
  "__signed",
  "signed",
  "__signed__",
  "sizeof",
  "static",
  "_Static_assert",
  "struct",
  "switch",
  "__thread",
  "_Thread_local",
  "typedef",
  "__typeof",
  "typeof",
  "__typeof__",
  "union",
  "unsigned",
  "void",
  "__volatile",
  "volatile",
  "__volatile__",
  "while"];

val keywords2 =
 ["__asm",
  "asm",
  "__asm__",
  "extern"];

val keywords3 =
 ["_Bool",
  "char",
  "double",
  "float",
  "int",
  "__int128",
  "long",
  "short",
  "__signed",
  "signed",
  "__signed__",
  "unsigned",
  "void"];

val lexicon = Scan.make_lexicon (map raw_explode keywords);



(** tokens **)

(* datatype token *)

datatype token_kind_comment =
   Comment_formal of C_Antiquote.antiq
 | Comment_suspicious of (bool * string * ((Position.T * Markup.T) * string) list) option

datatype token_kind_encoding =
   Encoding_L
 | Encoding_default
 | Encoding_file of string (* error message *) option

type token_kind_string =
  token_kind_encoding
  * (Symbol.symbol, Position.range * int \<comment> \<open>exceeding \<^ML>\<open>Char.maxOrd\<close>\<close>) either list

datatype token_kind_int_repr = Repr_decimal
                             | Repr_hexadecimal
                             | Repr_octal

datatype token_kind_int_flag = Flag_unsigned
                             | Flag_long
                             | Flag_long_long
                             | Flag_imag

datatype token_kind =
  Keyword | Ident | Type_ident | GnuC | ClangC |
  (**)
  Char of token_kind_string |
  Integer of int * token_kind_int_repr * token_kind_int_flag list |
  Float of Symbol_Pos.T list |
  String of token_kind_string |
  File of token_kind_string |
  (**)
  Space | Comment of token_kind_comment | Sharp of int |
  (**)
  Unknown | Error of string * token_group | Directive of token_kind_directive | EOF

and token_kind_directive = Inline of token_group (* a not yet analyzed directive *)
                         | Include of token_group
                         | Define of token_group (* define *)
                                   * token_group (* name *)
                                   * token_group option (* functional arguments *)
                                   * token_group (* rewrite body *)
                         | Undef of token_group (* name *)
                         | Cpp of token_group
                         | Conditional of token_group (* if *)
                                        * token_group list (* elif *)
                                        * token_group option (* else *)
                                        * token_group (* endif *)

and token_group = Group1 of token list (* spaces and comments filtered from the directive *)
                          * token list (* directive: raw data *)
                | Group2 of token list (* spaces and comments filtered from the directive *)
                          * token list (* directive: function *)
                          * token list (* directive: arguments (same line) *)
                | Group3 of (  Position.range (* full directive (with blanks) *)
                             * token list (* spaces and comments filtered from the directive *)
                             * token list (* directive: function *)
                             * token list (* directive: arguments (same line) *))
                          * (Position.range * token list) (* C code or directive:
                                                               arguments (following lines) *)

and token = Token of Position.range * (token_kind * string);


(* position *)

fun set_range range (Token (_, x)) = Token (range, x);
fun range_of (Token (range, _)) = range;

val pos_of = #1 o range_of;
val end_pos_of = #2 o range_of;


(* stopper *)

fun mk_eof pos = Token ((pos, Position.none), (EOF, ""));
val eof = mk_eof Position.none;

fun is_eof (Token (_, (EOF, _))) = true
  | is_eof _ = false;

val stopper =
  Scan.stopper (fn [] => eof | toks => mk_eof (end_pos_of (List.last toks))) is_eof;

val one_not_eof = Scan.one (not o is_eof)

(* token content *)

fun kind_of (Token (_, (k, _))) = k;

val group_list_of = fn
   Inline g => [g]
 | Include g => [g]
 | Define (g1, g2, o_g3, g4) => flat [[g1], [g2], the_list o_g3, [g4]]
 | Undef g => [g]
 | Cpp g => [g]
 | Conditional (g1, gs2, o_g3, g4) => flat [[g1], gs2, the_list o_g3, [g4]]

fun content_of (Token (_, (_, x))) = x;
fun token_leq (tok, tok') = content_of tok <= content_of tok';

val directive_cmds = fn
   Inline (Group1 (_, _ :: tok2 :: _)) => [tok2]
 | Include (Group2 (_, [_, tok2], _)) => [tok2]
 | Define (Group1 (_, [_, tok2]), _, _, _) => [tok2]
 | Undef (Group2 (_, [_, tok2], _)) => [tok2]
 | Conditional (c1, cs2, c3, c4) =>
     maps (fn Group3 ((_, _, [_, tok2], _), _) => [tok2]
            | _ => error "Only expecting Group3")
          (flat [[c1], cs2, the_list c3, [c4]])
 | _ => []

fun is_keyword (Token (_, (Keyword, _))) = true
  | is_keyword _ = false;

fun is_ident (Token (_, (Ident, _))) = true
  | is_ident _ = false;

fun is_integer (Token (_, (Integer _, _))) = true
  | is_integer _ = false;

fun is_delimiter (Token (_, (Keyword, x))) = not (C_Symbol.is_ascii_identifier x)
  | is_delimiter _ = false;

(* range *)

val range_list_of0 =
 fn [] => Position.no_range
  | toks as tok1 :: _ => Position.range (pos_of tok1, end_pos_of (List.last toks))
    (* WARNING the use of:
       \<comment>\<open>\<^ML>\<open>fn content_of => fn pos_of => fn tok2 =>
             List.last (Symbol_Pos.explode (content_of tok2, pos_of tok2)) |-> Position.advance\<close>\<close>
       would not return an accurate position if for example several
       "backslash newlines" are present in the symbol *)

fun range_list_of toks = (range_list_of0 toks, toks)
fun range_list_of' toks1 toks2 = (range_list_of0 toks1, toks2)

local
fun cmp_pos x2 x1 = case Position.distance_of (pos_of x2, pos_of x1) of SOME dist => dist < 0
                                                                      | NONE => error "cmp_pos"

fun merge_pos xs = case xs of (xs1, []) => xs1
                            | ([], xs2) => xs2
                            | (x1 :: xs1, x2 :: xs2) =>
                                let val (x, xs) = if cmp_pos x2 x1 then (x1, (xs1, x2 :: xs2))
                                                                   else (x2, (x1 :: xs1, xs2))
                                in x :: merge_pos xs end
in
fun merge_blank toks_bl xs1 xs2 =
  let val cmp_tok2 = cmp_pos (List.last xs1)
  in ( range_list_of (merge_pos (xs1, filter cmp_tok2 toks_bl))
     , range_list_of (merge_pos (xs2, filter_out cmp_tok2 toks_bl)))
  end
end

val token_list_of = 
  let fun merge_blank' toks_bl xs1 xs2 =
    let val ((_, l1), (_, l2)) = merge_blank toks_bl xs1 xs2
    in [l1, l2] end
  in group_list_of
    #> maps (fn
        Group1 (toks_bl, []) => [toks_bl]
      | Group1 (toks_bl, xs1) => merge_blank' toks_bl xs1 []
      | Group2 (toks_bl, xs1, xs2) => merge_blank' toks_bl xs1 xs2
      | Group3 ((_, toks_bl, xs1, xs2), (_, xs3)) => flat [merge_blank' toks_bl xs1 xs2, [xs3]])
    #> flat
  end

local

fun warn0 pos l s =
  ()
  |> tap
       (fn _ =>
        if exists (fn Left s => not (Symbol.is_printable s) | _ => false) l then
          app (fn (s, pos) =>
                if Symbol.is_printable s
                then ()
                else Output.information ("Not printable character " ^ @{make_string} (ord s, s)
                                         ^ Position.here pos))
              (Symbol_Pos.explode (s, pos))
        else ())
  |> tap
       (fn _ =>
        app (fn Left _ => ()
              | Right ((pos1, _), n) =>
                  Output.information
                    ("Out of the supported range (character number " ^ Int.toString n ^ ")"
                     ^ Position.here pos1))
            l)



fun unknown pos = Output.information ("Unknown symbol" ^ Position.here pos)

val app_directive =
      app (fn Token (_, (Error (msg, _), _)) => warning msg
            | Token ((pos, _), (Unknown, _)) => unknown pos
            | _ => ())

in
val warn = fn
    Token ((pos, _), (Char (_, l), s)) => warn0 pos l s
  | Token ((pos, _), (String (_, l), s)) => warn0 pos l s
  | Token ((pos, _), (File (_, l), s)) => warn0 pos l s
  | Token ((pos, _), (Unknown, _)) => unknown pos
  | Token (_, (Comment (Comment_suspicious (SOME (explicit, msg, _))), _)) =>
      (if explicit then warning else tracing) msg
  | Token (_, (Directive (kind as Conditional _), _)) => app_directive (token_list_of kind)
  | Token (_, (Directive (Define (_, _, _, Group1 (_, toks4))), _)) => app_directive toks4
  | Token (_, (Directive (Include (Group2 (_, _, toks))), _)) =>
    (case toks of
       [Token (_, (String _, _))] => ()
     | [Token (_, (File _, _))] => ()
     | _ => Output.information
              ("Expecting at least and at most one file"
               ^ Position.here
                   (Position.range_position (pos_of (hd toks), end_pos_of (List.last toks)))))
  | _ => ();
end

fun check_error tok =
  case kind_of tok of
    Error (msg, _) => [msg]
  | _ => [];

(* markup *)

local

val token_kind_markup0 =
 fn Char _ => (Markup.ML_char, "")
  | Integer _ => (Markup.ML_numeral, "")
  | Float _ => (Markup.ML_numeral, "")
  | ClangC => (Markup.ML_numeral, "")
  | String _ => (Markup.ML_string, "")
  | File _ => (Markup.ML_string, "")
  | Sharp _ => (Markup.antiquote, "")
  | Unknown => (Markup.intensify, "")
  | Error (msg, _) => (Markup.bad (), msg)
  | _ => (Markup.empty, "");

fun token_report' escape_directive (tok as Token ((pos, _), (kind, x))) =
  if escape_directive andalso (is_keyword tok orelse is_ident tok) then
    [((pos, Markup.antiquote), "")]
  else if is_keyword tok then
    let
      val (markup, txt) = if is_delimiter tok then (Markup.ML_delimiter, "")
        else if member (op =) keywords2 x then (Markup.ML_keyword2 |> Markup.keyword_properties, "")
        else if member (op =) keywords3 x then (Markup.ML_keyword3 |> Markup.keyword_properties, "")
        else (Markup.ML_keyword1 |> Markup.keyword_properties, "");
    in [((pos, markup), txt)] end
  else
    case kind of
     Directive (tokens as Inline _) =>
       ((pos, Markup.antiquoted), "") :: maps token_report0 (token_list_of tokens)
   | Directive (Include (Group2 (toks_bl, tok1 :: _, toks2))) =>
       ((pos, Markup.antiquoted), "")
       :: flat [ maps token_report1 [tok1]
               , maps token_report0 toks2
               , maps token_report0 toks_bl ]
   | Directive
       (Define
         (Group1 (toks_bl1, tok1 :: _), Group1 (toks_bl2, _), toks3, Group1 (toks_bl4, toks4))) =>
       let val (toks_bl3, toks3) = case toks3 of SOME (Group1 x) => x | _ => ([], [])
       in ((pos, Markup.antiquoted), "")
         :: ((range_list_of0 toks4 |> #1, Markup.intensify), "")
         :: flat [ maps token_report1 [tok1]
                 , maps token_report0 toks3
                 , maps token_report0 toks4
                 , maps token_report0 toks_bl1
                 , maps token_report0 toks_bl2
                 , map (fn tok => ((pos_of tok, Markup.antiquote), "")) toks_bl3
                 , maps token_report0 toks_bl4 ] end
   | Directive (Undef (Group2 (toks_bl, tok1 :: _, _))) =>
       ((pos, Markup.antiquoted), "")
       :: flat [ maps token_report1 [tok1]
               , maps token_report0 toks_bl ]
   | Directive (Cpp (Group2 (toks_bl, toks1, toks2))) =>
       ((pos, Markup.antiquoted), "")
       :: flat [ maps token_report1 toks1
               , maps token_report0 toks2
               , maps token_report0 toks_bl ]
   | Directive (Conditional (c1, cs2, c3, c4)) =>
       maps (fn Group3 (((pos, _), toks_bl, tok1 :: _, toks2), ((pos3, _), toks3)) => 
                ((pos, Markup.antiquoted), "")
                :: ((pos3, Markup.intensify), "")
                :: flat [ maps token_report1 [tok1]
                        , maps token_report0 toks2
                        , maps token_report0 toks3
                        , maps token_report0 toks_bl ]
              | _ => error "Only expecting Group3")
            (flat [[c1], cs2, the_list c3, [c4]])
   | Error (msg, Group2 (toks_bl, toks1, toks2)) =>
        ((range_list_of0 toks1 |> #1, Markup.bad ()), msg)
        :: ((pos, Markup.antiquoted), "")
        :: flat [ maps token_report1 toks1
                , maps token_report0 toks2
                , maps token_report0 toks_bl ]
   | Error (msg, Group3 ((_, toks_bl, toks1, toks2), _)) =>
        ((range_list_of0 toks1 |> #1, Markup.bad ()), msg)
        :: ((pos, Markup.antiquoted), "")
        :: flat [ maps token_report1 toks1
                , maps token_report0 toks2
                , maps token_report0 toks_bl ]
   | Comment (Comment_suspicious c) => ((pos, Markup.ML_comment), "")
                                       :: (case c of NONE => [] | SOME (_, _, l) => l)
   | x => [let val (markup, txt) = token_kind_markup0 x in ((pos, markup), txt) end]

and token_report0 tok = token_report' false tok
and token_report1 tok = token_report' true tok

in
val token_report = token_report0
end;



(** scanners **)

val err_prefix = "C lexical error: ";

fun !!! msg = Symbol_Pos.!!! (fn () => err_prefix ^ msg);

fun !!!! msg = C_Symbol_Pos.!!!! (fn () => err_prefix ^ msg);

val many1_blanks_no_line = many1 C_Symbol.is_ascii_blank_no_line

(* identifiers *)

val scan_ident_sym =
  let val hex = one' Symbol.is_ascii_hex
  in   one' C_Symbol.is_identletter
    || $$$ "\\" @@@ $$$ "u" @@@ hex @@@ hex @@@ hex @@@ hex
    || $$$ "\\" @@@ $$$ "U" @@@ hex @@@ hex @@@ hex @@@ hex @@@ hex @@@ hex @@@ hex @@@ hex
    || one' Symbol.is_symbolic
    || one' Symbol.is_control
    || one' Symbol.is_utf8
  end
  
val scan_ident =
      scan_ident_sym
  @@@ Scan.repeats (scan_ident_sym || one' Symbol.is_ascii_digit);

val keywords_ident =
  map_filter
    (fn s => 
         Source.of_list (Symbol_Pos.explode (s, Position.none))
      |> Source.source
           Symbol_Pos.stopper
           (Scan.bulk (scan_ident >> SOME || Scan.one (not o Symbol_Pos.is_eof) >> K NONE))
      |> Source.exhaust
      |> (fn [SOME _] => SOME s | _ => NONE))
    keywords

(* numerals *)

fun read_bin s = #1 (read_radix_int 2 s)
fun read_oct s = #1 (read_radix_int 8 s)
fun read_dec s = #1 (read_int s)
val read_hex =
  let fun conv_ascii c1 c0 = String.str (Char.chr (Char.ord #"9" + Char.ord c1 - Char.ord c0 + 1))
  in map (fn s => let val c = String.sub (s, 0) in
                  if c >= #"A" andalso c <= #"F" then
                    conv_ascii c #"A"
                  else if c >= #"a" andalso c <= #"f" then
                    conv_ascii c #"a"
                  else s
                  end)
  #> read_radix_int 16
  #> #1
  end

local
val many_digit = many Symbol.is_ascii_digit
val many1_digit = many1 Symbol.is_ascii_digit
val many_hex = many Symbol.is_ascii_hex
val many1_hex = many1 Symbol.is_ascii_hex

val scan_suffix_ll = ($$$ "l" @@@ $$$ "l" || $$$ "L" @@@ $$$ "L") >> K [Flag_long_long]
fun scan_suffix_gnu flag = ($$$ "i" || $$$ "j") >> K [flag]
val scan_suffix_int = 
  let val u = ($$$ "u" || $$$ "U") >> K [Flag_unsigned]
      val l = ($$$ "l" || $$$ "L") >> K [Flag_long] in
      u @@@ scan_suffix_ll
   || scan_suffix_ll @@@ opt u
   || u @@@ opt l
   || l @@@ opt u
  end

val scan_suffix_gnu_int0 = scan_suffix_gnu Flag_imag
val scan_suffix_gnu_int = scan_full !!!
                                    (member (op =) (raw_explode "uUlLij"))
                                    "Invalid integer constant suffix"
                                    (   scan_suffix_int @@@ opt scan_suffix_gnu_int0
                                     || scan_suffix_gnu_int0 @@@ opt scan_suffix_int)

fun scan_intgnu x =
  x -- opt scan_suffix_gnu_int
  >> (fn ((s1', read, repr), l) => (read (map (Symbol_Pos.content o single) s1'), repr, l))

val scan_intoct = scan_intgnu ($$ "0" |--
                               scan_full
                                 !!!
                                 Symbol.is_ascii_digit
                                 "Invalid digit in octal constant"
                                 (Scan.max
                                   (fn ((xs2, _, _), (xs1, _, _)) => length xs2 < length xs1)
                                   (many C_Symbol.is_ascii_oct
                                      >> (fn xs => (xs, read_oct, Repr_octal)))
                                   (many (fn x => x = "0")
                                      >> (fn xs => (xs, read_dec, Repr_decimal)))))
val scan_intdec = scan_intgnu (one C_Symbol.is_ascii_digit1 -- many Symbol.is_ascii_digit
                               >> (fn (x, xs) => (x :: xs, read_dec, Repr_decimal)))
val scan_inthex = scan_intgnu (($$ "0" -- ($$ "x" || $$ "X")) |-- many1_hex
                               >> (fn xs2 => (xs2, read_hex, Repr_hexadecimal)))

(**)

fun scan_signpart a A = ($$$ a || $$$ A) @@@ opt ($$$ "+" || $$$ "-") @@@ many1_digit
val scan_exppart = scan_signpart "e" "E"

val scan_suffix_float = $$$ "f" || $$$ "F" || $$$ "l" || $$$ "L"
val scan_suffix_gnu_float0 = Scan.trace (scan_suffix_gnu ()) >> #2
val scan_suffix_gnu_float = scan_full !!!
                                      (member (op =) (raw_explode "fFlLij"))
                                      "Invalid float constant suffix"
                                      (   scan_suffix_float @@@ opt scan_suffix_gnu_float0
                                       || scan_suffix_gnu_float0 @@@ opt scan_suffix_float)

val scan_hex_pref = $$$ "0" @@@ $$$ "x"

val scan_hexmant = many_hex @@@ $$$ "." @@@ many1_hex
                || many1_hex @@@ $$$ "."
val scan_floatdec =
      (       (   many_digit @@@ $$$ "." @@@ many1_digit
               || many1_digit @@@ $$$ ".")
          @@@ opt scan_exppart
       || many1_digit @@@ scan_exppart)
  @@@ opt scan_suffix_gnu_float

val scan_floathex = scan_hex_pref @@@ (scan_hexmant || many1_hex)
                    @@@ scan_signpart "p" "P" @@@ opt scan_suffix_gnu_float
val scan_floatfail = scan_hex_pref @@@ scan_hexmant
in
val scan_int = scan_inthex
            || scan_intoct
            || scan_intdec

val recover_int =
     many1 (fn s => Symbol.is_ascii_hex s orelse member (op =) (raw_explode "xXuUlLij") s)

val scan_float = scan_floatdec
              || scan_floathex
              || scan_floatfail @@@ !!! "Hexadecimal floating constant requires an exponent"
                                        Scan.fail

val scan_clangversion = many1_digit @@@ $$$ "." @@@ many1_digit @@@ $$$ "." @@@ many1_digit

end;


(* chars and strings *)

val scan_blanks1 = many1 Symbol.is_ascii_blank

local
val escape_char = [ ("n", #"\n")
                  , ("t", #"\t")
                  , ("v", #"\v")
                  , ("b", #"\b")
                  , ("r", #"\r")
                  , ("f", #"\f")
                  , ("a", #"\a")
                  , ("e", #"\^[")
                  , ("E", #"\^[")
                  , ("\\", #"\\")
                  , ("?", #"?")
                  , ("'", #"'")
                  , ("\"", #"\"") ]

val _ = \<comment> \<open>printing a ML function translating code point from \<^ML_type>\<open>int -> string\<close>\<close>
 fn _ => 
  app (fn (x0, x) => writeln (" | "
                              ^ string_of_int (Char.ord x)
                              ^ " => \"\\\\"
                              ^ (if exists (fn x1 => x0 = x1) ["\"", "\\"] then "\\" ^ x0 else x0)
                              ^ "\""))
      escape_char

fun scan_escape s0 =
  let val oct = one' C_Symbol.is_ascii_oct
      val hex = one' Symbol.is_ascii_hex
      fun chr' f l =
        let val x = f (map Symbol_Pos.content l)
        in [if x <= Char.maxOrd then Left (chr x) else Right (Symbol_Pos.range (flat l), x)] end
      val read_oct' = chr' read_oct
      val read_hex' = chr' read_hex
  in one' (member (op =) (raw_explode (s0 ^ String.concat (map #1 escape_char))))
     >> (fn i =>
          [Left (case AList.lookup (op =) escape_char (Symbol_Pos.content i) of
                   NONE => s0
                 | SOME c => String.str c)])
  || oct -- oct -- oct >> (fn ((o1, o2), o3) => read_oct' [o1, o2, o3])
  || oct -- oct >> (fn (o1, o2) => read_oct' [o1, o2])
  || oct >> (read_oct' o single)
  || $$ "x" |-- many1 Symbol.is_ascii_hex
     >> (read_hex' o map single)
  || $$ "u" |-- hex -- hex -- hex -- hex
     >> (fn (((x1, x2), x3), x4) => read_hex' [x1, x2, x3, x4])
  || $$ "U" |-- hex -- hex -- hex -- hex -- hex -- hex -- hex -- hex
     >> (fn (((((((x1, x2), x3), x4), x5), x6), x7), x8) =>
          read_hex' [x1, x2, x3, x4, x5, x6, x7, x8])
  end

fun scan_str s0 =
     Scan.unless newline
                 (Scan.one (fn (s, _) => Symbol.not_eof s andalso s <> s0 andalso s <> "\\"))
     >> (fn s => [Left (#1 s)])
  || Scan.ahead newline |-- !!! "bad newline" Scan.fail
  || $$ "\\" |-- !!! "bad escape character" (scan_escape s0);

fun scan_string0 s0 msg repeats =
  Scan.optional ($$ "L" >> K Encoding_L) Encoding_default --
    (Scan.ahead ($$ s0) |--
      !!! ("unclosed " ^ msg ^ " literal")
        ($$ s0 |-- repeats (scan_str s0) --| $$ s0))

fun recover_string0 s0 repeats =
  opt ($$$ "L") @@@ $$$ s0 @@@ repeats (Scan.permissive (Scan.trace (scan_str s0) >> #2));
in

val scan_char = scan_string0 "'" "char" Scan.repeats1
val scan_string = scan_string0 "\"" "string" Scan.repeats
fun scan_string' src =
  case
    Source.source
      Symbol_Pos.stopper
      (Scan.recover (Scan.bulk (!!! "bad input" scan_string >> K NONE))
                    (fn msg => C_Basic_Symbol_Pos.one_not_eof >> K [SOME msg]))
      (Source.of_list src)
    |> Source.exhaust
  of
      [NONE] => NONE
    | [] => SOME "Empty input"
    | l => case map_filter I l of msg :: _ => SOME msg
                                | _ => SOME "More than one string"
val scan_file =
  let fun scan !!! s_l s_r =
    Scan.ahead ($$ s_l) |--
          !!!
          ($$ s_l
           |-- Scan.repeats
                 (Scan.unless newline
                              (Scan.one (fn (s, _) => Symbol.not_eof s andalso s <> s_r)
                               >> (fn s => [Left (#1 s)])))
           --| $$ s_r)
  in
     Scan.trace (scan (!!! ("unclosed file literal")) "\"" "\"")
       >> (fn (s, src) => String (Encoding_file (scan_string' src), s))
  || scan I \<comment> \<open>Due to conflicting symbols, raising \<^ML>\<open>Symbol_Pos.!!!\<close> here will not let a potential
                legal \<^ML>\<open>"<"\<close> symbol be tried and parsed as a \<^emph>\<open>keyword\<close>.\<close>
            "<" ">" >> (fn s => File (Encoding_default, s))
  end

val recover_char = recover_string0 "'" Scan.repeats1
val recover_string = recover_string0 "\"" Scan.repeats

end;

(* scan tokens *)

val check = fold (tap warn #> fold cons o check_error)

local

fun token k ss = Token (Symbol_Pos.range ss, (k, Symbol_Pos.content ss));
fun scan_token f1 f2 = Scan.trace f1 >> (fn (v, s) => token (f2 v) s)

val comments =
     Scan.recover
       (scan_token C_Antiquote.scan_antiq (Comment o Comment_formal))
       (fn msg => Scan.ahead C_Antiquote.scan_antiq_recover
                  -- C_Symbol_Pos.scan_comment_no_nest err_prefix
                  >> (fn (explicit, res) =>
                       token (Comment (Comment_suspicious (SOME (explicit, msg, [])))) res)
               || Scan.fail_with (fn _ => fn _ => msg))
  || C_Symbol_Pos.scan_comment_no_nest err_prefix >> token (Comment (Comment_suspicious NONE))

fun scan_fragment blanks comments sharps non_blanks =
     non_blanks (scan_token scan_char Char)
  || non_blanks (scan_token scan_string String)
  || blanks
  || comments
  || non_blanks sharps
  || non_blanks (Scan.max token_leq (Scan.literal lexicon >> token Keyword)
                                    (   scan_clangversion >> token ClangC
                                     || scan_token scan_float Float
                                     || scan_token scan_int Integer
                                     || scan_ident >> token Ident))
  || non_blanks (Scan.one (Symbol.is_printable o #1) >> single >> token Unknown)

(* scan tokens, directive part *)

val scan_sharp1 = $$$ "#"
val scan_sharp2 = $$$ "#" @@@ $$$ "#"

val scan_directive =
  let val f_filter = fn Token (_, (Space, _)) => true
                      | Token (_, (Comment _, _)) => true
                      | Token (_, (Error _, _)) => true
                      | _ => false
      val sharp1 = scan_sharp1 >> token (Sharp 1)
  in    (sharp1 >> single)
    @@@ Scan.repeat (   scan_token scan_file I
                     || scan_fragment (many1_blanks_no_line >> token Space)
                                      comments
                                      (scan_sharp2 >> token (Sharp 2) || sharp1)
                                      I)
    >> (fn tokens => Inline (Group1 (filter f_filter tokens, filter_out f_filter tokens)))
  end

local
fun !!! text scan =
  let
    fun get_pos [] = " (end-of-input)"
      | get_pos (t :: _) = Position.here (pos_of t);

    fun err (syms, msg) = fn () =>
      err_prefix ^ text ^ get_pos syms ^
      (case msg of NONE => "" | SOME m => "\n" ^ m ());
  in Scan.!! err scan end

val pos_here_of = Position.here o pos_of

fun one_directive f =
  Scan.one (fn Token (_, (Directive ( Inline (Group1 (_, Token (_, (Sharp 1, _))
                                                         :: Token (_, s)
                                                         :: _)))
                                    , _))
                 => f s
             | _ => false)

val get_cond = fn Token (pos, (Directive (Inline (Group1 (toks_bl, tok1 :: tok2 :: toks))), _)) =>
                    (fn t3 => Group3 ((pos, toks_bl, [tok1, tok2], toks), range_list_of t3))
                | _ => error "Inline directive expected"

val one_start_cond = one_directive (fn (Keyword, "if") => true
                                     | (Ident, "ifdef") => true
                                     | (Ident, "ifndef") => true
                                     | _ => false)
val one_elif = one_directive (fn (Ident, "elif") => true | _ => false)
val one_else = one_directive (fn (Keyword, "else") => true | _ => false)
val one_endif = one_directive (fn (Ident, "endif") => true | _ => false)

val not_cond =
 Scan.unless
  (one_start_cond || one_elif || one_else || one_endif)
  (one_not_eof
   >>
    (fn Token (pos, ( Directive (Inline (Group1 ( toks_bl
                                                , (tok1 as Token (_, (Sharp _, _)))
                                                  :: (tok2 as Token (_, (Ident, "include")))
                                                  :: toks)))
                    , s)) =>
          Token (pos, ( case toks of [] =>
                          Error ( "Expecting at least one file"
                                  ^ Position.here (end_pos_of tok2)
                                , Group2 (toks_bl, [tok1, tok2], toks))
                        | _ => Directive (Include (Group2 (toks_bl, [tok1, tok2], toks)))
                      , s))
      | Token (pos, ( Directive (Inline (Group1 ( toks_bl
                                                , (tok1 as Token (_, (Sharp _, _)))
                                                  :: (tok2 as Token (_, (Ident, "define")))
                                                  :: toks)))
                    , s)) =>
         let
          fun define tok3 toks = 
           case
             case toks of
               (tok3' as Token (pos, (Keyword, "("(*)*)))) :: toks => 
                 if Position.offset_of (end_pos_of tok3) = Position.offset_of (pos_of tok3')
                 then
                  let
                    fun right msg pos = Right (msg ^ Position.here pos)
                    fun right1 msg = right msg o #1
                    fun right2 msg = right msg o #2
                    fun take_prefix' toks_bl toks_acc pos =
                     fn
                       (tok1 as Token (_, (Ident, _)))
                       :: (tok2 as Token (pos2, (Keyword, key)))
                       :: toks =>
                         if key = ","
                         then take_prefix' (tok2 :: toks_bl) (tok1 :: toks_acc) pos2 toks
                         else if key = (*( *)")" then
                           Left (rev (tok2 :: toks_bl), rev (tok1 :: toks_acc), toks)
                         else
                           right1 "Expecting a colon delimiter or a closing parenthesis" pos2
                     | Token (pos1, (Ident, _)) :: _ =>
                         right2 "Expecting a colon delimiter or a closing parenthesis" pos1
                     | (tok1 as Token (_, (Keyword, key1)))
                       :: (tok2 as Token (pos2, (Keyword, key2)))
                       :: toks =>
                         if key1 = "..." then
                           if key2 = (*( *)")"
                           then Left (rev (tok2 :: toks_bl), rev (tok1 :: toks_acc), toks)
                           else right1 "Expecting a closing parenthesis" pos2
                         else right2 "Expecting an identifier or the keyword '...'" pos
                     | _ => right2 "Expecting an identifier or the keyword '...'" pos
                  in case
                      case toks of
                        (tok2 as Token (_, (Keyword, (*( *)")"))) :: toks => Left ([tok2], [], toks)
                      | _ => take_prefix' [] [] pos toks
                     of Left (toks_bl, toks_acc, toks) =>
                          Left (SOME (Group1 (tok3' :: toks_bl, toks_acc)), Group1 ([], toks))
                      | Right x => Right x
                  end
                 else Left (NONE, Group1 ([], tok3' :: toks))
             | _ => Left (NONE, Group1 ([], toks))
           of Left (gr1, gr2) =>
                Directive (Define (Group1 (toks_bl, [tok1, tok2]), Group1 ([], [tok3]), gr1, gr2))
            | Right msg => Error (msg, Group2 (toks_bl, [tok1, tok2], tok3 :: toks))
          fun err () = Error ( "Expecting at least one identifier" ^ Position.here (end_pos_of tok2)
                             , Group2 (toks_bl, [tok1, tok2], toks))
         in
           Token (pos, ( case toks of
                           (tok3 as Token (_, (Ident, _))) :: toks => define tok3 toks
                         | (tok3 as Token (_, (Keyword, cts))) :: toks =>
                             if exists (fn cts0 => cts = cts0) keywords_ident
                             then define tok3 toks
                             else err ()
                         | _ => err ()
                       , s))
         end
      | Token (pos, ( Directive (Inline (Group1 ( toks_bl
                                                , (tok1 as Token (_, (Sharp _, _)))
                                                  :: (tok2 as Token (_, (Ident, "undef")))
                                                  :: toks)))
                    , s)) =>
          Token (pos, ( let fun err () = Error ( "Expecting at least and at most one identifier"
                                                 ^ Position.here (end_pos_of tok2)
                                               , Group2 (toks_bl, [tok1, tok2], toks))
                        in
                          case toks of
                            [Token (_, (Ident, _))] =>
                              Directive (Undef (Group2 (toks_bl, [tok1, tok2], toks)))
                          | [Token (_, (Keyword, cts))] =>
                              if exists (fn cts0 => cts = cts0) keywords_ident
                              then Directive (Undef (Group2 (toks_bl, [tok1, tok2], toks)))
                              else err ()
                          | _ => err ()
                        end
                      , s))
      | Token (pos, ( Directive (Inline (Group1 ( toks_bl
                                                , (tok1 as Token (_, (Sharp _, _)))
                                                  :: (tok2 as Token (_, (Integer _, _)))
                                                  :: (tok3 as Token (_, (String _, _)))
                                                  :: toks)))
                    , s)) =>
          Token (pos, ( if forall is_integer toks then
                          Directive (Cpp (Group2 (toks_bl, [tok1], tok2 :: tok3 :: toks)))
                        else Error ( "Expecting an integer"
                                     ^ Position.here (drop_prefix is_integer toks |> hd |> pos_of)
                                   , Group2 (toks_bl, [tok1], tok2 :: tok3 :: toks))
                      , s))
      | x => x))

fun scan_cond xs = xs |>
  (one_start_cond -- scan_cond_list
   -- Scan.repeat (one_elif -- scan_cond_list)
   -- Scan.option (one_else -- scan_cond_list)
   -- Scan.recover one_endif
                   (fn msg =>
                     Scan.fail_with
                       (fn toks => fn () =>
                         case toks of
                           tok :: _ => "can be closed here" ^ Position.here (pos_of tok)
                         | _ => msg))
    >> (fn (((t_if, t_elif), t_else), t_endif) =>
         Token ( Position.no_range
               , ( Directive
                     (Conditional
                       let fun t_body x = x |-> get_cond
                       in
                       ( t_body t_if
                       , map t_body t_elif
                       , Option.map t_body t_else
                       , t_body (t_endif, []))
                       end)
                 , ""))))

and scan_cond_list xs = xs |> Scan.repeat (not_cond || scan_cond)

val scan_directive_cond0 =
     not_cond
  || Scan.ahead ( one_start_cond |-- scan_cond_list
                 |-- Scan.repeat (one_elif -- scan_cond_list)
                 |-- one_else --| scan_cond_list -- (one_elif || one_else))
     :-- (fn (tok1, tok2) => !!! ( "directive" ^ pos_here_of tok2
                                 ^ " not expected after" ^ pos_here_of tok1
                                 ^ ", detected at")
                                 Scan.fail)
     >> #2
  || (Scan.ahead one_start_cond |-- !!! "unclosed directive" scan_cond)
  || (Scan.ahead one_not_eof |-- !!! "missing or ambiguous beginning of conditional" Scan.fail)

fun scan_directive_recover msg =
     not_cond
  || one_not_eof >>
       (fn tok as Token (pos, (_, s)) => Token (pos, (Error (msg, get_cond tok []), s)))

in

val scan_directive_cond =
  Scan.recover
    (Scan.bulk scan_directive_cond0)
    (fn msg => scan_directive_recover msg >> single)

end

(* scan tokens, main *)

val scan_ml =
  Scan.depend
    let
      fun non_blanks st scan = scan >> pair st 
      fun scan_frag st =
        scan_fragment (   C_Basic_Symbol_Pos.newline >> token Space >> pair true
                       || many1_blanks_no_line >> token Space >> pair st)
                      (non_blanks st comments)
                      ((scan_sharp2 || scan_sharp1) >> token Keyword)
                      (non_blanks false)
    in
      fn true => scan_token scan_directive Directive >> pair false || scan_frag true
       | false => scan_frag false
    end;

fun recover msg =
 (recover_char ||
  recover_string ||
  Symbol_Pos.recover_cartouche ||
  C_Symbol_Pos.recover_comment ||
  recover_int ||
  one' Symbol.not_eof)
  >> token (Error (msg, Group1 ([], [])));

fun reader scan syms =
  let
    val termination =
      if null syms then []
      else
        let
          val pos1 = List.last syms |-> Position.advance;
          val pos2 = Position.advance Symbol.space pos1;
        in [Token (Position.range (pos1, pos2), (Space, Symbol.space))] end;

    val backslash1 =
          $$$ "\\" @@@ many C_Symbol.is_ascii_blank_no_line @@@ C_Basic_Symbol_Pos.newline
    val backslash2 = Scan.one (not o Symbol_Pos.is_eof)

    val input0 =
      Source.of_list syms
      |> Source.source Symbol_Pos.stopper (Scan.bulk (backslash1 >> SOME || backslash2 >> K NONE))
      |> Source.map_filter I
      |> Source.exhaust
      |> map (Symbol_Pos.range #> Position.range_position)

    val input1 =
      Source.of_list syms
      |> Source.source Symbol_Pos.stopper (Scan.bulk (backslash1 >> K NONE || backslash2 >> SOME))
      |> Source.map_filter I
      |> Source.source' true
                        Symbol_Pos.stopper
                        (Scan.recover (Scan.bulk (!!!! "bad input" scan))
                                      (fn msg => Scan.lift (recover msg) >> single))
      |> Source.source stopper scan_directive_cond
      |> Source.exhaust
      |> (fn input => input @ termination);

    val _ = app (fn pos => Output.information ("Backslash newline" ^ Position.here pos)) input0
    val _ = Position.reports_text (map (fn pos => ((pos, Markup.intensify), "")) input0);
  in (input1, check input1)
end;

in

fun op @@ ((input1, f_error_lines1), (input2, f_error_lines2)) =
  (input1 @ input2, f_error_lines1 #> f_error_lines2)

val read_init = ([], I)

fun read text = (reader scan_ml o Symbol_Pos.explode) (text, Position.none);

fun read_source' {language, symbols} scan source =
  let
    val pos = Input.pos_of source;
    val _ =
      if Position.is_reported_range pos
      then Position.report pos (language (Input.is_delimited source))
      else ();
  in
    Input.source_explode source
    |> not symbols ? maps (fn (s, p) => raw_explode s |> map (rpair p))
    |> reader scan
  end;

val read_source =
  read_source' { language =
                  Markup.language' {name = "C", symbols = false, antiquotes = true}, symbols = true}
               scan_ml;

end;

end;
\<close>

end
