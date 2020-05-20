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

section \<open>Parsing Environment\<close>

theory C_Environment
  imports C_Lexer_Language C_Ast
begin

text \<open> The environment comes in two parts: a basic core structure, and a (thin) layer of
utilities. \<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/context.ML\<close>\<close> \<open>
structure C_Env = struct

type 'a markup_store = Position.T list * serial * 'a

type env_directives =
      (   ( string * Position.range -> Context.generic -> C_Lex.token list * Context.generic
          , C_Lex.token list)
        C_Scan.either
      * (string * Position.range -> Context.generic -> Context.generic))
    markup_store
  Symtab.table

(**)

datatype 'a parse_status = Parsed of 'a | Previous_in_stack

type markup_global = bool (*true: global*)

type markup_ident = { global : markup_global
                    , params : C_Ast.CDerivedDeclr list
                    , ret : C_Ast.CDeclSpec list parse_status }

type var_table = { tyidents : markup_global markup_store Symtab.table (*ident name*)
                                                                      Symtab.table (*internal
                                                                                     namespace*)
                 , idents : markup_ident markup_store Symtab.table (*ident name*) }

type 'antiq_language_list stream = ('antiq_language_list, C_Lex.token) C_Scan.either list

\<comment> \<open>Key entry point environment to the C language\<close>
type env_lang = { var_table : var_table \<comment> \<open>current active table in the scope\<close>
                , scopes : (C_Ast.ident option * var_table) list  \<comment> \<open>parent scope tables\<close>
                , namesupply : int
                , stream_ignored : C_Antiquote.antiq stream
                , env_directives : env_directives }
(* NOTE: The distinction between type variable or identifier can not be solely made
         during the lexing process.
         Another pass on the parsed tree is required. *)

type error_lines = string list

type env_tree = { context : Context.generic
                , reports_text : C_Position.reports_text
                , error_lines : error_lines }

type rule_static = (env_tree -> env_lang * env_tree) option

(**)

datatype comment_style = Comment_directive
                       | Comment_language

type env_propagation_reduce = int (*reduce rule number*) option (* NONE: shift action *)

type env_propagation_ctxt = env_propagation_reduce -> Context.generic -> Context.generic

type env_propagation_directive =
       env_propagation_reduce -> env_directives -> env_lang * env_tree -> env_lang * env_tree

datatype env_propagation_bottom_up = Exec_annotation of env_propagation_ctxt
                                   | Exec_directive of env_propagation_directive

datatype env_propagation = Bottom_up (*during parsing*) of env_propagation_bottom_up
                         | Top_down (*after parsing*) of env_propagation_ctxt

type eval_node = Position.range
                 * env_propagation
                 * env_directives
                 * bool (* true: skip vacuous reduce rules *)

datatype eval_time = Lexing of Position.range
                               * (comment_style -> Context.generic -> Context.generic)
                   | Parsing of (Symbol_Pos.T list (* length = number of tokens to advance *) 
                                 * Symbol_Pos.T list (* length = number of steps back in stack *)) 
                                 * eval_node
                   | Never (* to be manually treated by the semantic back-end, and analyzed there *)

datatype antiq_language = Antiq_stack of C_Position.reports_text * eval_time
                        | Antiq_none of C_Lex.token

\<comment> \<open> One of the key element of the structure is
\<^ML_text>\<open>eval_time\<close>, relevant for the generic annotation
module. \<close>

(**)

type ('LrTable_state, 'a, 'Position_T) stack_elem0 = 'LrTable_state
                                                     * ('a * 'Position_T * 'Position_T)
type ('LrTable_state, 'a, 'Position_T) stack0 = ('LrTable_state, 'a, 'Position_T) stack_elem0 list

type ('LrTable_state, 'svalue0, 'pos) rule_reduce0 =
       (('LrTable_state, 'svalue0, 'pos) stack0 * env_lang * eval_node) list
type ('LrTable_state, 'svalue0, 'pos) rule_reduce =
       int * ('LrTable_state, 'svalue0, 'pos) stack0 * eval_node list list
type ('LrTable_state, 'svalue0, 'pos) rule_reduce' =
       int * bool (*vacuous*) * ('LrTable_state, 'svalue0, 'pos) rule_reduce0

datatype ('LrTable_state, 'svalue0, 'pos) rule_type =
                               Void
                             | Shift
                             | Reduce of rule_static * ('LrTable_state, 'svalue0, 'pos) rule_reduce'

type ('LrTable_state, 'svalue0, 'pos) rule_ml =
  { rule_pos : 'pos * 'pos
  , rule_type : ('LrTable_state, 'svalue0, 'pos) rule_type }

(**)

type 'class_Pos rule_output0' = { output_pos : 'class_Pos option
                                , output_vacuous : bool
                                , output_env : rule_static }

type ('LrTable_state, 'svalue0, 'pos) rule_output0 =
                                         eval_node list list (* delayed *)
                                       * ('LrTable_state, 'svalue0, 'pos) rule_reduce0 (* actual *)
                                       * ('pos * 'pos) rule_output0'

type rule_output = C_Ast.class_Pos rule_output0'

(**)

datatype stream_lang_state = Stream_ident of Position.range * string
                           | Stream_string of (Position.range * string) list
                           | Stream_atomic
                           | Stream_regular

type T = { env_lang : env_lang
         , env_tree : env_tree
         , rule_output : rule_output
         , rule_input : C_Ast.class_Pos list * int
         , stream_hook : (Symbol_Pos.T list * Symbol_Pos.T list * eval_node) list list
         , stream_lang : stream_lang_state * (C_Antiquote.antiq * antiq_language list) stream }

(**)

datatype 'a tree = Tree of 'a * 'a tree list

type ('LrTable_state, 'a, 'Position_T) stack' =
     ('LrTable_state, 'a, 'Position_T) stack0
   * eval_node list list
   * ('Position_T * 'Position_T) list
   * ('LrTable_state, 'a, 'Position_T) rule_ml tree list

(**)

fun map_env_lang f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                     {env_lang = f
                                 env_lang, env_tree = env_tree, rule_output = rule_output, 
                      rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang}

fun map_env_tree f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                     {env_lang = env_lang, env_tree = f
                                                      env_tree, rule_output = rule_output, 
                      rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang}

fun map_rule_output f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                     {env_lang = env_lang, env_tree = env_tree, rule_output = f
                                                                              rule_output,
                      rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang}

fun map_rule_input f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                     {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                      rule_input = f
                                   rule_input, stream_hook = stream_hook, stream_lang = stream_lang}

fun map_stream_hook f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                     {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                      rule_input = rule_input, stream_hook = f
                                                             stream_hook, stream_lang = stream_lang}

fun map_stream_lang f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                     {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                      rule_input = rule_input, stream_hook = stream_hook, stream_lang = f
                                                                                        stream_lang}

(**)

fun map_output_pos f {output_pos, output_vacuous, output_env} =
               {output_pos = f output_pos, output_vacuous = output_vacuous, output_env = output_env}

fun map_output_vacuous f {output_pos, output_vacuous, output_env} =
               {output_pos = output_pos, output_vacuous = f output_vacuous, output_env = output_env}

fun map_output_env f {output_pos, output_vacuous, output_env} =
               {output_pos = output_pos, output_vacuous = output_vacuous, output_env = f output_env}

(**)

fun map_tyidents f {tyidents, idents} =
                                        {tyidents = f tyidents, idents = idents}

fun map_idents f {tyidents, idents} =
                                        {tyidents = tyidents, idents = f idents}

(**)

fun map_var_table f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                                  {var_table = f
                                               var_table, scopes = scopes, namesupply = namesupply, 
                                   stream_ignored = stream_ignored, env_directives = env_directives}

fun map_scopes f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                                  {var_table = var_table, scopes = f
                                                                   scopes, namesupply = namesupply, 
                                   stream_ignored = stream_ignored, env_directives = env_directives}

fun map_namesupply f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                                  {var_table = var_table, scopes = scopes, namesupply = f
                                                                                        namesupply, 
                                   stream_ignored = stream_ignored, env_directives = env_directives}

fun map_stream_ignored f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                                  {var_table = var_table, scopes = scopes, namesupply = namesupply, 
                                   stream_ignored = f
                                                    stream_ignored, env_directives = env_directives}

fun map_env_directives f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                                  {var_table = var_table, scopes = scopes, namesupply = namesupply, 
                                   stream_ignored = stream_ignored, env_directives = f
                                                                                     env_directives}

(**)

fun map_context f {context, reports_text, error_lines} =
                       {context = f context, reports_text = reports_text, error_lines = error_lines}

fun map_context' f {context, reports_text, error_lines} =
              let val (res, context) = f context
              in (res, {context = context, reports_text = reports_text, error_lines = error_lines})
              end

fun map_reports_text f {context, reports_text, error_lines} =
                       {context = context, reports_text = f reports_text, error_lines = error_lines}

fun map_error_lines f {context, reports_text, error_lines} =
                       {context = context, reports_text = reports_text, error_lines = f error_lines}

(**)

fun map_env_tree' f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                let val (res, env_tree) = f env_tree
                in (res, {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                    rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang})
                end

fun map_env_lang_tree f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                let val (env_lang, env_tree) = f env_lang env_tree
                in {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                    rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang}
                end

fun map_env_lang_tree' f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                let val (res, (env_lang, env_tree)) = f env_lang env_tree
                in (res, {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                    rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang})
                end

(**)

fun get_scopes (t : env_lang) = #scopes t

(**)

val empty_env_lang : env_lang = 
        {var_table = {tyidents = Symtab.make [], idents = Symtab.make []}, 
         scopes = [], namesupply = 0, stream_ignored = [],
         env_directives = Symtab.empty}
fun empty_env_tree context =
        {context = context, reports_text = [], error_lines = []}
val empty_rule_output : rule_output = 
        {output_pos = NONE, output_vacuous = true, output_env = NONE}
fun make env_lang stream_lang env_tree =
       { env_lang = env_lang
       , env_tree = env_tree
       , rule_output = empty_rule_output
       , rule_input = ([], 0)
       , stream_hook = []
       , stream_lang = ( Stream_regular
                       , map_filter (fn C_Scan.Right (C_Lex.Token (_, (C_Lex.Space, _))) => NONE
                                      | C_Scan.Right (C_Lex.Token (_, (C_Lex.Comment _, _))) => NONE
                                      | C_Scan.Right tok => SOME (C_Scan.Right tok)
                                      | C_Scan.Left antiq => SOME (C_Scan.Left antiq))
                                    stream_lang) }
fun string_of (env_lang : env_lang) = 
  let fun dest0 x f = x |> Symtab.dest |> map f
      fun dest {tyidents, idents} =
            (dest0 tyidents #1, dest0 idents (fn (i, (_,_,v)) =>
                                               (i, if #global v then "global" else "local")))
  in \<^make_string> ( ("var_table", dest (#var_table env_lang))
                 , ("scopes", map (fn (id, i) =>
                                    ( Option.map (fn C_Ast.Ident0 (i, _, _) =>
                                                   C_Ast.meta_of_logic i)
                                                 id
                                    , dest i))
                                  (#scopes env_lang))
                 , ("namesupply", #namesupply env_lang)
                 , ("stream_ignored", #stream_ignored env_lang)) end

val namespace_typedef = "typedef"
val namespace_tag = "tag"
val namespace_enum = namespace_tag

(**)

val encode_positions =
     map (Position.dest
       #> (fn pos => ((#line pos, #offset pos, #end_offset pos), #props pos)))
  #> let open XML.Encode in list (pair (triple int int int) properties) end
  #> YXML.string_of_body
  
val decode_positions =
     YXML.parse_body
  #> let open XML.Decode in list (pair (triple int int int) properties) end
  #> map ((fn ((line, offset, end_offset), props) =>
           {line = line, offset = offset, end_offset = end_offset, props = props})
          #> Position.make)

end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/context.ML\<close>\<close> \<open>
structure C_Env_Ext =
struct

local
fun map_tyidents' f = C_Env.map_var_table (C_Env.map_tyidents f)
fun map_tyidents f = C_Env.map_env_lang (map_tyidents' f)
in
fun map_tyidents_typedef f =
                       map_tyidents (Symtab.map_default (C_Env.namespace_typedef, Symtab.empty) f)
fun map_tyidents_enum f = map_tyidents (Symtab.map_default (C_Env.namespace_enum, Symtab.empty) f)
fun map_tyidents'_typedef f =
                        map_tyidents' (Symtab.map_default (C_Env.namespace_typedef, Symtab.empty) f)
fun map_tyidents'_enum f = map_tyidents' (Symtab.map_default (C_Env.namespace_enum, Symtab.empty) f)
end
fun map_idents' f = C_Env.map_var_table (C_Env.map_idents f)
fun map_idents f = C_Env.map_env_lang (map_idents' f)

(**)

fun map_var_table f = C_Env.map_env_lang (C_Env.map_var_table f)
fun map_scopes f = C_Env.map_env_lang (C_Env.map_scopes f)
fun map_namesupply f = C_Env.map_env_lang (C_Env.map_namesupply f)
fun map_stream_ignored f = C_Env.map_env_lang (C_Env.map_stream_ignored f)

(**)

local
fun get_tyidents' namespace (env_lang : C_Env.env_lang) =
  case Symtab.lookup (env_lang |> #var_table |> #tyidents) namespace of
    NONE => Symtab.empty
  | SOME t => t

fun get_tyidents namespace (t : C_Env.T) = get_tyidents' namespace (#env_lang t)
in
val get_tyidents_typedef = get_tyidents C_Env.namespace_typedef
val get_tyidents_enum = get_tyidents C_Env.namespace_enum
val get_tyidents'_typedef = get_tyidents' C_Env.namespace_typedef
val get_tyidents'_enum = get_tyidents' C_Env.namespace_enum
end

fun get_idents (t:C_Env.T) = #env_lang t |> #var_table |> #idents
fun get_idents' (env:C_Env.env_lang) = env |> #var_table |> #idents

(**)

fun get_var_table (t:C_Env.T) = #env_lang t |> #var_table
fun get_scopes (t:C_Env.T) = #env_lang t |> #scopes
fun get_namesupply (t:C_Env.T) = #env_lang t |> #namesupply

(**)

fun map_output_pos f = C_Env.map_rule_output (C_Env.map_output_pos f)
fun map_output_vacuous f = C_Env.map_rule_output (C_Env.map_output_vacuous f)
fun map_output_env f = C_Env.map_rule_output (C_Env.map_output_env f)

(**)

fun get_output_pos (t : C_Env.T) = #rule_output t |> #output_pos

(**)

fun map_context f = C_Env.map_env_tree (C_Env.map_context f)
fun map_reports_text f = C_Env.map_env_tree (C_Env.map_reports_text f)

(**)

fun get_context (t : C_Env.T) = #env_tree t |> #context
fun get_reports_text (t : C_Env.T) = #env_tree t |> #reports_text

(**)

fun map_env_directives' f {var_table, scopes, namesupply, stream_ignored, env_directives} =
  let val (res, env_directives) = f env_directives
  in (res, {var_table = var_table, scopes = scopes, namesupply = namesupply, 
                      stream_ignored = stream_ignored, env_directives = env_directives})
  end

(**)

fun map_stream_lang' f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
  let val (res, stream_lang) = f stream_lang
  in (res, {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
            rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang})
  end

(**)

fun context_map (f : C_Env.env_tree -> C_Env.env_tree) =
  C_Env.empty_env_tree #> f #> #context

fun context_map' (f : C_Env.env_tree -> 'a * C_Env.env_tree) =
  C_Env.empty_env_tree #> f #> apsnd #context

(**)

fun list_lookup tab name = flat (map (fn (x, _, _) => x) (the_list (Symtab.lookup tab name)))

end

\<close>

end
