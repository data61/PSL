(******************************************************************************
 * ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.
 *
 * Copyright (c) 1986-2018 Contributors (in the changeset history)
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

chapter\<open>Part ...\<close>

theory  Isabelle_code_target
imports Main
keywords "attach"
  and "lazy_code_printing" "apply_code_printing" "apply_code_printing_reflect"
           :: thy_decl
begin

subsection\<open>beginning (lazy code printing)\<close>

ML\<open>
structure Isabelle_Code_Target =
struct
(*  Title:      Tools/Code/code_target.ML
    Author:     Florian Haftmann, TU Muenchen

Generic infrastructure for target language data.
*)

open Basic_Code_Symbol;
open Basic_Code_Thingol;



(** checking and parsing of symbols **)


val parse_classrel_ident = Parse.class --| @{keyword "<"} -- Parse.class;


val parse_inst_ident = Parse.name --| @{keyword "::"} -- Parse.class;



(** serializations and serializer **)

(* serialization: abstract nonsense to cover different destinies for generated code *)



(* serializers: functions producing serializations *)



(** theory data **)



(** serializer usage **)

(* montage *)



(* code generation *)

fun prep_destination s = ({physical = true}, (Path.explode s, Position.none));

fun export_code_cmd all_public raw_cs seris thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val cs = Code_Thingol.read_const_exprs ctxt raw_cs;
  in
    thy |> Named_Target.theory_map
      (Code_Target.export_code all_public cs
        ((map o apfst o apsnd o Option.map) prep_destination seris))
  end;



(** serializer configuration **)

(* reserved symbol names *)



(* checking of syntax *)



(* custom symbol names *)



(* custom printings *)



(* concrete syntax *)


(** Isar setup **)

fun parse_single_symbol_pragma parse_keyword parse_isa parse_target =
  parse_keyword |-- Parse.!!! (parse_isa --| (@{keyword "\<rightharpoonup>"} || @{keyword "=>"})
    -- Parse.and_list1 (@{keyword "("} |-- (Parse.name --| @{keyword ")"} -- Scan.option parse_target)));

fun parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  parse_single_symbol_pragma @{keyword "constant"} Parse.term parse_const
    >> Constant
  || parse_single_symbol_pragma @{keyword "type_constructor"} Parse.type_const parse_tyco
    >> Type_Constructor
  || parse_single_symbol_pragma @{keyword "type_class"} Parse.class parse_class
    >> Type_Class
  || parse_single_symbol_pragma @{keyword "class_relation"} parse_classrel_ident parse_classrel
    >> Class_Relation
  || parse_single_symbol_pragma @{keyword "class_instance"} parse_inst_ident parse_inst
    >> Class_Instance
  || parse_single_symbol_pragma @{keyword "code_module"} Parse.name parse_module
    >> Code_Symbol.Module;

fun parse_symbol_pragmas parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  Parse.enum1 "|" (Parse.group (fn () => "code symbol pragma")
    (parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module));

end
\<close>

ML\<open>
structure Code_printing = struct
datatype code_printing = Code_printing of
     (string * (bstring * Code_Printer.raw_const_syntax option) list,
      string * (bstring * Code_Printer.tyco_syntax option) list,
      string * (bstring * string option) list,
      (string * string) * (bstring * unit option) list,
      (xstring * string) * (bstring * unit option) list,
      bstring * (bstring * (string * Code_Symbol.T list) option) list)
      Code_Symbol.attr
      list

structure Data_code = Theory_Data
  (type T = code_printing list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_empty = ""

val () =
  Outer_Syntax.command @{command_keyword lazy_code_printing} "declare dedicated printing for code symbols"
    (Isabelle_Code_Target.parse_symbol_pragmas (Code_Printer.parse_const_syntax) (Code_Printer.parse_tyco_syntax)
      Parse.string (Parse.minus >> K ()) (Parse.minus >> K ())
      (Parse.text -- Scan.optional (@{keyword "attach"} |-- Scan.repeat1 Parse.term >> map Code_Symbol.Constant) [])
      >> (fn code =>
            Toplevel.theory (Data_code.map (Symtab.map_default (code_empty, []) (fn l => Code_printing code :: l)))))

fun apply_code_printing thy =
    (case Symtab.lookup (Data_code.get thy) code_empty of SOME l => rev l | _ => [])
 |> (fn l => fold (fn Code_printing l => fold Code_Target.set_printings l) l thy)

val () =
  Outer_Syntax.command @{command_keyword apply_code_printing} "apply dedicated printing for code symbols"
    (Parse.$$$ "(" -- Parse.$$$ ")" >> K (Toplevel.theory apply_code_printing))

fun reflect_ml source thy =
  case ML_Context.exec (fn () =>
            ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags) source) (Context.Theory thy) of
    Context.Theory thy => thy

fun apply_code_printing_reflect thy =
    (case Symtab.lookup (Data_code.get thy) code_empty of SOME l => rev l | _ => [])
 |> (fn l => fold (fn Code_printing l =>
      fold (fn Code_Symbol.Module (_, l) =>
                 fold (fn ("SML", SOME (txt, _)) => reflect_ml (Input.source false txt (Position.none, Position.none))
                        | _ => I) l
             | _ => I) l) l thy)

val () =
  Outer_Syntax.command @{command_keyword apply_code_printing_reflect} "apply dedicated printing for code symbols"
    (Parse.ML_source >> (fn src => Toplevel.theory (apply_code_printing_reflect o reflect_ml src)))

end

\<close>

end
