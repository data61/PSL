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

theory  Isabelle_code_runtime
imports Main
  keywords "code_reflect'" :: thy_decl
begin

ML\<open>
structure Code_Runtime =
struct
(*  Title:      Tools/Code/code_runtime.ML
    Author:     Florian Haftmann, TU Muenchen

Runtime services building on code generation into implementation language SML.
*)

open Basic_Code_Symbol;
open Basic_Code_Thingol;

(** evaluation **)

(* technical prerequisites *)


val trace = Attrib.setup_config_bool @{binding "code_runtime_trace"} (K false);

fun exec ctxt verbose code =
 (if Config.get ctxt trace then tracing code else ();
  ML_Context.exec (fn () =>
    ML_Compiler0.ML ML_Env.context
      {line = 0, file = "generated code", verbose = verbose, debug = false} code));



(* evaluation into target language values *)



(* evaluation for truth or nothing *)



(** full static evaluation -- still with limited coverage! **)

fun evaluation_code ctxt module_name program tycos consts all_public =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (ml_modules, target_names) =
      Code_Target.produce_code_for ctxt
        Code_Runtime.target module_name NONE [] program all_public (map Constant consts @ map Type_Constructor tycos);
    val ml_code = space_implode "\n\n" (map snd ml_modules);
    val (consts', tycos') = chop (length consts) target_names;
    val consts_map = map2 (fn const =>
      fn NONE =>
          error ("Constant " ^ (quote o Code.string_of_const thy) const ^
            "\nhas a user-defined serialization")
       | SOME const' => (const, const')) consts consts'
    val tycos_map = map2 (fn tyco =>
      fn NONE =>
          error ("Type " ^ quote (Proof_Context.markup_type ctxt tyco) ^
            "\nhas a user-defined serialization")
        | SOME tyco' => (tyco, tyco')) tycos tycos';
  in (ml_code, (tycos_map, consts_map)) end;



(** code antiquotation **)



(** reflection support **)

fun check_datatype thy tyco some_consts =
  let
    val constrs = (map fst o snd o fst o Code.get_type thy) tyco;
    val _ = case some_consts
     of SOME consts =>
          let
            val missing_constrs = subtract (op =) consts constrs;
            val _ = if null missing_constrs then []
              else error ("Missing constructor(s) " ^ commas_quote missing_constrs
                ^ " for datatype " ^ quote tyco);
            val false_constrs = subtract (op =) constrs consts;
            val _ = if null false_constrs then []
              else error ("Non-constructor(s) " ^ commas_quote false_constrs
                ^ " for datatype " ^ quote tyco)
          in () end
      | NONE => ();
  in (tyco, constrs) end;

fun add_eval_tyco (tyco, tyco') thy =
  let
    val k = Sign.arity_number thy tyco;
    fun pr pr' _ [] = tyco'
      | pr pr' _ [ty] =
          Code_Printer.concat [pr' Code_Printer.BR ty, tyco']
      | pr pr' _ tys =
          Code_Printer.concat [Code_Printer.enum "," "(" ")" (map (pr' Code_Printer.BR) tys), tyco']
  in
    thy
    |> Code_Target.set_printings (Type_Constructor (tyco, [(Code_Runtime.target, SOME (k, pr))]))
  end;

fun add_eval_constr (const, const') thy =
  let
    val k = Code.args_number thy const;
    fun pr pr' fxy ts = Code_Printer.brackify fxy
      (const' :: the_list (Code_Printer.tuplify pr' Code_Printer.BR (map fst ts)));
  in
    thy
    |> Code_Target.set_printings (Constant (const,
      [(Code_Runtime.target, SOME (Code_Printer.simple_const_syntax (k, pr)))]))
  end;

fun add_eval_const (const, const') = Code_Target.set_printings (Constant
  (const, [(Code_Runtime.target, SOME (Code_Printer.simple_const_syntax (0, (K o K o K) const')))]));

fun process_reflection (code, (tyco_map, (constr_map, const_map))) module_name NONE thy =
      thy
      |> Code_Target.add_reserved Code_Runtime.target module_name
      |> Context.theory_map (exec (Proof_Context.init_global thy (*FIXME*)) true code)
      |> fold (add_eval_tyco o apsnd Code_Printer.str) tyco_map
      |> fold (add_eval_constr o apsnd Code_Printer.str) constr_map
      |> fold (add_eval_const o apsnd Code_Printer.str) const_map
  | process_reflection (code, _) _ (SOME file_name) thy =
      let
        val preamble =
          "(* Generated from " ^
            Path.implode (Resources.thy_path (Path.basic (Context.theory_name thy))) ^
          "; DO NOT EDIT! *)";
        val _ = File.write (Path.explode file_name) (preamble ^ "\n\n" ^ code);
      in
        thy
      end;

fun gen_code_reflect prep_type prep_const all_public raw_datatypes raw_functions module_name some_file thy  =
  let
    val ctxt = Proof_Context.init_global thy;
    val datatypes = map (fn (raw_tyco, raw_cos) =>
      (prep_type ctxt raw_tyco, (Option.map o map) (prep_const thy) raw_cos)) raw_datatypes;
    val (tycos, constrs) = map_split (uncurry (check_datatype thy)) datatypes
      |> apsnd flat;
    val functions = map (prep_const thy) raw_functions;
    val consts = constrs @ functions;
    val program = Code_Thingol.consts_program ctxt consts;
    val result = evaluation_code ctxt module_name program tycos consts all_public
      |> (apsnd o apsnd) (chop (length constrs));
  in
    thy
    |> process_reflection result module_name some_file
  end;

val code_reflect_cmd = gen_code_reflect Code_Target.read_tyco Code.read_const;


(** Isar setup **)

local

val parse_datatype =
  Parse.name --| @{keyword "="} --
    (((Parse.sym_ident || Parse.string) >> (fn "_" => NONE | _ => Scan.fail ()))
    || ((Parse.term ::: (Scan.repeat (@{keyword "|"} |-- Parse.term))) >> SOME));

in

val _ =
  Outer_Syntax.command @{command_keyword code_reflect'}
    "enrich runtime environment with generated code"
    (Scan.optional (@{keyword "open"} |-- Scan.succeed true) false --
     Parse.name -- Scan.optional (@{keyword "datatypes"} |-- Parse.!!!  (parse_datatype
      ::: Scan.repeat (@{keyword "and"} |-- parse_datatype))) []
    -- Scan.optional (@{keyword "functions"} |-- Parse.!!!  (Scan.repeat1 Parse.name)) []
    -- Scan.option (@{keyword "file"} |-- Parse.!!! Parse.name)
    >> (fn ((((all_public, module_name), raw_datatypes), raw_functions), some_file) => Toplevel.theory
      (code_reflect_cmd all_public raw_datatypes raw_functions module_name some_file)))

end; (*local*)

end
\<close>

end
