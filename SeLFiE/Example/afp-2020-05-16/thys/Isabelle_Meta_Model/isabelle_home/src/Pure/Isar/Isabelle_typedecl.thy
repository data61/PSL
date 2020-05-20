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

theory Isabelle_typedecl
imports Main
begin
ML\<open>
structure Isabelle_Typedecl =
struct
(*  Title:      Pure/Isar/typedecl.ML
    Author:     Makarius

Type declarations (with object-logic arities) and type abbreviations.
*)


(* type abbreviations *)

local


fun read_abbrev b ctxt raw_rhs =
  let
    val rhs = Proof_Context.read_typ_syntax (ctxt |> Proof_Context.set_defsort []) raw_rhs;
    val ignored = Term.fold_atyps_sorts (fn (_, []) => I | (T, _) => insert (op =) T) rhs [];
    val _ =
      if not (null ignored) andalso Context_Position.is_visible ctxt then
        warning
          ("Ignoring sort constraints in type variables(s): " ^
            commas_quote (map (Syntax.string_of_typ ctxt) (rev ignored)) ^
            "\nin type abbreviation " ^ (case b of NONE => "" | SOME b => Binding.print b))
      else ();
  in rhs end;

in

fun abbrev_cmd0 b = read_abbrev b
                  o Proof_Context.init_global

end;

end
\<close>
end
