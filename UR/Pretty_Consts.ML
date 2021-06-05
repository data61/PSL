(* Utility functions. 

This is motly copied and pasted from  Pure/Tools/find_consts.ML
Author: Timothy Bourke and Gerwin Klein, NICTA

The only major difference from the original file is that
this version does not add extra texts to the output.

ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2020,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are 
met:

* Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer in the 
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS 
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED 
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A 
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT 
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, 
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY 
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

structure Pretty_Consts =
struct

local

fun check_const pred (c, (ty, _)) = 
  if pred (c, ty) then SOME (Term.size_of_typ ty) else NONE;

fun matches_subtype thy typat =
  Term.exists_subtype (fn ty => Sign.typ_instance thy (ty, typat));

fun opt_not f (c as (_, (ty, _))) =
  if is_some (f c) then NONE else SOME (Term.size_of_typ ty);

fun filter_const _ _ NONE = NONE
  | filter_const c f (SOME rank) =
      (case f c of
        NONE => NONE
      | SOME i => SOME (Int.min (rank, i)));

in

fun pretty_consts ctxt raw_criteria =
  let
    val thy = Proof_Context.theory_of ctxt;
    val low_ranking = 10000;

    fun make_pattern crit =
      let
        val raw_T = Syntax.parse_typ ctxt crit;
        val t =
          Syntax.check_term
            (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
            (Term.dummy_pattern raw_T);
      in Term.type_of t end;

    fun make_match (Find_Consts.Strict arg) =
          let val qty = make_pattern arg; in
            fn (_, (ty, _)) =>
              let
                val tye = Sign.typ_match thy (qty, ty) Vartab.empty;
                val sub_size =
                  Vartab.fold (fn (_, (_, t)) => fn n => Term.size_of_typ t + n) tye 0;
              in SOME sub_size end handle Type.TYPE_MATCH => NONE
          end
      | make_match (Find_Consts.Loose arg) =
          check_const (matches_subtype thy (make_pattern arg) o snd)
      | make_match (Find_Consts.Name arg) = check_const (match_string arg o fst);

    fun make_criterion (b, crit) = (if b then I else opt_not) (make_match crit);
    val criteria = map make_criterion raw_criteria;

    fun user_visible (c, _) =
      if Consts.is_concealed (Proof_Context.consts_of ctxt) c
      then NONE else SOME low_ranking;

    fun eval_entry c =
      fold (filter_const c) (user_visible :: criteria) (SOME low_ranking);

    val {constants, ...} = Consts.dest (Sign.consts_of thy);
    val matches =
      fold (fn c => (case eval_entry c of NONE => I | SOME rank => cons (rank, c))) constants []
      |> sort (prod_ord (rev_order o int_ord) (string_ord o apply2 fst))
      |> map (apsnd fst o snd);
in
  matches
end;

end

end;