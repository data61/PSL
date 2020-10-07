(*
  File: wellform.ML
  Author: Bohua Zhan

  Wellformed-ness of terms.
*)

signature WELLFORM =
sig
  val register_wellform_data: string * string list -> theory -> theory
  val lookup_wellform_data: theory -> term -> term list
  val is_subterm_wellform_data':
      theory -> term -> term -> (term * term) option
  val is_subterm_wellform_data:
      theory -> term -> term list -> (term * term) option
  val lookup_wellform_pattern: theory -> term * term -> (term * term) option
end;

structure WellForm : WELLFORM =
struct

(* Each entry in the table consists of a term of the form f ?a_1
   ... ?a_n, where f is a constant, and each ?a_i is a pure schematic
   variable, paired with a list of requirements for the term to be
   valid. It is indexed under the string of the constant f.
 *)
structure Data = Theory_Data (
  type T = (term * term list) Symtab.table
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (op =)
)

(* Add a term with its requirements to the table. *)
fun register_wellform_data (t_str, req_strs) thy =
    let
      val ctxt = Proof_Context.init_global thy
      val t = Proof_Context.read_term_pattern ctxt t_str
      val ctxt' = Variable.declare_term t ctxt
      val reqs = map (Proof_Context.read_term_pattern ctxt') req_strs

      val (f, args) = Term.strip_comb t
      val _ = assert (Term.is_Const f)
                     "add_wellform_data: head must be Const."
      val _ = assert (forall Term.is_Free args)
                     "add_wellform_data: arguments must be Free."
      val (c, _) = Term.dest_Const f
    in
      thy |> Data.map (Symtab.update_new (c, (t, reqs)))
    end

(* Lookup table for the given term t. If nothing is found, return the
   empty list by default.
 *)
fun lookup_wellform_data thy t =
    let
      val (f, args) = Term.strip_comb t
      val data = Data.get thy
    in
      case f of
          Const (c, _) =>
          (case Symtab.lookup data c of
               NONE => []
             | SOME (t', reqs) =>
               let
                 val (_, vars) = Term.strip_comb t'
               in
                 if length vars <> length args then [] else
                 let
                   val tys = map fastype_of vars ~~ map fastype_of args
                   val tyinst = fold (Sign.typ_match thy) tys Vartab.empty
                   val vars' = map (Envir.subst_term_types tyinst) vars
                   fun subst_fun req =
                       req |> Envir.subst_term_types tyinst
                           |> Term.subst_atomic (vars' ~~ args)
                 in
                   distinct (op aconv) (map subst_fun reqs)
                 end
                 handle Type.TYPE_MATCH => []
               end)
        | _ => []
    end

(* Check whether req is part of the wellformed-ness data of a subterm
   of t. If so, return the pair SOME (t', req), where t' is a subterm
   of t and req is a wellformed-ness data of t'. Otherwise return
   NONE.
 *)
fun is_subterm_wellform_data' thy req t =
    if member (op aconv) (lookup_wellform_data thy t) req then
      SOME (t, req)
    else let
      val (_, args) = Term.strip_comb t
    in
      get_first (is_subterm_wellform_data' thy req) args
    end

fun is_subterm_wellform_data thy req ts =
    get_first (is_subterm_wellform_data' thy req) ts

(* Given a term t and wellform data for t, return the relevant
   wellform pattern.
 *)
fun lookup_wellform_pattern thy (t, wf_t) =
    let
      val (f, args) = Term.strip_comb t
      val data = Data.get thy
    in
      case f of
          Const (c, _) =>
          (case Symtab.lookup data c of
               NONE => NONE
             | SOME (t', reqs) =>
               let
                 val (_, vars) = Term.strip_comb t'
               in
                 if length vars <> length args then NONE
                 else let
                   val tys = map fastype_of vars ~~ map fastype_of args
                   val tyinst = fold (Sign.typ_match thy) tys Vartab.empty
                   val vars' = map (Envir.subst_term_types tyinst) vars
                   fun subst_fun t =
                       t |> Envir.subst_term_types tyinst
                         |> Term.subst_atomic (vars' ~~ args)
                   val reqs' = filter (fn req => wf_t aconv subst_fun req) reqs
                 in
                   case reqs' of
                       [] => NONE
                     | req' :: _ =>
                       SOME (apply2 (Envir.subst_term_types tyinst) (t', req'))
                 end
               end)
        | _ => NONE
    end

end  (* structure WellForm. *)

val register_wellform_data = WellForm.register_wellform_data
