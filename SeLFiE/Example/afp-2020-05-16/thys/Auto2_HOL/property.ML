(*
  File: property.ML
  Author: Bohua Zhan

  Theory data for properties. This data consists of the following parts:

  - Two tables containing property update rules.

  - A table containing list of fields that can have properties.
*)

signature PROPERTY =
sig
  val is_property: term -> bool
  val add_property_field_const: term -> theory -> theory
  val is_property_field: theory -> term -> bool
  val strip_property_field: theory -> term -> term list
  val is_property_prem: theory -> term -> bool
  val get_property_name: term -> string
  val get_property_names: term list -> string list
  val get_property_arg: term -> term
  val get_property_arg_th: thm -> cterm

  (* About the PropertyUpdateData table.*)
  val can_add_property_update: thm -> theory -> bool
  val add_property_update: thm -> theory -> theory
  val lookup_property_update: theory -> string -> thm list
  val lookup_property_update_fun: theory -> string -> thm list
  val instantiate_property_update: Proof.context -> term -> thm -> thm option
end;

structure Property : PROPERTY =
struct

(* Rules deriving new properties of t from other properties of t. They
   are indexed under the names of the properties in the premises.
 *)
structure UpdateData = Theory_Data (
  type T = (thm list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list Thm.eq_thm_prop
)

(* Rules for deriving properties of f x_1 ... x_n from properties of
   x_1, ... x_n. They are indexed under the name of the head function
   f.
 *)
structure UpdateFunData = Theory_Data (
  type T = (thm list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list Thm.eq_thm_prop
)

(* Set of fields of a structure whose property can be considered as
   properties of the structure itself. Relevant when checking
   is_property_prem.
 *)
structure FieldData = Theory_Data (
  type T = unit Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (K true)
)

(* Whether the term is a property predicate applied to a term. *)
fun is_property t =
    let
      val _ = assert (fastype_of t = boolT) "is_property: wrong type"
      val (f, ts) = Term.strip_comb t
    in
      if length ts <> 1 orelse not (Term.is_Const f) then false else
      let
        val T = fastype_of (the_single ts)
        val (dT, _) = Term.strip_type T
      in
        length dT = 0 andalso T <> boolT
      end
    end

(* Insert the following constant as a property field. *)
fun add_property_field_const t thy =
    case Term.head_of t of
        Const (c, T) =>
        let
          val (pTs, _) = Term.strip_type T
          val _ = if length pTs = 1 then ()
                  else error "Add property field: input should be a field."
          val _ = writeln ("Add field " ^ c ^ " as property field.")
        in
          thy |> FieldData.map (Symtab.update_new (c, ()))
        end
      | _ => error "Add property field: input should be a constant."

(* Whether the term is zero or more property field constants applied
   to a Var term.
 *)
fun is_property_field thy t =
    case t of
        Var _ => true
      | Const (c, _) $ t' =>
        Symtab.defined (FieldData.get thy) c andalso is_property_field thy t'
      | _ => false

(* Given a term t, return all possible ways to strip property field
   constants from t. For example, if t is of the form f1(f2(x)), where
   f1 and f2 are property constants, then the result is [f1(f2(x)),
   f2(x), x].
 *)
fun strip_property_field thy t =
    case t of
        Const (c, _) $ t' =>
        if Symtab.defined (FieldData.get thy) c then
          t :: strip_property_field thy t'
        else [t]
      | _ => [t]

(* Stricter condition than is_property: the argument must be a
   schematic variable (up to property fields).
 *)
fun is_property_prem thy t =
    is_property t andalso is_property_field thy (dest_arg t)

val get_property_name = Util.get_head_name

fun get_property_names ts =
    ts |> map get_property_name |> distinct (op =)

(* Return the argument of the property. *)
fun get_property_arg t =
    dest_arg t
    handle Fail "dest_arg" => raise Fail "get_property_arg: t in wrong form."

(* Return the argument of the property theorem as a cterm. *)
fun get_property_arg_th th =
    Thm.dest_arg (cprop_of' th)
    handle CTERM _ => raise Fail "get_property_carg"
         | Fail "dest_Trueprop" => raise Fail "get_property_carg"

(* Add the given rule as a property update. The requirements on th is
   as follows:

   - The conclusion must be a property constant, with argument in the
     form of either ?x or f ?x1 ... ?xn.

   - Each premise must be a property constant on ?x (in the first
     case) or one of ?x1 ... ?xn (in the second case). The argument of
     the property in the conclusion must contain all schematic
     variables of the theorem.
 *)
fun can_add_property_update th thy =
    let
      val (prems, concl) = UtilLogic.strip_horn' th
    in
      if is_property concl andalso forall (is_property_prem thy) prems
      then let
        val concl_arg = get_property_arg concl
        val all_vars = map Var (Term.add_vars (Thm.prop_of th) [])
      in
        if is_Var concl_arg then
          (* First case: check that concl_arg is the only schematic Var. *)
          length all_vars = 1
        else
          (* Second case: concl_arg is of the form f ?x1 ... ?xn. *)
          let
            val args = Util.dest_args concl_arg
          in
            forall is_Var args andalso subset (op aconv) (all_vars, args)
          end
      end
      else false
    end

(* Add the given theorem as a property update rule. Choose which table
   to add the rule to.
 *)
fun add_property_update th thy =
    let
      val (prems, concl) = UtilLogic.strip_horn' th
      val _ = assert (is_property concl)
                     "add_property_update: concl must be a property constant."
      val _ = assert (forall (is_property_prem thy) prems)
                     "add_property_update: prem must be a property premise."
      val concl_arg = get_property_arg concl
      val all_vars = map Var (Term.add_vars (Thm.prop_of th) [])
    in
      if is_Var concl_arg then
        (* First case. Each premise must also be about ?x. Add to
           UpdateData table under the names of the predicates.
         *)
        let
          val _ = assert (length all_vars = 1)
                         "add_property_update: extraneous Vars in th."
          val names = get_property_names prems
          val _ = writeln ("Add property rule for " ^
                           (Util.string_of_list I names))
        in
          thy |> UpdateData.map (
            fold (Symtab.update_list Thm.eq_thm_prop) (map (rpair th) names))
        end
      else
        (* Second case. concl_arg in the form f ?x1 ... ?xn. Add to
           UpdateFunData table under f.
         *)
        let
          val (f, args) = Term.strip_comb concl_arg
          val c =
              case f of
                  Const (c, _) => c
                | _ => raise Fail "add_property_update: f is not constant."
          val _ = assert (forall is_Var args)
                         "add_property_update: all args of concl must be Vars."
          val _ = assert (subset (op aconv) (all_vars, args))
                         "add_property_update: extraneous Vars in th."
          val _ = writeln ("Add property rule for function " ^ c)
        in
          thy |> UpdateFunData.map (Symtab.update_list Thm.eq_thm_prop (c, th))
        end
    end

(* Find update rules of the form P1 x ==> ... ==> Pn x ==> P x, where
   c is one of P1, ... Pn.
 *)
fun lookup_property_update thy c =
    Symtab.lookup_list (UpdateData.get thy) c

(* Find update rules of the form A1 ==> ... ==> An ==>
   P(f(x1,...,xn)), where each A_i is a property on one of x_j. Here c
   is the name of f.
 *)
fun lookup_property_update_fun thy c =
    Symtab.lookup_list (UpdateFunData.get thy) c

(* Instantiate th by matching t with the argument of the conclusion of
   th. Return NONE if instantiation is unsuccessful (because type does
   not match).
 *)
fun instantiate_property_update ctxt t th =
    let
      val (_, concl) = UtilLogic.strip_horn' th
      val concl_arg = get_property_arg concl
      val thy = Proof_Context.theory_of ctxt
    in
      if Sign.typ_instance thy (fastype_of t, fastype_of concl_arg) then
        let
          val err_str = "instantiate_property_update: cannot match with t."
          val inst = Pattern.first_order_match thy (concl_arg, t) fo_init
                     handle Pattern.MATCH => raise Fail err_str
        in
          SOME (Util.subst_thm ctxt inst th)
        end
      else NONE
    end

end  (* structure Property. *)

val add_property_field_const = Property.add_property_field_const
