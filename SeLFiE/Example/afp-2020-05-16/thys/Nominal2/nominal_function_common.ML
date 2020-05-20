(*  Nominal Function Common
    Author: Christian Urban

    heavily based on the code of Alexander Krauss
    (code forked on 5 June 2011)

Redefinition of config datatype
*)

signature NOMINAL_FUNCTION_DATA =
sig

type nominal_info =
 {is_partial : bool,
  defname : string,
    (* contains no logical entities: invariant under morphisms: *)
  add_simps : (binding -> binding) -> string -> (binding -> binding) ->
    Token.src list -> thm list -> local_theory -> thm list * local_theory,
  case_names : string list,
  fs : term list,
  R : term,
  psimps: thm list,
  pinducts: thm list,
  simps : thm list option,
  inducts : thm list option,
  termination: thm,
  eqvts: thm list}

end


structure Nominal_Function_Common =
struct

type nominal_info =
 {is_partial : bool,
  defname : string,
    (* contains no logical entities: invariant under morphisms: *)
  add_simps : (binding -> binding) -> string -> (binding -> binding) ->
    Token.src list -> thm list -> local_theory -> thm list * local_theory,
  case_names : string list,
  fs : term list,
  R : term,
  psimps: thm list,
  pinducts: thm list,
  simps : thm list option,
  inducts : thm list option,
  termination: thm,
  eqvts: thm list}

fun morph_function_data ({add_simps, case_names, fs, R, psimps, pinducts,
  simps, inducts, termination, defname, is_partial, eqvts} : nominal_info) phi =
    let
      val term = Morphism.term phi val thm = Morphism.thm phi val fact = Morphism.fact phi
      val name = Binding.name_of o Morphism.binding phi o Binding.name
    in
      { add_simps = add_simps, case_names = case_names,
        fs = map term fs, R = term R, psimps = fact psimps,
        pinducts = fact pinducts, simps = Option.map fact simps,
        inducts = Option.map fact inducts, termination = thm termination,
        defname = name defname, is_partial=is_partial, eqvts = fact eqvts }
    end

structure NominalFunctionData = Generic_Data
(
  type T = (term * nominal_info) Item_Net.T;
  val empty : T = Item_Net.init (op aconv o apply2 fst) (single o fst);
  val extend = I;
  fun merge tabs : T = Item_Net.merge tabs;
)

val get_function = NominalFunctionData.get o Context.Proof;


fun lift_morphism ctxt f =
  let
    fun term t = Thm.term_of (Drule.cterm_rule f (Thm.cterm_of ctxt t))
  in
    Morphism.morphism "lift_morphism"
      {binding = [],
       typ = [Logic.type_map term],
       term = [term],
       fact = [map f]}
  end

fun import_function_data t ctxt =
  let
    val ct = Thm.cterm_of ctxt t
    val inst_morph = lift_morphism ctxt o Thm.instantiate

    fun match (trm, data) =
      SOME (morph_function_data data (inst_morph (Thm.match (Thm.cterm_of ctxt trm, ct))))
      handle Pattern.MATCH => NONE
  in
    get_first match (Item_Net.retrieve (get_function ctxt) t)
  end

fun import_last_function ctxt =
  case Item_Net.content (get_function ctxt) of
    [] => NONE
  | (t, data) :: _ =>
    let
      val ([t'], ctxt') = Variable.import_terms true [t] ctxt
    in
      import_function_data t' ctxt'
    end

val all_function_data = Item_Net.content o get_function

fun add_function_data (data : nominal_info as {fs, termination, ...}) =
  NominalFunctionData.map (fold (fn f => Item_Net.update (f, data)) fs)
  #> Function_Common.store_termination_rule termination




(* Configuration management *)
datatype nominal_function_opt
  = Sequential
  | Default of string
  | DomIntros
  | No_Partials
  | Invariant of string

datatype nominal_function_config = NominalFunctionConfig of
 {sequential: bool,
  default: string option,
  domintros: bool,
  partials: bool,
  inv: string option}

fun apply_opt Sequential (NominalFunctionConfig {sequential, default, domintros, partials, inv}) =
    NominalFunctionConfig
      {sequential=true, default=default, domintros=domintros, partials=partials, inv=inv}
  | apply_opt (Default d) (NominalFunctionConfig {sequential, default, domintros, partials, inv}) =
    NominalFunctionConfig
      {sequential=sequential, default=SOME d, domintros=domintros, partials=partials, inv=inv}
  | apply_opt DomIntros (NominalFunctionConfig {sequential, default, domintros, partials, inv}) =
    NominalFunctionConfig
      {sequential=sequential, default=default, domintros=true, partials=partials, inv=inv}
  | apply_opt No_Partials (NominalFunctionConfig {sequential, default, domintros, partials, inv}) =
    NominalFunctionConfig
      {sequential=sequential, default=default, domintros=domintros, partials=false, inv=inv}
  | apply_opt (Invariant s) (NominalFunctionConfig {sequential, default, domintros, partials, inv}) =
    NominalFunctionConfig
      {sequential=sequential, default=default, domintros=domintros, partials=partials, inv = SOME s}

val nominal_default_config =
  NominalFunctionConfig { sequential=false, default=NONE,
    domintros=false, partials=true, inv=NONE}

datatype nominal_function_result = NominalFunctionResult of
 {fs: term list,
  G: term,
  R: term,
  psimps : thm list,
  simple_pinducts : thm list,
  cases : thm,
  termination : thm,
  domintros : thm list option,
  eqvts : thm list}

end
