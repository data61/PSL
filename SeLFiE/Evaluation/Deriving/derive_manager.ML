signature DERIVE_MANAGER =
sig
  (* identifier, description, (fn dtyp_name => param => derive-method) *)
  val register_derive : string -> string -> (string -> string -> theory -> theory) -> theory -> theory
  (* identifier, description, (fn dtyp_name => param => derive-method) *)
  val derive : string -> string -> string -> theory -> theory
  val derive_cmd : string -> string -> string -> theory -> theory
  (* print all registered deriving-methods  *)
  val print_info : theory -> unit
end

structure Derive_Manager : DERIVE_MANAGER =
struct

structure Derive_Data = Theory_Data
  (
    type T =
      (string * (string -> string -> theory -> theory)) Symtab.table  (* descr * derive-fun *)

    val empty = Symtab.empty
    val extend = I
    val merge = Symtab.merge (K true)
  )

val derive_options =
  Derive_Data.get #> Symtab.dest #> map (fn (id, (descr, _)) => (id, descr))

(* FIXME: possibly use Pretty function for presentation. *)
fun print_info thy =
  let
    val _ = writeln "The following sorts can be derived"
    val _ = derive_options thy |> sort_by fst |> map (fn (id,descr) => writeln (id ^ ": " ^ descr))
  in () end

fun register_derive id descr f thy =
  if Symtab.defined (Derive_Data.get thy) id then
    error ("Identifier " ^ quote id ^ " already in use for " ^ quote "deriving")
  else
    Derive_Data.map (Symtab.update_new (id, (descr, f))) thy

fun gen_derive prep id dtname param thy =
  (case Symtab.lookup (Derive_Data.get thy) id of
    NONE => error ("No handler to derive sort " ^ quote id ^
      " is registered. Try " ^ quote "print_derives" ^ " to see available sorts.")
  | SOME (_, f) => f (prep thy dtname) param thy)

val derive = gen_derive (K I)

fun derive_cmd id param dtname = gen_derive
  (fn thy => fst o dest_Type o Syntax.parse_typ (Proof_Context.init_global thy)) id dtname param
  
(* TODO: also check for alternative of  *)
(* NB: Proof_Context.read_type_name_proper ctxt false could be an alternative. *)

val _ =
  Outer_Syntax.command @{command_keyword print_derives} "lists all registered sorts which can be derived"
    (Scan.succeed (Toplevel.theory (tap print_info)))

val _ =
  Outer_Syntax.command @{command_keyword derive} "derives some sort"
    (Parse.parname -- Parse.name -- Scan.repeat1 Parse.type_const >> (fn ((param, s), tycons) =>
      Toplevel.theory (fold (derive_cmd s param) tycons)))

end

