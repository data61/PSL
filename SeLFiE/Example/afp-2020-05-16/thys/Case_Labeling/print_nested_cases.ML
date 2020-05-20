signature PRINT_NESTED_CASES =
sig
  val pretty_cases: Proof.context -> Pretty.T
  val print_cases: Proof.context -> unit
end;

structure Print_Nested_Cases : PRINT_NESTED_CASES =
struct

fun pretty_cases ctxt =
  let
    val prt_term = Syntax.pretty_term ctxt;
    fun prt_asm (a, ts) = Pretty.block (Pretty.breaks
      ((if a = "" then []
        else [Pretty.str a, Pretty.str ":"]) @ map (Pretty.quote o prt_term) ts));
    fun prt_let (xi, t) = Pretty.block
      [Pretty.quote (prt_term (Var (xi, Term.fastype_of t))), Pretty.str " =", Pretty.brk 1,
        Pretty.quote (prt_term t)];

    fun prt_sect _ _ _ [] = []
      | prt_sect head sep prt xs =
          [Pretty.block (Pretty.breaks (head ::
            flat (separate sep (map (single o prt) xs))))];

    val prt_and = Pretty.keyword2 "and"

    fun pretty_assumes asms =
      if forall (null o #2) asms then []
      else prt_sect (Pretty.keyword1 "assume") [prt_and] prt_asm asms
    val pretty_binds = prt_sect (Pretty.keyword1 "let") [prt_and] prt_let
          o map_filter (fn (xi, SOME t) => SOME (xi, t) | _ => NONE)
    val pretty_fixes = prt_sect (Pretty.keyword1 "fix") [prt_and] (fn (x,ty) =>
      Pretty.block [Pretty.str (Binding.name_of x), Pretty.str " :: ", Syntax.pretty_typ ctxt ty])

    fun pretty_case (name, Rule_Cases.Case {cases, fixes, binds, assumes}) =
      Pretty.chunks [Pretty.big_list (name ^ ":")
        (pretty_fixes fixes @ pretty_binds binds @ pretty_assumes assumes @ pretty_cases cases)]
    and pretty_cases cases = if null cases then []
      else [Pretty.big_list "subcases:" (map pretty_case cases)]
    val cases = Proof_Context.dest_cases NONE ctxt
      |> Pretty.big_list "cases:"  o map (Pretty.chunks o single o pretty_case)
  in cases end

val print_cases = Pretty.writeln o pretty_cases

val _ =
  Outer_Syntax.command @{command_keyword "print_nested_cases"} "print nested cases of proof context"
    (Scan.succeed (Toplevel.keep (print_cases o Toplevel.context_of)));

end;
