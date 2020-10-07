signature PATTERN_COMPATIBILITY = sig
  val enabled: bool Config.T
end

structure Pattern_Compatibility : PATTERN_COMPATIBILITY = struct

open Dict_Construction_Util

fun non_overlapping (Const x) (Const y) = not (x = y)
  | non_overlapping (Const _) (_ $ _) = true
  | non_overlapping (_ $ _) (Const _) = true
  | non_overlapping (t1 $ t2) (u1 $ u2) = non_overlapping t1 u1 orelse non_overlapping t2 u2
  | non_overlapping _ _ = false

fun extract thm =
  let
    val lhs = fst (Logic.dest_equals (Thm.prop_of thm))
    val name = fst (dest_Const (fst (strip_comb lhs)))
  in (name, (lhs, thm)) end

fun functrans ctxt thms =
  let
    val groups = AList.group op = (map extract thms)

    fun process_group (name, eqs) =
      let
        val const = Pretty.string_of (pretty_const ctxt name)

        fun pattern_renames (t1 $ t2) (u1 $ u2) =
              pattern_renames t1 u1 @ (if t1 = u1 then pattern_renames t2 u2 else [])
          | pattern_renames t u =
              if t = u orelse non_overlapping t u then
                []
              else
                case t of
                  Var (iname, _) => [(iname, u)]
                | _ => error ("Unsupported pattern situation in " ^ const)

        fun is_bogus_eq term =
          case term of
            (Const (@{const_name equal_class.equal}, _) $ t $ u) =>
              t = u andalso is_Var t
          | _ => false

        fun insert (lhs1, thm1) (changed, (lhss, thms)) =
          if is_bogus_eq lhs1 then
            (true, (lhss, thms))
          else
            let
              val renamess =
                map (fn lhs2 =>
                  case pattern_renames lhs1 lhs2 of
                    [] => NONE
                  | xs => SOME xs) lhss
                |> cat_options

              fun rename renames =
                let
                  val inst = map (fn (t, u) => (t, Thm.cterm_of ctxt u)) renames
                  val msg = "Renaming pattern variables in " ^ const
                  val _ = warning msg
                in
                  Drule.infer_instantiate ctxt inst thm1
                end
            in
              case renamess of
                [] => (changed, (lhs1 :: lhss, thm1 :: thms))
              | [renames] => (true, (lhss, rename renames :: thms))
              | _ => error ("Too many incompatible equations in " ^ const ^ ", this is unsupported")
            end
      in
        fold insert eqs (false, ([], []))
        |> apsnd snd
      end

    val (changed, thms) =
      map process_group groups
      |> split_list
      |> apsnd flat
      |> apfst (exists I)
  in
    if changed then SOME thms else NONE
  end

val enabled = setup_conditional_functrans @{binding pattern_compatibility} functrans

end