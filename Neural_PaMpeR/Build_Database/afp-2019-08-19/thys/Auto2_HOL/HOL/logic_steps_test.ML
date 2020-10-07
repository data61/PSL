(*
  File: logic_steps_test.ML
  Author: Bohua Zhan

  Unit test for logic_steps.ML.
*)

local
  val ctxt = @{context}
  val thy = @{theory}
in

val test_norm_all_disj =
    let
      fun test (str1, str2) =
          let
            val (t1, t2) = (Proof_Context.read_term_pattern ctxt str1,
                            Proof_Context.read_term_pattern ctxt str2)
            val ct1 = Thm.cterm_of ctxt t1
            val (vars, ts) = Logic_ProofSteps.strip_all_disj t1
            val res_th = Logic_ProofSteps.norm_all_disj ctxt ct1
          in
            if not (Logic_ProofSteps.mk_all_disj (vars, ts) aconv t2) then
              let
                val _ = trace_t ctxt "Input" t1
                val _ = trace_t ctxt "Output" (Logic_ProofSteps.mk_all_disj (vars, ts))
                val _ = trace_t ctxt "Expected" t2
              in
                raise Fail "test_strip_all_disj"
              end
            else if not (Util.rhs_of res_th aconv t2) then
              let
                val _ = trace_t ctxt "Input" t1
                val _ = trace_t ctxt "Output" (Util.rhs_of res_th)
                val _ = trace_t ctxt "Expected" t2
              in
                raise Fail "test_norm_all_disj"
              end
            else ()
          end

      val test_data = [
        ("A::bool", "A::bool"),
        ("A | B", "A | B"),
        ("A | B | C | D", "A | B | C | D"),
        ("((A | B) | C) | D", "A | B | C | D"),
        ("(A | B | C) | (D | E) | F", "A | B | C | D | E | F"),
        ("~~A", "A::bool"),
        ("~~((A | B) | C)", "A | B | C"),
        ("~(A & B)", "~A | ~B"),
        ("~(A & B & C & D)", "~A | ~B | ~C | ~D"),
        ("~(((A & B) & C) & D)", "~A | ~B | ~C | ~D"),
        ("A --> B", "~A | B"),
        ("A --> B --> C --> D", "~A | ~B | ~C | D"),
        ("A & B --> C", "~A | ~B | C"),
        ("A --> B | C", "~A | B | C"),

        ("p & (q --> r) --> s", "~p | ~(q --> r) | s"),
        ("~ (p & (q --> r)) | s", "~p | ~(q --> r) | s"),

        ("!x. A x", "!x. A x"),
        ("!x y z. P x y z", "!x y z. P x y z"),
        ("!x:S. A x", "!x. x ~: S | A x"),
        ("!x:S. !y:S. !z:S. P x y z",
         "!x y z. x ~: S | y ~: S | z ~: S | P x y z"),
        ("!x. A x --> B x --> C x", "!x. ~A x | ~B x | C x"),
        ("!x. A x --> (!y. B x y --> (!z. C x y z))",
         "!x y z. ~A x | ~B x y | C x y z"),
        ("!x:S. A x --> (!y:S. B x y --> (!z:S. C x y z))",
         "!x y z. x ~: S | ~A x | y ~: S | ~B x y | z ~: S | C x y z"),
        ("!x. (!y. A y) --> B x", "!x. ~(!y. A y) | B x"),
        ("~(EX x. P x)", "!x. ~P x"),
        ("~(EX x:S. P x)", "!x. x ~: S | ~P x"),
        ("~(EX x. P x & Q x)", "!x. ~P x | ~Q x"),
        ("~(EX x:S. P x & Q x)", "!x. x ~: S | ~P x | ~Q x"),
        ("~(EX x y. P x y)", "!x y. ~P x y"),
        ("~(EX x:S. EX y:S. P x y)", "!x y. x ~: S | y ~: S | ~P x y"),
        ("~(EX x. P x & (EX y. Q x y))", "!x y. ~P x | ~Q x y"),

        ("p & (q --> r) --> s", "~p | ~(q --> r) | s"),
        ("~ (p & (q --> r)) | s", "~p | ~(q --> r) | s"),
        ("!x. ?P x", "!x. ?P x"),
        ("(!x. P x) | (!y. Q y)", "!x y. P x | Q y"),
        ("!x. (P::'a=>bool) y", "(P::'a=>bool) y"),
        ("!x. P (y::'a) --> Q y", "~P (y::'a) | Q y")
      ]
    in
      map test test_data
    end

fun free_to_var t =
    case t of
        Free (x, T) => Var ((x, 0), T)
      | _ => raise Fail "free_to_var"

val test_disj_prop_match =
    let
      fun test (str1, str2) =
          let
            val (t, u) = (Proof_Context.read_term_pattern ctxt str1,
                          Syntax.read_term ctxt str2)
            val (var_u, us) = Logic_ProofSteps.strip_all_disj u
            val var_u' = map free_to_var var_u
            val us' = map (subst_atomic (var_u ~~ var_u')) us
            val (cvar_u, cus) = (map Term.dest_Var var_u', map (Thm.cterm_of ctxt) us')
            val (var_t, ts) = (Logic_ProofSteps.strip_all_disj t) |> Logic_ProofSteps.replace_disj_vars ctxt
            val res = Logic_ProofSteps.disj_prop_match ctxt ([], fo_init) (t, (var_t, ts), (cvar_u, cus))
            val u' = Logic_ProofSteps.mk_all_disj (var_u, us)
          in
            case res of
                [(([], instsp), eq)] =>
                if Util.lhs_of eq aconv (Util.subst_term_norm instsp t) andalso
                   Util.rhs_of eq aconv u' then () else
                let
                  val _ = trace_t ctxt "t" t
                  val _ = trace_t ctxt "u" u
                  val _ = trace_thm ctxt "Output" eq
                in
                  raise Fail "disj_prop_match: wrong equation"
                end
              | _ =>
                let
                  val _ = trace_t ctxt "t" t
                  val _ = trace_t ctxt "u" u
                  val _ = tracing ("Number of results: " ^
                                   (string_of_int (length res)))
                in
                  raise Fail "disj_prop_match: wrong number of equations"
                end
          end

      val test_data = [
        ("A::bool", "A::bool"),
        ("A | B | C", "A | B | C"),
        ("(A | B) | C", "A | B | C"),
        ("A --> B --> C", "~A | ~B | C"),
        ("B --> A --> C", "C | ~B | ~A"),
        ("A & (B --> C) --> D", "A & (B --> C) --> D"),
        ("p & (q --> r) --> s", "~ (p & (q --> r)) | s"),
        ("!x. P x | Q x", "!x. P x | Q x"),
        ("!x::nat. Q x | P x", "!x::nat. P x | Q x"),
        ("!x::nat. P x --> Q x", "!x::nat. Q x | ~P x"),
        ("!x y. P x y | Q x y", "!x y. Q x y | P x y"),
        ("!a. P a | Q a", "!x. P x | Q x"),
        ("~(EX x. P x)", "~(EX x. P x)"),
        ("~(EX x. P x)", "!x. ~P x"),
        ("!x. ~P x", "~(EX x. P x)"),
        ("~(EX x:S. P x)", "~(EX x:S. P x)"),
        ("~(EX x:S. P x)", "!x:S. ~P x"),
        ("~(EX x:S. EX y:S. P x y)", "!x:S. !y:S. ~P x y"),

        ("!x. P x ?a", "!x. P x a"),
        ("!x:?S. P x", "!x:S. P x"),
        ("~(EX x. P x ?a)", "!x. ~P x a"),
        ("~(EX x:?S. P x)", "!x:S. ~P x"),
        ("!x. ?P x", "!x. P x"),
        ("!x y. ?P x | ?Q y", "!x y. P x | Q y"),
        ("~(EX x. EX y. ?P x & ?Q y)", "~(EX x. EX y. P x & Q y)"),
        ("!x y. ?P x | ?Q y", "!x y. P y | Q x"),
        ("!x. P y --> Q y", "P y --> Q y")
      ]
    in
      map test test_data
    end

val test_disj_prop_no_match =
    let
      fun test (str1, str2) =
          let
            val (t, u) = (Proof_Context.read_term_pattern ctxt str1,
                          Syntax.read_term ctxt str2)
            val (var_u, us) = Logic_ProofSteps.strip_all_disj u
            val var_u' = map free_to_var var_u
            val us' = map (subst_atomic (var_u ~~ var_u')) us
            val (cvar_u, cus) = (map Term.dest_Var var_u', map (Thm.cterm_of ctxt) us')
            val (var_t, ts) = (Logic_ProofSteps.strip_all_disj t) |> Logic_ProofSteps.replace_disj_vars ctxt
            val res = Logic_ProofSteps.disj_prop_match ctxt ([], fo_init) (t, (var_t, ts), (cvar_u, cus))
          in
            if null res then ()
            else let
              val _ = trace_t ctxt "t" t
              val _ = trace_t ctxt "u" u
            in
              raise Fail "disj_prop_no_match: expected no match"
            end
          end

      val test_data = [
        ("!x y. ?P x | ?Q y", "!x y. P x y | Q x y"),
        ("!x::'a. P (a::'a) | Q x", "!a::'a. P (a::'a) | Q a")
      ]
    in
      map test test_data
    end

val test_match_update =
    let
      val x = Free ("x", natT)
      val y = Free ("y", natT)
      val A = Free ("A", boolT)
      val B = Free ("B", natT --> boolT)
      val D = Free ("D", boolT)
      val ctxt' = ctxt |> fold Variable.declare_term [x, y, A, B, D]
      val ctxt'' = ctxt' |> RewriteTable.add_rewrite ([], assume_eq thy (x, y)) |> snd

      fun disj_to_ritem th =
          let
            val subs = strip_disj (prop_of' th)
          in
            Fact (TY_DISJ, bFalse :: disj :: subs, th)
          end

      fun read_prop str =
          str |> Proof_Context.read_term_pattern ctxt' |> mk_Trueprop

      fun updt_to_thm updt =
          case updt of
              AddItems {raw_items, ...} => map BoxItem.get_thm_raw raw_items
            | ResolveBox {th, ...} => [th]
            | _ => []

      fun test_updt ctxt (disj_str, t_str, res_strs) =
          let
            val disj_th = Util.assume_thm ctxt' (read_prop disj_str)
            val th = Util.assume_thm ctxt' (read_prop t_str)
            val res_ts = map read_prop res_strs
            val mk_box_item = BoxItem.mk_box_item ctxt'
            val items = [mk_box_item (0, [], 0, disj_to_ritem disj_th),
                         mk_box_item (0, [0], 0, Update.thm_to_ritem th)]
            val updts = ProofStep.apply_prfstep ctxt items Logic_ProofSteps.match_update_prfstep
            val res_ts' = maps updt_to_thm updts |> map Thm.prop_of
          in
            if eq_set (op aconv) (res_ts, res_ts') then ()
            else let
              val _ = trace_t ctxt' "Input disj:" (prop_of' disj_th)
              val _ = trace_t ctxt' "Input t:" (prop_of' th)
              val _ = trace_tlist ctxt' "Expected:" res_ts
              val _ = trace_tlist ctxt' "Actual:" res_ts'
            in
              raise Fail "test_match_update"
            end
          end

      val data1 = [("B x | B y | ~A", "A", ["B x | B y"]),
                   ("B x | B y | ~A", "~B x", ["B y | ~A"]),
                   ("B x | B y | ~A", "~B y", [])]
      val _ = map (test_updt ctxt') data1

      val data2 = [("B x | B y | ~A", "~B x", ["B y | ~A"]),
                   ("B x | B y | ~A", "D", []),
                   ("B x | B y", "~B x", ["False"])]
      val _ = map (test_updt ctxt'') data2
    in
      ()
    end

end
