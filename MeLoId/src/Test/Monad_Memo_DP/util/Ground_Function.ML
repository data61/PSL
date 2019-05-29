(** Define a new ground constant from an existing function definition **)
structure Ground_Function = struct

fun add_function bind defs =
  let
    val fixes = [(bind, NONE, NoSyn)];
    val specs = map (fn def => (((Binding.empty, []), def), [], [])) defs
    val pat_completeness_auto = fn ctxt =>
      Pat_Completeness.pat_completeness_tac ctxt 1
      THEN auto_tac ctxt
  in
    Function.add_function fixes specs Function_Fun.fun_config pat_completeness_auto
end

fun dest_hol_eq_prop t =
  let
    val Const ("HOL.Trueprop", _) $ (Const ("HOL.eq", _) $ a $ b) = t
  in (a, b) end
fun get_fun_head t =
  let
    val (t, _) = dest_hol_eq_prop t
    val t = Term.head_of t
    val Const (fun_name, fun_ty) = t
 in (fun_name, fun_ty) end

fun mk_fun termination simps binding ctxt =
  let
    val eqns = map Thm.concl_of simps
    val (eqns, _) = Variable.import_terms true eqns ctxt
    val (f_name, f_ty) = get_fun_head (hd eqns)
    val s = Binding.name_of binding
    val replacement = (Const (f_name, f_ty), Free (s, f_ty))
    val eqns = map (subst_free [replacement]) eqns
    val (_, ctxt) = add_function binding eqns ctxt
    fun prove_termination lthy =
        Function.prove_termination NONE (Function_Common.termination_prover_tac false lthy) lthy
  in ctxt |> (if termination then snd o prove_termination else I) end

end