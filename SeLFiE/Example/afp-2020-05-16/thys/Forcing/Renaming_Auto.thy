theory Renaming_Auto
  imports
    Renaming
    ZF.Finite
    ZF.List
keywords
  "rename" :: thy_decl % "ML"
and
  "simple_rename" :: thy_decl % "ML"
and
  "src"
and
  "tgt"
abbrevs
  "simple_rename" = ""

begin

lemmas app_fun = apply_iff[THEN iffD1]
lemmas nat_succI = nat_succ_iff[THEN iffD2]
ML_file\<open>Utils.ml\<close>
ML_file\<open>Renaming_ML.ml\<close>
ML\<open>
  open Renaming_ML

  fun renaming_def mk_ren name from to ctxt =
    let val to = to |> Syntax.read_term ctxt
        val from = from |> Syntax.read_term ctxt
        val (tc_lemma,action_lemma,fvs,r) = mk_ren from to ctxt
        val (tc_lemma,action_lemma) = (fix_vars tc_lemma fvs ctxt , fix_vars action_lemma fvs ctxt)
        val ren_fun_name = Binding.name (name ^ "_fn")
        val ren_fun_def =  Binding.name (name ^ "_fn_def")
        val ren_thm = Binding.name (name ^ "_thm")
    in
      Local_Theory.note   ((ren_thm, []), [tc_lemma,action_lemma]) ctxt |> snd |>
      Local_Theory.define ((ren_fun_name, NoSyn), ((ren_fun_def, []), r)) |> snd      
  end;
\<close>

ML\<open>
local

  val ren_parser = Parse.position (Parse.string --
      (Parse.$$$ "src" |-- Parse.string --| Parse.$$$ "tgt" -- Parse.string));

  val _ =
   Outer_Syntax.local_theory \<^command_keyword>\<open>rename\<close> "ML setup for synthetic definitions"
     (ren_parser >> (fn ((name,(from,to)),_) => renaming_def sum_rename name from to ))

  val _ =
   Outer_Syntax.local_theory \<^command_keyword>\<open>simple_rename\<close> "ML setup for synthetic definitions"
     (ren_parser >> (fn ((name,(from,to)),_) => renaming_def ren_thm name from to ))

in
end
\<close>
end