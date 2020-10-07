(* Author: Manuel Eberl *)
theory Instantiate_Existentials
  imports Main
begin

ML \<open>
fun inst_existentials_tac ctxt [] = TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms conjI})
  | inst_existentials_tac ctxt (t :: ts) =
      (TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms conjI}))
      THEN_ALL_NEW (TRY o (
        let
          val inst = Drule.infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt t)]
          val thms = map inst @{thms exI bexI}
        in
          resolve_tac ctxt thms THEN' inst_existentials_tac ctxt ts
        end))
\<close>

method_setup inst_existentials =
  \<open>
  Scan.lift (Scan.repeat Parse.term) >>
      (fn ts => fn ctxt => SIMPLE_METHOD' (inst_existentials_tac ctxt
         (map (Syntax.read_term ctxt) ts)))
  \<close>

text \<open>Test\<close>
lemma
  "\<exists> x. \<exists> y \<in> UNIV. (\<exists> z \<in> UNIV. x + y = (z::nat)) \<and> (\<exists> z. x + y = (z::nat))"
  by (inst_existentials "1 :: nat" "2 :: nat" "3 :: nat"; simp)

end
