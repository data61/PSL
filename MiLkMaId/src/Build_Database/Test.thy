theory Test
imports Main Build_Database
begin

lemma "True"
  apply2 induct
  apply2 induct_tac
  apply2 induction
  apply2 induct
  apply2 auto
  done

end