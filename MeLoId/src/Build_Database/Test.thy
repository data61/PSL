theory Test
imports Main Build_Database
begin

lemma "True"
  apply induct
  apply induct_tac
  apply induction
  apply induct
  apply auto
  done

end