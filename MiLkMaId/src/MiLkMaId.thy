theory MiLkMaId
  imports MiLkMaId_Util MiLkMaId_Example
begin

ML_file "MiLkMaId_Assertion.ML"

ML{* (* TODO: to differentiate "inductive" and "inductive_set", we should check the types.  *)
dest_Const @{term "even_set"} |> snd |> dest_Type |> fst;
*}

ML_file "Smart_Induct.ML"

end