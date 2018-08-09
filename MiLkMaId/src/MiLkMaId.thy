theory MiLkMaId
  imports MiLkMaId_Util MiLkMaId_Example
begin

ML_file "MiLkMaId_Assertion.ML"

term "filter (\<lambda> _. True) xs = xs"

end