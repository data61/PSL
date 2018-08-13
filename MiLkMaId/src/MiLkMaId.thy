theory MiLkMaId
  imports MiLkMaId_Util MiLkMaId_Example
begin

ML_file "MiLkMaId_Assertion.ML"


(** tests **)
ML{* open MiLkMaId_Assertion; *}

ML{* get_many @{context} "evn.intros" get_cncl; *}

ML{* @{term "(A B (identity G)) (D (\<lambda>E. F E))"} |> uncurry; *}

ML{*
uncurry @{term "even 1"};
uncurry @{term "\<lambda> B. C B (\<lambda>E. F E B)"};
uncurry @{term "\<forall>x. P x y x"};
uncurry @{term "\<And>x. P x y x"};
*}

end