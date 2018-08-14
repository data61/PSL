theory MiLkMaId
  imports MiLkMaId_Util MiLkMaId_Example
begin

ML_file "MiLkMaId_Assertion.ML"

ML{* (* TODO: to differentiate "inductive" and "inductive_set", we should check the types.  *)
dest_Const @{term "even_set"} |> snd |> dest_Type |> fst;
*}

ML{*
(* test check_suffix *)
(* "evn" defined with the "inductive" keyword *)
val _ = @{assert} (check_suffix @{context} "evn" suffix_for_inductive);
val _ = @{assert} (check_suffix @{context} "evn" suffix_for_fun = false);
val _ = @{assert} (check_suffix @{context} "evn" suffix_for_function = false);
val _ = @{assert} (check_suffix @{context} "evn" suffix_for_primrec = false);
 
(* "fib" defined with the "fun" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.fib" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.fib" suffix_for_fun);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.fib" suffix_for_function = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.fib" suffix_for_primrec = false);

(* "even" defined with the "function" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.even" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.even" suffix_for_fun = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.even" suffix_for_function);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.even" suffix_for_primrec = false);

(* "odd" defined with the "function" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.odd" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.odd" suffix_for_fun = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.odd" suffix_for_function);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.odd" suffix_for_primrec = false);

(* "filter" defined with the "fun" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.filter" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.filter" suffix_for_fun);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.filter" suffix_for_function = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.filter" suffix_for_primrec = false);

(* "nubBy" defined with the "fun" keyword *)
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.nubBy" suffix_for_inductive = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.nubBy" suffix_for_fun = false);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.nubBy" suffix_for_function);
val _ = @{assert} (check_suffix @{context} "MiLkMaId_Example.nubBy" suffix_for_primrec = false);

(* test get_command *)
val _ = @{assert} (get_command "MiLkMaId_Example.MyTrue1"  @{context} = Unknown);
val _ = @{assert} (get_command "MiLkMaId.append2"          @{context} = Unknown (*Because it is not really defined in that file.*));
val _ = @{assert} (get_command "MiLkMaId_Example.append2"  @{context} = Primrec);
val _ = @{assert} (get_command "MiLkMaId_Example.evn"      @{context} = Inductive);
val _ = @{assert} (get_command "MiLkMaId_Example.fib"      @{context} = Fun);
val _ = @{assert} (get_command "MiLkMaId_Example.even"     @{context} = Function);
val _ = @{assert} (get_command "MiLkMaId_Example.odd"      @{context} = Function);
val _ = @{assert} (get_command "MiLkMaId_Example.filter"   @{context} = Fun);
val _ = @{assert} (get_command "MiLkMaId_Example.nubBy"    @{context} = Function);
val _ = @{assert} (get_command "MiLkMaId_Example.even_set" @{context} = Inductive);(*FIXME: It should be Inductive_Set.*)
*}

end