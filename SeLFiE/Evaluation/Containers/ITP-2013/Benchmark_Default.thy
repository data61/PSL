theory Benchmark_Default imports 
  Benchmark_Comparison 
  "HOL-Library.Code_Target_Nat"
begin

lemma [code]: "test (set xs) P = length (remdups (filter P xs))"
apply(simp add: test_def)
apply(fold card_set)
apply(rule arg_cong[where f=card])
apply auto
done

notepad begin
  have "Benchmark_Comparison.complete 200 (12345, 67889) = (48, 50)" by eval
end

end
