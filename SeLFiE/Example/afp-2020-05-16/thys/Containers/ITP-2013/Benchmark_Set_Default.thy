theory Benchmark_Set_Default 
imports
  Benchmark_Set
  "HOL-Library.Code_Target_Nat"
begin

text \<open>Implement set equality for all combinations of @{term "List.set"} and @{term "List.coset"}\<close>
lemma [code]: "equal_class.equal A B \<longleftrightarrow> Cardinality.eq_set A B" 
 by(simp add: equal_eq)

ML_val \<open>
  val seed = (Code_Numeral.natural_of_integer 12345, Code_Numeral.natural_of_integer 67889);
  val n = @{code nat_of_integer} 30;
  val m = @{code nat_of_integer} 40;
  val c = @{code Benchmark_Set.complete} n m seed;
\<close>

notepad begin
  have "Benchmark_Set.complete 30 40 (12345, 67889) = (30, 4294967296)" by eval
end

end
