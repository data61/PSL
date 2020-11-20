theory Benchmark_LC imports
  Benchmark_Comparison
  Containers.Set_Impl
  "HOL-Library.Code_Target_Nat"
begin

notepad begin
  have "Benchmark_Comparison.complete 200 (12345, 67889) = (48, 50)"
    by eval
end

end
