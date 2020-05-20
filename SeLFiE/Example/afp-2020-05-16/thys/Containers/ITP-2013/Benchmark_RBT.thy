theory Benchmark_RBT 
imports 
  Benchmark_Comparison
  "HOL-Library.RBT_Impl"
  "HOL-Library.Code_Target_Nat"
begin

fun gen_build :: "natural \<Rightarrow> nat \<Rightarrow> ((natural, unit) rbt \<times> Random.seed) \<Rightarrow> ((natural, unit) rbt \<times> Random.seed)"
where 
  "gen_build bound n (A, seed) =
  (if n = 0 then (A, seed) 
   else let (x, seed') = Random.range bound seed in gen_build bound (n - 1) (rbt_insert x () A, seed'))"

declare gen_build.simps [simp del]

fun gen_remove :: "natural \<Rightarrow> nat \<Rightarrow> ((natural, unit) rbt \<times> Random.seed) \<Rightarrow> ((natural, unit) rbt \<times> Random.seed)"
where
  "gen_remove bound n (A, seed) =
  (if n = 0 then (A, seed)
   else let (x, seed') = Random.range bound seed in gen_remove bound (n - 1) (rbt_delete x A, seed'))"

declare gen_remove.simps [simp del]

definition build :: "nat \<Rightarrow> Random.seed \<Rightarrow> ((natural, unit) rbt \<times> Random.seed)"
where "build n seed = (let bound = of_nat n * 2 in gen_remove bound n (gen_build bound n (rbt.Empty, seed)))"

fun gen_lookup :: "natural \<Rightarrow> (natural, unit) rbt \<Rightarrow> nat \<Rightarrow> (natural \<times> Random.seed) \<Rightarrow> (natural \<times> Random.seed)"
where
  "gen_lookup bound A n (hits, seed) =
  (if n = 0 then (hits, seed)
   else let (x, seed') = Random.range bound seed in gen_lookup bound A (n - 1) (if rbt_lookup A x = Some () then hits + 1 else hits, seed'))"

declare gen_lookup.simps [simp del]

primrec lookup :: "nat \<Rightarrow> ((natural, unit) rbt \<times> Random.seed) \<Rightarrow> (natural \<times> Random.seed)"
where "lookup n (A, seed) = gen_lookup (of_nat n * 2) A n (0, seed)"

definition test :: "(natural, unit) rbt \<Rightarrow> (natural \<Rightarrow> bool) \<Rightarrow> nat"
where "test A P = RBT_Impl.fold (\<lambda>x _ i. if P x then i + 1 else i) A 0"

definition complete :: "nat \<Rightarrow> Random.seed \<Rightarrow> (natural \<times> nat)"
where 
  "complete n seed =
  (let (A, seed') = build n seed;
       (hits, seed'') = lookup n (A, seed');
       less = test A (\<lambda>x. x \<le> of_nat n)
   in (hits, less))"

notepad begin
  have "complete 200 (12345, 67889) = (48, 50)" by eval
end

end
