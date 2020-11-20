theory Benchmark_Comparison imports 
  Main
begin

fun gen_build :: "natural \<Rightarrow> nat \<Rightarrow> (natural set \<times> Random.seed) \<Rightarrow> (natural set \<times> Random.seed)"
where 
  "gen_build bound n (A, seed) =
  (if n = 0 then (A, seed) 
   else let (x, seed') = Random.range bound seed in gen_build bound (n - 1) (insert x A, seed'))"

declare gen_build.simps [simp del]

fun gen_remove :: "natural \<Rightarrow> nat \<Rightarrow> (natural set \<times> Random.seed) \<Rightarrow> (natural set \<times> Random.seed)"
where
  "gen_remove bound n (A, seed) =
  (if n = 0 then (A, seed)
   else let (x, seed') = Random.range bound seed in gen_remove bound (n - 1) (Set.remove x A, seed'))"

declare gen_remove.simps [simp del]

definition build :: "nat \<Rightarrow> Random.seed \<Rightarrow> (natural set \<times> Random.seed)"
where "build n seed = (let bound = of_nat n * 2 in gen_remove bound n (gen_build bound n ({}, seed)))"

fun gen_lookup :: "natural \<Rightarrow> natural set \<Rightarrow> nat \<Rightarrow> (natural \<times> Random.seed) \<Rightarrow> (natural \<times> Random.seed)"
where
  "gen_lookup bound A n (hits, seed) =
  (if n = 0 then (hits, seed)
   else let (x, seed') = Random.range bound seed in gen_lookup bound A (n - 1) (if x \<in> A then hits + 1 else hits, seed'))"

declare gen_lookup.simps [simp del]

primrec lookup :: "nat \<Rightarrow> (natural set \<times> Random.seed) \<Rightarrow> (natural \<times> Random.seed)"
where "lookup n (A, seed) = gen_lookup (of_nat n * 2) A n (0, seed)"

definition test :: "natural set \<Rightarrow> (natural \<Rightarrow> bool) \<Rightarrow> nat"
where "test A P = card (A \<inter> {x. P x})"

definition complete :: "nat \<Rightarrow> Random.seed \<Rightarrow> (natural \<times> nat)"
where 
  "complete n seed =
  (let (A, seed') = build n seed;
       (hits, seed'') = lookup n (A, seed');
       less = test A (\<lambda>x. x \<le> of_nat n)
   in (hits, less))"

text \<open>@{term complete'} is @{term complete} without iteration\<close>

definition complete' :: "nat \<Rightarrow> Random.seed \<Rightarrow> (natural \<times> nat)"
where "complete' n seed =
  (let (A, seed') = build n seed;
       (hits, seed'') = lookup n (A, seed')
   in (hits, 0))"

end
