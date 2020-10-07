theory Benchmark_ICF 
imports 
  Benchmark_Comparison
  Collections.CollectionsV1
  "HOL-Library.Code_Target_Nat"
begin

locale benchmark_base = 
  fixes empty :: "unit \<Rightarrow> 's"
  and memb :: "natural \<Rightarrow> 's \<Rightarrow> bool"
  and ins :: "natural \<Rightarrow> 's \<Rightarrow> 's"
  and rem :: "natural \<Rightarrow> 's => 's"
  and size :: "'s \<Rightarrow> nat"
  and filter :: "(natural \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's"
begin

fun gen_build :: "natural \<Rightarrow> nat \<Rightarrow> ('s \<times> Random.seed) \<Rightarrow> ('s \<times> Random.seed)"
where 
  "gen_build bound n (A, seed) =
  (if n = 0 then (A, seed) 
   else let (x, seed') = Random.range bound seed in gen_build bound (n - 1) (ins x A, seed'))"

declare gen_build.simps [simp del]

fun gen_remove :: "natural \<Rightarrow> nat \<Rightarrow> ('s \<times> Random.seed) \<Rightarrow> ('s \<times> Random.seed)"
where
  "gen_remove bound n (A, seed) =
  (if n = 0 then (A, seed) 
   else let (x, seed') = Random.range bound seed in gen_remove bound (n - 1) (rem x A, seed'))"

declare gen_remove.simps [simp del]

definition build :: "nat \<Rightarrow> Random.seed \<Rightarrow> ('s \<times> Random.seed)"
where "build n seed = (let bound = of_nat n * 2 in gen_remove bound n (gen_build bound n (empty (), seed)))"

fun gen_lookup :: "natural \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> (natural \<times> Random.seed) \<Rightarrow> (natural \<times> Random.seed)"
where
  "gen_lookup bound A n (hits, seed) =
  (if n = 0 then (hits, seed)
   else let (x, seed') = Random.range bound seed in gen_lookup bound A (n - 1) (if memb x A then hits + 1 else hits, seed'))"

declare gen_lookup.simps [simp del]

primrec lookup :: "nat \<Rightarrow> ('s \<times> Random.seed) \<Rightarrow> (natural \<times> Random.seed)"
where "lookup n (A, seed) = gen_lookup (of_nat n * 2) A n (0, seed)"

definition test :: "'s \<Rightarrow> (natural \<Rightarrow> bool) \<Rightarrow> nat"
where "test A P = size (filter P A)"

definition complete :: "nat \<Rightarrow> Random.seed \<Rightarrow> (natural \<times> nat)"
where 
  "complete n seed =
  (let (A, seed') = build n seed;
       (hits, seed'') = lookup n (A, seed');
       less = test A (\<lambda>x. x \<le> of_nat n)
   in (hits, less))"

end

lemmas [code] =
  benchmark_base.gen_build.simps
  benchmark_base.gen_remove.simps
  benchmark_base.build_def
  benchmark_base.gen_lookup.simps
  benchmark_base.lookup.simps
  benchmark_base.test_def
  benchmark_base.complete_def

locale benchmark = 
  benchmark_base empty memb ins rem size filter +
  set \<alpha> invar +
  set_empty \<alpha> invar empty +
  set_memb \<alpha> invar memb +
  set_ins \<alpha> invar ins +
  set_delete \<alpha> invar rem +
  set_size \<alpha> invar size +
  set_filter \<alpha> invar \<alpha> invar filter
  for \<alpha> :: "'s \<Rightarrow> natural set"
  and invar :: "'s \<Rightarrow> bool"
  and empty :: "unit \<Rightarrow> 's"
  and memb :: "natural \<Rightarrow> 's \<Rightarrow> bool"
  and ins :: "natural \<Rightarrow> 's \<Rightarrow> 's"
  and rem :: "natural \<Rightarrow> 's \<Rightarrow> 's"
  and size :: "'s \<Rightarrow> nat"
  and filter :: "(natural \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's"
begin

lemma gen_build_invar: "invar (fst As) \<Longrightarrow> invar (fst (gen_build bound n As))"
apply(induct bound n As rule: gen_build.induct)
apply(subst gen_build.simps)
apply(simp add: split_beta ins_correct)
done

lemma \<alpha>_gen_build: "invar (fst As) \<Longrightarrow> apfst \<alpha> (gen_build bound n As) = Benchmark_Comparison.gen_build bound n (apfst \<alpha> As)"
apply(induct bound n As rule: gen_build.induct)
apply simp
apply(subst gen_build.simps)
apply(subst Benchmark_Comparison.gen_build.simps)
apply(simp add: split_beta ins_correct)
done

lemma gen_remove_invar: "invar (fst As) \<Longrightarrow> invar (fst (gen_remove bound n As))"
apply(induct bound n As rule: gen_remove.induct)
apply(subst gen_remove.simps)
apply(simp add: split_beta delete_correct)
done

lemma \<alpha>_gen_remove: "invar (fst As) \<Longrightarrow> apfst \<alpha> (gen_remove bound n As) = Benchmark_Comparison.gen_remove bound n (apfst \<alpha> As)"
apply(induct bound n As rule: gen_remove.induct)
apply simp
apply(subst gen_remove.simps)
apply(subst Benchmark_Comparison.gen_remove.simps)
apply(simp add: split_beta delete_correct Set.remove_def)
done

lemma build_invar: "invar (fst (build n seed))"
by(simp add: build_def gen_build_invar gen_remove_invar Let_def empty_correct)

lemma \<alpha>_build: "apfst \<alpha> (build n seed) = Benchmark_Comparison.build n seed"
by(simp add: build_def Benchmark_Comparison.build_def empty_correct \<alpha>_gen_build \<alpha>_gen_remove gen_build_invar Let_def)

lemma \<alpha>_gen_lookup: "invar A \<Longrightarrow> gen_lookup bound A n hs = Benchmark_Comparison.gen_lookup bound (\<alpha> A) n hs"
apply(induct A n hs rule: gen_lookup.induct)
apply(subst gen_lookup.simps)
apply(subst Benchmark_Comparison.gen_lookup.simps)
apply(simp add: split_beta memb_correct)
done

lemma \<alpha>_lookup: "invar A \<Longrightarrow> lookup n (A, seed) = Benchmark_Comparison.lookup n (\<alpha> A, seed)"
by(simp add: \<alpha>_gen_lookup)

lemma \<alpha>_test: "invar A \<Longrightarrow> test A P = Benchmark_Comparison.test (\<alpha> A) P"
apply(simp only: test_def Benchmark_Comparison.test_def size_correct filter_correct)
apply(rule arg_cong[where f=card])
apply auto
done

lemma apfst_fst: "apfst f x = (f (fst x), snd x)"
by(cases x) simp

lemma case_prod_apfst: "(case (apfst f z) of (x, y) \<Rightarrow> g x y) = (case z of (x, y) \<Rightarrow> g (f x) y)"
by(cases z) simp

lemma \<alpha>_complete: "complete n seed = Benchmark_Comparison.complete n seed"
apply(simp add: complete_def Benchmark_Comparison.complete_def \<alpha>_test \<alpha>_gen_lookup build_invar \<alpha>_build[symmetric] \<alpha>_gen_lookup[symmetric])
apply(simp add: split_beta \<alpha>_gen_lookup[symmetric] build_invar \<alpha>_test)
done

end

setup Locale_Code.open_block
interpretation gen_rr: g_set_xy_loc rs_ops rs_ops by unfold_locales
setup Locale_Code.close_block


definition rs_filter where "rs_filter = iflt_filter gen_rr.g_inj_image_filter"
lemmas rs_filter_impl = iflt_filter_correct[OF gen_rr.g_inj_image_filter_impl, folded rs_filter_def]
interpretation rs: set_filter rs_\<alpha> rs_invar rs_\<alpha> rs_invar rs_filter using rs_filter_impl .

interpretation rs: benchmark rs_\<alpha> rs_invar rs_empty rs_memb rs_ins rs_delete rs_size rs_filter
by(unfold_locales)

definition complete where "complete = rs.complete"

notepad begin
  have "complete 200 (12345, 67889) = (48, 50)" by eval
end

end
