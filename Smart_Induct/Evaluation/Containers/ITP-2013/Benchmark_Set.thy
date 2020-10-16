theory Benchmark_Set
imports
  "HOL-Word.Word"
  "HOL-Library.Cardinality"
begin

instantiation word :: (len) card_UNIV begin
definition "finite_UNIV = Phantom('a word) True"
definition "card_UNIV = Phantom('a word) (2 ^ LENGTH('a))"
instance by(intro_classes)(simp_all add: card_UNIV_word_def card_word finite_UNIV_word_def)
end

definition word_of_integer :: "integer \<Rightarrow> 'a::len0 word"
where "word_of_integer = word_of_int \<circ> int_of_integer"

lemma word_of_integer_code [code]:
  "word_of_integer k = 
  (if k < 0 then - word_of_integer (- k)
   else if k = 0 then 0
   else let (q, r) = divmod_integer k 2
        in if r = 0 then 2 * word_of_integer q else 2 * word_of_integer q + 1)"
apply(unfold word_of_integer_def o_def)
apply(subst int_of_integer_code)
apply(clarsimp simp add: divmod_integer_def)
by (metis minus_minus plus_word.abs_eq times_word.abs_eq wi_hom_neg word_1_wi word_numeral_alt)

definition word_of :: "natural \<Rightarrow> 'a::len0 word"
where "word_of = word_of_integer o integer_of_natural"

text \<open>randomly generate a set of (up to) n elements drawn from 0 to bound\<close>

fun gen_build1 :: "natural \<Rightarrow> nat \<Rightarrow> (32 word set \<times> Random.seed) \<Rightarrow> (32 word set \<times> Random.seed)"
where 
  "gen_build1 bound n (A, seed) =
  (if n = 0 then (A, seed) 
   else let (x, seed') = Random.range bound seed in gen_build1 bound (n - 1) (insert (word_of x) A, seed'))"

declare gen_build1.simps[simp del]

definition build1 :: "natural \<Rightarrow> Random.seed \<Rightarrow> (32 word set \<times> Random.seed)"
where 
  "build1 bound seed =
  (let (n', seed') = Random.range bound seed;
       (compl, seed'') = Random.range 2 seed;
       (x, seed''') = gen_build1 bound (Code_Numeral.nat_of_natural n') ({}, seed'')
   in (if compl = 0 then x else - x, seed'''))"

text \<open>randomly generate a set of (up to) n sets each with a random number between 0 and bound of elements between 0 and bound\<close>

fun gen_build2 :: "natural \<Rightarrow> nat \<Rightarrow> (32 word set set \<times> Random.seed) \<Rightarrow> (32 word set set \<times> Random.seed)"
where
  "gen_build2 bound n (A, seed) =
  (if n = 0 then (A, seed)
   else let (x, seed') = build1 bound seed
        in gen_build2 bound (n - 1) (insert x A, seed'))"

declare gen_build2.simps[simp del]

definition build :: "nat \<Rightarrow> nat \<Rightarrow> Random.seed \<Rightarrow> 32 word set set \<times> Random.seed"
where "build n m seed = gen_build2 (of_nat m) n ({}, seed)"

fun gen_lookup :: "32 word set set \<Rightarrow> natural \<Rightarrow> nat \<Rightarrow> (nat \<times> Random.seed) \<Rightarrow> (nat \<times> Random.seed)"
where
  "gen_lookup A bound n (hits, seed) =
  (if n = 0 then (hits, seed)
   else let (x, seed') = build1 bound seed
        in gen_lookup A bound (n - 1) (if x : A then hits + 1 else hits, seed'))"

declare gen_lookup.simps [simp del]

primrec lookup :: "nat \<Rightarrow> nat \<Rightarrow> (32 word set set \<times> Random.seed) \<Rightarrow> (nat \<times> Random.seed)"
where "lookup n m (A, seed) = gen_lookup A (of_nat m) 100 (0, seed)"

definition covered :: "32 word set set \<Rightarrow> nat"
where "covered A = card (\<Union>A)"

definition complete :: "nat \<Rightarrow> nat \<Rightarrow> Random.seed \<Rightarrow> (nat \<times> nat)"
where "complete n m seed = (let (A, seed') = build n m seed in (fst (lookup n m (A, seed)), covered A))"

end
