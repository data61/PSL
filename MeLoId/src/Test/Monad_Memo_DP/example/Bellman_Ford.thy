subsection \<open>The Bellman-Ford Algorithm\<close>

theory Bellman_Ford
  imports
    "HOL-Library.Extended"
    "HOL-Library.IArray"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Product_Lexorder"
    "../state_monad/State_Main"
    "../heap_monad/Heap_Main"
    Example_Misc
    "../util/Tracing"
    "../util/Ground_Function"
begin

subsubsection \<open>Misc\<close>

instance extended :: (countable) countable
proof standard
  obtain to_nat :: "'a \<Rightarrow> nat" where "inj to_nat"
    by auto
  let ?f = "\<lambda> x. case x of Fin n \<Rightarrow> to_nat n + 2 | Pinf \<Rightarrow> 0 | Minf \<Rightarrow> 1"
  from \<open>inj _ \<close> have "inj ?f"
    by (auto simp: inj_def split: extended.split)
  then show "\<exists>to_nat :: 'a extended \<Rightarrow> nat. inj to_nat"
    by auto
qed

instance extended :: (heap) heap ..

lemma fold_acc_preserv:
  assumes "\<And> x acc. P acc \<Longrightarrow> P (f x acc)" "P acc"
  shows "P (fold f xs acc)"
  using assms(2) by (induction xs arbitrary: acc) (auto intro: assms(1))

lemma get_return:
  "run_state (State_Monad.bind State_Monad.get (\<lambda> m. State_Monad.return (f m))) m = (f m, m)"
  by (simp add: State_Monad.bind_def State_Monad.get_def)


subsubsection \<open>Single-Sink Shortest Path Problem\<close>

datatype bf_result = Path "nat list" int | No_Path | Computation_Error

context
  fixes n :: nat and W :: "nat \<Rightarrow> nat \<Rightarrow> int extended"
begin

context
  fixes t :: nat -- "Final node"
begin

text \<open>
  The correctness proof closely follows Kleinberg \<open>&\<close> Tardos: "Algorithm Design",
  chapter "Dynamic Programming" @{cite "Kleinberg-Tardos"}
\<close>

definition weight :: "nat list \<Rightarrow> int extended" where
  "weight xs = snd (fold (\<lambda> i (j, x). (i, W i j + x)) (rev xs) (t, 0))"

definition
  "OPT i v = (
    Min (
      {weight (v # xs) | xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}} \<union>
      {if t = v then 0 else \<infinity>}
    )
  )"

lemma weight_Cons [simp]:
  "weight (v # w # xs) = W v w + weight (w # xs)"
  by (simp add: case_prod_beta' weight_def)

lemma weight_single [simp]:
  "weight [v] = W v t"
  by (simp add: weight_def)

(* XXX Generalize to the right type class *)
lemma Min_add_right:
  "Min S + (x :: int extended) = Min ((\<lambda> y. y + x) ` S)" (is "?A = ?B") if "finite S" "S \<noteq> {}"
proof -
  have "?A \<le> ?B"
    using that by (force intro: Min.boundedI add_right_mono)
  moreover have "?B \<le> ?A"
    using that by (force intro: Min.boundedI)
  ultimately show ?thesis
    by simp
qed

lemma OPT_0:
  "OPT 0 v = (if t = v then 0 else \<infinity>)"
  unfolding OPT_def by simp

(* TODO: Move to distribution! *)
lemma Pinf_add_right[simp]:
  "\<infinity> + x = \<infinity>"
  by (cases x; simp)

subsubsection \<open>Functional Correctness\<close>

lemma OPT_Suc:
  "OPT (Suc i) v = min (OPT i v) (Min {OPT i w + W v w | w. w \<le> n})" (is "?lhs = ?rhs")
  if "t \<le> n"
proof -
  have fin': "finite {xs. length xs \<le> i \<and> set xs \<subseteq> {0..n}}" for i
    by (auto intro: finite_subset[OF _ finite_lists_length_le[OF finite_atLeastAtMost]])
  have fin: "finite {weight (v # xs) |xs. length xs \<le> i \<and> set xs \<subseteq> {0..n}}"
    for v i using [[simproc add: finite_Collect]] by (auto intro: finite_subset[OF _ fin'])
  have OPT_in: "OPT i v \<in>
    {weight (v # xs) | xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}} \<union>
    {if t = v then 0 else \<infinity>}"
    if "i > 0" for i v
    using that unfolding OPT_def
    by - (rule Min_in, auto 4 3 intro: finite_subset[OF _ fin, of _ v "Suc i"])

  have "OPT i v \<ge> OPT (Suc i) v"
    unfolding OPT_def using fin by (auto 4 3 intro: Min_antimono)
  have subs:
    "(\<lambda>y. y + W v w) ` {weight (w # xs) |xs. length xs + 1 \<le> i \<and> set xs \<subseteq> {0..n}}
    \<subseteq> {weight (v # xs) |xs. length xs + 1 \<le> Suc i \<and> set xs \<subseteq> {0..n}}" if \<open>w \<le> n\<close> for v w
    using \<open>w \<le> n\<close> apply clarify
    subgoal for _ _ xs
      by (rule exI[where x = "w # xs"]) (auto simp: algebra_simps)
    done
  have "OPT i t + W v t \<ge> OPT (Suc i) v"
    unfolding OPT_def using subs[OF \<open>t \<le> n\<close>, of v] that
    by (subst Min_add_right)
       (auto 4 3
         simp: Bellman_Ford.weight_single
         intro: exI[where x = "[]"] finite_subset[OF _ fin[of _ "Suc i"]] intro!: Min_antimono
       )
  moreover have "OPT i w + W v w \<ge> OPT (Suc i) v" if "w \<le> n" \<open>w \<noteq> t\<close> \<open>t \<noteq> v\<close> for w
    unfolding OPT_def using subs[OF \<open>w \<le> n\<close>, of v] that
    by (subst Min_add_right)
       (auto 4 3 intro: finite_subset[OF _ fin[of _ "Suc i"]] intro!: Min_antimono)
  moreover have "OPT i w + W t w \<ge> OPT (Suc i) t" if "w \<le> n" \<open>w \<noteq> t\<close> for w
    unfolding OPT_def
    apply (subst Min_add_right)
      prefer 3
    using \<open>w \<noteq> t\<close>
      apply simp
      apply (cases "i = 0")
       apply (simp; fail)
    using subs[OF \<open>w \<le> n\<close>, of t]
    by (subst (2) Min_insert)
       (auto 4 4
         intro: finite_subset[OF _ fin[of _ "Suc i"]] exI[where x = "[]"] intro!: Min_antimono
       )
  ultimately have "Min {local.OPT i w + W v w |w. w \<le> n} \<ge> OPT (Suc i) v"
    by (auto intro!: Min.boundedI)
  with \<open>OPT i v \<ge> _\<close> have "?lhs \<le> ?rhs"
    by simp

  from OPT_in[of "Suc i" v] consider
    "OPT (Suc i) v = \<infinity>" | "t = v" "OPT (Suc i) v = 0" |
    xs where "OPT (Suc i) v = weight (v # xs)" "length xs \<le> i" "set xs \<subseteq> {0..n}"
    by (auto split: if_split_asm)
  then have "?lhs \<ge> ?rhs"
  proof cases
    case 1
    then show ?thesis
      by simp
  next
    case 2
    then have "OPT i v \<le> OPT (Suc i) v"
      unfolding OPT_def using [[simproc add: finite_Collect]]
      by (auto 4 4 intro: finite_subset[OF _ fin', of _ "Suc i"] intro!: Min_le)
    then show ?thesis
      by (rule min.coboundedI1)
  next
    case xs: 3
    note [simp] = xs(1)
    show ?thesis
    proof (cases "length xs = i")
      case True
      show ?thesis
      proof (cases "i = 0")
        case True
        with xs have "OPT (Suc i) v = W v t"
          by simp
        also have "W v t = OPT i t + W v t"
          unfolding OPT_def using \<open>i = 0\<close> by auto
        also have "\<dots> \<ge> Min {OPT i w + W v w |w. w \<le> n}"
          using \<open>t \<le> n\<close> by (auto intro: Min_le)
        finally show ?thesis
          by (rule min.coboundedI2)
      next
        case False
        with \<open>_ = i\<close> have "xs \<noteq> []"
          by auto
        with xs have "weight xs \<ge> OPT i (hd xs)"
          unfolding OPT_def
          by (intro Min_le[rotated] UnI1 CollectI exI[where x = "tl xs"])
             (auto 4 3 intro: finite_subset[OF _ fin, of _ "hd xs" "Suc i"] dest: list.set_sel(2))
        have "Min {OPT i w + W v w |w. w \<le> n} \<le> W v (hd xs) + OPT i (hd xs)"
          using \<open>set xs \<subseteq> _\<close> \<open>xs \<noteq> []\<close> by (force simp: add.commute intro: Min_le)
        also have "\<dots> \<le> W v (hd xs) + weight xs"
          using \<open>_ \<ge> OPT i (hd xs)\<close> by (metis add_left_mono)
        also from \<open>xs \<noteq> []\<close> have "\<dots> = OPT (Suc i) v"
          by (cases xs) auto
        finally show ?thesis
          by (rule min.coboundedI2)
      qed
    next
      case False
      with xs have "OPT i v \<le> OPT (Suc i) v"
        by (auto 4 4 intro: Min_le finite_subset[OF _ fin, of _ v "Suc i"] simp: OPT_def)
      then show ?thesis
        by (rule min.coboundedI1)
    qed
  qed
  with \<open>?lhs \<le> ?rhs\<close> show ?thesis
    by (rule order.antisym)
qed

fun bf :: "nat \<Rightarrow> nat \<Rightarrow> int extended" where
  "bf 0 j = (if t = j then 0 else \<infinity>)"
| "bf (Suc k) j = min_list
      (bf k j # [W j i + bf k i . i \<leftarrow> [0 ..< Suc n]])"

lemmas [simp del] = bf.simps
lemmas [simp] = bf.simps[unfolded min_list_fold]
thm bf.simps
thm bf.induct

lemma bf_correct:
  "OPT i j = bf i j" if \<open>t \<le> n\<close>
proof (induction i arbitrary: j)
  case 0
  then show ?case
    by (simp add: OPT_0)
next
  case (Suc i)
  have *:
    "{bf i w + W j w |w. w \<le> n} = set (map (\<lambda>w. W j w + bf i w) [0..<Suc n])"
    by (fastforce simp: add.commute image_def)
  from Suc \<open>t \<le> n\<close> show ?case
    by (simp add: OPT_Suc del: upt_Suc, subst Min.set_eq_fold[symmetric], auto simp: *)
qed


subsubsection \<open>Functional Memoization\<close>

memoize_fun bf\<^sub>m: bf with_memory dp_consistency_rbt monadifies (state) bf.simps

text \<open>Generated Definitions\<close>
context includes state_monad_syntax begin
thm bf\<^sub>m'.simps bf\<^sub>m_def
end

text \<open>Correspondence Proof\<close>
memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = bf\<^sub>m.memoized_correct

interpretation iterator
  "\<lambda> (x, y). x \<le> n \<and> y \<le> n"
  "\<lambda> (x, y). if y < n then (x, y + 1) else (x + 1, 0)"
  "\<lambda> (x, y). x * (n + 1) + y"
  by (rule table_iterator_up)

interpretation bottom_up: dp_consistency_iterator_empty
  "\<lambda> (_::(nat \<times> nat, int extended) mapping). True"
  "\<lambda> (x, y). bf x y"
  "\<lambda> k. do {m \<leftarrow> State_Monad.get; State_Monad.return (Mapping.lookup m k :: int extended option)}"
  "\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (Mapping.update k v m)}"
  "\<lambda> (x, y). x \<le> n \<and> y \<le> n"
  "\<lambda> (x, y). if y < n then (x, y + 1) else (x + 1, 0)"
  "\<lambda> (x, y). x * (n + 1) + y"
  Mapping.empty ..

definition
  "iter_bf = iter_state (\<lambda> (x, y). bf\<^sub>m' x y)"

lemma iter_bf_unfold[code]:
  "iter_bf = (\<lambda> (i, j).
    (if i \<le> n \<and> j \<le> n
     then do {
            bf\<^sub>m' i j;
            iter_bf (if j < n then (i, j + 1) else (i + 1, 0))
          }
     else State_Monad.return ()))"
  unfolding iter_bf_def by (rule ext) (safe, clarsimp simp: iter_state_unfold)

lemmas bf_memoized = bf\<^sub>m.memoized[OF bf\<^sub>m.crel]
lemmas bf_bottom_up = bottom_up.memoized[OF bf\<^sub>m.crel, folded iter_bf_def]

thm bf\<^sub>m'.simps bf_memoized


subsubsection \<open>Imperative Memoization\<close>

context
  fixes mem :: "nat ref \<times> nat ref \<times> int extended option array ref \<times> int extended option array ref"
  assumes mem_is_init: "mem = result_of (init_state (n + 1) 1 0) Heap.empty"
begin

lemma [intro]:
  "dp_consistency_heap_array_pair' (n + 1) fst snd id 1 0 mem"
  by (standard; simp add: mem_is_init injective_def)

interpretation iterator
  "\<lambda> (x, y). x \<le> n \<and> y \<le> n"
  "\<lambda> (x, y). if y < n then (x, y + 1) else (x + 1, 0)"
  "\<lambda> (x, y). x * (n + 1) + y"
  by (rule table_iterator_up)

lemma [intro]:
  "dp_consistency_heap_array_pair_iterator (n + 1) fst snd id 1 0 mem
  (\<lambda> (x, y). if y < n then (x, y + 1) else (x + 1, 0))
  (\<lambda> (x, y). x * (n + 1) + y)
  (\<lambda> (x, y). x \<le> n \<and> y \<le> n)"
  by (standard; simp add: mem_is_init injective_def)

memoize_fun bf\<^sub>h: bf
  with_memory (default_proof) dp_consistency_heap_array_pair_iterator
  where size = "n + 1"
    and key1="fst :: nat \<times> nat \<Rightarrow> nat" and key2="snd :: nat \<times> nat \<Rightarrow> nat"
    and k1="1 :: nat" and k2="0 :: nat"
    and to_index = "id :: nat \<Rightarrow> nat"
    and mem = mem
    and cnt = "\<lambda> (x, y). x \<le> n \<and> y \<le> n"
    and nxt = "\<lambda> (x :: nat, y). if y < n then (x, y + 1) else (x + 1, 0)"
    and sizef = "\<lambda> (x, y). x * (n + 1) + y"
monadifies (heap) bf.simps

memoize_correct
  by memoize_prover

lemmas memoized_empty = bf\<^sub>h.memoized_empty[OF bf\<^sub>h.consistent_DP_iter_and_compute[OF bf\<^sub>h.crel]]
lemmas iter_heap_unfold = iter_heap_unfold

end (* Fixed Memory *)

end (* Final Node *)

end (* Bellman Ford *)



subsubsection \<open>Extracting an Executable Constant for the Imperative Implementation\<close>

ground_function (prove_termination) bf\<^sub>h'_impl: bf\<^sub>h'.simps

lemma bf\<^sub>h'_impl_def:
  fixes n :: nat
  fixes mem :: "nat ref \<times> nat ref \<times> int extended option array ref \<times> int extended option array ref"
  assumes mem_is_init: "mem = result_of (init_state (n + 1) 1 0) Heap.empty"
  shows "bf\<^sub>h'_impl n w t mem = bf\<^sub>h' n w t mem"
proof -
  have "bf\<^sub>h'_impl n w t mem i j = bf\<^sub>h' n w t mem i j" for i j
    by (induction rule: bf\<^sub>h'.induct[OF mem_is_init];
        simp add: bf\<^sub>h'.simps[OF mem_is_init]; solve_cong simp
       )
  then show ?thesis
    by auto
qed

definition
  "iter_bf_heap n w t mem = iterator_defs.iter_heap
      (\<lambda>(x, y). x \<le> n \<and> y \<le> n)
      (\<lambda>(x, y). if y < n then (x, y + 1) else (x + 1, 0))
      (\<lambda>(x, y). bf\<^sub>h'_impl n w t mem x y)"

lemma iter_bf_heap_unfold[code]:
  "iter_bf_heap n w t mem = (\<lambda> (i, j).
    (if i \<le> n \<and> j \<le> n
     then do {
            bf\<^sub>h'_impl n w t mem i j;
            iter_bf_heap n w t mem (if j < n then (i, j + 1) else (i + 1, 0))
          }
     else Heap_Monad.return ()))"
  unfolding iter_bf_heap_def by (rule ext) (safe, simp add: iter_heap_unfold)

definition
  "bf_impl n w t i j = do {
    mem \<leftarrow> (init_state (n + 1) (1::nat) (0::nat) ::
      (nat ref \<times> nat ref \<times> int extended option array ref \<times> int extended option array ref) Heap);
    iter_bf_heap n w t mem (0, 0);
    bf\<^sub>h'_impl n w t mem i j
  }"

lemma bf_impl_correct:
  "bf n w t i j = result_of (bf_impl n w t i j) Heap.empty"
  using memoized_empty[OF HOL.refl, of n w t "(i, j)"]
  by (simp add:
        execute_bind_success[OF succes_init_state] bf_impl_def bf\<^sub>h'_impl_def iter_bf_heap_def
      )


subsubsection \<open>Test Cases\<close>

definition
  "G\<^sub>1_list = [[(1 :: nat,-6 :: int), (2,4), (3,5)], [(3,10)], [(3,2)], []]"

definition
  "graph_of a i j = case_option \<infinity> (Fin o snd) (List.find (\<lambda> p. fst p = j) (a !! i))"

definition "test_bf = bf_impl 3 (graph_of (IArray G\<^sub>1_list)) 3 3 0"

code_reflect Test functions test_bf

text \<open>One can see a trace of the calls to the memory in the output\<close>
ML \<open>Test.test_bf ()\<close>

lemma bottom_up_alt[code]:
  "bf n W t i j =
     fst (run_state
      (iter_bf n W t (0, 0) \<bind> (\<lambda>_. bf\<^sub>m' n W t i j))
      Mapping.empty)"
  using bf_bottom_up by auto

definition
  "bf_ia n W t i j = (let W' = graph_of (IArray W) in
    fst (run_state
      (iter_bf n W' t (i, j) \<bind> (\<lambda>_. bf\<^sub>m' n W' t i j))
      Mapping.empty)
  )"

value "fst (run_state (bf\<^sub>m' 3 (graph_of (IArray G\<^sub>1_list)) 3 3 0) Mapping.empty)"

value "bf 3 (graph_of (IArray G\<^sub>1_list)) 3 3 0"

end (* Theory *)