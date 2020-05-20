subsection "Minimum Edit Distance"

theory Min_Ed_Dist0
imports
  "HOL-Library.IArray"
  "HOL-Library.Code_Target_Numeral"
  "HOL-Library.Product_Lexorder"
  "HOL-Library.RBT_Mapping"
  "../state_monad/State_Main"
  "../heap_monad/Heap_Main"
  Example_Misc
  "../util/Tracing"
  "../util/Ground_Function"
begin

subsubsection "Misc"

text "Executable argmin"

fun argmin :: "('a \<Rightarrow> 'b::order) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"argmin f [a] = a" |
"argmin f (a#as) = (let m = argmin f as in if f a \<le> f m then a else m)"
(* end rm *)

(* Ex: Optimization of argmin *)
fun argmin2 :: "('a \<Rightarrow> 'b::order) \<Rightarrow> 'a list \<Rightarrow> 'a * 'b" where
"argmin2 f [a] = (a, f a)" |
"argmin2 f (a#as) = (let fa = f a; (am,m) = argmin2 f as in if fa \<le> m then (a, fa) else (am,m))"


subsubsection "Edit Distance"

datatype 'a ed = Copy | Repl 'a | Ins 'a | Del

fun edit :: "'a ed list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"edit (Copy # es) (x # xs) = x # edit es xs" |
"edit (Repl a # es) (x # xs) = a # edit es xs" |
"edit (Ins a # es) xs = a # edit es xs" |
"edit (Del # es) (x # xs) = edit es xs" |
"edit (Copy # es) [] = edit es []" |
"edit (Repl a # es) [] = edit es []" |
"edit (Del # es) [] = edit es []" |
"edit [] xs = xs"

abbreviation cost where
"cost es \<equiv> length [e <- es. e \<noteq> Copy]"


subsubsection "Minimum Edit Sequence"

fun min_eds :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a ed list" where
"min_eds [] [] = []" |
"min_eds [] (y#ys) = Ins y # min_eds [] ys" |
"min_eds (x#xs) [] = Del # min_eds xs []" |
"min_eds (x#xs) (y#ys) =
  argmin cost [Ins y # min_eds (x#xs) ys, Del # min_eds xs (y#ys),
     (if x=y then Copy else Repl y) # min_eds xs ys]"

lemma "min_eds ''vintner'' ''writers'' =
  [Ins CHR ''w'', Repl CHR ''r'', Copy, Del, Copy, Del, Copy, Copy, Ins CHR ''s'']"
by eval
(*
value "min_eds ''madagascar'' ''bananas''"

value "min_eds ''madagascaram'' ''banananas''"
*)
lemma min_eds_correct: "edit (min_eds xs ys) xs = ys"
by (induction xs ys rule: min_eds.induct) auto

lemma min_eds_same: "min_eds xs xs = replicate (length xs) Copy"
by (induction xs) auto

lemma min_eds_eq_Nil_iff: "min_eds xs ys = [] \<longleftrightarrow> xs = [] \<and> ys = []"
by (induction xs ys rule: min_eds.induct) auto

lemma min_eds_Nil: "min_eds [] ys = map Ins ys"
by (induction ys) auto

lemma min_eds_Nil2: "min_eds xs [] = replicate (length xs) Del"
by (induction xs) auto

lemma if_edit_Nil2: "edit es ([]::'a list) = ys \<Longrightarrow> length ys \<le> cost es"
apply(induction es "[]::'a list" arbitrary: ys rule: edit.induct)
apply auto
 apply fastforce
apply fastforce
done

lemma if_edit_eq_Nil: "edit es xs = [] \<Longrightarrow> length xs \<le> cost es"
by (induction es xs rule: edit.induct) auto

lemma min_eds_minimal: "edit es xs = ys \<Longrightarrow> cost(min_eds xs ys) \<le> cost es"
proof(induction xs ys arbitrary: es rule: min_eds.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by (auto simp add: min_eds_Nil dest: if_edit_Nil2)
next
  case 3
  thus ?case by(auto simp add: min_eds_Nil2 dest: if_edit_eq_Nil)
next
  case 4
  show ?case
  proof (cases "es")
    case Nil then show ?thesis using "4.prems" by (auto simp: min_eds_same)
  next
    case [simp]: (Cons e es')
    show ?thesis
    proof (cases e)
      case Copy
      thus ?thesis using "4.prems" "4.IH"(3)[of es'] by simp
    next
      case (Repl a)
      thus ?thesis using "4.prems" "4.IH"(3)[of es']
        using [[simp_depth_limit=1]] by simp
    next
      case (Ins a)
      thus ?thesis using "4.prems" "4.IH"(1)[of es']
        using [[simp_depth_limit=1]] by auto
    next
      case Del
      thus ?thesis using "4.prems" "4.IH"(2)[of es']
        using [[simp_depth_limit=1]] by auto
    qed
  qed
qed


subsubsection "Computing the Minimum Edit Distance"

fun min_ed :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
"min_ed [] [] = 0" |
"min_ed [] (y#ys) = 1 + min_ed [] ys" |
"min_ed (x#xs) [] = 1 + min_ed xs []" |
"min_ed (x#xs) (y#ys) =
  Min {1 + min_ed (x#xs) ys, 1 + min_ed xs (y#ys), (if x=y then 0 else 1) + min_ed xs ys}"

lemma min_ed_min_eds: "min_ed xs ys = cost(min_eds xs ys)"
apply(induction xs ys rule: min_ed.induct)
apply (auto split!: if_splits)
done

lemma "min_ed ''madagascar'' ''bananas'' = 6"
by eval
(*
value "min_ed ''madagascaram'' ''banananas''"
*)

text "Exercise: Optimization of the Copy case"

fun min_eds2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a ed list" where
"min_eds2 [] [] = []" |
"min_eds2 [] (y#ys) = Ins y # min_eds2 [] ys" |
"min_eds2 (x#xs) [] = Del # min_eds2 xs []" |
"min_eds2 (x#xs) (y#ys) =
  (if x=y then Copy # min_eds2 xs ys
   else argmin cost
     [Ins y # min_eds2 (x#xs) ys, Del # min_eds2 xs (y#ys), Repl y # min_eds2 xs ys])"

value "min_eds2 ''madagascar'' ''bananas''"

lemma cost_Copy_Del: "cost(min_eds xs ys) \<le> cost (min_eds xs (x#ys)) + 1"
apply(induction xs ys rule: min_eds.induct)
apply(auto simp del: filter_True filter_False split!: if_splits)
done

lemma cost_Copy_Ins: "cost(min_eds xs ys) \<le> cost (min_eds (x#xs) ys) + 1"
apply(induction xs ys rule: min_eds.induct)
apply(auto simp del: filter_True filter_False split!: if_splits)
done

lemma "cost(min_eds2 xs ys) = cost(min_eds xs ys)"
proof(induction xs ys rule: min_eds2.induct)
  case (4 x xs y ys) thus ?case
    apply (auto split!: if_split)
      apply (metis (mono_tags, lifting) Suc_eq_plus1 Suc_leI cost_Copy_Del cost_Copy_Ins le_imp_less_Suc le_neq_implies_less not_less)
     apply (metis Suc_eq_plus1 cost_Copy_Del le_antisym)
    by (metis Suc_eq_plus1 cost_Copy_Ins le_antisym)
qed simp_all

lemma "min_eds2 xs ys = min_eds xs ys"
oops
(* Not proveable because Copy comes last in min_eds but first in min_eds2.
   Can reorder, but the proof still requires the same two lemmas cost_*_* above.
*)


subsubsection "Indexing"

text "Indexing lists"

context
fixes xs ys :: "'a list"
fixes m n :: nat
begin

function (sequential)
  min_ed_ix' :: "nat * nat \<Rightarrow> nat" where
"min_ed_ix' (i,j) =
  (if i \<ge> m then
     if j \<ge> n then 0 else 1 + min_ed_ix' (i,j+1) else
   if j \<ge> n then 1 + min_ed_ix' (i+1, j)
   else
   Min {1 + min_ed_ix' (i,j+1), 1 + min_ed_ix' (i+1, j),
       (if xs!i = ys!j then 0 else 1) + min_ed_ix' (i+1,j+1)})"
by pat_completeness auto
termination by(relation "measure(\<lambda>(i,j). (m - i) + (n - j))") auto


declare min_ed_ix'.simps[simp del]

end

lemma min_ed_ix'_min_ed:
  "min_ed_ix' xs ys (length xs) (length ys) (i, j) = min_ed (drop i xs) (drop j ys)"
apply(induction "(i,j)" arbitrary: i j rule: min_ed_ix'.induct[of "length xs" "length ys"])
apply(subst min_ed_ix'.simps)
apply(simp add: Cons_nth_drop_Suc[symmetric])
done


text "Indexing functions"

context
fixes xs ys :: "nat \<Rightarrow> 'a"
fixes m n :: nat
begin

function (sequential)
  min_ed_ix :: "nat \<times> nat \<Rightarrow> nat" where
"min_ed_ix (i, j) =
  (if i \<ge> m then
     if j \<ge> n then 0 else n-j else
   if j \<ge> n then m-i
   else
   min_list [1 + min_ed_ix (i, j+1), 1 + min_ed_ix (i+1, j),
       (if xs i = ys j then 0 else 1) + min_ed_ix (i+1, j+1)])"
by pat_completeness auto
termination by(relation "measure(\<lambda>(i,j). (m - i) + (n - j))") auto


subsubsection \<open>Functional Memoization\<close>

memoize_fun min_ed_ix\<^sub>m: min_ed_ix with_memory dp_consistency_mapping monadifies (state) min_ed_ix.simps
thm min_ed_ix\<^sub>m'.simps

memoize_correct
  by memoize_prover
print_theorems

lemmas [code] = min_ed_ix\<^sub>m.memoized_correct

declare min_ed_ix.simps[simp del]


subsubsection \<open>Imperative Memoization\<close>

context
  fixes mem :: "nat ref \<times> nat ref \<times> nat option array ref \<times> nat option array ref"
  assumes mem_is_init: "mem = result_of (init_state (n + 1) m (m + 1)) Heap.empty"
begin

interpretation iterator
  "\<lambda> (x, y). x \<le> m \<and> y \<le> n \<and> x > 0"
  "\<lambda> (x, y). if y > 0 then (x, y - 1) else (x - 1, n)"
  "\<lambda> (x, y). (m - x) * (n + 1) + (n - y)"
  by (rule table_iterator_down)

lemma [intro]:
  "dp_consistency_heap_array_pair' (n + 1) fst snd id m (m + 1) mem"
  by (standard; simp add: mem_is_init injective_def)

lemma [intro]:
  "dp_consistency_heap_array_pair_iterator (n + 1) fst snd id m (m + 1) mem
   (\<lambda> (x, y). if y > 0 then (x, y - 1) else (x - 1, n))
   (\<lambda> (x, y). (m - x) * (n + 1) + (n - y))
   (\<lambda> (x, y). x \<le> m \<and> y \<le> n \<and> x > 0)
  "
  by (standard; simp add: mem_is_init injective_def)

memoize_fun min_ed_ix\<^sub>h: min_ed_ix
  with_memory (default_proof) dp_consistency_heap_array_pair_iterator
  where size = "n + 1"
    and key1="fst :: nat \<times> nat \<Rightarrow> nat" and key2="snd :: nat \<times> nat \<Rightarrow> nat"
    and k1="m :: nat" and k2="m + 1 :: nat"
    and to_index = "id :: nat \<Rightarrow> nat"
    and mem = mem
    and cnt = "\<lambda> (x, y). x \<le> m \<and> y \<le> n \<and> x > 0"
    and nxt = "\<lambda> (x::nat, y). if y > 0 then (x, y - 1) else (x - 1, n)"
    and sizef = "\<lambda> (x, y). (m - x) * (n + 1) + (n - y)"
monadifies (heap) min_ed_ix.simps

memoize_correct
  by memoize_prover

lemmas memoized_empty =
  min_ed_ix\<^sub>h.memoized_empty[OF min_ed_ix\<^sub>h.consistent_DP_iter_and_compute[OF min_ed_ix\<^sub>h.crel]]
lemmas iter_heap_unfold = iter_heap_unfold

end (* Fixed Memory *)

end


subsubsection \<open>Test Cases\<close>

abbreviation "slice xs i j \<equiv> map xs [i..<j]"

lemma min_ed_Nil1: "min_ed [] ys = length ys"
by (induction ys) auto

lemma min_ed_Nil2: "min_ed xs [] = length xs"
by (induction xs) auto

(* prove correctness of min_ed_ix directly ? *)
lemma min_ed_ix_min_ed: "min_ed_ix xs ys m n (i,j) = min_ed (slice xs i m) (slice ys j n)"
apply(induction "(i,j)" arbitrary: i j rule: min_ed_ix.induct[of m n])
apply(simp add: min_ed_ix.simps upt_conv_Cons min_ed_Nil1 min_ed_Nil2 Suc_diff_Suc)
done


text \<open>Functional Test Cases\<close>

definition "min_ed_list xs ys = min_ed_ix (\<lambda>i. xs!i) (\<lambda>i. ys!i) (length xs) (length ys) (0,0)"

lemma "min_ed_list ''madagascar'' ''bananas'' = 6"
by eval

definition "min_ed_ia xs ys = (let a = IArray xs; b = IArray ys
  in min_ed_ix (\<lambda>i. a!!i) (\<lambda>i. b!!i) (length xs) (length ys) (0,0))"

lemma "min_ed_ia ''madagascar'' ''bananas'' = 6"
by eval



text \<open>Extracting an Executable Constant for the Imperative Implementation\<close>

ground_function min_ed_ix\<^sub>h'_impl: min_ed_ix\<^sub>h'.simps
termination
  by(relation "measure(\<lambda>(xs, ys, m, n, mem, i, j). (m - i) + (n - j))") auto

lemmas [simp del] = min_ed_ix\<^sub>h'_impl.simps min_ed_ix\<^sub>h'.simps

lemma min_ed_ix\<^sub>h'_impl_def:
  includes heap_monad_syntax
  fixes m n :: nat
  fixes mem :: "nat ref \<times> nat ref \<times> nat option array ref \<times> nat option array ref"
  assumes mem_is_init: "mem = result_of (init_state (n + 1) m (m + 1)) Heap.empty"
  shows "min_ed_ix\<^sub>h'_impl xs ys m n mem = min_ed_ix\<^sub>h' xs ys m n mem"
proof -
  have "min_ed_ix\<^sub>h'_impl xs ys m n mem (i, j) = min_ed_ix\<^sub>h' xs ys m n mem (i, j)" for i j
    apply (induction rule: min_ed_ix\<^sub>h'.induct[OF mem_is_init])
    apply (subst min_ed_ix\<^sub>h'_impl.simps)
    apply (subst min_ed_ix\<^sub>h'.simps[OF mem_is_init])
    apply (solve_cong simp)
    done
  then show ?thesis
    by auto
qed

definition
  "iter_min_ed_ix xs ys m n mem = iterator_defs.iter_heap
    (\<lambda> (x, y). x \<le> m \<and> y \<le> n \<and> x > 0)
    (\<lambda> (x, y). if y > 0 then (x, y - 1) else (x - 1, n))
    (min_ed_ix\<^sub>h'_impl xs ys m n mem)
  "

lemma iter_min_ed_ix_unfold[code]:
  "iter_min_ed_ix xs ys m n mem = (\<lambda> (i, j).
    (if i > 0 \<and> i \<le> m \<and> j \<le> n
     then do {
            min_ed_ix\<^sub>h'_impl xs ys m n mem (i, j);
            iter_min_ed_ix xs ys m n mem (if j > 0 then (i, j - 1) else (i - 1, n))
          }
     else Heap_Monad.return ()))"
  unfolding iter_min_ed_ix_def by (rule ext) (safe, simp add: iter_heap_unfold)

definition
  "min_ed_ix_impl xs ys m n i j = do {
    mem \<leftarrow> (init_state (n + 1) (m::nat) (m + 1) ::
      (nat ref \<times> nat ref \<times> nat option array ref \<times> nat option array ref) Heap);
    iter_min_ed_ix xs ys m n mem (m, n);
    min_ed_ix\<^sub>h'_impl xs ys m n mem (i, j)
  }"

lemma bf_impl_correct:
  "min_ed_ix xs ys m n (i, j) = result_of (min_ed_ix_impl xs ys m n i j) Heap.empty"
  using memoized_empty[OF HOL.refl, of xs ys m n "(i, j)" "\<lambda> _. (m, n)"]
  by (simp add:
      execute_bind_success[OF succes_init_state] min_ed_ix_impl_def min_ed_ix\<^sub>h'_impl_def
      iter_min_ed_ix_def
     )


text \<open>Imperative Test Case\<close>

definition
  "min_ed_ia\<^sub>h xs ys = (let a = IArray xs; b = IArray ys
  in min_ed_ix_impl (\<lambda>i. a!!i) (\<lambda>i. b!!i) (length xs) (length ys) 0 0)"

definition
  "test_case = min_ed_ia\<^sub>h ''madagascar'' ''bananas''"

export_code min_ed_ix in SML module_name Test

code_reflect Test functions test_case

text \<open>One can see a trace of the calls to the memory in the output\<close>
ML \<open>Test.test_case ()\<close>

end
