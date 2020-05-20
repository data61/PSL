subsection "The CYK Algorithm"

theory CYK
imports
  "HOL-Library.IArray"
  "HOL-Library.Code_Target_Numeral"
  "HOL-Library.Product_Lexorder"
  "HOL-Library.RBT_Mapping"
  "../state_monad/State_Main"
  "../heap_monad/Heap_Default"
  Example_Misc
begin

subsubsection \<open>Misc\<close>

lemma append_iff_take_drop:
  "w = u@v \<longleftrightarrow> (\<exists>k \<in> {0..length w}. u = take k w \<and> v = drop k w)"
by (metis (full_types) append_eq_conv_conj append_take_drop_id atLeastAtMost_iff le0 le_add1 length_append) 

lemma append_iff_take_drop1: "u \<noteq> [] \<Longrightarrow> v \<noteq> [] \<Longrightarrow>
  w = u@v \<longleftrightarrow> (\<exists>k \<in> {1..length w - 1}. u = take k w \<and> v = drop k w)"
by(auto simp: append_iff_take_drop)

subsubsection \<open>Definitions\<close>

datatype ('n, 't) rhs = NN 'n 'n | T 't 

type_synonym ('n, 't) prods = "('n \<times> ('n, 't) rhs) list"

context
fixes P :: "('n :: heap, 't) prods"
begin

inductive yield :: "'n \<Rightarrow> 't list \<Rightarrow> bool" where
"(A, T a) \<in> set P \<Longrightarrow> yield A [a]" |
"\<lbrakk> (A, NN B C) \<in> set P; yield B u; yield C v \<rbrakk> \<Longrightarrow> yield A (u@v)"

lemma yield_not_Nil: "yield A w \<Longrightarrow> w \<noteq> []"
by (induction rule: yield.induct) auto

lemma yield_eq1:
  "yield A [a] \<longleftrightarrow> (A, T a) \<in> set P" (is "?L = ?R")
proof
  assume ?L thus ?R 
    by(induction A "[a]" arbitrary: a rule: yield.induct)
      (auto simp add: yield_not_Nil append_eq_Cons_conv)
qed (simp add: yield.intros)

lemma yield_eq2: assumes "length w > 1"
shows "yield A w \<longleftrightarrow> (\<exists>B u C v. yield B u \<and> yield C v \<and> w = u@v \<and> (A, NN B C) \<in> set P)"
       (is "?L = ?R")
proof
  assume ?L from this assms show ?R
    by(induction rule: yield.induct) (auto)
next
  assume ?R with assms show ?L
    by (auto simp add: yield.intros)
qed


subsubsection "CYK on Lists"

fun cyk :: "'t list \<Rightarrow> 'n list" where
"cyk [] = []" |
"cyk [a] = [A . (A, T a') <- P, a'= a]" |
"cyk w =
  [A. k <- [1..<length w], B <- cyk (take k w), C <- cyk (drop k w), (A, NN B' C') <- P, B' = B, C' = C]"

lemma set_cyk_simp2[simp]: "length w \<ge> 2 \<Longrightarrow> set(cyk w) =
  (\<Union>k \<in> {1..length w - 1}. \<Union>B \<in> set(cyk (take k w)). \<Union>C \<in> set(cyk (drop k w)). {A. (A, NN B C) \<in> set P})"
apply(cases w)
 apply simp
subgoal for _ w'
apply(case_tac w')
 apply auto
    apply force
   apply force
  apply force
 using le_Suc_eq le_simps(3) apply auto[1]
by (metis drop_Suc_Cons le_Suc_eq le_antisym not_le take_Suc_Cons)
done

declare cyk.simps(3)[simp del]

lemma cyk_correct: "set(cyk w) = {N. yield N w}"
proof (induction w rule: cyk.induct)
  case 1 thus ?case by (auto dest: yield_not_Nil)
next
  case 2 thus ?case by (auto simp add: yield_eq1)
next
  case (3 v vb vc)
  let ?w = "v # vb # vc"
  have "set(cyk ?w) = (\<Union>k\<in>{1..length ?w-1}. {N. \<exists>A B. (N, NN A B) \<in> set P \<and>
             yield A (take k ?w) \<and> yield B (drop k ?w)})"
    by(auto simp add:"3.IH" simp del:upt_Suc)
  also have "... = {N. \<exists>A B. (N, NN A B) \<in> set P \<and>
              (\<exists>u v. yield A u \<and> yield B v \<and> ?w = u@v)}"
    by(fastforce simp add: append_iff_take_drop1 yield_not_Nil)
  also have "... = {N. yield N ?w}" using yield_eq2[of ?w] by(auto)
  finally show ?case .
qed

subsubsection "CYK on Lists and Index"

fun cyk2 :: "'t list \<Rightarrow> nat * nat \<Rightarrow> 'n list" where
"cyk2 w (i,0) = []" |
"cyk2 w (i,Suc 0) = [A . (A, T a) <- P, a = w!i]" |
"cyk2 w (i,n) =
[A. k <- [1..<n], B <- cyk2 w (i,k), C <- cyk2 w (i+k,n-k), (A, NN B' C') <- P, B' = B, C' = C]"

lemma set_aux: "(\<Union>xb\<in>set P. {A. (A, NN B C) = xb}) = {A. (A, NN B C) \<in> set P}"
by auto

lemma cyk2_eq_cyk: "i+n \<le> length w \<Longrightarrow> set(cyk2 w (i,n)) = set(cyk (take n (drop i w)))"
proof(induction w "(i,n)" arbitrary: i n rule: cyk2.induct)
  case 1 show ?case by(simp)
next
  case 2 show ?case using "2.prems"
    by(auto simp: hd_drop_conv_nth take_Suc)
next
  case (3 w i m)
  show ?case using "3.prems"
    by(simp add: 3(1,2) min.absorb1 min.absorb2 drop_take atLeastLessThanSuc_atLeastAtMost set_aux
         del:upt_Suc cong: SUP_cong_simp)
      (simp add: add.commute)
qed

definition "CYK S w =  (S \<in> set(cyk2 w (0, length w)))"

theorem CYK_correct: "CYK S w = yield S w"
by(simp add: CYK_def cyk2_eq_cyk cyk_correct)


subsubsection "CYK With Index Function"

context
fixes w :: "nat \<Rightarrow> 't"
begin

fun cyk_ix :: "nat * nat \<Rightarrow> 'n list" where
"cyk_ix (i,0) = []" |
"cyk_ix (i,Suc 0) = [A . (A, T a) <- P, a = w i]" |
"cyk_ix (i,n) =
  [A. k <- [1..<n], B <- cyk_ix (i,k), C <- cyk_ix (i+k,n-k), (A, NN B' C') <- P, B' = B, C' = C]"

subsubsection \<open>Correctness Proof\<close>

lemma cyk_ix_simp2: "set(cyk_ix (i,Suc(Suc n))) =
  (\<Union>k \<in> {1..Suc n}. \<Union>B \<in> set(cyk_ix (i,k)). \<Union>C \<in> set(cyk_ix (i+k,n+2-k)). {A. (A, NN B C) \<in> set P})"
by(simp add: atLeastLessThanSuc_atLeastAtMost set_aux del: upt_Suc)

declare cyk_ix.simps(3)[simp del]

abbreviation "slice f i j \<equiv> map f [i..<j]"

lemma slice_append_iff_take_drop1: "u \<noteq> [] \<Longrightarrow> v \<noteq> [] \<Longrightarrow>
  slice w i j = u @ v \<longleftrightarrow> (\<exists>k. 1 \<le> k \<and> k \<le> j-i-1 \<and> slice w i (i + k) = u \<and> slice w (i + k) j = v)"
by(subst append_iff_take_drop1) (auto simp: take_map drop_map Bex_def)

lemma cyk_ix_correct:
  "set(cyk_ix (i,n)) = {N. yield N (slice w i (i+n))}"
proof (induction "(i,n)" arbitrary: i n rule: cyk_ix.induct)
  case 1 thus ?case by (auto simp: dest: yield_not_Nil)
next
  case 2 thus ?case by (auto simp add: yield_eq1)
next
  case (3 i m)
  let ?n = "Suc(Suc m)" let ?w = "slice w i (i+?n)"
  have "set(cyk_ix (i,?n)) = (\<Union>k\<in>{1..Suc m}. {N. \<exists>A B. (N, NN A B) \<in> set P \<and>
             yield A (slice w i (i+k)) \<and> yield B (slice w (i+k) (i+?n))})"
    by(auto simp add: 3 cyk_ix_simp2 simp del: upt_Suc)
  also have "... = {N. \<exists>A B. (N, NN A B) \<in> set P \<and>
              (\<exists>u v. yield A u \<and> yield B v \<and> slice w i (i+?n) = u@v)}"
    by(fastforce simp del: upt_Suc simp: slice_append_iff_take_drop1 yield_not_Nil cong: conj_cong)
  also have "... = {N. yield N ?w}" using yield_eq2[of ?w] by(auto)
  finally show ?case .
qed

subsubsection \<open>Functional Memoization\<close>

memoize_fun cyk_ix\<^sub>m: cyk_ix with_memory dp_consistency_mapping monadifies (state) cyk_ix.simps
thm cyk_ix\<^sub>m'.simps

memoize_correct
  by memoize_prover
print_theorems

lemmas [code] = cyk_ix\<^sub>m.memoized_correct


subsubsection \<open>Imperative Memoization\<close>

context
  fixes n :: nat
begin

context
  fixes mem :: "'n list option array"
begin

memoize_fun cyk_ix\<^sub>h: cyk_ix
  with_memory dp_consistency_heap_default where bound = "Bound (0, 0) (n, n)" and mem="mem"
  monadifies (heap) cyk_ix.simps

context includes heap_monad_syntax begin
thm cyk_ix\<^sub>h'.simps cyk_ix\<^sub>h_def
end

memoize_correct
  by memoize_prover

lemmas memoized_empty = cyk_ix\<^sub>h.memoized_empty

lemmas init_success = cyk_ix\<^sub>h.init_success

end (* Fixed array *)

definition "cyk_ix_impl i j = do {mem \<leftarrow> mem_empty (n * n); cyk_ix\<^sub>h' mem (i, j)}"

lemma cyk_ix_impl_success:
  "success (cyk_ix_impl i j) Heap.empty"
  using init_success[of _ cyk_ix\<^sub>h' "(i, j)", OF cyk_ix\<^sub>h.crel]
  by (simp add: cyk_ix_impl_def index_size_defs)

lemma min_wpl_heap:
  "cyk_ix (i, j) = result_of (cyk_ix_impl i j) Heap.empty"
  unfolding cyk_ix_impl_def
  using memoized_empty[of _ cyk_ix\<^sub>h' "(i, j)", OF cyk_ix\<^sub>h.crel]
  by (simp add: index_size_defs)

end (* Bound *)

end (* Index *)

definition "CYK_ix S w n =  (S \<in> set(cyk_ix w (0,n)))"

theorem CYK_ix_correct: "CYK_ix S w n = yield S (slice w 0 n)"
by(simp add: CYK_ix_def cyk_ix_correct)

definition "cyk_list w = cyk_ix (\<lambda>i. w ! i) (0,length w)"

definition
  "CYK_ix_impl S w n = do {R \<leftarrow> cyk_ix_impl w n 0 n; return (S \<in> set R)}"

lemma CYK_ix_impl_correct:
  "result_of (CYK_ix_impl S w n) Heap.empty = yield S (slice w 0 n)"
  unfolding CYK_ix_impl_def
  by (simp add: execute_bind_success[OF cyk_ix_impl_success]
        min_wpl_heap[symmetric] CYK_ix_correct CYK_ix_def[symmetric]
     )

end (* Fixed Productions *)


subsubsection \<open>Functional Test Case\<close>

value
  "(let P = [(0::int, NN 1 2), (0, NN 2 3),
            (1, NN 2 1), (1, T (CHR ''a'')),
            (2, NN 3 3), (2, T (CHR ''b'')),
            (3, NN 1 2), (3, T (CHR ''a''))]
  in map (\<lambda>w. cyk2 P w (0,length w)) [''baaba'', ''baba''])"

value
  "(let P = [(0::int, NN 1 2), (0, NN 2 3),
            (1, NN 2 1), (1, T (CHR ''a'')),
            (2, NN 3 3), (2, T (CHR ''b'')),
            (3, NN 1 2), (3, T (CHR ''a''))]
  in map (cyk_list P) [''baaba'', ''baba''])"

definition "cyk_ia P w = (let a = IArray w in cyk_ix P (\<lambda>i. a !! i) (0,length w))"

value
  "(let P = [(0::int, NN 1 2), (0, NN 2 3),
            (1, NN 2 1), (1, T (CHR ''a'')),
            (2, NN 3 3), (2, T (CHR ''b'')),
            (3, NN 1 2), (3, T (CHR ''a''))]
  in map (cyk_ia P) [''baaba'', ''baba''])"

subsubsection \<open>Imperative Test Case\<close>

definition "cyk_ia' P w = (let a = IArray w in cyk_ix_impl P (\<lambda>i. a !! i) (length w) 0 (length w))"

definition
  "test = (let P = [(0::int, NN 1 2), (0, NN 2 3),
            (1, NN 2 1), (1, T (CHR ''a'')),
            (2, NN 3 3), (2, T (CHR ''b'')),
            (3, NN 1 2), (3, T (CHR ''a''))]
  in map (cyk_ia' P) [''baaba'', ''baba''])"

code_reflect Test functions test

ML \<open>List.map (fn f => f ()) Test.test\<close>

end
