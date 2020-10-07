(*
  File: DynamicArray.thy
  Author: Bohua Zhan
*)

section \<open>Implementation of dynamic arrays\<close>

theory DynamicArray
  imports Arrays_Impl
begin

text \<open>Dynamically allocated arrays.\<close>

datatype 'a dynamic_array = Dyn_Array (alen: nat) (aref: "'a array")
setup \<open>add_simple_datatype "dynamic_array"\<close>

subsection \<open>Raw assertion\<close>

fun dyn_array_raw :: "'a::heap list \<times> nat \<Rightarrow> 'a dynamic_array \<Rightarrow> assn" where
  "dyn_array_raw (xs, n) (Dyn_Array m a) = (a \<mapsto>\<^sub>a xs * \<up>(m = n))"
setup \<open>add_rewrite_ent_rule @{thm dyn_array_raw.simps}\<close>

definition dyn_array_new :: "'a::heap dynamic_array Heap" where
  "dyn_array_new = do {
     p \<leftarrow> Array.new 5 undefined;
     return (Dyn_Array 0 p)
   }"

lemma dyn_array_new_rule' [hoare_triple]:
  "<emp>
   dyn_array_new
   <dyn_array_raw (replicate 5 undefined, 0)>" by auto2

fun double_length :: "'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where
  "double_length (Dyn_Array al ar) = do {
      am \<leftarrow> Array.len ar;
      p \<leftarrow> Array.new (2 * am + 1) undefined;
      array_copy ar p am;
      return (Dyn_Array am p)
    }"

fun double_length_fun :: "'a::heap list \<times> nat \<Rightarrow> 'a list \<times> nat" where
  "double_length_fun (xs, n) =
    (Arrays_Ex.array_copy xs (replicate (2 * n + 1) undefined) n, n)"
setup \<open>add_rewrite_rule @{thm double_length_fun.simps}\<close>

lemma double_length_rule' [hoare_triple]:
  "length xs = n \<Longrightarrow>
   <dyn_array_raw (xs, n) p>
   double_length p
   <dyn_array_raw (double_length_fun (xs, n))>\<^sub>t" by auto2

fun push_array_basic :: "'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where
  "push_array_basic x (Dyn_Array al ar) = do {
    Array.upd al x ar;
    return (Dyn_Array (al + 1) ar)
   }"

fun push_array_basic_fun :: "'a \<Rightarrow> 'a::heap list \<times> nat \<Rightarrow> 'a list \<times> nat" where
  "push_array_basic_fun x (xs, n) = (list_update xs n x, n + 1)"
setup \<open>add_rewrite_rule @{thm push_array_basic_fun.simps}\<close>

lemma push_array_basic_rule' [hoare_triple]:
  "n < length xs \<Longrightarrow>
   <dyn_array_raw (xs, n) p>
   push_array_basic x p
   <dyn_array_raw (push_array_basic_fun x (xs, n))>" by auto2

definition array_length :: "'a dynamic_array \<Rightarrow> nat Heap" where
  "array_length d = return (alen d)"

lemma array_length_rule' [hoare_triple]:
  "<dyn_array_raw (xs, n) p>
   array_length p
   <\<lambda>r. dyn_array_raw (xs, n) p * \<up>(r = n)>" by auto2

definition array_max :: "'a::heap dynamic_array \<Rightarrow> nat Heap" where
  "array_max d = Array.len (aref d)"

lemma array_max_rule' [hoare_triple]:
  "<dyn_array_raw (xs, n) p>
   array_max p
   <\<lambda>r. dyn_array_raw (xs, n) p * \<up>(r = length xs)>" by auto2

definition array_nth :: "'a::heap dynamic_array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  "array_nth d i = Array.nth (aref d) i"

lemma array_nth_rule' [hoare_triple]:
  "i < n \<Longrightarrow> n \<le> length xs \<Longrightarrow>
   <dyn_array_raw (xs, n) p>
   array_nth p i
   <\<lambda>r. dyn_array_raw (xs, n) p * \<up>(r = xs ! i)>" by auto2

definition array_upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> unit Heap" where
  "array_upd i x d = do { Array.upd i x (aref d); return () }"

lemma array_upd_rule' [hoare_triple]:
  "i < n \<Longrightarrow> n \<le> length xs \<Longrightarrow>
   <dyn_array_raw (xs, n) p>
   array_upd i x p
   <\<lambda>_. dyn_array_raw (list_update xs i x, n) p>" by auto2

definition push_array :: "'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where
  "push_array x p = do {
    m \<leftarrow> array_max p;
    l \<leftarrow> array_length p;
    if l < m then push_array_basic x p
    else do {
      u \<leftarrow> double_length p;
      push_array_basic x u
    }
  }"

definition pop_array :: "'a::heap dynamic_array \<Rightarrow> ('a \<times> 'a dynamic_array) Heap" where
  "pop_array d = do {
    x \<leftarrow> Array.nth (aref d) (alen d - 1);
    return (x, Dyn_Array (alen d - 1) (aref d))
   }"

lemma pop_array_rule' [hoare_triple]:
  "n > 0 \<Longrightarrow> n \<le> length xs \<Longrightarrow>
   <dyn_array_raw (xs, n) p>
   pop_array p
   <\<lambda>(x, r). dyn_array_raw (xs, n - 1) r * \<up>(x = xs ! (n - 1))>" by auto2

setup \<open>del_prfstep_thm @{thm dyn_array_raw.simps}\<close>
setup \<open>del_simple_datatype "dynamic_array"\<close>

fun push_array_fun :: "'a \<Rightarrow> 'a::heap list \<times> nat \<Rightarrow> 'a list \<times> nat" where
  "push_array_fun x (xs, n) = (
     if n < length xs then push_array_basic_fun x (xs, n)
     else push_array_basic_fun x (double_length_fun (xs, n)))"
setup \<open>add_rewrite_rule @{thm push_array_fun.simps}\<close>

lemma push_array_rule' [hoare_triple]:
  "n \<le> length xs \<Longrightarrow>
   <dyn_array_raw (xs, n) p>
   push_array x p
   <dyn_array_raw (push_array_fun x (xs, n))>\<^sub>t" by auto2

subsection \<open>Abstract assertion\<close>

fun abs_array :: "'a::heap list \<times> nat \<Rightarrow> 'a list" where
  "abs_array (xs, n) = take n xs"
setup \<open>add_rewrite_rule @{thm abs_array.simps}\<close>

lemma double_length_abs [rewrite]:
  "length xs = n \<Longrightarrow> abs_array (double_length_fun (xs, n)) = abs_array (xs, n)" by auto2

lemma push_array_basic_abs [rewrite]:
  "n < length xs \<Longrightarrow> abs_array (push_array_basic_fun x (xs, n)) = abs_array (xs, n) @ [x]"
@proof @have "length (take n xs @ [x]) = n + 1" @qed

lemma push_array_fun_abs [rewrite]:
  "n \<le> length xs \<Longrightarrow> abs_array (push_array_fun x (xs, n)) = abs_array (xs, n) @ [x]" by auto2

definition dyn_array :: "'a::heap list \<Rightarrow> 'a dynamic_array \<Rightarrow> assn" where [rewrite_ent]:
  "dyn_array xs a = (\<exists>\<^sub>Ap. dyn_array_raw p a * \<up>(xs = abs_array p) * \<up>(snd p \<le> length (fst p)))"

lemma dyn_array_new_rule [hoare_triple]:
  "<emp> dyn_array_new <dyn_array []>" by auto2

lemma array_length_rule [hoare_triple]:
  "<dyn_array xs p>
   array_length p
   <\<lambda>r. dyn_array xs p * \<up>(r = length xs)>" by auto2

lemma array_nth_rule [hoare_triple]:
  "i < length xs \<Longrightarrow>
   <dyn_array xs p>
    array_nth p i
   <\<lambda>r. dyn_array xs p * \<up>(r = xs ! i)>" by auto2

lemma array_upd_rule [hoare_triple]:
  "i < length xs \<Longrightarrow>
   <dyn_array xs p>
    array_upd i x p
   <\<lambda>_. dyn_array (list_update xs i x) p>" by auto2

lemma push_array_rule [hoare_triple]:
  "<dyn_array xs p>
    push_array x p
   <dyn_array (xs @ [x])>\<^sub>t" by auto2

lemma pop_array_rule [hoare_triple]:
  "xs \<noteq> [] \<Longrightarrow>
   <dyn_array xs p>
   pop_array p
   <\<lambda>(x, r). dyn_array (butlast xs) r * \<up>(x = last xs)>"
@proof @have "last xs = xs ! (length xs - 1)" @qed

setup \<open>del_prfstep_thm @{thm dyn_array_def}\<close>

subsection \<open>Derived operations\<close>

definition array_swap :: "'a::heap dynamic_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_swap d i j = do {
    x \<leftarrow> array_nth d i;
    y \<leftarrow> array_nth d j;
    array_upd i y d;
    array_upd j x d;
    return ()
   }"

lemma array_swap_rule [hoare_triple]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
   <dyn_array xs p>
   array_swap p i j
   <\<lambda>_. dyn_array (list_swap xs i j) p>" by auto2

end
