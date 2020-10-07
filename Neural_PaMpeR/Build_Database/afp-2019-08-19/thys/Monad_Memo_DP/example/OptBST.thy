subsection \<open>Optimal Binary Search Trees\<close>

theory OptBST
imports
  "HOL-Library.Tree"
  "HOL-Library.Code_Target_Numeral"
  "../state_monad/State_Main" 
  "../heap_monad/Heap_Default"
  Example_Misc
begin

subsubsection \<open>Misc\<close>

(* FIXME mv List *)
lemma induct_list012:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. P (y # zs) \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
by induction_schema (pat_completeness, lexicographic_order)

lemma upto_split1: 
  "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i..k] = [i..j-1] @ [j..k]"
proof (induction j rule: int_ge_induct)
  case base thus ?case by (simp add: upto_rec1)
next
  case step thus ?case using upto_rec1 upto_rec2 by simp
qed

lemma upto_split2: 
  "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i..k] = [i..j] @ [j+1..k]"
using upto_rec1 upto_rec2 upto_split1 by auto

lemma upto_Nil: "[i..j] = [] \<longleftrightarrow> j < i"
by (simp add: upto.simps)

lemma upto_Nil2: "[] = [i..j] \<longleftrightarrow> j < i"
by (simp add: upto.simps)

lemma upto_join3: "\<lbrakk> i \<le> j; j \<le> k \<rbrakk> \<Longrightarrow> [i..j-1] @ j # [j+1..k] = [i..k]"
using upto_rec1 upto_split1 by auto

fun arg_min_list :: "('a \<Rightarrow> ('b::linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"arg_min_list f [x] = x" |
"arg_min_list f (x#y#zs) = (let m = arg_min_list f (y#zs) in if f x \<le> f m then x else m)"

lemma f_arg_min_list_f: "xs \<noteq> [] \<Longrightarrow> f (arg_min_list f xs) = Min (f ` (set xs))"
by(induction f xs rule: arg_min_list.induct) (auto simp: min_def intro!: antisym)
(* end mv *)


subsubsection \<open>Definitions\<close>

context
fixes W :: "int \<Rightarrow> int \<Rightarrow> nat"
begin

fun wpl :: "int \<Rightarrow> int \<Rightarrow> int tree \<Rightarrow> nat" where
   "wpl i j Leaf = 0"
 | "wpl i j (Node l k r) = wpl i (k-1) l + wpl (k+1) j r + W i j"

function min_wpl :: "int \<Rightarrow> int \<Rightarrow> nat" where
"min_wpl i j =
  (if i > j then 0
   else min_list (map (\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) [i..j]))"
by auto
termination by (relation "measure (\<lambda>(i,j) . nat(j-i+1))") auto
declare min_wpl.simps[simp del]

function opt_bst :: "int * int \<Rightarrow> int tree" where
"opt_bst (i,j) =
  (if i > j then Leaf else arg_min_list (wpl i j) [\<langle>opt_bst (i,k-1), k, opt_bst (k+1,j)\<rangle>. k \<leftarrow> [i..j]])"
by auto
termination by (relation "measure (\<lambda>(i,j) . nat(j-i+1))") auto
declare opt_bst.simps[simp del]


subsubsection \<open>Functional Memoization\<close>

context
  fixes n :: nat
begin

context fixes
  mem :: "nat option array"
begin

memoize_fun min_wpl\<^sub>T: min_wpl
  with_memory dp_consistency_heap_default where bound = "Bound (0, 0) (int n, int n)" and mem="mem"
  monadifies (heap) min_wpl.simps

context includes heap_monad_syntax begin
thm min_wpl\<^sub>T'.simps min_wpl\<^sub>T_def
end

memoize_correct
  by memoize_prover

lemmas memoized_empty = min_wpl\<^sub>T.memoized_empty

end (* Fixed array *)

context
  includes heap_monad_syntax
  notes [simp del] = min_wpl\<^sub>T'.simps
begin

definition "min_wpl\<^sub>h \<equiv> \<lambda> i j. Heap_Monad.bind (mem_empty (n * n)) (\<lambda> mem. min_wpl\<^sub>T' mem i j)"

lemma min_wpl_heap:
  "min_wpl i j = result_of (min_wpl\<^sub>h i j) Heap.empty"
  unfolding min_wpl\<^sub>h_def
  using memoized_empty[of _ "\<lambda> m. \<lambda> (a, b). min_wpl\<^sub>T' m a b" "(i, j)", OF min_wpl\<^sub>T.crel]
  by (simp add: index_size_defs)

end

end (* Bound *)

context begin
memoize_fun min_wpl\<^sub>m: min_wpl with_memory dp_consistency_mapping monadifies (state) min_wpl.simps
thm min_wpl\<^sub>m'.simps

memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = min_wpl\<^sub>m.memoized_correct

end


subsubsection \<open>Correctness Proof\<close>

lemma min_wpl_minimal:
  "inorder t = [i..j] \<Longrightarrow> min_wpl i j \<le> wpl i j t"
proof(induction i j t rule: wpl.induct)
  case (1 i j)
  then show ?case by (simp add: min_wpl.simps upto_Nil2)
next
  case (2 i j l k r)
  then show ?case 
  proof cases
    assume "i > j" thus ?thesis by(simp add: min_wpl.simps)
  next
    assume [arith]: "\<not> i > j"
    have kk_ij: "k\<in>set[i..j]" using 2 
        by (metis set_inorder tree.set_intros(2))
        
    let ?M = "((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) ` {i..j})"
    let ?w = "min_wpl i (k-1) + min_wpl (k+1) j + W i j"
 
    have aux_min:"Min ?M \<le> ?w"
    proof (rule Min_le)
      show "finite ?M" by simp
      show "?w \<in> ?M" using kk_ij by auto
    qed

    have"inorder \<langle>l,k,r\<rangle> = inorder l @k#inorder r" by auto
    from this have C:"[i..j] = inorder l @ k#inorder r" using 2 by auto
    have D: "[i..j] = [i..k-1]@k#[k+1..j]" using kk_ij upto_rec1 upto_split1
      by (metis atLeastAtMost_iff set_upto) 

    have l_inorder: "inorder l = [i..k-1]"
      by (smt C D append_Cons_eq_iff atLeastAtMost_iff set_upto)
    have r_inorder: "inorder r = [k+1..j]" 
      by (smt C D append_Cons_eq_iff atLeastAtMost_iff set_upto)

    have "min_wpl i j = Min ?M" by (simp add: min_wpl.simps min_list_Min upto_Nil)
    also have "... \<le> ?w" by (rule aux_min)    
    also have "... \<le> wpl i (k-1) l + wpl (k+1) j r + W i j" using l_inorder r_inorder "2.IH" by simp
    also have "... = wpl i j \<langle>l,k,r\<rangle>" by simp
    finally show ?thesis .
  qed
qed

lemma P_arg_min_list: "(\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> P(arg_min_list f xs)"
by(induction f xs rule: arg_min_list.induct) (auto simp: Let_def)

lemma opt_bst_correct: "inorder (opt_bst (i,j)) = [i..j]"
apply(induction "(i,j)" arbitrary: i j rule: opt_bst.induct)
by (force simp: opt_bst.simps upto_Nil upto_join3 intro: P_arg_min_list)

lemma wpl_opt_bst: "wpl i j (opt_bst (i,j)) = min_wpl i j"
proof(induction i j rule: min_wpl.induct)
  case (1 i j)
  show ?case
  proof cases
    assume "i > j" thus ?thesis by(simp add: min_wpl.simps opt_bst.simps)
  next
    assume *[arith]: "\<not> i > j"
    let ?ts = "[\<langle>opt_bst (i,k-1), k, opt_bst (k+1,j)\<rangle>. k <- [i..j]]"
    let ?M = "((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) ` {i..j})"
    have "?ts \<noteq> []" by (auto simp add: upto.simps)
    have "wpl i j (opt_bst (i,j)) = wpl i j (arg_min_list (wpl i j) ?ts)" by (simp add: opt_bst.simps)
    also have "\<dots> = Min (wpl i j ` (set ?ts))" by(rule f_arg_min_list_f[OF \<open>?ts \<noteq> []\<close>])
    also have "\<dots> = Min ?M"
    proof (rule arg_cong[where f=Min])
      show "wpl i j ` (set ?ts) = ?M"
        by (fastforce simp: Bex_def image_iff 1[OF *])
    qed
    also have "\<dots> = min_wpl i j" by (simp add: min_wpl.simps min_list_Min upto_Nil)
    finally show ?thesis .
  qed
qed

lemma opt_bst_is_optimal:
  "inorder t = [i..j] \<Longrightarrow> wpl i j (opt_bst (i,j)) \<le> wpl i j t"
by (simp add: min_wpl_minimal wpl_opt_bst)

end

subsubsection \<open>Test Case\<close>

code_thms min_wpl

definition "min_wpl_test = min_wpl\<^sub>h (\<lambda>i j. nat(i+j)) 2 3 3"

code_reflect Test functions min_wpl_test

ML \<open>Test.min_wpl_test ()\<close>

end
