(* Author: Tobias Nipkow, based on work by Daniel Somogyi *)

section \<open>Optimal BSTs: The `Cubic' Algorithm\label{sec:cubic}\<close>

theory Optimal_BST
imports Weighted_Path_Length
begin

subsection \<open>Function \<open>argmin\<close>\<close>

text \<open>Function \<open>argmin\<close> iterates over a list and returns the rightmost element
that minimizes a given function:\<close>

fun argmin :: "('a \<Rightarrow> ('b::linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"argmin f (x#xs) =
  (if xs = [] then x else
   let m = argmin f xs in if f x < f m then x else m)"

text \<open>An optimized version that avoids repeated computation of \<open>f x\<close>:\<close>

fun argmin2 :: "('a \<Rightarrow> ('b::linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a * 'b" where
"argmin2 f (x#xs) =
  (let fx = f x
   in if xs = [] then (x, fx)
      else let mfm = argmin2 f xs
           in if fx < snd mfm then (x,fx) else mfm)"

lemma argmin2_argmin: "xs \<noteq> [] \<Longrightarrow> argmin2 f xs = (argmin f xs, f(argmin f xs))"
by (induction xs) (auto simp: Let_def)

lemma argmin_argmin2[code]: "argmin f xs = (if xs = [] then undefined else fst(argmin2 f xs))"
apply(auto simp: argmin2_argmin)
apply (meson argmin.elims list.distinct(1))
done


lemma argmin_forall: "xs \<noteq> [] \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> P x) \<Longrightarrow> P (argmin f xs)"
by(induction xs) (auto simp: Let_def)

lemma argmin_in: "xs \<noteq> [] \<Longrightarrow> argmin f xs \<in> set xs"
using argmin_forall[of xs "\<lambda>x. x\<in>set xs"] by blast

lemma argmin_Min: "xs \<noteq> [] \<Longrightarrow> f (argmin f xs) = Min (f ` set xs)"
by(induction xs) (auto simp: min_def intro!: antisym)

lemma argmin_pairs: "xs \<noteq> [] \<Longrightarrow>
  (argmin f xs,f (argmin f xs)) = argmin snd (map (\<lambda>x. (x,f x)) xs)"
by (induction f xs rule:argmin.induct) (auto, smt snd_conv)

lemma argmin_map: "xs \<noteq> [] \<Longrightarrow> argmin c (map f xs) = f(argmin (c o f) xs)"
by(induction xs) (simp_all add: Let_def)


subsection \<open>The `Cubic' Algorithm\<close>

text \<open>We hide the details of the access frequencies \<open>a\<close> and \<open>b\<close> by working with an abstract
version of function \<open>w\<close> definied above (summing \<open>a\<close> and \<open>b\<close>). Later we interpret \<open>w\<close> accordingly.\<close>

locale Optimal_BST =
fixes w :: "int \<Rightarrow> int \<Rightarrow> nat"
begin

subsubsection \<open>Functions \<open>wpl\<close> and \<open>min_wpl\<close>\<close>

sublocale wpl where w = w .

text \<open>Function \<open>min_wpl i j\<close> computes the minimal weighted path length of any tree \<open>t\<close>
where @{prop"inorder t = [i..j]"}. It simply tries all possible indices between \<open>i\<close> and \<open>j\<close>
as the root. Thus it implicitly constructs all possible trees.\<close>

declare conj_cong [fundef_cong]
function min_wpl :: "int \<Rightarrow> int \<Rightarrow> nat" where
"min_wpl i j =
  (if i > j then 0
   else Min ((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j) ` {i..j}) + w i j)"
by auto
termination by (relation "measure (\<lambda>(i,j). nat(j-i+1))") auto
declare min_wpl.simps[simp del]

text \<open>Note that for efficiency reasons we have pulled \<open>+ w i j\<close> out of \<open>Min\<close>.
In the lemma below this is reversed because it simplifies the proofs.
Similar optimizations are possible in other functions below.\<close>

lemma min_wpl_simps[simp]:
  "i > j \<Longrightarrow> min_wpl i j = 0"
  "i \<le> j \<Longrightarrow> min_wpl i j =
     Min ((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + w i j) ` {i..j})"
by(auto simp add: min_wpl.simps[of i j] Min_add_commute)

lemma upto_split1: 
  "\<lbrakk> i \<le> j;  j \<le> k \<rbrakk> \<Longrightarrow> [i..k] = [i..j-1] @ [j..k]"
proof (induction j rule: int_ge_induct)
  case base thus ?case by (simp add: upto_rec1)
next
  case step thus ?case using upto_rec1 upto_rec2 by simp
qed

text\<open>Function @{const min_wpl} returns a lower bound for all possible BSTs:\<close>

theorem min_wpl_is_optimal:
  "inorder t = [i..j] \<Longrightarrow> min_wpl i j \<le> wpl i j t"
proof(induction i j t rule: wpl.induct)
  case 1
  thus ?case by(simp add: upto.simps split: if_splits)
next
  case (2 i j l k r)
  then show ?case 
  proof cases
    assume "i > j" thus ?thesis by(simp)
  next
    assume [arith]: "\<not> i > j"

    note inorder = inorder_upto_split[OF "2.prems"]
        
    let ?M = "(\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + w i j) ` {i..j}"
    let ?w = "min_wpl i (k-1) + min_wpl (k+1) j + w i j"
 
    have aux_min:"Min ?M \<le> ?w"
    proof (rule Min_le)
      show "finite ?M" by simp
      show "?w \<in> ?M" using inorder(3,4) by simp
    qed

    have "min_wpl i j = Min ?M" by(simp)
    also have "... \<le> ?w" by (rule aux_min)    
    also have "... \<le> wpl i (k-1) l + wpl (k+1) j r + w i j"
      using inorder(1,2) "2.IH" by simp
    also have "... = wpl i j \<langle>l,k,r\<rangle>" by simp
    finally show ?thesis .
  qed
qed

text \<open>Now we show that the lower bound computed by @{const min_wpl}
is the wpl of an optimal tree that can be computed in the same manner.\<close>

subsubsection \<open>Function \<open>opt_bst\<close>\<close>

text\<open>This is the functional equivalent of the standard cubic imperative algorithm.
Unless it is memoized, the complexity is again exponential.
The pattern of recursion is the same as for @{const min_wpl} but instead of the minimal weight
it computes a tree with the minimal weight:\<close>

function opt_bst :: "int \<Rightarrow> int \<Rightarrow> int tree" where
"opt_bst i j =
  (if i > j then Leaf
   else argmin (wpl i j) [\<langle>opt_bst i (k-1), k, opt_bst (k+1) j\<rangle>. k \<leftarrow> [i..j]])"
by auto
termination by (relation "measure (\<lambda>(i,j) . nat(j-i+1))") auto
declare opt_bst.simps[simp del]

corollary opt_bst_simps[simp]:
  "i > j \<Longrightarrow> opt_bst i j = Leaf"
  "i \<le> j \<Longrightarrow> opt_bst i j =
     (argmin (wpl i j) [\<langle>opt_bst i (k-1), k, opt_bst (k+1) j\<rangle>. k \<leftarrow> [i..j]])"
by(auto simp add: opt_bst.simps[of i j])

text \<open>As promised, @{const opt_bst} computes a tree with the minimal wpl:\<close>

theorem wpl_opt_bst: "wpl i j (opt_bst i j) = min_wpl i j"
proof(induction i j rule: min_wpl.induct)
  case (1 i j)
  show ?case
  proof cases
    assume "i > j" 
    thus ?thesis by(simp)
  next
    assume [arith]: "\<not> i > j"
    let ?ts = "[\<langle>opt_bst i (k-1), k, opt_bst (k+1) j\<rangle>. k \<leftarrow> [i..j]]"
    let ?M = "((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + w i j) ` {i..j})"
    have 1: "?ts \<noteq> []" by (auto simp add: upto.simps)
    have "wpl i j (opt_bst i j) = wpl i j (argmin (wpl i j) ?ts)" by simp
    also have "\<dots> = Min (wpl i j ` (set ?ts))"
      by(rule argmin_Min[OF 1])
    also have "\<dots> = Min ?M"
    proof (rule arg_cong[where f=Min])
      show "wpl i j ` (set ?ts) = ?M" using "1.IH"
        by (force simp: Bex_def image_iff "1.IH")
    qed
    also have "\<dots> = min_wpl i j" by simp
    finally show ?thesis .
  qed
qed

corollary opt_bst_is_optimal:
  "inorder t = [i..j] \<Longrightarrow> wpl i j (opt_bst i j) \<le> wpl i j t"
by (simp add: min_wpl_is_optimal wpl_opt_bst)

subsubsection \<open>Function \<open>opt_bst_wpl\<close>\<close>

text \<open>Function @{const opt_bst} is simplistic because it computes the wpl
of each tree anew rather than returning it with the tree. That is what \<open>opt_bst_wpl\<close> does:\<close>

function opt_bst_wpl :: "int \<Rightarrow> int \<Rightarrow> int tree \<times> nat" where
"opt_bst_wpl i j = 
  (if i > j then (Leaf, 0)
   else argmin snd [let (t1,c1) = opt_bst_wpl i (k-1);
                        (t2,c2) = opt_bst_wpl (k+1) j
                     in (\<langle>t1,k,t2\<rangle>, c1 + c2 + w i j). k \<leftarrow> [i..j]])"
by auto
termination
  by (relation "measure (\<lambda>(i,j). nat(j-i+1))")(auto)
declare opt_bst_wpl.simps[simp del]

text\<open>Function @{const opt_bst_wpl} returns an optimal tree and its wpl:\<close>

lemma opt_bst_wpl_eq_pair:
  "opt_bst_wpl i j = (opt_bst i j, wpl i j (opt_bst i j))"
proof(induction i j rule: opt_bst_wpl.induct)
  case (1 i j)
  note [simp] = opt_bst_wpl.simps[of i j]
  show ?case 
  proof cases
    assume "i > j" thus ?thesis using "1.prems" by auto
  next
    assume "\<not> i > j"
    thus ?thesis by (simp add: argmin_pairs comp_def "1.IH" cong: list.map_cong_simp)
  qed
qed

corollary opt_bst_wpl_eq_pair': "opt_bst_wpl i j = (opt_bst i j, min_wpl i j)"
by (simp add: opt_bst_wpl_eq_pair wpl_opt_bst)

end (* locale Optimal_BST *)

end
