(* Author: Tobias Nipkow (based on Hauke Brinkop's tree proofs) *)

subsection \<open>Okasaki's Pairing Heap\<close>

theory Pairing_Heap_List1_Analysis
imports
  Pairing_Heap.Pairing_Heap_List1
  Amortized_Framework
  Priority_Queue_ops_merge
  Lemmas_log
begin

text
\<open>Amortized analysis of pairing heaps as defined by Okasaki \cite{Okasaki}.\<close>

fun hps where
"hps (Hp _ hs) = hs"

lemma merge_Empty[simp]: "merge heap.Empty h = h"
by(cases h) auto

lemma merge2: "merge (Hp x lx) h = (case h of heap.Empty \<Rightarrow> Hp x lx | (Hp y ly) \<Rightarrow> 
    (if x < y then Hp x (Hp y ly # lx) else Hp y (Hp x lx # ly)))"
by(auto split: heap.split)

lemma pass1_Nil_iff: "pass\<^sub>1 hs = [] \<longleftrightarrow> hs = []"
by(cases hs rule: pass\<^sub>1.cases) auto


subsubsection \<open>Invariant\<close>

fun no_Empty :: "'a :: linorder heap \<Rightarrow> bool" where
"no_Empty heap.Empty = False" |
"no_Empty (Hp x hs) = (\<forall>h \<in> set hs. no_Empty h)"

abbreviation no_Emptys :: "'a :: linorder heap list \<Rightarrow> bool" where
"no_Emptys hs \<equiv> \<forall>h \<in> set hs. no_Empty h"

fun is_root :: "'a :: linorder heap \<Rightarrow> bool" where
"is_root heap.Empty = True" |
"is_root (Hp x hs) = no_Emptys hs"


lemma is_root_if_no_Empty: "no_Empty h \<Longrightarrow> is_root h"
by(cases h) auto

lemma no_Emptys_hps: "no_Empty h \<Longrightarrow> no_Emptys(hps h)"
by(induction h) auto

lemma no_Empty_merge: "\<lbrakk> no_Empty h1; no_Empty h2\<rbrakk> \<Longrightarrow> no_Empty (merge h1 h2)"
by (cases "(h1,h2)" rule: merge.cases) auto

lemma is_root_merge: "\<lbrakk> is_root h1; is_root h2\<rbrakk> \<Longrightarrow> is_root (merge h1 h2)"
by (cases "(h1,h2)" rule: merge.cases) auto

lemma no_Emptys_pass1:
  "no_Emptys hs \<Longrightarrow> no_Emptys (pass\<^sub>1 hs)"
by(induction hs rule: pass\<^sub>1.induct)(auto simp: no_Empty_merge)

lemma is_root_pass2: "no_Emptys hs \<Longrightarrow> is_root(pass\<^sub>2 hs)"
proof(induction hs)
  case (Cons _ hs)
  show ?case
  proof cases
    assume "hs = []" thus ?thesis using Cons by (auto simp: is_root_if_no_Empty)
  next
    assume "hs \<noteq> []" thus ?thesis using Cons by(auto simp: is_root_merge is_root_if_no_Empty)
  qed
qed simp


subsubsection \<open>Complexity\<close>

fun size_hp :: "'a heap \<Rightarrow> nat" where
"size_hp heap.Empty = 0" |
"size_hp (Hp x hs) = sum_list(map size_hp hs) + 1"

abbreviation size_hps where
"size_hps hs \<equiv> sum_list(map size_hp hs)"

fun \<Phi>_hps :: "'a heap list \<Rightarrow> real" where
"\<Phi>_hps [] = 0" |
"\<Phi>_hps (heap.Empty # hs) = \<Phi>_hps hs" |
"\<Phi>_hps (Hp x hsl # hsr) =
 \<Phi>_hps hsl + \<Phi>_hps hsr + log 2 (size_hps hsl + size_hps hsr + 1)"

fun \<Phi> :: "'a heap \<Rightarrow> real" where
"\<Phi> heap.Empty = 0" |
"\<Phi> (Hp _ hs) = \<Phi>_hps hs + log 2 (size_hps(hs)+1)"

lemma \<Phi>_hps_ge0: "\<Phi>_hps hs \<ge> 0"
by (induction hs rule: \<Phi>_hps.induct) auto

lemma no_Empty_ge0: "no_Empty h \<Longrightarrow> size_hp h > 0"
by(cases h) auto

declare algebra_simps[simp]

lemma \<Phi>_hps1: "\<Phi>_hps [h] = \<Phi> h"
by(cases h) auto

lemma size_hp_merge: "size_hp(merge h1 h2) = size_hp h1 + size_hp h2" 
by (induction h1 h2 rule: merge.induct) simp_all

lemma pass\<^sub>1_size[simp]: "size_hps (pass\<^sub>1 hs) = size_hps hs" 
by (induct hs rule: pass\<^sub>1.induct) (simp_all add: size_hp_merge)

lemma \<Delta>\<Phi>_insert:
  "\<Phi> (Pairing_Heap_List1.insert x h) - \<Phi> h \<le> log 2 (size_hp h + 1)"
by(cases h)(auto simp: size_hp_merge)

lemma \<Delta>\<Phi>_merge:
  "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2
  \<le> log 2 (size_hp h1 + size_hp h2 + 1) + 1"
proof(induction h1 h2 rule: merge.induct)
  case (3 x lx y ly)
  thus ?case
    using ld_le_2ld[of "size_hps lx" "size_hps ly"]
      log_le_cancel_iff[of 2 "size_hps lx + size_hps ly + 2" "size_hps lx + size_hps ly + 3"]
    by (auto simp del: log_le_cancel_iff)
qed auto

fun sum_ub :: "'a heap list \<Rightarrow> real" where
  "sum_ub [] = 0"
| "sum_ub [_] = 0"
| "sum_ub [h1, h2] = 2*log 2 (size_hp h1 + size_hp h2)" 
| "sum_ub (h1 # h2 # hs) = 2*log 2 (size_hp h1 + size_hp h2 + size_hps hs) 
    - 2*log 2 (size_hps hs) - 2 + sum_ub hs"

lemma \<Delta>\<Phi>_pass1_sum_ub: "no_Emptys hs \<Longrightarrow>
  \<Phi>_hps (pass\<^sub>1 hs) - \<Phi>_hps hs  \<le> sum_ub hs" (is "_ \<Longrightarrow> ?P hs")
proof (induction hs rule: sum_ub.induct)
  case (3 h1 h2)
  then obtain x hsx y hsy where [simp]: "h1 = Hp x hsx" "h2 = Hp y hsy"
    by simp (meson no_Empty.elims(2))
  have 0: "\<And>x y::real. 0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> x \<le> 2*y" by linarith
  show ?case using 3 by (auto simp add: add_increasing 0)
next
  case (4 h1 h2 h3 hs)
  hence IH: "?P(h3#hs)" by auto
  from "4.prems" obtain x hsx y hsy where [simp]: "h1 = Hp x hsx" "h2 = Hp y hsy"
    by simp (meson no_Empty.elims(2))
  from "4.prems" have s3: "size_hp h3 > 0"
    apply auto using size_hp.elims by force
  let ?ry = "h3 # hs"
  let ?rx = "Hp y hsy # ?ry"
  let ?h = "Hp x hsx # ?rx"
  have "\<Phi>_hps(pass\<^sub>1 ?h) - \<Phi>_hps ?h  
    \<le> log 2 (1 + size_hps hsx + size_hps hsy) - log 2 (1 + size_hps hsy + size_hps ?ry) + sum_ub ?ry"
    using IH by simp
  also have "log 2 (1 + size_hps hsx + size_hps hsy) - log 2 (1 + size_hps hsy + size_hps ?ry) 
    \<le> 2*log 2 (size_hps ?h) - 2*log 2 (size_hps ?ry) - 2"
  proof -
    have "log 2 (1 + size_hps hsx + size_hps hsy) + log 2 (size_hps ?ry) - 2*log 2 (size_hps ?h) 
      = log 2 ((1 + size_hps hsx + size_hps hsy)/(size_hps ?h) ) + log 2 (size_hps ?ry / size_hps ?h)"
      using s3 by (simp add: log_divide)
    also have "\<dots> \<le> -2" 
    proof -
      have "2 + \<dots>
        \<le> 2*log 2 ((1 + size_hps hsx + size_hps hsy) / size_hps ?h +  size_hps ?ry / size_hps ?h)"  
        using ld_sum_inequality [of "(1 + size_hps hsx + size_hps hsy) / size_hps ?h" "(size_hps ?ry / size_hps ?h)"] using s3 by simp
      also have "\<dots> \<le> 0" by (simp add: field_simps log_divide add_pos_nonneg)
      finally show ?thesis by linarith
    qed 
    finally have "log 2 (1 + size_hps hsx + size_hps hsy) + log 2 (size_hps ?ry) + 2
      \<le>  2*log 2 (size_hps ?h)" by simp
    moreover have "log 2 (size_hps ?ry) \<le> log 2 (size_hps ?rx)" using s3 by simp
    ultimately have "log 2 (1 + size_hps hsx + size_hps hsy) - \<dots> 
      \<le>  2*log 2 (size_hps ?h) - 2*log 2 (size_hps ?ry) - 2" by linarith
    thus ?thesis by simp
  qed
  finally show ?case by (simp)
qed simp_all

lemma \<Delta>\<Phi>_pass1: assumes "hs \<noteq> []" "no_Emptys hs"
  shows "\<Phi>_hps (pass\<^sub>1 hs) - \<Phi>_hps hs \<le> 2 * log 2 (size_hps hs) - length hs + 2"
proof - 
  have "sum_ub hs \<le> 2 * log 2 (size_hps hs) - length hs + 2" 
    using assms by (induct hs rule: sum_ub.induct) (auto dest: no_Empty_ge0)
  thus ?thesis using \<Delta>\<Phi>_pass1_sum_ub[OF assms(2)] by linarith
qed

lemma size_hps_pass2: "hs \<noteq> [] \<Longrightarrow> no_Emptys hs \<Longrightarrow>
  no_Empty(pass\<^sub>2 hs) & size_hps hs = size_hps(hps(pass\<^sub>2 hs))+1"
apply(induction hs rule: \<Phi>_hps.induct)
  apply (fastforce simp: merge2 split: heap.split)+
done

lemma \<Delta>\<Phi>_pass2: "hs \<noteq> [] \<Longrightarrow> no_Emptys hs \<Longrightarrow>
  \<Phi> (pass\<^sub>2 hs) - \<Phi>_hps hs \<le> log 2 (size_hps hs)"
proof (induction hs)
  case (Cons h hs)
  thus ?case
  proof cases
    assume "hs = []"
    thus ?thesis using Cons by (auto simp add: \<Phi>_hps1 dest: no_Empty_ge0)
  next
    assume *: "hs \<noteq> []"
    obtain x hs2 where [simp]: "h = Hp x hs2"
      using Cons.prems(2)by simp (meson no_Empty.elims(2))
    show ?thesis
    proof (cases "pass\<^sub>2 hs")
      case Empty thus ?thesis using \<Phi>_hps_ge0[of hs]
        by(simp add: add_increasing xt1(3)[OF mult_2, OF add_increasing])
    next
      case (Hp y hs3)
      with Cons * size_hps_pass2[of hs] show ?thesis by(auto simp: add_mono)
    qed
  qed
qed simp

lemma \<Delta>\<Phi>_del_min: assumes "hps h \<noteq> []" "no_Empty h"
  shows "\<Phi> (del_min h) - \<Phi> h 
  \<le> 3 * log 2 (size_hps(hps h)) - length(hps h) + 2"
proof -
  obtain x hs where [simp]: "h = Hp x hs" using assms(2) by (cases h) auto
  let ?\<Delta>\<Phi>\<^sub>1 = "\<Phi>_hps(hps h) - \<Phi> h" 
  let ?\<Delta>\<Phi>\<^sub>2 = "\<Phi>(pass\<^sub>2(pass\<^sub>1 (hps h))) - \<Phi>_hps (hps h)"
  let ?\<Delta>\<Phi> = "\<Phi> (del_min h) - \<Phi> h"
  have "\<Phi>(pass\<^sub>2(pass\<^sub>1(hps h))) - \<Phi>_hps (pass\<^sub>1(hps h)) \<le> log 2 (size_hps(hps h))" 
    using \<Delta>\<Phi>_pass2[of "pass\<^sub>1(hps h)"] using assms
    by (auto simp: pass1_Nil_iff no_Emptys_pass1 dest: no_Emptys_hps)
  moreover have "\<Phi>_hps (pass\<^sub>1 (hps h)) - \<Phi>_hps (hps h) \<le>  2*\<dots> - length (hps h) + 2"
    using \<Delta>\<Phi>_pass1[OF assms(1) no_Emptys_hps[OF assms(2)]] by blast
  moreover have "?\<Delta>\<Phi>\<^sub>1 \<le> 0" by simp
  moreover have "?\<Delta>\<Phi> = ?\<Delta>\<Phi>\<^sub>1 + ?\<Delta>\<Phi>\<^sub>2" by simp
  ultimately show ?thesis by linarith
qed


fun exec :: "'a :: linorder op \<Rightarrow> 'a heap list \<Rightarrow> 'a heap" where
"exec Empty [] = heap.Empty" | 
"exec Del_min [h] = del_min h" |
"exec (Insert x) [h] = Pairing_Heap_List1.insert x h" |
"exec Merge [h1,h2] = merge h1 h2"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 :: "'a heap list \<Rightarrow> nat" where
  "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 [] = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 [_] = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 (_ # _ # hs) = 1 + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 hs"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 :: "'a heap list \<Rightarrow> nat" where
 "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 [] = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (_ # hs) = 1 + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 hs"

fun cost :: "'a :: linorder op \<Rightarrow> 'a heap list \<Rightarrow> nat" where
"cost Empty _ = 1" |
"cost Del_min [heap.Empty] = 1" |
"cost Del_min [Hp x hs] = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 hs) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 hs" |
"cost (Insert a) _ = 1" |
"cost Merge _ = 1"

fun U :: "'a :: linorder op \<Rightarrow> 'a heap list \<Rightarrow> real" where
"U Empty _ = 1" |
"U (Insert a) [h] = log 2 (size_hp h + 1) + 1" |
"U Del_min [h] = 3*log 2 (size_hp h + 1) + 4" |
"U Merge [h1,h2] = log 2 (size_hp h1 + size_hp h2 + 1) + 2"

interpretation pairing: Amortized
where arity = arity and exec = exec and cost = cost and inv = "is_root"
and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case (1 ss f) show ?case
  proof (cases f)
    case Empty with 1 show ?thesis by simp
  next
    case Insert thus ?thesis using 1 by(auto simp: is_root_merge)
  next
    case Merge
    thus ?thesis using 1 by(auto simp: is_root_merge numeral_eq_Suc)
  next
    case [simp]: Del_min
    then obtain h where [simp]: "ss = [h]" using 1 by auto
    show ?thesis
    proof (cases h)
      case [simp]: (Hp _ hs)
      show ?thesis
      proof cases
        assume "hs = []" thus ?thesis by simp
      next
        assume "hs \<noteq> []" thus ?thesis
          using 1(1) no_Emptys_pass1 by (auto intro: is_root_pass2)
      qed
    qed simp
  qed
next
  case (2 s) show ?case by (cases s) (auto simp: \<Phi>_hps_ge0)
next
  case (3 ss f) show ?case
  proof (cases f)
    case Empty with 3 show ?thesis by(auto)
  next
    case Insert thus ?thesis using \<Delta>\<Phi>_insert 3 by auto
  next
    case [simp]: Del_min
    then obtain h where [simp]: "ss = [h]" using 3 by auto
    show ?thesis
    proof (cases h)
      case [simp]: (Hp x hs)
      have "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 hs) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 hs \<le> 2 + length hs"
        by (induct hs rule: pass\<^sub>1.induct) simp_all
      hence  "cost f ss \<le> \<dots>" by simp
      moreover have  "\<Phi> (del_min h) - \<Phi> h \<le> 3*log 2 (size_hp h + 1) - length hs + 2"
      proof (cases "hs = []")
        case False
        hence "\<Phi> (del_min h) - \<Phi> h \<le> 3*log 2 (size_hps hs) - length hs + 2"
          using  \<Delta>\<Phi>_del_min[of h] 3(1) by simp
        also have "\<dots> \<le> 3*log 2 (size_hp h + 1) - length hs + 2"
          using False 3(1) size_hps_pass2 by fastforce
        finally show ?thesis .
      qed simp
      ultimately show ?thesis by simp
    qed simp
  next
    case [simp]: Merge
    then obtain h1 h2 where [simp]: "ss = [h1, h2]"
      using 3 by(auto simp: numeral_eq_Suc)
    show ?thesis
    proof (cases "h1 = heap.Empty \<or> h2 = heap.Empty")
      case True thus ?thesis by auto
    next                  
      case False
      then obtain x1 x2 hs1 hs2 where [simp]: "h1 = Hp x1 hs1" "h2 = Hp x2 hs2"
        by (meson hps.cases) 
      have "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> log 2 (size_hp h1 + size_hp h2 + 1) + 1"
        using \<Delta>\<Phi>_merge[of h1 h2] by simp
      thus ?thesis by(simp)
    qed
  qed
qed

end
