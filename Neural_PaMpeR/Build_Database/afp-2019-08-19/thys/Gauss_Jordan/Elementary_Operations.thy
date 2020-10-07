(*  
    Title:      Elementary_Operations.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Elementary Operations over matrices\<close>

theory Elementary_Operations
imports 
  Rank_Nullity_Theorem.Fundamental_Subspaces
  Code_Matrix
begin

subsection\<open>Some previous results:\<close>

lemma mat_1_fun: "mat 1 $ a $ b = (\<lambda>i j. if i=j then 1 else 0) a b" unfolding mat_def by auto

lemma mat1_sum_eq:
  shows "(\<Sum>k\<in>UNIV. mat (1::'a::{semiring_1}) $ s $ k * mat 1 $ k $ t) = mat 1 $ s $ t"
proof (unfold mat_def, auto)
  let ?f="\<lambda>k. (if t = k then 1::'a else (0::'a)) * (if k = t then 1::'a else (0::'a))"
  have univ_eq: "UNIV = (UNIV - {t}) \<union> {t}" by fast
  have "sum ?f UNIV = sum ?f ((UNIV - {t}) \<union> {t}) " using univ_eq by simp
  also have "... = sum ?f (UNIV - {t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
  also have "... = 0 + sum ?f {t}" by auto
  also have "... = sum ?f {t}" by simp
  also have "... = 1" by simp
  finally show "sum ?f UNIV = 1" .
next
  assume s_not_t: "s \<noteq> t"
  let ?g="\<lambda>k. (if s = k then 1::'a else 0) * (if k = t then 1 else 0)"
  have "sum ?g UNIV = sum (\<lambda>k. 0::'a) (UNIV::'b set)" by (rule sum.cong, auto simp add: s_not_t)
  also have "... = 0" by simp
  finally show "sum ?g UNIV = 0" .
qed


lemma invertible_mat_n:
  fixes n::"'a::{field}"
  assumes n: "n \<noteq> 0"
  shows "invertible ((mat n)::'a^'n^'n)"
proof (unfold invertible_def, rule exI[of _ "mat (inverse n)"], rule conjI)
  show "mat n ** mat (inverse n) = (mat 1::'a^'n^'n)"
  proof (unfold matrix_matrix_mult_def mat_def, vector, auto)
    fix ia::'n
    let ?f="(\<lambda>k. (if ia = k then n else 0) * (if k = ia then inverse n else 0))"
    have UNIV_rw: "(UNIV::'n set) = insert ia (UNIV-{ia})" by auto
    have "(\<Sum>k\<in>(UNIV::'n set). (if ia = k then n else 0) * (if k = ia then inverse n else 0)) = 
      (\<Sum>k\<in>insert ia (UNIV-{ia}). (if ia = k then n else 0) * (if k = ia then inverse n else 0))" using UNIV_rw by simp
    also have "... = ?f ia + sum ?f (UNIV-{ia})"
    proof (rule sum.insert)
      show "finite (UNIV - {ia})"  using finite_UNIV by fastforce
      show "ia \<notin> UNIV - {ia}" by fast
    qed
    also have "... = 1" using right_inverse[OF n] by simp
    finally show " (\<Sum>k\<in>(UNIV::'n set). (if ia = k then n else 0) * (if k = ia then inverse n else 0)) = (1::'a)" .
    fix i::'n
    assume i_not_ia: "i \<noteq> ia"
    show "(\<Sum>k\<in>(UNIV::'n set). (if i = k then n else 0) * (if k = ia then inverse n else 0)) = 0" by (rule sum.neutral, simp add: i_not_ia)
  qed
next
  show "mat (inverse n) ** mat n = ((mat 1)::'a^'n^'n)"
  proof (unfold matrix_matrix_mult_def mat_def, vector, auto)
    fix ia::'n
    let ?f=" (\<lambda>k. (if ia = k then inverse n else 0) * (if k = ia then n else 0))"
    have UNIV_rw: "(UNIV::'n set) = insert ia (UNIV-{ia})" by auto
    have "(\<Sum>k\<in>(UNIV::'n set). (if ia = k then inverse n else 0) * (if k = ia then n else 0)) = 
      (\<Sum>k\<in>insert ia (UNIV-{ia}). (if ia = k then inverse n else 0) * (if k = ia then n else 0))" using UNIV_rw by simp
    also have "... = ?f ia + sum ?f (UNIV-{ia})"
    proof (rule sum.insert)
      show "finite (UNIV - {ia})"  using finite_UNIV by fastforce
      show "ia \<notin> UNIV - {ia}" by fast
    qed
    also have "... = 1" using left_inverse[OF n] by simp
    finally show " (\<Sum>k\<in>(UNIV::'n set). (if ia = k then inverse n else 0) * (if k = ia then n else 0)) = (1::'a)" .
    fix i::'n
    assume i_not_ia: "i \<noteq> ia"
    show "(\<Sum>k\<in>(UNIV::'n set). (if i = k then inverse n else 0) * (if k = ia then n else 0)) = 0" by (rule sum.neutral, simp add: i_not_ia)
  qed
qed

corollary invertible_mat_1:
  shows "invertible (mat (1::'a::{field}))" by (metis invertible_mat_n zero_neq_one)

subsection\<open>Definitions of elementary row and column operations\<close>

text\<open>Definitions of elementary row operations\<close>

definition interchange_rows :: "'a ^'n^'m => 'm => 'm \<Rightarrow> 'a ^'n^'m"
  where "interchange_rows A a b = (\<chi> i j. if i=a then A $ b $ j else if i=b then A $ a $ j else A $ i $ j)"

definition mult_row :: "('a::times) ^'n^'m => 'm => 'a \<Rightarrow> 'a ^'n^'m"
  where "mult_row A a q = (\<chi> i j. if i=a then q*(A $ a $ j) else A $ i $ j)"

definition row_add :: "('a::{plus, times}) ^'n^'m => 'm => 'm \<Rightarrow> 'a \<Rightarrow> 'a ^'n^'m"
  where "row_add A a b q = (\<chi> i j. if i=a then (A $ a $ j) + q*(A $ b $ j) else A $ i $ j)"

text\<open>Definitions of elementary column operations\<close>

definition interchange_columns :: "'a ^'n^'m => 'n => 'n \<Rightarrow> 'a ^'n^'m"
  where "interchange_columns A n m = (\<chi> i j. if j=n then A $ i $ m else if j=m then A $ i $ n else A $ i $ j)"

definition mult_column :: "('a::times) ^'n^'m => 'n => 'a \<Rightarrow> 'a ^'n^'m"
  where " mult_column A n q = (\<chi> i j. if j=n then (A $ i $ j)*q else A $ i $ j)"

definition column_add :: "('a::{plus, times}) ^'n^'m => 'n => 'n \<Rightarrow> 'a \<Rightarrow> 'a ^'n^'m"
  where "column_add A n m q = (\<chi> i j. if j=n then ((A $ i $ n) + (A $ i $ m)*q) else A $ i $ j)"

subsection\<open>Properties about elementary row operations\<close>
subsubsection\<open>Properties about interchanging rows\<close>

text\<open>Properties about @{term "interchange_rows"}\<close>

lemma interchange_same_rows: "interchange_rows A a a = A"
  unfolding interchange_rows_def by vector

lemma interchange_rows_i[simp]: "interchange_rows A i j $ i = A $ j"
  unfolding interchange_rows_def by vector

lemma interchange_rows_j[simp]: "interchange_rows A i j $ j = A $ i"
  unfolding interchange_rows_def by vector

lemma interchange_rows_preserves:
  assumes "i \<noteq> a" and "j \<noteq> a"
  shows "interchange_rows A i j $ a = A $ a"
  using assms unfolding interchange_rows_def by vector

lemma interchange_rows_mat_1:
  shows "interchange_rows (mat 1) a b ** A = interchange_rows A a b"
proof (unfold matrix_matrix_mult_def interchange_rows_def, vector, auto)
  fix ia
  let ?f="(\<lambda>k. mat (1::'a) $ a $ k * A $ k $ ia)"
  have univ_rw:"UNIV = (UNIV-{a}) \<union> {a}" by auto
  have "sum ?f UNIV = sum ?f ((UNIV-{a}) \<union> {a})" using univ_rw by auto
  also have "... = sum ?f (UNIV-{a}) + sum ?f {a}"
  proof (rule sum.union_disjoint)
    show "finite (UNIV - {a})" by (metis finite_code) 
    show "finite {a}" by simp
    show "(UNIV - {a}) \<inter> {a} = {}" by simp
  qed
  also have "... = sum ?f {a}" unfolding mat_def by auto
  also have "... = ?f a" by auto
  also have "... = A $ a $ ia" unfolding mat_def by auto
  finally show "(\<Sum>k\<in>UNIV. mat (1::'a) $ a $ k * A $ k $ ia) = A $ a $ ia" .
  assume i: " a \<noteq> b"
  let ?g= "\<lambda>k. mat (1::'a) $ b $ k * A $ k $ ia"
  have univ_rw':"UNIV = (UNIV-{b}) \<union> {b}" by auto
  have "sum ?g UNIV = sum ?g ((UNIV-{b}) \<union> {b})" using univ_rw' by auto
  also have "... = sum ?g (UNIV-{b}) + sum ?g {b}" by (rule sum.union_disjoint, auto)
  also have "... = sum ?g {b}"  unfolding mat_def by auto
  also have "... = ?g b" by simp
  finally show "(\<Sum>k\<in>UNIV. mat (1::'a) $ b $ k * A $ k $ ia) = A $ b $ ia" unfolding mat_def by simp
next
  fix i j
  assume ib: "i \<noteq> b" and ia:"i \<noteq> a"
  let ?h="\<lambda>k. mat (1::'a) $ i $ k * A $ k $ j"
  have univ_rw'':"UNIV = (UNIV-{i}) \<union> {i}" by auto
  have "sum ?h UNIV = sum ?h ((UNIV-{i}) \<union> {i})" using univ_rw'' by auto
  also have "... = sum ?h (UNIV-{i}) + sum ?h {i}"  by (rule sum.union_disjoint, auto)
  also have "... =  sum ?h {i}" unfolding mat_def by auto  
  also have "... = ?h i" by simp
  finally show " (\<Sum>k\<in>UNIV. mat (1::'a) $ i $ k * A $ k $ j) = A $ i $ j" unfolding mat_def by auto
qed

lemma invertible_interchange_rows: "invertible (interchange_rows (mat 1) a b)"
proof (unfold invertible_def, rule exI[of _ "interchange_rows (mat 1) a b"], simp, unfold matrix_matrix_mult_def, vector, clarify, 
    unfold interchange_rows_def, vector, unfold mat_1_fun, auto+) 
  fix s t::"'b"   
  assume s_not_t: "s \<noteq> t"
  show " (\<Sum>k::'b\<in>UNIV. (if s = k then 1::'a else (0::'a)) * (if k = t then 1::'a else if k = t then 1::'a else if k = t then 1::'a else (0::'a))) = (0::'a)"
    by (rule sum.neutral, simp add: s_not_t)
  assume b_not_t: "b \<noteq> t"
  show "(\<Sum>k\<in>UNIV. (if s = b then if t = k then 1::'a else (0::'a) else if s = k then 1::'a else (0::'a)) *
    (if k = t then 0::'a else if k = b then 1::'a else if k = t then 1::'a else (0::'a))) =
    (0::'a)" by (rule sum.neutral, simp)
  assume a_not_t: "a \<noteq> t"
  show "(\<Sum>k\<in>UNIV. (if s = a then if b = k then 1::'a else (0::'a) else if s = b then if a = k then 1::'a else (0::'a) else if s = k then 1::'a else (0::'a)) *
    (if k = a then 0::'a else if k = b then 0::'a else if k = t then 1::'a else (0::'a))) =
    (0::'a)" by (rule sum.neutral, auto simp add: s_not_t)
next
  fix s t::"'b"
  assume a_noteq_t: "a\<noteq>t" and s_noteq_t: "s \<noteq> t"
  show " (\<Sum>k\<in>UNIV. (if s = a then if t = k then 1::'a else (0::'a) else if s = t then if a = k then 1::'a else (0::'a) else if s = k then 1::'a else (0::'a)) *
    (if k = a then 1::'a else if k = t then 0::'a else if k = t then 1::'a else (0::'a))) =
    (0::'a)" apply (rule sum.neutral) using s_noteq_t by fastforce
next
  fix s t::"'b"
  show "(\<Sum>k\<in>UNIV. (if t = k then 1::'a else (0::'a)) * (if k = t then 1::'a else if k = t then 1::'a else if k = t then 1::'a else (0::'a))) = (1::'a)"
  proof - 
    let ?f="(\<lambda>k. (if t = k then 1::'a else (0::'a)) * (if k = t then 1::'a else if k = t then 1::'a else if k = t then 1::'a else (0::'a)))"
    have univ_eq: "UNIV = ((UNIV - {t}) \<union> {t})" by auto
    have "sum ?f UNIV = sum ?f ((UNIV - {t}) \<union> {t}) " using univ_eq by simp
    also have "... = sum ?f (UNIV - {t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
    also have "... = 0 + sum ?f {t}" by auto
    also have "... = sum ?f {t}" by simp
    also have "... = 1" by simp
    finally show ?thesis .
  qed
next
  fix s t::"'b"
  assume b_noteq_t: "b \<noteq> t"
  show " (\<Sum>k\<in>UNIV. (if b = k then 1::'a else (0::'a)) * (if k = t then 0::'a else if k = b then 1::'a else if k = t then 1::'a else (0::'a))) = (1::'a)"
  proof -
    let ?f="(\<lambda>k. (if b = k then 1::'a else (0::'a)) * (if k = t then 0::'a else if k = b then 1::'a else if k = t then 1::'a else (0::'a)))"
    have univ_eq: "UNIV = ((UNIV - {b}) \<union> {b})" by auto
    have "sum ?f UNIV = sum ?f ((UNIV - {b}) \<union> {b}) " using univ_eq by simp
    also have "... = sum ?f (UNIV - {b}) + sum ?f {b}" by (rule sum.union_disjoint, auto)
    also have "... = 0 + sum ?f {b}" by auto
    also have "... = sum ?f {b}" by simp
    also have "... = 1" using b_noteq_t by simp
    finally show ?thesis .
  qed
  assume a_noteq_t: "a\<noteq>t"
  show " (\<Sum>k\<in>UNIV. (if t = k then 1::'a else (0::'a)) * (if k = a then 0::'a else if k = b then 0::'a else if k = t then 1::'a else (0::'a))) = (1::'a)"
  proof -
    let ?f="(\<lambda>k.  (if t = k then 1::'a else (0::'a)) * (if k = a then 0::'a else if k = b then 0::'a else if k = t then 1::'a else (0::'a)))"
    have univ_eq: "UNIV = ((UNIV - {t}) \<union> {t})" by auto
    have "sum ?f UNIV = sum ?f ((UNIV - {t}) \<union> {t}) " using univ_eq by simp
    also have "... = sum ?f (UNIV - {t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
    also have "... = 0 + sum ?f {t}" by auto
    also have "... = sum ?f {t}" by simp
    also have "... = 1" using b_noteq_t a_noteq_t by simp
    finally show ?thesis .
  qed
next
  fix s t::"'b"
  assume a_noteq_t: "a\<noteq>t"
  show "(\<Sum>k\<in>UNIV. (if a = k then 1::'a else (0::'a)) * (if k = a then 1::'a else if k = t then 0::'a else if k = t then 1::'a else (0::'a))) = (1::'a)"
  proof -
    let ?f="\<lambda>k.  (if a = k then 1::'a else (0::'a)) * (if k = a then 1::'a else if k = t then 0::'a else if k = t then 1::'a else (0::'a))"
    have univ_eq: "UNIV = ((UNIV - {a}) \<union> {a})" by auto
    have "sum ?f UNIV = sum ?f ((UNIV - {a}) \<union> {a}) " using univ_eq by simp
    also have "... = sum ?f (UNIV - {a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
    also have "... = 0 + sum ?f {a}" by auto
    also have "... = sum ?f {a}" by simp
    also have "... = 1" using a_noteq_t by simp
    finally show ?thesis .    
  qed
qed

subsubsection\<open>Properties about multiplying a row by a constant\<close>
text\<open>Properties about @{term "mult_row"}\<close>

lemma mult_row_mat_1: "mult_row (mat 1) a q ** A = mult_row A a q"
proof (unfold matrix_matrix_mult_def mult_row_def, vector, auto)
  fix ia
  let ?f="\<lambda>k. q * mat (1::'a) $ a $ k * A $ k $ ia"
  have univ_rw:"UNIV = (UNIV-{a}) \<union> {a}" by auto
  have "sum ?f UNIV = sum ?f ((UNIV-{a}) \<union> {a})" using univ_rw by auto
  also have "... = sum ?f (UNIV-{a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
  also have "... = sum ?f {a}" unfolding mat_def by auto  
  also have "... = ?f a" by auto
  also have "... = q * A $ a $ ia" unfolding mat_def by auto
  finally show  "(\<Sum>k\<in>UNIV. q * mat (1::'a) $ a $ k * A $ k $ ia) = q * A $ a $ ia" .
  fix i
  assume i: "i \<noteq> a"
  let ?g="\<lambda>k. mat (1::'a) $ i $ k * A $ k $ ia"
  have univ_rw'':"UNIV = (UNIV-{i}) \<union> {i}" by auto
  have "sum ?g UNIV = sum ?g ((UNIV-{i}) \<union> {i})" using univ_rw'' by auto
  also have "... = sum ?g (UNIV-{i}) + sum ?g {i}"  by (rule sum.union_disjoint, auto)
  also have "... =  sum ?g {i}" unfolding mat_def by auto 
  also have "... = ?g i" by simp
  finally show "(\<Sum>k\<in>UNIV. mat (1::'a) $ i $ k * A $ k $ ia) = A $ i $ ia" unfolding mat_def by simp
qed

lemma invertible_mult_row:
  assumes qk: "q * k = 1" and kq: "k*q=1"
  shows "invertible (mult_row (mat 1) a q)"
proof (unfold invertible_def, rule exI[of _ "mult_row (mat 1) a k"],rule conjI)
  show "mult_row (mat (1::'a)) a q ** mult_row (mat (1::'a)) a k = mat (1::'a)"
  proof (unfold matrix_matrix_mult_def, vector, clarify, unfold mult_row_def, vector, unfold mat_1_fun, auto)
    show "(\<Sum>ka\<in>UNIV. q * (if a = ka then 1::'a else (0::'a)) * (if ka = a then k * (1::'a) else if ka = a then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>ka. q * (if a = ka then 1::'a else (0::'a)) * (if ka = a then k * (1::'a) else if ka = a then 1::'a else (0::'a)) "
      have univ_eq: "UNIV = ((UNIV - {a}) \<union> {a})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {a}) \<union> {a}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
      also have "... = 0 + sum ?f {a}" by auto
      also have "... = sum ?f {a}" by simp
      also have "... = 1" using qk by simp
      finally show ?thesis .        
    qed
  next
    fix s
    assume s_noteq_a: "s\<noteq>a"
    show "(\<Sum>ka\<in>UNIV. (if s = ka then 1::'a else (0::'a)) * (if ka = a then k * (1::'a) else if ka = a then 1::'a else 0)) = 0"
      by (rule sum.neutral, simp add: s_noteq_a)
  next
    fix t
    assume a_noteq_t: "a\<noteq>t"
    show "(\<Sum>ka\<in>UNIV. (if t = ka then 1::'a else (0::'a)) * (if ka = a then k * (0::'a) else if ka = t then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>ka. (if t = ka then 1::'a else (0::'a)) * (if ka = a then k * (0::'a) else if ka = t then 1::'a else (0::'a)) "
      have univ_eq: "UNIV = ((UNIV - {t}) \<union> {t})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {t}) \<union> {t}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {t}" by simp
      also have "... = 1" using a_noteq_t by auto
      finally show ?thesis .
    qed            
    fix s
    assume s_not_t: "s\<noteq>t"
    show "(\<Sum>ka\<in>UNIV. (if s = a then q * (if a = ka then 1::'a else (0::'a)) else if s = ka then 1::'a else (0::'a)) *
      (if ka = a then k * (0::'a) else if ka = t then 1::'a else (0::'a))) = (0::'a)"
      by (rule sum.neutral, simp add: s_not_t a_noteq_t)
  qed            
  show "mult_row (mat (1::'a)) a k ** mult_row (mat (1::'a)) a q = mat (1::'a)"
  proof (unfold matrix_matrix_mult_def, vector, clarify, unfold mult_row_def, vector, unfold mat_1_fun, auto)
    show "(\<Sum>ka\<in>UNIV. k * (if a = ka then 1::'a else (0::'a)) * (if ka = a then q * (1::'a) else if ka = a then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>ka. k * (if a = ka then 1::'a else (0::'a)) * (if ka = a then q * (1::'a) else if ka = a then 1::'a else (0::'a)) "
      have univ_eq: "UNIV = ((UNIV - {a}) \<union> {a})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {a}) \<union> {a}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
      also have "... = 0 + sum ?f {a}" by auto
      also have "... = sum ?f {a}" by simp
      also have "... = 1" using kq by simp
      finally show ?thesis .        
    qed
  next
    fix s
    assume s_not_a: "s\<noteq>a"
    show "(\<Sum>k\<in>UNIV. (if s = k then 1::'a else (0::'a)) * (if k = a then q * (1::'a) else if k = a then 1::'a else (0::'a))) = (0::'a)"
      by (rule sum.neutral, simp add: s_not_a)
  next
    fix t
    assume a_not_t: "a\<noteq>t"
    show "(\<Sum>k\<in>UNIV. (if t = k then 1::'a else (0::'a)) * (if k = a then q * (0::'a) else if k = t then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k. (if t = k then 1::'a else (0::'a)) * (if k = a then q * (0::'a) else if k = t then 1::'a else (0::'a))"
      have univ_eq: "UNIV = ((UNIV - {t}) \<union> {t})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {t}) \<union> {t}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {t}" by simp
      also have "... = 1" using a_not_t by simp
      finally show ?thesis .
    qed
    fix s
    assume s_not_t: "s\<noteq>t"
    show " (\<Sum>ka\<in>UNIV. (if s = a then k * (if a = ka then 1::'a else (0::'a)) else if s = ka then 1::'a else (0::'a)) *
      (if ka = a then q * (0::'a) else if ka = t then 1::'a else (0::'a))) = (0::'a)"
      by (rule sum.neutral, simp add: s_not_t)    
  qed
qed

corollary invertible_mult_row':
  assumes q_not_zero: "q \<noteq> 0"
  shows "invertible (mult_row (mat (1::'a::{field})) a q)"
  by (simp add: invertible_mult_row[of q "inverse q"] q_not_zero)

subsubsection\<open>Properties about adding a row multiplied by a constant to another row\<close>
text\<open>Properties about @{term "row_add"}\<close>

lemma row_add_mat_1: "row_add (mat 1) a b q ** A = row_add A a b q"
proof (unfold matrix_matrix_mult_def row_add_def, vector, auto)
  fix j
  let ?f=" (\<lambda>k. (mat (1::'a) $ a $ k + q * mat (1::'a) $ b $ k) * A $ k $ j)"
  show "sum ?f UNIV = A $ a $ j + q * A $ b $ j"
  proof (cases "a=b")
    case False
    have univ_rw: "UNIV = {a} \<union> ({b} \<union> (UNIV - {a} - {b}))" by auto
    have sum_rw: "sum ?f ({b} \<union> (UNIV - {a} - {b})) = sum ?f {b} + sum ?f (UNIV - {a} - {b})" by (rule sum.union_disjoint, auto simp add: False)
    have "sum ?f UNIV = sum ?f ({a} \<union> ({b} \<union> (UNIV - {a} - {b})))" using univ_rw by simp
    also have "... = sum ?f {a} + sum ?f ({b} \<union> (UNIV - {a} - {b}))" by (rule sum.union_disjoint, auto simp add: False)
    also have "... = sum ?f {a} + sum ?f {b} + sum ?f (UNIV - {a} - {b})" unfolding sum_rw add.assoc ..
    also have "... = sum ?f {a} + sum ?f {b}"
    proof -
      have "sum ?f (UNIV - {a} - {b}) = sum (\<lambda>k. 0) (UNIV - {a} - {b})" unfolding mat_def by (rule sum.cong, auto)
      also have "... = 0" unfolding sum.neutral_const ..
      finally show ?thesis by simp
    qed
    also have "... = A $ a $ j + q * A $ b $ j" using False unfolding mat_def by simp
    finally show ?thesis .
  next
    case True
    have univ_rw: "UNIV = {b} \<union> (UNIV - {b})" by auto
    have "sum ?f UNIV = sum ?f ({b} \<union> (UNIV - {b}))" using univ_rw by simp
    also have "... = sum ?f {b} + sum ?f (UNIV  - {b})" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {b}"
    proof -
      have "sum ?f (UNIV - {b}) = sum (\<lambda>k. 0) (UNIV - {b})" using True unfolding mat_def by auto
      also have "... = 0" unfolding sum.neutral_const ..
      finally show ?thesis by simp
    qed
    also have "... = A $ a $ j + q * A $ b $ j" 
      by (unfold True mat_def, simp, metis (hide_lams, no_types) vector_add_component vector_sadd_rdistrib vector_smult_component vector_smult_lid)
    finally show ?thesis .
  qed
  fix i assume i: "i\<noteq>a"
  let ?g="\<lambda>k.  mat (1::'a) $ i $ k * A $ k $ j"
  have univ_rw: "UNIV = {i} \<union> (UNIV - {i})" by auto
  have "sum ?g UNIV = sum ?g ({i} \<union> (UNIV - {i}))" using univ_rw by simp
  also have "... = sum ?g {i} + sum ?g (UNIV - {i})" by (rule sum.union_disjoint, auto)
  also have "... = sum ?g {i}"
  proof -
    have "sum ?g (UNIV - {i}) = sum (\<lambda>k. 0) (UNIV - {i})" unfolding mat_def by auto
    also have "... = 0" unfolding sum.neutral_const ..
    finally show ?thesis by simp
  qed
  also have "... =  A $ i $ j" unfolding mat_def by simp
  finally show "(\<Sum>k\<in>UNIV. mat (1::'a) $ i $ k * A $ k $ j) = A $ i $ j" .
qed

lemma invertible_row_add:
  assumes a_noteq_b: "a\<noteq>b"
  shows "invertible (row_add (mat (1::'a::{ring_1})) a b q)"
proof (unfold invertible_def, rule exI[of _ "(row_add (mat 1) a b (-q))"], rule conjI)
  show "row_add (mat (1::'a)) a b q ** row_add (mat (1::'a)) a b (- q) = mat (1::'a)" using a_noteq_b
  proof (unfold matrix_matrix_mult_def, vector, clarify, unfold row_add_def, vector, unfold mat_1_fun, auto)
    show " (\<Sum>k::'b\<in>UNIV. (if b = k then 1::'a else (0::'a)) * (if k = a then (0::'a) + - q * (1::'a) else if k = b then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k. (if b = k then 1::'a else (0::'a)) * (if k = a then (0::'a) + - q * (1::'a) else if k = b then 1::'a else (0::'a))"
      have univ_eq: "UNIV = ((UNIV - {b}) \<union> {b})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {b}) \<union> {b}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {b}) + sum ?f {b}" by (rule sum.union_disjoint, auto)
      also have "... = 0 + sum ?f {b}" by auto
      also have "... = sum ?f {b}" by simp
      also have "... = 1" using a_noteq_b by simp
      finally show ?thesis .
    qed
    show "(\<Sum>k::'b\<in>UNIV. ((if a = k then 1::'a else (0::'a)) + q * (if b = k then 1::'a else (0::'a))) * (if k = a then (1::'a) + - 
      q * (0::'a) else if k = a then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k.  ((if a = k then 1::'a else (0::'a)) + q * (if b = k then 1::'a else (0::'a))) * (if k = a then (1::'a) + - 
        q * (0::'a) else if k = a then 1::'a else (0::'a))"
      have univ_eq: "UNIV = ((UNIV - {a}) \<union> {a})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {a}) \<union> {a}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
      also have "... = 0 + sum ?f {a}" by auto
      also have "... = sum ?f {a}" by simp
      also have "... = 1" using a_noteq_b by simp
      finally show ?thesis .
    qed
  next
    fix s
    assume s_not_a: "s \<noteq> a"
    show "(\<Sum>k::'b\<in>UNIV. (if s = k then 1::'a else (0::'a)) * (if k = a then (1::'a) + - q * (0::'a) else if k = a then 1::'a else (0::'a))) = (0::'a)"
      by (rule sum.neutral, auto simp add: s_not_a)       
  next
    fix t
    assume b_not_t: "b \<noteq> t" and a_not_t: "a \<noteq> t"
    show "(\<Sum>k\<in>UNIV. (if t = k then 1::'a else (0::'a)) * (if k = a then (0::'a) + - q * (0::'a) else if k = t then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k. (if t = k then 1::'a else (0::'a)) * (if k = a then (0::'a) + - q * (0::'a) else if k = t then 1::'a else (0::'a)) "
      have univ_eq: "UNIV = ((UNIV - {t}) \<union> {t})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {t}) \<union> {t}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
      also have "... = 0 + sum ?f {t}" by auto
      also have "... = sum ?f {t}" by simp
      also have "... = 1" using b_not_t a_not_t by simp
      finally show ?thesis .
    qed
  next     
    fix s t
    assume  b_not_t: "b \<noteq> t" and a_not_t: "a \<noteq> t" and  s_not_t: "s \<noteq> t"
    show " (\<Sum>k\<in>UNIV. (if s = a then (if a = k then 1::'a else (0::'a)) + q * (if b = k then 1::'a else (0::'a)) else if s = k then 1::'a else (0::'a)) *
      (if k = a then (0::'a) + - q * (0::'a) else if k = t then 1::'a else (0::'a))) = (0::'a)" by (rule sum.neutral, auto simp add: b_not_t a_not_t s_not_t)     
  next         
    fix s
    assume s_not_b: "s\<noteq>b"
    let ?f="\<lambda>k. (if s = a then (if a = k then 1::'a else (0::'a)) + q * (if b = k then 1::'a else (0::'a)) else if s = k then 1::'a else (0::'a)) *
      (if k = a then (0::'a) + - q * (1::'a) else if k = b then 1::'a else (0::'a))"
    show "sum ?f UNIV = (0::'a)"         
    proof (cases "s=a")         
      case False
      show ?thesis by (rule sum.neutral, auto simp add: False s_not_b a_noteq_b)
    next         
      case True \<comment> \<open>This case is different from the other cases\<close>                  
      have univ_eq: "UNIV = ((UNIV - {a}- {b}) \<union> ({b} \<union> {a}))" by auto
      have sum_a: "sum ?f {a} = -q"  unfolding True using s_not_b using a_noteq_b by auto
      have sum_b: "sum ?f {b} = q" unfolding True using s_not_b using a_noteq_b by auto
      have sum_rest: "sum ?f (UNIV - {a} - {b}) = 0"  by (rule sum.neutral, auto simp add: True s_not_b a_noteq_b)
      have "sum ?f UNIV = sum ?f ((UNIV - {a}- {b}) \<union> ({b} \<union> {a}))"  using univ_eq by simp
      also have "... = sum ?f (UNIV - {a} - {b}) + sum ?f ({b} \<union> {a})" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f (UNIV - {a} - {b}) + sum ?f {b} + sum ?f {a}" by (auto simp add: sum.union_disjoint a_noteq_b)     
      also have "... = 0" unfolding sum_a sum_b sum_rest by simp
      finally show ?thesis .
    qed
  qed
next
  show "row_add (mat (1::'a)) a b (- q) ** row_add (mat (1::'a)) a b q = mat (1::'a)" using a_noteq_b
  proof (unfold matrix_matrix_mult_def, vector, clarify, unfold row_add_def, vector, unfold mat_1_fun, auto)     
    show "(\<Sum>k\<in>UNIV. (if b = k then 1::'a else (0::'a)) * (if k = a then (0::'a) + q * (1::'a) else if k = b then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k. (if b = k then 1::'a else (0::'a)) * (if k = a then (0::'a) + q * (1::'a) else if k = b then 1::'a else (0::'a))"
      have univ_eq: "UNIV = ((UNIV - {b}) \<union> {b})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {b}) \<union> {b}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {b}) + sum ?f {b}" by (rule sum.union_disjoint, auto)
      also have "... = 0 + sum ?f {b}" by auto
      also have "... = sum ?f {b}" by simp
      also have "... = 1" using a_noteq_b by simp
      finally show ?thesis .
    qed
  next
    show "(\<Sum>k\<in>UNIV. ((if a = k then 1 else 0) - q * (if b = k then 1 else 0)) * (if k = a then 1 + q * 0 else if k = a then 1 else 0)) = 1"
    proof -
      let ?f="\<lambda>k. ((if a = k then 1::'a else (0::'a)) + - (q * (if b = k then 1::'a else (0::'a)))) * (if k = a then (1::'a) + q * (0::'a) else if k = a then 1::'a else (0::'a))"
      have univ_eq: "UNIV = ((UNIV - {a}) \<union> {a})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {a}) \<union> {a}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
      also have "... = 0 + sum ?f {a}" by auto
      also have "... = sum ?f {a}" by simp
      also have "... = 1" using a_noteq_b by simp
      finally show ?thesis by simp
    qed
  next
    fix s
    assume s_not_a: "s\<noteq>a"
    show "(\<Sum>k\<in>UNIV. (if s = k then 1::'a else (0::'a)) * (if k = a then (1::'a) + q * (0::'a) else if k = a then 1::'a else (0::'a))) = (0::'a)"
      by (rule sum.neutral, auto simp add: s_not_a)
  next 
    fix t
    assume b_not_t: "b \<noteq> t" and a_not_t: "a \<noteq> t"
    show "(\<Sum>k\<in>UNIV. (if t = k then 1::'a else (0::'a)) * (if k = a then (0::'a) + q * (0::'a) else if k = t then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k. (if t = k then 1::'a else (0::'a)) * (if k = a then (0::'a) + q * (0::'a) else if k = t then 1::'a else (0::'a))"
      have univ_eq: "UNIV = ((UNIV - {t}) \<union> {t})" by auto
      have "sum ?f UNIV = sum ?f ((UNIV - {t}) \<union> {t}) " using univ_eq by simp
      also have "... = sum ?f (UNIV - {t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
      also have "... = 0 + sum ?f {t}" by auto
      also have "... = sum ?f {t}" by simp
      also have "... = 1" using b_not_t a_not_t by simp
      finally show ?thesis .
    qed
  next
    fix s t
    assume b_not_t: "b \<noteq> t" and a_not_t: "a \<noteq> t" and s_not_t: "s \<noteq> t"     
    show "(\<Sum>k\<in>UNIV. (if s = a then (if a = k then 1::'a else (0::'a)) + - q * (if b = k then 1::'a else (0::'a)) else if s = k then 1::'a else (0::'a)) *
      (if k = a then (0::'a) + q * (0::'a) else if k = t then 1::'a else (0::'a))) = (0::'a)"
      by (rule sum.neutral, auto simp add: b_not_t a_not_t s_not_t)
  next
    fix s
    assume s_not_b: "s\<noteq>b"
    let ?f="\<lambda>k.(if s = a then (if a = k then 1::'a else (0::'a)) + - q * (if b = k then 1::'a else (0::'a)) else if s = k then 1::'a else (0::'a)) 
      * (if k = a then (0::'a) + q * (1::'a) else if k = b then 1::'a else (0::'a))"
    show "sum ?f UNIV = 0"
    proof (cases "s=a")         
      case False
      show ?thesis by (rule sum.neutral, auto simp add: False s_not_b a_noteq_b)
    next         
      case True \<comment> \<open>This case is different from the other cases\<close>                  
      have univ_eq: "UNIV = ((UNIV - {a}- {b}) \<union> ({b} \<union> {a}))" by auto
      have sum_a: "sum ?f {a} = q"  unfolding True using s_not_b using a_noteq_b by auto
      have sum_b: "sum ?f {b} = -q" unfolding True using s_not_b using a_noteq_b by auto
      have sum_rest: "sum ?f (UNIV - {a} - {b}) = 0"  by (rule sum.neutral, auto simp add: True s_not_b a_noteq_b)
      have "sum ?f UNIV = sum ?f ((UNIV - {a}- {b}) \<union> ({b} \<union> {a}))"  using univ_eq by simp
      also have "... = sum ?f (UNIV - {a} - {b}) + sum ?f ({b} \<union> {a})" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f (UNIV - {a} - {b}) + sum ?f {b} + sum ?f {a}" by (auto simp add: sum.union_disjoint a_noteq_b)
      also have "... = 0" unfolding sum_a sum_b sum_rest by simp
      finally show ?thesis .
    qed
  qed
qed

subsection\<open>Properties about elementary column operations\<close>
subsubsection\<open>Properties about interchanging columns\<close>
text\<open>Properties about @{term "interchange_columns"}\<close>

lemma interchange_columns_mat_1: "A ** interchange_columns (mat 1) a b = interchange_columns A a b"
proof (unfold matrix_matrix_mult_def, unfold interchange_columns_def, vector, auto) 
  fix i  
  show "(\<Sum>k\<in>UNIV. A $ i $ k * mat (1::'a) $ k $ a) = A $ i $ a"
  proof -
    let ?f="(\<lambda>k. A $ i $ k * mat (1::'a) $ k $ a)"
    have univ_rw:"UNIV = (UNIV-{a}) \<union> {a}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{a}) \<union> {a})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {a}" unfolding mat_def by auto
    finally show ?thesis unfolding mat_def by simp
  qed    
  assume a_not_b: "a\<noteq>b"
  show " (\<Sum>k\<in>UNIV. A $ i $ k * mat (1::'a) $ k $ b) = A $ i $ b"
  proof -
    let ?f="(\<lambda>k. A $ i $ k * mat (1::'a) $ k $ b)"
    have univ_rw:"UNIV = (UNIV-{b}) \<union> {b}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{b}) \<union> {b})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{b}) + sum ?f {b}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {b}" unfolding mat_def by auto
    finally show ?thesis unfolding mat_def by simp
  qed
next
  fix i j
  assume j_not_b: "j \<noteq> b" and j_not_a: "j \<noteq> a"
  show "(\<Sum>k\<in>UNIV. A $ i $ k * mat (1::'a) $ k $ j) = A $ i $ j"
  proof -
    let ?f="(\<lambda>k. A $ i $ k * mat (1::'a) $ k $ j)"
    have univ_rw:"UNIV = (UNIV-{j}) \<union> {j}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{j}) \<union> {j})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{j}) + sum ?f {j}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {j}" unfolding mat_def using j_not_b j_not_a by auto
    finally show ?thesis unfolding mat_def by simp
  qed
qed

lemma invertible_interchange_columns: "invertible (interchange_columns (mat 1) a b)"
proof (unfold invertible_def, rule exI[of _ "interchange_columns (mat 1) a b"], simp, unfold matrix_matrix_mult_def, vector, clarify, 
    unfold interchange_columns_def, vector, unfold mat_1_fun, auto+) 
  show "(\<Sum>k\<in>UNIV. (if k = b then 1::'a else if k = b then 1::'a else if b = k then 1::'a else (0::'a)) * (if k = b then 1::'a else (0::'a))) = (1::'a)"
  proof -
    let ?f="(\<lambda>k. (if k = b then 1::'a else if k = b then 1::'a else if b = k then 1::'a else (0::'a)) * (if k = b then 1::'a else (0::'a)))"
    have univ_rw:"UNIV = (UNIV-{b}) \<union> {b}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{b}) \<union> {b})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{b}) + sum ?f {b}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {b}" by auto
    finally show ?thesis by simp
  qed
  assume a_not_b: "a \<noteq> b"
  show "(\<Sum>k\<in>UNIV. (if k = a then 0::'a else if k = b then 1::'a else if a = k then 1::'a else (0::'a)) * (if k = b then 1::'a else (0::'a))) = (1::'a)"
  proof -
    let ?f="\<lambda>k. (if k = a then 0::'a else if k = b then 1::'a else if a = k then 1::'a else (0::'a)) * (if k = b then 1::'a else (0::'a))"
    have univ_rw:"UNIV = (UNIV-{b}) \<union> {b}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{b}) \<union> {b})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{b}) + sum ?f {b}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {b}" using a_not_b by simp
    finally show ?thesis using a_not_b by auto
  qed
next
  fix t
  assume b_not_t: "b \<noteq> t"
  show " (\<Sum>k\<in>UNIV. (if k = b then 1::'a else if k = b then 1::'a else if b = k then 1::'a else (0::'a)) * (if k = t then 1::'a else (0::'a))) = (0::'a)"
    apply (rule sum.neutral) using b_not_t by auto
  assume b_not_a: "b \<noteq> a"
  show "(\<Sum>k\<in>UNIV. (if k = a then 1::'a else if k = b then 0::'a else if b = k then 1::'a else (0::'a)) *
    (if t = a then if k = b then 1::'a else (0::'a) else if t = b then if k = a then 1::'a else (0::'a) else if k = t then 1::'a else (0::'a))) =
    (0::'a)" apply (rule sum.neutral) using b_not_t by auto
next
  fix t
  assume a_not_b: "a \<noteq> b" and a_not_t: "a \<noteq> t"
  show "(\<Sum>k\<in>UNIV. (if k = a then 0::'a else if k = b then 1::'a else if a = k then 1::'a else (0::'a)) *
    (if t = b then if k = a then 1::'a else (0::'a) else if k = t then 1::'a else (0::'a))) = (0::'a)"
    by (rule sum.neutral, auto simp add: a_not_b a_not_t)
next
  assume b_not_a: "b \<noteq> a"
  show "(\<Sum>k\<in>UNIV. (if k = a then 1::'a else if k = b then 0::'a else if b = k then 1::'a else (0::'a)) * (if k = a then 1::'a else (0::'a))) = (1::'a)"
  proof -
    let ?f="\<lambda>k.  (if k = a then 1::'a else if k = b then 0::'a else if b = k then 1::'a else (0::'a)) * (if k = a then 1::'a else (0::'a))"
    have univ_rw:"UNIV = (UNIV-{a}) \<union> {a}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{a}) \<union> {a})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {a}" using b_not_a by simp
    finally show ?thesis using b_not_a by auto
  qed
next
  fix t
  assume t_not_a: "t \<noteq> a" and t_not_b: "t \<noteq> b"
  show "(\<Sum>k\<in>UNIV. (if k = a then 0::'a else if k = b then 0::'a else if t = k then 1::'a else (0::'a)) * (if k = t then 1::'a else (0::'a))) = (1::'a)"
  proof -
    let ?f="\<lambda>k. (if k = a then 0::'a else if k = b then 0::'a else if t = k then 1::'a else (0::'a)) * (if k = t then 1::'a else (0::'a))"
    have univ_rw:"UNIV = (UNIV-{t}) \<union> {t}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{t}) \<union> {t})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {t}" using t_not_a t_not_b by simp
    also have "... = 1"  using t_not_a t_not_b by simp
    finally show ?thesis .
  qed
next
  fix s t
  assume s_not_a: "s \<noteq> a" and s_not_b: "s \<noteq> b" and s_not_t: "s \<noteq> t"
  show "(\<Sum>k\<in>UNIV. (if k = a then 0::'a else if k = b then 0::'a else if s = k then 1::'a else (0::'a)) *
    (if t = a then if k = b then 1::'a else (0::'a) else if t = b then if k = a then 1::'a else (0::'a) else if k = t then 1::'a else (0::'a))) =
    (0::'a)"
    by (rule sum.neutral, auto simp add: s_not_a s_not_b s_not_t)
qed

subsubsection\<open>Properties about multiplying a column by a constant\<close>
text\<open>Properties about @{term "mult_column"}\<close>

lemma mult_column_mat_1: "A ** mult_column (mat 1) a q = mult_column A a q"
proof (unfold matrix_matrix_mult_def, unfold mult_column_def, vector, auto)
  fix i
  show "(\<Sum>k\<in>UNIV. A $ i $ k * (mat (1::'a) $ k $ a * q)) = A $ i $ a * q"
  proof -
    let ?f="\<lambda>k.  A $ i $ k * (mat (1::'a) $ k $ a * q)"
    have univ_rw:"UNIV = (UNIV-{a}) \<union> {a}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{a}) \<union> {a})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {a}" unfolding mat_def by auto
    also have "... = A $ i $ a * q" unfolding mat_def by auto
    finally show ?thesis .
  qed
  fix j
  show "(\<Sum>k\<in>UNIV. A $ i $ k * mat (1::'a) $ k $ j) = A $ i $ j"
  proof -
    let ?f="\<lambda>k. A $ i $ k * mat (1::'a) $ k $ j"
    have univ_rw:"UNIV = (UNIV-{j}) \<union> {j}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{j}) \<union> {j})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{j}) + sum ?f {j}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {j}" unfolding mat_def by auto
    also have "... = A $ i $ j" unfolding mat_def by auto
    finally show ?thesis .
  qed
qed

lemma invertible_mult_column:
  assumes qk: "q * k = 1" and kq: "k * q = 1"
  shows "invertible (mult_column (mat 1) a q)"
proof (unfold invertible_def, rule exI[of _ "mult_column (mat 1) a k"], rule conjI)  
  show "mult_column (mat 1) a q ** mult_column (mat 1) a k = mat 1" 
  proof (unfold matrix_matrix_mult_def, vector, clarify, unfold mult_column_def, vector, unfold mat_1_fun, auto)
    fix t    
    show "(\<Sum>ka\<in>UNIV. (if ka = a then (if t = ka then 1::'a else (0::'a)) * q else if t = ka then 1::'a else (0::'a)) *
      (if t = a then (if ka = t then 1::'a else (0::'a)) * k else if ka = t then 1::'a else (0::'a))) =
      (1::'a)"
    proof -
      let ?f=" \<lambda>ka. (if ka = a then (if t = ka then 1::'a else (0::'a)) * q else if t = ka then 1::'a else (0::'a)) *
        (if t = a then (if ka = t then 1::'a else (0::'a)) * k else if ka = t then 1::'a else (0::'a))"
      have univ_rw:"UNIV = (UNIV-{t}) \<union> {t}" by auto
      have "sum ?f UNIV = sum ?f ((UNIV-{t}) \<union> {t})" using univ_rw by auto
      also have "... = sum ?f (UNIV-{t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {t}" by auto
      also have "... = 1" using qk by auto
      finally show ?thesis .     
    qed   
    fix s
    assume s_not_t: "s \<noteq> t"
    show "(\<Sum>ka\<in>UNIV. (if ka = a then (if s = ka then 1::'a else (0::'a)) * q else if s = ka then 1::'a else (0::'a)) *
      (if t = a then (if ka = t then 1::'a else (0::'a)) * k else if ka = t then 1::'a else (0::'a))) =
      (0::'a)"
      apply (rule sum.neutral) using s_not_t by auto
  qed       
  show "mult_column (mat (1::'a)) a k ** mult_column (mat (1::'a)) a q = mat (1::'a)"
  proof (unfold matrix_matrix_mult_def, vector, clarify, unfold mult_column_def, vector, unfold mat_1_fun, auto)
    fix t
    show "(\<Sum>ka\<in>UNIV. (if ka = a then (if t = ka then 1::'a else (0::'a)) * k else if t = ka then 1::'a else (0::'a)) *
      (if t = a then (if ka = t then 1::'a else (0::'a)) * q else if ka = t then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f=" \<lambda>ka. (if ka = a then (if t = ka then 1::'a else (0::'a)) * k else if t = ka then 1::'a else (0::'a)) *
        (if t = a then (if ka = t then 1::'a else (0::'a)) * q else if ka = t then 1::'a else (0::'a))"
      have univ_rw:"UNIV = (UNIV-{t}) \<union> {t}" by auto
      have "sum ?f UNIV = sum ?f ((UNIV-{t}) \<union> {t})" using univ_rw by auto
      also have "... = sum ?f (UNIV-{t}) + sum ?f {t}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {t}" by auto
      also have "... = 1" using kq by auto
      finally show ?thesis .
    qed   
    fix s assume s_not_t: "s \<noteq> t"
    show "(\<Sum>ka\<in>UNIV. (if ka = a then (if s = ka then 1::'a else (0::'a)) * k else if s = ka then 1::'a else (0::'a)) *
      (if t = a then (if ka = t then 1::'a else (0::'a)) * q else if ka = t then 1::'a else (0::'a))) = 0"
      apply (rule sum.neutral) using s_not_t by auto
  qed
qed

corollary invertible_mult_column':  
  assumes q_not_zero: "q \<noteq> 0"
  shows "invertible (mult_column (mat (1::'a::{field})) a q)"
  by (simp add: invertible_mult_column[of q "inverse q"] q_not_zero)

subsubsection\<open>Properties about adding a column multiplied by a constant to another column\<close>
text\<open>Properties about @{term "column_add"}\<close>

lemma column_add_mat_1: "A ** column_add (mat 1) a b q = column_add A a b q"
proof (unfold matrix_matrix_mult_def, 
    unfold column_add_def, vector, auto)
  fix i
  let ?f="\<lambda>k. A $ i $ k * (mat (1::'a) $ k $ a + mat (1::'a) $ k $ b * q)"
  show "sum ?f UNIV =  A $ i $ a + A $ i $ b * q"
  proof (cases "a=b")
    case True
    have univ_rw:"UNIV = (UNIV-{a}) \<union> {a}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{a}) \<union> {a})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {a}" unfolding mat_def True by auto
    also have "... = ?f a" by auto
    also have "... = A $ i $ a + A $ i $ b * q" using True unfolding mat_1_fun using distrib_left[of "A $ i $ b" 1 q] by auto
    finally show ?thesis .
  next
    case False
    have univ_rw: "UNIV = {a} \<union> ({b} \<union> (UNIV - {a} - {b}))" by auto
    have sum_rw: "sum ?f ({b} \<union> (UNIV - {a} - {b})) = sum ?f {b} + sum ?f (UNIV - {a} - {b})" by (rule sum.union_disjoint, auto simp add: False)
    have "sum ?f UNIV = sum ?f ({a} \<union> ({b} \<union> (UNIV - {a} - {b})))" using univ_rw by simp
    also have "... = sum ?f {a} + sum ?f ({b} \<union> (UNIV - {a} - {b}))" by (rule sum.union_disjoint, auto simp add: False)
    also have "... = sum ?f {a} + sum ?f {b} + sum ?f (UNIV - {a} - {b})" 
      unfolding sum_rw add.assoc[symmetric] ..
    also have "... = sum ?f {a} + sum ?f {b}" unfolding mat_def by auto    
    also have "... =  A $ i $ a + A $ i $ b * q" using False unfolding mat_def by simp
    finally show ?thesis .
  qed    
  fix j
  assume j_noteq_a: "j\<noteq>a"
  show "(\<Sum>k\<in>UNIV. A $ i $ k * mat (1::'a) $ k $ j) = A $ i $ j"
  proof -
    let ?f="\<lambda>k. A $ i $ k * mat (1::'a) $ k $ j"
    have univ_rw:"UNIV = (UNIV-{j}) \<union> {j}" by auto
    have "sum ?f UNIV = sum ?f ((UNIV-{j}) \<union> {j})" using univ_rw by auto
    also have "... = sum ?f (UNIV-{j}) + sum ?f {j}" by (rule sum.union_disjoint, auto)
    also have "... = sum ?f {j}" unfolding mat_def by auto
    also have "... =  A $ i $ j" unfolding mat_def by simp
    finally show ?thesis .
  qed
qed


lemma invertible_column_add:
  assumes a_noteq_b: "a\<noteq>b"
  shows "invertible (column_add (mat (1::'a::{ring_1})) a b q)"
proof (unfold invertible_def, rule exI[of _ "(column_add (mat 1) a b (-q))"], rule conjI)
  show " column_add (mat (1::'a)) a b q ** column_add (mat (1::'a)) a b (- q) = mat (1::'a)"  using a_noteq_b
  proof (unfold matrix_matrix_mult_def, vector, clarify, unfold column_add_def, vector, unfold mat_1_fun, auto)
    show " (\<Sum>k\<in>UNIV. (if k = a then (0::'a) + (1::'a) * q else if b = k then 1::'a else (0::'a)) * (if k = b then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k.  (if k = a then (0::'a) + (1::'a) * q else if b = k then 1::'a else (0::'a)) * (if k = b then 1::'a else (0::'a))"
      have univ_rw:"UNIV = (UNIV-{b}) \<union> {b}" by auto
      have "sum ?f UNIV = sum ?f ((UNIV-{b}) \<union> {b})" using univ_rw by auto
      also have "... = sum ?f (UNIV-{b}) + sum ?f {b}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {b}" by auto 
      also have "... =  1" using a_noteq_b by simp
      finally show ?thesis .
    qed
    show "(\<Sum>k\<in>UNIV. (if k = a then 1 + 0 * q else if a = k then 1 else 0) * ((if k = a then 1 else 0) - (if k = b then 1 else 0) * q)) = 1"
    proof -
      let ?f="\<lambda>k. (if k = a then (1::'a) + (0::'a) * q else if a = k then 1::'a else (0::'a)) * ((if k = a then 1::'a else (0::'a)) + - ((if k = b then 1::'a else (0::'a)) * q))"
      have univ_rw:"UNIV = (UNIV-{a}) \<union> {a}" by auto
      have "sum ?f UNIV = sum ?f ((UNIV-{a}) \<union> {a})" using univ_rw by auto
      also have "... = sum ?f (UNIV-{a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {a}" by auto 
      also have "... =  1" using a_noteq_b by simp
      finally show ?thesis by simp
    qed  
    fix i j
    assume i_not_b: "i \<noteq> b" and i_not_a: "i \<noteq> a" and i_not_j: "i \<noteq> j"
    show "(\<Sum>k\<in>UNIV. (if k = a then (0::'a) + (0::'a) * q else if i = k then 1::'a else (0::'a)) *
      (if j = a then (if k = a then 1::'a else (0::'a)) + (if k = b then 1::'a else (0::'a)) * - q else if k = j then 1::'a else (0::'a))) = (0::'a)"
      by (rule sum.neutral, auto simp add: i_not_b i_not_a i_not_j)
  next
    fix j
    assume a_not_j: "a\<noteq>j"
    show " (\<Sum>k\<in>UNIV. (if k = a then (1::'a) + (0::'a) * q else if a = k then 1::'a else (0::'a)) * (if k = j then 1::'a else (0::'a))) = (0::'a)"
      apply (rule sum.neutral) using a_not_j a_noteq_b by auto
  next
    fix j
    assume j_not_b: "j \<noteq> b" and j_not_a: "j \<noteq> a"
    show " (\<Sum>k\<in>UNIV. (if k = a then (0::'a) + (0::'a) * q else if j = k then 1::'a else (0::'a)) * (if k = j then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k. (if k = a then (0::'a) + (0::'a) * q else if j = k then 1::'a else (0::'a)) * (if k = j then 1::'a else (0::'a))"
      have univ_rw:"UNIV = (UNIV-{j}) \<union> {j}" by auto
      have "sum ?f UNIV = sum ?f ((UNIV-{j}) \<union> {j})" using univ_rw by auto
      also have "... = sum ?f (UNIV-{j}) + sum ?f {j}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {j}" using j_not_b j_not_a by auto 
      also have "... =  1" using j_not_b j_not_a by auto 
      finally show ?thesis .
    qed
  next
    fix j
    assume b_not_j: "b \<noteq> j"
    show "(\<Sum>k\<in>UNIV. (if k = a then 0 + 1 * q else if b = k then 1 else 0) *
      (if j = a then (if k = a then 1 else 0) + (if k = b then 1 else 0) * - q else if k = j then 1 else 0)) = 0"
    proof (cases "j=a")
      case False
      show ?thesis by (rule sum.neutral, auto simp add: False b_not_j)
    next
      case True \<comment> \<open>This case is different from the other cases\<close>
      let ?f="\<lambda>k. (if k = a then 0 + 1 * q else if b = k then 1 else 0) *
        (if j = a then (if k = a then 1 else 0) + (if k = b then 1 else 0) * - q else if k = j then 1 else 0)"
      have univ_eq: "UNIV = ((UNIV - {a}- {b}) \<union> ({b} \<union> {a}))" by auto
      have sum_a: "sum ?f {a} = q"  unfolding True using b_not_j using a_noteq_b by auto
      have sum_b: "sum ?f {b} = -q" unfolding True using b_not_j using a_noteq_b by auto
      have sum_rest: "sum ?f (UNIV - {a} - {b}) = 0"  by (rule sum.neutral, auto simp add: True b_not_j a_noteq_b)
      have "sum ?f UNIV = sum ?f ((UNIV - {a}- {b}) \<union> ({b} \<union> {a}))"  using univ_eq by simp
      also have "... = sum ?f (UNIV - {a} - {b}) + sum ?f ({b} \<union> {a})" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f (UNIV - {a} - {b}) + sum ?f {b} + sum ?f {a}" by (auto simp add: sum.union_disjoint a_noteq_b)     
      also have "... = 0" unfolding sum_a sum_b sum_rest by simp
      finally show ?thesis .
    qed                        
  qed
next
  show " column_add (mat (1::'a)) a b (- q) ** column_add (mat (1::'a)) a b q = mat (1::'a)" using a_noteq_b
  proof (unfold matrix_matrix_mult_def, vector, clarify, unfold column_add_def, vector, unfold mat_1_fun, auto)
    show "(\<Sum>k\<in>UNIV. (if k = a then (0::'a) + (1::'a) * - q else if b = k then 1::'a else (0::'a)) * (if k = b then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k. (if k = a then (0::'a) + (1::'a) * - q else if b = k then 1::'a else (0::'a)) * (if k = b then 1::'a else (0::'a))"
      have univ_rw:"UNIV = (UNIV-{b}) \<union> {b}" by auto
      have "sum ?f UNIV = sum ?f ((UNIV-{b}) \<union> {b})" using univ_rw by auto
      also have "... = sum ?f (UNIV-{b}) + sum ?f {b}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {b}" by auto 
      also have "... =  1" using a_noteq_b by auto
      finally show ?thesis .
    qed
  next
    show "(\<Sum>k\<in>UNIV. (if k = a then (1::'a) + (0::'a) * - q else if a = k then 1::'a else (0::'a)) * ((if k = a then 1::'a else (0::'a)) + (if k = b then 1::'a else (0::'a)) * q)) =
      (1::'a)"
    proof -
      let ?f="\<lambda>k. (if k = a then (1::'a) + (0::'a) * - q else if a = k then 1::'a else (0::'a)) * ((if k = a then 1::'a else (0::'a)) + (if k = b then 1::'a else (0::'a)) * q) "
      have univ_rw:"UNIV = (UNIV-{a}) \<union> {a}" by auto
      have "sum ?f UNIV = sum ?f ((UNIV-{a}) \<union> {a})" using univ_rw by auto
      also have "... = sum ?f (UNIV-{a}) + sum ?f {a}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {a}" by auto 
      also have "... =  1" using a_noteq_b by auto
      finally show ?thesis .
    qed
  next
    fix j
    assume a_not_j: "a \<noteq> j" show "(\<Sum>k\<in>UNIV. (if k = a then (1::'a) + (0::'a) * - q else if a = k then 1::'a else (0::'a)) * (if k = j then 1::'a else (0::'a))) = (0::'a)"
      apply (rule sum.neutral) using a_not_j by auto
  next
    fix j
    assume j_not_b: "j \<noteq> b" and j_not_a: "j \<noteq> a" 
    show "(\<Sum>k\<in>UNIV. (if k = a then (0::'a) + (0::'a) * - q else if j = k then 1::'a else (0::'a)) * (if k = j then 1::'a else (0::'a))) = (1::'a)"
    proof -
      let ?f="\<lambda>k.(if k = a then (0::'a) + (0::'a) * - q else if j = k then 1::'a else (0::'a)) * (if k = j then 1::'a else (0::'a))"
      have univ_rw:"UNIV = (UNIV-{j}) \<union> {j}" by auto
      have "sum ?f UNIV = sum ?f ((UNIV-{j}) \<union> {j})" using univ_rw by auto
      also have "... = sum ?f (UNIV-{j}) + sum ?f {j}" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f {j}" by auto 
      also have "... =  1" using a_noteq_b j_not_b j_not_a by auto
      finally show ?thesis .
    qed
  next
    fix i j
    assume i_not_b: "i \<noteq> b" and i_not_a: "i \<noteq> a" and i_not_j: "i \<noteq> j"
    show "(\<Sum>k\<in>UNIV. (if k = a then (0::'a) + (0::'a) * - q else if i = k then 1::'a else (0::'a)) *
      (if j = a then (if k = a then 1::'a else (0::'a)) + (if k = b then 1::'a else (0::'a)) * q else if k = j then 1::'a else (0::'a))) = (0::'a)"
      by (rule sum.neutral, auto simp add: i_not_b i_not_a i_not_j)
  next
    fix j
    assume b_not_j: "b \<noteq> j"
    show "(\<Sum>k\<in>UNIV. (if k = a then (0::'a) + (1::'a) * - q else if b = k then 1::'a else (0::'a)) *
      (if j = a then (if k = a then 1::'a else (0::'a)) + (if k = b then 1::'a else (0::'a)) * q else if k = j then 1::'a else (0::'a))) = 0"
    proof (cases "j=a")
      case False
      show ?thesis by (rule sum.neutral, auto simp add: False b_not_j)
    next
      case True \<comment> \<open>This case is different from the other cases\<close>
      let ?f="\<lambda>k. (if k = a then (0::'a) + (1::'a) * - q else if b = k then 1::'a else (0::'a)) *
        (if j = a then (if k = a then 1::'a else (0::'a)) + (if k = b then 1::'a else (0::'a)) * q else if k = j then 1::'a else (0::'a))"
      have univ_eq: "UNIV = ((UNIV - {a}- {b}) \<union> ({b} \<union> {a}))" by auto
      have sum_a: "sum ?f {a} = -q"  unfolding True using b_not_j using a_noteq_b by auto
      have sum_b: "sum ?f {b} = q" unfolding True using b_not_j using a_noteq_b by auto
      have sum_rest: "sum ?f (UNIV - {a} - {b}) = 0"  by (rule sum.neutral, auto simp add: True b_not_j a_noteq_b)
      have "sum ?f UNIV = sum ?f ((UNIV - {a}- {b}) \<union> ({b} \<union> {a}))"  using univ_eq by simp
      also have "... = sum ?f (UNIV - {a} - {b}) + sum ?f ({b} \<union> {a})" by (rule sum.union_disjoint, auto)
      also have "... = sum ?f (UNIV - {a} - {b}) + sum ?f {b} + sum ?f {a}" by (auto simp add: sum.union_disjoint a_noteq_b)     
      also have "... = 0" unfolding sum_a sum_b sum_rest by simp
      finally show ?thesis .
    qed                   
  qed
qed

subsection\<open>Relationships amongst the definitions\<close>

text\<open>Relationships between @{term "interchange_rows"} and @{term "interchange_columns"}\<close>

lemma interchange_rows_transpose:
  shows "interchange_rows (transpose A) a b = transpose (interchange_columns A a b)"
  unfolding interchange_rows_def interchange_columns_def transpose_def by vector

lemma interchange_rows_transpose':
  shows "interchange_rows A a b = transpose (interchange_columns (transpose A) a b)"
  unfolding interchange_rows_def interchange_columns_def transpose_def by vector

lemma interchange_columns_transpose:
  shows "interchange_columns (transpose A) a b = transpose (interchange_rows A a b)"
  unfolding interchange_rows_def interchange_columns_def transpose_def by vector

lemma interchange_columns_transpose':
  shows "interchange_columns A a b = transpose (interchange_rows (transpose A) a b)"
  unfolding interchange_rows_def interchange_columns_def transpose_def by vector

subsection\<open>Code Equations\<close>
text\<open>Code equations for @{thm interchange_rows_def}, @{thm interchange_columns_def}, @{thm row_add_def}, @{thm column_add_def}, 
@{thm mult_row_def} and @{thm mult_column_def}:\<close>

definition interchange_rows_row 
  where "interchange_rows_row A a b i = vec_lambda (%j. if i = a then A $ b $ j else if i = b then A $ a $ j else A $ i $ j)"

lemma interchange_rows_code [code abstract]:
  "vec_nth (interchange_rows_row A a b i) = (%j. if i = a then A $ b $ j else if i = b then A $ a $ j else A $ i $ j)"
  unfolding interchange_rows_row_def by auto 

lemma interchange_rows_code_nth [code abstract]: "vec_nth (interchange_rows A a b) = interchange_rows_row A a b"
  unfolding interchange_rows_def unfolding interchange_rows_row_def[abs_def]
  by auto

definition interchange_columns_row 
  where "interchange_columns_row A n m i = vec_lambda (%j.  if j = n then A $ i $ m else if j = m then A $ i $ n else A $ i $ j)"

lemma interchange_columns_code [code abstract]:
  "vec_nth (interchange_columns_row A n m i) = (%j.  if j = n then A $ i $ m else if j = m then A $ i $ n else A $ i $ j)"
  unfolding interchange_columns_row_def by auto 

lemma interchange_columns_code_nth [code abstract]: "vec_nth (interchange_columns A a b) = interchange_columns_row A a b"
  unfolding interchange_columns_def unfolding interchange_columns_row_def[abs_def]
  by auto

definition row_add_row 
  where "row_add_row A a b q i = vec_lambda (%j. if i = a then A $ a $ j + q * A $ b $ j else A $ i $ j)"

lemma row_add_code [code abstract]:
  "vec_nth (row_add_row A a b q i) =  (%j. if i = a then A $ a $ j + q * A $ b $ j else A $ i $ j)"
  unfolding row_add_row_def by auto 

lemma row_add_code_nth [code abstract]: "vec_nth (row_add A a b q) = row_add_row A a b q"
  unfolding row_add_def unfolding row_add_row_def[abs_def]
  by auto

definition column_add_row 
  where "column_add_row  A n m q i = vec_lambda (%j. if j = n then A $ i $ n + A $ i $ m * q else A $ i $ j)"

lemma column_add_code [code abstract]:
  "vec_nth (column_add_row A n m q i) =  (%j. if j = n then A $ i $ n + A $ i $ m * q else A $ i $ j)"
  unfolding column_add_row_def by auto

lemma column_add_code_nth [code abstract]: "vec_nth (column_add A a b q) = column_add_row A a b q"
  unfolding column_add_def unfolding column_add_row_def[abs_def]
  by auto

definition mult_row_row 
  where "mult_row_row A a q i = vec_lambda (%j. if i = a then q * A $ a $ j else A $ i $ j)"

lemma mult_row_code [code abstract]:
  "vec_nth (mult_row_row A a q i) = (%j. if i = a then q * A $ a $ j else A $ i $ j)"
  unfolding mult_row_row_def by auto

lemma mult_row_code_nth [code abstract]: "vec_nth (mult_row A a q) = mult_row_row A a q"
  unfolding mult_row_def unfolding mult_row_row_def[abs_def]
  by auto

definition mult_column_row 
  where "mult_column_row A n q i = vec_lambda (%j. if j = n then A $ i $ j * q else A $ i $ j)"

lemma mult_column_code [code abstract]:
  "vec_nth (mult_column_row A n q i) = (%j. if j = n then A $ i $ j * q else A $ i $ j)"
  unfolding mult_column_row_def by auto

lemma mult_column_code_nth [code abstract]: "vec_nth (mult_column A a q) = mult_column_row A a q"
  unfolding mult_column_def unfolding mult_column_row_def[abs_def]
  by auto


end
