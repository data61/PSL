(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Enumerations of Well-Ordered Sets in Increasing Order\<close>

theory Least_Enum
imports Main
begin
  
locale infinitely_many1 =
  fixes P :: "'a :: wellorder \<Rightarrow> bool"
  assumes infm: "\<forall>i. \<exists>j>i. P j"
begin

text \<open>
  Enumerate the elements of a well-ordered infinite set in increasing order.
\<close>
fun enum :: "nat \<Rightarrow> 'a" where
  "enum 0 = (LEAST n. P n)" |
  "enum (Suc i) = (LEAST n. n > enum i \<and> P n)"

lemma enum_mono:
  shows "enum i < enum (Suc i)"
  using infm by (cases i, auto) (metis (lifting) LeastI)+

lemma enum_less:
  "i < j \<Longrightarrow> enum i < enum j"
  using enum_mono by (metis lift_Suc_mono_less)

lemma enum_P:
  shows "P (enum i)"
  using infm by (cases i, auto) (metis (lifting) LeastI)+

end

locale infinitely_many2 =
  fixes P :: "'a :: wellorder \<Rightarrow> 'a \<Rightarrow> bool"
    and N :: "'a"
  assumes infm: "\<forall>i\<ge>N. \<exists>j>i. P i j"
begin

text \<open>
  Enumerate the elements of a well-ordered infinite set that form a chain w.r.t.\ a given predicate
  @{term P} starting from a given index @{term N} in increasing order.
\<close>
fun enumchain :: "nat \<Rightarrow> 'a" where
  "enumchain 0 = N" |
  "enumchain (Suc n) = (LEAST m. m > enumchain n \<and> P (enumchain n) m)"

lemma enumchain_mono:
  shows "N \<le> enumchain i \<and> enumchain i < enumchain (Suc i)"
proof (induct i)
  case 0
  have "enumchain 0 \<ge> N" by simp
  moreover then have "\<exists>m>enumchain 0. P (enumchain 0) m" using infm by blast
  ultimately show ?case by auto (metis (lifting) LeastI)
next
  case (Suc i)
  then have "N \<le> enumchain (Suc i)" by auto
  moreover then have "\<exists>m>enumchain (Suc i). P (enumchain (Suc i)) m" using infm by blast
  ultimately show ?case by (auto) (metis (lifting) LeastI)
qed

lemma enumchain_chain:
  shows "P (enumchain i) (enumchain (Suc i))"
proof (cases i)
  case 0
  moreover have "\<exists>m>enumchain 0. P (enumchain 0) m" using infm by auto
  ultimately show ?thesis by auto (metis (lifting) LeastI)
next
  case (Suc i)
  moreover have "enumchain (Suc i) > N" using enumchain_mono by (metis le_less_trans)
  moreover then have "\<exists>m>enumchain (Suc i). P (enumchain (Suc i)) m" using infm by auto
  ultimately show ?thesis by (auto) (metis (lifting) LeastI)
qed

end

end

