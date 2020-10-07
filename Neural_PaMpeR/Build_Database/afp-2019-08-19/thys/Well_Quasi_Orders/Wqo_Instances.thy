(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Instances of Well-Quasi-Orders\<close>

theory Wqo_Instances
imports Kruskal
begin


subsection \<open>The Option Type is Well-Quasi-Ordered\<close>

instantiation option :: (wqo) wqo
begin
definition "x \<le> y \<longleftrightarrow> option_le (\<le>) x y"
definition "(x :: 'a option) < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_option_def [abs_def] less_option_def [abs_def])
end


subsection \<open>The Sum Type is Well-Quasi-Ordered\<close>

instantiation sum :: (wqo, wqo) wqo
begin
definition "x \<le> y \<longleftrightarrow> sum_le (\<le>) (\<le>) x y"
definition "(x :: 'a + 'b) < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_sum_def [abs_def] less_sum_def [abs_def])
end


subsection \<open>Pairs are Well-Quasi-Ordered\<close>

text \<open>If types @{typ "'a"} and @{typ "'b"} are well-quasi-ordered by \<open>P\<close>
and \<open>Q\<close>, then pairs of type @{typ "'a \<times> 'b"} are well-quasi-ordered by
the pointwise combination of \<open>P\<close> and \<open>Q\<close>.\<close>

instantiation prod :: (wqo, wqo) wqo
begin
definition "p \<le> q \<longleftrightarrow> prod_le (\<le>) (\<le>) p q"
definition "(p :: 'a \<times> 'b) < q \<longleftrightarrow> p \<le> q \<and> \<not> (q \<le> p)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_prod_def [abs_def] less_prod_def [abs_def])
end


subsection \<open>Lists are Well-Quasi-Ordered\<close>

text \<open>If the type @{typ "'a"} is well-quasi-ordered by \<open>P\<close>, then
lists of type @{typ "'a list"} are well-quasi-ordered by the homeomorphic
embedding relation.\<close>

instantiation list :: (wqo) wqo
begin
definition "xs \<le> ys \<longleftrightarrow> list_emb (\<le>) xs ys"
definition "(xs :: 'a list) < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> (ys \<le> xs)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_list_def [abs_def] less_list_def [abs_def])
end

end

