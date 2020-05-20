(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

theory Sorted_Wrt
  imports Main
begin

lemma sorted_wrt_filter:
  "sorted_wrt P xs \<Longrightarrow> sorted_wrt P (filter Q xs)"
  by (induct xs) (auto)

lemma sorted_wrt_map_mono:
  assumes "sorted_wrt Q xs"
    and "\<And>x y. Q x y \<Longrightarrow> P (f x) (f y)"
  shows "sorted_wrt P (map f xs)"
  using assms by (induct xs) (auto)

lemma sorted_wrt_concat_map_map:
  assumes "sorted_wrt Q xs"
    and "sorted_wrt Q ys"
    and "\<And>a x y. Q x y \<Longrightarrow> P (f x a) (f y a)"
    and "\<And>x y u v. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> Q u v \<Longrightarrow> P (f x u) (f y v)"
  shows "sorted_wrt P [f x y . y \<leftarrow> ys, x \<leftarrow> xs]"
  using assms by (induct ys)
    (auto simp: sorted_wrt_append intro: sorted_wrt_map_mono [of Q])

lemma sorted_wrt_concat_map:
  assumes "sorted_wrt P (map h xs)"
    and "\<And>x. x \<in> set xs \<Longrightarrow> sorted_wrt P (map h (f x))"
    and "\<And>x y u v. P (h x) (h y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> u \<in> set (f x) \<Longrightarrow> v \<in> set (f y) \<Longrightarrow> P (h u) (h v)"
  shows "sorted_wrt P (concat (map (map h \<circ> f) xs))"
  using assms by (induct xs) (auto simp: sorted_wrt_append)

lemma sorted_wrt_map_distr:
  assumes "sorted_wrt (\<lambda>x y. P x y) (map f xs)"
  shows "sorted_wrt (\<lambda>x y. P (f x) (f y)) xs"
  using assms
  by (induct xs) (auto)

lemma sorted_wrt_tl:
  "xs \<noteq> [] \<Longrightarrow> sorted_wrt P xs \<Longrightarrow> sorted_wrt P (tl xs)"
  by (cases xs) (auto)

end
