theory Term_Utils
imports
  "HOL-Library.Finite_Map"
  "HOL-Library.Monad_Syntax"
  "HOL-Library.State_Monad"
begin

fun map2 where
"map2 f (x # xs) (y # ys) = f x y # map2 f xs ys" |
"map2 _ _ _ = []"

lemma map2_elemE:
  assumes "z \<in> set (map2 f xs ys)"
  obtains x y where "x \<in> set xs" "y \<in> set ys" "z = f x y"
using assms by (induct f xs ys rule: map2.induct) auto

lemma map2_elemE1:
  assumes "length xs = length ys" "x \<in> set xs"
  obtains y where "y \<in> set ys" "f x y \<in> set (map2 f xs ys)"
using assms by (induct xs ys rule: list_induct2) auto

lemma map2_elemE2:
  assumes "length xs = length ys" "y \<in> set ys"
  obtains x where "x \<in> set xs" "f x y \<in> set (map2 f xs ys)"
using assms by (induct xs ys rule: list_induct2) auto

lemma map2_cong[fundef_cong]:
  assumes "xs1 = xs2" "ys1 = ys2"
  assumes fg: "\<And>x y. x \<in> set xs1 \<Longrightarrow> y \<in> set ys1 \<Longrightarrow> f x y = g x y"
  shows "map2 f xs1 ys1 = map2 g xs2 ys2"
proof -
  have "map2 f xs1 ys1 = map2 g xs1 ys1"
    using fg
    by (induction f xs1 ys1 rule: map2.induct) auto
  with assms show ?thesis
    by simp
qed

lemma option_bindE:
  assumes "x \<bind> f = Some a"
  obtains x' where "x = Some x'"  "f x' = Some a"
using assms
by (cases x) auto

lemma rel_option_bind[intro]:
  assumes "rel_option R x y" "\<And>a b. R a b \<Longrightarrow> rel_option R (f a) (g b)"
  shows "rel_option R (x \<bind> f) (y \<bind> g)"
using assms(1) proof (cases rule: option.rel_cases)
  case None
  thus ?thesis
    by simp
next
  case (Some a b)
  thus ?thesis
    using assms(2) by simp
qed

lemma list_split:
  assumes "n < length xs"
  obtains xs\<^sub>1 xs\<^sub>2 where "xs = xs\<^sub>1 @ xs\<^sub>2" "n = length xs\<^sub>2" "0 < length xs\<^sub>1"
proof
  let ?xs\<^sub>1 = "take (length xs - n) xs"
  let ?xs\<^sub>2 = "drop (length xs - n) xs"

  show "xs = ?xs\<^sub>1 @ ?xs\<^sub>2"
    by simp
  show "n = length ?xs\<^sub>2" "0 < length ?xs\<^sub>1"
    using assms by auto
qed

context
  includes fset.lifting
begin

lemma ffUnion_alt_def: "x |\<in>| ffUnion A \<longleftrightarrow> fBex A (\<lambda>X. x |\<in>| X)"
by transfer blast

lemma funion_image_bind_eq: "ffUnion (f |`| M) = fbind M f"
by transfer auto

lemma fbind_funion: "fbind (M |\<union>| N) f = fbind M f |\<union>| fbind N f"
by transfer' auto

lemma ffUnion_least: "fBall A (\<lambda>X. X |\<subseteq>| C) \<Longrightarrow> ffUnion A |\<subseteq>| C"
by transfer blast

lemma fbind_iff: "x |\<in>| fbind S f \<longleftrightarrow> (\<exists>s. x |\<in>| f s \<and> s |\<in>| S)"
  by transfer' auto

lemma fBall_pred_weaken: "(\<And>x. x |\<in>| M \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> fBall M P \<Longrightarrow> fBall M Q"
by auto

end

lemma fmmap_fmupd[simp]:
  "fmmap f (fmupd k v m) = fmupd k (f v) (fmmap f m)"
apply (rule fmap_ext)
by auto

definition fmlookup_default :: "('a, 'b) fmap \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"fmlookup_default m f x = (case fmlookup m x of None \<Rightarrow> f x | Some b \<Rightarrow> b)"

end
