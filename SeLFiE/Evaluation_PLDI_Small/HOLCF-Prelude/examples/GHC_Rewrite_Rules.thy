section \<open>GHC's "fold/build" Rule\<close>

theory GHC_Rewrite_Rules
  imports "../HOLCF_Prelude"
begin

subsection \<open>Approximating the Rewrite Rule\<close>

text \<open>
  The original rule looks as follows (see also \cite{ghc-rewriting}):
  \begin{verbatim}
  "fold/build"
    forall k z (g :: forall b. (a -> b -> b) -> b -> b).
    foldr k z (build g) = g k z
  \end{verbatim}
  Since we do not have rank-2 polymorphic types in Isabelle/HOL, we try to imitate a similar
  statement by introducing a new type that combines possible folds with their argument lists, i.e.,
  @{term f} below is a function that, in a way, represents the list @{term xs}, but where list
  constructors are functionally abstracted.
\<close>

abbreviation (input) abstract_list where
  "abstract_list xs \<equiv> (\<Lambda> c n. foldr\<cdot>c\<cdot>n\<cdot>xs)"

cpodef ('a, 'b) listfun =
  "{(f :: ('a \<rightarrow> 'b \<rightarrow> 'b) \<rightarrow> 'b \<rightarrow> 'b, xs). f = abstract_list xs}"
  by auto

definition listfun :: "('a, 'b) listfun \<rightarrow> ('a \<rightarrow> 'b \<rightarrow> 'b) \<rightarrow> 'b \<rightarrow> 'b" where
  "listfun = (\<Lambda> g. Product_Type.fst (Rep_listfun g))"

definition build :: "('a, 'b) listfun \<rightarrow> ['a]" where
  "build = (\<Lambda> g. Product_Type.snd (Rep_listfun g))"

definition augment :: "('a, 'b) listfun \<rightarrow> ['a] \<rightarrow> ['a]" where
  "augment = (\<Lambda> g xs. build\<cdot>g ++ xs)"

definition listfun_comp :: "('a, 'b) listfun \<rightarrow> ('a, 'b) listfun \<rightarrow> ('a, 'b) listfun" where
  "listfun_comp = (\<Lambda> g h.
    Abs_listfun (\<Lambda> c n. listfun\<cdot>g\<cdot>c\<cdot>(listfun\<cdot>h\<cdot>c\<cdot>n), build\<cdot>g ++ build\<cdot>h))"

abbreviation
  listfun_comp_infix :: "('a, 'b) listfun \<Rightarrow> ('a, 'b) listfun \<Rightarrow> ('a, 'b) listfun" (infixl "\<circ>lf" 55)
  where
    "g \<circ>lf h \<equiv> listfun_comp\<cdot>g\<cdot>h"

fixrec mapFB :: "('b \<rightarrow> 'c \<rightarrow> 'c) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'c \<rightarrow> 'c" where
  "mapFB\<cdot>c\<cdot>f = (\<Lambda> x ys. c\<cdot>(f\<cdot>x)\<cdot>ys)"


subsection \<open>Lemmas\<close>

lemma cont_listfun_body [simp]:
  "cont (\<lambda>g. Product_Type.fst (Rep_listfun g))"
  by (simp add: cont_Rep_listfun)

lemma cont_build_body [simp]:
  "cont (\<lambda>g. Product_Type.snd (Rep_listfun g))"
  by (simp add: cont_Rep_listfun)

lemma build_Abs_listfun:
  assumes "abstract_list xs = f"
  shows "build\<cdot>(Abs_listfun (f, xs)) = xs"
  using assms and Abs_listfun_inverse [of "(f, xs)"]
  by (simp add: build_def)

lemma listfun_Abs_listfun [simp]:
  assumes "abstract_list xs = f"
  shows "listfun\<cdot>(Abs_listfun (f, xs)) = f"
  using assms and Abs_listfun_inverse [of "(f, xs)"]
  by (simp add: listfun_def)

lemma augment_Abs_listfun [simp]:
  assumes "abstract_list xs = f"
  shows "augment\<cdot>(Abs_listfun (f, xs))\<cdot>ys = xs ++ ys"
  using assms and Abs_listfun_inverse [of "(f, xs)"]
  by (simp add: augment_def build_Abs_listfun)

lemma cont_augment_body [simp]:
  "cont (\<lambda>g. Abs_cfun ((++) (Product_Type.snd (Rep_listfun g))))"
  by (simp add: cont_Rep_listfun)

lemma "fold/build":
  fixes g :: "('a, 'b) listfun"
  shows "foldr\<cdot>k\<cdot>z\<cdot>(build\<cdot>g) = listfun\<cdot>g\<cdot>k\<cdot>z"
proof -
  from Rep_listfun obtain f xs where
    "Rep_listfun g = (f, xs)" and "f = abstract_list xs" by blast
  then show ?thesis by (simp add: build_def listfun_def)
qed

lemma "foldr/augment":
  fixes g :: "('a, 'b) listfun"
  shows "foldr\<cdot>k\<cdot>z\<cdot>(augment\<cdot>g\<cdot>xs) = listfun\<cdot>g\<cdot>k\<cdot>(foldr\<cdot>k\<cdot>z\<cdot>xs)"
proof -
  from Rep_listfun obtain f ys where
    "Rep_listfun g = (f, ys)" and "f = abstract_list ys" by blast
  then show ?thesis
    by (simp add: augment_def build_def listfun_def)
qed

lemma "foldr/id":
  "foldr\<cdot>(:)\<cdot>[] = (\<Lambda> x. x)"
proof (rule cfun_eqI)
  fix xs :: "['a]"
  show "foldr\<cdot>(:)\<cdot>[]\<cdot>xs = (\<Lambda> x. x)\<cdot>xs"
    by (induction xs) simp+
qed

lemma "foldr/app":
  "foldr\<cdot>(:)\<cdot>ys = (\<Lambda> xs. xs ++ ys)"
proof (rule cfun_eqI)
  fix xs :: "['a]"
  show "foldr\<cdot>(:)\<cdot>ys\<cdot>xs = (\<Lambda> xs. xs ++ ys)\<cdot>xs" by (induct xs) simp+
qed

lemma "foldr/cons": "foldr\<cdot>k\<cdot>z\<cdot>(x:xs) = k\<cdot>x\<cdot>(foldr\<cdot>k\<cdot>z\<cdot>xs)" by simp
lemma "foldr/single": "foldr\<cdot>k\<cdot>z\<cdot>[x] = k\<cdot>x\<cdot>z" by simp
lemma "foldr/nil": "foldr\<cdot>k\<cdot>z\<cdot>[] = z" by simp

lemma cont_listfun_comp_body1 [simp]:
  "cont (\<lambda>h. Abs_listfun (\<Lambda> c n. listfun\<cdot>g\<cdot>c\<cdot>(listfun\<cdot>h\<cdot>c\<cdot>n), build\<cdot>g ++ build\<cdot>h))"
proof -
  have "\<And>h.
    (\<Lambda> c n. listfun\<cdot>g\<cdot>c\<cdot>(listfun\<cdot>h\<cdot>c\<cdot>n), build\<cdot>g ++ build\<cdot>h) \<in> {(f, xs). f = abstract_list xs}"
    by (simp add: "fold/build")
  from cont_Abs_listfun [OF this, of "\<lambda>x. x"]
  show ?thesis by simp
qed

lemma cont_listfun_comp_body2 [simp]:
  "cont (\<lambda>g. Abs_listfun (\<Lambda> c n. listfun\<cdot>g\<cdot>c\<cdot>(listfun\<cdot>h\<cdot>c\<cdot>n), build\<cdot>g ++ build\<cdot>h))"
proof -
  have "\<And>g.
    (\<Lambda> c n. listfun\<cdot>g\<cdot>c\<cdot>(listfun\<cdot>h\<cdot>c\<cdot>n), build\<cdot>g ++ build\<cdot>h) \<in> {(f, xs). f = abstract_list xs}"
    by (simp add: "fold/build")
  from cont_Abs_listfun [OF this, of "\<lambda>x. x"]
  show ?thesis by simp
qed

lemma cont_listfun_comp_body [simp]:
  "cont (\<lambda>g. \<Lambda> h. Abs_listfun (\<Lambda> c n. listfun\<cdot>g\<cdot>c\<cdot>(listfun\<cdot>h\<cdot>c\<cdot>n), build\<cdot>g ++ build\<cdot>h))"
  by (rule cont2cont_LAM) simp+

lemma abstract_list_build_append:
  "abstract_list (build\<cdot>g ++ build\<cdot>h) = (\<Lambda> c n. listfun\<cdot>g\<cdot>c\<cdot>(listfun\<cdot>h\<cdot>c\<cdot>n))"
  by (intro cfun_eqI) (simp add: "fold/build")

lemma "augment/build":
  "augment\<cdot>g\<cdot>(build\<cdot>h) = build\<cdot>(g \<circ>lf h)"
  by (simp add: listfun_comp_def augment_def build_Abs_listfun [OF abstract_list_build_append])

lemma "augment/nil":
  "augment\<cdot>g\<cdot>[] = build\<cdot>g"
  by (simp add: augment_def)

lemma build_listfun_comp [simp]:
  "build\<cdot>(g \<circ>lf h) = build\<cdot>g ++ build\<cdot>h"
  unfolding "augment/build" [symmetric]
  by (simp add: augment_def)

lemma augment_augment:
  "augment\<cdot>g\<cdot>(augment\<cdot>h\<cdot>xs) = augment\<cdot>(g \<circ>lf h)\<cdot>xs"
  by (simp add: augment_def)

lemma abstract_list_map [simp]:
  "abstract_list (map\<cdot>f\<cdot>xs) = (\<Lambda> c n. foldr\<cdot>(mapFB\<cdot>c\<cdot>f)\<cdot>n\<cdot>xs)"
  by (intro cfun_eqI, induct xs) simp+

lemma "map":
  "map\<cdot>f\<cdot>xs = build\<cdot>(Abs_listfun (\<Lambda> c n. foldr\<cdot>(mapFB\<cdot>c\<cdot>f)\<cdot>n\<cdot>xs, map\<cdot>f\<cdot>xs))"
  by (simp add: build_Abs_listfun)

lemma "mapList":
  "foldr\<cdot>(mapFB\<cdot>(:)\<cdot>f)\<cdot>[] = map\<cdot>f"
  by (rule cfun_eqI, rename_tac x, induct_tac x) simp+

lemma "mapFB":
  "mapFB\<cdot>(mapFB\<cdot>c\<cdot>f)\<cdot>g = mapFB\<cdot>c\<cdot>(f oo g)"
  by simp

lemma "++":
  "xs ++ ys = augment\<cdot>(Abs_listfun (abstract_list xs, xs))\<cdot>ys"
  by simp

subsection \<open>Examples\<close>

fixrec sum :: "[Integer] \<rightarrow> Integer" where
  "sum\<cdot>xs = foldr\<cdot>(+)\<cdot>0\<cdot>xs"

fixrec down' :: "Integer \<rightarrow> (Integer \<rightarrow> 'a \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> 'a" where
  "down'\<cdot>v\<cdot>c\<cdot>n = If le\<cdot>1\<cdot>v then c\<cdot>v\<cdot>(down'\<cdot>(v - 1)\<cdot>c\<cdot>n) else n"
declare down'.simps [simp del]

lemma down'_strict [simp]: "down'\<cdot>\<bottom> = \<bottom>" by (fixrec_simp)

definition down :: "'b itself \<Rightarrow> Integer \<rightarrow> [Integer]" where
  "down C_type = (\<Lambda> v. build\<cdot>(Abs_listfun (
    (down' :: Integer \<rightarrow> (Integer \<rightarrow> 'b \<rightarrow> 'b) \<rightarrow> 'b \<rightarrow> 'b)\<cdot>v,
    down'\<cdot>v\<cdot>(:)\<cdot>[])))"

lemma abstract_list_down' [simp]:
  "abstract_list (down'\<cdot>v\<cdot>(:)\<cdot>[]) = down'\<cdot>v"
proof (intro cfun_eqI)
  fix c :: "Integer \<rightarrow> 'b \<rightarrow> 'b" and n :: "'b"
  show "(abstract_list (down'\<cdot>v\<cdot>(:)\<cdot>[]))\<cdot>c\<cdot>n = down'\<cdot>v\<cdot>c\<cdot>n"
  proof (cases "le\<cdot>1\<cdot>v")
    assume "le\<cdot>1\<cdot>v = \<bottom>" then show ?thesis by simp
  next
    assume "le\<cdot>1\<cdot>v = FF" then show ?thesis
      by (subst (1 2) down'.simps) simp
  next
    have "le\<cdot>(0::Integer)\<cdot>1 = TT" by simp
    moreover assume "le\<cdot>1\<cdot>v = TT"
    ultimately have "le\<cdot>0\<cdot>v = TT" by (rule le_trans)
    then show ?thesis
      by (induct v rule: nonneg_Integer_induct)
         (subst (1 2) down'.simps, simp)+
  qed
qed

lemma cont_Abs_listfun_down' [simp]:
  "cont (\<lambda>v. Abs_listfun (down'\<cdot>v, down'\<cdot>v\<cdot>(:)\<cdot>[]))"
proof -
  have "\<And>v. (down'\<cdot>v, down'\<cdot>v\<cdot>(:)\<cdot>[]) \<in> {(f, xs). f = abstract_list xs}" by simp
  from cont_Abs_listfun [OF this, of id] show ?thesis by simp
qed

lemma sum_down:
  "sum\<cdot>((down TYPE(Integer))\<cdot>v) = down'\<cdot>v\<cdot>(+)\<cdot>0"
  by (simp add: down_def "fold/build")

end
