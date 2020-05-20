section \<open>Monad-Plus Class\<close>

theory Monad_Plus
imports Monad
begin

hide_const (open) Fixrec.mplus

class plusU = tycon +
  fixes plusU :: "udom\<cdot>'a \<rightarrow> udom\<cdot>'a \<rightarrow> udom\<cdot>'a::tycon"

class functor_plus = plusU + "functor" +
  assumes fmapU_plusU [coerce_simp]:
    "fmapU\<cdot>f\<cdot>(plusU\<cdot>a\<cdot>b) = plusU\<cdot>(fmapU\<cdot>f\<cdot>a)\<cdot>(fmapU\<cdot>f\<cdot>b)"
  assumes plusU_assoc:
    "plusU\<cdot>(plusU\<cdot>a\<cdot>b)\<cdot>c = plusU\<cdot>a\<cdot>(plusU\<cdot>b\<cdot>c)"

class monad_plus = plusU + monad +
  assumes bindU_plusU:
    "bindU\<cdot>(plusU\<cdot>xs\<cdot>ys)\<cdot>k = plusU\<cdot>(bindU\<cdot>xs\<cdot>k)\<cdot>(bindU\<cdot>ys\<cdot>k)"
  assumes plusU_assoc':
    "plusU\<cdot>(plusU\<cdot>a\<cdot>b)\<cdot>c = plusU\<cdot>a\<cdot>(plusU\<cdot>b\<cdot>c)"

instance monad_plus \<subseteq> functor_plus
by standard (simp_all only: fmapU_eq_bindU bindU_plusU plusU_assoc')

definition fplus :: "'a\<cdot>'f::functor_plus \<rightarrow> 'a\<cdot>'f \<rightarrow> 'a\<cdot>'f"
  where "fplus = coerce\<cdot>(plusU :: udom\<cdot>'f \<rightarrow> _)"

lemma fmap_fplus:
  fixes f :: "'a \<rightarrow> 'b" and a b :: "'a\<cdot>'f::functor_plus"
  shows "fmap\<cdot>f\<cdot>(fplus\<cdot>a\<cdot>b) = fplus\<cdot>(fmap\<cdot>f\<cdot>a)\<cdot>(fmap\<cdot>f\<cdot>b)"
unfolding fmap_def fplus_def
by (simp add: coerce_simp)

lemma fplus_assoc:
  fixes a b c :: "'a\<cdot>'f::functor_plus"
  shows "fplus\<cdot>(fplus\<cdot>a\<cdot>b)\<cdot>c = fplus\<cdot>a\<cdot>(fplus\<cdot>b\<cdot>c)"
unfolding fplus_def
by (simp add: coerce_simp plusU_assoc)

abbreviation mplus :: "'a\<cdot>'m::monad_plus \<rightarrow> 'a\<cdot>'m \<rightarrow> 'a\<cdot>'m"
  where "mplus \<equiv> fplus"

lemmas mplus_def = fplus_def [where 'f="'m::monad_plus" for f]
lemmas fmap_mplus = fmap_fplus [where 'f="'m::monad_plus" for f]
lemmas mplus_assoc = fplus_assoc [where 'f="'m::monad_plus" for f]

lemma bind_mplus:
  fixes a b :: "'a\<cdot>'m::monad_plus"
  shows "bind\<cdot>(mplus\<cdot>a\<cdot>b)\<cdot>k = mplus\<cdot>(bind\<cdot>a\<cdot>k)\<cdot>(bind\<cdot>b\<cdot>k)"
unfolding bind_def mplus_def
by (simp add: coerce_simp bindU_plusU)

lemma join_mplus:
  fixes xss yss :: "('a\<cdot>'m)\<cdot>'m::monad_plus"
  shows "join\<cdot>(mplus\<cdot>xss\<cdot>yss) = mplus\<cdot>(join\<cdot>xss)\<cdot>(join\<cdot>yss)"
by (simp add: join_def bind_mplus)

end
