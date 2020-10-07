section \<open>Monad-Zero Class\<close>

theory Monad_Zero
imports Monad
begin

class zeroU = tycon +
  fixes zeroU :: "udom\<cdot>'a::tycon"

class functor_zero = zeroU + "functor" +
  assumes fmapU_zeroU [coerce_simp]:
    "fmapU\<cdot>f\<cdot>zeroU = zeroU"

class monad_zero = zeroU + monad +
  assumes bindU_zeroU:
    "bindU\<cdot>zeroU\<cdot>f = zeroU"

instance monad_zero \<subseteq> functor_zero
proof
  fix f show "fmapU\<cdot>f\<cdot>zeroU = (zeroU :: udom\<cdot>'a)"
    unfolding fmapU_eq_bindU
    by (rule bindU_zeroU)
qed

definition fzero :: "'a\<cdot>'f::functor_zero"
  where "fzero = coerce\<cdot>(zeroU :: udom\<cdot>'f)"

lemma fmap_fzero:
  "fmap\<cdot>f\<cdot>(fzero :: 'a\<cdot>'f::functor_zero) = (fzero :: 'b\<cdot>'f)"
unfolding fmap_def fzero_def
by (simp add: coerce_simp)

abbreviation mzero :: "'a\<cdot>'m::monad_zero"
  where "mzero \<equiv> fzero"

lemmas mzero_def = fzero_def [where 'f="'m::monad_zero"] for f
lemmas fmap_mzero = fmap_fzero [where 'f="'m::monad_zero"] for f

lemma bindU_eq_bind: "bindU = bind"
unfolding bind_def by simp

lemma bind_mzero:
  "bind\<cdot>(fzero :: 'a\<cdot>'m::monad_zero)\<cdot>k = (mzero :: 'b\<cdot>'m)"
unfolding bind_def mzero_def
by (simp add: coerce_simp bindU_zeroU)

end
