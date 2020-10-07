section \<open>Monad-Zero-Plus Class\<close>

theory Monad_Zero_Plus
imports Monad_Zero Monad_Plus
begin

hide_const (open) Fixrec.mplus

class functor_zero_plus = functor_zero + functor_plus +
  assumes plusU_zeroU_left:
    "plusU\<cdot>zeroU\<cdot>m = m"
  assumes plusU_zeroU_right:
    "plusU\<cdot>m\<cdot>zeroU = m"

class monad_zero_plus = monad_zero + monad_plus + functor_zero_plus

lemma fplus_fzero_left:
  fixes m :: "'a\<cdot>'f::functor_zero_plus"
  shows "fplus\<cdot>fzero\<cdot>m = m"
unfolding fplus_def fzero_def
by (simp add: coerce_simp plusU_zeroU_left)

lemma fplus_fzero_right:
  fixes m :: "'a\<cdot>'f::functor_zero_plus"
  shows "fplus\<cdot>m\<cdot>fzero = m"
unfolding fplus_def fzero_def
by (simp add: coerce_simp plusU_zeroU_right)

lemmas mplus_mzero_left =
  fplus_fzero_left [where 'f="'m::monad_zero_plus"] for f

lemmas mplus_mzero_right =
  fplus_fzero_right [where 'f="'m::monad_zero_plus"] for f

end
