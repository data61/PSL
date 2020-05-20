section \<open>Maybe monad\<close>

theory Maybe_Monad
imports Monad_Zero_Plus
begin

subsection \<open>Type definition\<close>

tycondef 'a\<cdot>maybe = Nothing | Just (lazy "'a")

lemma coerce_maybe_abs [simp]: "coerce\<cdot>(maybe_abs\<cdot>x) = maybe_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: maybe_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_maybe)
done

lemma coerce_Nothing [simp]: "coerce\<cdot>Nothing = Nothing"
unfolding Nothing_def by simp

lemma coerce_Just [simp]: "coerce\<cdot>(Just\<cdot>x) = Just\<cdot>(coerce\<cdot>x)"
unfolding Just_def by simp

lemma fmapU_maybe_simps [simp]:
  "fmapU\<cdot>f\<cdot>(\<bottom>::udom\<cdot>maybe) = \<bottom>"
  "fmapU\<cdot>f\<cdot>Nothing = Nothing"
  "fmapU\<cdot>f\<cdot>(Just\<cdot>x) = Just\<cdot>(f\<cdot>x)"
unfolding fmapU_maybe_def maybe_map_def fix_const
apply simp
apply (simp add: Nothing_def)
apply (simp add: Just_def)
done

subsection \<open>Class instance proofs\<close>

instance maybe :: "functor"
apply standard
apply (induct_tac xs rule: maybe.induct, simp_all)
done

instantiation maybe :: "{functor_zero_plus, monad_zero}"
begin

fixrec plusU_maybe :: "udom\<cdot>maybe \<rightarrow> udom\<cdot>maybe \<rightarrow> udom\<cdot>maybe"
  where "plusU_maybe\<cdot>Nothing\<cdot>ys = ys"
  | "plusU_maybe\<cdot>(Just\<cdot>x)\<cdot>ys = Just\<cdot>x"

lemma plusU_maybe_strict [simp]: "plusU\<cdot>\<bottom>\<cdot>ys = (\<bottom>::udom\<cdot>maybe)"
by fixrec_simp

fixrec bindU_maybe :: "udom\<cdot>maybe \<rightarrow> (udom \<rightarrow> udom\<cdot>maybe) \<rightarrow> udom\<cdot>maybe"
  where "bindU_maybe\<cdot>Nothing\<cdot>k = Nothing"
  | "bindU_maybe\<cdot>(Just\<cdot>x)\<cdot>k = k\<cdot>x"

lemma bindU_maybe_strict [simp]: "bindU\<cdot>\<bottom>\<cdot>k = (\<bottom>::udom\<cdot>maybe)"
by fixrec_simp

definition zeroU_maybe_def:
  "zeroU = Nothing"

definition returnU_maybe_def:
  "returnU = Just"

lemma plusU_Nothing_right: "plusU\<cdot>xs\<cdot>Nothing = xs"
by (induct xs rule: maybe.induct) simp_all

lemma bindU_plusU_maybe:
  fixes xs ys :: "udom\<cdot>maybe" shows
  "bindU\<cdot>(plusU\<cdot>xs\<cdot>ys)\<cdot>f = plusU\<cdot>(bindU\<cdot>xs\<cdot>f)\<cdot>(bindU\<cdot>ys\<cdot>f)"
apply (induct xs rule: maybe.induct)
apply simp_all
oops

instance proof
  fix x :: "udom"
  fix f :: "udom \<rightarrow> udom"
  fix h k :: "udom \<rightarrow> udom\<cdot>maybe"
  fix xs ys zs :: "udom\<cdot>maybe"
  show "fmapU\<cdot>f\<cdot>xs = bindU\<cdot>xs\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
    by (induct xs rule: maybe.induct, simp_all add: returnU_maybe_def)
  show "bindU\<cdot>(returnU\<cdot>x)\<cdot>k = k\<cdot>x"
    by (simp add: returnU_maybe_def plusU_Nothing_right)
  show "bindU\<cdot>(bindU\<cdot>xs\<cdot>h)\<cdot>k = bindU\<cdot>xs\<cdot>(\<Lambda> x. bindU\<cdot>(h\<cdot>x)\<cdot>k)"
    by (induct xs rule: maybe.induct) simp_all
  show "plusU\<cdot>(plusU\<cdot>xs\<cdot>ys)\<cdot>zs = plusU\<cdot>xs\<cdot>(plusU\<cdot>ys\<cdot>zs)"
    by (induct xs rule: maybe.induct) simp_all
  show "bindU\<cdot>zeroU\<cdot>k = zeroU"
    by (simp add: zeroU_maybe_def)
  show "fmapU\<cdot>f\<cdot>(plusU\<cdot>xs\<cdot>ys) = plusU\<cdot>(fmapU\<cdot>f\<cdot>xs)\<cdot>(fmapU\<cdot>f\<cdot>ys)"
    by (induct xs rule: maybe.induct) simp_all
  show "fmapU\<cdot>f\<cdot>zeroU = (zeroU :: udom\<cdot>maybe)"
    by (simp add: zeroU_maybe_def)
  show "plusU\<cdot>zeroU\<cdot>xs = xs"
    by (simp add: zeroU_maybe_def)
  show "plusU\<cdot>xs\<cdot>zeroU = xs"
    by (simp add: zeroU_maybe_def plusU_Nothing_right)
qed

end

subsection \<open>Transfer properties to polymorphic versions\<close>

lemma fmap_maybe_simps [simp]:
  "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>maybe) = \<bottom>"
  "fmap\<cdot>f\<cdot>Nothing = Nothing"
  "fmap\<cdot>f\<cdot>(Just\<cdot>x) = Just\<cdot>(f\<cdot>x)"
unfolding fmap_def by simp_all

lemma fplus_maybe_simps [simp]:
  "fplus\<cdot>(\<bottom>::'a\<cdot>maybe)\<cdot>ys = \<bottom>"
  "fplus\<cdot>Nothing\<cdot>ys = ys"
  "fplus\<cdot>(Just\<cdot>x)\<cdot>ys = Just\<cdot>x"
unfolding fplus_def by simp_all

lemma fplus_Nothing_right [simp]:
  "fplus\<cdot>m\<cdot>Nothing = m"
by (simp add: fplus_def plusU_Nothing_right)

lemma bind_maybe_simps [simp]:
  "bind\<cdot>(\<bottom>::'a\<cdot>maybe)\<cdot>f = \<bottom>"
  "bind\<cdot>Nothing\<cdot>f = Nothing"
  "bind\<cdot>(Just\<cdot>x)\<cdot>f = f\<cdot>x"
unfolding bind_def fplus_def by simp_all

lemma return_maybe_def: "return = Just"
unfolding return_def returnU_maybe_def
by (simp add: coerce_cfun cfcomp1 eta_cfun)

lemma mzero_maybe_def: "mzero = Nothing"
unfolding mzero_def zeroU_maybe_def
by simp

lemma join_maybe_simps [simp]:
  "join\<cdot>(\<bottom>::'a\<cdot>maybe\<cdot>maybe) = \<bottom>"
  "join\<cdot>Nothing = Nothing"
  "join\<cdot>(Just\<cdot>xs) = xs"
unfolding join_def by simp_all

subsection \<open>Maybe is not in \<open>monad_plus\<close>\<close>

text \<open>
  The \<open>maybe\<close> type does not satisfy the law \<open>bind_mplus\<close>.
\<close>

lemma maybe_counterexample1:
  "\<lbrakk>a = Just\<cdot>x; b = \<bottom>; k\<cdot>x = Nothing\<rbrakk>
    \<Longrightarrow> fplus\<cdot>a\<cdot>b \<bind> k \<noteq> fplus\<cdot>(a \<bind> k)\<cdot>(b \<bind> k)"
by simp

lemma maybe_counterexample2:
  "\<lbrakk>a = Just\<cdot>x; b = Just\<cdot>y; k\<cdot>x = Nothing; k\<cdot>y = Just\<cdot>z\<rbrakk>
    \<Longrightarrow> fplus\<cdot>a\<cdot>b \<bind> k \<noteq> fplus\<cdot>(a \<bind> k)\<cdot>(b \<bind> k)"
by simp

end
