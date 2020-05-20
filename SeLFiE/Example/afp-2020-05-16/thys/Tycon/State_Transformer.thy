section \<open>State monad transformer\<close>

theory State_Transformer
imports Monad_Zero_Plus
begin

text \<open>
  This version has non-lifted product, and a non-lifted function space.
\<close>

tycondef 'a\<cdot>('f::"functor", 's) stateT =
  StateT (runStateT :: "'s \<rightarrow> ('a \<times> 's)\<cdot>'f")

lemma coerce_stateT_abs [simp]: "coerce\<cdot>(stateT_abs\<cdot>x) = stateT_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: stateT_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_stateT)
done

lemma coerce_StateT [simp]: "coerce\<cdot>(StateT\<cdot>k) = StateT\<cdot>(coerce\<cdot>k)"
unfolding StateT_def by simp

lemma stateT_cases [case_names StateT]:
  obtains k where "y = StateT\<cdot>k"
proof
  show "y = StateT\<cdot>(runStateT\<cdot>y)"
    by (cases y, simp_all)
qed

lemma stateT_induct [case_names StateT]:
  fixes P :: "'a\<cdot>('f::functor,'s) stateT \<Rightarrow> bool"
  assumes "\<And>k. P (StateT\<cdot>k)"
  shows "P y"
by (cases y rule: stateT_cases, simp add: assms)

lemma stateT_eqI:
  "(\<And>s. runStateT\<cdot>a\<cdot>s = runStateT\<cdot>b\<cdot>s) \<Longrightarrow> a = b"
apply (cases a rule: stateT_cases)
apply (cases b rule: stateT_cases)
apply (simp add: cfun_eq_iff)
done

lemma runStateT_coerce [simp]:
  "runStateT\<cdot>(coerce\<cdot>k)\<cdot>s = coerce\<cdot>(runStateT\<cdot>k\<cdot>s)"
by (induct k rule: stateT_induct, simp)

subsection \<open>Functor class instance\<close>

lemma fmapU_StateT [simp]:
  "fmapU\<cdot>f\<cdot>(StateT\<cdot>k) =
    StateT\<cdot>(\<Lambda> s. fmap\<cdot>(\<Lambda>(x, s'). (f\<cdot>x, s'))\<cdot>(k\<cdot>s))"
unfolding fmapU_stateT_def stateT_map_def StateT_def
by (subst fix_eq, simp add: cfun_map_def csplit_def prod_map_def)

lemma runStateT_fmapU [simp]:
  "runStateT\<cdot>(fmapU\<cdot>f\<cdot>m)\<cdot>s =
    fmap\<cdot>(\<Lambda>(x, s'). (f\<cdot>x, s'))\<cdot>(runStateT\<cdot>m\<cdot>s)"
by (cases m rule: stateT_cases, simp)

instantiation stateT :: ("functor", "domain") "functor"
begin

instance
apply standard
apply (induct_tac xs rule: stateT_induct)
apply (simp_all add: fmap_fmap ID_def csplit_def)
done

end

subsection \<open>Monad class instance\<close>

instantiation stateT :: (monad, "domain") monad
begin

definition returnU_stateT_def:
  "returnU = (\<Lambda> x. StateT\<cdot>(\<Lambda> s. return\<cdot>(x, s)))"

definition bindU_stateT_def:
  "bindU = (\<Lambda> m k. StateT\<cdot>(\<Lambda> s. runStateT\<cdot>m\<cdot>s \<bind> (\<Lambda> (x, s'). runStateT\<cdot>(k\<cdot>x)\<cdot>s')))"

lemma bindU_stateT_StateT [simp]:
  "bindU\<cdot>(StateT\<cdot>f)\<cdot>k =
    StateT\<cdot>(\<Lambda> s. f\<cdot>s \<bind> (\<Lambda> (x, s'). runStateT\<cdot>(k\<cdot>x)\<cdot>s'))"
unfolding bindU_stateT_def by simp

lemma runStateT_bindU [simp]:
  "runStateT\<cdot>(bindU\<cdot>m\<cdot>k)\<cdot>s = runStateT\<cdot>m\<cdot>s \<bind> (\<Lambda> (x, s'). runStateT\<cdot>(k\<cdot>x)\<cdot>s')"
unfolding bindU_stateT_def by simp

instance proof
  fix f :: "udom \<rightarrow> udom" and r :: "udom\<cdot>('a,'b) stateT"
  show "fmapU\<cdot>f\<cdot>r = bindU\<cdot>r\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
    by (rule stateT_eqI)
       (simp add: returnU_stateT_def monad_fmap prod_map_def csplit_def)
next
  fix f :: "udom \<rightarrow> udom\<cdot>('a,'b) stateT" and x :: "udom"
  show "bindU\<cdot>(returnU\<cdot>x)\<cdot>f = f\<cdot>x"
    by (rule stateT_eqI)
       (simp add: returnU_stateT_def eta_cfun)
next
  fix r :: "udom\<cdot>('a,'b) stateT" and f g :: "udom \<rightarrow> udom\<cdot>('a,'b) stateT"
  show "bindU\<cdot>(bindU\<cdot>r\<cdot>f)\<cdot>g = bindU\<cdot>r\<cdot>(\<Lambda> x. bindU\<cdot>(f\<cdot>x)\<cdot>g)"
    by (rule stateT_eqI)
       (simp add: bind_bind csplit_def)
qed

end

subsection \<open>Monad zero instance\<close>

instantiation stateT :: (monad_zero, "domain") monad_zero
begin

definition zeroU_stateT_def:
  "zeroU = StateT\<cdot>(\<Lambda> s. mzero)"

lemma runStateT_zeroU [simp]:
  "runStateT\<cdot>zeroU\<cdot>s = mzero"
unfolding zeroU_stateT_def by simp

instance proof
  fix k :: "udom \<rightarrow> udom\<cdot>('a,'b) stateT"
  show "bindU\<cdot>zeroU\<cdot>k = zeroU"
    by (rule stateT_eqI, simp add: bind_mzero)
qed

end

subsection \<open>Monad plus instance\<close>

instantiation stateT :: (monad_plus, "domain") monad_plus
begin

definition plusU_stateT_def:
  "plusU = (\<Lambda> a b. StateT\<cdot>(\<Lambda> s. mplus\<cdot>(runStateT\<cdot>a\<cdot>s)\<cdot>(runStateT\<cdot>b\<cdot>s)))"

lemma runStateT_plusU [simp]:
  "runStateT\<cdot>(plusU\<cdot>a\<cdot>b)\<cdot>s =
    mplus\<cdot>(runStateT\<cdot>a\<cdot>s)\<cdot>(runStateT\<cdot>b\<cdot>s)"
unfolding plusU_stateT_def by simp

instance proof
  fix a b :: "udom\<cdot>('a, 'b) stateT" and k :: "udom \<rightarrow> udom\<cdot>('a, 'b) stateT"
  show "bindU\<cdot>(plusU\<cdot>a\<cdot>b)\<cdot>k = plusU\<cdot>(bindU\<cdot>a\<cdot>k)\<cdot>(bindU\<cdot>b\<cdot>k)"
    by (rule stateT_eqI, simp add: bind_mplus)
next
  fix a b c :: "udom\<cdot>('a, 'b) stateT"
  show "plusU\<cdot>(plusU\<cdot>a\<cdot>b)\<cdot>c = plusU\<cdot>a\<cdot>(plusU\<cdot>b\<cdot>c)"
    by (rule stateT_eqI, simp add: mplus_assoc)
qed

end

subsection \<open>Monad zero plus instance\<close>

instance stateT :: (monad_zero_plus, "domain") monad_zero_plus
proof
  fix m :: "udom\<cdot>('a, 'b) stateT"
  show "plusU\<cdot>zeroU\<cdot>m = m"
    by (rule stateT_eqI, simp add: mplus_mzero_left)
next
  fix m :: "udom\<cdot>('a, 'b) stateT"
  show "plusU\<cdot>m\<cdot>zeroU = m"
    by (rule stateT_eqI, simp add: mplus_mzero_right)
qed

subsection \<open>Transfer properties to polymorphic versions\<close>

lemma coerce_csplit [coerce_simp]:
  shows "coerce\<cdot>(csplit\<cdot>f\<cdot>p) = csplit\<cdot>(\<Lambda> x y. coerce\<cdot>(f\<cdot>x\<cdot>y))\<cdot>p"
unfolding csplit_def by simp

lemma csplit_coerce [coerce_simp]:
  fixes p :: "'a \<times> 'b"
  shows "csplit\<cdot>f\<cdot>(COERCE('a \<times> 'b, 'c \<times> 'd)\<cdot>p) =
    csplit\<cdot>(\<Lambda> x y. f\<cdot>(COERCE('a, 'c)\<cdot>x)\<cdot>(COERCE('b, 'd)\<cdot>y))\<cdot>p"
unfolding coerce_prod csplit_def prod_map_def by simp

lemma fmap_stateT_simps [simp]:
  "fmap\<cdot>f\<cdot>(StateT\<cdot>m :: 'a\<cdot>('f::functor,'s) stateT) =
    StateT\<cdot>(\<Lambda> s. fmap\<cdot>(\<Lambda> (x, s'). (f\<cdot>x, s'))\<cdot>(m\<cdot>s))"
unfolding fmap_def [where 'f="('f, 's) stateT"]
by (simp add: coerce_simp eta_cfun)

lemma runStateT_fmap [simp]:
  "runStateT\<cdot>(fmap\<cdot>f\<cdot>m)\<cdot>s = fmap\<cdot>(\<Lambda> (x, s'). (f\<cdot>x, s'))\<cdot>(runStateT\<cdot>m\<cdot>s)"
by (induct m rule: stateT_induct, simp)

lemma return_stateT_def:
  "(return :: _ \<rightarrow> 'a\<cdot>('m::monad, 's) stateT) =
    (\<Lambda> x. StateT\<cdot>(\<Lambda> s. return\<cdot>(x, s)))"
unfolding return_def [where 'm="('m, 's) stateT"] returnU_stateT_def
by (simp add: coerce_simp)

lemma bind_stateT_def:
  "bind = (\<Lambda> m k. StateT\<cdot>(\<Lambda> s. runStateT\<cdot>m\<cdot>s \<bind> (\<Lambda> (x, s'). runStateT\<cdot>(k\<cdot>x)\<cdot>s')))"
apply (subst bind_def, subst bindU_stateT_def)
apply (simp add: coerce_simp)
apply (simp add: coerce_idem domain_defl_simps monofun_cfun)
apply (simp add: eta_cfun)
done

text "TODO: add \<open>coerce_idem\<close> to \<open>coerce_simps\<close>, along\010with monotonicity rules for DEFL."

lemma bind_stateT_simps [simp]:
  "bind\<cdot>(StateT\<cdot>m :: 'a\<cdot>('m::monad,'s) stateT)\<cdot>k =
    StateT\<cdot>(\<Lambda> s. m\<cdot>s \<bind> (\<Lambda> (x, s'). runStateT\<cdot>(k\<cdot>x)\<cdot>s'))"
unfolding bind_stateT_def by simp

lemma runStateT_bind [simp]:
  "runStateT\<cdot>(m \<bind> k)\<cdot>s = runStateT\<cdot>m\<cdot>s \<bind> (\<Lambda> (x, s'). runStateT\<cdot>(k\<cdot>x)\<cdot>s')"
unfolding bind_stateT_def by simp

end
