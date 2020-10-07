section \<open>Error monad transformer\<close>

theory Error_Transformer
imports Error_Monad
begin

subsection \<open>Type definition\<close>

text \<open>The error monad transformer is defined in Haskell by composing
the given monad with a standard error monad:\<close>

text_raw \<open>
\begin{verbatim}
data Error e a = Err e | Ok a
newtype ErrorT e m a = ErrorT { runErrorT :: m (Error e a) }
\end{verbatim}
\<close>

text \<open>We can formalize this definition directly using \<open>tycondef\<close>. \medskip\<close>

tycondef 'a\<cdot>('f::"functor",'e::"domain") errorT =
  ErrorT (runErrorT :: "('a\<cdot>'e error)\<cdot>'f")

lemma coerce_errorT_abs [simp]: "coerce\<cdot>(errorT_abs\<cdot>x) = errorT_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: errorT_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_errorT)
done

lemma coerce_ErrorT [simp]: "coerce\<cdot>(ErrorT\<cdot>k) = ErrorT\<cdot>(coerce\<cdot>k)"
unfolding ErrorT_def by simp

lemma errorT_cases [case_names ErrorT]:
  obtains k where "y = ErrorT\<cdot>k"
proof
  show "y = ErrorT\<cdot>(runErrorT\<cdot>y)"
    by (cases y, simp_all)
qed

lemma ErrorT_runErrorT [simp]: "ErrorT\<cdot>(runErrorT\<cdot>m) = m"
by (cases m rule: errorT_cases, simp)

lemma errorT_induct [case_names ErrorT]:
  fixes P :: "'a\<cdot>('f::functor,'e) errorT \<Rightarrow> bool"
  assumes "\<And>k. P (ErrorT\<cdot>k)"
  shows "P y"
by (cases y rule: errorT_cases, simp add: assms)

lemma errorT_eq_iff:
  "a = b \<longleftrightarrow> runErrorT\<cdot>a = runErrorT\<cdot>b"
apply (cases a rule: errorT_cases)
apply (cases b rule: errorT_cases)
apply simp
done

lemma errorT_eqI:
  "runErrorT\<cdot>a = runErrorT\<cdot>b \<Longrightarrow> a = b"
by (simp add: errorT_eq_iff)

lemma runErrorT_coerce [simp]:
  "runErrorT\<cdot>(coerce\<cdot>k) = coerce\<cdot>(runErrorT\<cdot>k)"
by (induct k rule: errorT_induct, simp)

subsection \<open>Functor class instance\<close>

lemma fmap_error_def: "fmap = error_map\<cdot>ID"
apply (rule cfun_eqI, rename_tac f)
apply (rule cfun_eqI, rename_tac x)
apply (case_tac x rule: error.exhaust, simp_all)
apply (simp add: error_map_def fix_const)
apply (simp add: error_map_def fix_const Err_def)
apply (simp add: error_map_def fix_const Ok_def)
done

lemma fmapU_ErrorT [simp]:
  "fmapU\<cdot>f\<cdot>(ErrorT\<cdot>m) = ErrorT\<cdot>(fmap\<cdot>(fmap\<cdot>f)\<cdot>m)"
unfolding fmapU_errorT_def errorT_map_def fmap_error_def fix_const ErrorT_def
by simp

lemma runErrorT_fmapU [simp]:
  "runErrorT\<cdot>(fmapU\<cdot>f\<cdot>m) = fmap\<cdot>(fmap\<cdot>f)\<cdot>(runErrorT\<cdot>m)"
by (induct m rule: errorT_induct) simp

instance errorT :: ("functor", "domain") "functor"
proof
  fix f g and xs :: "udom\<cdot>('a, 'b) errorT"
  show "fmapU\<cdot>f\<cdot>(fmapU\<cdot>g\<cdot>xs) = fmapU\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
    apply (induct xs rule: errorT_induct)
    apply (simp add: fmap_fmap eta_cfun)
    done
qed

subsection \<open>Transfer properties to polymorphic versions\<close>

lemma fmap_ErrorT [simp]:
  fixes f :: "'a \<rightarrow> 'b" and m :: "'a\<cdot>'e error\<cdot>('m::functor)"
  shows "fmap\<cdot>f\<cdot>(ErrorT\<cdot>m) = ErrorT\<cdot>(fmap\<cdot>(fmap\<cdot>f)\<cdot>m)"
unfolding fmap_def [where 'f="('m,'e) errorT"]
by (simp_all add: coerce_simp eta_cfun)

lemma runErrorT_fmap [simp]:
  fixes f :: "'a \<rightarrow> 'b" and m :: "'a\<cdot>('m::functor,'e) errorT"
  shows "runErrorT\<cdot>(fmap\<cdot>f\<cdot>m) = fmap\<cdot>(fmap\<cdot>f)\<cdot>(runErrorT\<cdot>m)"
using fmap_ErrorT [of f "runErrorT\<cdot>m"]
by simp

lemma errorT_fmap_strict [simp]:
  shows "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>('m::monad,'e) errorT) = \<bottom>"
by (simp add: errorT_eq_iff fmap_strict)

subsection \<open>Monad operations\<close>

text \<open>The error monad transformer does not yield a monad in the
usual sense: We cannot prove a \<open>monad\<close> class instance, because
type \<open>'a\<cdot>('m,'e) errorT\<close> contains values that break the monad
laws. However, it turns out that such values are inaccessible: The
monad laws are satisfied by all values constructible from the abstract
operations.\<close>

text \<open>To explore the properties of the error monad transformer
operations, we define them all as non-overloaded functions. \medskip
\<close>

definition unitET :: "'a \<rightarrow> 'a\<cdot>('m::monad,'e) errorT"
  where "unitET = (\<Lambda> x. ErrorT\<cdot>(return\<cdot>(Ok\<cdot>x)))"

definition bindET :: "'a\<cdot>('m::monad,'e) errorT \<rightarrow>
    ('a \<rightarrow> 'b\<cdot>('m,'e) errorT) \<rightarrow> 'b\<cdot>('m,'e) errorT"
  where "bindET = (\<Lambda> m k. ErrorT\<cdot>(bind\<cdot>(runErrorT\<cdot>m)\<cdot>
    (\<Lambda> n. case n of Err\<cdot>e \<Rightarrow> return\<cdot>(Err\<cdot>e) | Ok\<cdot>x \<Rightarrow> runErrorT\<cdot>(k\<cdot>x))))"

definition liftET :: "'a\<cdot>'m::monad \<rightarrow> 'a\<cdot>('m,'e) errorT"
  where "liftET = (\<Lambda> m. ErrorT\<cdot>(fmap\<cdot>Ok\<cdot>m))"

definition throwET :: "'e \<rightarrow> 'a\<cdot>('m::monad,'e) errorT"
  where "throwET = (\<Lambda> e. ErrorT\<cdot>(return\<cdot>(Err\<cdot>e)))"

definition catchET :: "'a\<cdot>('m::monad,'e) errorT \<rightarrow>
    ('e \<rightarrow> 'a\<cdot>('m,'e) errorT) \<rightarrow> 'a\<cdot>('m,'e) errorT"
  where "catchET = (\<Lambda> m h. ErrorT\<cdot>(bind\<cdot>(runErrorT\<cdot>m)\<cdot>(\<Lambda> n. case n of
    Err\<cdot>e \<Rightarrow> runErrorT\<cdot>(h\<cdot>e) | Ok\<cdot>x \<Rightarrow> return\<cdot>(Ok\<cdot>x))))"

definition fmapET :: "('a \<rightarrow> 'b) \<rightarrow>
    'a\<cdot>('m::monad,'e) errorT \<rightarrow> 'b\<cdot>('m,'e) errorT"
  where "fmapET = (\<Lambda> f m. bindET\<cdot>m\<cdot>(\<Lambda> x. unitET\<cdot>(f\<cdot>x)))"

lemma runErrorT_unitET [simp]:
  "runErrorT\<cdot>(unitET\<cdot>x) = return\<cdot>(Ok\<cdot>x)"
unfolding unitET_def by simp

lemma runErrorT_bindET [simp]:
  "runErrorT\<cdot>(bindET\<cdot>m\<cdot>k) = bind\<cdot>(runErrorT\<cdot>m)\<cdot>
    (\<Lambda> n. case n of Err\<cdot>e \<Rightarrow> return\<cdot>(Err\<cdot>e) | Ok\<cdot>x \<Rightarrow> runErrorT\<cdot>(k\<cdot>x))"
unfolding bindET_def by simp

lemma runErrorT_liftET [simp]:
  "runErrorT\<cdot>(liftET\<cdot>m) = fmap\<cdot>Ok\<cdot>m"
unfolding liftET_def by simp

lemma runErrorT_throwET [simp]:
  "runErrorT\<cdot>(throwET\<cdot>e) = return\<cdot>(Err\<cdot>e)"
unfolding throwET_def by simp

lemma runErrorT_catchET [simp]:
  "runErrorT\<cdot>(catchET\<cdot>m\<cdot>h) =
    bind\<cdot>(runErrorT\<cdot>m)\<cdot>(\<Lambda> n. case n of
      Err\<cdot>e \<Rightarrow> runErrorT\<cdot>(h\<cdot>e) | Ok\<cdot>x \<Rightarrow> return\<cdot>(Ok\<cdot>x))"
unfolding catchET_def by simp

lemma runErrorT_fmapET [simp]:
  "runErrorT\<cdot>(fmapET\<cdot>f\<cdot>m) =
    bind\<cdot>(runErrorT\<cdot>m)\<cdot>(\<Lambda> n. case n of
      Err\<cdot>e \<Rightarrow> return\<cdot>(Err\<cdot>e) | Ok\<cdot>x \<Rightarrow> return\<cdot>(Ok\<cdot>(f\<cdot>x)))"
unfolding fmapET_def by simp

subsection \<open>Laws\<close>

lemma bindET_unitET [simp]:
  "bindET\<cdot>(unitET\<cdot>x)\<cdot>k = k\<cdot>x"
by (rule errorT_eqI, simp)

lemma catchET_unitET [simp]:
  "catchET\<cdot>(unitET\<cdot>x)\<cdot>h = unitET\<cdot>x"
by (rule errorT_eqI, simp)

lemma catchET_throwET [simp]:
  "catchET\<cdot>(throwET\<cdot>e)\<cdot>h = h\<cdot>e"
by (rule errorT_eqI, simp)

lemma liftET_return:
  "liftET\<cdot>(return\<cdot>x) = unitET\<cdot>x"
by (rule errorT_eqI, simp add: fmap_return)

lemma liftET_bind:
  "liftET\<cdot>(bind\<cdot>m\<cdot>k) = bindET\<cdot>(liftET\<cdot>m)\<cdot>(liftET oo k)"
by (rule errorT_eqI, simp add: fmap_bind bind_fmap)

lemma bindET_throwET:
  "bindET\<cdot>(throwET\<cdot>e)\<cdot>k = throwET\<cdot>e"
by (rule errorT_eqI, simp)

lemma bindET_bindET:
  "bindET\<cdot>(bindET\<cdot>m\<cdot>h)\<cdot>k = bindET\<cdot>m\<cdot>(\<Lambda> x. bindET\<cdot>(h\<cdot>x)\<cdot>k)"
apply (rule errorT_eqI)
apply simp
apply (simp add: bind_bind)
apply (rule cfun_arg_cong)
apply (rule cfun_eqI, simp)
apply (case_tac x)
apply (simp add: bind_strict)
apply simp
apply simp
done

lemma fmapET_fmapET:
  "fmapET\<cdot>f\<cdot>(fmapET\<cdot>g\<cdot>m) = fmapET\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>m"
by (simp add: fmapET_def bindET_bindET)

text \<open>Right unit monad law is not satisfied in general.\<close>

lemma bindET_unitET_right_counterexample:
  fixes m :: "'a\<cdot>('m::monad,'e) errorT"
  assumes "m = ErrorT\<cdot>(return\<cdot>\<bottom>)"
  assumes "return\<cdot>\<bottom> \<noteq> (\<bottom> :: ('a\<cdot>'e error)\<cdot>'m)"
  shows "bindET\<cdot>m\<cdot>unitET \<noteq> m"
by (simp add: errorT_eq_iff assms)

text \<open>Right unit is satisfied for inner monads with strict return.\<close>

lemma bindET_unitET_right_restricted:
  fixes m :: "'a\<cdot>('m::monad,'e) errorT"
  assumes "return\<cdot>\<bottom> = (\<bottom> :: ('a\<cdot>'e error)\<cdot>'m)"
  shows "bindET\<cdot>m\<cdot>unitET = m"
unfolding errorT_eq_iff
apply simp
apply (rule trans [OF _ monad_right_unit])
apply (rule cfun_arg_cong)
apply (rule cfun_eqI)
apply (case_tac x, simp_all add: assms)
done

subsection \<open>Error monad transformer invariant\<close>

text \<open>This inductively-defined invariant is supposed to represent
the set of all values constructible using the standard \<open>errorT\<close>
operations.\<close>

inductive invar :: "'a\<cdot>('m::monad, 'e) errorT \<Rightarrow> bool"
  where invar_bottom: "invar \<bottom>"
  | invar_lub: "\<And>Y. \<lbrakk>chain Y; \<And>i. invar (Y i)\<rbrakk> \<Longrightarrow> invar (\<Squnion>i. Y i)"
  | invar_unitET: "\<And>x. invar (unitET\<cdot>x)"
  | invar_bindET: "\<And>m k. \<lbrakk>invar m; \<And>x. invar (k\<cdot>x)\<rbrakk> \<Longrightarrow> invar (bindET\<cdot>m\<cdot>k)"
  | invar_throwET: "\<And>e. invar (throwET\<cdot>e)"
  | invar_catchET: "\<And>m h. \<lbrakk>invar m; \<And>e. invar (h\<cdot>e)\<rbrakk> \<Longrightarrow> invar (catchET\<cdot>m\<cdot>h)"
  | invar_liftET: "\<And>m. invar (liftET\<cdot>m)"

text \<open>Right unit is satisfied for arguments built from standard functions.\<close>

lemma bindET_unitET_right_invar:
  assumes "invar m"
  shows "bindET\<cdot>m\<cdot>unitET = m"
using assms
apply (induct set: invar)
apply (rule errorT_eqI, simp add: bind_strict)
apply (rule admD, simp, assumption, assumption)
apply (rule errorT_eqI, simp)
apply (simp add: errorT_eq_iff bind_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, simp)
apply (case_tac x, simp add: bind_strict, simp, simp)
apply (rule errorT_eqI, simp)
apply (simp add: errorT_eq_iff bind_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, simp)
apply (case_tac x, simp add: bind_strict, simp, simp)
apply (rule errorT_eqI, simp add: monad_fmap bind_bind)
done

text \<open>Monad-fmap is satisfied for arguments built from standard functions.\<close>

lemma errorT_monad_fmap_invar:
  fixes f :: "'a \<rightarrow> 'b" and m :: "'a\<cdot>('m::monad,'e) errorT"
  assumes "invar m"
  shows "fmap\<cdot>f\<cdot>m = bindET\<cdot>m\<cdot>(\<Lambda> x. unitET\<cdot>(f\<cdot>x))"
using assms
apply (induct set: invar)
apply (rule errorT_eqI, simp add: bind_strict fmap_strict)
apply (rule admD, simp, assumption, assumption)
apply (rule errorT_eqI, simp add: fmap_return)
apply (simp add: errorT_eq_iff bind_bind fmap_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, simp)
apply (case_tac x)
apply (simp add: bind_strict fmap_strict)
apply (simp add: fmap_return)
apply simp
apply (rule errorT_eqI, simp add: fmap_return)
apply (simp add: errorT_eq_iff bind_bind fmap_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, simp)
apply (case_tac x)
apply (simp add: bind_strict fmap_strict)
apply simp
apply (simp add: fmap_return)
apply (rule errorT_eqI, simp add: monad_fmap bind_bind return_error_def)
done

subsection \<open>Invariant expressed as a deflation\<close>

text \<open>We can also define an invariant in a more semantic way, as the
set of fixed-points of a deflation.\<close>

definition invar' :: "'a\<cdot>('m::monad, 'e) errorT \<Rightarrow> bool"
  where "invar' m \<longleftrightarrow> fmapET\<cdot>ID\<cdot>m = m"

text \<open>All standard operations preserve the invariant.\<close>

lemma invar'_unitET: "invar' (unitET\<cdot>x)"
  unfolding invar'_def by (simp add: fmapET_def)

lemma invar'_fmapET: "invar' m \<Longrightarrow> invar' (fmapET\<cdot>f\<cdot>m)"
  unfolding invar'_def
  by (erule subst, simp add: fmapET_def bindET_bindET eta_cfun)

lemma invar'_bindET: "\<lbrakk>invar' m; \<And>x. invar' (k\<cdot>x)\<rbrakk> \<Longrightarrow> invar' (bindET\<cdot>m\<cdot>k)"
  unfolding invar'_def
  by (simp add: fmapET_def bindET_bindET eta_cfun)

lemma invar'_throwET: "invar' (throwET\<cdot>e)"
  unfolding invar'_def by (simp add: fmapET_def bindET_throwET eta_cfun)

lemma invar'_catchET: "\<lbrakk>invar' m; \<And>e. invar' (h\<cdot>e)\<rbrakk> \<Longrightarrow> invar' (catchET\<cdot>m\<cdot>h)"
  unfolding invar'_def
  apply (simp add: fmapET_def eta_cfun)
  apply (rule errorT_eqI)
  apply (simp add: bind_bind eta_cfun)
  apply (rule cfun_arg_cong)
  apply (rule cfun_eqI)
  apply (case_tac x)
  apply (simp add: bind_strict)
  apply simp
  apply (drule_tac x=e in meta_spec)
  apply (erule_tac t="h\<cdot>e" in subst) back
  apply (simp add: eta_cfun)
  apply simp
  done

lemma invar'_liftET: "invar' (liftET\<cdot>m)"
  unfolding invar'_def
  apply (simp add: fmapET_def errorT_eq_iff)
  apply (simp add: monad_fmap bind_bind)
  done

lemma invar'_bottom: "invar' \<bottom>"
  unfolding invar'_def fmapET_def
  by (simp add: errorT_eq_iff bind_strict)

lemma adm_invar': "adm invar'"
  unfolding invar'_def [abs_def] by simp

text \<open>All monad laws are preserved by values satisfying the invariant.\<close>

lemma bindET_fmapET_unitET:
  shows "bindET\<cdot>(fmapET\<cdot>f\<cdot>m)\<cdot>unitET = fmapET\<cdot>f\<cdot>m"
by (simp add: fmapET_def bindET_bindET)

lemma invar'_right_unit: "invar' m \<Longrightarrow> bindET\<cdot>m\<cdot>unitET = m"
unfolding invar'_def by (erule subst, rule bindET_fmapET_unitET)

lemma invar'_monad_fmap:
  "invar' m \<Longrightarrow> fmapET\<cdot>f\<cdot>m = bindET\<cdot>m\<cdot>(\<Lambda> x. unitET\<cdot>(f\<cdot>x))"
  unfolding invar'_def by (erule subst, simp add: errorT_eq_iff)

lemma invar'_bind_assoc:
  "\<lbrakk>invar' m; \<And>x. invar' (f\<cdot>x); \<And>y. invar' (g\<cdot>y)\<rbrakk>
    \<Longrightarrow> bindET\<cdot>(bindET\<cdot>m\<cdot>f)\<cdot>g = bindET\<cdot>m\<cdot>(\<Lambda> x. bindET\<cdot>(f\<cdot>x)\<cdot>g)"
  by (rule bindET_bindET)

end
