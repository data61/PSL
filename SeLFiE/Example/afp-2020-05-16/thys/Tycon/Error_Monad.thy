section \<open>Error monad\<close>

theory Error_Monad
imports Monad_Plus
begin

subsection \<open>Type definition\<close>

tycondef 'a\<cdot>'e error = Err (lazy "'e") | Ok (lazy "'a")

lemma coerce_error_abs [simp]: "coerce\<cdot>(error_abs\<cdot>x) = error_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: error_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_error)
done

lemma coerce_Err [simp]: "coerce\<cdot>(Err\<cdot>x) = Err\<cdot>(coerce\<cdot>x)"
unfolding Err_def by simp

lemma coerce_Ok [simp]: "coerce\<cdot>(Ok\<cdot>m) = Ok\<cdot>(coerce\<cdot>m)"
unfolding Ok_def by simp

lemma fmapU_error_simps [simp]:
  "fmapU\<cdot>f\<cdot>(\<bottom>::udom\<cdot>'a error) = \<bottom>"
  "fmapU\<cdot>f\<cdot>(Err\<cdot>e) = Err\<cdot>e"
  "fmapU\<cdot>f\<cdot>(Ok\<cdot>x) = Ok\<cdot>(f\<cdot>x)"
unfolding fmapU_error_def error_map_def fix_const
apply simp
apply (simp add: Err_def)
apply (simp add: Ok_def)
done

subsection \<open>Monad class instance\<close>

instantiation error :: ("domain") "{monad, functor_plus}"
begin

definition
  "returnU = Ok"

fixrec bindU_error :: "udom\<cdot>'a error \<rightarrow> (udom \<rightarrow> udom\<cdot>'a error) \<rightarrow> udom\<cdot>'a error"
  where "bindU_error\<cdot>(Err\<cdot>e)\<cdot>f = Err\<cdot>e"
  | "bindU_error\<cdot>(Ok\<cdot>x)\<cdot>f = f\<cdot>x"

lemma bindU_error_strict [simp]: "bindU\<cdot>\<bottom>\<cdot>k = (\<bottom>::udom\<cdot>'a error)"
by fixrec_simp

fixrec plusU_error :: "udom\<cdot>'a error \<rightarrow> udom\<cdot>'a error \<rightarrow> udom\<cdot>'a error"
  where "plusU_error\<cdot>(Err\<cdot>e)\<cdot>f = f"
  | "plusU_error\<cdot>(Ok\<cdot>x)\<cdot>f = Ok\<cdot>x"

lemma plusU_error_strict [simp]: "plusU\<cdot>(\<bottom> :: udom\<cdot>'a error) = \<bottom>"
by fixrec_simp

instance proof
  fix f g :: "udom \<rightarrow> udom" and r :: "udom\<cdot>'a error"
  show "fmapU\<cdot>f\<cdot>(fmapU\<cdot>g\<cdot>r) = fmapU\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>r"
    by (induct r rule: error.induct) simp_all
next
  fix f :: "udom \<rightarrow> udom" and r :: "udom\<cdot>'a error"
  show "fmapU\<cdot>f\<cdot>r = bindU\<cdot>r\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
    by (induct r rule: error.induct)
       (simp_all add: returnU_error_def)
next
  fix f :: "udom \<rightarrow> udom\<cdot>'a error" and x :: "udom"
  show "bindU\<cdot>(returnU\<cdot>x)\<cdot>f = f\<cdot>x"
    by (simp add: returnU_error_def)
next
  fix r :: "udom\<cdot>'a error" and f g :: "udom \<rightarrow> udom\<cdot>'a error"
  show "bindU\<cdot>(bindU\<cdot>r\<cdot>f)\<cdot>g = bindU\<cdot>r\<cdot>(\<Lambda> x. bindU\<cdot>(f\<cdot>x)\<cdot>g)"
    by (induct r rule: error.induct)
       simp_all
next
  fix f :: "udom \<rightarrow> udom" and a b :: "udom\<cdot>'a error"
  show "fmapU\<cdot>f\<cdot>(plusU\<cdot>a\<cdot>b) = plusU\<cdot>(fmapU\<cdot>f\<cdot>a)\<cdot>(fmapU\<cdot>f\<cdot>b)"
    by (induct a rule: error.induct) simp_all
next
  fix a b c :: "udom\<cdot>'a error"
  show "plusU\<cdot>(plusU\<cdot>a\<cdot>b)\<cdot>c = plusU\<cdot>a\<cdot>(plusU\<cdot>b\<cdot>c)"
    by (induct a rule: error.induct) simp_all
qed

end

subsection \<open>Transfer properties to polymorphic versions\<close>

lemma fmap_error_simps [simp]:
  "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>'e error) = \<bottom>"
  "fmap\<cdot>f\<cdot>(Err\<cdot>e :: 'a\<cdot>'e error) = Err\<cdot>e"
  "fmap\<cdot>f\<cdot>(Ok\<cdot>x :: 'a\<cdot>'e error) = Ok\<cdot>(f\<cdot>x)"
unfolding fmap_def [where 'f="'e error"]
by (simp_all add: coerce_simp)

lemma return_error_def: "return = Ok"
unfolding return_def returnU_error_def
by (simp add: coerce_simp eta_cfun)

lemma bind_error_simps [simp]:
  "bind\<cdot>(\<bottom> :: 'a\<cdot>'e error)\<cdot>f = \<bottom>"
  "bind\<cdot>(Err\<cdot>e :: 'a\<cdot>'e error)\<cdot>f = Err\<cdot>e"
  "bind\<cdot>(Ok\<cdot>x :: 'a\<cdot>'e error)\<cdot>f = f\<cdot>x"
unfolding bind_def
by (simp_all add: coerce_simp)

lemma join_error_simps [simp]:
  "join\<cdot>\<bottom> = (\<bottom> :: 'a\<cdot>'e error)"
  "join\<cdot>(Err\<cdot>e) = Err\<cdot>e"
  "join\<cdot>(Ok\<cdot>x) = x"
unfolding join_def by simp_all

lemma fplus_error_simps [simp]:
  "fplus\<cdot>\<bottom>\<cdot>r = (\<bottom> :: 'a\<cdot>'e error)"
  "fplus\<cdot>(Err\<cdot>e)\<cdot>r = r"
  "fplus\<cdot>(Ok\<cdot>x)\<cdot>r = Ok\<cdot>x"
unfolding fplus_def
by (simp_all add: coerce_simp)

end
