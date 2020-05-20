section \<open>Lift monad\<close>

theory Lift_Monad
imports Monad
begin

subsection \<open>Type definition\<close>

tycondef 'a\<cdot>lifted = Lifted (lazy "'a")

lemma coerce_lifted_abs [simp]: "coerce\<cdot>(lifted_abs\<cdot>x) = lifted_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: lifted_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_lifted)
done

lemma coerce_Lifted [simp]: "coerce\<cdot>(Lifted\<cdot>x) = Lifted\<cdot>(coerce\<cdot>x)"
unfolding Lifted_def by simp

lemma fmapU_lifted_simps [simp]:
  "fmapU\<cdot>f\<cdot>(\<bottom>::udom\<cdot>lifted) = \<bottom>"
  "fmapU\<cdot>f\<cdot>(Lifted\<cdot>x) = Lifted\<cdot>(f\<cdot>x)"
unfolding fmapU_lifted_def lifted_map_def fix_const
apply simp
apply (simp add: Lifted_def)
done

subsection \<open>Class instance proofs\<close>

instance lifted :: "functor"
  by standard (induct_tac xs rule: lifted.induct, simp_all)

instantiation lifted :: monad
begin

fixrec bindU_lifted :: "udom\<cdot>lifted \<rightarrow> (udom \<rightarrow> udom\<cdot>lifted) \<rightarrow> udom\<cdot>lifted"
  where "bindU_lifted\<cdot>(Lifted\<cdot>x)\<cdot>k = k\<cdot>x"

lemma bindU_lifted_strict [simp]: "bindU\<cdot>\<bottom>\<cdot>k = (\<bottom>::udom\<cdot>lifted)"
by fixrec_simp

definition returnU_lifted_def:
  "returnU = Lifted"

instance proof
  fix x :: "udom"
  fix f :: "udom \<rightarrow> udom"
  fix h k :: "udom \<rightarrow> udom\<cdot>lifted"
  fix xs :: "udom\<cdot>lifted"
  show "fmapU\<cdot>f\<cdot>xs = bindU\<cdot>xs\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
    by (induct xs rule: lifted.induct, simp_all add: returnU_lifted_def)
  show "bindU\<cdot>(returnU\<cdot>x)\<cdot>k = k\<cdot>x"
    by (simp add: returnU_lifted_def)
  show "bindU\<cdot>(bindU\<cdot>xs\<cdot>h)\<cdot>k = bindU\<cdot>xs\<cdot>(\<Lambda> x. bindU\<cdot>(h\<cdot>x)\<cdot>k)"
    by (induct xs rule: lifted.induct) simp_all
qed

end

subsection \<open>Transfer properties to polymorphic versions\<close>

lemma fmap_lifted_simps [simp]:
  "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>lifted) = \<bottom>"
  "fmap\<cdot>f\<cdot>(Lifted\<cdot>x) = Lifted\<cdot>(f\<cdot>x)"
unfolding fmap_def by simp_all

lemma bind_lifted_simps [simp]:
  "bind\<cdot>(\<bottom>::'a\<cdot>lifted)\<cdot>f = \<bottom>"
  "bind\<cdot>(Lifted\<cdot>x)\<cdot>f = f\<cdot>x"
unfolding bind_def by simp_all

lemma return_lifted_def: "return = Lifted"
unfolding return_def returnU_lifted_def
by (simp add: coerce_cfun cfcomp1 eta_cfun)

lemma join_lifted_simps [simp]:
  "join\<cdot>(\<bottom>::'a\<cdot>lifted\<cdot>lifted) = \<bottom>"
  "join\<cdot>(Lifted\<cdot>xs) = xs"
unfolding join_def by simp_all

end
