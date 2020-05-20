section \<open>Binary tree monad\<close>

theory Binary_Tree_Monad
imports Monad
begin

subsection \<open>Type definition\<close>

tycondef 'a\<cdot>btree =
  Leaf (lazy "'a") | Node (lazy "'a\<cdot>btree") (lazy "'a\<cdot>btree")

lemma coerce_btree_abs [simp]: "coerce\<cdot>(btree_abs\<cdot>x) = btree_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: btree_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_btree)
done

lemma coerce_Leaf [simp]: "coerce\<cdot>(Leaf\<cdot>x) = Leaf\<cdot>(coerce\<cdot>x)"
unfolding Leaf_def by simp

lemma coerce_Node [simp]: "coerce\<cdot>(Node\<cdot>xs\<cdot>ys) = Node\<cdot>(coerce\<cdot>xs)\<cdot>(coerce\<cdot>ys)"
unfolding Node_def by simp

lemma fmapU_btree_simps [simp]:
  "fmapU\<cdot>f\<cdot>(\<bottom>::udom\<cdot>btree) = \<bottom>"
  "fmapU\<cdot>f\<cdot>(Leaf\<cdot>x) = Leaf\<cdot>(f\<cdot>x)"
  "fmapU\<cdot>f\<cdot>(Node\<cdot>xs\<cdot>ys) = Node\<cdot>(fmapU\<cdot>f\<cdot>xs)\<cdot>(fmapU\<cdot>f\<cdot>ys)"
unfolding fmapU_btree_def btree_map_def
apply (subst fix_eq, simp)
apply (subst fix_eq, simp add: Leaf_def)
apply (subst fix_eq, simp add: Node_def)
done

subsection \<open>Class instance proofs\<close>

instance btree :: "functor"
apply standard
apply (induct_tac xs rule: btree.induct, simp_all)
done

instantiation btree :: monad
begin

definition
  "returnU = Leaf"

fixrec bindU_btree :: "udom\<cdot>btree \<rightarrow> (udom \<rightarrow> udom\<cdot>btree) \<rightarrow> udom\<cdot>btree"
  where "bindU_btree\<cdot>(Leaf\<cdot>x)\<cdot>k = k\<cdot>x"
  | "bindU_btree\<cdot>(Node\<cdot>xs\<cdot>ys)\<cdot>k =
      Node\<cdot>(bindU_btree\<cdot>xs\<cdot>k)\<cdot>(bindU_btree\<cdot>ys\<cdot>k)"

lemma bindU_btree_strict [simp]: "bindU\<cdot>\<bottom>\<cdot>k = (\<bottom>::udom\<cdot>btree)"
by fixrec_simp

instance proof
  fix x :: "udom"
  fix f :: "udom \<rightarrow> udom"
  fix h k :: "udom \<rightarrow> udom\<cdot>btree"
  fix xs :: "udom\<cdot>btree"
  show "fmapU\<cdot>f\<cdot>xs = bindU\<cdot>xs\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
    by (induct xs rule: btree.induct, simp_all add: returnU_btree_def)
  show "bindU\<cdot>(returnU\<cdot>x)\<cdot>k = k\<cdot>x"
    by (simp add: returnU_btree_def)
  show "bindU\<cdot>(bindU\<cdot>xs\<cdot>h)\<cdot>k = bindU\<cdot>xs\<cdot>(\<Lambda> x. bindU\<cdot>(h\<cdot>x)\<cdot>k)"
    by (induct xs rule: btree.induct) simp_all
qed

end

subsection \<open>Transfer properties to polymorphic versions\<close>

lemma fmap_btree_simps [simp]:
  "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>btree) = \<bottom>"
  "fmap\<cdot>f\<cdot>(Leaf\<cdot>x) = Leaf\<cdot>(f\<cdot>x)"
  "fmap\<cdot>f\<cdot>(Node\<cdot>xs\<cdot>ys) = Node\<cdot>(fmap\<cdot>f\<cdot>xs)\<cdot>(fmap\<cdot>f\<cdot>ys)"
unfolding fmap_def by simp_all

lemma bind_btree_simps [simp]:
  "bind\<cdot>(\<bottom>::'a\<cdot>btree)\<cdot>k = \<bottom>"
  "bind\<cdot>(Leaf\<cdot>x)\<cdot>k = k\<cdot>x"
  "bind\<cdot>(Node\<cdot>xs\<cdot>ys)\<cdot>k = Node\<cdot>(bind\<cdot>xs\<cdot>k)\<cdot>(bind\<cdot>ys\<cdot>k)"
unfolding bind_def
by (simp_all add: coerce_simp)

lemma return_btree_def:
  "return = Leaf"
unfolding return_def returnU_btree_def
by (simp add: coerce_simp eta_cfun)

lemma join_btree_simps [simp]:
  "join\<cdot>(\<bottom>::'a\<cdot>btree\<cdot>btree) = \<bottom>"
  "join\<cdot>(Leaf\<cdot>xs) = xs"
  "join\<cdot>(Node\<cdot>xss\<cdot>yss) = Node\<cdot>(join\<cdot>xss)\<cdot>(join\<cdot>yss)"
unfolding join_def by simp_all

end
