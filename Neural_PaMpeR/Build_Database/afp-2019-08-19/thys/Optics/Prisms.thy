section \<open>Prisms\<close>

theory Prisms
  imports Main
begin
  
text \<open>Prisms are like lenses, but they act on sum types rather than product types. For now
  we do not support many properties about them. See \url{https://hackage.haskell.org/package/lens-4.15.2/docs/Control-Lens-Prism.html}
  for more information.\<close>

record ('v, 's) prism =
  prism_match :: "'s \<Rightarrow> 'v option" ("match\<index>")
  prism_build :: "'v \<Rightarrow> 's" ("build\<index>")

locale wb_prism =
  fixes x :: "('v, 's) prism" (structure)
  assumes match_build: "match (build v) = Some v"
  and build_match: "match s = Some v \<Longrightarrow> s = build v"
begin

  lemma build_match_iff: "match s = Some v \<longleftrightarrow> s = build v"
    using build_match match_build by blast

  lemma range_build: "range build = dom match"
    using build_match match_build by fastforce
end

definition prism_suml :: "('a, 'a + 'b) prism" where
"prism_suml = \<lparr> prism_match = (\<lambda> v. case v of Inl x \<Rightarrow> Some x | _ \<Rightarrow> None), prism_build = Inl \<rparr>"

lemma wb_prim_suml: "wb_prism prism_suml"
  apply (unfold_locales)
   apply (simp_all add: prism_suml_def sum.case_eq_if)
  apply (metis option.inject option.simps(3) sum.collapse(1))
done

definition prism_diff :: "('a, 's) prism \<Rightarrow> ('b, 's) prism \<Rightarrow> bool" (infix "\<nabla>" 50) where
"prism_diff X Y = (range build\<^bsub>X\<^esub> \<inter> range build\<^bsub>Y\<^esub> = {})"

lemma prism_diff_build: "X \<nabla> Y \<Longrightarrow> build\<^bsub>X\<^esub> u \<noteq> build\<^bsub>Y\<^esub> v"
  by (simp add: disjoint_iff_not_equal prism_diff_def)

definition prism_plus :: "('a, 's) prism \<Rightarrow> ('b, 's) prism \<Rightarrow> ('a + 'b, 's) prism" (infixl "+\<^sub>P" 85) where
"X +\<^sub>P Y = \<lparr> prism_match = (\<lambda> s. case (match\<^bsub>X\<^esub> s, match\<^bsub>Y\<^esub> s) of
                                 (Some u, _) \<Rightarrow> Some (Inl u) |
                                 (None, Some v) \<Rightarrow> Some (Inr v) |
                                 (None, None) \<Rightarrow> None),
           prism_build = (\<lambda> v. case v of Inl x \<Rightarrow> build\<^bsub>X\<^esub> x | Inr y \<Rightarrow> build\<^bsub>Y\<^esub> y) \<rparr>"
end
