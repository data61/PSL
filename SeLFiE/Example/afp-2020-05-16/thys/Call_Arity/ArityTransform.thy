theory ArityTransform
imports ArityAnalysisSig AbstractTransform ArityEtaExpansionSafe
begin

context ArityAnalysisHeapEqvt
begin
sublocale AbstractTransformBound
  "\<lambda> a . inc\<cdot>a"
  "\<lambda> a . pred\<cdot>a"
  "\<lambda> \<Delta> e a . (a, Aheap \<Delta> e\<cdot>a)"
  "fst"
  "snd"
  "\<lambda> _. 0"
  "Aeta_expand"
  "snd"
apply standard
apply (((rule eq_reflection)?, perm_simp, rule)+)
done

abbreviation transform_syn ("\<T>\<^bsub>_\<^esub>") where "\<T>\<^bsub>a\<^esub> \<equiv> transform a"

lemma transform_simps:
  "\<T>\<^bsub>a\<^esub> (App e x) = App (\<T>\<^bsub>inc\<cdot>a\<^esub> e) x"
  "\<T>\<^bsub>a\<^esub> (Lam [x]. e) = Lam [x]. \<T>\<^bsub>pred\<cdot>a\<^esub> e"
  "\<T>\<^bsub>a\<^esub> (Var x) = Var x"
  "\<T>\<^bsub>a\<^esub> (Let \<Gamma> e) = Let (map_transform Aeta_expand (Aheap \<Gamma> e\<cdot>a) (map_transform (\<lambda>a. \<T>\<^bsub>a\<^esub>) (Aheap \<Gamma> e\<cdot>a) \<Gamma>)) (\<T>\<^bsub>a\<^esub> e)"
  "\<T>\<^bsub>a\<^esub> (Bool b) = Bool b"
  "\<T>\<^bsub>a\<^esub> (scrut ? e1 : e2) = (\<T>\<^bsub>0\<^esub> scrut ? \<T>\<^bsub>a\<^esub> e1 : \<T>\<^bsub>a\<^esub> e2)"
  by simp_all
end


end
