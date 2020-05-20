theory Array_Iterator
imports Iterator "../Lib/Diff_Array"
begin

lemma idx_iteratei_aux_array_get_Array_conv_nth:
  "idx_iteratei_aux array_get sz i (Array xs) c f \<sigma> = 
   idx_iteratei_aux (!) sz i xs c f \<sigma>"
apply(induct get\<equiv>"(!) :: 'b list \<Rightarrow> nat \<Rightarrow> 'b" sz i xs c f \<sigma> rule: idx_iteratei_aux.induct)
apply(subst (1 2) idx_iteratei_aux.simps)
apply simp
done

lemma idx_iteratei_array_get_Array_conv_nth:
  "idx_iteratei array_get array_length (Array xs) = idx_iteratei nth length xs"
by(simp add: idx_iteratei_def fun_eq_iff idx_iteratei_aux_array_get_Array_conv_nth)

end
