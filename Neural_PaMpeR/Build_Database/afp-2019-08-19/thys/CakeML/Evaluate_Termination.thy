chapter "Functional big-step semantics"

section "Termination proof"

theory Evaluate_Termination
  imports Semantic_Extras
begin

case_of_simps fix_clock_alt_def: fix_clock.simps

primrec size_exp' :: "exp \<Rightarrow> nat" where
"size_exp' (Raise e) = Suc (size_exp' e)" |
[simp del]: "size_exp' (Handle e pes) = Suc (size_exp' e + size_list (\<lambda>(p, es). Suc (size p + es)) (map (map_prod id size_exp') pes))" |
"size_exp' (Con _ es) = Suc (size_list id (map size_exp' es))" |
"size_exp' (Fun _ e) = Suc (size_exp' e)" |
"size_exp' (App _ es) = Suc (size_list id (map size_exp' es))" |
"size_exp' (Log _ e f) = Suc (size_exp' e + size_exp' f)" |
"size_exp' (If e f g) = Suc (size_exp' e + size_exp' f + size_exp' g)" |
[simp del]: "size_exp' (Mat e pes) = Suc (size_exp' e + size_list (\<lambda>(p, es). Suc (size p + es)) (map (map_prod id size_exp') pes))" |
"size_exp' (Let _ e f) = Suc (size_exp' e + size_exp' f)" |
[simp del]: "size_exp' (Letrec defs e) = Suc (size_exp' e + size_list (\<lambda>(_, _, es). Suc (Suc es)) (map (map_prod id (map_prod id size_exp')) defs))" |
"size_exp' (Tannot e _) = Suc (size_exp' e)" |
"size_exp' (Lannot e _) = Suc (size_exp' e)" |
"size_exp' (Lit _) = 0" |
"size_exp' (Var _) = 0"

lemma [simp]:
  "size_exp' (Mat e pes) = Suc (size_exp' e + size_list (size_prod size size_exp') pes)"
apply (simp add: size_exp'.simps size_list_conv_sum_list)
apply (rule arg_cong[where f = sum_list])
apply auto
done

lemma [simp]:
  "size_exp' (Handle e pes) = Suc (size_exp' e + size_list (size_prod size size_exp') pes)"
apply (simp add: size_exp'.simps size_list_conv_sum_list)
apply (rule arg_cong[where f = sum_list])
apply auto
done

lemma [simp]:
  "size_exp' (Letrec defs e) = Suc (size_exp' e + size_list (size_prod (\<lambda>_. 0) (size_prod (\<lambda>_. 0) size_exp')) defs)"
apply (simp add: size_exp'.simps size_list_conv_sum_list)
apply (rule arg_cong[where f = sum_list])
apply auto
done

context begin

private definition fun_evaluate_relation where
"fun_evaluate_relation = inv_image (less_than <*lex*> less_than) (\<lambda>x.
  case x of
    Inr (s, _, es) \<Rightarrow> (clock s, size_list size_exp' es)
  | Inl (s,_,_,pes,_) \<Rightarrow> (clock s, size_list (size_prod size size_exp') pes))"

termination fun_evaluate
by (relation fun_evaluate_relation;
    auto
      simp: fun_evaluate_relation_def fix_clock_alt_def dec_clock_def do_if_def do_log_alt_def
      simp: datatype_record_update
      split: prod.splits state.splits lop.splits v.splits option.splits if_splits tid_or_exn.splits id0.splits list.splits)

end

end