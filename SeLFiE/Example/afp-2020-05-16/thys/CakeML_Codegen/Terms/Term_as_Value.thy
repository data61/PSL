section \<open>Irreducible terms (values)\<close>

theory Term_as_Value
imports Sterm
begin

section \<open>Viewing @{typ sterm} as values\<close>

(* FIXME why isn't this declared by BNF *)
declare list.pred_mono[mono]

context constructors begin

inductive is_value :: "sterm \<Rightarrow> bool" where
abs: "is_value (Sabs cs)" |
constr: "list_all is_value vs \<Longrightarrow> name |\<in>| C \<Longrightarrow> is_value (name $$ vs)"

lemma value_distinct:
  "Sabs cs \<noteq> name $$ ts" (is ?P)
  "name $$ ts \<noteq> Sabs cs" (is ?Q)
proof -
  show ?P
    apply (rule list_comb_cases'[where f = "const name" and xs = ts])
     apply (auto simp: const_sterm_def is_app_def elim: unapp_sterm.elims)
    done
  thus ?Q
    by simp
qed

abbreviation value_env :: "(name, sterm) fmap \<Rightarrow> bool" where
"value_env \<equiv> fmpred (\<lambda>_. is_value)"

lemma svar_value[simp]: "\<not> is_value (Svar name)"
proof
  assume "is_value (Svar name)"
  thus False
    apply (cases rule: is_value.cases)
    apply (fold free_sterm_def)
    by simp
qed

lemma value_cases:
  obtains (comb) name vs where "list_all is_value vs" "t = name $$ vs" "name |\<in>| C"
        | (abs) cs where "t = Sabs cs"
        | (nonvalue) "\<not> is_value t"
proof (cases t)
  case Svar
  thus thesis using nonvalue by simp
next
  case Sabs
  thus thesis using abs by (auto intro: is_value.abs)
next
  case (Sconst name)

  have "list_all is_value []" by simp
  have "t = name $$ []" unfolding Sconst by (simp add: const_sterm_def)
  show thesis
    using comb is_value.cases abs nonvalue by blast
next
  case Sapp

  show thesis
    proof (cases "is_value t")
      case False
      thus thesis using nonvalue by simp
    next
      case True
      then obtain name vs where "list_all is_value vs" "t = name $$ vs" "name |\<in>| C"
        unfolding Sapp
        by cases auto
      thus thesis using comb by simp
    qed
qed

end

fun smatch' :: "pat \<Rightarrow> sterm \<Rightarrow> (name, sterm) fmap option" where
"smatch' (Patvar name) t = Some (fmap_of_list [(name, t)])" |
"smatch' (Patconstr name ps) t =
  (case strip_comb t of
    (Sconst name', vs) \<Rightarrow>
      (if name = name' \<and> length ps = length vs then
        map_option (foldl (++\<^sub>f) fmempty) (those (map2 smatch' ps vs))
      else
        None)
  | _ \<Rightarrow> None)"

lemmas smatch'_induct = smatch'.induct[case_names var constr]

context constructors begin

context begin

private lemma smatch_list_comb_is_value:
  assumes "is_value t"
  shows "match (name $$ ps) t = (case strip_comb t of
    (Sconst name', vs) \<Rightarrow>
      (if name = name' \<and> length ps = length vs then
        map_option (foldl (++\<^sub>f) fmempty) (those (map2 match ps vs))
      else
        None)
  | _ \<Rightarrow> None)"
using assms
apply cases
apply (auto simp: strip_list_comb split: option.splits)
apply (subst (2) const_sterm_def)
apply (auto simp: matchs_alt_def)
done

lemma smatch_smatch'_eq:
  assumes "linear pat" "is_value t"
  shows "match pat t = smatch' (mk_pat pat) t"
using assms
proof (induction pat arbitrary: t rule: linear_pat_induct)
  case (comb name args)

  show ?case
    using \<open>is_value t\<close>
    proof (cases rule: is_value.cases)
      case (abs cs)
      thus ?thesis
        by (force simp: strip_list_comb_const)
    next
      case (constr args' name')

      have "map2 match args args' = map2 smatch' (map mk_pat args) args'" if "length args = length args'"
        using that constr(2) comb(2)
        by (induct args args' rule: list_induct2) auto

      thus ?thesis
        using constr
        apply (auto
                simp: smatch_list_comb_is_value strip_list_comb map_option_case strip_list_comb_const
                intro: is_value.intros)
        apply (subst (2) const_sterm_def)
        apply (auto simp: matchs_alt_def)
        done
    qed
qed simp

end

end

end