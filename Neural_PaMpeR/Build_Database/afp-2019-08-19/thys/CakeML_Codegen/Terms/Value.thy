section \<open>A dedicated value type\<close>

theory Value
imports Term_as_Value
begin

datatype "value" =
  is_Vconstr: Vconstr name "value list" |
  Vabs "sclauses" "(name, value) fmap" |
  Vrecabs "(name, sclauses) fmap" name "(name, value) fmap"

type_synonym vrule = "name \<times> value"

setup \<open>Sign.mandatory_path "quickcheck"\<close>

(* FIXME: make private, prevented by bug in datatype_compat; workaround: mandatory path *)
datatype "value" =
  Vconstr name "value list" |
  Vabs "sclauses" "(name \<times> value) list" |
  Vrecabs "(name \<times> sclauses) list" name "(name \<times> value) list"

primrec "Value" :: "quickcheck.value \<Rightarrow> value" where
"Value (quickcheck.Vconstr s vs) = Vconstr s (map Value vs)" |
"Value (quickcheck.Vabs cs \<Gamma>) = Vabs cs (fmap_of_list (map (map_prod id Value) \<Gamma>))" |
"Value (quickcheck.Vrecabs css name \<Gamma>) = Vrecabs (fmap_of_list css) name (fmap_of_list (map (map_prod id Value) \<Gamma>))"

setup \<open>Sign.parent_path\<close>

quickcheck_generator "value"
  constructors: quickcheck.Value

fun vmatch :: "pat \<Rightarrow> value \<Rightarrow> (name, value) fmap option" where
"vmatch (Patvar name) v = Some (fmap_of_list [(name, v)])" |
"vmatch (Patconstr name ps) (Vconstr name' vs) =
  (if name = name' \<and> length ps = length vs then
    map_option (foldl (++\<^sub>f) fmempty) (those (map2 vmatch ps vs))
  else
    None)" |
"vmatch _ _ = None"

lemmas vmatch_induct = vmatch.induct[case_names var constr]

locale value_pred =
  fixes P :: "(name, value) fmap \<Rightarrow> sclauses \<Rightarrow> bool"
  fixes Q :: "name \<Rightarrow> bool"
  fixes R :: "name fset \<Rightarrow> bool"
begin

primrec pred :: "value \<Rightarrow> bool" where
"pred (Vconstr name vs) \<longleftrightarrow> Q name \<and> list_all id (map pred vs)" |
"pred (Vabs cs \<Gamma>) \<longleftrightarrow> pred_fmap id (fmmap pred \<Gamma>) \<and> P \<Gamma> cs" |
"pred (Vrecabs css name \<Gamma>) \<longleftrightarrow>
    pred_fmap id (fmmap pred \<Gamma>) \<and>
    pred_fmap (P \<Gamma>) css \<and>
    name |\<in>| fmdom css \<and>
    R (fmdom css)"

declare pred.simps[simp del]

lemma pred_alt_def[simp, code]:
  "pred (Vconstr name vs) \<longleftrightarrow> Q name \<and> list_all pred vs"
  "pred (Vabs cs \<Gamma>) \<longleftrightarrow> fmpred (\<lambda>_. pred) \<Gamma> \<and> P \<Gamma> cs"
  "pred (Vrecabs css name \<Gamma>) \<longleftrightarrow> fmpred (\<lambda>_. pred) \<Gamma> \<and> pred_fmap (P \<Gamma>) css \<and> name |\<in>| fmdom css \<and> R (fmdom css)"
by (auto simp: list_all_iff pred.simps)

text \<open>
  For technical reasons, we don't introduce an abbreviation for @{prop \<open>fmpred (\<lambda>_. pred) env\<close>}
  here. This locale is supposed to be interpreted with @{command global_interpretation} (or
  @{command sublocale} and a @{theory_text \<open>defines\<close>} clause. However, this does not affect
  abbreviations: the abbreviation would still refer to the locale constant, not the constant
  introduced by the interpretation.
\<close>

lemma vmatch_env:
  assumes "vmatch pat v = Some env" "pred v"
  shows "fmpred (\<lambda>_. pred) env"
using assms proof (induction pat v arbitrary: env rule: vmatch_induct)
  case (constr name ps name' vs)
  hence
    "map_option (foldl (++\<^sub>f) fmempty) (those (map2 vmatch ps vs)) = Some env"
    "name = name'" "length ps = length vs"
    by (auto split: if_splits)
  then obtain envs where "env = foldl (++\<^sub>f) fmempty envs" "map2 vmatch ps vs = map Some envs"
    by (blast dest: those_someD)

  moreover have "fmpred (\<lambda>_. pred) env" if "env \<in> set envs" for env
    proof -
      from that have "Some env \<in> set (map2 vmatch ps vs)"
        unfolding \<open>map2 _ _ _ = _\<close> by simp
      then obtain p v where "p \<in> set ps" "v \<in> set vs" "vmatch p v = Some env"
        apply (rule map2_elemE)
        by auto
      hence "pred v"
        using constr by (simp add: list_all_iff)
      show ?thesis
        by (rule constr; safe?) fact+
    qed

    ultimately show ?case
      by auto
qed auto

end

primrec value_to_sterm :: "value \<Rightarrow> sterm" where
"value_to_sterm (Vconstr name vs) = name $$ map value_to_sterm vs" |
"value_to_sterm (Vabs cs \<Gamma>) = Sabs (map (\<lambda>(pat, t). (pat, subst t (fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>)))) cs)" |
"value_to_sterm (Vrecabs css name \<Gamma>) =
  Sabs (map (\<lambda>(pat, t). (pat, subst t (fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>)))) (the (fmlookup css name)))"

text \<open>
  This locale establishes a connection between a predicate on @{typ value}s with the corresponding
  predicate on @{typ sterm}s, by means of @{const value_to_sterm}.
\<close>

locale pre_value_sterm_pred = value_pred +
  fixes S
  assumes value_to_sterm: "pred v \<Longrightarrow> S (value_to_sterm v)"
begin

corollary value_to_sterm_env:
  assumes "fmpred (\<lambda>_. pred) \<Gamma>"
  shows "fmpred (\<lambda>_. S) (fmmap value_to_sterm \<Gamma>)"
unfolding fmpred_map proof
  fix name v
  assume "fmlookup \<Gamma> name = Some v"
  with assms have "pred v" by (metis fmpredD)
  thus "S (value_to_sterm v)" by (rule value_to_sterm)
qed

end

locale value_sterm_pred = value_pred + S: simple_syntactic_and S for S +
  assumes const: "\<And>name. Q name \<Longrightarrow> S (const name)"
  assumes abs: "\<And>\<Gamma> cs.
    (\<And>n v. fmlookup \<Gamma> n = Some v \<Longrightarrow> pred v \<Longrightarrow> S (value_to_sterm v)) \<Longrightarrow>
    fmpred (\<lambda>_. pred) \<Gamma> \<Longrightarrow>
    P \<Gamma> cs \<Longrightarrow>
    S (Sabs (map (\<lambda>(pat, t). (pat, subst t (fmmap value_to_sterm (fmdrop_fset (frees pat) \<Gamma>)))) cs))"
begin

sublocale pre_value_sterm_pred
proof
  fix v
  assume "pred v"
  then show "S (value_to_sterm v)"
    proof (induction v)
      case (Vconstr x1 x2)
      show ?case
        apply simp
        unfolding S.list_comb
        apply rule
         apply (rule const)
        using Vconstr by (auto simp: list_all_iff)
    next
      case (Vabs x1 x2)
      show ?case
        apply auto
        apply (rule abs)
        using Vabs
        by (auto intro: fmran'I)
    next
      case (Vrecabs x1 x2 x3)
      show ?case
        apply auto
        apply (rule abs)
        using Vrecabs
        by (auto simp: fmlookup_dom_iff fmpred_iff intro: fmran'I)
    qed
qed

end

global_interpretation vwellformed:
  value_sterm_pred
    "\<lambda>_. wellformed_clauses"
    "\<lambda>_. True"
    "\<lambda>_. True"
    wellformed
  defines vwellformed = vwellformed.pred
proof (standard, goal_cases)
  case (2 \<Gamma> cs)
  hence "cs \<noteq> []"
    by simp

  moreover have "wellformed (subst rhs (fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>)))"
    if "(pat, rhs) \<in> set cs" for pat rhs
    proof -
      show ?thesis
        apply (rule subst_wellformed)
        subgoal using 2 that by (force simp: list_all_iff)
        apply (rule fmpred_drop_fset)
        using 2 by auto
    qed

  moreover have "distinct (map (fst \<circ> (\<lambda>(pat, t). (pat, subst t (fmmap value_to_sterm (fmdrop_fset (frees pat) \<Gamma>))))) cs)"
    apply (subst map_cong[OF refl, where g = fst])
    using 2 by auto

  ultimately show ?case
    using 2 by (auto simp: list_all_iff)
qed (auto simp: const_sterm_def)

abbreviation "wellformed_venv \<equiv> fmpred (\<lambda>_. vwellformed)"

global_interpretation vclosed:
  value_sterm_pred
    "\<lambda>\<Gamma> cs. list_all (\<lambda>(pat, t). closed_except t (fmdom \<Gamma> |\<union>| frees pat)) cs"
    "\<lambda>_. True"
    "\<lambda>_. True"
    closed
  defines vclosed = vclosed.pred
proof (standard, goal_cases)
  case (2 \<Gamma> cs)
  show ?case
    apply (simp add: list_all_iff case_prod_twice Sterm.closed_except_simps)
    apply safe
    apply (subst closed_except_def)
    apply (subst subst_frees)
     apply simp
    subgoal
      apply (rule fmpred_drop_fset)
      apply (rule fmpredI)
      apply (rule 2)
       apply assumption
      using 2 by auto
    subgoal
      using 2 by (auto simp: list_all_iff closed_except_def)
    done
qed simp

abbreviation "closed_venv \<equiv> fmpred (\<lambda>_. vclosed)"

context pre_constants begin

sublocale vwelldefined:
  value_sterm_pred
    "\<lambda>_ cs. list_all (\<lambda>(_, t). welldefined t) cs"
    "\<lambda>name. name |\<in>| C"
    "\<lambda>dom. dom |\<subseteq>| heads"
    welldefined
  defines vwelldefined = vwelldefined.pred
proof (standard, goal_cases)
  case (2 \<Gamma> cs)
  note fset_of_list_map[simp del]

  show ?case
    apply simp
    apply (rule ffUnion_least)
    apply (rule fBallI)
    apply (subst (asm) fset_of_list_elem)
    apply simp
    apply (erule imageE)
    apply (simp add: case_prod_twice)
    subgoal for _ x
      apply (cases x)
      apply simp
      apply (rule subst_consts)
      subgoal
        using 2 by (fastforce simp: list_all_iff)
      subgoal
        apply simp
        apply (rule fmpred_drop_fset)
        unfolding fmpred_map
        apply (rule fmpredI)
        using 2 by auto
      done
    done
qed (simp add: all_consts_def)

lemmas vwelldefined_alt_def = vwelldefined.pred_alt_def

end

declare pre_constants.vwelldefined_alt_def[code]

context constructors begin

sublocale vconstructor_value:
  pre_value_sterm_pred
    "\<lambda>_ _. True"
    "\<lambda>name. name |\<in>| C"
    "\<lambda>_. True"
    is_value
  defines vconstructor_value = vconstructor_value.pred
proof
  fix v
  assume "value_pred.pred (\<lambda>_ _. True) (\<lambda>name. name |\<in>| C) (\<lambda>_. True) v"
  then show "is_value (value_to_sterm v)"
    proof (induction v)
      case (Vconstr name vs)
      hence "list_all is_value (map value_to_sterm vs)"
        by (fastforce simp: list_all_iff value_pred.pred_alt_def)
      show ?case
        unfolding value_to_sterm.simps
        apply (rule is_value.constr)
         apply fact
        using Vconstr by (simp add: value_pred.pred_alt_def)
    qed (auto simp: disjnt_def intro: is_value.intros)
qed

lemmas vconstructor_value_alt_def = vconstructor_value.pred_alt_def

abbreviation "vconstructor_value_env \<equiv> fmpred (\<lambda>_. vconstructor_value)"

definition vconstructor_value_rs :: "vrule list \<Rightarrow> bool" where
"vconstructor_value_rs rs \<longleftrightarrow>
  list_all (\<lambda>(_, rhs). vconstructor_value rhs) rs \<and>
  fdisjnt (fset_of_list (map fst rs)) C"

end

declare constructors.vconstructor_value_alt_def[code]
declare constructors.vconstructor_value_rs_def[code]

context pre_constants begin

sublocale not_shadows_vconsts:
  value_sterm_pred
    "\<lambda>_ cs. list_all (\<lambda>(pat, t). fdisjnt all_consts (frees pat) \<and> \<not> shadows_consts t) cs"
    "\<lambda>_. True"
    "\<lambda>_. True"
    "\<lambda>t. \<not> shadows_consts t"
  defines not_shadows_vconsts = not_shadows_vconsts.pred
proof (standard, goal_cases)
  case (2 \<Gamma> cs)
  show ?case
    apply (simp add: list_all_iff list_ex_iff case_prod_twice)
    apply (rule ballI)
    subgoal for x
      apply (cases x, simp)
      apply (rule conjI)
      subgoal
        using 2 by (force simp: list_all_iff)
      apply (rule subst_shadows)
      subgoal
        using 2 by (force simp: list_all_iff)
      apply simp
      apply (rule fmpred_drop_fset)
      apply (rule fmpredI)
      using 2 by auto
    done
qed (auto simp: const_sterm_def app_sterm_def)

lemmas not_shadows_vconsts_alt_def = not_shadows_vconsts.pred_alt_def

abbreviation "not_shadows_vconsts_env \<equiv> fmpred (\<lambda>_ s. not_shadows_vconsts s)"

end

declare pre_constants.not_shadows_vconsts_alt_def[code]

fun term_to_value :: "sterm \<Rightarrow> value" where
"term_to_value t =
  (case strip_comb t of
    (Sconst name, args) \<Rightarrow> Vconstr name (map term_to_value args)
  | (Sabs cs, []) \<Rightarrow> Vabs cs fmempty)"

lemma (in constructors) term_to_value_to_sterm:
  assumes "is_value t"
  shows "value_to_sterm (term_to_value t) = t"
using assms proof induction
  case (constr vs name)

  have "map (value_to_sterm \<circ> term_to_value) vs = map id vs"
    proof (rule list.map_cong0, unfold comp_apply id_apply)
      fix v
      assume "v \<in> set vs"
      with constr show "value_to_sterm (term_to_value v) = v"
        by (simp add: list_all_iff)
    qed
  thus ?case
    apply (simp add: strip_list_comb_const)
    apply (subst const_sterm_def)
    by simp
qed simp

lemma vmatch_dom:
  assumes "vmatch pat v = Some env"
  shows "fmdom env = patvars pat"
using assms proof (induction pat v arbitrary: env rule: vmatch_induct)
  case (constr name ps name' vs)
  hence
    "map_option (foldl (++\<^sub>f) fmempty) (those (map2 vmatch ps vs)) = Some env"
    "name = name'" "length ps = length vs"
    by (auto split: if_splits)
  then obtain envs where "env = foldl (++\<^sub>f) fmempty envs" "map2 vmatch ps vs = map Some envs"
    by (blast dest: those_someD)

  moreover have "fset_of_list (map fmdom envs) = fset_of_list (map patvars ps)"
    proof safe
      fix names
      assume "names |\<in>| fset_of_list (map fmdom envs)"
      hence "names \<in> set (map fmdom envs)"
        unfolding fset_of_list_elem .
      then obtain env where "env \<in> set envs" "names = fmdom env"
        by auto
      hence "Some env \<in> set (map2 vmatch ps vs)"
        unfolding \<open>map2 _ _ _ = _\<close> by simp
      then obtain p v where "p \<in> set ps" "v \<in> set vs" "vmatch p v = Some env"
        by (auto elim: map2_elemE)
      moreover hence "fmdom env = patvars p"
        using constr by fastforce
      ultimately have "names \<in> set (map patvars ps)"
        unfolding \<open>names = _\<close> by simp
      thus "names |\<in>| fset_of_list (map patvars ps)"
        unfolding fset_of_list_elem .
    next
      fix names
      assume "names |\<in>| fset_of_list (map patvars ps)"
      hence "names \<in> set (map patvars ps)"
        unfolding fset_of_list_elem .
      then obtain p where "p \<in> set ps" "names = patvars p"
        by auto
      then obtain v where "v \<in> set vs" "vmatch p v \<in> set (map2 vmatch ps vs)"
        using \<open>length ps = length vs\<close> by (auto elim!: map2_elemE1)
      then obtain env where "env \<in> set envs" "vmatch p v = Some env"
        unfolding \<open>map2 vmatch ps vs = _\<close> by auto
      moreover hence "fmdom env = patvars p"
        using constr \<open>name = name'\<close> \<open>length ps = length vs\<close> \<open>p \<in> set ps\<close> \<open>v \<in> set vs\<close>
        by fastforce
      ultimately have "names \<in> set (map fmdom envs)"
        unfolding \<open>names = _\<close> by auto
      thus "names |\<in>| fset_of_list (map fmdom envs)"
        unfolding fset_of_list_elem .
    qed

  ultimately show ?case
    by (auto simp: fmdom_foldl_add)
qed auto

fun vfind_match :: "sclauses \<Rightarrow> value \<Rightarrow> ((name, value) fmap \<times> term \<times> sterm) option" where
"vfind_match [] _ = None" |
"vfind_match ((pat, rhs) # cs) t =
  (case vmatch (mk_pat pat) t of
    Some env \<Rightarrow> Some (env, pat, rhs)
  | None \<Rightarrow> vfind_match cs t)"

lemma vfind_match_elem:
  assumes "vfind_match cs t = Some (env, pat, rhs)"
  shows "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) t = Some env"
using assms
by (induct cs) (auto split: option.splits)

inductive veq_structure :: "value \<Rightarrow> value \<Rightarrow> bool" where
abs_abs: "veq_structure (Vabs _ _) (Vabs _ _)" |
recabs_recabs: "veq_structure (Vrecabs _ _ _) (Vrecabs _ _ _)" |
constr_constr: "list_all2 veq_structure ts us \<Longrightarrow> veq_structure (Vconstr name ts) (Vconstr name us)"

lemma veq_structure_simps[code, simp]:
  "veq_structure (Vabs cs\<^sub>1 \<Gamma>\<^sub>1) (Vabs cs\<^sub>2 \<Gamma>\<^sub>2)"
  "veq_structure (Vrecabs css\<^sub>1 name\<^sub>1 \<Gamma>\<^sub>1) (Vrecabs css\<^sub>2 name\<^sub>2 \<Gamma>\<^sub>2)"
  "veq_structure (Vconstr name\<^sub>1 ts) (Vconstr name\<^sub>2 us) \<longleftrightarrow> name\<^sub>1 = name\<^sub>2 \<and> list_all2 veq_structure ts us"
by (auto intro: veq_structure.intros elim: veq_structure.cases)

lemma veq_structure_refl[simp]: "veq_structure t t"
by (induction t) (auto simp: list.rel_refl_strong)

global_interpretation vno_abs: value_pred "\<lambda>_ _. False" "\<lambda>_. True" "\<lambda>_. False"
  defines vno_abs = vno_abs.pred .

lemma veq_structure_eq_left:
  assumes "veq_structure t u" "vno_abs t"
  shows "t = u"
using assms proof (induction rule: veq_structure.induct)
  case (constr_constr ts us name)
  have "ts = us" if "list_all vno_abs ts"
    using constr_constr.IH that
    by induction auto
  with constr_constr show ?case
    by auto
qed auto

lemma veq_structure_eq_right:
  assumes "veq_structure t u" "vno_abs u"
  shows "t = u"
using assms proof (induction rule: veq_structure.induct)
  case (constr_constr ts us name)
  have "ts = us" if "list_all vno_abs us"
    using constr_constr.IH that
    by induction auto
  with constr_constr show ?case
    by auto
qed auto

fun vmatch' :: "pat \<Rightarrow> value \<Rightarrow> (name, value) fmap option" where
"vmatch' (Patvar name) v = Some (fmap_of_list [(name, v)])" |
"vmatch' (Patconstr name ps) v =
  (case v of
    Vconstr name' vs \<Rightarrow>
      (if name = name' \<and> length ps = length vs then
        map_option (foldl (++\<^sub>f) fmempty) (those (map2 vmatch' ps vs))
      else
        None)
  | _ \<Rightarrow> None)"

lemma vmatch_vmatch'_eq: "vmatch p v = vmatch' p v"
proof (induction rule: vmatch.induct)
  case (2 name ps name' vs)
  then show ?case
    apply auto
    apply (rule map_option_cong[OF _ refl])
    apply (rule arg_cong[where f = those])
    apply (rule map2_cong[OF refl refl])
    apply blast
    done
qed auto

locale value_struct_rel =
  fixes Q :: "value \<Rightarrow> value \<Rightarrow> bool"
  assumes Q_impl_struct: "Q t\<^sub>1 t\<^sub>2 \<Longrightarrow> veq_structure t\<^sub>1 t\<^sub>2"
  assumes Q_def[simp]: "Q (Vconstr name ts) (Vconstr name' us) \<longleftrightarrow> name = name' \<and> list_all2 Q ts us"
begin

lemma eq_left: "Q t u \<Longrightarrow> vno_abs t \<Longrightarrow> t = u"
using Q_impl_struct by (metis veq_structure_eq_left)

lemma eq_right: "Q t u \<Longrightarrow> vno_abs u \<Longrightarrow> t = u"
using Q_impl_struct by (metis veq_structure_eq_right)

context begin

private lemma vmatch'_rel:
  assumes "Q t\<^sub>1 t\<^sub>2"
  shows "rel_option (fmrel Q) (vmatch' p t\<^sub>1) (vmatch' p t\<^sub>2)"
using assms(1) proof (induction p arbitrary: t\<^sub>1 t\<^sub>2)
  case (Patconstr name ps)
  with Q_impl_struct have "veq_structure t\<^sub>1 t\<^sub>2"
    by blast

  thus ?case
    proof (cases rule: veq_structure.cases)
      case (constr_constr ts us name')

      {
        assume "length ps = length ts"

        have "list_all2 (rel_option (fmrel Q)) (map2 vmatch' ps ts) (map2 vmatch' ps us)"
          using \<open>list_all2 veq_structure ts us\<close> Patconstr \<open>length ps = length ts\<close>
          unfolding \<open>t\<^sub>1 = _\<close> \<open>t\<^sub>2 = _\<close>
          proof (induction arbitrary: ps)
            case (Cons t ts u us ps0)
            then obtain p ps where "ps0 = p # ps"
              by (cases ps0) auto

            have "length ts = length us"
              using Cons by (auto dest: list_all2_lengthD)

            hence "Q t u"
              using \<open>Q (Vconstr name' (t # ts)) (Vconstr name' (u # us))\<close>
              by (simp add: list_all_iff)
            hence "rel_option (fmrel Q) (vmatch' p t) (vmatch' p u)"
              using Cons unfolding \<open>ps0 = _\<close> by simp

            moreover have "list_all2 (rel_option (fmrel Q)) (map2 vmatch' ps ts) (map2 vmatch' ps us)"
              apply (rule Cons)
              subgoal
                apply (rule Cons)
                unfolding \<open>ps0 = _\<close> apply simp
                by assumption
              subgoal
                using \<open>Q (Vconstr name' (t # ts)) (Vconstr name' (u # us))\<close> \<open>length ts = length us\<close>
                by (simp add: list_all_iff)
              subgoal
                using \<open>length ps0 = length (t # ts)\<close>
                unfolding \<open>ps0 = _\<close> by simp
              done

            ultimately show ?case
              unfolding \<open>ps0 = _\<close>
              by auto
          qed auto

        hence "rel_option (list_all2 (fmrel Q)) (those (map2 vmatch' ps ts)) (those (map2 vmatch' ps us))"
          by (rule rel_funD[OF those_transfer])

        have
          "rel_option (fmrel Q)
            (map_option (foldl (++\<^sub>f) fmempty) (those (map2 vmatch' ps ts)))
            (map_option (foldl (++\<^sub>f) fmempty) (those (map2 vmatch' ps us)))"
          apply (rule rel_funD[OF rel_funD[OF option.map_transfer]])
           apply transfer_prover
          by fact
      }
      note * = this

      have "length ts = length us"
        using constr_constr by (auto dest: list_all2_lengthD)

      thus ?thesis
        unfolding \<open>t\<^sub>1 = _\<close> \<open>t\<^sub>2 = _\<close>
        apply auto
        apply (rule *)
        by simp
    qed auto
qed auto

lemma vmatch_rel: "Q t\<^sub>1 t\<^sub>2 \<Longrightarrow> rel_option (fmrel Q) (vmatch p t\<^sub>1) (vmatch p t\<^sub>2)"
unfolding vmatch_vmatch'_eq by (rule vmatch'_rel)

lemma vfind_match_rel:
  assumes "list_all2 (rel_prod (=) R) cs\<^sub>1 cs\<^sub>2"
  assumes "Q t\<^sub>1 t\<^sub>2"
  shows "rel_option (rel_prod (fmrel Q) (rel_prod (=) R)) (vfind_match cs\<^sub>1 t\<^sub>1) (vfind_match cs\<^sub>2 t\<^sub>2)"
using assms(1) proof induction
  case (Cons c\<^sub>1 cs\<^sub>1 c\<^sub>2 cs\<^sub>2)
  moreover obtain pat\<^sub>1 rhs\<^sub>1 where "c\<^sub>1 = (pat\<^sub>1, rhs\<^sub>1)" by fastforce
  moreover obtain pat\<^sub>2 rhs\<^sub>2 where "c\<^sub>2 = (pat\<^sub>2, rhs\<^sub>2)" by fastforce

  ultimately have "pat\<^sub>1 = pat\<^sub>2" "R rhs\<^sub>1 rhs\<^sub>2"
    by auto

  have "rel_option (fmrel Q) (vmatch (mk_pat pat\<^sub>1) t\<^sub>1) (vmatch (mk_pat pat\<^sub>1) t\<^sub>2)"
    by (rule vmatch_rel) fact
  thus ?case
    proof cases
      case None
      thus ?thesis
        unfolding \<open>c\<^sub>1 = _\<close> \<open>c\<^sub>2 = _\<close> \<open>pat\<^sub>1 = _\<close>
        using Cons by auto
    next
      case (Some \<Gamma>\<^sub>1 \<Gamma>\<^sub>2)
      thus ?thesis
        unfolding \<open>c\<^sub>1 = _\<close> \<open>c\<^sub>2 = _\<close> \<open>pat\<^sub>1 = _\<close>
        using \<open>R rhs\<^sub>1 rhs\<^sub>2\<close>
        by auto
    qed
qed simp

lemmas vfind_match_rel' =
  vfind_match_rel[
    where R = "(=)" and cs\<^sub>1 = cs and cs\<^sub>2 = cs for cs,
    unfolded prod.rel_eq,
    OF list.rel_refl, OF refl]

end end

hide_fact vmatch_vmatch'_eq
hide_const vmatch'

global_interpretation veq_structure: value_struct_rel veq_structure
by standard auto

abbreviation env_eq where
"env_eq \<equiv> fmrel (\<lambda>v t. t = value_to_sterm v)"

lemma env_eq_eq:
  assumes "env_eq venv senv"
  shows "senv = fmmap value_to_sterm venv"
proof (rule fmap_ext, unfold fmlookup_map)
  fix name
  from assms have "rel_option (\<lambda>v t. t = value_to_sterm v) (fmlookup venv name) (fmlookup senv name)"
    by auto
  thus "fmlookup senv name = map_option value_to_sterm (fmlookup venv name)"
    by cases auto
qed

context constructors begin

context begin

private lemma vmatch_eq0: "rel_option env_eq (vmatch p v) (smatch' p (value_to_sterm v))"
proof (induction p v rule: vmatch_induct)
  case (constr name ps name' vs)

  have
    "rel_option env_eq
      (map_option (foldl (++\<^sub>f) \<Gamma>) (those (map2 vmatch ps vs)))
      (map_option (foldl (++\<^sub>f) \<Gamma>') (those (map2 smatch' ps (map value_to_sterm vs))))"
    if "length ps = length vs" and "name = name'" and "env_eq \<Gamma> \<Gamma>'" for \<Gamma> \<Gamma>'
    using that constr
    proof (induction arbitrary: \<Gamma> \<Gamma>' rule: list_induct2)
      case (Cons p ps v vs)
      hence "rel_option env_eq (vmatch p v) (smatch' p (value_to_sterm v))"
        by auto
      thus ?case
        proof cases
          case (Some \<Gamma>\<^sub>1 \<Gamma>\<^sub>2)
          thus ?thesis
            apply (simp add: option.map_comp comp_def)
            apply (rule Cons)
            using Cons by auto
        qed simp
    qed fastforce

  thus ?case
    apply (auto simp: strip_list_comb_const)
    apply (subst const_sterm_def, simp)+
    done
qed auto

corollary vmatch_eq:
  assumes "linear p" "vconstructor_value v"
  shows "rel_option env_eq (vmatch (mk_pat p) v) (match p (value_to_sterm v))"
using assms
by (metis smatch_smatch'_eq vmatch_eq0 vconstructor_value.value_to_sterm)

end

end

abbreviation match_related where
"match_related \<equiv> (\<lambda>(\<Gamma>\<^sub>1, pat\<^sub>1, rhs\<^sub>1) (\<Gamma>\<^sub>2, pat\<^sub>2, rhs\<^sub>2). rhs\<^sub>1 = rhs\<^sub>2 \<and> pat\<^sub>1 = pat\<^sub>2 \<and> env_eq \<Gamma>\<^sub>1 \<Gamma>\<^sub>2)"

lemma (in constructors) find_match_eq:
  assumes "list_all (linear \<circ> fst) cs" "vconstructor_value v"
  shows "rel_option match_related (vfind_match cs v) (find_match cs (value_to_sterm v))"
using assms proof (induct cs)
  case (Cons c cs)
  then obtain p t where "c = (p, t)" by fastforce
  hence "rel_option env_eq (vmatch (mk_pat p) v) (match p (value_to_sterm v))"
    using Cons by (fastforce intro: vmatch_eq)
  thus ?case
    using Cons unfolding \<open>c = _\<close>
    by cases auto
qed auto

inductive erelated :: "value \<Rightarrow> value \<Rightarrow> bool" ("_ \<approx>\<^sub>e _") where
constr: "list_all2 erelated ts us \<Longrightarrow> Vconstr name ts \<approx>\<^sub>e Vconstr name us" |
abs: "fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<Longrightarrow> Vabs cs \<Gamma>\<^sub>1 \<approx>\<^sub>e Vabs cs \<Gamma>\<^sub>2" |
rec_abs:
  "pred_fmap (\<lambda>cs. fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2) css \<Longrightarrow>
     Vrecabs css name \<Gamma>\<^sub>1 \<approx>\<^sub>e Vrecabs css name \<Gamma>\<^sub>2"

code_pred erelated .

global_interpretation erelated: value_struct_rel erelated
proof
  fix v\<^sub>1 v\<^sub>2
  assume "v\<^sub>1 \<approx>\<^sub>e v\<^sub>2"
  thus "veq_structure v\<^sub>1 v\<^sub>2"
    by induction (auto intro: list.rel_mono_strong)
next
  fix name name' and ts us :: "value list"
  show "Vconstr name ts \<approx>\<^sub>e Vconstr name' us \<longleftrightarrow> (name = name' \<and> list_all2 erelated ts us)"
    by (auto intro: erelated.intros elim: erelated.cases)
qed

lemma erelated_refl[intro]: "t \<approx>\<^sub>e t"
proof (induction t)
  case Vrecabs
  thus ?case
    apply (auto intro!: erelated.intros fmpredI fmrel_on_fset_refl_strong)
    apply (auto intro: fmran'I)
    done
qed (auto intro!: erelated.intros list.rel_refl_strong fmrel_on_fset_refl_strong fmran'I)

export_code
  value_to_sterm vmatch vwellformed vclosed erelated_i_i pre_constants.vwelldefined
  constructors.vconstructor_value_rs pre_constants.not_shadows_vconsts term_to_value
  vfind_match veq_structure vno_abs
  checking Scala

end