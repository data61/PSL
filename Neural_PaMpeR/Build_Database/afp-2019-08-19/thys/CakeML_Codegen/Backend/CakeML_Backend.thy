section \<open>CakeML backend\<close>

theory CakeML_Backend
imports
  CakeML_Setup
  "../Terms/Value"
  "../Rewriting/Rewriting_Sterm"
begin

subsection \<open>Compilation\<close>

fun mk_ml_pat :: "pat \<Rightarrow> Ast.pat" where
"mk_ml_pat (Patvar s) = Ast.Pvar (as_string s)" |
"mk_ml_pat (Patconstr s args) = Ast.Pcon (Some (Short (as_string s))) (map mk_ml_pat args)"

lemma mk_pat_cupcake[intro]: "is_cupcake_pat (mk_ml_pat pat)"
by (induct pat) (auto simp: list_all_iff)

context begin

private fun frees' :: "term \<Rightarrow> name list" where
"frees' (Free x) = [x]" |
"frees' (t\<^sub>1 $ t\<^sub>2) = frees' t\<^sub>2 @ frees' t\<^sub>1 " |
"frees' (\<Lambda> t) = frees' t" |
"frees' _ = []"

private lemma frees'_eq[simp]: "fset_of_list (frees' t) = frees t"
by (induction t) auto

private lemma frees'_list_comb: "frees' (list_comb f xs) = concat (rev (map frees' xs)) @ frees' f"
by (induction xs arbitrary: f) (auto simp: app_term_def)

private lemma frees'_distinct: "linear pat \<Longrightarrow> distinct (frees' pat)"
proof (induction pat)
  case (App t u)
  hence "distinct (frees' u @ frees' t)"
    by (fastforce intro: distinct_append_fset fdisjnt_swap)
  thus ?case
    by simp
qed auto

private fun pat_bindings' :: "Ast.pat \<Rightarrow> name list" where
"pat_bindings' (Ast.Pvar n) = [Name n]" |
"pat_bindings' (Ast.Pcon _ ps) = concat (rev (map pat_bindings' ps))" |
"pat_bindings' (Ast.Pref p) = pat_bindings' p" |
"pat_bindings' (Ast.Ptannot p _) = pat_bindings' p" |
"pat_bindings' _ = []"

private lemma pat_bindings'_eq:
  "map Name (pats_bindings ps xs) = concat (rev (map pat_bindings' ps)) @ map Name xs"
  "map Name (pat_bindings p xs) = pat_bindings' p @ map Name xs"
by (induction ps xs and p xs rule: pats_bindings_pat_bindings.induct) (auto simp: ac_simps)

private lemma pat_bindings'_empty_eq: "map Name (pat_bindings p []) = pat_bindings' p"
by (simp add: pat_bindings'_eq)

private lemma pat_bindings'_eq_frees: "linear p \<Longrightarrow> pat_bindings' (mk_ml_pat (mk_pat p)) = frees' p"
proof (induction rule: mk_pat.induct)
  case (1 t)

  show ?case
    using \<open>linear t\<close> proof (cases rule: linear_strip_comb_cases)
      case (comb s args)
      have "map (pat_bindings' \<circ> mk_ml_pat \<circ> mk_pat) args = map frees' args"
        proof (rule list.map_cong0, unfold comp_apply)
          fix x
          assume "x \<in> set args"
          moreover hence "linear x"
            using 1 comb by (metis linears_linear linears_strip_comb snd_conv)
          ultimately show "pat_bindings' (mk_ml_pat (mk_pat x)) = frees' x"
            using 1 comb by auto
        qed

      hence "concat (rev (map (pat_bindings' \<circ> mk_ml_pat \<circ> mk_pat) args)) = concat (rev (map frees' args))"
        by metis
      with comb show ?thesis
        apply (fold const_term_def)
        apply (auto simp: strip_list_comb_const frees'_list_comb comp_assoc)
        apply (unfold const_term_def)
        apply simp
        done
    qed auto
qed

lemma mk_pat_distinct: "linear pat \<Longrightarrow> distinct (pat_bindings (mk_ml_pat (mk_pat pat)) [])"
by (metis pat_bindings'_eq_frees pat_bindings'_empty_eq frees'_distinct distinct_map)

end

locale cakeml = pre_constants
begin

fun
  mk_exp :: "name fset \<Rightarrow> sterm \<Rightarrow> exp" and
  mk_clauses :: "name fset \<Rightarrow> (term \<times> sterm) list \<Rightarrow> (Ast.pat \<times> exp) list" and
  mk_con :: "name fset \<Rightarrow> sterm \<Rightarrow> exp" where
"mk_exp _ (Svar s) = Ast.Var (Short (as_string s))" |
"mk_exp _ (Sconst s) = (if s |\<in>| C then Ast.Con (Some (Short (as_string s))) [] else Ast.Var (Short (as_string s)))" |
"mk_exp S (t\<^sub>1 $\<^sub>s t\<^sub>2) = Ast.App Ast.Opapp [mk_con S t\<^sub>1, mk_con S t\<^sub>2]" |
"mk_exp S (Sabs cs) = (
  let n = fresh_fNext S in
  Ast.Fun (as_string n) (Ast.Mat (Ast.Var (Short (as_string n))) (mk_clauses S cs)))" |
"mk_con S t =
  (case strip_comb t of
    (Sconst c, args) \<Rightarrow>
      if c |\<in>| C then Ast.Con (Some (Short (as_string c))) (map (mk_con S) args) else mk_exp S t
   | _ \<Rightarrow> mk_exp S t)" |
"mk_clauses S cs = map (\<lambda>(pat, t). (mk_ml_pat (mk_pat pat), mk_con (frees pat |\<union>| S) t)) cs"

context begin

private lemma mk_exp_cupcake0:
  "wellformed t \<Longrightarrow> is_cupcake_exp (mk_exp S t)"
  "wellformed_clauses cs \<Longrightarrow> cupcake_clauses (mk_clauses S cs) \<and> cake_linear_clauses (mk_clauses S cs)"
  "wellformed t \<Longrightarrow> is_cupcake_exp (mk_con S t)"
proof (induction rule: mk_exp_mk_clauses_mk_con.induct)
  case (5 S t)
  show ?case
    apply (simp split!: prod.splits sterm.splits if_splits)
    subgoal premises prems for args c
      proof -
        from prems have "t = c $$ args"
          apply (fold const_sterm_def)
          by (metis fst_conv list_strip_comb snd_conv)
        show ?thesis
          apply (auto simp: list_all_iff simp del: mk_con.simps)
          apply (rule 5(1))
              apply (rule prems(1)[symmetric])
             apply (rule refl)
            apply (rule prems)
           apply assumption
          using \<open>wellformed t\<close> \<open>t = _\<close>
          apply (auto simp: wellformed.list_comb list_all_iff)
          done
      qed
    using 5 by (auto split: prod.splits sterm.splits)
qed (auto simp: Let_def list_all_iff intro: mk_pat_distinct)

declare mk_con.simps[simp del]

lemma mk_exp_cupcake:
  "wellformed t \<Longrightarrow> is_cupcake_exp (mk_exp S t)"
  "wellformed t \<Longrightarrow> is_cupcake_exp (mk_con S t)"
by (metis mk_exp_cupcake0)+

end

definition mk_letrec_body where
"mk_letrec_body S rs = (
  map (\<lambda>(name, rhs).
    (as_string name, (
      let n = fresh_fNext S in
        (as_string n, Ast.Mat (Ast.Var (Short (as_string n))) (mk_clauses S (sterm.clauses rhs)))))) rs
)"

definition compile_group :: "name fset \<Rightarrow> srule list \<Rightarrow> Ast.dec" where
"compile_group S rs = Ast.Dletrec empty_locs (mk_letrec_body S rs)"

definition compile :: "srule list \<Rightarrow> Ast.prog" where
"compile rs = [Ast.Tdec (compile_group all_consts rs)]"

end

declare cakeml.mk_con.simps[code]
declare cakeml.mk_exp.simps[code]
declare cakeml.mk_clauses.simps[code]
declare cakeml.mk_letrec_body_def[code]
declare cakeml.compile_group_def[code]
declare cakeml.compile_def[code]

locale cakeml' = cakeml + constants

context srules begin

sublocale srules_as_cake?: cakeml' C_info "fst |`| fset_of_list rs" by standard

lemma mk_letrec_cupcake:
  "list_all (\<lambda>(_, _, exp). is_cupcake_exp exp) (mk_letrec_body S rs)"
unfolding mk_letrec_body_def
using all_rules
apply (auto simp: Let_def list_all_iff intro!: mk_pat_cupcake mk_exp_cupcake mk_pat_distinct)
subgoal for a b
  apply (erule ballE[where x = "(a, b)"]; cases b)
         apply (auto simp: list_all_iff is_abs_def term_cases_def)
  done
subgoal for a b
  apply (erule ballE[where x = "(a, b)"]; cases b)
         apply (auto simp: list_all_iff is_abs_def term_cases_def)
  done
done

end

definition compile' where
"compile' C_info rs = cakeml.compile C_info (fst |`| fset_of_list rs) rs"

lemma (in srules) compile'_compile_eq: "compile' C_info rs = compile rs"
unfolding compile'_def ..


subsection \<open>Computability\<close>

export_code cakeml.compile
  checking Scala


subsection \<open>Correctness of semantic functions\<close>

abbreviation related_pat :: "term \<Rightarrow> Ast.pat \<Rightarrow> bool" where
"related_pat t p \<equiv> (p = mk_ml_pat (mk_pat t))"

context cakeml' begin

inductive related_exp :: "sterm \<Rightarrow> exp \<Rightarrow> bool" where
var: "related_exp (Svar name) (Ast.Var (Short (as_string name)))" |
const: "name |\<notin>| C \<Longrightarrow> related_exp (Sconst name) (Ast.Var (Short (as_string name)))" |
constr: "name |\<in>| C \<Longrightarrow> list_all2 related_exp ts es \<Longrightarrow>
          related_exp (name $$ ts) (Ast.Con (Some (Short (as_string name))) es)" |
app: "related_exp t\<^sub>1 u\<^sub>1 \<Longrightarrow> related_exp t\<^sub>2 u\<^sub>2 \<Longrightarrow> related_exp (t\<^sub>1 $\<^sub>s t\<^sub>2) (Ast.App Ast.Opapp [u\<^sub>1, u\<^sub>2])" |
"fun": "list_all2 (rel_prod related_pat related_exp) cs ml_cs \<Longrightarrow>
        n |\<notin>| ids (Sabs cs) \<Longrightarrow> n |\<notin>| all_consts \<Longrightarrow>
          related_exp (Sabs cs) (Ast.Fun (as_string n) (Ast.Mat (Ast.Var (Short (as_string n))) ml_cs))" |
mat: "list_all2 (rel_prod related_pat related_exp) cs ml_cs \<Longrightarrow>
      related_exp scr ml_scr \<Longrightarrow>
          related_exp (Sabs cs $\<^sub>s scr) (Ast.Mat ml_scr ml_cs)"

lemma related_exp_is_cupcake:
  assumes "related_exp t e" "wellformed t"
  shows "is_cupcake_exp e"
using assms proof induction
  case ("fun" cs ml_cs n)
  hence "list_all (\<lambda>(pat, t). linear pat \<and> wellformed t) cs" by simp
  moreover have "cupcake_clauses ml_cs \<and> cake_linear_clauses ml_cs"
    using \<open>list_all2 _ cs ml_cs\<close> \<open>list_all _ cs\<close>
    proof induction
      case (Cons c cs ml_c ml_cs)
      obtain ml_p ml_e where "ml_c = (ml_p, ml_e)" by fastforce
      obtain p t where "c = (p, t)" by fastforce

      have "ml_p = mk_ml_pat (mk_pat p)"
        using Cons unfolding \<open>ml_c = _\<close> \<open>c = _\<close> by simp
      thus ?case
        using Cons unfolding \<open>ml_c = _\<close> \<open>c = _\<close> by (auto intro: mk_pat_distinct)
    qed simp

  ultimately show ?case
    by auto
next
  case (mat cs ml_cs scr ml_scr)
  hence "list_all (\<lambda>(pat, t). linear pat \<and> wellformed t) cs" by simp
  moreover have "cupcake_clauses ml_cs \<and> cake_linear_clauses ml_cs"
    using \<open>list_all2 _ cs ml_cs\<close> \<open>list_all _ cs\<close>
    proof induction
      case (Cons c cs ml_c ml_cs)
      obtain ml_p ml_e where "ml_c = (ml_p, ml_e)" by fastforce
      obtain p t where "c = (p, t)" by fastforce

      have "ml_p = mk_ml_pat (mk_pat p)"
        using Cons unfolding \<open>ml_c = _\<close> \<open>c = _\<close> by simp
      thus ?case
        using Cons unfolding \<open>ml_c = _\<close> \<open>c = _\<close> by (auto intro: mk_pat_distinct)
    qed simp

  ultimately show ?case
    using mat by auto
next
  case (constr name ts es)
  hence "list_all wellformed ts"
    by (simp add: wellformed.list_comb)
  with \<open>list_all2 _ ts es\<close> have "list_all is_cupcake_exp es"
    by induction auto
  thus ?case
    by simp
qed auto

definition related_fun :: "(term \<times> sterm) list \<Rightarrow> name \<Rightarrow> exp \<Rightarrow> bool" where
"related_fun cs n e \<longleftrightarrow>
  n |\<notin>| ids (Sabs cs) \<and> n |\<notin>| all_consts \<and> (case e of
    (Ast.Mat (Ast.Var (Short n')) ml_cs) \<Rightarrow>
      n = Name n' \<and> list_all2 (rel_prod related_pat related_exp) cs ml_cs
  | _ \<Rightarrow> False)"

lemma related_fun_alt_def:
  "related_fun cs n (Ast.Mat (Ast.Var (Short (as_string n))) ml_cs) \<longleftrightarrow>
    list_all2 (rel_prod related_pat related_exp) cs ml_cs \<and>
    n |\<notin>| ids (Sabs cs) \<and> n |\<notin>| all_consts"
unfolding related_fun_def
by auto

lemma related_funE:
  assumes "related_fun cs n e"
  obtains ml_cs
    where "e = Ast.Mat (Ast.Var (Short (as_string n))) ml_cs" "n |\<notin>| ids (Sabs cs)" "n |\<notin>| all_consts"
      and "list_all2 (rel_prod related_pat related_exp) cs ml_cs"
using assms unfolding related_fun_def
by (simp split: exp0.splits id0.splits)

lemma related_exp_fun:
  "related_fun cs n e \<longleftrightarrow> related_exp (Sabs cs) (Ast.Fun (as_string n) e) \<and> n |\<notin>| ids (Sabs cs) \<and> n |\<notin>| all_consts"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  hence "related_exp (Sabs cs) (Ast.Fun (as_string n) e)" by simp
  thus ?lhs
    by cases (auto simp: related_fun_def dest: name.expand)
next
  assume ?lhs
  thus ?rhs
    by (auto intro: related_exp.fun elim: related_funE)
qed

inductive related_v :: "value \<Rightarrow> v \<Rightarrow> bool" where
conv:
  "list_all2 related_v us vs \<Longrightarrow>
    related_v (Vconstr name us) (Conv (Some (as_string name, _)) vs)" |
closure:
  "related_fun cs n e \<Longrightarrow>
   fmrel_on_fset (ids (Sabs cs)) related_v \<Gamma> (fmap_of_ns (sem_env.v env)) \<Longrightarrow>
    related_v (Vabs cs \<Gamma>) (Closure env (as_string n) e)" |
rec_closure:
  "fmrel_on_fset (fbind (fmran css) (ids \<circ> Sabs)) related_v \<Gamma> (fmap_of_ns (sem_env.v env)) \<Longrightarrow>
   fmrel (\<lambda>cs. \<lambda>(n, e). related_fun cs n e) css (fmap_of_list (map (map_prod Name (map_prod Name id)) exps)) \<Longrightarrow>
    related_v (Vrecabs css name \<Gamma>) (Recclosure env exps (as_string name))"

abbreviation var_env :: "(name, value) fmap \<Rightarrow> (string \<times> v) list \<Rightarrow> bool" where
"var_env \<Gamma> ns \<equiv> fmrel related_v \<Gamma> (fmap_of_list (map (map_prod Name id) ns))"

lemma related_v_ext:
  assumes "related_v v ml_v"
  assumes "v' \<approx>\<^sub>e v"
  shows "related_v v' ml_v"
using assms proof (induction arbitrary: v')
  case (conv us ml_us name)
  obtain ts where "v' = Vconstr name ts" "list_all2 erelated ts us"
    using \<open>v' \<approx>\<^sub>e Vconstr name us\<close>
    by cases auto

  have "list_all2 related_v ts ml_us"
    by (rule list_all2_trans[OF _ \<open>list_all2 erelated ts us\<close> conv(1)]) auto

  thus ?case
    using conv unfolding \<open>v' = _\<close>
    by (auto intro: related_v.conv)
next
  case (closure cs n e \<Gamma>\<^sub>2 env)
  obtain \<Gamma>\<^sub>1 where "v' = Vabs cs \<Gamma>\<^sub>1" "fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2"
    using \<open>v' \<approx>\<^sub>e _\<close>
    by cases auto

  have "fmrel_on_fset (ids (Sabs cs)) related_v \<Gamma>\<^sub>1 (fmap_of_ns (sem_env.v env))"
    apply rule
    subgoal premises prems for x
      apply (insert prems)
      apply (drule fmrel_on_fsetD)
       apply (rule closure)
      subgoal
        apply (insert prems)
        apply (drule fmrel_on_fsetD)
         apply (rule \<open>fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2\<close>)
        apply (metis (mono_tags, lifting) option.rel_sel)
        done
      done
    done

  show ?case
    unfolding \<open>v' = _\<close>
    by (rule related_v.closure) fact+
next
  case (rec_closure css \<Gamma>\<^sub>2 env exps name)
  obtain \<Gamma>\<^sub>1 where "v' = Vrecabs css name \<Gamma>\<^sub>1" "pred_fmap (\<lambda>cs. fmrel_on_fset (ids (Sabs cs)) erelated \<Gamma>\<^sub>1 \<Gamma>\<^sub>2) css"
    using \<open>v' \<approx>\<^sub>e _\<close>
    by cases auto

  have "fmrel_on_fset (fbind (fmran css) (ids \<circ> Sabs)) related_v \<Gamma>\<^sub>1 (fmap_of_ns (sem_env.v env))"
    apply (rule fmrel_on_fsetI)
    subgoal premises prems for x
      apply (insert prems)
      apply (drule fmrel_on_fsetD)
       apply (rule rec_closure)
      subgoal
        apply (insert prems)
        apply (erule fbindE)
        apply (drule pred_fmapD[OF \<open>pred_fmap _ css\<close>])
        unfolding comp_apply
        apply (drule fmrel_on_fsetD)
         apply assumption
        apply (metis (mono_tags, lifting) option.rel_sel)
        done
      done
    done

  show ?case
    unfolding \<open>v' = _\<close>
    by (rule related_v.rec_closure) fact+
qed

context begin

private inductive match_result_related :: "(string \<times> v) list \<Rightarrow> (string \<times> v) list match_result \<Rightarrow> (name, value) fmap option \<Rightarrow> bool" for eenv where
no_match: "match_result_related eenv No_match None" |
error: "match_result_related eenv Match_type_error _" |
match: "var_env \<Gamma> eenv_m \<Longrightarrow> match_result_related eenv (Match (eenv_m @ eenv)) (Some \<Gamma>)"

private corollary match_result_related_empty: "match_result_related eenv (Match eenv) (Some fmempty)"
proof -
  have "match_result_related eenv (Match ([] @ eenv)) (Some fmempty)"
    by (rule match_result_related.match) auto
  thus ?thesis
    by simp
qed

private fun is_Match :: "'a match_result \<Rightarrow> bool" where
"is_Match (Match _) \<longleftrightarrow> True" |
"is_Match _ \<longleftrightarrow> False"

lemma cupcake_pmatch_related:
  assumes "related_v v ml_v"
  shows "match_result_related eenv (cupcake_pmatch as_static_cenv (mk_ml_pat pat) ml_v eenv) (vmatch pat v)"
using assms proof (induction pat arbitrary: v ml_v eenv)
  case (Patvar name)
  have "var_env (fmap_of_list [(name, v)]) [(as_string name, ml_v)]"
    using Patvar by auto
  hence "match_result_related eenv (Match ([(as_string name, ml_v)] @ eenv)) (Some (fmap_of_list [(name, v)]))"
    by (rule match_result_related.match)
  thus ?case
    by simp
next
  case (Patconstr name ps v0)

  show ?case
    using Patconstr.prems
    proof (cases rule: related_v.cases)
      case (conv us vs name' _)

      define f where
      "f p v m =
        (case m of
          Match env \<Rightarrow> cupcake_pmatch as_static_cenv p v env
        | m \<Rightarrow> m)" for p v m

      {
        assume "name = name'"

        assume "length ps = length us"
        hence "list_all2 (\<lambda>_ _. True) us ps"
          by (induct rule: list_induct2) auto
        hence "list_all3 (\<lambda>t p v. related_v t v) us ps vs"
          using \<open>list_all2 related_v us vs\<close>
          by (rule list_all3_from_list_all2s) auto

        hence *: "match_result_related eenv
                    (Matching.fold2 f Match_type_error (map mk_ml_pat ps) vs (Match (eenv_m @ eenv)))
                    (map_option (foldl (++\<^sub>f) \<Gamma>) (those (map2 vmatch ps us)))" (is "?rel")
          if "var_env \<Gamma> eenv_m"
          for eenv_m \<Gamma>
          using Patconstr.IH \<open>related_v v0 ml_v\<close> that
          proof (induction us ps vs arbitrary: \<Gamma> eenv_m rule: list_all3_induct)
            case (Cons t us p ps v vs)

            have "match_result_related (eenv_m @ eenv) (cupcake_pmatch as_static_cenv (mk_ml_pat p) v (eenv_m @ eenv)) (vmatch p t)"
              using Cons by simp

            thus ?case
              proof cases
                case no_match
                thus ?thesis
                  unfolding f_def
                  apply (cases "length (map mk_ml_pat ps) = length vs")
                  by (fastforce intro: match_result_related.intros simp:cup_pmatch_list_nomatch cup_pmatch_list_length_neq)+
              next
                case error
                thus ?thesis
                  unfolding f_def
                  apply (cases "length (map mk_ml_pat ps) = length vs")
                  by (fastforce intro: match_result_related.intros simp:cup_pmatch_list_typerr cup_pmatch_list_length_neq)+
              next
                case (match \<Gamma>' eenv_m')

                have "match_result_related eenv
                        (Matching.fold2 f Match_type_error (map mk_ml_pat ps) vs (Match ((eenv_m' @ eenv_m) @ eenv)))
                        (map_option (foldl (++\<^sub>f) (\<Gamma> ++\<^sub>f \<Gamma>')) (those (map2 vmatch ps us)))"
                  proof (rule Cons, rule Cons)
                    show "var_env (\<Gamma> ++\<^sub>f \<Gamma>') (eenv_m' @ eenv_m)"
                      using \<open>var_env \<Gamma> eenv_m\<close> match
                      by force
                  qed (simp | fact)+

                thus ?thesis
                  using match
                  unfolding f_def
                  by (auto simp: map_option.compositionality comp_def)
              qed
          qed (auto intro: match_result_related.match)

        moreover have "var_env fmempty []"
          by force

        ultimately have "?rel [] fmempty"
          by fastforce

        hence ?thesis
          using conv \<open>length ps = length us\<close>
          unfolding f_def \<open>name = name'\<close>
          by (auto intro: match_result_related.intros split: option.splits elim: static_cenv_lookup)
      }
      moreover
      {
        assume "name \<noteq> name'"
        with conv have ?thesis
          by (auto intro: match_result_related.intros split: option.splits elim: same_ctor.elims simp: name.expand)
      }
      moreover
      {
        let ?fold = "Matching.fold2 f Match_type_error (map mk_ml_pat ps) vs (Match eenv)"

        assume *: "length ps \<noteq> length us"
        moreover have "length us = length vs"
          using \<open>list_all2 related_v us vs\<close> by (rule list_all2_lengthD)
        ultimately have "length ps \<noteq> length vs"
          by simp

        moreover have "\<not> is_Match (Matching.fold2 f err xs ys init)"
          if "\<not> is_Match err" and "length xs \<noteq> length ys" for init err xs ys
          using that f_def
          by (induct f err xs ys init rule: fold2.induct) (auto split: match_result.splits)
        ultimately have "\<not> is_Match ?fold"
          by simp
        hence "?fold = Match_type_error \<or> ?fold = No_match"
          by (cases ?fold) auto

        with * have ?thesis
          unfolding \<open>ml_v = _\<close> \<open>v0 = _\<close> f_def
          by (auto intro: match_result_related.intros split: option.splits)
      }

      ultimately show ?thesis
        by auto
    qed (auto intro: match_result_related.intros)
qed

lemma match_all_related:
  assumes "list_all2 (rel_prod related_pat related_exp) cs ml_cs"
  assumes "list_all (\<lambda>(pat, _). linear pat) cs"
  assumes "related_v v ml_v"
  assumes "cupcake_match_result as_static_cenv ml_v ml_cs Bindv = Rval (ml_rhs, ml_pat, eenv)"
  obtains rhs pat \<Gamma> where
    "ml_pat = mk_ml_pat (mk_pat pat)"
    "related_exp rhs ml_rhs"
    "vfind_match cs v = Some (\<Gamma>, pat, rhs)"
    "var_env \<Gamma> eenv"
using assms
proof (induction cs ml_cs arbitrary: thesis ml_pat ml_rhs rule: list_all2_induct)
  case (Cons c cs ml_c ml_cs)
  moreover obtain pat0 rhs0 where "c = (pat0, rhs0)" by fastforce
  moreover obtain ml_pat0 ml_rhs0 where "ml_c = (ml_pat0, ml_rhs0)" by fastforce
  ultimately have "ml_pat0 = mk_ml_pat (mk_pat pat0)" "related_exp rhs0 ml_rhs0" by auto

  have "linear pat0"
    using Cons(5) unfolding \<open>c = _\<close> by simp+

  have rel: "match_result_related [] (cupcake_pmatch as_static_cenv (mk_ml_pat (mk_pat pat0)) ml_v []) (vmatch (mk_pat pat0) v)"
    by (rule cupcake_pmatch_related) fact+

  show ?case
    proof (cases "cupcake_pmatch as_static_cenv ml_pat0 ml_v []")
      case Match_type_error
      hence False
        using Cons(7) unfolding \<open>ml_c = _\<close>
        by (simp split: if_splits)
      thus thesis ..
    next
      case No_match

      show thesis
        proof (rule Cons(3))
          show "cupcake_match_result as_static_cenv ml_v ml_cs Bindv = Rval (ml_rhs, ml_pat, eenv)"
            using Cons(7) No_match unfolding \<open>ml_c = _\<close>
            by (simp split: if_splits)
        next
          fix pat rhs \<Gamma>
          assume "ml_pat = mk_ml_pat (mk_pat pat)"
          assume "related_exp rhs ml_rhs"
          assume "vfind_match cs v = Some (\<Gamma>, pat, rhs)"
          assume "var_env \<Gamma> eenv"

          from rel have "match_result_related [] No_match (vmatch (mk_pat pat0) v)"
            using No_match unfolding \<open>ml_pat0 = _\<close>
            by simp
          hence "vmatch (mk_pat pat0) v = None"
            by (cases rule: match_result_related.cases)

          show thesis
            proof (rule Cons(4))
              show "vfind_match (c # cs) v = Some (\<Gamma>, pat, rhs)"
                unfolding \<open>c = _\<close>
                using \<open>vfind_match cs v = _\<close> \<open>vmatch (mk_pat pat0) v = _\<close>
                by simp
            qed fact+
        next
          show "list_all (\<lambda>(pat, _). linear pat) cs"
            using Cons(5) by simp
        qed fact+
    next
      case (Match eenv')
      hence "ml_rhs = ml_rhs0" "ml_pat = ml_pat0" "eenv = eenv'"
        using Cons(7) unfolding \<open>ml_c = _\<close>
        by (simp split: if_splits)+

      from rel have "match_result_related [] (Match eenv') (vmatch (mk_pat pat0) v) "
        using Match unfolding \<open>ml_pat0 = _\<close> by simp
      then obtain \<Gamma> where "vmatch (mk_pat pat0) v = Some \<Gamma>" "var_env \<Gamma> eenv'"
        by (cases rule: match_result_related.cases) auto

      show thesis
        proof (rule Cons(4))
          show "ml_pat = mk_ml_pat (mk_pat pat0)"
            unfolding \<open>ml_pat = _\<close> by fact
        next
          show "related_exp rhs0 ml_rhs"
            unfolding \<open>ml_rhs = _\<close> by fact
        next
          show "var_env \<Gamma> eenv"
            unfolding \<open>eenv = _\<close> by fact
        next
          show "vfind_match (c # cs) v = Some (\<Gamma>, pat0, rhs0)"
            unfolding \<open>c = _\<close>
            using \<open>vmatch (mk_pat pat0) v = Some \<Gamma>\<close>
            by simp
        qed
    qed
qed simp

end end

end