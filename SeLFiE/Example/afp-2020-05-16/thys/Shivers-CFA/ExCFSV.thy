section \<open>The exact call cache is a map\<close>

theory ExCFSV
imports ExCF
begin

subsection \<open>Preparations\<close>

text \<open>
Before we state the main result of this section, we need to define
\begin{itemize}
\item the set of binding environments occurring in a semantic value (which exists only if it is a closure),
\item the set of binding environments in a variable environment, using the previous definition,
\item the set of contour counters occurring in a semantic value and
\item the set of contour counters occurring in a variable environment.
\end{itemize}
\<close>

fun benv_in_d :: "d \<Rightarrow> benv set"
  where "benv_in_d (DC (l,\<beta>)) = {\<beta>}"
      | "benv_in_d _ = {}"

definition benv_in_ve :: "venv \<Rightarrow> benv set"
  where "benv_in_ve ve = \<Union>{benv_in_d d | d . d \<in> ran ve}"

fun contours_in_d :: "d \<Rightarrow> contour set"
  where "contours_in_d (DC (l,\<beta>)) = ran \<beta>"
      | "contours_in_d _ = {}"

definition contours_in_ve :: "venv \<Rightarrow> contour set"
  where "contours_in_ve ve = \<Union>{contours_in_d d | d . d \<in> ran ve}"

text \<open>
The following 6 lemmas allow us to calculate the above definition, when applied to constructs used in our semantics function, e.g. map updates, empty maps etc.
\<close>

lemma benv_in_ve_upds:
  assumes eq_length: "length vs = length ds"
      and "\<forall>\<beta>\<in>benv_in_ve ve. Q \<beta>"
      and "\<forall>d'\<in>set ds. \<forall>\<beta>\<in>benv_in_d d'. Q \<beta>"
  shows   "\<forall>\<beta>\<in>benv_in_ve (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds)). Q \<beta>"
proof
  fix \<beta>
  assume ass:"\<beta> \<in> benv_in_ve (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds))"
  then obtain d where "\<beta>\<in>benv_in_d d" and "d \<in> ran (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds))" unfolding benv_in_ve_def by auto
  moreover have "ran (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds)) \<subseteq> ran ve \<union> set ds" using eq_length by(auto intro!:ran_upds) 
  ultimately
  have "d \<in> ran ve \<or> d \<in> set ds" by auto
  thus "Q \<beta>" using assms(2,3) \<open>\<beta>\<in>benv_in_d d\<close> unfolding benv_in_ve_def by auto
qed

lemma benv_in_eval:
  assumes "\<forall>\<beta>'\<in>benv_in_ve ve. Q \<beta>'"
      and "Q \<beta>"
  shows "\<forall>\<beta>\<in>benv_in_d (\<A> v \<beta> ve). Q \<beta>"
proof(cases v)
  case (R _ var)
  thus ?thesis
  proof (cases "\<beta> (fst var)")
    case None with R show ?thesis by simp next
    case (Some cnt) show ?thesis
    proof (cases "ve (var,cnt)")
      case None with Some R show ?thesis by simp next
      case (Some d)
        hence "d \<in> ran ve" unfolding ran_def by blast
        thus ?thesis using Some \<open>\<beta> (fst var) = Some cnt\<close> R assms(1)
          unfolding benv_in_ve_def by auto
    qed
  qed next
  case (L l) thus ?thesis using assms(2) by simp next
  case C thus ?thesis by simp next
  case P thus ?thesis by simp
qed

lemma contours_in_ve_empty[simp]: "contours_in_ve Map.empty = {}"
  unfolding contours_in_ve_def by auto

lemma contours_in_ve_upds:
  assumes eq_length: "length vs = length ds"
      and "\<forall>b'\<in>contours_in_ve ve. Q b'"
      and "\<forall>d'\<in>set ds. \<forall>b'\<in>contours_in_d d'. Q b'"
  shows   "\<forall>b'\<in>contours_in_ve (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds)). Q b'"
proof-
  have "ran (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds)) \<subseteq> ran ve \<union> set ds" using eq_length by(auto intro!:ran_upds)
  thus ?thesis using assms(2,3) unfolding contours_in_ve_def  by blast
qed

lemma contours_in_ve_upds_binds:
  assumes "\<forall>b'\<in>contours_in_ve ve. Q b'"
      and "\<forall>b'\<in>ran \<beta>'. Q b'"
  shows   "\<forall>b'\<in>contours_in_ve (ve ++ map_of (map (\<lambda>(v,l). ((v,b''), \<A> (L l) \<beta>' ve)) ls)). Q b'"
proof
  fix b' assume "b'\<in>contours_in_ve (ve ++ map_of (map (\<lambda>(v,l). ((v,b''), \<A> (L l) \<beta>' ve)) ls))"
  then obtain d where d:"d \<in> ran (ve ++ map_of (map (\<lambda>(v,l). ((v,b''), \<A> (L l) \<beta>' ve)) ls))" and b:"b' \<in> contours_in_d d" unfolding contours_in_ve_def by auto
  
  have "ran (ve ++ map_of (map (\<lambda>(v,l). ((v,b''), \<A> (L l) \<beta>' ve)) ls)) \<subseteq> ran ve \<union> ran (map_of (map (\<lambda>(v,l). ((v,b''), \<A> (L l) \<beta>' ve)) ls))"
    by(auto intro!:ran_concat)
  also
  have "\<dots> \<subseteq> ran ve \<union> snd ` set (map (\<lambda>(v,l). ((v,b''), \<A> (L l) \<beta>' ve)) ls)"
    by (rule Un_mono[of "ran ve" "ran ve", OF subset_refl ran_map_of])
  also
  have "\<dots> \<subseteq> ran ve \<union> set (map (\<lambda>(v,l). (\<A> (L l) \<beta>' ve)) ls)"
    by (rule Un_mono[of "ran ve" "ran ve", OF subset_refl ])auto
  finally
  have "d \<in>  ran ve \<union> set (map (\<lambda>(v,l). (\<A> (L l) \<beta>' ve)) ls)" using d by auto
  thus "Q b'"  using assms b unfolding contours_in_ve_def by auto
qed

lemma contours_in_eval:
  assumes "\<forall>b'\<in>contours_in_ve ve. Q b'"
      and "\<forall>b'\<in> ran \<beta>. Q b'"
  shows "\<forall>b'\<in>contours_in_d (\<A> f \<beta> ve). Q b'"
unfolding contours_in_ve_def
proof(cases f)
  case (R _ var)
  thus ?thesis
  proof (cases "\<beta> (fst var)")
    case None with R show ?thesis by simp next
    case (Some cnt) show ?thesis
    proof (cases "ve (var,cnt)")
      case None with Some R show ?thesis by simp next
      case (Some d)
        hence "d \<in> ran ve" unfolding ran_def by blast
        thus ?thesis using Some \<open>\<beta> (fst var) = Some cnt\<close> R \<open>\<forall>b'\<in>contours_in_ve ve. Q b'\<close>
          unfolding contours_in_ve_def
          by auto
    qed
  qed next
  case (L l) thus ?thesis using \<open>\<forall>b'\<in> ran \<beta>. Q b'\<close> by simp next
  case C thus ?thesis by simp next
  case P thus ?thesis by simp
qed

subsection \<open>The proof\<close>

text \<open>
The set returned by \<open>\<F>\<close> and \<open>\<C>\<close> is actually a partial map from callsite/binding environment pairs to called values. The corresponding predicate in Isabelle is \<open>single_valued\<close>.

We would like to show an auxiliary result about the contour counter passed to \<open>\<F>\<close> and \<open>\<C>\<close> (such that it is an unused counter when passed to \<open>\<F>\<close> and others) first. Unfortunately, this is not possible with induction proofs over fixed points: While proving the inductive case, one does not show results for the function in question, but for an information-theoretical approximation. Thus, any previously shown results are not available.
We therefore intertwine the two inductions in one large proof.

This is a proof by fixpoint induction, so we have are obliged to show that the predicate is admissible and that it holds for the base case, i.e. the empty set. For the proof of admissibiliy, @{theory HOLCF} provides a number of introduction lemmas that, together with some additions in @{theory "Shivers-CFA.HOLCFUtils"} and the continuity lemmas, mechanically proove admissibiliy. The base case is trivial.

The remaining case is the preservation of the properties when applying the recursive equations to a function known to have have the desired property. Here, we break the proof into the various cases that occur in the definitions of \<open>\<F>\<close> and \<open>\<C>\<close> and use the induction hypothesises.
\<close>

lemma cc_single_valued':
      "\<lbrakk> \<forall>b' \<in> contours_in_ve ve. b' < b
       ; \<forall>b' \<in> contours_in_d d. b' < b
       ; \<forall>d' \<in> set ds. \<forall>b' \<in> contours_in_d d'. b' < b
       \<rbrakk>
       \<Longrightarrow>
       (   single_valued (\<F>\<cdot>(Discr (d,ds,ve,b)))
       \<and> (\<forall> ((lab,\<beta>),t) \<in> \<F>\<cdot>(Discr (d,ds,ve, b)). \<exists> b'. b' \<in> ran \<beta> \<and> b \<le> b')
       )"
  and "\<lbrakk> b \<in> ran \<beta>'
       ; \<forall>b'\<in>ran \<beta>'. b' \<le> b
       ; \<forall>b' \<in> contours_in_ve ve. b' \<le> b
       \<rbrakk>
       \<Longrightarrow>
       (   single_valued (\<C>\<cdot>(Discr (c,\<beta>',ve,b)))
       \<and> (\<forall> ((lab,\<beta>),t) \<in> \<C>\<cdot>(Discr (c,\<beta>',ve,b)). \<exists> b'. b' \<in> ran \<beta> \<and> b \<le> b')
       )"
proof(induct arbitrary:d ds ve b c \<beta>' rule:evalF_evalC_induct)
case Admissibility show ?case
  by (intro adm_lemmas adm_ball' adm_prod_split adm_not_conj adm_not_mem adm_single_valued cont2cont)
next
  case Bottom {
    case 1 thus ?case by auto next
    case 2 thus ?case by auto
  }
next
  case (Next evalF evalC)

  txt \<open>Nicer names for the hypothesises:\<close>
  note hyps_F_sv = Next.hyps(1)[THEN conjunct1]
  note hyps_F_b = Next.hyps(1)[THEN conjunct2, THEN bspec]
  note hyps_C_sv = Next.hyps(2)[THEN conjunct1]
  note hyps_C_b = Next.hyps(2)[THEN conjunct2, THEN bspec]
  {
  case (1 d ds ve b)
  thus ?case
  proof (cases "(d,ds,ve,b)" rule:fstate_case, auto simp del:Un_insert_left Un_insert_right)
  txt \<open>Case Closure\<close>
    fix lab' and vs :: "var list" and c and \<beta>' :: benv
    assume prem_d: "\<forall>b'\<in>ran \<beta>'. b' < b"
    assume eq_length: "length vs = length ds"
    have new: "b\<in>ran (\<beta>'(lab' \<mapsto> b))" by simp

    have b_dom_beta: "\<forall>b'\<in> ran (\<beta>'(lab' \<mapsto> b)). b' \<le> b"
    proof fix b' assume "b' \<in> ran (\<beta>'(lab' \<mapsto> b))"
      hence "b' \<in> ran \<beta>' \<or> b' \<le> b" by (auto dest:ran_upd[THEN subsetD])
      thus "b' \<le> b" using prem_d by auto
    qed
    from contours_in_ve_upds[OF eq_length "1.prems"(1) "1.prems"(3)]
    have b_dom_ve: "\<forall>b'\<in>contours_in_ve (ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds)). b' \<le> b"
      by auto

    show "single_valued (evalC\<cdot>(Discr (c, \<beta>'(lab' \<mapsto> b), ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds), b)))"
      by (rule hyps_C_sv[OF new b_dom_beta b_dom_ve, of c])

    fix lab and \<beta> and t
    assume "((lab, \<beta>), t)\<in> evalC\<cdot>(Discr(c, \<beta>'(lab' \<mapsto> b), ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds),b))"
    thus "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'"
      by (auto dest: hyps_C_b[OF new b_dom_beta b_dom_ve])
  next
  txt \<open>Case Plus\<close>
    fix cp and i1 and i2 and cnt
    assume "\<forall>b'\<in>contours_in_d cnt. b' < b"
    hence b_dom_d: "\<forall>b'\<in>contours_in_d cnt. b' < nb b cp" by auto
    have b_dom_ds: "\<forall>d' \<in> set [DI (i1+i2)]. \<forall>b'\<in>contours_in_d d'. b' < nb b cp" by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < nb b cp" using "1.prems"(1) by auto
    {
      fix t
      assume "((cp,[cp \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, nb b cp))"
      hence False by (auto dest:hyps_F_b[OF b_dom_ve b_dom_d b_dom_ds])
    }
    with hyps_F_sv[OF b_dom_ve b_dom_d b_dom_ds]
    show "single_valued ((evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, nb b cp)))
                      \<union> {((cp, [cp \<mapsto> b]), cnt)})"
      by (auto intro:single_valued_insert)

    fix lab \<beta> t
    assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, nb b cp))"
    thus "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'"
      by (auto dest: hyps_F_b[OF b_dom_ve b_dom_d b_dom_ds])
  next
  txt \<open>Case If (true branch)\<close>
    fix cp1 cp2 i cntt cntf
    assume "\<forall>b'\<in>contours_in_d cntt. b' < b"
    hence b_dom_d: "\<forall>b'\<in>contours_in_d cntt. b' < nb b cp1" by auto
    have b_dom_ds: "\<forall>d' \<in> set []. \<forall>b'\<in>contours_in_d d'. b' < nb b cp1" by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < nb b cp1" using "1.prems"(1) by auto
    {
      fix t
      assume "((cp1,[cp1 \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, nb b cp1))"
      hence False by (auto dest:hyps_F_b[OF b_dom_ve b_dom_d b_dom_ds])
    }
    with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct1]
    show "single_valued ((evalF\<cdot>(Discr (cntt, [], ve, nb b cp1)))
                       \<union> {((cp1, [cp1 \<mapsto> b]), cntt)})"
      by (auto intro:single_valued_insert)

    fix lab \<beta> t
    assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, nb b cp1))"
    thus "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'"
      by (auto dest: hyps_F_b[OF b_dom_ve b_dom_d b_dom_ds])
  next
  txt \<open>Case If (false branch). Variable names swapped for easier code reuse.\<close>
    fix cp2 cp1 i cntf cntt
    assume "\<forall>b'\<in>contours_in_d cntt. b' < b"
    hence b_dom_d: "\<forall>b'\<in>contours_in_d cntt. b' < nb b cp1" by auto
    have b_dom_ds: "\<forall>d' \<in> set []. \<forall>b'\<in>contours_in_d d'. b' < nb b cp1" by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < nb b cp1" using "1.prems"(1) by auto
    {
      fix t
      assume "((cp1,[cp1 \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, nb b cp1))"
      hence False by (auto dest:hyps_F_b[OF b_dom_ve b_dom_d b_dom_ds])
    }
    with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct1]
    show "single_valued ((evalF\<cdot>(Discr (cntt, [], ve, nb b cp1)))
                       \<union> {((cp1, [cp1 \<mapsto> b]), cntt)})"
      by (auto intro:single_valued_insert)

    fix lab \<beta> t
    assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, nb b cp1))"
    thus "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'"
      by (auto dest: hyps_F_b[OF b_dom_ve b_dom_d b_dom_ds])
  qed
next
  case (2 ve b c \<beta>')
  thus ?case
  proof (cases c, auto simp add:HOL.Let_def simp del:Un_insert_left Un_insert_right evalV.simps)
  txt \<open>Case App\<close>
    fix lab' f vs

    have prem2': "\<forall>b'\<in>ran \<beta>'. b' < nb b lab'" using "2.prems"(2) by auto
    have prem3': "\<forall>b'\<in>contours_in_ve ve. b' < nb b lab'" using "2.prems"(3) by auto
    note c_in_e = contours_in_eval[OF prem3' prem2']

    have b_dom_d: "\<forall>b'\<in>contours_in_d (evalV f \<beta>' ve). b' < nb b lab'" by(rule c_in_e)
    have b_dom_ds: "\<forall>d' \<in> set (map (\<lambda>v. evalV v \<beta>' ve) vs). \<forall>b'\<in>contours_in_d d'. b' < nb b lab'"
      using c_in_e by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < nb b lab'" by (rule prem3')

    have "\<forall>y. ((lab', \<beta>'), y) \<notin> evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab'))"
    proof(rule allI, rule notI)
      fix y assume "((lab', \<beta>'), y) \<in> evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab'))"
      hence "\<exists>b'. b' \<in> ran \<beta>' \<and> nb b lab' \<le> b'"
        by (auto dest: hyps_F_b[OF b_dom_ve b_dom_d b_dom_ds])
      thus False using prem2' by (auto iff:less_le_not_le)
    qed

    with hyps_F_sv[OF b_dom_ve b_dom_d b_dom_ds]
    show "single_valued (evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab'))
                       \<union> {((lab', \<beta>'), evalV f \<beta>' ve)})"
      by(auto intro:single_valued_insert)

    fix lab \<beta> t
    assume "((lab, \<beta>), t) \<in> (evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab')))"
    thus "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'"
      by (auto dest: hyps_F_b[OF b_dom_ve b_dom_d b_dom_ds])
  next
  txt \<open>Case Let\<close>
    fix lab' ls c'
    have prem2': "\<forall>b'\<in>ran (\<beta>'(lab' \<mapsto> nb b lab')). b' \<le> nb b lab'"
    proof
      fix b' assume "b'\<in>ran (\<beta>'(lab' \<mapsto> nb b lab'))"
      hence "b' \<in> ran \<beta>' \<or> b' = nb b lab'" by (auto dest:ran_upd[THEN subsetD])
      thus "b' \<le> nb b lab'" using "2.prems"(2) by auto
    qed
    have prem3': "\<forall>b'\<in>contours_in_ve ve. b' \<le> nb b lab'" using "2.prems"(3)
      by auto

    note c_in_e = contours_in_eval[OF prem3' prem2']
    note c_in_ve' = contours_in_ve_upds_binds[OF prem3' prem2']

    have b_dom_ve: "\<forall>b' \<in> contours_in_ve (ve ++ map_of (map (\<lambda>(v,l). ((v,nb b lab'), evalV (L l) ((\<beta>'(lab' \<mapsto> nb b lab'))) ve)) ls)). b' \<le> nb b lab'"
      by (rule c_in_ve')
    have b_dom_beta: "\<forall>b'\<in>ran (\<beta>'(lab' \<mapsto> nb b lab')). b' \<le> nb b lab'" by (rule prem2')
    have new: "nb b lab' \<in> ran (\<beta>'(lab' \<mapsto> nb b lab'))" by simp
      
    from hyps_C_sv[OF new b_dom_beta b_dom_ve, of c']
    show "single_valued (evalC\<cdot>(Discr (c', \<beta>'(lab' \<mapsto> nb b lab'),
       ve ++ map_of (map (\<lambda>(v, l).((v, nb b lab'), evalV (L l) (\<beta>'(lab' \<mapsto> nb b lab')) ve))ls),
       nb b lab')))".
    
    fix lab \<beta> t 
    assume "((lab, \<beta>), t) \<in> evalC\<cdot>(Discr (c', \<beta>'(lab' \<mapsto> nb b lab'),
       ve ++ map_of (map (\<lambda>(v, l).((v, nb b lab'), \<A> (L l) (\<beta>'(lab' \<mapsto> nb b lab')) ve))ls),
       nb b lab'))"
    thus "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'"
      by -(drule hyps_C_b[OF new b_dom_beta b_dom_ve], auto)
  qed
 }
qed

lemma "single_valued (\<PR> prog)"
unfolding evalCPS_def
by ((subst HOL.Let_def)+, rule cc_single_valued'[THEN conjunct1], auto)
end
