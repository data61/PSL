subsection\<open>Converting between Resolution and SC proofs\<close>
theory LSC_Resolution
imports LSC Resolution
begin    

lemma literal_subset_sandwich:
  assumes "is_lit_plus F" "cnf F = {C}" "R \<subseteq> C"
  shows "R = \<box> \<or> R = C"
using assms by(cases F rule: is_lit_plus.cases; simp) blast+ (* proof somewhat strange internally\<dots> *)

text\<open>Proof following Gallier~\cite{gallier2015logic}.\<close>
theorem CSC_Resolution_pre: "\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<forall>\<gamma> \<in> set_mset \<Gamma>. is_cnf \<gamma> \<Longrightarrow> (\<Union>(cnf ` set_mset \<Gamma>)) \<turnstile> \<box>"
proof(induction rule: LSC.induct)
  case (Ax k \<Gamma>)
  let ?s = "\<Union>(cnf ` set_mset (\<^bold>\<not> (Atom k), Atom k, \<Gamma>))"
  have "?s \<turnstile> {k\<^sup>+}" "?s \<turnstile> {k\<inverse>}" using Resolution.Ass[where 'a='a] by simp_all
  from Resolution.R[OF this, of k]
  have "?s \<turnstile> \<box>" by simp
  thus ?case by simp
next
  case (BotL \<Gamma>) thus ?case by(simp add: Ass)
next
  case (AndL F G \<Gamma>)
  hence "\<Union>(cnf ` set_mset (F, G, \<Gamma>)) \<turnstile> \<box>" by simp
  thus ?case by(simp add: Un_left_commute sup.assoc)
next
  (* The idea for the whole trickery with F being a literal (is_disj has to only allows right deep formulas)
    and the sandwiching is from Gallier, but mentioned there only in one little sentence. *)
  case (OrL F \<Gamma> G)
  hence "is_cnf (F \<^bold>\<or> G)" by simp
  hence d: "is_disj (F \<^bold>\<or> G)" by simp
  hence db: "is_disj F" "is_lit_plus F" "is_disj G" by (-, cases F) simp_all
  hence "is_cnf F \<and> is_cnf G" by(cases F; cases G; simp)
  with OrL have IH: "(\<Union>(cnf ` set_mset (F, \<Gamma>))) \<turnstile> \<box>" "(\<Union>(cnf ` set_mset (G, \<Gamma>))) \<turnstile> \<box>" by simp_all
  let ?\<Gamma> = "(\<Union>(cnf ` set_mset \<Gamma>))"
  from IH have IH_readable: "cnf F \<union> ?\<Gamma> \<turnstile> \<box>" "cnf G \<union> ?\<Gamma> \<turnstile> \<box>" by auto
  show ?case proof(cases "cnf F = {} \<or> cnf G = {}")
    case True
    hence "cnf (F \<^bold>\<or> G) = {}" by auto
    thus ?thesis using True IH by auto
  next
    case False
    then obtain S T where ST: "cnf F = {S}" "cnf G = {T}"
      using cnf_disj_ex db(1,3) (* try applying meson here. It's weird. and sledgehammer even suggests it. *) by metis
    (* hint: card S \<le> 1 *)
    hence R: "cnf (F \<^bold>\<or> G) = { S \<union> T }" by simp
    have "\<lbrakk>S\<triangleright>?\<Gamma> \<turnstile> \<box>; T\<triangleright>?\<Gamma> \<turnstile> \<box>\<rbrakk> \<Longrightarrow> S \<union> T\<triangleright> ?\<Gamma> \<turnstile> \<box>" proof -
      assume s: "S\<triangleright>?\<Gamma> \<turnstile> \<box>" and t: "T\<triangleright>?\<Gamma> \<turnstile> \<box>"
      hence s_w: "S \<triangleright> S \<union> T \<triangleright> ?\<Gamma> \<turnstile> \<box>" using Resolution_weaken by (metis insert_commute insert_is_Un)
      note Resolution_taint_assumptions[of "{T}" ?\<Gamma> "\<box>" S] t
      then obtain R where R: "S \<union> T \<triangleright> \<Union>(cnf ` set_mset \<Gamma>) \<turnstile> R" "R\<subseteq>S" by (auto simp: Un_commute)
      show ?thesis using literal_subset_sandwich[OF db(2) ST(1) R(2)] proof
        assume "R = \<box>" thus ?thesis using R(1) by blast
      next
        from Resolution_unnecessary[where T="{_}", simplified] R(1)
        have "(R \<triangleright> S \<union> T \<triangleright> ?\<Gamma> \<turnstile> \<box>) = (S \<union> T \<triangleright> ?\<Gamma> \<turnstile> \<box>)"  .
        moreover assume "R = S" 
        ultimately show ?thesis using s_w by simp
      qed
    qed
    thus ?thesis using IH ST R by simp
  qed
  hence case_readable: "cnf (F \<^bold>\<or> G) \<union> ?\<Gamma> \<turnstile> \<box>" by auto
qed auto

corollary LSC_Resolution:
  assumes "\<Gamma> \<Rightarrow>\<^sub>n"
  shows "(\<Union>(cnf ` nnf ` set_mset \<Gamma>)) \<turnstile> \<box>"
proof -
  from assms
  have "image_mset nnf \<Gamma> \<Rightarrow>\<^sub>n" by (simp add: LSC_NNF)
  from LSC_cnf[OF this]
  have "image_mset (cnf_form_of \<circ> nnf) \<Gamma> \<Rightarrow>\<^sub>n" by(simp add: image_mset.compositionality is_nnf_nnf)
  moreover have "\<forall>\<gamma> \<in> set_mset (image_mset (cnf_form_of \<circ> nnf) \<Gamma>). is_cnf \<gamma>" 
    using cnf_form_of_is[where 'a='a, OF is_nnf_nnf] by simp
  moreover note CSC_Resolution_pre
  ultimately have "\<Union>(cnf ` set_mset (image_mset (cnf_form_of \<circ> nnf) \<Gamma>)) \<turnstile> \<box>"  by blast
  hence "\<Union>((\<lambda>F. cnf (cnf_form_of (nnf F))) ` set_mset \<Gamma>) \<turnstile> \<box>" by simp
  thus ?thesis unfolding cnf_cnf[OF is_nnf_nnf] by simp
qed
  
corollary SC_Resolution:
  assumes "\<Gamma> \<Rightarrow> {#}"
  shows "(\<Union>(cnf ` nnf ` set_mset \<Gamma>)) \<turnstile> \<box>"
proof -
  from assms have "image_mset nnf \<Gamma> \<Rightarrow>\<^sub>n" by (simp add: LSC_NNF SC_LSC)
  hence "\<Union>(cnf` nnf ` set_mset (image_mset nnf \<Gamma>)) \<turnstile> \<box>" using LSC_Resolution by blast
  thus ?thesis using is_nnf_nnf_id[where 'a='a] is_nnf_nnf[where 'a='a] by auto
qed

(* Gallier just goes "Any resolution refutation can be transformed to a derivation in SCNF'"
   But we don't know what a resolution refutation is, inductively speaking. *)
(* would have been a bit nicer with orderings on formula to convert mset \<rightarrow> list *)
lemma Resolution_LSC_pre:
  assumes "S \<turnstile> R"
  assumes "finite R"
  assumes "finite S" "Ball S finite"
  shows "\<exists>S' R'. \<forall>\<Gamma>. set R' = R \<and> set (map set S') = S \<and> 
    (disj_of_clause R', {#disj_of_clause c. c \<in># mset S'#} + \<Gamma> \<Rightarrow>\<^sub>n \<longrightarrow> {#disj_of_clause c. c \<in># mset S'#} + \<Gamma> \<Rightarrow>\<^sub>n)"
(* order of quantifiers is important here\<dots> *)
using assms proof(induction S R rule: Resolution.induct)
  case (Ass F S)
  (* Idea: we don't just obtain an S', we obtain an S' that contains R (and not just some reordering of it) *)
  define Sm where "Sm = S - {F}"
  hence Sm: "S = F\<triangleright>Sm" "F \<notin> Sm" using Ass by fast+ (* try doing this with obtain\<dots> *)
  with Ass have fsm: "finite Sm" "Ball Sm finite" by auto
  then obtain Sm' where "Sm = set (map set Sm')" by (metis (full_types) ex_map_conv finite_list)
  moreover obtain R' where [simp]: "F = set R'" using Ass finite_list by blast
  ultimately have S: "S = set (map set (R'#Sm'))" unfolding Sm by simp
  show ?case
    using LSC_Contract[where 'a='a]
    by(intro exI[where x="R'#Sm'"] exI[where x=R']) (simp add: S add_ac)
  (* this was the base case. ugh. *)
next
  case (R S F G k)
  from R.prems have fin: "finite F" "finite G" by simp_all
  from R.IH(1)[OF fin(1) R.prems(2,3)] obtain FR FS where IHF:
    "set FR = F" "set (map set FS) = S"
    "\<And>\<Gamma> GS. (disj_of_clause FR, image_mset disj_of_clause (mset (FS@GS)) + \<Gamma> \<Rightarrow>\<^sub>n 
      \<Longrightarrow> image_mset disj_of_clause (mset (FS@GS)) + \<Gamma> \<Rightarrow>\<^sub>n)"
      by simp (metis add.assoc)
  from R.IH(2)[OF fin(2) R.prems(2,3)] obtain GR GS where IHG:
    "set GR = G" "set (map set GS) = S"
    "\<And>\<Gamma> HS. (disj_of_clause GR, image_mset disj_of_clause (mset (GS@HS)) + \<Gamma> \<Rightarrow>\<^sub>n 
      \<Longrightarrow> image_mset disj_of_clause (mset (GS@HS)) + \<Gamma> \<Rightarrow>\<^sub>n)"
    by simp (metis add.assoc)
  have IH: "image_mset disj_of_clause (mset (FS @ GS)) + \<Gamma> \<Rightarrow>\<^sub>n"
    if "disj_of_clause FR, disj_of_clause GR, image_mset disj_of_clause (mset (FS @ GS)) + \<Gamma> \<Rightarrow>\<^sub>n"
    for \<Gamma> using IHF(3)[of GS \<Gamma>] IHG(3)[of FS "disj_of_clause FR, \<Gamma>"] that
    by(simp add: add_mset_commute add_ac)
  show ?case
    apply(intro exI[where x="FS @ GS"] exI[where x="removeAll (k\<^sup>+) FR @ removeAll (k\<inverse>) GR"] allI impI conjI)
      apply(simp add: IHF IHG;fail)
     apply(insert IHF IHG; simp;fail)
    apply(intro IH)
    apply(auto dest!: LSC_Sim_resolution_la simp add: IHF IHG R.hyps)
  done
qed
  
lemma Resolution_LSC_pre_nodisj: (* I've tried showing this directly instead of Resolution_LSC_pre, but that is surprisingly painful. *)
  assumes "S \<turnstile> R"
  assumes "finite R"
  assumes "finite S" "Ball S finite"
  shows "\<exists>S' R'. \<forall>\<Gamma>. is_nnf_mset \<Gamma> \<longrightarrow> is_disj R' \<and> is_nnf S' \<and> cnf R' = {R} \<and> cnf S' \<subseteq> S \<and> 
    (R', S', \<Gamma> \<Rightarrow>\<^sub>n \<longrightarrow> S', \<Gamma> \<Rightarrow>\<^sub>n)"
proof -
  have mehorder: "F, \<^bold>\<And>G, \<Gamma> = \<^bold>\<And>G, F, \<Gamma>" for F G \<Gamma> by(simp add: add_ac)
  from Resolution_LSC_pre[where 'a='a,OF assms]
  obtain S' R' where o: "\<And>\<Gamma>. is_nnf_mset \<Gamma> \<Longrightarrow> set R' = R \<and> set (map set S') = S \<and> 
  (disj_of_clause R', image_mset disj_of_clause (mset S') + \<Gamma> \<Rightarrow>\<^sub>n \<longrightarrow> image_mset disj_of_clause (mset S') + \<Gamma> \<Rightarrow>\<^sub>n)"
    by blast
  hence p: "is_nnf_mset \<Gamma> \<Longrightarrow> (disj_of_clause R', image_mset disj_of_clause (mset S') + \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> image_mset disj_of_clause (mset S') + \<Gamma> \<Rightarrow>\<^sub>n)" 
    for \<Gamma> by blast
  show ?thesis
    apply(rule exI[where x="\<^bold>\<And>map disj_of_clause S'"])
    apply(rule exI[where x="disj_of_clause R'"])
    apply safe
         apply(intro disj_of_clause_is;fail)
        apply(simp add: cnf_disj o; fail)+
     subgoal using o by(fastforce simp add: cnf_BigAnd cnf_disj)
    subgoal for \<Gamma>
      apply(frule p)
       apply(unfold mehorder)
       apply(drule LSC_BigAndL_inv)
         apply(simp;fail)+
      by (simp add: LSC_BigAndL)     
    done
qed

corollary Resolution_LSC1:
  assumes "S \<turnstile> \<box>"
  shows "\<exists>F. is_nnf F \<and> cnf F \<subseteq> S \<and> {#F#} \<Rightarrow>\<^sub>n"
proof -
  have *: "{f \<union> g |f g. f \<in> F \<and> g \<in> G} = {\<box>} \<Longrightarrow> F = {\<box>}" for F G
  proof (rule ccontr)
    assume m: "{f \<union> g |f g. f \<in> F \<and> g \<in> G} = {\<box>}"
    assume "F \<noteq> {\<box>}"
    hence "F = {} \<or> (\<exists>E. E \<in> F \<and> E \<noteq> \<box>)" by blast
    thus False proof
      assume "F = {}"
      with m show False by simp
    next
      assume "\<exists>E. E \<in> F \<and> E \<noteq> \<box>" then guess E .. note E = this
      show False proof cases
        assume "G = {}" with m show False by simp
      next
        assume "G \<noteq> {}"
        then obtain D where "D \<in> G" by blast
        with E have "E \<union> D \<in> {f \<union> g |f g. f \<in> F \<and> g \<in> G}" by blast
        with m E show False by simp
      qed
    qed
  qed
  have *: "F = {\<box>} \<and> G = {\<box>}" if "{f \<union> g |f g. f \<in> F \<and> g \<in> G} = {\<box>}" for F G
  proof (intro conjI)
    show "G = {\<box>}"
      apply(rule *[of G F])
      apply(subst that[symmetric])
    by blast
  qed (rule *[OF that])
  have *: "is_nnf F \<Longrightarrow> is_nnf_mset \<Gamma> \<Longrightarrow> cnf F = {\<box>} \<Longrightarrow> F,\<Gamma> \<Rightarrow>\<^sub>n" for F \<Gamma>
    apply(induction F rule: cnf.induct; simp)
      apply blast
     apply (metis LSC.LSC.AndL LSC_weaken add_mset_commute singleton_Un_iff)
    apply(drule *; simp add: LSC.LSC.OrL)
  done
  from Resolution_useless_infinite[OF assms]
  obtain S' where su: "S'\<subseteq>S" and fin: "finite S'" "Ball S' finite" and pr: "(S' \<turnstile> \<box>)" by blast
  from Resolution_LSC_pre_nodisj[OF pr finite.emptyI fin]
  obtain S'' where "is_nnf S''" "cnf S'' \<subseteq> S'" "{# S'' #} \<Rightarrow>\<^sub>n" 
    using *[OF disj_is_nnf, of _ Mempty]
    by (metis LSC_weaken add_mset_commute empty_iff set_mset_empty)
  with su show ?thesis by blast
qed

corollary Resolution_SC1:
  assumes "S \<turnstile> \<box>"
  shows "\<exists>F. cnf (nnf F) \<subseteq> S \<and> {#F#} \<Rightarrow> {#}"
  apply(insert Resolution_LSC1[OF assms])
  apply(elim ex_forward)
  apply(elim conjE; intro conjI)
   subgoal by(subst is_nnf_nnf_id; assumption)
  apply(unfold SC_LSC)
  subgoal by (simp;fail)
done
    
(* really, these proofs have to do with sets, multisets and lists.
If I'd introduce finite sets somehow, the chaos would be perfect.
I want out.
*)

end
