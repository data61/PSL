(* Author: Xingyuan Zhang, Chunhan Wu, Christian Urban *)
theory Myhill_1
imports Folds
        "HOL-Library.While_Combinator" 
begin

section \<open>First direction of MN: \<open>finite partition \<Rightarrow> regular language\<close>\<close>

notation 
  conc (infixr "\<cdot>" 100) and
  star ("_\<star>" [101] 102)

lemma Pair_Collect [simp]:
  shows "(x, y) \<in> {(x, y). P x y} \<longleftrightarrow> P x y"
by simp

text \<open>Myhill-Nerode relation\<close>

definition
  str_eq :: "'a lang \<Rightarrow> ('a list \<times> 'a list) set" ("\<approx>_" [100] 100)
where
  "\<approx>A \<equiv> {(x, y).  (\<forall>z. x @ z \<in> A \<longleftrightarrow> y @ z \<in> A)}"

abbreviation
  str_eq_applied :: "'a list \<Rightarrow> 'a lang \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<approx>_ _")
where
  "x \<approx>A y \<equiv> (x, y) \<in> \<approx>A"

lemma str_eq_conv_Derivs:
  "str_eq A = {(u,v). Derivs u A = Derivs v A}"
  by (auto simp: str_eq_def Derivs_def)  

definition 
  finals :: "'a lang \<Rightarrow> 'a lang set"
where
  "finals A \<equiv> {\<approx>A `` {s} | s . s \<in> A}"

lemma lang_is_union_of_finals: 
  shows "A = \<Union>(finals A)"
unfolding finals_def
unfolding Image_def
unfolding str_eq_def
by (auto) (metis append_Nil2)

lemma finals_in_partitions:
  shows "finals A \<subseteq> (UNIV // \<approx>A)"
unfolding finals_def quotient_def
by auto

subsection \<open>Equational systems\<close>

text \<open>The two kinds of terms in the rhs of equations.\<close>

datatype 'a trm = 
   Lam "'a rexp"            (* Lambda-marker *)
 | Trn "'a lang" "'a rexp"     (* Transition *)

fun 
  lang_trm::"'a trm \<Rightarrow> 'a lang"
where
  "lang_trm (Lam r) = lang r" 
| "lang_trm (Trn X r) = X \<cdot> lang r"

fun 
  lang_rhs::"('a trm) set \<Rightarrow> 'a lang"
where 
  "lang_rhs rhs = \<Union> (lang_trm ` rhs)"

lemma lang_rhs_set:
  shows "lang_rhs {Trn X r | r. P r} = \<Union>{lang_trm (Trn X r) | r. P r}"
by (auto)

lemma lang_rhs_union_distrib:
  shows "lang_rhs A \<union> lang_rhs B = lang_rhs (A \<union> B)"
by simp


text \<open>Transitions between equivalence classes\<close>

definition 
  transition :: "'a lang \<Rightarrow> 'a \<Rightarrow> 'a lang \<Rightarrow> bool" ("_ \<Turnstile>_\<Rightarrow>_" [100,100,100] 100)
where
  "Y \<Turnstile>c\<Rightarrow> X \<equiv> Y \<cdot> {[c]} \<subseteq> X"

text \<open>Initial equational system\<close>

definition
  "Init_rhs CS X \<equiv>  
      if ([] \<in> X) then 
          {Lam One} \<union> {Trn Y (Atom c) | Y c. Y \<in> CS \<and> Y \<Turnstile>c\<Rightarrow> X}
      else 
          {Trn Y (Atom c)| Y c. Y \<in> CS \<and> Y \<Turnstile>c\<Rightarrow> X}"

definition 
  "Init CS \<equiv> {(X, Init_rhs CS X) | X.  X \<in> CS}"


subsection \<open>Arden Operation on equations\<close>

fun 
  Append_rexp :: "'a rexp \<Rightarrow> 'a trm \<Rightarrow> 'a trm"
where
  "Append_rexp r (Lam rexp)   = Lam (Times rexp r)"
| "Append_rexp r (Trn X rexp) = Trn X (Times rexp r)"


definition
  "Append_rexp_rhs rhs rexp \<equiv> (Append_rexp rexp) ` rhs"

definition 
  "Arden X rhs \<equiv> 
     Append_rexp_rhs (rhs - {Trn X r | r. Trn X r \<in> rhs}) (Star (\<Uplus> {r. Trn X r \<in> rhs}))"


subsection \<open>Substitution Operation on equations\<close>

definition 
  "Subst rhs X xrhs \<equiv> 
        (rhs - {Trn X r | r. Trn X r \<in> rhs}) \<union> (Append_rexp_rhs xrhs (\<Uplus> {r. Trn X r \<in> rhs}))"

definition
  Subst_all :: "('a lang \<times> ('a trm) set) set \<Rightarrow> 'a lang \<Rightarrow> ('a trm) set \<Rightarrow> ('a lang \<times> ('a trm) set) set"
where
  "Subst_all ES X xrhs \<equiv> {(Y, Subst yrhs X xrhs) | Y yrhs. (Y, yrhs) \<in> ES}"

definition
  "Remove ES X xrhs \<equiv> 
      Subst_all  (ES - {(X, xrhs)}) X (Arden X xrhs)"


subsection \<open>While-combinator and invariants\<close>

definition 
  "Iter X ES \<equiv> (let (Y, yrhs) = SOME (Y, yrhs). (Y, yrhs) \<in> ES \<and> X \<noteq> Y
                in Remove ES Y yrhs)"

lemma IterI2:
  assumes "(Y, yrhs) \<in> ES"
  and     "X \<noteq> Y"
  and     "\<And>Y yrhs. \<lbrakk>(Y, yrhs) \<in> ES; X \<noteq> Y\<rbrakk> \<Longrightarrow> Q (Remove ES Y yrhs)"
  shows "Q (Iter X ES)"
unfolding Iter_def using assms
by (rule_tac a="(Y, yrhs)" in someI2) (auto)

abbreviation
  "Cond ES \<equiv> card ES \<noteq> 1"

definition 
  "Solve X ES \<equiv> while Cond (Iter X) ES"


definition 
  "distinctness ES \<equiv> 
     \<forall> X rhs rhs'. (X, rhs) \<in> ES \<and> (X, rhs') \<in> ES \<longrightarrow> rhs = rhs'"

definition 
  "soundness ES \<equiv> \<forall>(X, rhs) \<in> ES. X = lang_rhs rhs"

definition 
  "ardenable rhs \<equiv> (\<forall> Y r. Trn Y r \<in> rhs \<longrightarrow> [] \<notin> lang r)"

definition 
  "ardenable_all ES \<equiv> \<forall>(X, rhs) \<in> ES. ardenable rhs"

definition
  "finite_rhs ES \<equiv> \<forall>(X, rhs) \<in> ES. finite rhs"

lemma finite_rhs_def2:
  "finite_rhs ES = (\<forall> X rhs. (X, rhs) \<in> ES \<longrightarrow> finite rhs)"
unfolding finite_rhs_def by auto

definition 
  "rhss rhs \<equiv> {X | X r. Trn X r \<in> rhs}"

definition
  "lhss ES \<equiv> {Y | Y yrhs. (Y, yrhs) \<in> ES}"

definition 
  "validity ES \<equiv> \<forall>(X, rhs) \<in> ES. rhss rhs \<subseteq> lhss ES"

lemma rhss_union_distrib:
  shows "rhss (A \<union> B) = rhss A \<union> rhss B"
by (auto simp add: rhss_def)

lemma lhss_union_distrib:
  shows "lhss (A \<union> B) = lhss A \<union> lhss B"
by (auto simp add: lhss_def)


definition 
  "invariant ES \<equiv> finite ES
                \<and> finite_rhs ES
                \<and> soundness ES 
                \<and> distinctness ES 
                \<and> ardenable_all ES 
                \<and> validity ES"


lemma invariantI:
  assumes "soundness ES" "finite ES" "distinctness ES" "ardenable_all ES" 
          "finite_rhs ES" "validity ES"
  shows "invariant ES"
using assms by (simp add: invariant_def)


declare [[simproc add: finite_Collect]]

lemma finite_Trn:
  assumes fin: "finite rhs"
  shows "finite {r. Trn Y r \<in> rhs}"
using assms by (auto intro!: finite_vimageI simp add: inj_on_def)

lemma finite_Lam:
  assumes fin: "finite rhs"
  shows "finite {r. Lam r \<in> rhs}"
using assms by (auto intro!: finite_vimageI simp add: inj_on_def)

lemma trm_soundness:
  assumes finite:"finite rhs"
  shows "lang_rhs ({Trn X r| r. Trn X r \<in> rhs}) = X \<cdot> (lang (\<Uplus>{r. Trn X r \<in> rhs}))"
proof -
  have "finite {r. Trn X r \<in> rhs}" 
    by (rule finite_Trn[OF finite]) 
  then show "lang_rhs ({Trn X r| r. Trn X r \<in> rhs}) = X \<cdot> (lang (\<Uplus>{r. Trn X r \<in> rhs}))"
    by (simp only: lang_rhs_set lang_trm.simps) (auto simp add: conc_def)
qed

lemma lang_of_append_rexp:
  "lang_trm (Append_rexp r trm) = lang_trm trm \<cdot> lang r"
by (induct rule: Append_rexp.induct)
   (auto simp add: conc_assoc)

lemma lang_of_append_rexp_rhs:
  "lang_rhs (Append_rexp_rhs rhs r) = lang_rhs rhs \<cdot> lang r"
unfolding Append_rexp_rhs_def
by (auto simp add: conc_def lang_of_append_rexp)


subsection \<open>Intial Equational Systems\<close>

lemma defined_by_str:
  assumes "s \<in> X" "X \<in> UNIV // \<approx>A" 
  shows "X = \<approx>A `` {s}"
using assms
unfolding quotient_def Image_def str_eq_def 
by auto

lemma every_eqclass_has_transition:
  assumes has_str: "s @ [c] \<in> X"
  and     in_CS:   "X \<in> UNIV // \<approx>A"
  obtains Y where "Y \<in> UNIV // \<approx>A" and "Y \<cdot> {[c]} \<subseteq> X" and "s \<in> Y"
proof -
  define Y where "Y = \<approx>A `` {s}"
  have "Y \<in> UNIV // \<approx>A" 
    unfolding Y_def quotient_def by auto
  moreover
  have "X = \<approx>A `` {s @ [c]}" 
    using has_str in_CS defined_by_str by blast
  then have "Y \<cdot> {[c]} \<subseteq> X" 
    unfolding Y_def Image_def conc_def
    unfolding str_eq_def
    by clarsimp
  moreover
  have "s \<in> Y" unfolding Y_def 
    unfolding Image_def str_eq_def by simp
  ultimately show thesis using that by blast
qed

lemma l_eq_r_in_eqs:
  assumes X_in_eqs: "(X, rhs) \<in> Init (UNIV // \<approx>A)"
  shows "X = lang_rhs rhs"
proof 
  show "X \<subseteq> lang_rhs rhs"
  proof
    fix x
    assume in_X: "x \<in> X"
    { assume empty: "x = []"
      then have "x \<in> lang_rhs rhs" using X_in_eqs in_X
        unfolding Init_def Init_rhs_def
        by auto
    }
    moreover
    { assume not_empty: "x \<noteq> []"
      then obtain s c where decom: "x = s @ [c]"
        using rev_cases by blast
      have "X \<in> UNIV // \<approx>A" using X_in_eqs unfolding Init_def by auto
      then obtain Y where "Y \<in> UNIV // \<approx>A" "Y \<cdot> {[c]} \<subseteq> X" "s \<in> Y"
        using decom in_X every_eqclass_has_transition by metis
      then have "x \<in> lang_rhs {Trn Y (Atom c)| Y c. Y \<in> UNIV // \<approx>A \<and> Y \<Turnstile>c\<Rightarrow> X}"
        unfolding transition_def
        using decom by (force simp add: conc_def)
      then have "x \<in> lang_rhs rhs" using X_in_eqs in_X
        unfolding Init_def Init_rhs_def by simp
    }
    ultimately show "x \<in> lang_rhs rhs" by blast
  qed
next
  show "lang_rhs rhs \<subseteq> X" using X_in_eqs
    unfolding Init_def Init_rhs_def transition_def
    by auto 
qed


lemma finite_Init_rhs: 
  fixes CS::"(('a::finite) lang) set"
  assumes finite: "finite CS"
  shows "finite (Init_rhs CS X)"
using assms unfolding Init_rhs_def transition_def by simp


lemma Init_ES_satisfies_invariant:
  fixes A::"(('a::finite) lang)"
  assumes finite_CS: "finite (UNIV // \<approx>A)"
  shows "invariant (Init (UNIV // \<approx>A))"
proof (rule invariantI)
  show "soundness (Init (UNIV // \<approx>A))"
    unfolding soundness_def 
    using l_eq_r_in_eqs by auto
  show "finite (Init (UNIV // \<approx>A))" using finite_CS
    unfolding Init_def by simp
  show "distinctness (Init (UNIV // \<approx>A))"     
    unfolding distinctness_def Init_def by simp
  show "ardenable_all (Init (UNIV // \<approx>A))"
    unfolding ardenable_all_def Init_def Init_rhs_def ardenable_def
   by auto 
  show "finite_rhs (Init (UNIV // \<approx>A))"
    using finite_Init_rhs[OF finite_CS]
    unfolding finite_rhs_def Init_def by auto
  show "validity (Init (UNIV // \<approx>A))"
    unfolding validity_def Init_def Init_rhs_def rhss_def lhss_def
    by auto
qed

subsection \<open>Interations\<close>

lemma Arden_preserves_soundness:
  assumes l_eq_r: "X = lang_rhs rhs"
  and not_empty: "ardenable rhs"
  and finite: "finite rhs"
  shows "X = lang_rhs (Arden X rhs)"
proof -
  define A where "A = lang (\<Uplus>{r. Trn X r \<in> rhs})"
  define b where "b = {Trn X r | r. Trn X r \<in> rhs}"
  define B where "B = lang_rhs (rhs - b)"
  have not_empty2: "[] \<notin> A" 
    using finite_Trn[OF finite] not_empty
    unfolding A_def ardenable_def by simp
  have "X = lang_rhs rhs" using l_eq_r by simp
  also have "\<dots> = lang_rhs (b \<union> (rhs - b))" unfolding b_def by auto
  also have "\<dots> = lang_rhs b \<union> B" unfolding B_def by (simp only: lang_rhs_union_distrib)
  also have "\<dots> = X \<cdot> A \<union> B"
    unfolding b_def
    unfolding trm_soundness[OF finite]
    unfolding A_def
    by blast
  finally have "X = X \<cdot> A \<union> B" . 
  then have "X = B \<cdot> A\<star>"
    by (simp add: reversed_Arden[OF not_empty2])
  also have "\<dots> = lang_rhs (Arden X rhs)"
    unfolding Arden_def A_def B_def b_def
    by (simp only: lang_of_append_rexp_rhs lang.simps)
  finally show "X = lang_rhs (Arden X rhs)" by simp
qed 

lemma Append_preserves_finite:
  "finite rhs \<Longrightarrow> finite (Append_rexp_rhs rhs r)"
by (auto simp: Append_rexp_rhs_def)

lemma Arden_preserves_finite:
  "finite rhs \<Longrightarrow> finite (Arden X rhs)"
by (auto simp: Arden_def Append_preserves_finite)

lemma Append_preserves_ardenable:
  "ardenable rhs \<Longrightarrow> ardenable (Append_rexp_rhs rhs r)"
apply (auto simp: ardenable_def Append_rexp_rhs_def)
by (case_tac x, auto simp: conc_def)

lemma ardenable_set_sub:
  "ardenable rhs \<Longrightarrow> ardenable (rhs - A)"
by (auto simp:ardenable_def)

lemma ardenable_set_union:
  "\<lbrakk>ardenable rhs; ardenable rhs'\<rbrakk> \<Longrightarrow> ardenable (rhs \<union> rhs')"
by (auto simp:ardenable_def)

lemma Arden_preserves_ardenable:
  "ardenable rhs \<Longrightarrow> ardenable (Arden X rhs)"
by (simp only:Arden_def Append_preserves_ardenable ardenable_set_sub)


lemma Subst_preserves_ardenable:
  "\<lbrakk>ardenable rhs; ardenable xrhs\<rbrakk> \<Longrightarrow> ardenable (Subst rhs X xrhs)"
by (simp only: Subst_def Append_preserves_ardenable ardenable_set_union ardenable_set_sub)

lemma Subst_preserves_soundness:
  assumes substor: "X = lang_rhs xrhs"
  and finite: "finite rhs"
  shows "lang_rhs (Subst rhs X xrhs) = lang_rhs rhs" (is "?Left = ?Right")
proof-
  define A where "A = lang_rhs (rhs - {Trn X r | r. Trn X r \<in> rhs})"
  have "?Left = A \<union> lang_rhs (Append_rexp_rhs xrhs (\<Uplus>{r. Trn X r \<in> rhs}))"
    unfolding Subst_def
    unfolding lang_rhs_union_distrib[symmetric]
    by (simp add: A_def)
  moreover have "?Right = A \<union> lang_rhs {Trn X r | r. Trn X r \<in> rhs}"
  proof-
    have "rhs = (rhs - {Trn X r | r. Trn X r \<in> rhs}) \<union> ({Trn X r | r. Trn X r \<in> rhs})" by auto
    thus ?thesis 
      unfolding A_def
      unfolding lang_rhs_union_distrib
      by simp
  qed
  moreover 
  have "lang_rhs (Append_rexp_rhs xrhs (\<Uplus>{r. Trn X r \<in> rhs})) = lang_rhs {Trn X r | r. Trn X r \<in> rhs}" 
    using finite substor by (simp only: lang_of_append_rexp_rhs trm_soundness)
  ultimately show ?thesis by simp
qed

lemma Subst_preserves_finite_rhs:
  "\<lbrakk>finite rhs; finite yrhs\<rbrakk> \<Longrightarrow> finite (Subst rhs Y yrhs)"
by (auto simp: Subst_def Append_preserves_finite)

lemma Subst_all_preserves_finite:
  assumes finite: "finite ES"
  shows "finite (Subst_all ES Y yrhs)"
using assms unfolding Subst_all_def by simp

declare [[simproc del: finite_Collect]]

lemma Subst_all_preserves_finite_rhs:
  "\<lbrakk>finite_rhs ES; finite yrhs\<rbrakk> \<Longrightarrow> finite_rhs (Subst_all ES Y yrhs)"
by (auto intro:Subst_preserves_finite_rhs simp add:Subst_all_def finite_rhs_def)

lemma append_rhs_preserves_cls:
  "rhss (Append_rexp_rhs rhs r) = rhss rhs"
apply (auto simp: rhss_def Append_rexp_rhs_def)
apply (case_tac xa, auto simp: image_def)
by (rule_tac x = "Times ra r" in exI, rule_tac x = "Trn x ra" in bexI, simp+)

lemma Arden_removes_cl:
  "rhss (Arden Y yrhs) = rhss yrhs - {Y}"
apply (simp add:Arden_def append_rhs_preserves_cls)
by (auto simp: rhss_def)

lemma lhss_preserves_cls:
  "lhss (Subst_all ES Y yrhs) = lhss ES"
by (auto simp: lhss_def Subst_all_def)

lemma Subst_updates_cls:
  "X \<notin> rhss xrhs \<Longrightarrow> 
      rhss (Subst rhs X xrhs) = rhss rhs \<union> rhss xrhs - {X}"
apply (simp only:Subst_def append_rhs_preserves_cls rhss_union_distrib)
by (auto simp: rhss_def)

lemma Subst_all_preserves_validity:
  assumes sc: "validity (ES \<union> {(Y, yrhs)})"        (is "validity ?A")
  shows "validity (Subst_all ES Y (Arden Y yrhs))"  (is "validity ?B")
proof -
  { fix X xrhs'
    assume "(X, xrhs') \<in> ?B"
    then obtain xrhs 
      where xrhs_xrhs': "xrhs' = Subst xrhs Y (Arden Y yrhs)"
      and X_in: "(X, xrhs) \<in> ES" by (simp add:Subst_all_def, blast)    
    have "rhss xrhs' \<subseteq> lhss ?B"
    proof-
      have "lhss ?B = lhss ES" by (auto simp add:lhss_def Subst_all_def)
      moreover have "rhss xrhs' \<subseteq> lhss ES"
      proof-
        have "rhss xrhs' \<subseteq>  rhss xrhs \<union> rhss (Arden Y yrhs) - {Y}"
        proof -
          have "Y \<notin> rhss (Arden Y yrhs)" 
            using Arden_removes_cl by auto
          thus ?thesis using xrhs_xrhs' by (auto simp: Subst_updates_cls)
        qed
        moreover have "rhss xrhs \<subseteq> lhss ES \<union> {Y}" using X_in sc
          apply (simp only:validity_def lhss_union_distrib)
          by (drule_tac x = "(X, xrhs)" in bspec, auto simp:lhss_def)
        moreover have "rhss (Arden Y yrhs) \<subseteq> lhss ES \<union> {Y}" 
          using sc 
          by (auto simp add: Arden_removes_cl validity_def lhss_def)
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis by simp
    qed
  } thus ?thesis by (auto simp only:Subst_all_def validity_def)
qed

lemma Subst_all_satisfies_invariant:
  assumes invariant_ES: "invariant (ES \<union> {(Y, yrhs)})"
  shows "invariant (Subst_all ES Y (Arden Y yrhs))"
proof (rule invariantI)
  have Y_eq_yrhs: "Y = lang_rhs yrhs" 
    using invariant_ES by (simp only:invariant_def soundness_def, blast)
   have finite_yrhs: "finite yrhs" 
    using invariant_ES by (auto simp:invariant_def finite_rhs_def)
  have ardenable_yrhs: "ardenable yrhs" 
    using invariant_ES by (auto simp:invariant_def ardenable_all_def)
  show "soundness (Subst_all ES Y (Arden Y yrhs))"
  proof -
    have "Y = lang_rhs (Arden Y yrhs)" 
      using Y_eq_yrhs invariant_ES finite_yrhs
      using finite_Trn[OF finite_yrhs]
      apply(rule_tac Arden_preserves_soundness)
      apply(simp_all)
      unfolding invariant_def ardenable_all_def ardenable_def
      apply(auto)
      done
    thus ?thesis using invariant_ES
      unfolding invariant_def finite_rhs_def2 soundness_def Subst_all_def
      by (auto simp add: Subst_preserves_soundness simp del: lang_rhs.simps)
  qed
  show "finite (Subst_all ES Y (Arden Y yrhs))" 
    using invariant_ES by (simp add:invariant_def Subst_all_preserves_finite)
  show "distinctness (Subst_all ES Y (Arden Y yrhs))" 
    using invariant_ES 
    unfolding distinctness_def Subst_all_def invariant_def by auto
  show "ardenable_all (Subst_all ES Y (Arden Y yrhs))"
  proof - 
    { fix X rhs
      assume "(X, rhs) \<in> ES"
      hence "ardenable rhs"  using invariant_ES  
        by (auto simp add:invariant_def ardenable_all_def)
      with ardenable_yrhs 
      have "ardenable (Subst rhs Y (Arden Y yrhs))"
        by (simp add:ardenable_yrhs 
               Subst_preserves_ardenable Arden_preserves_ardenable)
    } thus ?thesis by (auto simp add:ardenable_all_def Subst_all_def)
  qed
  show "finite_rhs (Subst_all ES Y (Arden Y yrhs))"
  proof-
    have "finite_rhs ES" using invariant_ES 
      by (simp add:invariant_def finite_rhs_def)
    moreover have "finite (Arden Y yrhs)"
    proof -
      have "finite yrhs" using invariant_ES 
        by (auto simp:invariant_def finite_rhs_def)
      thus ?thesis using Arden_preserves_finite by auto
    qed
    ultimately show ?thesis 
      by (simp add:Subst_all_preserves_finite_rhs)
  qed
  show "validity (Subst_all ES Y (Arden Y yrhs))"
    using invariant_ES Subst_all_preserves_validity by (auto simp add: invariant_def)
qed

lemma Remove_in_card_measure:
  assumes finite: "finite ES"
  and     in_ES: "(X, rhs) \<in> ES"
  shows "(Remove ES X rhs, ES) \<in> measure card"
proof -
  define f where "f x = ((fst x)::'a lang, Subst (snd x) X (Arden X rhs))" for x
  define ES' where "ES' = ES - {(X, rhs)}"
  have "Subst_all ES' X (Arden X rhs) = f ` ES'" 
    apply (auto simp: Subst_all_def f_def image_def)
    by (rule_tac x = "(Y, yrhs)" in bexI, simp+)
  then have "card (Subst_all ES' X (Arden X rhs)) \<le> card ES'"
    unfolding ES'_def using finite by (auto intro: card_image_le)
  also have "\<dots> < card ES" unfolding ES'_def 
    using in_ES finite by (rule_tac card_Diff1_less)
  finally show "(Remove ES X rhs, ES) \<in> measure card" 
    unfolding Remove_def ES'_def by simp
qed
    

lemma Subst_all_cls_remains: 
  "(X, xrhs) \<in> ES \<Longrightarrow> \<exists> xrhs'. (X, xrhs') \<in> (Subst_all ES Y yrhs)"
by (auto simp: Subst_all_def)

lemma card_noteq_1_has_more:
  assumes card:"Cond ES"
  and e_in: "(X, xrhs) \<in> ES"
  and finite: "finite ES"
  shows "\<exists>(Y, yrhs) \<in> ES. (X, xrhs) \<noteq> (Y, yrhs)"
proof-
  have "card ES > 1" using card e_in finite 
    by (cases "card ES") (auto) 
  then have "card (ES - {(X, xrhs)}) > 0"
    using finite e_in by auto
  then have "(ES - {(X, xrhs)}) \<noteq> {}" using finite by (rule_tac notI, simp)
  then show "\<exists>(Y, yrhs) \<in> ES. (X, xrhs) \<noteq> (Y, yrhs)"
    by auto
qed

lemma iteration_step_measure:
  assumes Inv_ES: "invariant ES"
  and    X_in_ES: "(X, xrhs) \<in> ES"
  and    Cnd:     "Cond ES "
  shows "(Iter X ES, ES) \<in> measure card"
proof -
  have fin: "finite ES" using Inv_ES unfolding invariant_def by simp
  then obtain Y yrhs 
    where Y_in_ES: "(Y, yrhs) \<in> ES" and not_eq: "(X, xrhs) \<noteq> (Y, yrhs)" 
    using Cnd X_in_ES by (drule_tac card_noteq_1_has_more) (auto)
  then have "(Y, yrhs) \<in> ES " "X \<noteq> Y"  
    using X_in_ES Inv_ES unfolding invariant_def distinctness_def
    by auto
  then show "(Iter X ES, ES) \<in> measure card" 
  apply(rule IterI2)
  apply(rule Remove_in_card_measure)
  apply(simp_all add: fin)
  done
qed

lemma iteration_step_invariant:
  assumes Inv_ES: "invariant ES"
  and    X_in_ES: "(X, xrhs) \<in> ES"
  and    Cnd: "Cond ES"
  shows "invariant (Iter X ES)"
proof -
  have finite_ES: "finite ES" using Inv_ES by (simp add: invariant_def)
  then obtain Y yrhs 
    where Y_in_ES: "(Y, yrhs) \<in> ES" and not_eq: "(X, xrhs) \<noteq> (Y, yrhs)" 
    using Cnd X_in_ES by (drule_tac card_noteq_1_has_more) (auto)
  then have "(Y, yrhs) \<in> ES" "X \<noteq> Y" 
    using X_in_ES Inv_ES unfolding invariant_def distinctness_def
    by auto
  then show "invariant (Iter X ES)" 
  proof(rule IterI2)
    fix Y yrhs
    assume h: "(Y, yrhs) \<in> ES" "X \<noteq> Y"
    then have "ES - {(Y, yrhs)} \<union> {(Y, yrhs)} = ES" by auto
    then show "invariant (Remove ES Y yrhs)" unfolding Remove_def
      using Inv_ES
      by (rule_tac Subst_all_satisfies_invariant) (simp) 
  qed
qed

lemma iteration_step_ex:
  assumes Inv_ES: "invariant ES"
  and    X_in_ES: "(X, xrhs) \<in> ES"
  and    Cnd: "Cond ES"
  shows "\<exists>xrhs'. (X, xrhs') \<in> (Iter X ES)"
proof -
  have finite_ES: "finite ES" using Inv_ES by (simp add: invariant_def)
  then obtain Y yrhs 
    where "(Y, yrhs) \<in> ES" "(X, xrhs) \<noteq> (Y, yrhs)" 
    using Cnd X_in_ES by (drule_tac card_noteq_1_has_more) (auto)
  then have "(Y, yrhs) \<in> ES " "X \<noteq> Y"  
    using X_in_ES Inv_ES unfolding invariant_def distinctness_def
    by auto
  then show "\<exists>xrhs'. (X, xrhs') \<in> (Iter X ES)" 
  apply(rule IterI2)
  unfolding Remove_def
  apply(rule Subst_all_cls_remains)
  using X_in_ES
  apply(auto)
  done
qed


subsection \<open>The conclusion of the first direction\<close>

lemma Solve:
  fixes A::"('a::finite) lang"
  assumes fin: "finite (UNIV // \<approx>A)"
  and     X_in: "X \<in> (UNIV // \<approx>A)"
  shows "\<exists>rhs. Solve X (Init (UNIV // \<approx>A)) = {(X, rhs)} \<and> invariant {(X, rhs)}"
proof -
  define Inv where "Inv ES \<longleftrightarrow> invariant ES \<and> (\<exists>rhs. (X, rhs) \<in> ES)" for ES
  have "Inv (Init (UNIV // \<approx>A))" unfolding Inv_def
      using fin X_in by (simp add: Init_ES_satisfies_invariant, simp add: Init_def)
  moreover
  { fix ES
    assume inv: "Inv ES" and crd: "Cond ES"
    then have "Inv (Iter X ES)"
      unfolding Inv_def
      by (auto simp add: iteration_step_invariant iteration_step_ex) }
  moreover
  { fix ES
    assume inv: "Inv ES" and not_crd: "\<not>Cond ES"
    from inv obtain rhs where "(X, rhs) \<in> ES" unfolding Inv_def by auto
    moreover
    from not_crd have "card ES = 1" by simp
    ultimately 
    have "ES = {(X, rhs)}" by (auto simp add: card_Suc_eq) 
    then have "\<exists>rhs'. ES = {(X, rhs')} \<and> invariant {(X, rhs')}" using inv
      unfolding Inv_def by auto }
  moreover
    have "wf (measure card)" by simp
  moreover
  { fix ES
    assume inv: "Inv ES" and crd: "Cond ES"
    then have "(Iter X ES, ES) \<in> measure card"
      unfolding Inv_def
      apply(clarify)
      apply(rule_tac iteration_step_measure)
      apply(auto)
      done }
  ultimately 
  show "\<exists>rhs. Solve X (Init (UNIV // \<approx>A)) = {(X, rhs)} \<and> invariant {(X, rhs)}" 
    unfolding Solve_def by (rule while_rule)
qed

lemma every_eqcl_has_reg:
  fixes A::"('a::finite) lang"
  assumes finite_CS: "finite (UNIV // \<approx>A)"
  and X_in_CS: "X \<in> (UNIV // \<approx>A)"
  shows "\<exists>r. X = lang r" 
proof -
  from finite_CS X_in_CS 
  obtain xrhs where Inv_ES: "invariant {(X, xrhs)}"
    using Solve by metis

  define A where "A = Arden X xrhs"
  have "rhss xrhs \<subseteq> {X}" using Inv_ES 
    unfolding validity_def invariant_def rhss_def lhss_def
    by auto
  then have "rhss A = {}" unfolding A_def 
    by (simp add: Arden_removes_cl)
  then have eq: "{Lam r | r. Lam r \<in> A} = A" unfolding rhss_def
    by (auto, case_tac x, auto)
  
  have "finite A" using Inv_ES unfolding A_def invariant_def finite_rhs_def
    using Arden_preserves_finite by auto
  then have fin: "finite {r. Lam r \<in> A}" by (rule finite_Lam)

  have "X = lang_rhs xrhs" using Inv_ES unfolding invariant_def soundness_def
    by simp
  then have "X = lang_rhs A" using Inv_ES 
    unfolding A_def invariant_def ardenable_all_def finite_rhs_def 
    by (rule_tac Arden_preserves_soundness) (simp_all add: finite_Trn)
  then have "X = lang_rhs {Lam r | r. Lam r \<in> A}" using eq by simp
  then have "X = lang (\<Uplus>{r. Lam r \<in> A})" using fin by auto
  then show "\<exists>r. X = lang r" by blast
qed

lemma bchoice_finite_set:
  assumes a: "\<forall>x \<in> S. \<exists>y. x = f y" 
  and     b: "finite S"
  shows "\<exists>ys. (\<Union> S) = \<Union>(f ` ys) \<and> finite ys"
using bchoice[OF a] b
apply(erule_tac exE)
apply(rule_tac x="fa ` S" in exI)
apply(auto)
done

theorem Myhill_Nerode1:
  fixes A::"('a::finite) lang"
  assumes finite_CS: "finite (UNIV // \<approx>A)"
  shows   "\<exists>r. A = lang r"
proof -
  have fin: "finite (finals A)" 
    using finals_in_partitions finite_CS by (rule finite_subset)
  have "\<forall>X \<in> (UNIV // \<approx>A). \<exists>r. X = lang r" 
    using finite_CS every_eqcl_has_reg by blast
  then have a: "\<forall>X \<in> finals A. \<exists>r. X = lang r"
    using finals_in_partitions by auto
  then obtain rs::"('a rexp) set" where "\<Union> (finals A) = \<Union>(lang ` rs)" "finite rs"
    using fin by (auto dest: bchoice_finite_set)
  then have "A = lang (\<Uplus>rs)" 
    unfolding lang_is_union_of_finals[symmetric] by simp
  then show "\<exists>r. A = lang r" by blast
qed 


end
