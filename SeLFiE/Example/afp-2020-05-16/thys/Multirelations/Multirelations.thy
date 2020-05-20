(*
Title: Binary Multirelations
Author: Hitoshi Furusawa, Georg Struth
Maintainer: <g.struth at sheffield.ac.uk>
*)

section \<open>Multirelations\<close>

theory Multirelations
imports C_Algebras
begin

subsection \<open>Basic Definitions\<close>

text \<open>We define a type synonym for multirelations.\<close>

type_synonym 'a mrel = "('a * ('a set)) set"

no_notation  s_prod (infixl "\<cdot>" 80)
no_notation s_id ("1\<^sub>\<sigma>")
no_notation c_prod (infixl "\<parallel>" 80)
no_notation c_id ("1\<^sub>\<pi>")

text \<open>Now we start with formalising the multirelational model. First
  we define  sequential composition and paraellel composition of multirelations, their units and 
the universal multirelation as in Section 2 of the article.\<close>

definition s_prod :: "'a mrel \<Rightarrow> 'a mrel \<Rightarrow> 'a mrel" (infixl "\<cdot>" 70) where
  "R \<cdot> S = {(a,A). (\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>{f b |b. b \<in> B}))}"

definition s_id :: "'a mrel" ("1\<^sub>\<sigma>") where
  "1\<^sub>\<sigma> \<equiv> \<Union>a. {(a,{a})}"

definition p_prod :: "'a mrel \<Rightarrow> 'a mrel \<Rightarrow> 'a mrel"  (infixl "\<parallel>" 70) where
  "R \<parallel> S = {(a,A). (\<exists>B C. A = B \<union> C \<and> (a,B) \<in> R \<and> (a,C) \<in> S)}"
 
definition p_id :: "'a mrel" ("1\<^sub>\<pi>") where
  "1\<^sub>\<pi> \<equiv> \<Union>a. {(a,{})}"

definition U :: "'a mrel" where 
  "U \<equiv> {(a,A) |a A. a \<in> UNIV \<and> A \<subseteq> UNIV}"

abbreviation "NC \<equiv> U - 1\<^sub>\<pi>"

text \<open>We write NC where $\overline{1_\pi}$ is written in~\cite{FurusawaS15a}.\<close>

text \<open>Next we prove some basic set-theoretic properties.\<close>

lemma s_prod_im: "R \<cdot> S = {(a,A). (\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>((\<lambda>x. f x) ` B)))}"
  by (auto simp: s_prod_def)

lemma s_prod_iff: "(a,A) \<in> (R \<cdot> S) \<longleftrightarrow> (\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>((\<lambda>x. f x) ` B)))"
  by (unfold s_prod_im, auto)

lemma s_id_iff: "(a,A) \<in> 1\<^sub>\<sigma> \<longleftrightarrow> A = {a}"
  by (simp add: s_id_def)

lemma p_prod_iff: "(a,A) \<in> R \<parallel> S \<longleftrightarrow> (\<exists>B C. A = B \<union> C \<and> (a,B) \<in> R \<and> (a,C) \<in> S)"
  by (clarsimp simp add: p_prod_def)

named_theorems mr_simp
declare s_prod_im [mr_simp] p_prod_def [mr_simp] s_id_def [mr_simp] p_id_def [mr_simp] U_def [mr_simp]

subsection\<open>Multirelations and Proto-Dioids\<close>

text \<open>We can now show that multirelations form proto-trioids. 
This is Proposition 5.1, and it subsumes Proposition 4.1,\<close>

interpretation mrel_proto_trioid: proto_trioid "1\<^sub>\<sigma>" "(\<cdot>)" "1\<^sub>\<pi>" "(\<parallel>)" "(\<union>)" "(\<subseteq>)" "(\<subset>)" "{}"
proof 
  show "\<And>x. 1\<^sub>\<sigma> \<cdot> x = x"
    by (auto simp: mr_simp)
  show "\<And>x. x \<cdot> 1\<^sub>\<sigma> = x"
    by (auto simp add: mr_simp) (metis UN_singleton)
  show "\<And>x. 1\<^sub>\<pi> \<parallel> x = x"
    by (simp add: mr_simp)
  show "\<And>x y z. x \<parallel> y \<parallel> z = x \<parallel> (y \<parallel> z)"
    apply (rule antisym)
    apply (clarsimp simp: mr_simp Un_assoc, metis) 
    by (clarsimp simp: mr_simp, metis (no_types) Un_assoc)
  show "\<And>x y. x \<parallel> y = y \<parallel> x"
    by  (auto simp: mr_simp)
  show "\<And>x y. (x \<subseteq> y) = (x \<union> y = y)"
    by blast
  show "\<And>x y. (x \<subset> y) = (x \<subseteq> y \<and> x \<noteq> y)"
    by (simp add: psubset_eq)
  show "\<And>x y z. x \<union> y \<union> z = x \<union> (y \<union> z)"
    by (simp add: Un_assoc)
  show "\<And>x y. x \<union> y = y \<union> x"
    by blast
  show "\<And>x. x \<union> x = x"
    by auto
  show "\<And>x. {} \<union> x = x"
    by blast
  show "\<And>x y z. (x \<union> y) \<cdot> z = x \<cdot> z \<union> y \<cdot> z"
    by (auto simp: mr_simp)
  show "\<And>x y z. x \<cdot> y \<union> x \<cdot> z \<subseteq> x \<cdot> (y \<union> z)"
    by (auto simp: mr_simp)
  show "\<And>x. {} \<cdot> x = {}"
    by (auto simp: mr_simp)
  show "\<And>x y z. x \<parallel> (y \<union> z) = x \<parallel> y \<union> x \<parallel> z"
    by (auto simp: mr_simp)
  show "\<And>x. x \<parallel> {} = {}"
    by (simp add: mr_simp)
qed

subsection \<open>Simple Properties\<close>

text\<open>This covers all the identities in the display before Lemma 2.1  except the two following ones.\<close>

lemma s_prod_assoc1: "(R \<cdot> S ) \<cdot> T \<subseteq> R \<cdot> (S \<cdot> T)"
  by (clarsimp simp: mr_simp, metis)

lemma seq_conc_subdistr: "(R \<parallel> S) \<cdot> T \<subseteq> (R \<cdot> T) \<parallel> (S \<cdot> T)"
  by (clarsimp simp: mr_simp UnI1 UnI2, blast)

text \<open>Next we provide some counterexamples. These do not feature in~\cite{FurusawaS15a}.\<close>

lemma  "R \<cdot> {} = {}"
  nitpick 
  oops

lemma "R \<cdot> (S \<union> T) = R \<cdot> S \<union> R \<cdot> T"
  apply (auto simp: s_prod_im)
  nitpick
  oops

lemma "R \<cdot> (S \<cdot> T) \<subseteq> (R \<cdot> S) \<cdot> T"
  apply (auto simp: s_prod_im)
  nitpick
  oops

lemma "(R \<parallel> R) \<cdot> T = (R \<cdot> T) \<parallel> (R \<cdot> T)"
  quickcheck 
  oops

text \<open>Next we prove the distributivity and associativity laws for sequential subidentities 
mentioned before Lemma 2.1\<close>   

lemma subid_aux2: 
assumes "R \<subseteq> 1\<^sub>\<sigma>"and "(a,A) \<in> R"
shows "A = {a}"
  using assms by (auto simp: mr_simp)

lemma s_prod_test_aux1: 
assumes "S \<subseteq> 1\<^sub>\<sigma>"
and  "(a,A) \<in> R \<cdot> S"
shows "((a,A) \<in> R \<and> (\<forall>a \<in> A. (a,{a}) \<in> S))" 
  using assms apply (clarsimp simp: s_prod_im)
  by (metis assms(2) mrel_proto_trioid.s_prod_idr mrel_proto_trioid.s_prod_isol singletonD subid_aux2 subset_eq)

lemma s_prod_test_aux2: 
assumes "(a,A) \<in> R"
and "\<forall>a \<in> A. (a,{a}) \<in> S"
shows "(a,A) \<in> R \<cdot> S"
  using assms by (auto simp: mr_simp, fastforce)

lemma s_prod_test: 
assumes "P \<subseteq> 1\<^sub>\<sigma>"
shows "(a,A) \<in> R \<cdot> P \<longleftrightarrow> (a,A) \<in> R \<and> (\<forall>a \<in> A. (a,{a}) \<in> P)"
  by (meson assms s_prod_test_aux1 s_prod_test_aux2) 

lemma test_s_prod_aux1: 
assumes "P \<subseteq>  1\<^sub>\<sigma>" 
and "(a,A) \<in> P \<cdot> R"
shows "(a,{a}) \<in> P \<and> (a,A) \<in> R" 
  by (metis assms mrel_proto_trioid.s_prod_idl s_id_iff s_prod_iff subid_aux2)
  
lemma test_s_prod_aux2: 
assumes "(a,A) \<in> R" 
and "(a,{a}) \<in> P"
shows "(a,A) \<in> P \<cdot> R"
  using assms s_prod_iff by fastforce

lemma test_s_prod: 
assumes "P \<subseteq> 1\<^sub>\<sigma>"
shows "(a,A) \<in> P \<cdot> R \<longleftrightarrow> (a,{a}) \<in> P \<and> (a,A) \<in> R"
  by (meson assms test_s_prod_aux1 test_s_prod_aux2)

lemma test_assoc1: 
assumes "P \<subseteq> 1\<^sub>\<sigma>"
shows "(R \<cdot> P) \<cdot> S = R \<cdot> (P \<cdot> S)"
proof (rule antisym)
  show  "(R \<cdot> P) \<cdot> S \<subseteq> R \<cdot> (P \<cdot> S)"
    by (metis s_prod_assoc1)
next
  show "R \<cdot> (P \<cdot> S) \<subseteq> (R \<cdot> P) \<cdot> S" using assms
  proof clarify
    fix a A
    assume "(a,A) \<in> R \<cdot> (P \<cdot> S)"
    hence "\<exists>B.(a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> P \<cdot> S) \<and> A = \<Union>((\<lambda>x. f x) ` B))" 
      by (clarsimp simp: mr_simp)
    hence "\<exists>B.(a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,{b}) \<in> P \<and> (b,f b) \<in> S) \<and> A = \<Union>((\<lambda>x. f x) ` B))" 
      by (metis assms test_s_prod)
    hence "\<exists>B.(a,B) \<in> R \<and> (\<forall>b \<in> B. (b,{b}) \<in> P) \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>((\<lambda>x. f x) ` B))"  
      by auto
    hence "\<exists>B. (a,B) \<in> R \<cdot> P \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (metis assms s_prod_test)
    thus "(a,A) \<in> (R \<cdot> P) \<cdot> S"
      by (clarsimp simp: mr_simp)
  qed
qed

lemma test_assoc2: 
assumes "P \<subseteq> 1\<^sub>\<sigma>"
shows "(P \<cdot> R) \<cdot> S = P \<cdot> (R \<cdot> S)"
proof (rule antisym)
  show "(P \<cdot> R) \<cdot> S \<subseteq>  P \<cdot> (R \<cdot> S)"
    by (metis s_prod_assoc1)
  show "P \<cdot> (R \<cdot> S) \<subseteq> (P \<cdot> R) \<cdot> S" using assms
  proof clarify
    fix a A
    assume "(a,A) \<in> P \<cdot> (R \<cdot> S)"
    hence "(a,{a}) \<in> P \<and> (a,A) \<in> R \<cdot> S"
      by (metis assms test_s_prod)
    hence "(a,{a}) \<in> P \<and> (\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>((\<lambda>x. f x) ` B)))" 
      by (clarsimp simp: mr_simp)
    hence "\<exists>B.(a,{a}) \<in> P \<and> (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>((\<lambda>x. f x) ` B))" 
      by (clarsimp simp: mr_simp)
    hence "\<exists>B. (a,B) \<in> P \<cdot> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (metis assms test_s_prod)
    thus "(a,A) \<in> (P \<cdot> R) \<cdot> S"
      by (clarsimp simp: mr_simp)
  qed
qed

lemma test_assoc3: 
assumes "P \<subseteq> 1\<^sub>\<sigma>"
shows "(R \<cdot> S) \<cdot> P = R \<cdot> (S \<cdot> P)"
proof (rule antisym)
  show "(R \<cdot> S) \<cdot> P \<subseteq> R \<cdot> (S \<cdot> P)"
    by (metis s_prod_assoc1)
  show "R \<cdot> (S \<cdot> P) \<subseteq> (R \<cdot> S) \<cdot> P" using assms
    proof clarify
    fix a A
    assume hyp1: "(a, A) \<in> R \<cdot> (S \<cdot> P)"
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b\<in>B. (b,f b) \<in> S \<cdot> P) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (simp add: s_prod_test s_prod_im)
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b\<in>B. (b,f b) \<in> S \<and> (\<forall>a\<in>f b. (a,{a}) \<in> P)) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (simp add: s_prod_test assms)
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b\<in>B. (b,f b) \<in> S) \<and> (\<forall>a\<in>\<Union>((\<lambda>x. f x) ` B). (a,{a}) \<in> P) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by auto
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b\<in>B. (b,f b) \<in> S) \<and> (\<forall>a\<in>A. (a,{a}) \<in> P) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by auto blast
    hence "(a,A) \<in> R \<cdot> S \<and> (\<forall>a\<in>A. (a,{a}) \<in> P)"
      by (auto simp: mr_simp)
    thus "(a,A) \<in> (R \<cdot> S) \<cdot> P"
      by (simp add: s_prod_test assms)
  qed
qed

lemma s_distl_test: 
assumes "R \<subseteq> 1\<^sub>\<sigma>"
shows "R \<cdot> (S \<union> T) = R \<cdot> S \<union> R \<cdot> T" 
  apply (clarsimp simp: mr_simp) using assms subid_aux2 by fastforce 

text \<open>Next we verify Lemma 2.1.\<close>

lemma subid_par_idem: 
assumes "R \<subseteq> 1\<^sub>\<sigma>"
shows "R \<parallel> R = R"
  by (rule set_eqI, clarsimp simp: mr_simp, metis Un_absorb assms subid_aux2) 

lemma term_par_idem: 
assumes "R \<subseteq> 1\<^sub>\<pi>" 
shows "R \<parallel> R = R"
  using assms by (auto simp: mr_simp)

lemma U_par_idem: "U \<parallel> U = U"
  by (auto simp: mr_simp)

lemma nc_par_idem: "NC \<parallel> NC = NC"
  by (auto simp: mr_simp)

text \<open>Next we prove the properties of Lemma 2.2 and 3.2. First we prepare to show that multirelations form c-lattices.\<close>

text \<open>We define the domain operation on multirelations and verify the explicit definition from Section 3.\<close>

definition d :: "'a mrel \<Rightarrow> 'a mrel" where
  "d R \<equiv> {(a,{a}) |a. \<exists>B. (a,B) \<in> R}"

named_theorems mrd_simp
declare mr_simp [mrd_simp] d_def [mrd_simp]

lemma d_def_expl: "d R = (R \<cdot> 1\<^sub>\<pi>) \<parallel> 1\<^sub>\<sigma>"
  apply (simp add: mrd_simp) using set_eqI by force

interpretation mrel_pbdl_monoid: pbdl_monoid "1\<^sub>\<sigma>" "(\<cdot>)" "1\<^sub>\<pi>" "(\<parallel>)" "(\<union>)" "(\<subseteq>)" "(\<subset>)" "{}" "U" "(\<inter>)"
  by (unfold_locales, auto simp: mrd_simp)

text \<open>Here come the properties of Lemma 2.2.\<close>

lemma c1: "(R \<cdot> 1\<^sub>\<pi>) \<parallel> R = R"
  apply (rule set_eqI) 
  apply (clarsimp simp: mr_simp)
  by (metis (no_types, lifting) SUP_bot SUP_bot_conv(2) sup_bot.left_neutral) 

lemma t_aux: "T \<parallel> T \<subseteq> T \<Longrightarrow> (\<forall>a B C. (a,B) \<in> T \<and> (a,C) \<in> T \<Longrightarrow> (a,B \<union> C) \<in> T)"
  by (clarsimp simp: mr_simp)

lemma cl4:
assumes "T \<parallel> T \<subseteq> T"
shows "(R \<cdot> T) \<parallel> (S \<cdot> T) \<subseteq> (R \<parallel> S) \<cdot> T" 
proof clarify
fix a A   
  assume  "(a,A) \<in> (R \<cdot> T) \<parallel> (S \<cdot> T)"
  hence "\<exists>B C. A = B \<union> C \<and> (\<exists>D. (a,D) \<in> R \<and> (\<exists>f. (\<forall>d \<in> D. (d,f d) \<in> T) \<and> B = \<Union> ((\<lambda>x. f x) ` D))) \<and> (\<exists>E. (a,E) \<in> S \<and> (\<exists>g. (\<forall>e \<in> E. (e,g e) \<in> T) \<and> C = \<Union> ((\<lambda>x. g x)` E)))"
    by (simp add: mr_simp)
  hence "\<exists>D E. (a,D \<union> E) \<in> R \<parallel> S \<and> (\<exists>f g. (\<forall>d \<in> D. (d,f d) \<in> T) \<and> (\<forall>e \<in> E. (e,g e) \<in> T) \<and> A = (\<Union> ((\<lambda>x. f x) ` D)) \<union> (\<Union> ((\<lambda>x. g x)` E)))"
    by (auto simp: mr_simp)
  hence "\<exists>D E. (a,D \<union> E) \<in> R \<parallel> S \<and> (\<exists>f g. (\<forall>d \<in> D-E. (d,f d) \<in> T) \<and> (\<forall>e \<in> E-D. (e,g e) \<in> T) \<and> (\<forall>x \<in> D \<inter> E. (x,f x) \<in> T \<and> (x,g x) \<in> T) \<and> A = (\<Union> ((\<lambda>x. f x) ` (D-E))) \<union> (\<Union> ((\<lambda>x. g x) ` (E-D)) \<union> (\<Union> ((\<lambda>y. f y \<union> g y) ` (D \<inter> E)))))"
    by auto blast
  hence "\<exists>D E. (a,D \<union> E) \<in> R \<parallel> S \<and> (\<exists>f g. (\<forall>d \<in> D-E. (d,f d) \<in> T) \<and> (\<forall>e \<in> E-D. (e,g e) \<in> T) \<and> (\<forall>x \<in> D \<inter> E. (x,f x \<union> g x) \<in> T) \<and> A = (\<Union> ((\<lambda>x. f x) ` (D-E))) \<union> (\<Union> ((\<lambda>x. g x) ` (E-D)) \<union> (\<Union> ((\<lambda>y. f y \<union> g y) ` (D \<inter> E)))))"
    apply clarify
    apply (rule_tac x = D in exI)
    apply (rule_tac x = E in exI)
    apply clarify
    apply (rule_tac x = f in exI)
    apply (rule_tac x = g in exI)
    using assms by (auto simp: p_prod_def p_prod_iff, blast)
  hence "\<exists>D E. (a,D \<union> E) \<in> R \<parallel> S \<and> (\<exists>h. (\<forall>d \<in> D-E. (d,h d) \<in> T) \<and> (\<forall>e \<in> E-D. (e, h e) \<in> T) \<and> (\<forall>x \<in> D \<inter> E. (x, h x) \<in> T) \<and> A = (\<Union> ((\<lambda>x. h x) ` (D-E))) \<union> (\<Union> ((\<lambda>x. h x) ` (E-D)) \<union> (\<Union> ((\<lambda>y. h y) ` (D \<inter> E)))))"
    apply clarify
    apply (rule_tac x = D in exI)
    apply (rule_tac x = E in exI)
    apply clarify
    apply (rule_tac x = "\<lambda>x. if x \<in> (D - E) then f x else (if x \<in> D \<inter> E then (f x \<union> g x) else g x)" in exI)
    by auto
  hence " (\<exists>B. (a,B) \<in> R \<parallel> S \<and> (\<exists>h. (\<forall>b\<in>B. (b,h b) \<in> T) \<and> A = \<Union>((\<lambda>x. h x) ` B)))"
    by auto blast
  thus "(a,A) \<in> (R \<parallel> S) \<cdot> T"
    by (simp add: mr_simp)
qed

lemma cl3: "R \<cdot> (S \<parallel> T) \<subseteq> (R \<cdot> S) \<parallel> (R \<cdot> T)"
proof clarify
fix a A
assume "(a,A) \<in> R \<cdot> (S \<parallel> T)"
  hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. \<exists>C D. f b = C \<union> D \<and> (b,C) \<in> S \<and> (b,D) \<in> T) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
    by (clarsimp simp: mr_simp)
  hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f g h. (\<forall>b \<in> B. f b = g b \<union> h b \<and> (b,g b) \<in> S \<and> (b,h b) \<in> T) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
    by (clarsimp simp: bchoice, metis)
  hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>g h. (\<forall>b \<in> B. (b,g b) \<in> S \<and> (b,h b) \<in> T) \<and> A = (\<Union> ((\<lambda>x. g x) ` B)) \<union> (\<Union> ((\<lambda>x. h x) ` B)))"
    by  blast
  hence "\<exists>C D. (\<exists>B. (a,B) \<in> R \<and> (\<exists>g. (\<forall>b \<in> B. (b,g b) \<in> S) \<and>  C = \<Union> ((\<lambda>x. g x) ` B))) \<and> (\<exists>B. (a,B) \<in> R \<and> (\<exists>h. (\<forall>b \<in> B. (b,h b) \<in> T) \<and>  D = \<Union> ((\<lambda>x. h x)` B))) \<and> A = C \<union> D"
    by blast
  thus "(a,A) \<in> (R \<cdot> S) \<parallel> (R \<cdot> T)"
    by (auto simp: mr_simp)
qed

lemma cl5: "(R \<cdot> S) \<cdot> (T \<cdot> {}) = R \<cdot> (S \<cdot> (T \<cdot> {}))"
  proof (rule antisym)
  show "(R \<cdot> S) \<cdot> (T \<cdot> {}) \<subseteq> R \<cdot> (S \<cdot> (T \<cdot> {}))"
    by (metis s_prod_assoc1)
  show " R \<cdot> (S \<cdot> (T \<cdot> {})) \<subseteq> (R \<cdot> S) \<cdot> (T \<cdot> {})"
  proof clarify
  fix a A
  assume "(a,A) \<in>  R \<cdot> (S \<cdot> (T \<cdot> {}))"
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (\<exists> C. (b,C) \<in> S \<and> (\<exists>g. (\<forall>x \<in> C. (x,g x) \<in> T \<cdot> {}) \<and> f b = \<Union>((\<lambda>x. g x) ` C)))) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (clarsimp simp: mr_simp)
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (\<exists> C. (b,C) \<in> S \<and> (\<forall>x \<in> C. (x,{}) \<in> T \<cdot> {}) \<and> f b = {})) \<and> A = \<Union>((\<lambda>x. f x) ` B))"
      by (clarsimp simp: mr_simp) fastforce
    hence "\<exists>B. (a,B) \<in> R \<and> (\<forall>b \<in> B. (\<exists> C. (b,C) \<in> S \<and> (\<forall>x \<in> C. (x,{}) \<in> T \<cdot> {}))) \<and> A = {}"
      by (metis (erased, hide_lams) SUP_bot_conv(2))
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S \<and> (\<forall>x \<in> f b. (x,{}) \<in> T \<cdot> {}))) \<and> A = {}" 
      by metis
    hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> (\<forall>x \<in> \<Union>((\<lambda>x. f x) ` B). (x,{}) \<in> T \<cdot> {})) \<and> A = {}"
      by (metis UN_E) 
    hence "\<exists>C B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b, f b) \<in> S) \<and> C =  \<Union>((\<lambda>x. f x) ` B) \<and> (\<forall>x \<in> C. (x,{}) \<in> T \<cdot> {})) \<and> A = {}"
      by metis
    hence "\<exists>C. (a,C) \<in> R \<cdot> S \<and> (\<forall>x \<in> C. (x,{}) \<in> T \<cdot> {}) \<and> A = {}"
      by (auto simp: mr_simp)
    thus "(a,A) \<in> (R \<cdot> S) \<cdot> (T \<cdot> {})"
      by (clarsimp simp: mr_simp) blast
  qed
qed

text \<open>We continue verifying other c-lattice axioms\<close>

lemma cl8_var: "d R \<cdot> S = (R \<cdot> 1\<^sub>\<pi>) \<parallel> S"
  apply (rule set_eqI)
  apply (clarsimp simp: mrd_simp)
  apply standard
  apply (metis SUP_bot sup.commute sup_bot.right_neutral)
  by auto

lemma cl9_var: "d (R \<inter> 1\<^sub>\<sigma>) = R \<inter> 1\<^sub>\<sigma>"
  by (auto simp: mrd_simp)

lemma cl10_var: "d (R - 1\<^sub>\<pi>) = 1\<^sub>\<sigma> \<inter> ((R - 1\<^sub>\<pi>) \<cdot> NC)"
  apply (rule set_eqI)
  apply (clarsimp simp: d_def p_id_def s_id_def U_def s_prod_im)
  by (metis UN_constant insert_not_empty)

subsection \<open>Multirelations and C-Lattices\<close>

text \<open>Next we show that multirelations form c-lattices (Proposition 7.3) and prove further facts in this setting.\<close>

interpretation mrel_c_lattice: c_lattice "1\<^sub>\<sigma>" "(\<cdot>)" "1\<^sub>\<pi>" "(\<parallel>)" "(\<union>)" "(\<subseteq>)" "(\<subset>)" "{}" "U" "(\<inter>)" "NC"
proof
  fix x y z :: "('b \<times> 'b set) set"
  show "x \<cdot> 1\<^sub>\<pi> \<union> x \<cdot> NC = x \<cdot> U"
    apply (rule set_eqI) 
    apply (clarsimp simp:  mr_simp)
    using UN_constant all_not_in_conv by metis
  show "1\<^sub>\<pi> \<inter> (x \<union> NC) = x \<cdot> {}"
    by (auto simp: mr_simp)
  show "x \<cdot> (y \<parallel> z) \<subseteq> x \<cdot> y \<parallel> (x \<cdot> z)"
    by (rule cl3)
  show "z \<parallel> z \<subseteq> z \<Longrightarrow> x \<parallel> y \<cdot> z = x \<cdot> z \<parallel> (y \<cdot> z)"
    by (metis cl4 seq_conc_subdistr subset_antisym)
  show "x \<cdot> (y \<cdot> (z \<cdot> {})) = x \<cdot> y \<cdot> (z \<cdot> {})"
    by (metis cl5)
  show "x \<cdot> {} \<cdot> z = x \<cdot> {}"
    by (clarsimp simp: mr_simp)
  show "1\<^sub>\<sigma> \<parallel> 1\<^sub>\<sigma> = 1\<^sub>\<sigma>"
    by (auto simp: mr_simp)
  show "x \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> \<cdot> y = x \<cdot> 1\<^sub>\<pi> \<parallel> y"
    by (metis cl8_var d_def_expl)
  show "x \<inter> 1\<^sub>\<sigma> \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> = x \<inter> 1\<^sub>\<sigma>"
    by (auto simp: mr_simp)
  show "x \<inter> NC \<cdot> 1\<^sub>\<pi> \<parallel> 1\<^sub>\<sigma> = 1\<^sub>\<sigma> \<inter> (x \<inter> NC \<cdot> NC)"
    by (metis Int_Diff cl10_var d_def_expl)
  show "x \<inter> NC \<cdot> 1\<^sub>\<pi> \<parallel> NC = x \<inter> NC \<cdot> NC"
    apply (rule set_eqI)
    apply (clarsimp simp: d_def U_def p_id_def p_prod_def s_prod_im)
    apply standard
    apply (metis (no_types, lifting) UN_extend_simps(2) Un_empty)
  proof -
    fix a :: 'b and b :: "'b set"
    assume a1: "\<exists>B. (a, B) \<in> x \<and> B \<noteq> {} \<and> (\<exists>f. (\<forall>b\<in>B. f b \<noteq> {}) \<and> b = (\<Union>x\<in>B. f x))"
    { fix bb :: "'b set \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b set) \<Rightarrow> 'b"
      obtain BB :: "'b set" and BBa :: "'b \<Rightarrow> 'b set" where
        ff1: "(a, BB) \<in> x \<and> {} \<noteq> BB \<and> (\<forall>b. b \<notin> BB \<or> {} \<noteq> BBa b) \<and> \<Union>(BBa ` BB) = b"
        by (metis (full_types) a1)
      hence "\<forall>B. (\<Union>b\<in>BB. (B::'b set)) = B"
        by force
      hence "\<exists>B Ba. B \<union> Ba = b \<and> (\<exists>Bb. (a, Bb) \<in> x \<and> {} \<noteq> Bb \<and> (\<exists>f. (bb B Ba Bb f \<notin> Bb \<or> {} = f (bb B Ba Bb f)) \<and> \<Union>(f ` Bb) = B)) \<and> {} \<noteq> Ba"
        by (metis ff1 SUP_bot_conv(2) sup_bot.left_neutral) }
    thus "\<exists>B Ba. b = B \<union> Ba \<and> (\<exists>Ba. (a, Ba) \<in> x \<and> Ba \<noteq> {} \<and> (\<exists>f. (\<forall>b\<in>Ba. f b = {}) \<and> B = (\<Union>b\<in>Ba. f b))) \<and> Ba \<noteq> {}"
      by metis
  qed
qed

text \<open>The following facts from Lemma 2.2 remain to be shown.\<close>

lemma p_id_assoc1: "(1\<^sub>\<pi> \<cdot> R) \<cdot> S = 1\<^sub>\<pi> \<cdot> (R \<cdot> S)"
  by (clarsimp simp: mr_simp)

lemma p_id_assoc2: "(R \<cdot> 1\<^sub>\<pi>) \<cdot> T = R \<cdot> (1\<^sub>\<pi> \<cdot> T)"
  by (auto simp add: mr_simp cong del: SUP_cong_simp, blast+)

lemma seq_conc_subdistrl: 
assumes "P \<subseteq> 1\<^sub>\<sigma>"
shows "P \<cdot> (S \<parallel> T) = (P \<cdot> S) \<parallel> (P \<cdot> T)"
  by (metis assms mrel_c_lattice.d_inter_r mrel_c_lattice.d_s_subid)

lemma test_s_prod_is_meet [simp]: 
assumes "R \<subseteq> 1\<^sub>\<sigma>" 
and "S \<subseteq> 1\<^sub>\<sigma>"
shows "R \<cdot> S = R \<inter> S"
  using assms by (auto simp: mr_simp, force+)

lemma test_p_prod_is_meet: 
assumes "R \<subseteq> 1\<^sub>\<sigma>"
and "S \<subseteq> 1\<^sub>\<sigma>"
shows "R \<parallel> S = R \<inter> S"
  apply standard
  using assms
  apply (auto simp: mr_simp, force+)
  done

lemma test_multipliciativer:
assumes "R \<subseteq> 1\<^sub>\<sigma>"
and "S \<subseteq> 1\<^sub>\<sigma>"
shows "(R \<inter> S) \<cdot> T = (R \<cdot> T) \<inter> (S \<cdot> T)"
  using assms by (clarsimp simp: set_eqI mr_simp subid_aux2, force)

text \<open>Next we verify the remaining fact from Lemma 2.2; in fact it follows from the corresponding theorem of c-lattices.\<close>

lemma c6: "R \<cdot> 1\<^sub>\<pi> \<subseteq> 1\<^sub>\<pi>"
 by (clarsimp simp: mr_simp)

text \<open>Next we verify Lemma 3.1.\<close>

lemma p_id_st: "R \<cdot> 1\<^sub>\<pi> = {(a,{}) |a.  \<exists>B. (a,B) \<in> R}"
  by (auto simp: mr_simp)
 
lemma p_id_zero: "R \<inter> 1\<^sub>\<pi> = R \<cdot> {}"
  by (auto simp: mr_simp)

lemma p_id_zero_st: "R \<inter> 1\<^sub>\<pi> = {(a,{}) |a. (a,{}) \<in> R}"
  by (auto simp: mr_simp)

lemma s_id_st: "R \<inter> 1\<^sub>\<sigma> = {(a,{a}) |a. (a,{a}) \<in> R}"
  by (auto simp: mr_simp)

lemma U_seq_st: "(a,A) \<in> R \<cdot> U \<longleftrightarrow> (A = {} \<and> (a,{}) \<in> R) \<or> (\<exists>B. B \<noteq> {} \<and> (a,B) \<in> R)"
  by (clarsimp simp: s_prod_im U_def, metis SUP_constant SUP_empty) 

lemma U_par_st: "(a,A) \<in> R \<parallel> U \<longleftrightarrow> (\<exists>B. B \<subseteq> A \<and> (a,B) \<in> R)"
  by (auto simp: mr_simp)

text \<open>Next we verify the relationships after Lemma 3.1.\<close>

lemma s_subid_iff1: "R \<subseteq> 1\<^sub>\<sigma> \<longleftrightarrow> R \<inter> 1\<^sub>\<sigma> = R"
  by blast

lemma s_subid_iff2: "R \<subseteq> 1\<^sub>\<sigma> \<longleftrightarrow> d R = R"
  by (auto simp: mrd_simp)

lemma p_subid_iff: "R \<subseteq> 1\<^sub>\<pi> \<longleftrightarrow> R \<cdot> 1\<^sub>\<pi> = R"
  by (simp add: mrel_c_lattice.term_p_subid)

lemma vec_iff1: 
assumes "\<forall>a. (\<exists>A. (a,A) \<in> R) \<longrightarrow> (\<forall>A. (a,A) \<in> R)"
shows "(R \<cdot> 1\<^sub>\<pi>) \<parallel> U = R"
  using assms by (auto simp: mr_simp)

lemma vec_iff2: 
assumes "(R \<cdot> 1\<^sub>\<pi>) \<parallel> U = R"
shows "(\<forall>a. (\<exists>A. (a,A) \<in> R) \<longrightarrow> (\<forall>A. (a,A) \<in> R))"
  using assms apply (clarsimp simp: mr_simp)
  proof -
    fix a :: 'a and A :: "'a set" and Aa :: "'a set"
    assume a1: "(a, A) \<in> R"
    obtain AA :: "('a \<times> 'a set) set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
    "\<forall>x0 x1 x2. (\<exists>v3\<subseteq>x1. (x2, v3) \<in> x0) = (AA x0 x1 x2 \<subseteq> x1 \<and> (x2, AA x0 x1 x2) \<in> x0)"
      by moura
    hence f2: "AA (R \<cdot> 1\<^sub>\<pi>) A a \<subseteq> A \<and> (a, AA (R \<cdot> 1\<^sub>\<pi>) A a) \<in> R \<cdot> 1\<^sub>\<pi>"
      by (metis a1 U_par_st assms)
    hence "\<exists>aa. (a, AA (R \<cdot> 1\<^sub>\<pi>) A a) = (aa, {}) \<and> (\<exists>A. (aa, A) \<in> R)"
      by (simp add: p_id_st)
    hence "AA (R \<cdot> 1\<^sub>\<pi>) A a \<subseteq> Aa"
      by blast
   thus "(a, Aa) \<in> R"
      using f2 by (metis (no_types) U_par_st assms)
qed

lemma vec_iff: "(\<forall>a. (\<exists>A. (a,A) \<in> R) \<longrightarrow> (\<forall>A. (a,A) \<in> R)) \<longleftrightarrow> (R \<cdot> 1\<^sub>\<pi>) \<parallel> U = R"
  by (metis vec_iff1 vec_iff2)

lemma ucl_iff: "(\<forall>a A B. (a,A) \<in> R \<and> A \<subseteq> B \<longrightarrow> (a,B) \<in> R) \<longleftrightarrow> R \<parallel> U = R" 
  by (clarsimp simp: mr_simp, blast)

lemma nt_iff: "R \<subseteq> NC \<longleftrightarrow> R \<inter> NC = R"
  by blast

text\<open>Next we provide a counterexample for the final paragraph of Section 3.\<close>

lemma "1\<^sub>\<sigma> \<inter> R \<cdot> U = R"
  nitpick
  oops

text\<open>Next we present a counterexample for vectors mentioned before Lemma 9.3.\<close>

lemma "d (d R \<cdot> U) \<cdot> (d S \<cdot> U) \<cdot> U = (d R \<cdot> U) \<cdot> (d S \<cdot> U)"
  nitpick
  oops

text\<open>Next we prove Tarski' rule (Lemma 9.3).\<close>

lemma tarski_aux: 
assumes "R - 1\<^sub>\<pi> \<noteq> {}"
and "(a,A) \<in>  NC"
shows "(a,A) \<in> NC \<cdot> ((R - 1\<^sub>\<pi>) \<cdot> NC)"
proof -
  have "(\<exists>B. B \<noteq> {} \<and> (\<forall>x \<in> B. (x,{x}) \<in> d (R - 1\<^sub>\<pi>)))" 
    using assms(1) by (auto simp: mrd_simp)
  hence "(\<exists>B. B \<noteq> {} \<and> (\<forall>x \<in> B. (x,{x}) \<in> d (R - 1\<^sub>\<pi>))) \<and> A \<noteq> {}" 
    using assms(2) by (clarsimp simp: mr_simp)
  hence "(\<exists>B. B \<noteq> {} \<and> (\<exists>f. (\<forall>x \<in> B. (x,{x}) \<in> d (R - 1\<^sub>\<pi>) \<and> f x \<noteq> {}) \<and> A = \<Union> ((\<lambda>x. (f x)) ` B)))"
    by (metis UN_constant)
  hence "(a,A) \<in> NC \<cdot> (d (R - 1\<^sub>\<pi>) \<cdot> NC)"
    by (clarsimp simp: mrd_simp) metis
  thus ?thesis
   by (clarsimp simp: mrd_simp, metis UN_constant)
qed

lemma tarski: 
assumes "R - 1\<^sub>\<pi> \<noteq> {}"
shows "NC \<cdot> ((R - 1\<^sub>\<pi>) \<cdot> NC) = NC"
  by standard (simp add: U_def p_id_def s_prod_im, force, metis assms tarski_aux subrelI)

text \<open>Next we verify the assumptions of Proposition 9.8.\<close>

lemma d_assoc1: "d R \<cdot> (S \<cdot> T) = (d R \<cdot> S) \<cdot> T"
  by (metis d_def_expl mrel_c_lattice.d_def mrel_c_lattice.d_sub_id_ax test_assoc2)

lemma d_meet_distr_var: "(d R \<inter> d S) \<cdot> T = (d R \<cdot> T) \<inter> (d S \<cdot> T)"
  by (auto simp: mrd_simp)

text \<open>Lemma 10.5.\<close>

lemma "((R \<inter> 1\<^sub>\<sigma>) \<cdot> (S \<inter> 1\<^sub>\<sigma>)) \<cdot> 1\<^sub>\<pi> = ((R \<inter> 1\<^sub>\<sigma>) \<cdot> 1\<^sub>\<pi>) \<cdot> ((S \<inter> 1\<^sub>\<sigma>) \<cdot> 1\<^sub>\<pi>)" 
  nitpick
  oops

lemma "d ((R \<cdot> 1\<^sub>\<pi>) \<cdot> (S \<cdot> 1\<^sub>\<pi>)) = d (R \<cdot> 1\<^sub>\<pi>) \<cdot> d (S \<cdot> 1\<^sub>\<pi>)"
  nitpick
  oops

lemma "((R \<inter> 1\<^sub>\<sigma>) \<cdot> (S \<inter> 1\<^sub>\<sigma>)) \<cdot> U = ((R \<inter> 1\<^sub>\<sigma>) \<cdot> U) \<cdot> ((S \<inter> 1\<^sub>\<sigma>) \<cdot> U)" 
  nitpick
  oops

lemma "d (((R \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> ((S \<cdot> 1\<^sub>\<pi>) \<parallel> U)) = d ((R \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> d ((S \<cdot> 1\<^sub>\<pi>) \<parallel> U)"
  nitpick
  oops

lemma "((R \<cdot> 1\<^sub>\<pi>) \<cdot> (S \<cdot> 1\<^sub>\<pi>)) \<parallel> U = ((R \<cdot> 1\<^sub>\<pi>) \<parallel> U) \<cdot> ((S \<cdot> 1\<^sub>\<pi>) \<parallel> U)"
  nitpick
  oops

lemma "(((R - 1\<^sub>\<pi>) \<inter> 1\<^sub>\<sigma>) \<cdot> ((S - 1\<^sub>\<pi>) \<inter> 1\<^sub>\<sigma>)) \<cdot> 1\<^sub>\<pi> = (((R - 1\<^sub>\<pi>) \<inter> 1\<^sub>\<sigma>) \<cdot> 1\<^sub>\<pi>) \<cdot> (((S - 1\<^sub>\<pi>) \<inter> 1\<^sub>\<sigma>) \<cdot> 1\<^sub>\<pi>)" 
  nitpick
  oops

lemma "d (((R - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<cdot> ((S - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>)) = d ((R - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<cdot> d ((S - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>)"
  nitpick
  oops

lemma "(((R - 1\<^sub>\<pi>) \<inter> 1\<^sub>\<sigma>) \<cdot> ((S - 1\<^sub>\<pi>) \<inter> 1\<^sub>\<sigma>)) \<cdot> NC = (((R - 1\<^sub>\<pi>) \<inter> 1\<^sub>\<sigma>) \<cdot> NC) \<cdot> (((S - 1\<^sub>\<pi>) \<inter> 1\<^sub>\<sigma>) \<cdot> NC)" 
  apply (auto simp: U_def p_id_def s_id_def s_prod_im)
  defer
  nitpick
  oops

lemma "d ((((R - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC) \<cdot> (((S - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC)) = d (((R - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC) \<cdot> d (((S - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC)"
  apply (simp add: U_def p_id_def s_prod_im p_prod_def d_def)
  nitpick
  oops

lemma "(((R - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<cdot> ((S - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>)) \<parallel> NC = (((R - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC) \<cdot> (((S - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC)"
  nitpick
  oops

lemma "((((R - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC) \<cdot> (((S - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC)) \<cdot> 1\<^sub>\<pi>  = ((((R - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC) \<cdot> 1\<^sub>\<pi>) \<cdot> ((((S - 1\<^sub>\<pi>) \<cdot> 1\<^sub>\<pi>) \<parallel> NC) \<cdot> 1\<^sub>\<pi>)"
  nitpick
  oops

subsection \<open>Terminal and Nonterminal Elements\<close>

text \<open>Lemma 11.4\<close>

lemma "(R \<cdot> S) \<cdot> {} = (R \<cdot> {}) \<cdot> (S \<cdot> {})"
  nitpick
  oops

lemma "(R \<cdot> S) - 1\<^sub>\<pi> = (R - 1\<^sub>\<pi>) \<cdot> (S - 1\<^sub>\<pi>)"
  apply (auto simp: s_prod_im p_id_def)
  nitpick
  oops

lemma "(R \<parallel> S) - 1\<^sub>\<pi> = (R - 1\<^sub>\<pi>) \<parallel> (S - 1\<^sub>\<pi>)"
  nitpick
  oops

text \<open>Lemma 11.8.\<close>

lemma "((R \<cdot> 1\<^sub>\<pi>) \<cdot> (S - 1\<^sub>\<pi>)) - 1\<^sub>\<pi> = (R \<cdot> 1\<^sub>\<pi>) \<cdot> (S - 1\<^sub>\<pi>)"
  nitpick 
  oops

lemma "((S - 1\<^sub>\<pi>) \<cdot> (R \<cdot> 1\<^sub>\<pi>)) - 1\<^sub>\<pi> = (S - 1\<^sub>\<pi>) \<cdot> (R \<cdot> 1\<^sub>\<pi>)"
  nitpick 
  oops

lemma "((R \<cdot> 1\<^sub>\<pi>) \<parallel> (S - 1\<^sub>\<pi>)) \<cdot> 1\<^sub>\<pi> = (R \<cdot> 1\<^sub>\<pi>) \<parallel> (S - 1\<^sub>\<pi>)"
  nitpick
  oops

text \<open>Lemma 11.10.\<close>

lemma "R \<cdot> {} \<subseteq> S \<cdot> {} \<Longrightarrow> (R \<cdot> T) \<cdot> {} \<subseteq> (S \<cdot> T) \<cdot> {}"
  nitpick
  oops

lemma "R - 1\<^sub>\<pi> \<subseteq> S - 1\<^sub>\<pi> \<Longrightarrow> (R \<parallel> T) - 1\<^sub>\<pi> \<subseteq> (S \<parallel> T) - 1\<^sub>\<pi>"
  nitpick
  oops

lemma "R - 1\<^sub>\<pi> \<subseteq> S - 1\<^sub>\<pi> \<Longrightarrow> (T \<cdot> R) - 1\<^sub>\<pi> \<subseteq> (T \<cdot> S) - 1\<^sub>\<pi>"
  apply (auto simp: p_id_def s_prod_im)
  nitpick
  oops

text \<open>Corollary 11.12\<close>

lemma "R \<cdot> {} = S \<cdot> {} \<Longrightarrow> (R \<cdot> T) \<cdot> {} = (S \<cdot> T) \<cdot> {}"
  nitpick
  oops

lemma "R - 1\<^sub>\<pi> = S - 1\<^sub>\<pi> \<Longrightarrow> (R \<parallel> T) - 1\<^sub>\<pi> = (S \<parallel> T) - 1\<^sub>\<pi>"
  nitpick
  oops

lemma "R - 1\<^sub>\<pi> = S - 1\<^sub>\<pi> \<Longrightarrow> (T \<cdot> R) - 1\<^sub>\<pi> = (T \<cdot> S) - 1\<^sub>\<pi>"
  apply (auto simp: p_id_def s_prod_im)
  nitpick
  oops

subsection \<open>Multirelations, Proto-Quantales and Iteration\<close>

interpretation mrel_proto_quantale: proto_quantale "1\<^sub>\<sigma>" "(\<cdot>)" Inter Union "(\<inter>)" "(\<subseteq>)" "(\<subset>)" "(\<union>)" "{}" "U"
  by (unfold_locales, auto simp: mr_simp)

text \<open>We reprove Corollary 13.2. because Isabelle does not pick it up from the quantale level.\<close>

lemma iso_prop: "mono (\<lambda>X. S \<union> R \<cdot> X)"
  by (rule monoI, (clarsimp simp: mr_simp), blast)

lemma gfp_lfp_prop: "gfp (\<lambda>X. R \<cdot> X) \<union> lfp (\<lambda>X. S \<union> R \<cdot> X) \<subseteq> gfp (\<lambda>X. S \<union> R \<cdot> X)"
  by (simp add: lfp_le_gfp gfp_mono iso_prop)

subsection \<open>Further Counterexamples\<close>

text \<open>Lemma 14,1. and 14.2\<close> 

lemma  "R \<parallel> R \<subseteq> R" 
   nitpick
   oops 

lemma "R \<subseteq> R \<parallel> S"
   nitpick
   oops

lemma "R \<parallel> S \<inter> R \<parallel> T \<subseteq> R \<parallel> (S \<inter> T)"
  nitpick
  oops

lemma "R \<cdot> (S \<parallel> T) = (R \<cdot> S) \<parallel> (R \<cdot> T)"
  nitpick
  oops

lemma "R \<cdot> (S \<cdot> T) \<subseteq> (R \<cdot> S) \<cdot> T"
  apply (auto simp: s_prod_im)
  nitpick
  oops

lemma "\<lbrakk>R \<parallel> R = R; S \<parallel> S = S; T \<parallel> T = T\<rbrakk> \<Longrightarrow> R \<cdot> (S \<parallel> T) = (R \<cdot> S) \<parallel> (R \<cdot> T)"
  nitpick
  oops

lemma "\<lbrakk>R \<noteq> {}; S \<noteq> {}; \<forall>a. (a,{}) \<notin> R \<union> S\<rbrakk> \<Longrightarrow> R \<cdot> S \<subseteq> R \<parallel> S"
  quickcheck
  oops

lemma "\<lbrakk>R \<noteq> {}; S \<noteq> {}; \<forall>a. (a,{}) \<notin> R \<union> S\<rbrakk> \<Longrightarrow> R \<parallel> S \<subseteq> R \<cdot> S"
  quickcheck
  oops

lemma "\<lbrakk>R \<noteq> {}; S \<noteq> {}; T \<noteq> {}; \<forall>a. (a,{}) \<notin> R \<union> S \<union> T\<rbrakk> \<Longrightarrow> (R \<parallel> S) \<cdot> T \<subseteq> R \<parallel> (S \<cdot> T)"
  quickcheck
  oops

lemma "\<lbrakk>R \<noteq> {}; S \<noteq> {}; T \<noteq> {}; \<forall>a. (a,{}) \<notin> R \<union> S \<union> T\<rbrakk> \<Longrightarrow> R \<parallel> (S \<cdot> T) \<subseteq> (R \<parallel> S) \<cdot> T" 
  quickcheck
  oops

lemma "\<lbrakk>R \<noteq> {}; S \<noteq> {}; T \<noteq> {}; \<forall>a. (a,{}) \<notin> R \<union> S \<union> T\<rbrakk> \<Longrightarrow> R \<cdot> (S \<parallel> T) \<subseteq> (R \<cdot> S) \<parallel> T"
  quickcheck
  oops

lemma "\<lbrakk>R \<noteq> {}; S \<noteq> {}; T \<noteq> {}; \<forall>a. (a,{}) \<notin> R \<union> S \<union> T\<rbrakk> \<Longrightarrow> (R \<cdot> S) \<parallel> T \<subseteq> R \<cdot> (S \<parallel> T)"
  quickcheck
  oops

lemma "\<lbrakk>R \<noteq> {}; S \<noteq> {}; \<forall>a. (a,{}) \<notin> R \<union> S\<rbrakk> \<Longrightarrow> (R \<parallel> S) \<cdot> (R \<parallel> S) \<subseteq> (R \<cdot> R) \<parallel> (S \<cdot> S)"
  quickcheck
  oops

lemma "\<lbrakk>R \<noteq> {}; S \<noteq> {}; \<forall>a. (a,{}) \<notin> R \<union> S\<rbrakk> \<Longrightarrow> (R \<cdot> R) \<parallel> (S \<cdot> S) \<subseteq> (R \<parallel> S) \<cdot> (R \<parallel> S)"
  quickcheck
  oops

subsection \<open>Relationship with Up-Closed Multirelations\<close>

text \<open>We now define Parikh's sequential composition.\<close>

definition s_prod_pa :: "'a mrel \<Rightarrow> 'a mrel \<Rightarrow> 'a mrel" (infixl "\<otimes>" 70) where
  "R \<otimes> S = {(a,A). (\<exists>B. (a,B) \<in> R \<and> (\<forall>b \<in> B. (b,A) \<in> S))}"

text \<open>We show that Parikh's definition doesn't preserve up-closure.\<close>

lemma up_closed_prop: "((R \<parallel> U) \<cdot> (S \<parallel> U)) \<parallel> U = (R \<parallel> U) \<cdot> (S \<parallel> U)"
  apply (auto simp: p_prod_def s_prod_pa_def U_def)
  nitpick
  oops

text \<open>Lemma 15.1.\<close>

lemma onelem: "(R \<cdot> S) \<parallel> U \<subseteq> R \<otimes> (S \<parallel> U)"
  by (auto simp: s_prod_im p_prod_def U_def s_prod_pa_def)

lemma twolem: "R \<otimes> (S \<parallel> U)  \<subseteq> (R \<cdot> S) \<parallel> U"
proof clarify
  fix a A
  assume "(a,A) \<in> R \<otimes> (S \<parallel> U)"
  hence "\<exists>B. (a,B) \<in> R \<and> (\<forall>b \<in> B. (b,A) \<in> S \<parallel> U)"
    by (auto simp: s_prod_pa_def)
  hence "\<exists>B. (a,B) \<in> R \<and> (\<forall>b \<in> B. \<exists>C. C \<subseteq> A \<and> (b,C) \<in> S)"
    by (metis U_par_st)
  hence "\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. f b \<subseteq> A \<and> (b,f b) \<in> S))"
    by metis
  hence "\<exists>C. C \<subseteq> A \<and> (\<exists>B. (a,B) \<in> R \<and> (\<exists>f. (\<forall>b \<in> B. (b,f b) \<in> S) \<and> C = \<Union> ((\<lambda>x. f x) ` B)))"
    by clarsimp blast
  hence "\<exists>C. C \<subseteq> A \<and> (a,C) \<in> R \<cdot> S"     
    by (clarsimp simp: mr_simp)
  thus "(a,A) \<in> (R \<cdot> S) \<parallel> U"
    by (simp add: U_par_st)
qed

lemma pe_pa_sim: "(R \<cdot> S) \<parallel> U = R \<otimes> (S \<parallel> U)"
  by (metis antisym onelem twolem)

lemma pe_pa_sim_var: "((R \<parallel> U) \<cdot> (S \<parallel> U)) \<parallel> U = (R \<parallel> U) \<otimes> (S \<parallel> U)"
  by (simp add: mrel_proto_trioid.mult_assoc pe_pa_sim)

lemma pa_assoc1: "((R \<parallel> U) \<otimes> (S \<parallel> U)) \<otimes> (T \<parallel> U) \<subseteq> (R \<parallel> U) \<otimes> ((S \<parallel> U) \<otimes> (T \<parallel> U))"
  by (clarsimp simp: p_prod_def s_prod_pa_def U_def, metis)

text \<open>The converse direction of associativity remains to be proved.\<close>

text \<open>Corollary 15.3.\<close>

lemma up_closed_par_is_meet: "(R \<parallel> U) \<parallel> (S \<parallel> U) = (R \<parallel> U) \<inter> (S \<parallel> U)"
  by (auto simp: mr_simp)

end
