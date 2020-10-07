theory "Coincidence" 
imports
  "Lib"
  "Syntax"
  "Denotational_Semantics"
  "Static_Semantics"
  "HOL.Finite_Set"
begin
section \<open>Static Semantics Properties\<close>

subsection Auxiliaries

text \<open>The state interpolating \<open>stateinterpol \<nu> \<omega> S\<close> between \<open>\<nu>\<close> and \<open>\<omega>\<close> that is \<open>\<nu>\<close> on \<open>S\<close> and \<open>\<omega>\<close> elsewhere\<close>

definition stateinterpol:: "state \<Rightarrow> state \<Rightarrow> variable set \<Rightarrow> state"
  where
  "stateinterpol \<nu> \<omega> S = (\<lambda>x. if (x\<in>S) then \<nu>(x) else \<omega>(x))"

definition statediff:: "state \<Rightarrow> state \<Rightarrow> variable set"
  where "statediff \<nu> \<omega> = {x. \<nu>(x)\<noteq>\<omega>(x)}"

lemma nostatediff: "x\<notin>statediff \<nu> \<omega> \<Longrightarrow> \<nu>(x)=\<omega>(x)"
  by (simp add: statediff_def)

lemma stateinterpol_empty: "stateinterpol \<nu> \<omega> {} = \<omega>"
proof
  fix x
  have empty: "\<And>x. \<not>(x\<in>{})" by auto
  show "\<And>x. stateinterpol \<nu> \<omega> {} x = \<omega> x" using empty by (simp add: stateinterpol_def)
qed

lemma stateinterpol_left [simp]: "x\<in>S \<Longrightarrow> (stateinterpol \<nu> \<omega> S)(x)=\<nu>(x)"
  by (simp add: stateinterpol_def)

lemma stateinterpol_right [simp]: "x\<notin>S \<Longrightarrow> (stateinterpol \<nu> \<omega> S)(x)=\<omega>(x)"
  by (simp add: stateinterpol_def)

lemma Vagree_stateinterpol [simp]: "Vagree (stateinterpol \<nu> \<omega> S) \<nu> S"
  and "Vagree (stateinterpol \<nu> \<omega> S) \<omega> (-S)"
  unfolding Vagree_def by auto

lemma Vagree_ror: "Vagree \<nu> \<nu>' (V\<inter>W) \<Longrightarrow> (\<exists>\<omega>. (Vagree \<nu> \<omega> V \<and> Vagree \<omega> \<nu>' W))"
proof -
  assume "Vagree \<nu> \<nu>' (V\<inter>W)"
  hence "\<forall>x. x\<in>V\<inter>W \<longrightarrow> \<nu>(x)=\<nu>'(x)" by (simp add: Vagree_def)
  let ?w="stateinterpol \<nu> \<nu>' V"
  have l: "Vagree \<nu> ?w V" by (simp add: Vagree_def)
  have r: "Vagree ?w \<nu>' W \<and> Vagree ?w \<nu>' W" by (simp add: Vagree_def stateinterpol_def \<open>\<forall>x. x\<in>V\<inter>W \<longrightarrow> \<nu> x = \<nu>' x\<close>)
  have "Vagree \<nu> ?w V \<and> Vagree ?w \<nu>' W" using l and r by blast
  thus ?thesis by auto
qed


text \<open>Remark 8 \<^url>\<open>https://doi.org/10.1007/978-3-319-94205-6_15\<close> about simple properties of projections\<close>

lemma restrictto_extends [simp]: "restrictto X V \<supseteq> X"
  by (auto simp add: restrictto_def)

lemma restrictto_compose [simp]: "restrictto (restrictto X V) W = restrictto X (V\<inter>W)"
proof
  show "restrictto (restrictto X V) W \<subseteq> restrictto X (V\<inter>W)"
    by (auto simp add: restrictto_def Vagree_def)
next
  show "restrictto X (V\<inter>W) \<subseteq> restrictto (restrictto X V) W" 
  (*by (smt Vagree_ror mem_Collect_eq restrictto_def subsetI)*)
  proof - (* sledgehammer *)
  obtain rr :: "(variable \<Rightarrow> real) set \<Rightarrow> (variable \<Rightarrow> real) set \<Rightarrow> variable \<Rightarrow> real" where
  "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (rr x0 x1 \<in> x1 \<and> rr x0 x1 \<notin> x0)"
  by moura
  then have f1: "\<forall>F Fa. rr Fa F \<in> F \<and> rr Fa F \<notin> Fa \<or> F \<subseteq> Fa"
  by (meson subsetI)
  obtain rra :: "(variable \<Rightarrow> real) \<Rightarrow> variable set \<Rightarrow> (variable \<Rightarrow> real) set \<Rightarrow> variable \<Rightarrow> real" where
  "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x2 \<and> Vagree v3 x0 x1) = (rra x0 x1 x2 \<in> x2 \<and> Vagree (rra x0 x1 x2) x0 x1)"
  by moura
  then have f2: "\<forall>F V f. (f \<notin> {f. \<exists>fa. fa \<in> F \<and> Vagree fa f V} \<or> rra f V F \<in> F \<and> Vagree (rra f V F) f V) \<and> (f \<in> {f. \<exists>fa. fa \<in> F \<and> Vagree fa f V} \<or> (\<forall>fa. fa \<notin> F \<or> \<not> Vagree fa f V))"
  by blast
  moreover
  { assume "\<exists>f. f \<in> X \<and> Vagree f (v4_1 W V (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) (rra (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) (V \<inter> W) X)) V"
    moreover
    { assume "\<exists>f. f \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree f (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) W"
      then have "rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)} \<notin> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)} \<or> rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)} \<in> {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W}"
      by blast
      then have "{f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)} \<subseteq> {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W}"
      using f1 by meson }
    ultimately have "(\<not> Vagree (rra (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) (V \<inter> W) X) (v4_1 W V (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) (rra (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) (V \<inter> W) X)) V \<or> \<not> Vagree (v4_1 W V (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) (rra (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) (V \<inter> W) X)) (rr {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W} {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)}) W) \<or> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)} \<subseteq> {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W}"
    using f2 by meson }
  ultimately have "{f. \<exists>fa. fa \<in> X \<and> Vagree fa f (V \<inter> W)} \<subseteq> {f. \<exists>fa. fa \<in> {f. \<exists>fa. fa \<in> X \<and> Vagree fa f V} \<and> Vagree fa f W}"
  using f1 by (meson Vagree_ror)
  then show ?thesis
  using restrictto_def by presburger
  qed 
qed

lemma restrictto_antimon [simp]: "W\<supseteq>V \<Longrightarrow> restrictto X W \<subseteq> restrictto X V"
proof -
  assume "W\<supseteq>V"
  then have "\<exists>U. V=W\<inter>U" by auto
  then obtain U where "V=W\<inter>U" by auto
  hence "restrictto X V = restrictto (restrictto X W) U" by simp
  hence "restrictto X V \<supseteq> restrictto X W" using restrictto_extends by blast
  thus ?thesis by auto
qed

lemma restrictto_empty [simp]: "X\<noteq>{} \<Longrightarrow> restrictto X {} = worlds"
  by (auto simp add: restrictto_def worlds_def)

lemma selectlike_shrinks [simp]: "selectlike X \<nu> V \<subseteq> X"
  by (auto simp add: selectlike_def)

lemma selectlike_compose [simp]: "selectlike (selectlike X \<nu> V) \<nu> W = selectlike X \<nu> (V\<union>W)"
  by (auto simp add: selectlike_def)

lemma selectlike_antimon [simp]: "W\<supseteq>V \<Longrightarrow> selectlike X \<nu> W \<subseteq> selectlike X \<nu> V"
  by (auto simp add: selectlike_def)

lemma selectlike_empty [simp]: "selectlike X \<nu> {} = X"
  by (auto simp add: selectlike_def)

lemma selectlike_self [simp]: "(\<nu> \<in> selectlike X \<nu> V) = (\<nu>\<in>X)"
  by (auto simp add: selectlike_def)

lemma selectlike_complement [simp]: "selectlike (-X) \<nu> V \<subseteq> -selectlike X \<nu> V"
  by (auto simp add: selectlike_def)

lemma selectlike_union: "selectlike (X\<union>Y) \<nu> V = selectlike X \<nu> V \<union> selectlike Y \<nu> V"
  by (auto simp add: selectlike_def)

lemma selectlike_Sup: "selectlike (Sup M) \<nu> V = Sup {selectlike X \<nu> V | X. X\<in>M}"
  using selectlike_def by auto

lemma selectlike_equal_cond: "(selectlike X \<nu> V = selectlike Y \<nu> V) = (\<forall>\<mu>. Uvariation \<mu> \<nu> (-V) \<longrightarrow> (\<mu>\<in>X) = (\<mu>\<in>Y))"
  unfolding selectlike_def using Uvariation_Vagree by auto

lemma selectlike_equal_cocond: "(selectlike X \<nu> (-V) = selectlike Y \<nu> (-V)) = (\<forall>\<mu>. Uvariation \<mu> \<nu> V \<longrightarrow> (\<mu>\<in>X) = (\<mu>\<in>Y))"
  using selectlike_equal_cond[where V=\<open>-V\<close>] by simp

lemma selectlike_equal_cocond_rule: "(\<And>\<mu>. Uvariation \<mu> \<nu> (-V) \<Longrightarrow> (\<mu>\<in>X) = (\<mu>\<in>Y))
  \<Longrightarrow> (selectlike X \<nu> V = selectlike Y \<nu> V)"
  using selectlike_equal_cond[where V=\<open>V\<close>] by simp

lemma selectlike_equal_cocond_corule: "(\<And>\<mu>. Uvariation \<mu> \<nu> V \<Longrightarrow> (\<mu>\<in>X) = (\<mu>\<in>Y))
  \<Longrightarrow> (selectlike X \<nu> (-V) = selectlike Y \<nu> (-V))"
  using selectlike_equal_cond[where V=\<open>-V\<close>] by simp

lemma co_selectlike: "-(selectlike X \<nu> V) = (-X) \<union> {\<omega>. \<not>Vagree \<omega> \<nu> V}"
  unfolding selectlike_def by auto

lemma selectlike_co_selectlike: "selectlike (-(selectlike X \<nu> V)) \<nu> V = selectlike (-X) \<nu> V"
  unfolding selectlike_def by auto

lemma selectlike_Vagree: "Vagree \<nu> \<omega> V \<Longrightarrow> selectlike X \<nu> V = selectlike X \<omega> V"
  using Vagree_def selectlike_def by auto  

lemma similar_selectlike_mem: "Vagree \<nu> \<omega> V \<Longrightarrow> (\<nu>\<in>selectlike X \<omega> V) = (\<nu>\<in>X)"
  unfolding selectlike_def using Vagree_sym_rel by blast  

(* also see nonBVG_rule *)
lemma BVG_nonelem [simp] :"(x\<notin>BVG \<alpha>) = (\<forall>I \<omega> X. (\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> {x})))"
  using BVG_elem monotone selectlike_shrinks
  by (metis subset_iff)


text \<open>\<open>statediff\<close> interoperability\<close>

lemma Vagree_statediff [simp]: "Vagree \<omega> \<omega>' S \<Longrightarrow> statediff \<omega> \<omega>' \<subseteq> -S"
  by (auto simp add: Vagree_def statediff_def)

lemma stateinterpol_diff [simp]: "stateinterpol \<nu> \<omega> (statediff \<nu> \<omega>) = \<nu>"
proof
  fix x
  show sp: "(stateinterpol \<nu> \<omega> (statediff \<nu> \<omega>))(x) = \<nu>(x)"
  proof (cases "x\<in>statediff \<nu> \<omega>")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis by (simp add: stateinterpol_def nostatediff)
  qed
qed

lemma stateinterpol_insert: "Vagree (stateinterpol v w S) (stateinterpol v w (insert z S)) (-{z})"
   by (simp add: Vagree_def stateinterpol_def)


lemma stateinterpol_FVT [simp]: "z\<notin>FVT(t) \<Longrightarrow> term_sem I t (stateinterpol \<omega> \<omega>' S) = term_sem I t (stateinterpol \<omega> \<omega>' (insert z S))"
proof -
  assume a: "z\<notin>FVT(t)"
  have fvc: "\<And>v. \<And>w. Vagree v w (-{z}) \<Longrightarrow> (term_sem I t v = term_sem I t w)" using a by (simp add: FVT_def)
  then show "term_sem I t (stateinterpol \<omega> \<omega>' S) = term_sem I t (stateinterpol \<omega> \<omega>' (insert z S))"
    using fvc and stateinterpol_insert by blast
qed

subsection \<open>Coincidence Lemmas\<close>

paragraph \<open>Coincidence for Terms\<close>

text \<open>Lemma 10 \<^url>\<open>https://doi.org/10.1007/978-3-319-94205-6_15\<close>\<close>

theorem coincidence_term: "Vagree \<omega> \<omega>' (FVT \<theta>) \<Longrightarrow> term_sem I \<theta> \<omega> = term_sem I \<theta> \<omega>'"
proof -
  assume a: "Vagree \<omega> \<omega>' (FVT \<theta>)"
  have isS: "statediff \<omega> \<omega>' \<subseteq> -FVT(\<theta>)" using a and Vagree_statediff by simp
  have gen: "S\<subseteq>-FVT(\<theta>) \<Longrightarrow> (term_sem I \<theta> \<omega>' = term_sem I \<theta> (stateinterpol \<omega> \<omega>' S))" if "finite S" for S
    using that
  proof (induction S)
    case empty
    show ?case by (simp add: stateinterpol_empty)
  next
    case (insert z S)
    thus ?case by auto
    qed
  from isS have finS: "finite (statediff \<omega> \<omega>')" using allvars_finite by (metis FVT_finite UNIV_def finite_compl rev_finite_subset)
  show ?thesis using gen[where S=\<open>statediff \<omega> \<omega>'\<close>, OF finS, OF isS] by simp
qed

corollary coincidence_term_cor: "Uvariation \<omega> \<omega>' U \<Longrightarrow> (FVT \<theta>)\<inter>U={} \<Longrightarrow> term_sem I \<theta> \<omega> = term_sem I \<theta> \<omega>'"
using coincidence_term Uvariation_Vagree
  by (metis Vagree_antimon disjoint_eq_subset_Compl double_compl)

  
lemma stateinterpol_FVF [simp]: "z\<notin>FVF(e) \<Longrightarrow> 
  ((stateinterpol \<omega> \<omega>' S) \<in> fml_sem I e \<longleftrightarrow> (stateinterpol \<omega> \<omega>' (insert z S)) \<in> fml_sem I e)"
proof -
  assume a: "z\<notin>FVF(e)"
  have agr: "Vagree (stateinterpol \<omega> \<omega>' S) (stateinterpol \<omega> \<omega>' (insert z S)) (-{z})" by (simp add: Vagree_def stateinterpol_def)
  have fvc: "\<And>v. \<And>w. (Vagree v w (-{z}) \<Longrightarrow> (v\<in>fml_sem I e \<Longrightarrow> w\<in>fml_sem I e))" using a by (simp add: FVF_def)
  then have fvce: "\<And>v. \<And>w. (Vagree v w (-{z}) \<Longrightarrow> ((v\<in>fml_sem I e) = (w\<in>fml_sem I e)))"  using Vagree_sym_rel by blast
  then show "(stateinterpol \<omega> \<omega>' S) \<in> fml_sem I e \<longleftrightarrow> (stateinterpol \<omega> \<omega>' (insert z S)) \<in> fml_sem I e"
    using agr by simp
qed


paragraph \<open>Coincidence for Formulas\<close>

text \<open>Lemma 11 \<^url>\<open>https://doi.org/10.1007/978-3-319-94205-6_15\<close>\<close>

theorem coincidence_formula: "Vagree \<omega> \<omega>' (FVF \<phi>) \<Longrightarrow> (\<omega> \<in> fml_sem I \<phi> \<longleftrightarrow> \<omega>' \<in> fml_sem I \<phi>)"
proof -
  assume a: "Vagree \<omega> \<omega>' (FVF \<phi>)"
  have isS: "statediff \<omega> \<omega>' \<subseteq> -FVF(\<phi>)" using a and Vagree_statediff by simp
  have gen: "S\<subseteq>-FVF(\<phi>) \<Longrightarrow> (\<omega>' \<in> fml_sem I \<phi> \<longleftrightarrow> (stateinterpol \<omega> \<omega>' S) \<in> fml_sem I \<phi>)" if "finite S" for S
    using that
  proof (induction S)
    case empty
    show ?case by (simp add: stateinterpol_empty)
  next
    case (insert z S)
    thus ?case by auto
  qed
  from isS have finS: "finite (statediff \<omega> \<omega>')" using allvars_finite by (metis FVF_finite UNIV_def finite_compl rev_finite_subset)
  show ?thesis using gen[where S=\<open>statediff \<omega> \<omega>'\<close>, OF finS, OF isS] by simp
qed

corollary coincidence_formula_cor: "Uvariation \<omega> \<omega>' U \<Longrightarrow> (FVF \<phi>)\<inter>U={} \<Longrightarrow> (\<omega> \<in> fml_sem I \<phi> \<longleftrightarrow> \<omega>' \<in> fml_sem I \<phi>)"
  using coincidence_formula Uvariation_Vagree 
  by (metis Uvariation_def disjoint_eq_subset_Compl inf.commute subsetCE)


paragraph \<open>Coincidence for Games\<close>

text \<open>\<open>Cignorabimus \<alpha> V\<close> is the set of all sets of variables that can be ignored for the coincidence game lemma\<close>
definition Cignorabimus:: "game \<Rightarrow> variable set \<Rightarrow> variable set set"
  where
"Cignorabimus \<alpha> V = {M. \<forall>I.\<forall>\<omega>.\<forall>\<omega>'.\<forall>X. (Vagree \<omega> \<omega>' (-M) \<longrightarrow> (\<omega>\<in>game_sem I \<alpha> (restrictto X V)) \<longrightarrow> (\<omega>'\<in>game_sem I \<alpha> (restrictto X V)))}"

lemma Cignorabimus_finite [simp]: "finite (Cignorabimus \<alpha> V)"
  unfolding Cignorabimus_def using finite_powerset[OF allvars_finite] finite_subset using Finite_Set.finite_subset by fastforce 

lemma Cignorabimus_equiv [simp]: "Cignorabimus \<alpha> V = {M. \<forall>I.\<forall>\<omega>.\<forall>\<omega>'.\<forall>X. (Vagree \<omega> \<omega>' (-M) \<longrightarrow> (\<omega>\<in>game_sem I \<alpha> (restrictto X V)) = (\<omega>'\<in>game_sem I \<alpha> (restrictto X V)))}"
  unfolding Cignorabimus_def by (metis (no_types, lifting) Vagree_sym_rel)

lemma Cignorabimus_antimon [simp]: "M \<in> Cignorabimus \<alpha> V \<and> N\<subseteq>M \<Longrightarrow> N \<in> Cignorabimus \<alpha> V"
  unfolding Cignorabimus_def
  using Vagree_antimon by blast 

lemma coempty: "-{}=allvars"
  by simp

lemma Cignorabimus_empty [simp]: "{} \<in> Cignorabimus \<alpha> V"
  unfolding Cignorabimus_def using coempty Vagree_univ
  by simp

text \<open>Cignorabimus contains nonfree variables\<close>
lemma Cignorabimus_init: "V\<supseteq>FVG(\<alpha>) \<Longrightarrow> x\<notin>V \<Longrightarrow> {x}\<in>Cignorabimus \<alpha> V"
proof-
  assume "V\<supseteq>FVG(\<alpha>)"
  assume a0: "x\<notin>V"
  hence a1: "x\<notin>FVG(\<alpha>)" using \<open>FVG \<alpha> \<subseteq> V\<close> by blast
  hence "\<And>I v w. Vagree v w (-{x}) \<Longrightarrow> (v \<in> game_sem I \<alpha> (restrictto X (-{x})) \<longleftrightarrow> w \<in> game_sem I \<alpha> (restrictto X (-{x})))" 
  by (metis (mono_tags, lifting) CollectI FVG_def Vagree_sym_rel)
  show "{x}\<in>Cignorabimus \<alpha> V"
  proof-
    {
      fix I \<omega> \<omega>' X
      have "Vagree \<omega> \<omega>' (-{x}) \<longrightarrow> (\<omega>\<in>game_sem I \<alpha> (restrictto X V)) \<longrightarrow> (\<omega>'\<in>game_sem I \<alpha> (restrictto X V))"
      proof
        assume a2: "Vagree \<omega> \<omega>' (-{x})"
        show "(\<omega>\<in>game_sem I \<alpha> (restrictto X V)) \<longrightarrow> (\<omega>'\<in>game_sem I \<alpha> (restrictto X V))"
        proof
          assume "\<omega>\<in>game_sem I \<alpha> (restrictto X V)"
          hence "\<omega>\<in>game_sem I \<alpha> (restrictto (restrictto X V) (-{x}))" by (simp add: Int_absorb2 \<open>x\<notin>V\<close>)
          hence "\<omega>'\<in>game_sem I \<alpha> (restrictto (restrictto X V) (-{x}))" using FVG_def a1 a2 by blast
          hence "\<omega>'\<in>game_sem I \<alpha> (restrictto X (V\<inter>-{x}))" by simp
          show "\<omega>'\<in>game_sem I \<alpha> (restrictto X V)" using a0
            by (metis Int_absorb2 \<open>\<omega>' \<in> game_sem I \<alpha> (restrictto X (V \<inter> - {x}))\<close> subset_Compl_singleton)
        qed
      qed
    }
    thus ?thesis
      unfolding Cignorabimus_def
      by auto
  qed
qed


text \<open>Cignorabimus is closed under union\<close>
lemma Cignorabimus_union: "M\<in>Cignorabimus \<alpha> V \<Longrightarrow> N\<in>Cignorabimus \<alpha> V \<Longrightarrow> (M\<union>N)\<in>Cignorabimus \<alpha> V"
proof-
  assume a1: "M\<in>Cignorabimus \<alpha> V"
  assume a2: "N\<in>Cignorabimus \<alpha> V"
  show "(M\<union>N)\<in>Cignorabimus \<alpha> V" (*using a1 a2 unfolding Cignorabimus_def *)
  proof-
    {
      fix I \<omega> \<omega>' X
    assume a3: "Vagree \<omega> \<omega>' (-(M\<union>N))"
    have h1: "\<And>I \<omega> \<omega>'.\<And>X. (Vagree \<omega> \<omega>' (-M) \<Longrightarrow>  (\<omega>\<in>game_sem I \<alpha> (restrictto X V)) \<Longrightarrow> (\<omega>'\<in>game_sem I \<alpha> (restrictto X V)))" using a1 by simp
    have h2: "\<And>I \<omega> \<omega>'.\<And>X. (Vagree \<omega> \<omega>' (-N) \<Longrightarrow>  (\<omega>\<in>game_sem I \<alpha> (restrictto X V)) \<Longrightarrow> (\<omega>'\<in>game_sem I \<alpha> (restrictto X V)))" using a2 by simp
    let ?s = "stateinterpol \<omega>' \<omega> M"
    have v1: "Vagree \<omega> ?s (-(M\<union>N))" using a3 by (simp add: Vagree_def)
    have v2: "Vagree ?s \<omega>' (-(M\<union>N))" using a3 by (simp add: Vagree_def)
    have r1: "\<omega>\<in>game_sem I \<alpha> (restrictto X V) \<Longrightarrow> ?s\<in>game_sem I \<alpha> (restrictto X V)"
      by (metis ComplD Vagree_def h1 stateinterpol_right)
    have r2: "?s\<in>game_sem I \<alpha> (restrictto X V) \<Longrightarrow> \<omega>'\<in>game_sem I \<alpha> (restrictto X V)"
      by (metis Vagree_ror compl_sup h1 h2 v2)
    have res: "\<omega>\<in>game_sem I \<alpha> (restrictto X V) \<Longrightarrow> \<omega>'\<in>game_sem I \<alpha> (restrictto X V)" using r1 r2 by blast
    }
    thus ?thesis
      unfolding Cignorabimus_def
      by auto
  qed
qed


lemma powersetup_induct [case_names Base Cup]:
   "\<And>C. (\<And>M. M\<in>C \<Longrightarrow> P M) \<Longrightarrow>
    (\<And>S. (\<And>M. M\<in>S \<Longrightarrow> P M) \<Longrightarrow> P (\<Union>S)) \<Longrightarrow>
     P (\<Union>C)"
  by simp

lemma Union_insert: "\<Union>(insert x S) = x\<union>\<Union>S"
  by simp

lemma powerset2up_induct [case_names Finite Nonempty Base Cup]:
   "(finite C) \<Longrightarrow> (C\<noteq>{}) \<Longrightarrow> (\<And>M. M\<in>C \<Longrightarrow> P M) \<Longrightarrow>
    (\<And>M N. P M \<Longrightarrow> P N \<Longrightarrow> P (M\<union>N)) \<Longrightarrow>
     P (\<Union>C)"
proof (induction rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case by force
qed

lemma Cignorabimus_step: "(\<And>M. M\<in>S \<Longrightarrow> M\<in>Cignorabimus \<alpha> V) \<Longrightarrow> (\<Union>S)\<in>Cignorabimus \<alpha> V"
proof (cases "S={}")
  case True
  then show ?thesis using Cignorabimus_empty by simp
next
  case nonem: False
  then show "\<Union>S\<in>Cignorabimus \<alpha> V" if "\<And>M. M\<in>S \<Longrightarrow> M\<in>Cignorabimus \<alpha> V" and nonemp:"S\<noteq>{}" for S
  proof (induction rule: powerset2up_induct)
    case Finite                                                   
    then show ?case using Cignorabimus_finite by (meson infinite_super subset_eq that(1))  
  next
    case Nonempty
    then show ?case using nonemp by simp
  next
    case (Base M)
    then show ?case using that by simp
  next
    case (Cup S)
    then show ?case using that Cignorabimus_union by blast
  qed
qed

text \<open>Lemma 12 \<^url>\<open>https://doi.org/10.1007/978-3-319-94205-6_15\<close>\<close>

theorem coincidence_game: "Vagree \<omega> \<omega>' V \<Longrightarrow> V\<supseteq>FVG(\<alpha>) \<Longrightarrow> (\<omega> \<in> game_sem I \<alpha> (restrictto X V)) = (\<omega>' \<in> game_sem I \<alpha> (restrictto X V))"
proof-
  assume a1: "Vagree \<omega> \<omega>' V"
  assume a2: "V \<supseteq> FVG \<alpha>"
  have base: "{x}\<in>Cignorabimus \<alpha> V" if a3: "x\<notin>V" and a4: "V \<supseteq> FVG \<alpha>" for x V
    using a3 and a4 and Cignorabimus_init by simp
  have h: "-V = \<Union>{xx. \<exists>x. xx={x} \<and> x\<notin>V}" by auto (* finite *)
  have "(-V)\<in>Cignorabimus \<alpha> V" using a2 base h using Cignorabimus_step
  (*by (smt Cignorabimus_step mem_Collect_eq)*)
  proof - (*sledgehammer*)
    have f1: "\<forall>v V. v \<in> V \<or> \<not> FVG \<alpha> \<subseteq> V \<or> {v} \<in> Cignorabimus \<alpha> V"
      using base by satx
    obtain VV :: "variable set \<Rightarrow> game \<Rightarrow> variable set set \<Rightarrow> variable set" where
      f2: "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x2 \<and> v3 \<notin> Cignorabimus x1 x0) = (VV x0 x1 x2 \<in> x2 \<and> VV x0 x1 x2 \<notin> Cignorabimus x1 x0)"
      by moura
    obtain vv :: "variable set \<Rightarrow> variable" where
      f3: "((\<nexists>v. VV V \<alpha> {{v} |v. v \<notin> V} = {v} \<and> v \<notin> V) \<or> VV V \<alpha> {{v} |v. v \<notin> V} = {vv (VV V \<alpha> {{v} |v. v \<notin> V})} \<and> vv (VV V \<alpha> {{v} |v. v \<notin> V}) \<notin> V) \<and> ((\<exists>v. VV V \<alpha> {{v} |v. v \<notin> V} = {v} \<and> v \<notin> V) \<or> (\<forall>v. VV V \<alpha> {{v} |v. v \<notin> V} \<noteq> {v} \<or> v \<in> V))"
      by moura
    moreover
    { assume "{vv (VV V \<alpha> {{v} |v. v \<notin> V})} \<in> Cignorabimus \<alpha> V"
      then have "(VV V \<alpha> {{v} |v. v \<notin> V} \<noteq> {vv (VV V \<alpha> {{v} |v. v \<notin> V})} \<or> vv (VV V \<alpha> {{v} |v. v \<notin> V}) \<in> V) \<or> VV V \<alpha> {{v} |v. v \<notin> V} \<notin> {{v} |v. v \<notin> V} \<or> VV V \<alpha> {{v} |v. v \<notin> V} \<in> Cignorabimus \<alpha> V"
        by metis
      then have "(\<exists>v. VV V \<alpha> {{v} |v. v \<notin> V} = {v} \<and> v \<notin> V) \<longrightarrow> VV V \<alpha> {{v} |v. v \<notin> V} \<notin> {{v} |v. v \<notin> V} \<or> VV V \<alpha> {{v} |v. v \<notin> V} \<in> Cignorabimus \<alpha> V"
        using f3 by blast }
    ultimately have "VV V \<alpha> {{v} |v. v \<notin> V} \<notin> {{v} |v. v \<notin> V} \<or> VV V \<alpha> {{v} |v. v \<notin> V} \<in> Cignorabimus \<alpha> V"
      using f1 a2 by blast
    then have "\<Union>{{v} |v. v \<notin> V} \<in> Cignorabimus \<alpha> V"
      using f2 by (meson Cignorabimus_step)
    then show ?thesis
      using h by presburger
  qed
  from this show ?thesis by (simp add: a1)
qed

corollary coincidence_game_cor: "Uvariation \<omega> \<omega>' U \<Longrightarrow> U\<inter>FVG(\<alpha>)={} \<Longrightarrow> (\<omega> \<in> game_sem I \<alpha> (restrictto X (-U))) = (\<omega>' \<in> game_sem I \<alpha> (restrictto X (-U)))"
  using coincidence_game Uvariation_Vagree 
  by (metis Uvariation_Vagree coincidence_game compl_le_swap1 disjoint_eq_subset_Compl double_compl)

  
subsection \<open>Bound Effect Lemmas\<close>

text \<open>\<open>Bignorabimus \<alpha> V\<close> is the set of all sets of variables that can be ignored for boundeffect\<close>
definition Bignorabimus:: "game \<Rightarrow> variable set set"
  where
  "Bignorabimus \<alpha> = {M. \<forall>I.\<forall>\<omega>.\<forall>X. \<omega>\<in>game_sem I \<alpha> X \<longleftrightarrow> \<omega>\<in>game_sem I \<alpha> (selectlike X \<omega> M)}"

lemma Bignorabimus_finite [simp]: "finite (Bignorabimus \<alpha>)"
  unfolding Bignorabimus_def using finite_powerset[OF allvars_finite] finite_subset using Finite_Set.finite_subset by fastforce 

lemma Bignorabimus_single [simp]: "game_sem I \<alpha> (selectlike X \<omega> M) \<subseteq> game_sem I \<alpha> X"
  by (meson monotone selectlike_shrinks subsetCE)

lemma Bignorabimus_equiv [simp]: "Bignorabimus \<alpha> = {M. \<forall>I.\<forall>\<omega>.\<forall>X. (\<omega>\<in>game_sem I \<alpha> X \<longrightarrow> \<omega>\<in>game_sem I \<alpha> (selectlike X \<omega> M))}"
  (*by (smt Bignorabimus_def Bignorabimus_single Collect_cong subsetCE)*)
proof - (*sledgehammer transformed*)
  obtain VV :: "(variable set \<Rightarrow> bool) \<Rightarrow> (variable set \<Rightarrow> bool) \<Rightarrow> variable set" where
    f1: "\<forall>p pa. (\<not> p (VV pa p)) = pa (VV pa p) \<or> Collect p = Collect pa"
    by (metis (no_types) Collect_cong)
  obtain rr :: "variable set \<Rightarrow> game \<Rightarrow> variable \<Rightarrow> real" and ii :: "variable set \<Rightarrow> game \<Rightarrow> interp" and FF :: "variable set \<Rightarrow> game \<Rightarrow> (variable \<Rightarrow> real) set" where
    f2: "\<forall>x0 x1. (\<exists>v2 v3 v4. (v3 \<in> game_sem v2 x1 v4) \<noteq> (v3 \<in> game_sem v2 x1 (selectlike v4 v3 x0))) = ((rr x0 x1 \<in> game_sem (ii x0 x1) x1 (FF x0 x1)) \<noteq> (rr x0 x1 \<in> game_sem (ii x0 x1) x1 (selectlike (FF x0 x1) (rr x0 x1) x0)))"
    by moura
    have fact: "{V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))} = {V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)}"
        using f1 by (metis (no_types, hide_lams) Bignorabimus_single subsetCE)
  have f3: "rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha> \<notin> game_sem (ii (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) \<alpha> (selectlike (FF (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) (rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)))) \<or> rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha> \<in> game_sem (ii (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) \<alpha> (FF (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>)"
    using Bignorabimus_single by blast
  have f4: "(\<not> (\<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)))))) \<or> (\<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))))))) \<and> ((\<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)))))) \<or> (rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha> \<notin> game_sem (ii (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) \<alpha> (FF (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>)) = (rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha> \<in> game_sem (ii (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) \<alpha> (selectlike (FF (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) (rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))))))"
    using f2 by blast
  have "rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha> \<in> game_sem (ii (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) \<alpha> (FF (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) \<longrightarrow> (\<exists>i f F. f \<in> game_sem i \<alpha> F \<and> f \<notin> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))))) \<or> rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha> \<in> game_sem (ii (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) \<alpha> (selectlike (FF (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) (rr (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))) \<alpha>) (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))))"
    by blast
  moreover
  { assume "\<exists>i f F. f \<in> game_sem i \<alpha> F \<and> f \<notin> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))))"
    then have "\<not> (\<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)))))"
      by blast
    moreover
    { assume "(\<not> (\<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)))))) \<noteq> (\<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))))))"
      then have "{V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))} = {V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)}"
        using fact by simp }
    ultimately have "(\<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)))))) \<or> {V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))} = {V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)}"
      by satx }
  moreover
  { assume "\<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)))))"
    then have "(\<not> (\<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)))))) \<noteq> (\<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f (VV (\<lambda>V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))) (\<lambda>V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V))))))"
      by blast
    then have "{V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))} = {V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)}"
      using fact by simp}
  ultimately have "{V. \<forall>i f F. (f \<in> game_sem i \<alpha> F) = (f \<in> game_sem i \<alpha> (selectlike F f V))} = {V. \<forall>i f F. f \<in> game_sem i \<alpha> F \<longrightarrow> f \<in> game_sem i \<alpha> (selectlike F f V)}"
    using f4 f3 by satx
  then show ?thesis
    using Bignorabimus_def by presburger
qed 

lemma Bignorabimus_empty [simp]: "{} \<in> Bignorabimus \<alpha>"
  unfolding Bignorabimus_def using coempty selectlike_empty
  by simp

lemma Bignorabimus_init: "x\<notin>BVG(\<alpha>) \<Longrightarrow> {x}\<in>Bignorabimus \<alpha>"
  unfolding Bignorabimus_def BVG_def
proof-
  assume "x \<notin> {x. \<exists>I \<omega> X. \<omega> \<in> game_sem I \<alpha> X \<and> \<omega> \<notin> game_sem I \<alpha> (selectlike X \<omega> {x})}"
  hence "\<not>(\<exists>I \<omega> X. \<omega> \<in> game_sem I \<alpha> X \<and> \<omega> \<notin> game_sem I \<alpha> (selectlike X \<omega> {x}))" by simp
  hence "\<forall>I \<omega> X. (\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> {x}))" using Bignorabimus_single by blast
  thus "{x} \<in> {M. \<forall>I \<omega> X. (\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> M))}" by simp
qed

text \<open>Bignorabimus is closed under union\<close>
lemma Bignorabimus_union: "M\<in>Bignorabimus \<alpha> \<Longrightarrow> N\<in>Bignorabimus \<alpha> \<Longrightarrow> (M\<union>N)\<in>Bignorabimus \<alpha>"
proof -
  assume a1: "M\<in>Bignorabimus \<alpha>"
  assume a2: "N\<in>Bignorabimus \<alpha>"
  have h1: "\<forall>I.\<forall>\<omega>.\<forall>X. (\<omega>\<in>game_sem I \<alpha> X) \<longleftrightarrow> (\<omega>\<in>game_sem I \<alpha> (selectlike X \<omega> M))" using a1
    using Bignorabimus_equiv Bignorabimus_single by blast
  have h2: "\<forall>I.\<forall>\<omega>.\<forall>X. (\<omega>\<in>game_sem I \<alpha> X) \<longleftrightarrow> (\<omega>\<in>game_sem I \<alpha> (selectlike X \<omega> N))" using a2
    using Bignorabimus_equiv Bignorabimus_single by blast
  have c: "\<forall>I.\<forall>\<omega>.\<forall>X. (\<omega>\<in>game_sem I \<alpha> X) \<longleftrightarrow> (\<omega>\<in>game_sem I \<alpha> (selectlike X \<omega> (M\<union>N)))" by (metis h1 h2 selectlike_compose)
  then show "(M\<union>N)\<in>Bignorabimus \<alpha>" unfolding Bignorabimus_def using c by fastforce 
qed

lemma Bignorabimus_step: "(\<And>M. M\<in>S \<Longrightarrow> M\<in>Bignorabimus \<alpha>) \<Longrightarrow> (\<Union>S)\<in>Bignorabimus \<alpha>"
proof (cases "S={}")
  case True
  then show ?thesis using Bignorabimus_empty by simp
next
  case nonem: False
  then show "\<Union>S\<in>Bignorabimus \<alpha>" if "\<And>M. M\<in>S \<Longrightarrow> M\<in>Bignorabimus \<alpha>" and nonemp:"S\<noteq>{}" for S
  proof (induction rule: powerset2up_induct)
    case Finite
    then show ?case using Bignorabimus_finite by (meson infinite_super subset_eq that(1))  
  next
    case Nonempty
    then show ?case using nonemp by simp
  next
    case (Base M)
    then show ?case using that by simp
  next
    case (Cup S)
    then show ?case using that Bignorabimus_union by blast
  qed
qed


text \<open>Lemma 13 \<^url>\<open>https://doi.org/10.1007/978-3-319-94205-6_15\<close>\<close>

theorem boundeffect: "(\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> (-BVG(\<alpha>))))"
proof-
  have base: "{x}\<in>Bignorabimus \<alpha>" if a3: "x\<notin>BVG \<alpha>" for x using a3 and Bignorabimus_init by simp
  have h: "-BVG \<alpha> = \<Union>{xx. \<exists>x. xx={x} \<and> x\<notin>BVG \<alpha>}" by blast (* finite *)
  have "(-BVG \<alpha>)\<in>Bignorabimus \<alpha>" using base h
  (*by (smt Bignorabimus_step mem_Collect_eq)*)
  proof - (*sledgehammer*)
    obtain VV :: "game \<Rightarrow> variable set set \<Rightarrow> variable set" where
      f1: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> Bignorabimus x0) = (VV x0 x1 \<in> x1 \<and> VV x0 x1 \<notin> Bignorabimus x0)"
      by moura
    have "VV \<alpha> {{v} |v. v \<notin> BVG \<alpha>} \<notin> {{v} |v. v \<notin> BVG \<alpha>} \<or> VV \<alpha> {{v} |v. v \<notin> BVG \<alpha>} \<in> Bignorabimus \<alpha>"
      by fastforce
    then have "\<Union>{{v} |v. v \<notin> BVG \<alpha>} \<in> Bignorabimus \<alpha>"
      using f1 by (meson Bignorabimus_step)
    then show ?thesis
      using h by presburger
  qed
  from this show ?thesis using Bignorabimus_def by blast
qed

corollary boundeffect_cor: "V\<inter>BVG(\<alpha>)={} \<Longrightarrow> (\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> V))"
  using boundeffect
  by (metis disjoint_eq_subset_Compl selectlike_compose sup.absorb_iff2)


subsection \<open>Static Analysis Observations\<close>

lemma BVG_equiv: "game_equiv \<alpha> \<beta> \<Longrightarrow> BVG(\<alpha>) = BVG(\<beta>)"
proof-
  assume a: "game_equiv \<alpha> \<beta>" 
  show "BVG(\<alpha>) = BVG(\<beta>)" unfolding BVG_def using game_equiv_subst_eq[OF a] by metis
qed

lemmas union_or = Set.Un_iff

lemma not_union_or: "(x\<notin>A\<union>B) = (x\<notin>A \<and> x\<notin>B)"
  by simp

lemma repv_selectlike_self: "(repv \<omega> x d \<in> selectlike X \<omega> {x}) = (d=\<omega>(x) \<and> \<omega> \<in> X)"
  unfolding selectlike_def using Vagree_repv_self Vagree_sym
  by (metis (no_types, lifting) mem_Collect_eq repv_self)

lemma repv_selectlike_other: "x\<noteq>y \<Longrightarrow> (repv \<omega> x d \<in> selectlike X \<omega> {y}) = (repv \<omega> x d \<in> X)"
proof
  assume a: "x\<noteq>y"
  then have h: "{y}\<subseteq>-{x}" by simp
  show "(repv \<omega> x d \<in> selectlike X \<omega> {y}) \<Longrightarrow> (repv \<omega> x d \<in> X)" using a selectlike_def Vagree_repv[of \<omega> x d] 
  by auto
  show "(repv \<omega> x d \<in> X) \<Longrightarrow> (repv \<omega> x d \<in> selectlike X \<omega> {y})" 
  using selectlike_def[where X=X and \<nu>=\<omega> and V=\<open>-{x}\<close>] Vagree_repv[where \<omega>=\<omega> and x=x and d=d]
  selectlike_antimon[where X=X and \<nu>=\<omega> and V=\<open>{y}\<close> and W=\<open>-{x}\<close>, OF h] Vagree_sym[where \<nu>=\<open>repv \<omega> x d\<close> and V=\<open>-{x}\<close>]
  by auto
qed

lemma repv_selectlike_other_converse: "x\<noteq>y \<Longrightarrow> (repv \<omega> x d \<in> X) = (repv \<omega> x d \<in> selectlike X \<omega> {y})"
  using repv_selectlike_other HOL.eq_commute by blast


lemma BVG_assign_other: "x\<noteq>y \<Longrightarrow> y\<notin>BVG(Assign x \<theta>)"
  using repv_selectlike_other_converse[where x=x and y=y] by simp

lemma BVG_assign_meta: "(\<And>I \<omega>. term_sem I \<theta> \<omega> = \<omega>(x)) \<Longrightarrow> BVG(Assign x \<theta>) = {}"
  and "term_sem I \<theta> \<omega> \<noteq> \<omega>(x) \<Longrightarrow> BVG(Assign x \<theta>) = {x}"
  (*using repv_selectlike_self BVG_assign_other BVG_def BVG_elem*)
proof-
  have fact: "BVG(Assign x \<theta>) \<subseteq> {x}" using BVG_assign_other by (metis singleton_iff subsetI)
  from fact show "(\<And>I \<omega>. term_sem I \<theta> \<omega> = \<omega>(x)) \<Longrightarrow> BVG(Assign x \<theta>) = {}" using BVG_def by simp
  have h2: "\<exists>I \<omega>. term_sem I \<theta> \<omega> \<noteq> \<omega>(x) \<Longrightarrow> x \<in> BVG(Assign x \<theta>)" using repv_selectlike_self by auto
  from fact show "term_sem I \<theta> \<omega> \<noteq> \<omega>(x) \<Longrightarrow> BVG(Assign x \<theta>) = {x}" using BVG_elem h2 by blast 
qed

lemma BVG_assign: "BVG(Assign x \<theta>) = (if (\<forall>I \<omega>. term_sem I \<theta> \<omega> = \<omega>(x)) then {} else {x})"
using repv_selectlike_self repv_selectlike_other BVG_assign_other 
proof-
  have c0: "BVG(Assign x \<theta>) \<subseteq> {x}" using BVG_assign_other by (metis singletonI subsetI)
  have c1: "\<forall>I \<omega>. term_sem I \<theta> \<omega> = \<omega>(x) \<Longrightarrow> BVG(Assign x \<theta>) = {}" using BVG_assign_other by auto
  have h2: "\<exists>I \<omega>. term_sem I \<theta> \<omega> \<noteq> \<omega>(x) \<Longrightarrow> x \<in> BVG(Assign x \<theta>)" using repv_selectlike_self by auto
  have c2: "\<exists>I \<omega>. term_sem I \<theta> \<omega> \<noteq> \<omega>(x) \<Longrightarrow> BVG(Assign x \<theta>) = {x}" using c0 h2 by blast 
  from c1 and c2 show ?thesis by simp
qed

lemma BVG_ODE_other: "y\<noteq>RVar x \<Longrightarrow> y\<noteq>DVar x \<Longrightarrow> y\<notin>BVG(ODE x \<theta>)"
  (*using nonBVG_rule selectlike_equal_cocond_rule solves_ODE_def*)
proof-
  assume yx: "y\<noteq>RVar x"
  assume yxp: "y\<noteq>DVar x"
  show "y\<notin>BVG(ODE x \<theta>)"
  proof (rule nonBVG_inc_rule)
    fix I \<omega> X
    assume "\<omega> \<in> game_sem I (ODE x \<theta>) X"
    then have "\<exists>F T. Vagree \<omega> (F(0)) (-{DVar x}) \<and> F(T) \<in> X \<and> solves_ODE I F x \<theta>" by simp
    then obtain F T where "Vagree \<omega> (F(0)) (-{DVar x}) \<and> F(T) \<in> X \<and> solves_ODE I F x \<theta>" by blast
    then have "Vagree \<omega> (F(0)) (-{DVar x}) \<and> F(T) \<in> (selectlike X \<omega> {y}) \<and> solves_ODE I F x \<theta>"
    using yx yxp solves_Vagree Vagree_def similar_selectlike_mem by auto 
    then have "\<exists>F T. Vagree \<omega> (F(0)) (-{DVar x}) \<and> F(T) \<in> (selectlike X \<omega> {y}) \<and> solves_ODE I F x \<theta>" by blast 
    then show "\<omega> \<in> game_sem I (ODE x \<theta>) (selectlike X \<omega> {y})" by simp
  qed
qed

text \<open>This result could be strengthened to a conditional equality based on the RHS values\<close>

lemma BVG_ODE: "BVG(ODE x \<theta>) \<subseteq> {RVar x,DVar x}"
  using BVG_ODE_other by blast


lemma BVG_test: "BVG(Test \<phi>) = {}"
  unfolding BVG_def game_sem.simps by auto


lemma BVG_choice: "BVG(Choice \<alpha> \<beta>) \<subseteq> BVG(\<alpha>) \<union> BVG(\<beta>)"
  unfolding BVG_def game_sem.simps using not_union_or by auto
(*proof-
  have f1: "\<And>\<omega> I X. (\<omega> \<in> game_sem I \<alpha> X \<union> game_sem I \<beta> X) = 
  (\<omega> \<in> game_sem I \<alpha> X \<or> \<omega> \<in> game_sem I \<beta> X)" by (rule union_or)
  have f2: "\<And>\<omega> I X. (\<omega> \<notin> game_sem I \<alpha> (selectlike X \<omega> {x}) \<union> game_sem I \<beta> (selectlike X \<omega> {x})) =
  (\<omega> \<notin> game_sem I \<alpha> (selectlike X \<omega> {x}) \<and> \<omega> \<notin> game_sem I \<beta> (selectlike X \<omega> {x}))" by (rule not_union_or)
  let ?lhs = "{x. \<exists>I \<omega> X.
           \<omega> \<in> game_sem I \<alpha> X \<union> game_sem I \<beta> X \<and>
           \<omega> \<notin> game_sem I \<alpha> (selectlike X \<omega> {x}) \<union> game_sem I \<beta> (selectlike X \<omega> {x})}"
  let ?rhs = "{x. \<exists>I \<omega> X. \<omega> \<in> game_sem I \<alpha> X \<and> \<omega> \<notin> game_sem I \<alpha> (selectlike X \<omega> {x})} \<union>
       {x. \<exists>I \<omega> X. \<omega> \<in> game_sem I \<beta> X \<and> \<omega> \<notin> game_sem I \<beta> (selectlike X \<omega> {x})}"
  show "?lhs\<subseteq>?rhs" using f1 f2 by auto
qed*)

lemma select_nonBV: "x\<notin>BVG(\<alpha>) \<Longrightarrow> selectlike (game_sem I \<alpha> (selectlike X \<omega> {x})) \<omega> {x} = selectlike (game_sem I \<alpha> X) \<omega> {x}"
proof
  show "selectlike (game_sem I \<alpha> (selectlike X \<omega> {x})) \<omega> {x} \<subseteq> selectlike (game_sem I \<alpha> X) \<omega> {x}" 
  using game_sem_mono selectlike_shrinks selectlike_antimon Bignorabimus_single
  by (metis selectlike_union sup.absorb_iff1) 
  next
  assume nonbound: "x\<notin>BVG(\<alpha>)"
  then have fact: "{x}\<inter>BVG(\<alpha>)={}" by auto
  show "selectlike (game_sem I \<alpha> X) \<omega> {x} \<subseteq> selectlike (game_sem I \<alpha> (selectlike X \<omega> {x})) \<omega> {x}"
  proof
    fix \<mu>
    assume "\<mu> \<in> selectlike (game_sem I \<alpha> X) \<omega> {x}"
    (* "V\<inter>BVG(\<alpha>)={} \<Longrightarrow> (\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> V))" *)
    then have "\<mu> \<in> selectlike (game_sem I \<alpha> (selectlike X \<mu> {x})) \<omega> {x}"
    using boundeffect_cor[where \<omega>=\<mu> and V=\<open>{x}\<close> and \<alpha>=\<alpha>, OF fact] nonbound
    by (metis ComplD ComplI co_selectlike not_union_or)
    then show "\<mu> \<in> selectlike (game_sem I \<alpha> (selectlike X \<omega> {x})) \<omega> {x}" using selectlike_Vagree selectlike_def by fastforce 
  qed
qed

lemma BVG_compose: "BVG(Compose \<alpha> \<beta>) \<subseteq> BVG(\<alpha>) \<union> BVG(\<beta>)"
  (*unfolding BVG_def game_sem.simps using game_union union_or not_union_or selectlike_shrinks monotone selectlike_compose*)
proof
  fix x
  assume a: "x\<in>BVG(Compose \<alpha> \<beta>)"
  show "x \<in> BVG \<alpha> \<union> BVG \<beta>"
  proof (rule ccontr)
    assume "x\<notin>BVG \<alpha> \<union> BVG(\<beta>)"
    then have n\<beta>: "x\<notin>BVG(\<beta>)"
    and n\<alpha>: "x\<notin>BVG(\<alpha>)" by simp_all
    from a have "\<exists>I.\<exists>\<omega>.\<exists>X. \<omega> \<in> game_sem I (Compose \<alpha> \<beta>) X \<and> \<omega> \<notin> game_sem I (Compose \<alpha> \<beta>) (selectlike X \<omega> {x})" by simp
    then obtain I \<omega> X where adef: "\<omega> \<in> game_sem I (Compose \<alpha> \<beta>) X \<and> \<omega> \<notin> game_sem I (Compose \<alpha> \<beta>) (selectlike X \<omega> {x})" by blast
    from adef have a1: "\<omega> \<in> game_sem I \<alpha> (game_sem I \<beta> X)" by simp
    from adef have a2: "\<omega> \<notin> game_sem I \<alpha> (game_sem I \<beta> (selectlike X \<omega> {x}))" by simp
    let ?Y = "selectlike X \<omega> {x}"
    from n\<alpha> have n\<alpha>c: "\<And>I \<omega> X. (\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> {x}))" using BVG_nonelem by simp
    from n\<beta> have n\<beta>c: "\<And>I \<omega> X. (\<omega> \<in> game_sem I \<beta> X) = (\<omega> \<in> game_sem I \<beta> (selectlike X \<omega> {x}))" using BVG_nonelem by simp
    have c1: "\<omega> \<in> game_sem I \<alpha> (selectlike (game_sem I \<beta> X) \<omega> {x})" using a1 n\<alpha>c[where I=I and \<omega>=\<omega> and X=\<open>game_sem I \<beta> X\<close>] by blast
    have c2: "\<omega> \<notin> game_sem I \<alpha> (selectlike (game_sem I \<beta> ?Y) \<omega> {x})" using a2 n\<alpha>c[where I=I and \<omega>=\<omega> and X=\<open>game_sem I \<beta> ?Y\<close>] by blast
    from c2 have c3: "\<omega> \<notin> game_sem I \<alpha> (selectlike (game_sem I \<beta> X) \<omega> {x})" using n\<beta> selectlike_Vagree
    proof-
      have "selectlike (game_sem I \<beta> ?Y) \<omega> {x} = selectlike (game_sem I \<beta> X) \<omega> {x}" using n\<beta> by (rule select_nonBV) 
      thus ?thesis using c2 by simp
    qed
    show "False" using c1 c3 n\<beta>c[where I=I] by auto
  qed
qed


text \<open>The converse inclusion does not hold generally, because
   \<open>BVG(x := x+1; x:= x-1) = {} \<noteq> BVG(x := x+1) \<union> BVG(x := x-1) = {x}\<close>\<close>

lemma "BVG(Compose (Assign x (Plus (Var x) (Number 1))) (Assign x (Plus (Var x) (Number (-1))))) 
    \<noteq> BVG(Assign x (Plus (Var x) (Number 1))) \<union> BVG(Assign x (Plus (Var x) (Number (-1))))"
    unfolding BVG_def selectlike_def repv_def Vagree_def by auto


lemma BVG_loop: "BVG(Loop \<alpha>) \<subseteq> BVG(\<alpha>)"
proof
  fix x
  assume a: "x\<in>BVG(Loop \<alpha>)"
  show "x \<in> BVG(\<alpha>)"
  proof (rule ccontr)
    assume "\<not> (x \<in> BVG(\<alpha>))"
    then have n\<alpha>: "x\<notin>BVG \<alpha>" by simp
    from n\<alpha> have n\<alpha>c: "\<And>I \<omega> X. (\<omega> \<in> game_sem I \<alpha> X) = (\<omega> \<in> game_sem I \<alpha> (selectlike X \<omega> {x}))" using BVG_nonelem by simp
    have "x\<notin>BVG(Loop \<alpha>)" (*using BVG_nonelem*)
    proof (rule nonBVG_rule)
      fix I \<omega> X
      let ?f = "\<lambda>Z. X \<union> game_sem I \<alpha> Z"
      let ?g = "\<lambda>Y. (selectlike X \<omega> {x}) \<union> game_sem I \<alpha> Y"
      let ?R = "\<lambda>Z Y. selectlike Z \<omega> {x} = selectlike Y \<omega> {x}"
      have "?R (lfp ?f) (lfp ?g)"
      proof (induction rule: lfp_lockstep_induct[where f=\<open>?f\<close> and g=\<open>?g\<close> and R=\<open>?R\<close>])
        case monof
        then show ?case using game_sem_loop_fixpoint_mono by simp
      next
        case monog
        then show ?case using game_sem_loop_fixpoint_mono by simp
      next
        case (step A B)
        then have IH: "selectlike A \<omega> {x} = selectlike B \<omega> {x}" by simp
        then show ?case
        (* using selectlike_union n\<alpha> select_nonBV IH by (smt insert_absorb2 insert_def selectlike_compose singleton_conv smt_solver=cvc4)  *)
        proof-
          have "selectlike (X \<union> game_sem I \<alpha> A) \<omega> {x} = selectlike X \<omega> {x} \<union> selectlike (game_sem I \<alpha> A) \<omega> {x}" using selectlike_union by simp
          also have "... = selectlike X \<omega> {x} \<union> selectlike (game_sem I \<alpha> (selectlike A \<omega> {x})) \<omega> {x}" using n\<alpha> select_nonBV by blast 
          also have "... = selectlike X \<omega> {x} \<union> selectlike (game_sem I \<alpha> (selectlike B \<omega> {x})) \<omega> {x}" using IH by simp
          also have "... = selectlike (selectlike X \<omega> {x} \<union> game_sem I \<alpha> B) \<omega> {x}" using selectlike_union n\<alpha> select_nonBV by auto 
          finally show "selectlike (X \<union> game_sem I \<alpha> A) \<omega> {x} = selectlike (selectlike X \<omega> {x} \<union> game_sem I \<alpha> B) \<omega> {x}" .
        qed
        next
        case (union M)
        then have IH: "\<forall>(A,B)\<in>M. selectlike A \<omega> {x} = selectlike B \<omega> {x}" .
        then show ?case
        using fst_proj_mem[where M=M] snd_proj_mem[where M=M] 
        selectlike_Sup[where \<nu>=\<omega> and V=\<open>{x}\<close>] sup_corr_eq_chain by simp
        (*proof-
          have "selectlike (\<Union>fst_proj M) \<omega> {x} = \<Union>{selectlike A \<omega> {x} | A. A\<in>fst_proj M}" using selectlike_Sup by simp
          also have "... = \<Union>{selectlike B \<omega> {x} | B. B\<in>snd_proj M}" using sup_corr_eq_chain[OF IH] by simp
          also have "... = selectlike (\<Union>snd_proj M) \<omega> {x}" using selectlike_Sup by simp
          finally show "selectlike (\<Union>fst_proj M) \<omega> {x} = selectlike (\<Union>snd_proj M) \<omega> {x}" .
        qed*)
      qed
      from this show "(\<omega> \<in> game_sem I (Loop \<alpha>) X) = (\<omega> \<in> game_sem I (Loop \<alpha>) (selectlike X \<omega> {x}))"
      by (metis (mono_tags) game_sem.simps(6) lfp_def selectlike_self) 
      (*by (simp add: selectlike_self game_sem_loop_back)*)
    qed
  then show "False" using a by blast  
  qed
qed


lemma BVG_dual: "BVG(Dual \<alpha>) \<subseteq> BVG(\<alpha>)"
  (*unfolding game_sem.simps using BVG_elem selectlike_co_selectlike co_selectlike selectlike_complement selectlike_antimon*)
proof
  fix x
  assume a: "x\<in>BVG(Dual \<alpha>)"
  show "x\<in>BVG \<alpha>"
  proof-
    from a have "\<exists>I.\<exists>\<omega>.\<exists>X. \<omega> \<in> game_sem I (Dual \<alpha>) X \<and> \<omega> \<notin> game_sem I (Dual \<alpha>) (selectlike X \<omega> {x})" by simp
    then obtain I \<omega> X where adef: "\<omega> \<in> game_sem I (Dual \<alpha>) X \<and> \<omega> \<notin> game_sem I (Dual \<alpha>) (selectlike X \<omega> {x})" by blast
    from adef have a1: "\<omega> \<notin> game_sem I \<alpha> (- X)" by simp
    from adef have a2: "\<omega> \<in> game_sem I \<alpha> (- selectlike X \<omega> {x})" by simp
    let ?Y = "- selectlike X \<omega> {x}"
    have f1: "\<omega> \<in> game_sem I \<alpha> ?Y" by (rule a2)
    have f2: "\<omega> \<notin> game_sem I \<alpha> (selectlike ?Y \<omega> {x})" using a1 selectlike_co_selectlike
    by (metis (no_types, lifting) selectlike_shrinks monotone dual_order.trans subset_Compl_singleton)
    show "x\<in>BVG(\<alpha>)" using f1 f2 by auto
  qed
qed
  
end
