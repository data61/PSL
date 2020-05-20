section \<open>Terms and Literals\<close>

theory TermsAndLiterals imports Main "HOL-Library.Countable_Set" begin

type_synonym var_sym  = string
type_synonym fun_sym  = string
type_synonym pred_sym = string

datatype fterm = 
  Fun fun_sym (get_sub_terms: "fterm list")
| Var var_sym

datatype hterm = HFun fun_sym "hterm list" \<comment> \<open>Herbrand terms defined as in Berghofer's FOL-Fitting\<close>


type_synonym 't atom = "pred_sym * 't list"

datatype 't literal = 
  sign: Pos (get_pred: pred_sym) (get_terms: "'t list")
| Neg (get_pred: pred_sym) (get_terms: "'t list")

fun get_atom :: "'t literal \<Rightarrow> 't atom" where
  "get_atom (Pos p ts) = (p, ts)"
| "get_atom (Neg p ts) = (p, ts)"


subsection \<open>Ground\<close>

fun ground\<^sub>t :: "fterm \<Rightarrow> bool" where
  "ground\<^sub>t (Var x) \<longleftrightarrow> False"
| "ground\<^sub>t (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. ground\<^sub>t t)"

abbreviation ground\<^sub>t\<^sub>s :: "fterm list \<Rightarrow> bool" where
  "ground\<^sub>t\<^sub>s ts \<equiv> (\<forall>t \<in> set ts. ground\<^sub>t t)"

abbreviation ground\<^sub>l :: "fterm literal \<Rightarrow> bool" where
  "ground\<^sub>l l \<equiv> ground\<^sub>t\<^sub>s (get_terms l)"

abbreviation ground\<^sub>l\<^sub>s :: "fterm literal set \<Rightarrow> bool" where
  "ground\<^sub>l\<^sub>s C \<equiv> (\<forall>l \<in> C. ground\<^sub>l l)"
  
definition ground_fatoms :: "fterm atom set" where
  "ground_fatoms \<equiv> {a. ground\<^sub>t\<^sub>s (snd a)}"

lemma ground\<^sub>l_ground_fatom: 
  assumes "ground\<^sub>l l"
  shows "get_atom l \<in> ground_fatoms"
  using assms unfolding ground_fatoms_def by (induction l) auto


subsection \<open>Auxiliary\<close>

lemma infinity:
  assumes inj: "\<forall>n :: nat. undiago (diago n) = n" 
  assumes all_tree: "\<forall>n :: nat. (diago n) \<in> S"
  shows "\<not>finite S"
proof -
  from inj all_tree have "\<forall>n. n = undiago (diago n) \<and> (diago n) \<in> S" by auto
  then have "\<forall>n. \<exists>ds. n = undiago ds \<and> ds \<in> S" by auto
  then have "undiago ` S = (UNIV :: nat set)" by auto
  then show "\<not>finite S" by (metis finite_imageI infinite_UNIV_nat) 
qed

lemma inv_into_f_f:
  assumes "bij_betw f A B"
  assumes "a\<in>A"
  shows "(inv_into A f) (f a) = a"
using assms bij_betw_inv_into_left by metis

lemma f_inv_into_f:
  assumes "bij_betw f A B"
  assumes "b\<in>B"
  shows "f ((inv_into A f) b) = b"
using assms bij_betw_inv_into_right by metis


subsection \<open>Conversions\<close>


subsubsection \<open>Conversions - Terms and Herbrand Terms\<close>

fun fterm_of_hterm :: "hterm \<Rightarrow> fterm" where
  "fterm_of_hterm (HFun p ts) = Fun p (map fterm_of_hterm ts)"

definition fterms_of_hterms :: "hterm list \<Rightarrow> fterm list" where
  "fterms_of_hterms ts \<equiv> map fterm_of_hterm ts"

fun hterm_of_fterm :: "fterm \<Rightarrow> hterm" where
  "hterm_of_fterm (Fun p ts) = HFun p (map hterm_of_fterm ts)"

definition hterms_of_fterms :: "fterm list \<Rightarrow> hterm list" where
"hterms_of_fterms ts \<equiv> map hterm_of_fterm ts"

lemma hterm_of_fterm_fterm_of_hterm[simp]: "hterm_of_fterm (fterm_of_hterm t) = t" 
  by (induction t) (simp add: map_idI)

lemma hterms_of_fterms_fterms_of_hterms[simp]: "hterms_of_fterms (fterms_of_hterms ts) = ts" 
  unfolding hterms_of_fterms_def fterms_of_hterms_def by (simp add: map_idI)

lemma fterm_of_hterm_hterm_of_fterm[simp]:
  assumes "ground\<^sub>t t"
  shows "fterm_of_hterm (hterm_of_fterm t) = t" 
  using assms by (induction t) (auto simp add: map_idI)

lemma fterms_of_hterms_hterms_of_fterms[simp]: 
  assumes "ground\<^sub>t\<^sub>s ts"
  shows "fterms_of_hterms (hterms_of_fterms ts) = ts" 
  using assms unfolding fterms_of_hterms_def hterms_of_fterms_def by (simp add: map_idI)

lemma ground_fterm_of_hterm:  "ground\<^sub>t (fterm_of_hterm t)"
  by (induction t) (auto simp add: map_idI)

lemma ground_fterms_of_hterms: "ground\<^sub>t\<^sub>s (fterms_of_hterms ts)"
  unfolding fterms_of_hterms_def using ground_fterm_of_hterm by auto


subsubsection \<open>Conversions -  Literals and Herbrand Literals\<close>

fun flit_of_hlit :: "hterm literal \<Rightarrow> fterm literal" where
  "flit_of_hlit (Pos p ts) = Pos p (fterms_of_hterms ts)"
| "flit_of_hlit (Neg p ts) = Neg p (fterms_of_hterms ts)"

fun hlit_of_flit :: "fterm literal \<Rightarrow> hterm literal" where
  "hlit_of_flit (Pos p ts) = Pos p (hterms_of_fterms ts)"
| "hlit_of_flit (Neg p ts) = Neg p (hterms_of_fterms ts)"

lemma ground_flit_of_hlit: "ground\<^sub>l (flit_of_hlit l)" 
  by  (induction l)  (simp add: ground_fterms_of_hterms)+

theorem hlit_of_flit_flit_of_hlit [simp]: "hlit_of_flit (flit_of_hlit l) =  l" by (cases l) auto

theorem flit_of_hlit_hlit_of_flit [simp]:
  assumes "ground\<^sub>l l"
  shows "flit_of_hlit (hlit_of_flit l) = l"
  using assms by (cases l) auto

lemma sign_flit_of_hlit: "sign (flit_of_hlit l) = sign l" by (cases l) auto

lemma hlit_of_flit_bij: "bij_betw hlit_of_flit {l. ground\<^sub>l l} UNIV" 
 unfolding bij_betw_def
proof
  show "inj_on hlit_of_flit {l. ground\<^sub>l l}" using inj_on_inverseI flit_of_hlit_hlit_of_flit 
    by (metis (mono_tags, lifting) mem_Collect_eq) 
next 
  have "\<forall>l. \<exists>l'. ground\<^sub>l l' \<and> l = hlit_of_flit l'" 
    using ground_flit_of_hlit hlit_of_flit_flit_of_hlit by metis
  then show "hlit_of_flit ` {l. ground\<^sub>l l} = UNIV" by auto
qed

lemma flit_of_hlit_bij: "bij_betw flit_of_hlit UNIV {l. ground\<^sub>l l}" 
 unfolding bij_betw_def inj_on_def
proof
  show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. flit_of_hlit x = flit_of_hlit y \<longrightarrow> x = y" 
    using ground_flit_of_hlit hlit_of_flit_flit_of_hlit by metis
next
  have "\<forall>l. ground\<^sub>l l \<longrightarrow> (l = flit_of_hlit (hlit_of_flit l))" using hlit_of_flit_flit_of_hlit by auto
  then have "{l. ground\<^sub>l l}  \<subseteq> flit_of_hlit ` UNIV " by blast
  moreover
  have "\<forall>l. ground\<^sub>l (flit_of_hlit l)" using ground_flit_of_hlit by auto
  ultimately show "flit_of_hlit ` UNIV = {l. ground\<^sub>l l}" using hlit_of_flit_flit_of_hlit ground_flit_of_hlit by auto
qed


subsubsection \<open>Conversions - Atoms and Herbrand Atoms\<close>

fun fatom_of_hatom :: "hterm atom \<Rightarrow> fterm atom" where
  "fatom_of_hatom (p, ts) = (p, fterms_of_hterms ts)"

fun hatom_of_fatom :: "fterm atom \<Rightarrow> hterm atom" where
  "hatom_of_fatom (p, ts) = (p, hterms_of_fterms ts)"

lemma ground_fatom_of_hatom: "ground\<^sub>t\<^sub>s (snd (fatom_of_hatom a))" 
  by  (induction a) (simp add: ground_fterms_of_hterms)+

theorem hatom_of_fatom_fatom_of_hatom [simp]: "hatom_of_fatom (fatom_of_hatom l) = l" 
  by (cases l) auto

theorem fatom_of_hatom_hatom_of_fatom [simp]: 
  assumes "ground\<^sub>t\<^sub>s (snd l)"
  shows "fatom_of_hatom (hatom_of_fatom l) = l"
  using assms by (cases l) auto

lemma hatom_of_fatom_bij: "bij_betw hatom_of_fatom ground_fatoms UNIV" 
 unfolding bij_betw_def
proof
  show "inj_on hatom_of_fatom ground_fatoms" using inj_on_inverseI fatom_of_hatom_hatom_of_fatom unfolding ground_fatoms_def 
    by (metis (mono_tags, lifting) mem_Collect_eq) 
next 
  have "\<forall>a. \<exists>a'. ground\<^sub>t\<^sub>s (snd a') \<and> a = hatom_of_fatom a'" 
    using ground_fatom_of_hatom hatom_of_fatom_fatom_of_hatom by metis
  then show "hatom_of_fatom ` ground_fatoms = UNIV" unfolding ground_fatoms_def by blast
qed

lemma fatom_of_hatom_bij: "bij_betw fatom_of_hatom UNIV ground_fatoms" 
 unfolding bij_betw_def inj_on_def
proof
  show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. fatom_of_hatom x = fatom_of_hatom y \<longrightarrow> x = y" 
    using ground_fatom_of_hatom hatom_of_fatom_fatom_of_hatom by metis
next
  have "\<forall>a. ground\<^sub>t\<^sub>s (snd a) \<longrightarrow> (a = fatom_of_hatom (hatom_of_fatom a))" using hatom_of_fatom_fatom_of_hatom by auto
  then have "ground_fatoms  \<subseteq> fatom_of_hatom ` UNIV " unfolding ground_fatoms_def by blast
  moreover
  have "\<forall>l. ground\<^sub>t\<^sub>s (snd (fatom_of_hatom l))" using ground_fatom_of_hatom by auto
  ultimately show "fatom_of_hatom ` UNIV = ground_fatoms" 
    using hatom_of_fatom_fatom_of_hatom ground_fatom_of_hatom unfolding ground_fatoms_def by auto
qed


subsection \<open>Enumerations\<close>


subsubsection \<open>Enumerating Strings\<close>

definition nat_of_string:: "string \<Rightarrow> nat" where
  "nat_of_string \<equiv> (SOME f. bij f)"

definition string_of_nat:: "nat \<Rightarrow> string" where
  "string_of_nat \<equiv> inv nat_of_string"

lemma nat_of_string_bij: "bij nat_of_string"
  proof -
  have "countable (UNIV::string set)" by auto
  moreover
  have "infinite (UNIV::string set)" using infinite_UNIV_listI by auto
  ultimately
  obtain x where "bij (x:: string \<Rightarrow> nat)" using countableE_infinite[of UNIV] by blast
  then show "?thesis" unfolding nat_of_string_def using someI by metis
qed

lemma string_of_nat_bij: "bij string_of_nat" unfolding string_of_nat_def using nat_of_string_bij bij_betw_inv_into by auto

lemma nat_of_string_string_of_nat[simp]: "nat_of_string (string_of_nat n) = n" 
  unfolding string_of_nat_def 
  using nat_of_string_bij f_inv_into_f[of nat_of_string] by simp

lemma string_of_nat_nat_of_string[simp]: "string_of_nat (nat_of_string n) = n" 
  unfolding string_of_nat_def 
  using nat_of_string_bij inv_into_f_f[of nat_of_string] by simp


subsubsection \<open>Enumerating Herbrand Atoms\<close>

definition nat_of_hatom:: "hterm atom \<Rightarrow> nat" where
  "nat_of_hatom \<equiv> (SOME f. bij f)"

definition hatom_of_nat:: "nat \<Rightarrow> hterm atom" where
  "hatom_of_nat \<equiv> inv nat_of_hatom"

instantiation hterm :: countable begin
instance by countable_datatype
end

lemma infinite_hatoms: "infinite (UNIV :: ('t atom) set)"
proof -
  let ?diago = "\<lambda>n. (string_of_nat n,[])"
  let ?undiago = "\<lambda>a. nat_of_string (fst a)"
  have "\<forall>n. ?undiago (?diago n) = n" using nat_of_string_string_of_nat by auto
  moreover
  have "\<forall>n. ?diago n \<in> UNIV" by auto
  ultimately show "infinite (UNIV :: ('t atom) set)" using infinity[of ?undiago ?diago UNIV] by simp
qed

lemma nat_of_hatom_bij: "bij nat_of_hatom"
proof -
  let ?S = "UNIV :: (('t::countable) atom) set"
  have "countable ?S" by auto
  moreover
  have "infinite ?S" using infinite_hatoms by auto
  ultimately
  obtain x where "bij (x :: hterm atom \<Rightarrow> nat)" using countableE_infinite[of ?S] by blast
  then have "bij nat_of_hatom" unfolding nat_of_hatom_def using someI by metis
  then show "?thesis" unfolding bij_betw_def inj_on_def unfolding nat_of_hatom_def by simp
qed

lemma hatom_of_nat_bij: "bij hatom_of_nat" unfolding hatom_of_nat_def using nat_of_hatom_bij bij_betw_inv_into by auto

lemma nat_of_hatom_hatom_of_nat[simp]: "nat_of_hatom (hatom_of_nat n) = n" 
  unfolding hatom_of_nat_def 
  using nat_of_hatom_bij f_inv_into_f[of nat_of_hatom] by simp

lemma hatom_of_nat_nat_of_hatom[simp]: "hatom_of_nat (nat_of_hatom l) = l" 
  unfolding hatom_of_nat_def 
  using nat_of_hatom_bij inv_into_f_f[of nat_of_hatom _ UNIV] by simp


subsubsection \<open>Enumerating Ground Atoms\<close>

definition fatom_of_nat :: "nat \<Rightarrow> fterm atom" where
  "fatom_of_nat = (\<lambda>n. fatom_of_hatom (hatom_of_nat n))"

definition nat_of_fatom :: "fterm atom \<Rightarrow> nat" where
  "nat_of_fatom = (\<lambda>t. nat_of_hatom (hatom_of_fatom t))"

theorem diag_undiag_fatom[simp]: 
  assumes "ground\<^sub>t\<^sub>s ts"
  shows "fatom_of_nat (nat_of_fatom (p,ts)) = (p,ts)"
using assms unfolding fatom_of_nat_def nat_of_fatom_def by auto

theorem undiag_diag_fatom[simp]: "nat_of_fatom (fatom_of_nat n) = n" unfolding fatom_of_nat_def nat_of_fatom_def by auto

lemma fatom_of_nat_bij: "bij_betw fatom_of_nat UNIV ground_fatoms" 
  using hatom_of_nat_bij bij_betw_trans fatom_of_hatom_bij hatom_of_nat_bij unfolding fatom_of_nat_def comp_def by blast

lemma ground_fatom_of_nat: "ground\<^sub>t\<^sub>s (snd (fatom_of_nat x))" unfolding fatom_of_nat_def using ground_fatom_of_hatom by auto

lemma nat_of_fatom_bij: "bij_betw nat_of_fatom ground_fatoms UNIV"
   using nat_of_hatom_bij bij_betw_trans hatom_of_fatom_bij hatom_of_nat_bij unfolding nat_of_fatom_def comp_def by blast

end
