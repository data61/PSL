(* Author: Dmitriy Traytel *)

section \<open>$\Pi$-Extended Regular Expressions\<close>

(*<*)
theory Pi_Regular_Exp
imports Pi_Regular_Set "HOL-Library.List_Lexorder" "HOL-Library.Code_Target_Nat"
  Deriving.Compare_Instances   
begin
(*>*)
subsection \<open>Syntax of regular expressions\<close>

datatype 'a rexp =
  Zero |
  Full |
  One |
  Atom 'a |
  Plus "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)" |
  Not "('a rexp)" |
  Inter "('a rexp)" "('a rexp)" |
  Pr "('a rexp)"
derive linorder rexp

text \<open>Lifting constructors to lists\<close>

fun rexp_of_list where
  "rexp_of_list OPERATION N [] = N"
| "rexp_of_list OPERATION N [x] = x"
| "rexp_of_list OPERATION N (x # xs) = OPERATION x (rexp_of_list OPERATION N xs)"

abbreviation "PLUS \<equiv> rexp_of_list Plus Zero"
abbreviation "TIMES \<equiv> rexp_of_list Times One"
abbreviation "INTERSECT \<equiv> rexp_of_list Inter Full"

lemma list_singleton_induct [case_names nil single cons]:
  assumes nil: "P []"
  assumes single: "\<And>x. P [x]"
  assumes cons: "\<And>x y xs. P (y # xs) \<Longrightarrow> P (x # (y # xs))"
  shows "P xs"
  using assms
proof (induct xs)
  case (Cons x xs) thus ?case by (cases xs) auto
qed simp


subsection \<open>ACI normalization\<close>

fun toplevel_summands :: "'a rexp \<Rightarrow> 'a rexp set" where
  "toplevel_summands (Plus r s) = toplevel_summands r \<union> toplevel_summands s"
| "toplevel_summands r = {r}"

abbreviation (input) "flatten LISTOP X \<equiv> LISTOP (sorted_list_of_set X)"

lemma toplevel_summands_nonempty[simp]:
  "toplevel_summands r \<noteq> {}"
  by (induct r) auto

lemma toplevel_summands_finite[simp]:
  "finite (toplevel_summands r)"
  by (induct r) auto

primrec ACI_norm :: "('a::linorder) rexp \<Rightarrow> 'a rexp"  ("\<guillemotleft>_\<guillemotright>") where
  "\<guillemotleft>Zero\<guillemotright> = Zero"
| "\<guillemotleft>Full\<guillemotright> = Full"
| "\<guillemotleft>One\<guillemotright> = One"
| "\<guillemotleft>Atom a\<guillemotright> = Atom a"
| "\<guillemotleft>Plus r s\<guillemotright> = flatten PLUS (toplevel_summands (Plus \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>))"
| "\<guillemotleft>Times r s\<guillemotright> = Times \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>"
| "\<guillemotleft>Star r\<guillemotright> = Star \<guillemotleft>r\<guillemotright>"
| "\<guillemotleft>Not r\<guillemotright> = Not \<guillemotleft>r\<guillemotright>"
| "\<guillemotleft>Inter r s\<guillemotright> = Inter \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>"
| "\<guillemotleft>Pr r\<guillemotright> = Pr \<guillemotleft>r\<guillemotright>"

lemma Plus_toplevel_summands:
  "Plus r s \<in> toplevel_summands t \<Longrightarrow> False"
  by (induct t) auto

lemma toplevel_summands_not_Plus[simp]:
  "(\<forall>r s. x \<noteq> Plus r s) \<Longrightarrow> toplevel_summands x = {x}"
  by (induct x) auto

lemma toplevel_summands_PLUS_strong:
  "\<lbrakk>xs \<noteq> []; list_all (\<lambda>x. \<not>(\<exists>r s. x = Plus r s)) xs\<rbrakk> \<Longrightarrow> toplevel_summands (PLUS xs) = set xs"
  by (induct xs rule: list_singleton_induct) auto

lemma toplevel_summands_flatten:
  "\<lbrakk>X \<noteq> {}; finite X; \<forall>x \<in> X. \<not>(\<exists>r s. x = Plus r s)\<rbrakk> \<Longrightarrow> toplevel_summands (flatten PLUS X) = X"
  using toplevel_summands_PLUS_strong[of "sorted_list_of_set X"]
  unfolding list_all_iff by fastforce

lemma ACI_norm_Plus:
  "\<guillemotleft>r\<guillemotright> = Plus s t \<Longrightarrow> \<exists>s t. r = Plus s t"
  by (induct r) auto

lemma toplevel_summands_flatten_ACI_norm_image:
  "toplevel_summands (flatten PLUS (ACI_norm ` toplevel_summands r)) = ACI_norm ` toplevel_summands r"
  by (intro toplevel_summands_flatten) (auto dest!: ACI_norm_Plus intro: Plus_toplevel_summands)

lemma toplevel_summands_flatten_ACI_norm_image_Union:
  "toplevel_summands (flatten PLUS (ACI_norm ` toplevel_summands r \<union> ACI_norm ` toplevel_summands s)) =
    ACI_norm ` toplevel_summands r \<union> ACI_norm ` toplevel_summands s"
  by (intro toplevel_summands_flatten) (auto dest!: ACI_norm_Plus[OF sym] intro: Plus_toplevel_summands)

lemma toplevel_summands_ACI_norm:
  "toplevel_summands \<guillemotleft>r\<guillemotright> = ACI_norm ` toplevel_summands r"
  by (induct r) (auto simp: toplevel_summands_flatten_ACI_norm_image_Union)

lemma ACI_norm_flatten:
  "\<guillemotleft>r\<guillemotright> = flatten PLUS (ACI_norm ` toplevel_summands r)"
  by (induct r) (auto simp: image_Un toplevel_summands_flatten_ACI_norm_image)

theorem ACI_norm_idem[simp]:
  "\<guillemotleft>\<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>r\<guillemotright>"
proof (induct r)
  case (Plus r s)
  have "\<guillemotleft>\<guillemotleft>Plus r s\<guillemotright>\<guillemotright> = \<guillemotleft>flatten PLUS (toplevel_summands \<guillemotleft>r\<guillemotright> \<union> toplevel_summands \<guillemotleft>s\<guillemotright>)\<guillemotright>"
    (is "_ = \<guillemotleft>flatten PLUS ?U\<guillemotright>") by simp
  also have "\<dots> = flatten PLUS (ACI_norm ` toplevel_summands (flatten PLUS ?U))"
    by (simp only: ACI_norm_flatten)
  also have "toplevel_summands (flatten PLUS ?U) = ?U"
    by (intro toplevel_summands_flatten) (auto intro: Plus_toplevel_summands)
  also have "flatten PLUS (ACI_norm ` ?U) = flatten PLUS (toplevel_summands \<guillemotleft>r\<guillemotright> \<union> toplevel_summands \<guillemotleft>s\<guillemotright>)"
    by (simp only: image_Un toplevel_summands_ACI_norm[symmetric] Plus)
  finally show ?case by simp
qed auto

fun ACI_nPlus :: "'a::linorder rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "ACI_nPlus (Plus r1 r2) s = ACI_nPlus r1 (ACI_nPlus r2 s)"
| "ACI_nPlus r (Plus s1 s2) =
  (if r = s1 then Plus s1 s2
  else if r < s1 then Plus r (Plus s1 s2)
  else Plus s1 (ACI_nPlus r s2))"
| "ACI_nPlus r s =
  (if r = s then r
  else if r < s then Plus r s
  else Plus s r)"

fun ACI_norm_alt where 
  "ACI_norm_alt Zero = Zero"
| "ACI_norm_alt Full = Full"
| "ACI_norm_alt One = One"
| "ACI_norm_alt (Atom a) = Atom a"
| "ACI_norm_alt (Plus r s) = ACI_nPlus (ACI_norm_alt r) (ACI_norm_alt s)"
| "ACI_norm_alt (Times r s) = Times (ACI_norm_alt r) (ACI_norm_alt s)"
| "ACI_norm_alt (Star r) = Star (ACI_norm_alt r)"
| "ACI_norm_alt (Not r) = Not (ACI_norm_alt r)"
| "ACI_norm_alt (Inter r s) = Inter (ACI_norm_alt r) (ACI_norm_alt s)"
| "ACI_norm_alt (Pr r) = Pr (ACI_norm_alt r)"

lemma toplevel_summands_ACI_nPlus:
  "toplevel_summands (ACI_nPlus r s) = toplevel_summands (Plus r s)"
  by (induct r s rule: ACI_nPlus.induct) auto

lemma toplevel_summands_ACI_norm_alt:
  "toplevel_summands (ACI_norm_alt r) = ACI_norm_alt ` toplevel_summands r"
  by (induct r) (auto simp: toplevel_summands_ACI_nPlus)

lemma ACI_norm_alt_Plus:
  "ACI_norm_alt r = Plus s t \<Longrightarrow> \<exists>s t. r = Plus s t"
  by (induct r) auto

lemma toplevel_summands_flatten_ACI_norm_alt_image:
  "toplevel_summands (flatten PLUS (ACI_norm_alt ` toplevel_summands r)) = ACI_norm_alt ` toplevel_summands r"
  by (intro toplevel_summands_flatten) (auto dest!: ACI_norm_alt_Plus intro: Plus_toplevel_summands)

lemma ACI_norm_ACI_norm_alt: "\<guillemotleft>ACI_norm_alt r\<guillemotright> = \<guillemotleft>r\<guillemotright>"
proof (induction r)
  case (Plus r s) show ?case
    using ACI_norm_flatten [of "ACI_norm_alt (Plus r s)"] ACI_norm_flatten [of "Plus r s"]
    by (auto simp: image_Un toplevel_summands_ACI_nPlus)
      (metis Plus.IH toplevel_summands_ACI_norm)
qed auto

lemma ACI_nPlus_singleton_PLUS: 
  "\<lbrakk>xs \<noteq> []; sorted xs; distinct xs; \<forall>x \<in> {x} \<union> set xs. \<not>(\<exists>r s. x = Plus r s)\<rbrakk> \<Longrightarrow>
  ACI_nPlus x (PLUS xs) = (if x \<in> set xs then PLUS xs else PLUS (insort x xs))"
proof (induct xs rule: list_singleton_induct)
  case (single y)
  thus ?case
    by (cases x y rule: linorder_cases) (induct x y rule: ACI_nPlus.induct, auto)+
next
  case (cons y1 y2 ys) thus ?case by (cases x) (auto)
qed simp

lemma ACI_nPlus_PLUS:
  "\<lbrakk>xs1 \<noteq> []; xs2 \<noteq> []; \<forall>x \<in> set (xs1 @ xs2). \<not>(\<exists>r s. x = Plus r s); sorted xs2; distinct xs2\<rbrakk>\<Longrightarrow>
  ACI_nPlus (PLUS xs1) (PLUS xs2) = flatten PLUS (set (xs1 @ xs2))"
proof (induct xs1 arbitrary: xs2 rule: list_singleton_induct)
  case (single x1) thus ?case
    apply (auto intro!: trans[OF ACI_nPlus_singleton_PLUS] simp: insert_absorb simp del: sorted_list_of_set_insert)
     apply (metis finite_set finite_sorted_distinct_unique sorted_list_of_set)
    apply (metis remdups_id_iff_distinct sorted_list_of_set_sort_remdups sorted_sort_id)
    done
next
  case (cons x11 x12 xs1) thus ?case
    apply (simp del: sorted_list_of_set_insert)
    apply (rule trans[OF ACI_nPlus_singleton_PLUS])
         apply (auto simp del: sorted_list_of_set_insert simp add: insert_commute[of x11])
       apply (auto simp only: Un_insert_left[of x11, symmetric] insert_absorb) []
      apply (auto simp only: Un_insert_right[of _ x11, symmetric] insert_absorb) []
     apply (auto simp add: insert_commute[of x12])
  done
qed simp

lemma ACI_nPlus_flatten_PLUS:
  "\<lbrakk>X1 \<noteq> {}; X2 \<noteq> {}; finite X1; finite X2; \<forall>x \<in> X1 \<union> X2. \<not>(\<exists>r s. x = Plus r s)\<rbrakk>\<Longrightarrow>
  ACI_nPlus (flatten PLUS X1) (flatten PLUS X2) = flatten PLUS (X1 \<union> X2)"
  by (rule trans[OF ACI_nPlus_PLUS]) auto

lemma ACI_nPlus_ACI_norm[simp]: "ACI_nPlus \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright> = \<guillemotleft>Plus r s\<guillemotright>"
  using ACI_norm_flatten [of r] ACI_norm_flatten [of s] ACI_norm_flatten [of "Plus r s"]
  apply (auto intro!: trans [OF ACI_nPlus_flatten_PLUS])
    apply (auto simp: image_Un Un_assoc  intro!: trans [OF ACI_nPlus_flatten_PLUS])
   apply (metis ACI_norm_Plus Plus_toplevel_summands)+
  done

lemma ACI_norm_alt:
  "ACI_norm_alt r = \<guillemotleft>r\<guillemotright>"
  by (induct r) auto

declare ACI_norm_alt[symmetric, code]




subsection \<open>Finality\<close>

primrec final :: "'a rexp \<Rightarrow> bool"
where
  "final Zero = False"
| "final Full = True"
| "final One = True"
| "final (Atom _) = False"
| "final (Plus r s) = (final r \<or> final s)"
| "final (Times r s) = (final r \<and> final s)"
| "final (Star _) = True"
| "final (Not r) = (~ final r)"
| "final (Inter r1 r2) = (final r1 \<and> final r2)"
| "final (Pr r) = final r"

lemma toplevel_summands_final:
  "final s = (\<exists>r\<in>toplevel_summands s. final r)"
  by (induct s) auto

lemma final_PLUS:
  "final (PLUS xs) = (\<exists>r \<in> set xs. final r)"
  by (induct xs rule: list_singleton_induct) auto

theorem ACI_norm_final[simp]:
  "final \<guillemotleft>r\<guillemotright> = final r"
proof (induct r)
  case (Plus r1 r2) thus ?case using toplevel_summands_final by (auto simp: final_PLUS)
qed auto



subsection \<open>Wellformedness w.r.t. an alphabet\<close>

locale alphabet =
fixes \<Sigma> :: "nat \<Rightarrow> 'a set" ("\<Sigma> _")
and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool"
begin

primrec wf :: "nat \<Rightarrow> 'b rexp \<Rightarrow> bool"
where
"wf n Zero = True" |
"wf n Full = True" |
"wf n One = True" |
"wf n (Atom a) = (wf_atom n a)" |
"wf n (Plus r s) = (wf n r \<and> wf n s)" |
"wf n (Times r s) = (wf n r \<and> wf n s)" |
"wf n (Star r) = wf n r" |
"wf n (Not r) = wf n r" |
"wf n (Inter r s) = (wf n r \<and> wf n s)" |
"wf n (Pr r) = wf (n + 1) r"

primrec wf_word where
  "wf_word n [] = True"
| "wf_word n (w # ws) = ((w \<in> \<Sigma> n) \<and> wf_word n ws)"

lemma wf_word_snoc[simp]: "wf_word n (ws @ [w]) = ((w \<in> \<Sigma> n) \<and> wf_word n ws)"
  by (induct ws) auto

lemma wf_word_append[simp]: "wf_word n (ws @ vs) = (wf_word n ws \<and> wf_word n vs)"
  by (induct ws arbitrary: vs) auto

lemma wf_word: "wf_word n w = (w \<in> lists (\<Sigma> n))"
  by (induct w) auto

lemma toplevel_summands_wf:
  "wf n s = (\<forall>r\<in>toplevel_summands s. wf n r)"
  by (induct s) auto

lemma wf_PLUS[simp]:
  "wf n (PLUS xs) = (\<forall>r \<in> set xs. wf n r)"
  by (induct xs rule: list_singleton_induct) auto
  
lemma wf_TIMES[simp]:
  "wf n (TIMES xs) = (\<forall>r \<in> set xs. wf n r)"
  by (induct xs rule: list_singleton_induct) auto

lemma wf_flatten_PLUS[simp]:
  "finite X \<Longrightarrow> wf n (flatten PLUS X) = (\<forall>r \<in> X. wf n r)"
  using wf_PLUS[of n "sorted_list_of_set X"] by fastforce

theorem ACI_norm_wf[simp]:
  "wf n \<guillemotleft>r\<guillemotright> = wf n r"
proof (induct r arbitrary: n)
  case (Plus r1 r2) thus ?case
   using toplevel_summands_wf[of n "\<guillemotleft>r1\<guillemotright>"] toplevel_summands_wf[of n "\<guillemotleft>r2\<guillemotright>"] by auto
qed auto

lemma wf_INTERSECT[simp]:
  "wf n (INTERSECT xs) = (\<forall>r \<in> set xs. wf n r)"
  by (induct xs rule: list_singleton_induct) auto

lemma wf_flatten_INTERSECT[simp]:
  "finite X \<Longrightarrow> wf n (flatten INTERSECT X) = (\<forall>r \<in> X. wf n r)"
  using wf_INTERSECT[of n "sorted_list_of_set X"] by fastforce

end



subsection \<open>Language\<close>

locale project =
  alphabet \<Sigma> wf_atom for \<Sigma> :: "nat \<Rightarrow> 'a set" and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool" +
fixes project :: "'a \<Rightarrow> 'a"
and lookup :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
assumes project: "\<And>a. a \<in> \<Sigma> (Suc n) \<Longrightarrow> project a \<in> \<Sigma> n"
begin

primrec lang :: "nat \<Rightarrow> 'b rexp => 'a lang" where
"lang n Zero = {}" |
"lang n Full = lists (\<Sigma> n)" |
"lang n One = {[]}" |
"lang n (Atom b) = {[x] | x. lookup b x \<and> x \<in> \<Sigma> n}" |
"lang n (Plus r s) = (lang n r) \<union> (lang n s)" |
"lang n (Times r s) = conc (lang n r) (lang n s)" |
"lang n (Star r) = star (lang n r)" |
"lang n (Not r) = lists (\<Sigma> n) - lang n r" |
"lang n (Inter r s) = (lang n r \<inter> lang n s)" |
"lang n (Pr r) = map project ` lang (n + 1) r"

lemma wf_word_map_project[simp]: "wf_word (Suc n) ws \<Longrightarrow> wf_word n (map project ws)"
  by (induct ws arbitrary: n) (auto intro: project)

lemma wf_lang_wf_word: "wf n r \<Longrightarrow> \<forall>w \<in> lang n r. wf_word n w"
  by (induct r arbitrary: n) (auto elim: rev_subsetD[OF _ conc_mono] star_induct intro: iffD2[OF wf_word])

lemma lang_subset_lists: "wf n r \<Longrightarrow> lang n r \<subseteq> lists (\<Sigma> n)"
proof (induct r arbitrary: n)
  case Pr thus ?case by (fastforce intro!: project)
qed (auto simp: conc_subset_lists star_subset_lists)

lemma toplevel_summands_lang:
  "r \<in> toplevel_summands s \<Longrightarrow> lang n r \<subseteq> lang n s"
  by (induct s) auto

lemma toplevel_summands_lang_UN:
  "lang n s = (\<Union>r\<in>toplevel_summands s. lang n r)"
  by (induct s) auto

lemma toplevel_summands_in_lang:
  "w \<in> lang n s = (\<exists>r\<in>toplevel_summands s. w \<in> lang n r)"
  by (induct s) auto

lemma lang_PLUS[simp]:
  "lang n (PLUS xs) = (\<Union>r \<in> set xs. lang n r)"
  by (induct xs rule: list_singleton_induct) auto
  
lemma lang_TIMES[simp]:
  "lang n (TIMES xs) = foldr (@@) (map (lang n) xs) {[]}"
  by (induct xs rule: list_singleton_induct) auto

lemma lang_flatten_PLUS:
  "finite X \<Longrightarrow> lang n (flatten PLUS X) = (\<Union>r \<in> X. lang n r)"
  using lang_PLUS[of n "sorted_list_of_set X"] by fastforce

theorem ACI_norm_lang[simp]:
  "lang n \<guillemotleft>r\<guillemotright> = lang n r"
proof (induct r arbitrary: n)
  case (Plus r1 r2)
  moreover
  from Plus[symmetric] have "lang n (Plus r1 r2) \<subseteq> lang n \<guillemotleft>Plus r1 r2\<guillemotright>"
    using toplevel_summands_in_lang[of _ n "\<guillemotleft>r1\<guillemotright>"] toplevel_summands_in_lang[of _ n "\<guillemotleft>r2\<guillemotright>"]
    by auto
  ultimately show ?case by (fastforce dest!: toplevel_summands_lang)
qed auto

lemma lang_final: "final r = ([] \<in> lang n r)"
  using concI[of "[]" _ "[]"] by (induct r arbitrary: n) auto

lemma in_lang_INTERSECT:
  "wf_word n w \<Longrightarrow> w \<in> lang n (INTERSECT xs) = (\<forall>r \<in> set xs. w \<in> lang n r)"
  by (induct xs rule: list_singleton_induct) (auto simp: wf_word)
  
lemma lang_INTERSECT:
  "lang n (INTERSECT xs) = (if xs = [] then lists (\<Sigma> n) else \<Inter>r \<in> set xs. lang n r)"
  by (induct xs rule: list_singleton_induct) auto

lemma lang_flatten_INTERSECT[simp]:
  assumes "finite X" "X \<noteq> {}" "\<forall>r\<in>X. wf n r"
  shows "w \<in> lang n (flatten INTERSECT X) = (\<forall>r \<in> X. w \<in> lang n r)" (is "?L = ?R")
proof
  assume ?L
  thus ?R using in_lang_INTERSECT[OF bspec[OF wf_lang_wf_word[OF iffD2[OF wf_flatten_INTERSECT]]],
    OF assms(1,3) \<open>?L\<close>, of "sorted_list_of_set X"] assms(1)
    by auto
next
  assume ?R
  with assms show ?L by (intro iffD2[OF in_lang_INTERSECT]) (auto dest: wf_lang_wf_word)
qed

end

(*<*)
end
(*>*)
