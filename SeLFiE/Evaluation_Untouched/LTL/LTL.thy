(*
    Author:   Salomon Sickert
    Author:   Benedikt Seidl
    Author:   Alexander Schimpf (original entry: CAVA/LTL.thy)
    Author:   Stephan Merz (original entry: Stuttering_Equivalence/PLTL.thy)
    License:  BSD
*)

section \<open>Linear Temporal Logic\<close>

theory LTL
imports
  Main "HOL-Library.Omega_Words_Fun"
begin

text \<open>This theory provides a formalisation of linear temporal logic. It provides three variants:
    \begin{enumerate}
      \item LTL with syntactic sugar. This variant is the semantic reference and the included parser
            generates ASTs of this datatype.
      \item LTL in negation normal form without syntactic sugar. This variant is used by the included
            rewriting engine and is used for the translation to automata (implemented in other entries).
      \item LTL in restricted negation normal form without the rather uncommon operators ``weak until''
            and ``strong release''. It is used by the formalization of Gerth's algorithm.
      \item PLTL. A variant with a reduced set of operators.
    \end{enumerate}
    This theory subsumes (and partly reuses) the existing formalisation found in LTL\_to\_GBA and
    Stuttering\_Equivalence and unifies them.\<close>

subsection \<open>LTL with Syntactic Sugar\<close>

text \<open>In this section, we provide a formulation of LTL with explicit syntactic sugar deeply embedded.
    This formalization serves as a reference semantics.\<close>

subsubsection \<open>Syntax\<close>

datatype (atoms_ltlc: 'a) ltlc =
    True_ltlc                               ("true\<^sub>c")
  | False_ltlc                              ("false\<^sub>c")
  | Prop_ltlc 'a                            ("prop\<^sub>c'(_')")
  | Not_ltlc "'a ltlc"                      ("not\<^sub>c _" [85] 85)
  | And_ltlc "'a ltlc" "'a ltlc"            ("_ and\<^sub>c _" [82,82] 81)
  | Or_ltlc "'a ltlc" "'a ltlc"             ("_ or\<^sub>c _" [81,81] 80)
  | Implies_ltlc "'a ltlc" "'a ltlc"        ("_ implies\<^sub>c _" [81,81] 80)
  | Next_ltlc "'a ltlc"                     ("X\<^sub>c _" [88] 87)
  | Final_ltlc "'a ltlc"                    ("F\<^sub>c _" [88] 87)
  | Global_ltlc "'a ltlc"                   ("G\<^sub>c _" [88] 87)
  | Until_ltlc "'a ltlc" "'a ltlc"          ("_ U\<^sub>c _" [84,84] 83)
  | Release_ltlc "'a ltlc" "'a ltlc"        ("_ R\<^sub>c _" [84,84] 83)
  | WeakUntil_ltlc "'a ltlc" "'a ltlc"      ("_ W\<^sub>c _" [84,84] 83)
  | StrongRelease_ltlc "'a ltlc" "'a ltlc"  ("_ M\<^sub>c _" [84,84] 83)

definition Iff_ltlc ("_ iff\<^sub>c _" [81,81] 80)
where
  "\<phi> iff\<^sub>c \<psi> \<equiv> (\<phi> implies\<^sub>c \<psi>) and\<^sub>c (\<psi> implies\<^sub>c \<phi>)"

subsubsection \<open>Semantics\<close>

primrec semantics_ltlc :: "['a set word, 'a ltlc] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>c _" [80,80] 80)
where
  "\<xi> \<Turnstile>\<^sub>c true\<^sub>c = True"
| "\<xi> \<Turnstile>\<^sub>c false\<^sub>c = False"
| "\<xi> \<Turnstile>\<^sub>c prop\<^sub>c(q) = (q\<in>\<xi> 0)"
| "\<xi> \<Turnstile>\<^sub>c not\<^sub>c \<phi> = (\<not> \<xi> \<Turnstile>\<^sub>c \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c \<phi> and\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<and> \<xi> \<Turnstile>\<^sub>c \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c \<phi> or\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<or> \<xi> \<Turnstile>\<^sub>c \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c \<phi> implies\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<longrightarrow> \<xi> \<Turnstile>\<^sub>c \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c X\<^sub>c \<phi> = (suffix 1 \<xi> \<Turnstile>\<^sub>c \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c F\<^sub>c \<phi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c G\<^sub>c \<phi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c \<phi> U\<^sub>c \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>c \<phi>))"
| "\<xi> \<Turnstile>\<^sub>c \<phi> R\<^sub>c \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>c \<phi>))"
| "\<xi> \<Turnstile>\<^sub>c \<phi> W\<^sub>c \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi> \<or> (\<exists>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>c \<psi>))"
| "\<xi> \<Turnstile>\<^sub>c \<phi> M\<^sub>c \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi> \<and> (\<forall>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>c \<psi>))"

lemma semantics_ltlc_sugar [simp]:
  "\<xi> \<Turnstile>\<^sub>c \<phi> iff\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c \<psi>)"
  "\<xi> \<Turnstile>\<^sub>c F\<^sub>c \<phi> = \<xi> \<Turnstile>\<^sub>c (true\<^sub>c U\<^sub>c \<phi>)"
  "\<xi> \<Turnstile>\<^sub>c G\<^sub>c \<phi> = \<xi> \<Turnstile>\<^sub>c (false\<^sub>c R\<^sub>c \<phi>)"
  by (auto simp add: Iff_ltlc_def)

definition "language_ltlc \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile>\<^sub>c \<phi>}"

lemma language_ltlc_negate[simp]:
  "language_ltlc (not\<^sub>c \<phi>) = - language_ltlc \<phi>"
  unfolding language_ltlc_def by auto

lemma ltl_true_or_con[simp]:
  "\<xi> \<Turnstile>\<^sub>c prop\<^sub>c(p) or\<^sub>c (not\<^sub>c prop\<^sub>c(p))"
  by auto

lemma ltl_false_true_con[simp]:
  "\<xi> \<Turnstile>\<^sub>c not\<^sub>c true\<^sub>c \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c false\<^sub>c"
  by auto

lemma ltl_Next_Neg_con[simp]:
  "\<xi> \<Turnstile>\<^sub>c X\<^sub>c (not\<^sub>c \<phi>) \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c not\<^sub>c X\<^sub>c \<phi>"
  by auto

\<comment> \<open>The connection between dual operators\<close>

lemma ltl_Until_Release_con:
  "\<xi> \<Turnstile>\<^sub>c \<phi> R\<^sub>c \<psi> \<longleftrightarrow> (\<not> \<xi> \<Turnstile>\<^sub>c (not\<^sub>c \<phi>) U\<^sub>c (not\<^sub>c \<psi>))"
  "\<xi> \<Turnstile>\<^sub>c \<phi> U\<^sub>c \<psi> \<longleftrightarrow> (\<not> \<xi> \<Turnstile>\<^sub>c (not\<^sub>c \<phi>) R\<^sub>c (not\<^sub>c \<psi>))"
  by auto

lemma ltl_WeakUntil_StrongRelease_con:
  "\<xi> \<Turnstile>\<^sub>c \<phi> W\<^sub>c \<psi> \<longleftrightarrow> (\<not> \<xi> \<Turnstile>\<^sub>c (not\<^sub>c \<phi>) M\<^sub>c (not\<^sub>c \<psi>))"
  "\<xi> \<Turnstile>\<^sub>c \<phi> M\<^sub>c \<psi> \<longleftrightarrow> (\<not> \<xi> \<Turnstile>\<^sub>c (not\<^sub>c \<phi>) W\<^sub>c (not\<^sub>c \<psi>))"
  by auto

\<comment> \<open>The connection between weak and strong operators\<close>

lemma ltl_Release_StrongRelease_con:
  "\<xi> \<Turnstile>\<^sub>c \<phi> R\<^sub>c \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c (\<phi> M\<^sub>c \<psi>) or\<^sub>c (G\<^sub>c \<psi>)"
  "\<xi> \<Turnstile>\<^sub>c \<phi> M\<^sub>c \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c (\<phi> R\<^sub>c \<psi>) and\<^sub>c (F\<^sub>c \<phi>)"
proof safe
  assume asm: "\<xi> \<Turnstile>\<^sub>c \<phi> R\<^sub>c \<psi>"

  show "\<xi> \<Turnstile>\<^sub>c (\<phi> M\<^sub>c \<psi>) or\<^sub>c (G\<^sub>c \<psi>)"
  proof (cases "\<xi> \<Turnstile>\<^sub>c G\<^sub>c \<psi>")
    case False

    then obtain i where "\<not> suffix i \<xi> \<Turnstile>\<^sub>c \<psi>" and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>c \<psi>"
      using exists_least_iff[of "\<lambda>i. \<not> suffix i \<xi> \<Turnstile>\<^sub>c \<psi>"] by force

    then show ?thesis
      using asm by force
  qed simp
next
  assume asm: "\<xi> \<Turnstile>\<^sub>c (\<phi> R\<^sub>c \<psi>) and\<^sub>c (F\<^sub>c \<phi>)"

  then show "\<xi> \<Turnstile>\<^sub>c \<phi> M\<^sub>c \<psi>"
  proof (cases "\<xi> \<Turnstile>\<^sub>c F\<^sub>c \<phi>")
    case True

    then obtain i where "suffix i \<xi> \<Turnstile>\<^sub>c \<phi>" and "\<forall>j<i. \<not> suffix j \<xi> \<Turnstile>\<^sub>c \<phi>"
      using exists_least_iff[of "\<lambda>i. suffix i \<xi> \<Turnstile>\<^sub>c \<phi>"] by force

    then show ?thesis
      using asm by force
  qed simp
qed (unfold semantics_ltlc.simps; insert not_less, blast)+

lemma ltl_Until_WeakUntil_con:
  "\<xi> \<Turnstile>\<^sub>c \<phi> U\<^sub>c \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c (\<phi> W\<^sub>c \<psi>) and\<^sub>c (F\<^sub>c \<psi>)"
  "\<xi> \<Turnstile>\<^sub>c \<phi> W\<^sub>c \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c (\<phi> U\<^sub>c \<psi>) or\<^sub>c (G\<^sub>c \<phi>)"
proof safe
  assume asm: "\<xi> \<Turnstile>\<^sub>c (\<phi> W\<^sub>c \<psi>) and\<^sub>c (F\<^sub>c \<psi>)"

  then show "\<xi> \<Turnstile>\<^sub>c \<phi> U\<^sub>c \<psi>"
  proof (cases "\<xi> \<Turnstile>\<^sub>c F\<^sub>c \<psi>")
    case True

    then obtain i where "suffix i \<xi> \<Turnstile>\<^sub>c \<psi>" and "\<forall>j<i. \<not> suffix j \<xi> \<Turnstile>\<^sub>c \<psi>"
      using exists_least_iff[of "\<lambda>i. suffix i \<xi> \<Turnstile>\<^sub>c \<psi>"] by force

    then show ?thesis
      using asm by force
  qed simp
next
  assume asm: "\<xi> \<Turnstile>\<^sub>c \<phi> W\<^sub>c \<psi>"

  then show "\<xi> \<Turnstile>\<^sub>c (\<phi> U\<^sub>c \<psi>) or\<^sub>c (G\<^sub>c \<phi>)"
  proof (cases "\<xi> \<Turnstile>\<^sub>c G\<^sub>c \<phi>")
    case False

    then obtain i where "\<not> suffix i \<xi> \<Turnstile>\<^sub>c \<phi>" and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>c \<phi>"
      using exists_least_iff[of "\<lambda>i. \<not> suffix i \<xi> \<Turnstile>\<^sub>c \<phi>"] by force

    then show ?thesis
      using asm by force
  qed simp
qed (unfold semantics_ltlc.simps; insert not_less, blast)+

lemma ltl_StrongRelease_Until_con:
  "\<xi> \<Turnstile>\<^sub>c \<phi> M\<^sub>c \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c \<psi> U\<^sub>c (\<phi> and\<^sub>c \<psi>)"
  using order.order_iff_strict by auto

lemma ltl_WeakUntil_Release_con:
  "\<xi> \<Turnstile>\<^sub>c \<phi> R\<^sub>c \<psi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c \<psi> W\<^sub>c (\<phi> and\<^sub>c \<psi>)"
  by (meson ltl_Release_StrongRelease_con(1) ltl_StrongRelease_Until_con ltl_Until_WeakUntil_con(2) semantics_ltlc.simps(6))


definition "pw_eq_on S w w' \<equiv> \<forall>i. w i \<inter> S = w' i \<inter> S"

lemma pw_eq_on_refl[simp]: "pw_eq_on S w w"
  and pw_eq_on_sym: "pw_eq_on S w w' \<Longrightarrow> pw_eq_on S w' w"
  and pw_eq_on_trans[trans]: "\<lbrakk>pw_eq_on S w w'; pw_eq_on S w' w''\<rbrakk> \<Longrightarrow> pw_eq_on S w w''"
  unfolding pw_eq_on_def by auto

lemma pw_eq_on_suffix:
  "pw_eq_on S w w' \<Longrightarrow> pw_eq_on S (suffix k w) (suffix k w')"
  by (simp add: pw_eq_on_def)

lemma pw_eq_on_subset:
  "S \<subseteq> S' \<Longrightarrow> pw_eq_on S' w w' \<Longrightarrow> pw_eq_on S w w'"
  by (auto simp add: pw_eq_on_def)

lemma ltlc_eq_on_aux:
  "pw_eq_on (atoms_ltlc \<phi>) w w' \<Longrightarrow> w \<Turnstile>\<^sub>c \<phi> \<Longrightarrow> w' \<Turnstile>\<^sub>c \<phi>"
proof (induction \<phi> arbitrary: w w')
  case Until_ltlc
  thus ?case
    by simp (meson Un_upper1 Un_upper2 pw_eq_on_subset pw_eq_on_suffix)
next
  case Release_ltlc
  thus ?case
    by simp (metis Un_upper1 pw_eq_on_subset pw_eq_on_suffix sup_commute)
next
  case WeakUntil_ltlc
  thus ?case
    by simp (meson pw_eq_on_subset pw_eq_on_suffix sup.cobounded1 sup_ge2)
next
  case StrongRelease_ltlc
  thus ?case
    by simp (metis Un_upper1 pw_eq_on_subset pw_eq_on_suffix pw_eq_on_sym sup_ge2)
next
  case (And_ltlc \<phi> \<psi>)
  thus ?case
    by simp (meson Un_upper1 inf_sup_ord(4) pw_eq_on_subset)
next
  case (Or_ltlc \<phi> \<psi>)
  thus ?case
    by simp (meson Un_upper2 pw_eq_on_subset sup_ge1)
next
  case (Implies_ltlc \<phi> \<psi>)
  thus ?case
    by simp (meson Un_upper1 Un_upper2 pw_eq_on_subset[of "atoms_ltlc _" "atoms_ltlc \<phi> \<union> atoms_ltlc \<psi>"]  pw_eq_on_sym)
qed (auto simp add: pw_eq_on_def; metis suffix_nth)+

lemma ltlc_eq_on:
  "pw_eq_on (atoms_ltlc \<phi>) w w' \<Longrightarrow> w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> w' \<Turnstile>\<^sub>c \<phi>"
  using ltlc_eq_on_aux pw_eq_on_sym by blast

lemma suffix_comp: "(\<lambda>i. f (suffix k w i)) = suffix k (f o w)"
  by auto

lemma suffix_range: "\<Union>(range \<xi>) \<subseteq> APs \<Longrightarrow> \<Union>(range (suffix k \<xi>)) \<subseteq> APs"
    by auto

lemma map_semantics_ltlc_aux:
  assumes "inj_on f APs"
  assumes "\<Union>(range w) \<subseteq> APs"
  assumes "atoms_ltlc \<phi> \<subseteq> APs"
  shows "w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> (\<lambda>i. f ` w i) \<Turnstile>\<^sub>c map_ltlc f \<phi>"
  using assms(2,3)
proof (induction \<phi> arbitrary: w)
  case (Prop_ltlc x)
    thus ?case   using assms(1)
      by (simp add: SUP_le_iff inj_on_image_mem_iff)
next
  case (Next_ltlc \<phi>)
    show ?case
      using Next_ltlc(1)[of "suffix 1 w", unfolded suffix_comp comp_def] Next_ltlc(2,3) apply simp
        by (metis Next_ltlc.prems(1) One_nat_def \<open>\<lbrakk>\<Union>(range (suffix 1 w)) \<subseteq> APs; atoms_ltlc \<phi> \<subseteq> APs\<rbrakk> \<Longrightarrow> suffix 1 w \<Turnstile>\<^sub>c \<phi> = suffix 1 (\<lambda>x. f ` w x) \<Turnstile>\<^sub>c map_ltlc f \<phi>\<close> suffix_range)
next
  case (Final_ltlc \<phi>)
    thus ?case
       using Final_ltlc(1)[of "suffix _ _", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
next
  case (Global_ltlc)
    thus ?case
      using Global_ltlc(1)[of "suffix _ w", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
next
  case (Until_ltlc)
    thus ?case
      using Until_ltlc(1,2)[of "suffix _ w", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
next
  case (Release_ltlc)
    thus ?case
      using Release_ltlc(1,2)[of "suffix _ w", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
next
  case (WeakUntil_ltlc)
    thus ?case
      using WeakUntil_ltlc(1,2)[of "suffix _ w", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
next
  case (StrongRelease_ltlc)
    thus ?case
      using StrongRelease_ltlc(1,2)[of "suffix _ w", unfolded suffix_comp comp_def, OF suffix_range] by fastforce
qed simp+

definition "map_props f APs \<equiv> {i. \<exists>p\<in>APs. f p = Some i}"

lemma map_semantics_ltlc:
  assumes INJ: "inj_on f (dom f)" and DOM: "atoms_ltlc \<phi> \<subseteq> dom f"
  shows "\<xi> \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> (map_props f o \<xi>) \<Turnstile>\<^sub>c map_ltlc (the o f) \<phi>"
proof -
  let ?\<xi>r = "\<lambda>i. \<xi> i \<inter> atoms_ltlc \<phi>"
  let ?\<xi>r' = "\<lambda>i. \<xi> i \<inter> dom f"

  have 1: "\<Union>(range ?\<xi>r) \<subseteq> atoms_ltlc \<phi>" by auto

  have INJ_the_dom: "inj_on (the o f) (dom f)"
    using assms
    by (auto simp: inj_on_def domIff)
  note 2 = subset_inj_on[OF this DOM]

  have 3: "(\<lambda>i. (the o f) ` ?\<xi>r' i) = map_props f o \<xi>" using DOM INJ
    apply (auto intro!: ext simp: map_props_def domIff image_iff)
    by (metis Int_iff domI option.sel)

  have "\<xi> \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> ?\<xi>r \<Turnstile>\<^sub>c \<phi>"
    apply (rule ltlc_eq_on)
    apply (auto simp: pw_eq_on_def)
    done
  also from map_semantics_ltlc_aux[OF 2 1 subset_refl]
  have "\<dots> \<longleftrightarrow> (\<lambda>i. (the o f) ` ?\<xi>r i) \<Turnstile>\<^sub>c map_ltlc (the o f) \<phi>" .
  also have "\<dots> \<longleftrightarrow> (\<lambda>i. (the o f) ` ?\<xi>r' i) \<Turnstile>\<^sub>c map_ltlc (the o f) \<phi>"
    apply (rule ltlc_eq_on) using DOM INJ
    apply (auto simp: pw_eq_on_def ltlc.set_map domIff image_iff)
    by (metis Int_iff contra_subsetD domD domI inj_on_eq_iff option.sel)
  also note 3
  finally show ?thesis .
qed

lemma map_semantics_ltlc_inv:
  assumes INJ: "inj_on f (dom f)" and DOM: "atoms_ltlc \<phi> \<subseteq> dom f"
  shows "\<xi> \<Turnstile>\<^sub>c map_ltlc (the o f) \<phi> \<longleftrightarrow> (\<lambda>i. (the o f) -` \<xi> i) \<Turnstile>\<^sub>c \<phi>"
  using map_semantics_ltlc[OF assms]
  apply simp
  apply (intro ltlc_eq_on)
  apply (auto simp add: pw_eq_on_def ltlc.set_map map_props_def)
  by (metis DOM comp_apply contra_subsetD domD option.sel vimage_eq)




subsection \<open>LTL in Negation Normal Form\<close>

text \<open>We define a type of LTL formula in negation normal form (NNF).\<close>

subsubsection \<open>Syntax\<close>

datatype (atoms_ltln: 'a) ltln  =
    True_ltln                               ("true\<^sub>n")
  | False_ltln                              ("false\<^sub>n")
  | Prop_ltln 'a                            ("prop\<^sub>n'(_')")
  | Nprop_ltln 'a                           ("nprop\<^sub>n'(_')")
  | And_ltln "'a ltln" "'a ltln"            ("_ and\<^sub>n _" [82,82] 81)
  | Or_ltln "'a ltln" "'a ltln"             ("_ or\<^sub>n _" [84,84] 83)
  | Next_ltln "'a ltln"                     ("X\<^sub>n _" [88] 87)
  | Until_ltln "'a ltln" "'a ltln"          ("_ U\<^sub>n _" [84,84] 83)
  | Release_ltln "'a ltln" "'a ltln"        ("_ R\<^sub>n _" [84,84] 83)
  | WeakUntil_ltln "'a ltln" "'a ltln"      ("_ W\<^sub>n _" [84,84] 83)
  | StrongRelease_ltln "'a ltln" "'a ltln"  ("_ M\<^sub>n _" [84,84] 83)

abbreviation finally\<^sub>n :: "'a ltln \<Rightarrow> 'a ltln" ("F\<^sub>n _" [88] 87)
where
  "F\<^sub>n \<phi> \<equiv> true\<^sub>n U\<^sub>n \<phi>"

notation (input) finally\<^sub>n ("\<diamondsuit>\<^sub>n _" [88] 87)

abbreviation globally\<^sub>n :: "'a ltln \<Rightarrow> 'a ltln" ("G\<^sub>n _" [88] 87)
where
  "G\<^sub>n \<phi> \<equiv> false\<^sub>n R\<^sub>n \<phi>"

notation (input) globally\<^sub>n ("\<box>\<^sub>n _" [88] 87)

subsubsection \<open>Semantics\<close>

primrec semantics_ltln :: "['a set word, 'a ltln] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>n _" [80,80] 80)
where
  "\<xi> \<Turnstile>\<^sub>n true\<^sub>n = True"
| "\<xi> \<Turnstile>\<^sub>n false\<^sub>n = False"
| "\<xi> \<Turnstile>\<^sub>n prop\<^sub>n(q) = (q \<in> \<xi> 0)"
| "\<xi> \<Turnstile>\<^sub>n nprop\<^sub>n(q) = (q \<notin> \<xi> 0)"
| "\<xi> \<Turnstile>\<^sub>n \<phi> and\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<phi> \<and> \<xi> \<Turnstile>\<^sub>n \<psi>)"
| "\<xi> \<Turnstile>\<^sub>n \<phi> or\<^sub>n \<psi> = (\<xi> \<Turnstile>\<^sub>n \<phi> \<or> \<xi> \<Turnstile>\<^sub>n \<psi>)"
| "\<xi> \<Turnstile>\<^sub>n X\<^sub>n \<phi> = (suffix 1 \<xi> \<Turnstile>\<^sub>n \<phi>)"
| "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>))"
| "\<xi> \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>n \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>))"
| "\<xi> \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>n \<phi> \<or> (\<exists>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>n \<psi>))"
| "\<xi> \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>n \<phi> \<and> (\<forall>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>n \<psi>))"

definition "language_ltln \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile>\<^sub>n \<phi>}"

lemma semantics_ltln_ite_simps[simp]:
  "w \<Turnstile>\<^sub>n (if P then true\<^sub>n else false\<^sub>n) = P"
  "w \<Turnstile>\<^sub>n (if P then false\<^sub>n else true\<^sub>n) = (\<not>P)"
  by simp_all

subsubsection \<open>Conversion\<close>

fun ltlc_to_ltln' :: "bool \<Rightarrow> 'a ltlc \<Rightarrow> 'a ltln"
where
  "ltlc_to_ltln' False true\<^sub>c = true\<^sub>n"
| "ltlc_to_ltln' False false\<^sub>c = false\<^sub>n"
| "ltlc_to_ltln' False prop\<^sub>c(q) = prop\<^sub>n(q)"
| "ltlc_to_ltln' False (\<phi> and\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) and\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (\<phi> or\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) or\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (\<phi> implies\<^sub>c \<psi>) = (ltlc_to_ltln' True \<phi>) or\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (F\<^sub>c \<phi>) = true\<^sub>n U\<^sub>n (ltlc_to_ltln' False \<phi>)"
| "ltlc_to_ltln' False (G\<^sub>c \<phi>) = false\<^sub>n R\<^sub>n (ltlc_to_ltln' False \<phi>)"
| "ltlc_to_ltln' False (\<phi> U\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) U\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (\<phi> R\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) R\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (\<phi> W\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) W\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' False (\<phi> M\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) M\<^sub>n (ltlc_to_ltln' False \<psi>)"
| "ltlc_to_ltln' True true\<^sub>c = false\<^sub>n"
| "ltlc_to_ltln' True false\<^sub>c = true\<^sub>n"
| "ltlc_to_ltln' True prop\<^sub>c(q) = nprop\<^sub>n(q)"
| "ltlc_to_ltln' True (\<phi> and\<^sub>c \<psi>) = (ltlc_to_ltln' True \<phi>) or\<^sub>n (ltlc_to_ltln' True \<psi>)"
| "ltlc_to_ltln' True (\<phi> or\<^sub>c \<psi>) = (ltlc_to_ltln' True \<phi>) and\<^sub>n (ltlc_to_ltln' True \<psi>)"
| "ltlc_to_ltln' True (\<phi> implies\<^sub>c \<psi>) = (ltlc_to_ltln' False \<phi>) and\<^sub>n (ltlc_to_ltln' True \<psi>)"
| "ltlc_to_ltln' True (F\<^sub>c \<phi>) = false\<^sub>n R\<^sub>n (ltlc_to_ltln' True \<phi>)"
| "ltlc_to_ltln' True (G\<^sub>c \<phi>) = true\<^sub>n U\<^sub>n (ltlc_to_ltln' True \<phi>)"
| "ltlc_to_ltln' True (\<phi> U\<^sub>c \<psi>) = (ltlc_to_ltln' True \<phi>) R\<^sub>n (ltlc_to_ltln' True \<psi>)"
| "ltlc_to_ltln' True (\<phi> R\<^sub>c \<psi>) = (ltlc_to_ltln' True \<phi>) U\<^sub>n (ltlc_to_ltln' True \<psi>)"
| "ltlc_to_ltln' True (\<phi> W\<^sub>c \<psi>) = (ltlc_to_ltln' True \<phi>) M\<^sub>n (ltlc_to_ltln' True \<psi>)"
| "ltlc_to_ltln' True (\<phi> M\<^sub>c \<psi>) = (ltlc_to_ltln' True \<phi>) W\<^sub>n (ltlc_to_ltln' True \<psi>)"
| "ltlc_to_ltln' b (not\<^sub>c \<phi>) = ltlc_to_ltln' (\<not> b) \<phi>"
| "ltlc_to_ltln' b (X\<^sub>c \<phi>) = X\<^sub>n (ltlc_to_ltln' b \<phi>)"

fun ltlc_to_ltln :: "'a ltlc \<Rightarrow> 'a ltln"
where
  "ltlc_to_ltln \<phi> = ltlc_to_ltln' False \<phi>"

fun ltln_to_ltlc :: "'a ltln \<Rightarrow> 'a ltlc"
where
  "ltln_to_ltlc true\<^sub>n = true\<^sub>c"
| "ltln_to_ltlc false\<^sub>n = false\<^sub>c"
| "ltln_to_ltlc prop\<^sub>n(q) = prop\<^sub>c(q)"
| "ltln_to_ltlc nprop\<^sub>n(q) = not\<^sub>c (prop\<^sub>c(q))"
| "ltln_to_ltlc (\<phi> and\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> and\<^sub>c ltln_to_ltlc \<psi>)"
| "ltln_to_ltlc (\<phi> or\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> or\<^sub>c ltln_to_ltlc \<psi>)"
| "ltln_to_ltlc (X\<^sub>n \<phi>) = (X\<^sub>c ltln_to_ltlc \<phi>)"
| "ltln_to_ltlc (\<phi> U\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> U\<^sub>c ltln_to_ltlc \<psi>)"
| "ltln_to_ltlc (\<phi> R\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> R\<^sub>c ltln_to_ltlc \<psi>)"
| "ltln_to_ltlc (\<phi> W\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> W\<^sub>c ltln_to_ltlc \<psi>)"
| "ltln_to_ltlc (\<phi> M\<^sub>n \<psi>) = (ltln_to_ltlc \<phi> M\<^sub>c ltln_to_ltlc \<psi>)"

lemma ltlc_to_ltln'_correct:
  "w \<Turnstile>\<^sub>n (ltlc_to_ltln' True \<phi>) \<longleftrightarrow> \<not> w \<Turnstile>\<^sub>c \<phi>"
  "w \<Turnstile>\<^sub>n (ltlc_to_ltln' False \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>c \<phi>"
  "size (ltlc_to_ltln' True \<phi>) \<le> 2 * size \<phi>"
  "size (ltlc_to_ltln' False \<phi>) \<le> 2 * size \<phi>"
  by (induction \<phi> arbitrary: w) simp+

lemma ltlc_to_ltln_semantics [simp]:
  "w \<Turnstile>\<^sub>n ltlc_to_ltln \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>c \<phi>"
  using ltlc_to_ltln'_correct by auto

lemma ltlc_to_ltln_size:
  "size (ltlc_to_ltln \<phi>) \<le> 2 * size \<phi>"
  using ltlc_to_ltln'_correct by simp

lemma ltln_to_ltlc_semantics [simp]:
  "w \<Turnstile>\<^sub>c ltln_to_ltlc \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (induction \<phi> arbitrary: w) simp+

lemma ltlc_to_ltln_atoms:
  "atoms_ltln (ltlc_to_ltln \<phi>) = atoms_ltlc \<phi>"
proof -
  have "atoms_ltln (ltlc_to_ltln' True \<phi>) = atoms_ltlc \<phi>"
    "atoms_ltln (ltlc_to_ltln' False \<phi>) = atoms_ltlc \<phi>"
    by (induction \<phi>) simp+
  thus ?thesis
    by simp
qed

subsubsection \<open>Negation\<close>

fun not\<^sub>n
where
  "not\<^sub>n true\<^sub>n = false\<^sub>n"
| "not\<^sub>n false\<^sub>n = true\<^sub>n"
| "not\<^sub>n prop\<^sub>n(a) = nprop\<^sub>n(a)"
| "not\<^sub>n nprop\<^sub>n(a) = prop\<^sub>n(a)"
| "not\<^sub>n (\<phi> and\<^sub>n \<psi>) = (not\<^sub>n \<phi>) or\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (\<phi> or\<^sub>n \<psi>) = (not\<^sub>n \<phi>) and\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (X\<^sub>n \<phi>) = X\<^sub>n (not\<^sub>n \<phi>)"
| "not\<^sub>n (\<phi> U\<^sub>n \<psi>) = (not\<^sub>n \<phi>) R\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (\<phi> R\<^sub>n \<psi>) = (not\<^sub>n \<phi>) U\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (\<phi> W\<^sub>n \<psi>) = (not\<^sub>n \<phi>) M\<^sub>n (not\<^sub>n \<psi>)"
| "not\<^sub>n (\<phi> M\<^sub>n \<psi>) = (not\<^sub>n \<phi>) W\<^sub>n (not\<^sub>n \<psi>)"

lemma not\<^sub>n_semantics[simp]:
  "w \<Turnstile>\<^sub>n not\<^sub>n \<phi> \<longleftrightarrow> \<not> w \<Turnstile>\<^sub>n \<phi>"
  by (induction \<phi> arbitrary: w) auto

lemma not\<^sub>n_size:
  "size (not\<^sub>n \<phi>) = size \<phi>"
  by (induction \<phi>) auto


subsubsection \<open>Subformulas\<close>

fun subfrmlsn :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "subfrmlsn (\<phi> and\<^sub>n \<psi>) = {\<phi> and\<^sub>n \<psi>} \<union> subfrmlsn \<phi> \<union> subfrmlsn \<psi>"
| "subfrmlsn (\<phi> or\<^sub>n \<psi>) = {\<phi> or\<^sub>n \<psi>} \<union> subfrmlsn \<phi> \<union> subfrmlsn \<psi>"
| "subfrmlsn (X\<^sub>n \<phi>) = {X\<^sub>n \<phi>} \<union> subfrmlsn \<phi>"
| "subfrmlsn (\<phi> U\<^sub>n \<psi>) = {\<phi> U\<^sub>n \<psi>} \<union> subfrmlsn \<phi> \<union> subfrmlsn \<psi>"
| "subfrmlsn (\<phi> R\<^sub>n \<psi>) = {\<phi> R\<^sub>n \<psi>} \<union> subfrmlsn \<phi> \<union> subfrmlsn \<psi>"
| "subfrmlsn (\<phi> W\<^sub>n \<psi>) = {\<phi> W\<^sub>n \<psi>} \<union> subfrmlsn \<phi> \<union> subfrmlsn \<psi>"
| "subfrmlsn (\<phi> M\<^sub>n \<psi>) = {\<phi> M\<^sub>n \<psi>} \<union> subfrmlsn \<phi> \<union> subfrmlsn \<psi>"
| "subfrmlsn \<phi> = {\<phi>}"

lemma subfrmlsn_id[simp]:
  "\<phi> \<in> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma subfrmlsn_finite:
  "finite (subfrmlsn \<phi>)"
  by (induction \<phi>) auto

lemma subfrmlsn_card:
  "card (subfrmlsn \<phi>) \<le> size \<phi>"
  by (induction \<phi>) (simp_all add: card_insert_if subfrmlsn_finite, (meson add_le_mono card_Un_le dual_order.trans le_SucI)+)

lemma subfrmlsn_subset:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> subfrmlsn \<psi> \<subseteq> subfrmlsn \<phi>"
  by (induction \<phi>) auto

lemma subfrmlsn_size:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> size \<psi> < size \<phi> \<or> \<psi> = \<phi>"
  by (induction \<phi>) auto

abbreviation
  "size_set S \<equiv> sum (\<lambda>x. 2 * size x + 1) S"

lemma size_set_diff:
  "finite S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> size_set (S - S') = size_set S - size_set S'"
  using sum_diff_nat finite_subset by metis


subsubsection \<open>Constant Folding\<close>

lemma U_consts[intro, simp]:
  "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n true\<^sub>n"
  "\<not> (w \<Turnstile>\<^sub>n \<phi> U\<^sub>n false\<^sub>n)"
  "(w \<Turnstile>\<^sub>n false\<^sub>n U\<^sub>n \<phi>) = (w \<Turnstile>\<^sub>n \<phi>)"
  by force+

lemma R_consts[intro, simp]:
  "w \<Turnstile>\<^sub>n \<phi> R\<^sub>n true\<^sub>n"
  "\<not> (w \<Turnstile>\<^sub>n \<phi> R\<^sub>n false\<^sub>n)"
  "(w \<Turnstile>\<^sub>n true\<^sub>n R\<^sub>n \<phi>) = (w \<Turnstile>\<^sub>n \<phi>)"
  by force+

lemma W_consts[intro, simp]:
  "w \<Turnstile>\<^sub>n true\<^sub>n W\<^sub>n \<phi>"
  "w \<Turnstile>\<^sub>n \<phi> W\<^sub>n true\<^sub>n"
  "(w \<Turnstile>\<^sub>n false\<^sub>n W\<^sub>n \<phi>) = (w \<Turnstile>\<^sub>n \<phi>)"
  "(w \<Turnstile>\<^sub>n \<phi> W\<^sub>n false\<^sub>n) = (w \<Turnstile>\<^sub>n G\<^sub>n \<phi>)"
  by force+

lemma M_consts[intro, simp]:
  "\<not> (w \<Turnstile>\<^sub>n false\<^sub>n M\<^sub>n \<phi>)"
  "\<not> (w \<Turnstile>\<^sub>n \<phi> M\<^sub>n false\<^sub>n)"
  "(w \<Turnstile>\<^sub>n true\<^sub>n M\<^sub>n \<phi>) = (w \<Turnstile>\<^sub>n \<phi>)"
  "(w \<Turnstile>\<^sub>n \<phi> M\<^sub>n true\<^sub>n) = (w \<Turnstile>\<^sub>n F\<^sub>n \<phi>)"
  by force+


subsubsection \<open>Distributivity\<close>

lemma until_and_left_distrib:
  "w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2) U\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 U\<^sub>n \<psi>) and\<^sub>n (\<phi>\<^sub>2 U\<^sub>n \<psi>)"
proof
  assume "w \<Turnstile>\<^sub>n \<phi>\<^sub>1 U\<^sub>n \<psi> and\<^sub>n \<phi>\<^sub>2 U\<^sub>n \<psi>"

  then obtain i1 i2 where "suffix i1 w \<Turnstile>\<^sub>n \<psi> \<and> (\<forall>j<i1. suffix j w \<Turnstile>\<^sub>n \<phi>\<^sub>1)" and "suffix i2 w \<Turnstile>\<^sub>n \<psi> \<and> (\<forall>j<i2. suffix j w \<Turnstile>\<^sub>n \<phi>\<^sub>2)"
    by auto

  then have "suffix (min i1 i2) w \<Turnstile>\<^sub>n \<psi> \<and> (\<forall>j<min i1 i2. suffix j w \<Turnstile>\<^sub>n \<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2)"
    by (simp add: min_def)

  then show "w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2) U\<^sub>n \<psi>"
    by force
qed auto

lemma until_or_right_distrib:
  "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n (\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2) \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> U\<^sub>n \<psi>\<^sub>1) or\<^sub>n (\<phi> U\<^sub>n \<psi>\<^sub>2)"
  by auto

lemma release_and_right_distrib:
  "w \<Turnstile>\<^sub>n \<phi> R\<^sub>n (\<psi>\<^sub>1 and\<^sub>n \<psi>\<^sub>2) \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> R\<^sub>n \<psi>\<^sub>1) and\<^sub>n (\<phi> R\<^sub>n \<psi>\<^sub>2)"
  by auto

lemma release_or_left_distrib:
  "w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2) R\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 R\<^sub>n \<psi>) or\<^sub>n (\<phi>\<^sub>2 R\<^sub>n \<psi>)"
  by (metis not\<^sub>n.simps(6) not\<^sub>n.simps(9) not\<^sub>n_semantics until_and_left_distrib)

lemma strong_release_and_right_distrib:
  "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n (\<psi>\<^sub>1 and\<^sub>n \<psi>\<^sub>2) \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> M\<^sub>n \<psi>\<^sub>1) and\<^sub>n (\<phi> M\<^sub>n \<psi>\<^sub>2)"
proof
  assume "w \<Turnstile>\<^sub>n (\<phi> M\<^sub>n \<psi>\<^sub>1) and\<^sub>n (\<phi> M\<^sub>n \<psi>\<^sub>2)"

  then obtain i1 i2 where "suffix i1 w \<Turnstile>\<^sub>n \<phi> \<and> (\<forall>j\<le>i1. suffix j w \<Turnstile>\<^sub>n \<psi>\<^sub>1)" and "suffix i2 w \<Turnstile>\<^sub>n \<phi> \<and> (\<forall>j\<le>i2. suffix j w \<Turnstile>\<^sub>n \<psi>\<^sub>2)"
    by auto

  then have "suffix (min i1 i2) w \<Turnstile>\<^sub>n \<phi> \<and> (\<forall>j\<le>min i1 i2. suffix j w \<Turnstile>\<^sub>n \<psi>\<^sub>1 and\<^sub>n \<psi>\<^sub>2)"
    by (simp add: min_def)

  then show "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n (\<psi>\<^sub>1 and\<^sub>n \<psi>\<^sub>2)"
    by force
qed auto

lemma strong_release_or_left_distrib:
  "w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 or\<^sub>n \<phi>\<^sub>2) M\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 M\<^sub>n \<psi>) or\<^sub>n (\<phi>\<^sub>2 M\<^sub>n \<psi>)"
  by auto

lemma weak_until_and_left_distrib:
  "w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 and\<^sub>n \<phi>\<^sub>2) W\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi>\<^sub>1 W\<^sub>n \<psi>) and\<^sub>n (\<phi>\<^sub>2 W\<^sub>n \<psi>)"
  by auto

lemma weak_until_or_right_distrib:
  "w \<Turnstile>\<^sub>n \<phi> W\<^sub>n (\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2) \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> W\<^sub>n \<psi>\<^sub>1) or\<^sub>n (\<phi> W\<^sub>n \<psi>\<^sub>2)"
  by (metis not\<^sub>n.simps(10) not\<^sub>n.simps(6) not\<^sub>n_semantics strong_release_and_right_distrib)


lemma next_until_distrib:
  "w \<Turnstile>\<^sub>n X\<^sub>n (\<phi> U\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n (X\<^sub>n \<phi>) U\<^sub>n (X\<^sub>n \<psi>)"
  by auto

lemma next_release_distrib:
  "w \<Turnstile>\<^sub>n X\<^sub>n (\<phi> R\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n (X\<^sub>n \<phi>) R\<^sub>n (X\<^sub>n \<psi>)"
  by auto

lemma next_weak_until_distrib:
  "w \<Turnstile>\<^sub>n X\<^sub>n (\<phi> W\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n (X\<^sub>n \<phi>) W\<^sub>n (X\<^sub>n \<psi>)"
  by auto

lemma next_strong_release_distrib:
  "w \<Turnstile>\<^sub>n X\<^sub>n (\<phi> M\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n (X\<^sub>n \<phi>) M\<^sub>n (X\<^sub>n \<psi>)"
  by auto


subsubsection \<open>Nested operators\<close>

lemma finally_until[simp]:
  "w \<Turnstile>\<^sub>n F\<^sub>n (\<phi> U\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n \<psi>"
  by auto force

lemma globally_release[simp]:
  "w \<Turnstile>\<^sub>n G\<^sub>n (\<phi> R\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
  by auto force

lemma globally_weak_until[simp]:
  "w \<Turnstile>\<^sub>n G\<^sub>n (\<phi> W\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n (\<phi> or\<^sub>n \<psi>)"
  by auto force

lemma finally_strong_release[simp]:
  "w \<Turnstile>\<^sub>n F\<^sub>n (\<phi> M\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n (\<phi> and\<^sub>n \<psi>)"
  by auto force


subsubsection \<open>Weak and strong operators\<close>

lemma ltln_weak_strong:
  "w \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (G\<^sub>n \<phi>) or\<^sub>n (\<phi> U\<^sub>n \<psi>)"
  "w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (G\<^sub>n \<psi>) or\<^sub>n (\<phi> M\<^sub>n \<psi>)"
proof auto
  fix i
  assume "\<forall>i. suffix i w \<Turnstile>\<^sub>n \<phi> \<or> (\<exists>j\<le>i. suffix j w \<Turnstile>\<^sub>n \<psi>)"
    and "\<forall>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<longrightarrow> (\<exists>j<i. \<not> suffix j w \<Turnstile>\<^sub>n \<phi>)"

  then show "suffix i w \<Turnstile>\<^sub>n \<phi>"
    by (induction i rule: less_induct) force
next
  fix i k
  assume "\<forall>j\<le>i. \<not> suffix j w \<Turnstile>\<^sub>n \<psi>"
    and "suffix k w \<Turnstile>\<^sub>n \<psi>"
    and "\<forall>j<k. suffix j w \<Turnstile>\<^sub>n \<phi>"

  then show "suffix i w \<Turnstile>\<^sub>n \<phi>"
    by (cases "i < k") simp_all
next
  fix i
  assume "\<forall>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<or> (\<exists>j<i. suffix j w \<Turnstile>\<^sub>n \<phi>)"
    and "\<forall>i. suffix i w \<Turnstile>\<^sub>n \<phi> \<longrightarrow> (\<exists>j\<le>i. \<not> suffix j w \<Turnstile>\<^sub>n \<psi>)"

  then show "suffix i w \<Turnstile>\<^sub>n \<psi>"
    by (induction i rule: less_induct) force
next
  fix i k
  assume "\<forall>j<i. \<not> suffix j w \<Turnstile>\<^sub>n \<phi>"
    and "suffix k w \<Turnstile>\<^sub>n \<phi>"
    and "\<forall>j\<le>k. suffix j w \<Turnstile>\<^sub>n \<psi>"

  then show "suffix i w \<Turnstile>\<^sub>n \<psi>"
    by (cases "i \<le> k") simp_all
qed

lemma ltln_strong_weak:
  "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (F\<^sub>n \<psi>) and\<^sub>n (\<phi> W\<^sub>n \<psi>)"
  "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (F\<^sub>n \<phi>) and\<^sub>n (\<phi> R\<^sub>n \<psi>)"
  by (metis ltln_weak_strong not\<^sub>n.simps(1,5,8-11) not\<^sub>n_semantics)+

lemma ltln_strong_to_weak:
  "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi>"
  "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi>"
  using ltln_weak_strong by simp_all blast+

lemma ltln_weak_to_strong:
  "\<lbrakk>w \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi>; \<not> w \<Turnstile>\<^sub>n G\<^sub>n \<phi>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi>"
  "\<lbrakk>w \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi>; w \<Turnstile>\<^sub>n F\<^sub>n \<psi>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi>"
  "\<lbrakk>w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi>; \<not> w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi>"
  "\<lbrakk>w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi>; w \<Turnstile>\<^sub>n F\<^sub>n \<phi>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi>"
  unfolding ltln_weak_strong[of w \<phi> \<psi>] by auto


lemma ltln_StrongRelease_to_Until:
  "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<psi> U\<^sub>n (\<phi> and\<^sub>n \<psi>)"
  using order.order_iff_strict by auto

lemma ltln_Release_to_WeakUntil:
  "w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<psi> W\<^sub>n (\<phi> and\<^sub>n \<psi>)"
  by (meson ltln_StrongRelease_to_Until ltln_weak_strong semantics_ltln.simps(6))

lemma ltln_WeakUntil_to_Release:
  "w \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<psi> R\<^sub>n (\<phi> or\<^sub>n \<psi>)"
  by (metis ltln_StrongRelease_to_Until not\<^sub>n.simps(6,9,10) not\<^sub>n_semantics)

lemma ltln_Until_to_StrongRelease:
  "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<psi> M\<^sub>n (\<phi> or\<^sub>n \<psi>)"
  by (metis ltln_Release_to_WeakUntil not\<^sub>n.simps(6,8,11) not\<^sub>n_semantics)


subsubsection \<open>GF and FG semantics\<close>

lemma GF_suffix:
  "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)"
  by auto (metis ab_semigroup_add_class.add_ac(1) add.left_commute)

lemma FG_suffix:
  "suffix i w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>)"
  by (auto simp: algebra_simps) (metis add.commute add.left_commute)

lemma GF_Inf_many:
  "w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>) \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. suffix i w \<Turnstile>\<^sub>n \<phi>)"
  unfolding INFM_nat_le
  by simp (blast dest: le_Suc_ex intro: le_add1)

lemma FG_Alm_all:
  "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>) \<longleftrightarrow> (\<forall>\<^sub>\<infinity> i. suffix i w \<Turnstile>\<^sub>n \<phi>)"
  unfolding MOST_nat_le
  by simp (blast dest: le_Suc_ex intro: le_add1)


(* TODO: move to Infinite_Set.thy ?? *)
lemma MOST_nat_add:
  "(\<forall>\<^sub>\<infinity>i::nat. P i) \<longleftrightarrow> (\<forall>\<^sub>\<infinity>i. P (i + j))"
  by (simp add: cofinite_eq_sequentially)

lemma INFM_nat_add:
  "(\<exists>\<^sub>\<infinity>i::nat. P i) \<longleftrightarrow> (\<exists>\<^sub>\<infinity>i. P (i + j))"
  using MOST_nat_add not_MOST not_INFM by blast


lemma FG_suffix_G:
  "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>) \<Longrightarrow> \<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<phi>"
proof -
  assume "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>)"
  then have "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n (G\<^sub>n \<phi>))"
    by (meson globally_release semantics_ltln.simps(8))
  then show "\<forall>\<^sub>\<infinity>i. suffix i w  \<Turnstile>\<^sub>n G\<^sub>n \<phi>"
    unfolding FG_Alm_all .
qed

lemma Alm_all_GF_F:
  "\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>) \<longleftrightarrow> suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<psi>"
  unfolding MOST_nat
proof standard+
  fix i :: nat
  assume "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)"
  then show "suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<psi>"
    unfolding GF_Inf_many INFM_nat by fastforce
next
  fix i :: nat
  assume suffix: "suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<psi>"
  assume max: "i > Max {i. suffix i w \<Turnstile>\<^sub>n \<psi>}"

  with suffix obtain j where "j \<ge> i" and j_suffix: "suffix j w \<Turnstile>\<^sub>n \<psi>"
    by simp (blast intro: le_add1)

  with max have j_max: "j > Max {i. suffix i w \<Turnstile>\<^sub>n \<psi>}"
    by fastforce

  show "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)"
  proof (cases "w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)")
    case False
    then have "\<not> (\<exists>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>)"
      unfolding GF_Inf_many by simp
    then have "finite {i. suffix i w \<Turnstile>\<^sub>n \<psi>}"
      by (simp add: INFM_iff_infinite)
    then have "\<forall>i>Max {i. suffix i w \<Turnstile>\<^sub>n \<psi>}. \<not> suffix i w \<Turnstile>\<^sub>n \<psi>"
      using Max_ge not_le by auto
    then show ?thesis
      using j_suffix j_max by blast
  qed force
qed

lemma Alm_all_FG_G:
  "\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>) \<longleftrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
  unfolding MOST_nat
proof standard+
  fix i :: nat
  assume "suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
  then show "suffix i w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>)"
    unfolding FG_Alm_all INFM_nat by fastforce
next
  fix i :: nat
  assume suffix: "suffix i w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>)"
  assume max: "i > Max {i. \<not> suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>}"

  with suffix have "\<forall>\<^sub>\<infinity>j. suffix (i + j) w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
    using FG_suffix_G[of "suffix i w"] suffix_suffix
    by fastforce
  then have "\<not> (\<exists>\<^sub>\<infinity>j. \<not> suffix j w \<Turnstile>\<^sub>n G\<^sub>n \<psi>)"
    using MOST_nat_add[of "\<lambda>i. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>" i]
    by (simp add: algebra_simps)
  then have "finite {i. \<not> suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>}"
    by (simp add: INFM_iff_infinite)

  with max show "suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
    using Max_ge leD by blast
qed


subsubsection \<open>Expansion\<close>

lemma ltln_expand_Until:
  "\<xi> \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<longleftrightarrow> (\<xi> \<Turnstile>\<^sub>n \<psi> or\<^sub>n (\<phi> and\<^sub>n (X\<^sub>n (\<phi> U\<^sub>n \<psi>))))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain i where "suffix i \<xi> \<Turnstile>\<^sub>n \<psi>"
    and "\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>"
    by auto
  thus ?rhs
    by (cases i) auto
next
  assume ?rhs
  show ?lhs
  proof (cases "\<xi> \<Turnstile>\<^sub>n \<psi>")
    case False
    then have "\<xi> \<Turnstile>\<^sub>n \<phi>" and "\<xi> \<Turnstile>\<^sub>n X\<^sub>n (\<phi> U\<^sub>n \<psi>)"
      using `?rhs` by auto
    thus ?lhs
      using less_Suc_eq_0_disj suffix_singleton_suffix by force
  qed force
qed

lemma ltln_expand_Release:
  "\<xi> \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi> \<longleftrightarrow> (\<xi> \<Turnstile>\<^sub>n \<psi> and\<^sub>n (\<phi> or\<^sub>n (X\<^sub>n (\<phi> R\<^sub>n \<psi>))))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    using less_Suc_eq_0_disj by force
next
  assume ?rhs

  {
    fix i
    assume "\<not> suffix i \<xi> \<Turnstile>\<^sub>n \<psi>"
    then have "\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>n \<phi>"
      using `?rhs` by (cases i) force+
  }

  thus ?lhs
    by auto
qed

lemma ltln_expand_WeakUntil:
  "\<xi> \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi> \<longleftrightarrow> (\<xi> \<Turnstile>\<^sub>n \<psi> or\<^sub>n (\<phi> and\<^sub>n (X\<^sub>n (\<phi> W\<^sub>n \<psi>))))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by (metis ltln_expand_Release ltln_expand_Until ltln_weak_strong(1) semantics_ltln.simps(2,5,6,7))
next
  assume ?rhs

  {
    fix i
    assume "\<not> suffix i \<xi> \<Turnstile>\<^sub>n \<phi>"
    then have "\<exists>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>n \<psi>"
      using `?rhs` by (cases i) force+
  }

  thus ?lhs
    by auto
qed

lemma ltln_expand_StrongRelease:
  "\<xi> \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<longleftrightarrow> (\<xi> \<Turnstile>\<^sub>n \<psi> and\<^sub>n (\<phi> or\<^sub>n (X\<^sub>n (\<phi> M\<^sub>n \<psi>))))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain i where "suffix i \<xi> \<Turnstile>\<^sub>n \<phi>"
    and "\<forall>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>n \<psi>"
    by auto
  thus ?rhs
    by (cases i) auto
next
  assume ?rhs
  show ?lhs
  proof (cases "\<xi> \<Turnstile>\<^sub>n \<phi>")
    case True
    thus ?lhs
      using `?rhs` ltln_expand_WeakUntil by fastforce
  next
    case False
    thus ?lhs
      by (metis `?rhs` ltln_expand_WeakUntil not\<^sub>n.simps(5,6,7,11) not\<^sub>n_semantics)
  qed
qed

lemma ltln_Release_alterdef:
  "w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (G\<^sub>n \<psi>) or\<^sub>n (\<psi> U\<^sub>n (\<phi> and\<^sub>n \<psi>))"
proof (cases "\<exists>i. \<not>suffix i w \<Turnstile>\<^sub>n \<psi>")
  case True
  define i where "i \<equiv> Least (\<lambda>i. \<not>suffix i w \<Turnstile>\<^sub>n \<psi>)"
  have "\<And>j. j < i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<psi>" and "\<not> suffix i w \<Turnstile>\<^sub>n \<psi>"
    using True LeastI not_less_Least unfolding i_def by fast+
  hence *: "\<forall>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<or> (\<exists>j<i. suffix j w \<Turnstile>\<^sub>n \<phi>) \<Longrightarrow> (\<exists>i. (suffix i w \<Turnstile>\<^sub>n \<psi> \<and> suffix i w \<Turnstile>\<^sub>n \<phi>) \<and> (\<forall>j<i. suffix j w \<Turnstile>\<^sub>n \<psi>))"
    by fastforce
  hence "\<exists>i. (suffix i w \<Turnstile>\<^sub>n \<psi> \<and> suffix i w \<Turnstile>\<^sub>n \<phi>) \<and> (\<forall>j<i. suffix j w \<Turnstile>\<^sub>n \<psi>) \<Longrightarrow> (\<forall>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<or> (\<exists>j<i. suffix j w \<Turnstile>\<^sub>n \<phi>))"
    using linorder_cases by blast
  thus ?thesis
    using True * by auto
qed auto




subsection \<open>LTL in restricted Negation Normal Form\<close>

text \<open>Some algorithms do not handle the operators W and M,
    hence we also provide a datatype without these two operators.\<close>

subsubsection \<open>Syntax\<close>

datatype (atoms_ltlr: 'a) ltlr =
    True_ltlr                               ("true\<^sub>r")
  | False_ltlr                              ("false\<^sub>r")
  | Prop_ltlr 'a                            ("prop\<^sub>r'(_')")
  | Nprop_ltlr 'a                           ("nprop\<^sub>r'(_')")
  | And_ltlr "'a ltlr" "'a ltlr"            ("_ and\<^sub>r _" [82,82] 81)
  | Or_ltlr "'a ltlr" "'a ltlr"             ("_ or\<^sub>r _" [84,84] 83)
  | Next_ltlr "'a ltlr"                     ("X\<^sub>r _" [88] 87)
  | Until_ltlr "'a ltlr" "'a ltlr"          ("_ U\<^sub>r _" [84,84] 83)
  | Release_ltlr "'a ltlr" "'a ltlr"        ("_ R\<^sub>r _" [84,84] 83)


subsubsection \<open>Semantics\<close>

primrec semantics_ltlr :: "['a set word, 'a ltlr] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>r _" [80,80] 80)
where
  "\<xi> \<Turnstile>\<^sub>r true\<^sub>r = True"
| "\<xi> \<Turnstile>\<^sub>r false\<^sub>r = False"
| "\<xi> \<Turnstile>\<^sub>r prop\<^sub>r(q) = (q \<in> \<xi> 0)"
| "\<xi> \<Turnstile>\<^sub>r nprop\<^sub>r(q) = (q \<notin> \<xi> 0)"
| "\<xi> \<Turnstile>\<^sub>r \<phi> and\<^sub>r \<psi> = (\<xi> \<Turnstile>\<^sub>r \<phi> \<and> \<xi> \<Turnstile>\<^sub>r \<psi>)"
| "\<xi> \<Turnstile>\<^sub>r \<phi> or\<^sub>r \<psi> = (\<xi> \<Turnstile>\<^sub>r \<phi> \<or> \<xi> \<Turnstile>\<^sub>r \<psi>)"
| "\<xi> \<Turnstile>\<^sub>r X\<^sub>r \<phi> = (suffix 1 \<xi> \<Turnstile>\<^sub>r \<phi>)"
| "\<xi> \<Turnstile>\<^sub>r \<phi> U\<^sub>r \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>r \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>r \<phi>))"
| "\<xi> \<Turnstile>\<^sub>r \<phi> R\<^sub>r \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>r \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>r \<phi>))"


subsubsection \<open>Conversion\<close>

fun ltln_to_ltlr :: "'a ltln \<Rightarrow> 'a ltlr"
where
  "ltln_to_ltlr true\<^sub>n = true\<^sub>r"
| "ltln_to_ltlr false\<^sub>n = false\<^sub>r"
| "ltln_to_ltlr prop\<^sub>n(a) = prop\<^sub>r(a)"
| "ltln_to_ltlr nprop\<^sub>n(a) = nprop\<^sub>r(a)"
| "ltln_to_ltlr (\<phi> and\<^sub>n \<psi>) = (ltln_to_ltlr \<phi>) and\<^sub>r (ltln_to_ltlr \<psi>)"
| "ltln_to_ltlr (\<phi> or\<^sub>n \<psi>) = (ltln_to_ltlr \<phi>) or\<^sub>r (ltln_to_ltlr \<psi>)"
| "ltln_to_ltlr (X\<^sub>n \<phi>) = X\<^sub>r (ltln_to_ltlr \<phi>)"
| "ltln_to_ltlr (\<phi> U\<^sub>n \<psi>) = (ltln_to_ltlr \<phi>) U\<^sub>r (ltln_to_ltlr \<psi>)"
| "ltln_to_ltlr (\<phi> R\<^sub>n \<psi>) = (ltln_to_ltlr \<phi>) R\<^sub>r (ltln_to_ltlr \<psi>)"
| "ltln_to_ltlr (\<phi> W\<^sub>n \<psi>) = (ltln_to_ltlr \<psi>) R\<^sub>r ((ltln_to_ltlr \<phi>) or\<^sub>r (ltln_to_ltlr \<psi>))"
| "ltln_to_ltlr (\<phi> M\<^sub>n \<psi>) = (ltln_to_ltlr \<psi>) U\<^sub>r ((ltln_to_ltlr \<phi>) and\<^sub>r (ltln_to_ltlr \<psi>))"

fun ltlr_to_ltln :: "'a ltlr \<Rightarrow> 'a ltln"
where
  "ltlr_to_ltln true\<^sub>r = true\<^sub>n"
| "ltlr_to_ltln false\<^sub>r = false\<^sub>n"
| "ltlr_to_ltln prop\<^sub>r(a) = prop\<^sub>n(a)"
| "ltlr_to_ltln nprop\<^sub>r(a) = nprop\<^sub>n(a)"
| "ltlr_to_ltln (\<phi> and\<^sub>r \<psi>) = (ltlr_to_ltln \<phi>) and\<^sub>n (ltlr_to_ltln \<psi>)"
| "ltlr_to_ltln (\<phi> or\<^sub>r \<psi>) = (ltlr_to_ltln \<phi>) or\<^sub>n (ltlr_to_ltln \<psi>)"
| "ltlr_to_ltln (X\<^sub>r \<phi>) = X\<^sub>n (ltlr_to_ltln \<phi>)"
| "ltlr_to_ltln (\<phi> U\<^sub>r \<psi>) = (ltlr_to_ltln \<phi>) U\<^sub>n (ltlr_to_ltln \<psi>)"
| "ltlr_to_ltln (\<phi> R\<^sub>r \<psi>) = (ltlr_to_ltln \<phi>) R\<^sub>n (ltlr_to_ltln \<psi>)"

lemma ltln_to_ltlr_semantics:
  "w \<Turnstile>\<^sub>r ltln_to_ltlr \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (induction \<phi> arbitrary: w) (unfold ltln_WeakUntil_to_Release ltln_StrongRelease_to_Until, simp_all)

lemma ltlr_to_ltln_semantics:
  "w \<Turnstile>\<^sub>n ltlr_to_ltln \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>r \<phi>"
  by (induction \<phi> arbitrary: w) simp_all


subsubsection \<open>Negation\<close>

fun not\<^sub>r
where
  "not\<^sub>r true\<^sub>r = false\<^sub>r"
| "not\<^sub>r false\<^sub>r = true\<^sub>r"
| "not\<^sub>r prop\<^sub>r(a) = nprop\<^sub>r(a)"
| "not\<^sub>r nprop\<^sub>r(a) = prop\<^sub>r(a)"
| "not\<^sub>r (\<phi> and\<^sub>r \<psi>) = (not\<^sub>r \<phi>) or\<^sub>r (not\<^sub>r \<psi>)"
| "not\<^sub>r (\<phi> or\<^sub>r \<psi>) = (not\<^sub>r \<phi>) and\<^sub>r (not\<^sub>r \<psi>)"
| "not\<^sub>r (X\<^sub>r \<phi>) = X\<^sub>r (not\<^sub>r \<phi>)"
| "not\<^sub>r (\<phi> U\<^sub>r \<psi>) = (not\<^sub>r \<phi>) R\<^sub>r (not\<^sub>r \<psi>)"
| "not\<^sub>r (\<phi> R\<^sub>r \<psi>) = (not\<^sub>r \<phi>) U\<^sub>r (not\<^sub>r \<psi>)"

lemma not\<^sub>r_semantics [simp]:
  "w \<Turnstile>\<^sub>r not\<^sub>r \<phi> \<longleftrightarrow> \<not> w \<Turnstile>\<^sub>r \<phi>"
  by (induction \<phi> arbitrary: w) auto


subsubsection \<open>Subformulas\<close>

fun subfrmlsr :: "'a ltlr \<Rightarrow> 'a ltlr set"
where
  "subfrmlsr (\<phi> and\<^sub>r \<psi>) = {\<phi> and\<^sub>r \<psi>} \<union> subfrmlsr \<phi> \<union> subfrmlsr \<psi>"
| "subfrmlsr (\<phi> or\<^sub>r \<psi>) = {\<phi> or\<^sub>r \<psi>} \<union> subfrmlsr \<phi> \<union> subfrmlsr \<psi>"
| "subfrmlsr (\<phi> U\<^sub>r \<psi>) = {\<phi> U\<^sub>r \<psi>} \<union> subfrmlsr \<phi> \<union> subfrmlsr \<psi>"
| "subfrmlsr (\<phi> R\<^sub>r \<psi>) = {\<phi> R\<^sub>r \<psi>} \<union> subfrmlsr \<phi> \<union> subfrmlsr \<psi>"
| "subfrmlsr (X\<^sub>r \<phi>) = {X\<^sub>r \<phi>} \<union> subfrmlsr \<phi>"
| "subfrmlsr x = {x}"

lemma subfrmlsr_id[simp]:
  "\<phi> \<in> subfrmlsr \<phi>"
  by (induction \<phi>) auto

lemma subfrmlsr_finite:
  "finite (subfrmlsr \<phi>)"
  by (induction \<phi>) auto

lemma subfrmlsr_subset:
  "\<psi> \<in> subfrmlsr \<phi> \<Longrightarrow> subfrmlsr \<psi> \<subseteq> subfrmlsr \<phi>"
  by (induction \<phi>) auto

lemma subfrmlsr_size:
  "\<psi> \<in> subfrmlsr \<phi> \<Longrightarrow> size \<psi> < size \<phi> \<or> \<psi> = \<phi>"
  by (induction \<phi>) auto


subsubsection \<open>Expansion lemmas\<close>

lemma ltlr_expand_Until:
  "\<xi> \<Turnstile>\<^sub>r \<phi> U\<^sub>r \<psi> \<longleftrightarrow> (\<xi> \<Turnstile>\<^sub>r \<psi> or\<^sub>r (\<phi> and\<^sub>r (X\<^sub>r (\<phi> U\<^sub>r \<psi>))))"
  by (metis ltln_expand_Until ltlr_to_ltln.simps(5-8) ltlr_to_ltln_semantics)

lemma ltlr_expand_Release:
  "\<xi> \<Turnstile>\<^sub>r \<phi> R\<^sub>r \<psi> \<longleftrightarrow> (\<xi> \<Turnstile>\<^sub>r \<psi> and\<^sub>r (\<phi> or\<^sub>r (X\<^sub>r (\<phi> R\<^sub>r \<psi>))))"
  by (metis ltln_expand_Release ltlr_to_ltln.simps(5-7,9) ltlr_to_ltln_semantics)




subsection \<open>Propositional LTL\<close>

text \<open>We define the syntax and semantics of propositional linear-time
    temporal logic PLTL.
    PLTL formulas are built from atomic formulas, propositional connectives,
    and the temporal operators ``next'' and ``until''. The following data
    type definition is parameterized by the type of states over which
    formulas are evaluated.\<close>

subsubsection \<open>Syntax\<close>

datatype 'a pltl  =
    False_ltlp                       ("false\<^sub>p")
  | Atom_ltlp "'a \<Rightarrow> bool"           ("atom\<^sub>p'(_')")
  | Implies_ltlp "'a pltl" "'a pltl" ("_ implies\<^sub>p _" [81,81] 80)
  | Next_ltlp "'a pltl"              ("X\<^sub>p _" [88] 87)
  | Until_ltlp "'a pltl" "'a pltl"   ("_ U\<^sub>p _" [84,84] 83)

\<comment> \<open>Further connectives of PLTL can be defined in terms of the existing syntax.\<close>

definition Not_ltlp ("not\<^sub>p _" [85] 85)
where
  "not\<^sub>p \<phi> \<equiv> \<phi> implies\<^sub>p false\<^sub>p"

definition True_ltlp ("true\<^sub>p")
where
  "true\<^sub>p \<equiv> not\<^sub>p false\<^sub>p"

definition Or_ltlp ("_ or\<^sub>p _" [81,81] 80)
where
  "\<phi> or\<^sub>p \<psi> \<equiv> (not\<^sub>p \<phi>) implies\<^sub>p \<psi>"

definition And_ltlp ("_ and\<^sub>p _" [82,82] 81)
where
  "\<phi> and\<^sub>p \<psi> \<equiv> not\<^sub>p ((not\<^sub>p \<phi>) or\<^sub>p (not\<^sub>p \<psi>))"

definition Eventually_ltlp ("F\<^sub>p _" [88] 87)
where
  "F\<^sub>p \<phi> \<equiv> true\<^sub>p U\<^sub>p \<phi>"

definition Always_ltlp ("G\<^sub>p _" [88] 87)
where
  "G\<^sub>p \<phi> \<equiv> not\<^sub>p (F\<^sub>p (not\<^sub>p \<phi>))"

definition Release_ltlp ("_ R\<^sub>p _" [84,84] 83)
where
  "\<phi> R\<^sub>p \<psi> \<equiv> not\<^sub>p ((not\<^sub>p \<phi>) U\<^sub>p (not\<^sub>p \<psi>))"

definition WeakUntil_ltlp ("_ W\<^sub>p _" [84,84] 83)
where
  "\<phi> W\<^sub>p \<psi> \<equiv> \<psi> R\<^sub>p (\<phi> or\<^sub>p \<psi>)"

definition StrongRelease_ltlp ("_ M\<^sub>p _" [84,84] 83)
where
  "\<phi> M\<^sub>p \<psi> \<equiv> \<psi> U\<^sub>p (\<phi> and\<^sub>p \<psi>)"


subsubsection \<open>Semantics\<close>

fun semantics_pltl :: "['a word, 'a pltl] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>p _" [80,80] 80)
where
  "w \<Turnstile>\<^sub>p false\<^sub>p = False"
| "w \<Turnstile>\<^sub>p atom\<^sub>p(p) = (p (w 0))"
| "w \<Turnstile>\<^sub>p \<phi> implies\<^sub>p \<psi> = (w \<Turnstile>\<^sub>p \<phi> \<longrightarrow> w \<Turnstile>\<^sub>p \<psi>)"
| "w \<Turnstile>\<^sub>p X\<^sub>p \<phi> = (suffix 1 w \<Turnstile>\<^sub>p \<phi>)"
| "w \<Turnstile>\<^sub>p \<phi> U\<^sub>p \<psi> = (\<exists>i. suffix i w \<Turnstile>\<^sub>p \<psi> \<and> (\<forall>j<i. suffix j w \<Turnstile>\<^sub>p \<phi>))"

lemma semantics_pltl_sugar [simp]:
  "w \<Turnstile>\<^sub>p not\<^sub>p \<phi> = (\<not>w \<Turnstile>\<^sub>p \<phi>)"
  "w \<Turnstile>\<^sub>p true\<^sub>p = True"
  "w \<Turnstile>\<^sub>p \<phi> or\<^sub>p \<psi> = (w \<Turnstile>\<^sub>p \<phi> \<or> w \<Turnstile>\<^sub>p \<psi>)"
  "w \<Turnstile>\<^sub>p \<phi> and\<^sub>p \<psi> = (w \<Turnstile>\<^sub>p \<phi> \<and> w \<Turnstile>\<^sub>p \<psi>)"
  "w \<Turnstile>\<^sub>p F\<^sub>p \<phi> = (\<exists>i. suffix i w \<Turnstile>\<^sub>p \<phi>)"
  "w \<Turnstile>\<^sub>p G\<^sub>p \<phi> = (\<forall>i. suffix i w \<Turnstile>\<^sub>p \<phi>)"
  "w \<Turnstile>\<^sub>p \<phi> R\<^sub>p \<psi> = (\<forall>i. suffix i w \<Turnstile>\<^sub>p \<psi> \<or> (\<exists>j<i. suffix j w \<Turnstile>\<^sub>p \<phi>))"
  "w \<Turnstile>\<^sub>p \<phi> W\<^sub>p \<psi> = (\<forall>i. suffix i w \<Turnstile>\<^sub>p \<phi> \<or> (\<exists>j\<le>i. suffix j w \<Turnstile>\<^sub>p \<psi>))"
  "w \<Turnstile>\<^sub>p \<phi> M\<^sub>p \<psi> = (\<exists>i. suffix i w \<Turnstile>\<^sub>p \<phi> \<and> (\<forall>j\<le>i. suffix j w \<Turnstile>\<^sub>p \<psi>))"
  by (auto simp: Not_ltlp_def True_ltlp_def Or_ltlp_def And_ltlp_def Eventually_ltlp_def Always_ltlp_def Release_ltlp_def WeakUntil_ltlp_def StrongRelease_ltlp_def) (insert le_neq_implies_less, blast)+

definition "language_ltlp \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile>\<^sub>p \<phi>}"


subsubsection \<open>Conversion\<close>

fun ltlc_to_pltl :: "'a ltlc \<Rightarrow> 'a set pltl"
where
  "ltlc_to_pltl true\<^sub>c = true\<^sub>p"
| "ltlc_to_pltl false\<^sub>c = false\<^sub>p"
| "ltlc_to_pltl (prop\<^sub>c(q)) = atom\<^sub>p((\<in>) q)"
| "ltlc_to_pltl (not\<^sub>c \<phi>) = not\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (\<phi> and\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) and\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> or\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) or\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> implies\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) implies\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (X\<^sub>c \<phi>) = X\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (F\<^sub>c \<phi>) = F\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (G\<^sub>c \<phi>) = G\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (\<phi> U\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) U\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> R\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) R\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> W\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) W\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> M\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) M\<^sub>p (ltlc_to_pltl \<psi>)"

lemma ltlc_to_pltl_semantics [simp]:
  "w \<Turnstile>\<^sub>p (ltlc_to_pltl \<phi>) \<longleftrightarrow> w \<Turnstile>\<^sub>c \<phi>"
  by (induction \<phi> arbitrary: w) simp_all


subsubsection \<open>Atoms\<close>

fun atoms_pltl :: "'a pltl \<Rightarrow> ('a \<Rightarrow> bool) set"
where
  "atoms_pltl false\<^sub>p = {}"
| "atoms_pltl atom\<^sub>p(p) = {p}"
| "atoms_pltl (\<phi> implies\<^sub>p \<psi>) = atoms_pltl \<phi> \<union> atoms_pltl \<psi>"
| "atoms_pltl (X\<^sub>p \<phi>) = atoms_pltl \<phi>"
| "atoms_pltl (\<phi> U\<^sub>p \<psi>) = atoms_pltl \<phi> \<union> atoms_pltl \<psi>"

lemma atoms_finite [iff]:
  "finite (atoms_pltl \<phi>)"
  by (induct \<phi>) auto

lemma atoms_pltl_sugar [simp]:
  "atoms_pltl (not\<^sub>p \<phi>) = atoms_pltl \<phi>"
  "atoms_pltl true\<^sub>p = {}"
  "atoms_pltl (\<phi> or\<^sub>p \<psi>) = atoms_pltl \<phi> \<union> atoms_pltl \<psi>"
  "atoms_pltl (\<phi> and\<^sub>p \<psi>) = atoms_pltl \<phi> \<union> atoms_pltl \<psi>"
  "atoms_pltl (F\<^sub>p \<phi>) = atoms_pltl \<phi>"
  "atoms_pltl (G\<^sub>p \<phi>) = atoms_pltl \<phi>"
  by (auto simp: Not_ltlp_def True_ltlp_def Or_ltlp_def And_ltlp_def Eventually_ltlp_def Always_ltlp_def)

end
