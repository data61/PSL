(*  Title:      LList2.thy
    Author:     Stefan Friedrich
    Maintainer: Stefan Friedrich
    License:    LGPL

Llists over an alphabet.
Common operations on LLists (ltake, ldrop, lnth).
The prefix order of llists.
Safety and liveness.
*)

section\<open>More on llists\<close>

theory LList2
imports Coinductive.Coinductive_List
begin

subsection\<open>Preliminaries\<close>

notation
  LCons  (infixr "##" 65) and
  lappend  (infixr "@@" 65)

translations
  "case p of XCONST LNil \<Rightarrow> a | x ## l \<Rightarrow> b" \<rightleftharpoons> "CONST case_llist a (\<lambda>x l. b) p"
  "case p of XCONST LNil :: 'a \<Rightarrow> a | x ## l \<Rightarrow> b" \<rightharpoonup> "CONST case_llist a (\<lambda>x l. b) p"


lemmas llistE = llist.exhaust

subsection\<open>Finite and infinite llists over an alphabet\<close>

inductive_set
  finlsts :: "'a set \<Rightarrow> 'a llist set" ("(_\<^sup>\<star>)" [1000] 999)
  for A :: "'a set"
where
  LNil_fin [iff]: "LNil \<in>  A\<^sup>\<star>"
| LCons_fin [intro!]: "\<lbrakk> l \<in> A\<^sup>\<star>; a \<in> A \<rbrakk> \<Longrightarrow>  a ## l \<in> A\<^sup>\<star>"

coinductive_set
  alllsts :: "'a set \<Rightarrow> 'a llist set" ("(_\<^sup>\<infinity>)" [1000] 999)
  for A :: "'a set"
where
  LNil_all [iff]: "LNil \<in> A\<^sup>\<infinity>"
| LCons_all [intro!]: "\<lbrakk> l \<in> A\<^sup>\<infinity>; a \<in> A \<rbrakk> \<Longrightarrow>  a ## l \<in> A\<^sup>\<infinity>"

declare alllsts.cases [case_names LNil LCons, cases set: alllsts]

definition inflsts :: "'a set \<Rightarrow> 'a llist set"  ("(_\<^sup>\<omega>)" [1000] 999)
where "A\<^sup>\<omega> \<equiv>  A\<^sup>\<infinity> - UNIV\<^sup>\<star>"

definition fpslsts :: "'a set \<Rightarrow> 'a llist set"  ("(_\<^sup>\<clubsuit>)" [1000] 999)
where "A\<^sup>\<clubsuit> \<equiv> A\<^sup>\<star> - {LNil}"

definition poslsts :: "'a set \<Rightarrow> 'a llist set"  ("(_\<^sup>\<spadesuit>)" [1000] 999)
where "A\<^sup>\<spadesuit> \<equiv> A\<^sup>\<infinity> - {LNil}"


subsubsection\<open>Facts about all llists\<close>

lemma alllsts_UNIV [iff]:
  "s \<in> UNIV\<^sup>\<infinity>"
proof -
  have "s \<in> UNIV" by blast
  thus ?thesis
  proof coinduct
    case (alllsts z)
    thus ?case by(cases z) auto
  qed
qed

lemma alllsts_empty [simp]: "{}\<^sup>\<infinity> = {LNil}"
  by (auto elim: alllsts.cases)

lemma alllsts_mono:
  assumes asubb: "A \<subseteq> B"
  shows "A\<^sup>\<infinity> \<subseteq> B\<^sup>\<infinity>"
proof
  fix x assume "x \<in> A\<^sup>\<infinity>" 
  thus "x \<in> B\<^sup>\<infinity>"
  proof coinduct
    case (alllsts z)
    thus ?case using asubb by(cases z) auto
  qed
qed

lemmas alllstsp_mono [mono] = alllsts_mono [to_pred pred_subset_eq]

lemma LConsE [iff]: "x##xs \<in> A\<^sup>\<infinity> = (x\<in>A \<and> xs \<in> A\<^sup>\<infinity>)"
  by (auto elim: alllsts.cases)


subsubsection\<open>Facts about non-empty (positive) llists\<close>

lemma poslsts_iff [iff]:
  "(s \<in> A\<^sup>\<spadesuit>) = (s \<in> A\<^sup>\<infinity> \<and> s \<noteq> LNil)"
  by (simp add: poslsts_def)

lemma poslsts_UNIV [iff]:
  "s \<in> UNIV\<^sup>\<spadesuit> = (s \<noteq> LNil)"
  by auto

lemma poslsts_empty [simp]: "{}\<^sup>\<spadesuit> = {}"
  by auto

lemma poslsts_mono:
  "A \<subseteq> B \<Longrightarrow> A\<^sup>\<spadesuit> \<subseteq> B\<^sup>\<spadesuit>"
  by (auto dest: alllsts_mono)

subsubsection\<open>Facts about finite llists\<close>

lemma finlsts_empty [simp]: "{}\<^sup>\<star> = {LNil}"
  by (auto elim: finlsts.cases)

lemma finsubsetall: "x \<in> A\<^sup>\<star> \<Longrightarrow> x \<in> A\<^sup>\<infinity>"
  by (induct rule: finlsts.induct) auto

lemma finlsts_mono:
"A\<subseteq>B \<Longrightarrow> A\<^sup>\<star> \<subseteq> B\<^sup>\<star>"
  by (auto, erule finlsts.induct) auto

lemmas finlstsp_mono [mono] = finlsts_mono [to_pred pred_subset_eq]

lemma finlsts_induct
  [case_names LNil_fin LCons_fin, induct set: finlsts, consumes 1]:
  assumes xA: "x \<in> A\<^sup>\<star>"
  and lnil: "\<And>l. l = LNil \<Longrightarrow> P l"
  and lcons: "\<And>a l. \<lbrakk>l \<in> A\<^sup>\<star>; P l; a \<in> A\<rbrakk> \<Longrightarrow> P (a ## l)"
  shows "P x"
  using xA by (induct "x") (auto intro: lnil lcons)

lemma finite_lemma:
  assumes "x \<in> A\<^sup>\<star>"
  shows "x \<in> B\<^sup>\<infinity> \<Longrightarrow> x \<in> B\<^sup>\<star>"
using assms
proof (induct)
  case LNil_fin thus ?case by auto
next
  case (LCons_fin a l)
  thus ?case using LCons_fin by (cases "a##l") auto
qed

lemma fin_finite [dest]:
assumes "r \<in> A\<^sup>\<star>" "r \<notin> UNIV\<^sup>\<star>"
  shows "False"
proof-
  have "A \<subseteq> UNIV" by auto
  hence "A\<^sup>\<star> \<subseteq> UNIV\<^sup>\<star>" by (rule finlsts_mono)
  thus ?thesis using assms by auto
qed

lemma finT_simp [simp]:
  "r \<in> A\<^sup>\<star> \<Longrightarrow> r\<in>UNIV\<^sup>\<star>"
  by auto


subsubsection\<open>A recursion operator for finite llists\<close>

definition finlsts_pred :: "('a llist \<times> 'a llist) set"
where "finlsts_pred \<equiv> {(r,s). r \<in> UNIV\<^sup>\<star> \<and> (\<exists>a. a##r = s)}"

definition finlsts_rec :: "['b, ['a, 'a llist, 'b] \<Rightarrow> 'b] \<Rightarrow> 'a llist \<Rightarrow> 'b"
where
  "finlsts_rec c d r \<equiv> if r \<in> UNIV\<^sup>\<star>
  then (wfrec finlsts_pred (%f. case_llist c (%a r. d a r (f r))) r)
  else undefined"

lemma finlsts_predI: "r \<in> A\<^sup>\<star> \<Longrightarrow> (r, a##r) \<in> finlsts_pred"
  by (auto simp: finlsts_pred_def)

lemma wf_finlsts_pred: "wf finlsts_pred"
proof (rule wfI [of _ "UNIV\<^sup>\<star>"])
  show "finlsts_pred \<subseteq> UNIV\<^sup>\<star> \<times> UNIV\<^sup>\<star>"
    by (auto simp: finlsts_pred_def elim: finlsts.cases)
next
  fix x::"'a llist" and P::"'a llist \<Rightarrow> bool"
  assume xfin: "x \<in> UNIV\<^sup>\<star>" and H [unfolded finlsts_pred_def]:
    "(\<forall>x. (\<forall>y. (y, x) \<in> finlsts_pred \<longrightarrow> P y) \<longrightarrow> P x)"
  from  xfin show "P x"
  proof(induct x)
    case LNil_fin with H show ?case by blast
  next
    case (LCons_fin a l) with H show ?case by blast
  qed
qed

lemma finlsts_rec_LNil: "finlsts_rec c d LNil = c"
  by (auto simp: wf_finlsts_pred finlsts_rec_def wfrec)

lemma finlsts_rec_LCons:
 "r \<in> A\<^sup>\<star> \<Longrightarrow> finlsts_rec c d (a ## r) = d a r (finlsts_rec c d r)"
  by (auto simp: wf_finlsts_pred finlsts_rec_def wfrec cut_def intro: finlsts_predI)

lemma finlsts_rec_LNil_def:
  "f \<equiv> finlsts_rec c d \<Longrightarrow> f LNil = c"
  by (auto simp: finlsts_rec_LNil)

lemma finlsts_rec_LCons_def:
  "\<lbrakk> f \<equiv> finlsts_rec c d; r \<in> A\<^sup>\<star> \<rbrakk> \<Longrightarrow> f (a ## r) = d a r (f r)"
  by (auto simp: finlsts_rec_LCons)


subsubsection\<open>Facts about non-empty (positive) finite llists\<close>

lemma fpslsts_iff [iff]:
  "(s \<in> A\<^sup>\<clubsuit>) = (s \<in> A\<^sup>\<star> \<and> s \<noteq> LNil)"
  by (auto simp: fpslsts_def)

lemma fpslsts_empty [simp]: "{}\<^sup>\<clubsuit> = {}"
  by auto

lemma fpslsts_mono:
  "A \<subseteq> B \<Longrightarrow> A\<^sup>\<clubsuit> \<subseteq> B\<^sup>\<clubsuit>"
  by (auto dest: finlsts_mono)

lemma fpslsts_cases [case_names LCons, cases set: fpslsts]:
assumes rfps: "r \<in> A\<^sup>\<clubsuit>"
  and H: "\<And> a rs. \<lbrakk> r = a ## rs; a\<in>A; rs \<in> A\<^sup>\<star> \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  from rfps have "r \<in> A\<^sup>\<star>" and "r \<noteq> LNil" by auto
  thus ?thesis
    by (cases r, simp) (blast intro!: H)
qed


subsubsection\<open>Facts about infinite llists\<close>

lemma inflstsI [intro]:
  "\<lbrakk> x \<in> A\<^sup>\<infinity>; x \<in> UNIV\<^sup>\<star> \<Longrightarrow> False \<rbrakk> \<Longrightarrow> x \<in> A\<^sup>\<omega>"
unfolding inflsts_def by clarsimp

lemma inflstsE [elim]:
  "\<lbrakk> x \<in> A\<^sup>\<omega>; \<lbrakk> x \<in> A\<^sup>\<infinity>; x \<notin> UNIV\<^sup>\<star> \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (unfold inflsts_def) auto

lemma inflsts_empty [simp]: "{}\<^sup>\<omega> = {}"
  by auto

lemma infsubsetall: "x \<in> A\<^sup>\<omega> \<Longrightarrow> x \<in> A\<^sup>\<infinity>"
  by (auto intro: finite_lemma finsubsetall)

lemma inflsts_mono:
  "A \<subseteq> B \<Longrightarrow> A\<^sup>\<omega> \<subseteq> B\<^sup>\<omega>"
  by (blast dest: alllsts_mono infsubsetall)

lemma inflsts_cases [case_names LCons, cases set: inflsts, consumes 1]:
  assumes sinf: "s \<in> A\<^sup>\<omega>"
  and R: "\<And>a l. \<lbrakk> l \<in> A\<^sup>\<omega>; a \<in> A; s = a ## l \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof -
  from sinf have "s \<in> A\<^sup>\<infinity>" "s \<notin> UNIV\<^sup>\<star>"
    by auto
  then obtain a l where "l \<in> A\<^sup>\<omega>" and "a\<in>A" and "s = a ## l"
    by (cases "s") auto
  thus ?thesis by (rule R)
qed

lemma inflstsI2: "\<lbrakk>a \<in> A; t \<in> A\<^sup>\<omega>\<rbrakk> \<Longrightarrow> a ## t \<in> A\<^sup>\<omega>"
  by  (auto elim: finlsts.cases)

lemma infT_simp [simp]:
  "r \<in> A\<^sup>\<omega> \<Longrightarrow> r\<in>UNIV\<^sup>\<omega>"
  by auto

lemma  alllstsE [consumes 1, case_names finite infinite]:
  "\<lbrakk> x\<in>A\<^sup>\<infinity>; x \<in> A\<^sup>\<star> \<Longrightarrow> P; x \<in> A\<^sup>\<omega> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto intro: finite_lemma simp: inflsts_def)


lemma fin_inf_cases [case_names finite infinite]:
  "\<lbrakk> r\<in>UNIV\<^sup>\<star> \<Longrightarrow> P; r \<in> UNIV\<^sup>\<omega> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto

lemma  fin_Int_inf: "A\<^sup>\<star> \<inter> A\<^sup>\<omega> = {}"
  and   fin_Un_inf: "A\<^sup>\<star> \<union> A\<^sup>\<omega> = A\<^sup>\<infinity>"
  by (auto intro: finite_lemma finsubsetall)

lemma notfin_inf [iff]: "(x \<notin> UNIV\<^sup>\<star>) = (x \<in> UNIV\<^sup>\<omega>)"
  by auto

lemma notinf_fin [iff]: "(x \<notin> UNIV\<^sup>\<omega>) = (x \<in> UNIV\<^sup>\<star>)"
  by auto


subsection\<open>Lappend\<close>

subsubsection\<open>Simplification\<close>

lemma lapp_inf [simp]:
  assumes "s \<in> A\<^sup>\<omega>"
  shows "s @@ t = s"
using assms
by(coinduction arbitrary: s)(auto elim: inflsts_cases)

lemma LNil_is_lappend_conv [iff]:
"(LNil = s @@ t) = (s = LNil \<and> t = LNil)"
  by (cases "s") auto

lemma lappend_is_LNil_conv [iff]:
  "(s @@ t = LNil) = (s = LNil \<and> t = LNil)"
  by (cases "s") auto

lemma same_lappend_eq [iff]:
 "r \<in> A\<^sup>\<star> \<Longrightarrow> (r @@ s = r @@ t) = (s = t)"
  by (erule finlsts.induct) simp+

subsubsection\<open>Typing rules\<close>

lemma lappT: 
  assumes sllist: "s \<in> A\<^sup>\<infinity>"
  and tllist: "t \<in> A\<^sup>\<infinity>"
  shows "s@@t \<in> A\<^sup>\<infinity>"
proof -
  from assms have "lappend s t \<in> (\<Union>u\<in>A\<^sup>\<infinity>. \<Union>v\<in>A\<^sup>\<infinity>. {lappend u v})" by fast
  thus ?thesis
  proof coinduct
    case (alllsts z)
    then obtain u v where ullist: "u\<in>A\<^sup>\<infinity>" and vllist: "v\<in>A\<^sup>\<infinity>"
      and zapp: "z=u @@ v" by auto
    thus ?case by (cases "u") (auto elim: alllsts.cases)
  qed
qed

lemma lappfin_finT: "\<lbrakk> s \<in> A\<^sup>\<star>; t \<in> A\<^sup>\<star> \<rbrakk> \<Longrightarrow> s@@t \<in> A\<^sup>\<star>"
  by (induct rule: finlsts.induct) auto

lemma lapp_fin_fin_lemma:
  assumes rsA: "r @@ s \<in> A\<^sup>\<star>"
  shows "r \<in> A\<^sup>\<star>"
using rsA
proof(induct l\<equiv>"r@@s" arbitrary: r)
  case LNil_fin thus ?case by auto
next
  case (LCons_fin a l')
  show ?case
  proof (cases "r")
    case LNil thus ?thesis by auto
  next
    case (LCons x xs) with \<open>a##l' = r @@ s\<close>
    have "a = x" and "l' = xs @@ s" by auto
    with LCons_fin LCons show ?thesis by auto
  qed
qed

lemma lapp_fin_fin_iff [iff]: "(r @@ s \<in> A\<^sup>\<star>) = (r \<in> A\<^sup>\<star> \<and> s \<in> A\<^sup>\<star>)"
proof (auto intro: lappfin_finT lapp_fin_fin_lemma)
  assume rsA: "r @@ s \<in> A\<^sup>\<star>"
  hence "r \<in> A\<^sup>\<star>" by (rule lapp_fin_fin_lemma)
  hence "r @@ s \<in> A\<^sup>\<star> \<longrightarrow> s \<in> A\<^sup>\<star>"
    by (induct "r", simp) (auto elim: finlsts.cases)
  with rsA show "s \<in> A\<^sup>\<star>" by auto
qed

lemma lapp_all_invT:
assumes rs: "r@@s \<in> A\<^sup>\<infinity>"
  shows "r \<in> A\<^sup>\<infinity>"
proof (cases "r \<in> UNIV\<^sup>\<star>")
  case False
  with rs show ?thesis by simp
next
  case True
  thus ?thesis using rs
    by (induct "r") auto
qed

lemma lapp_fin_infT: "\<lbrakk>s \<in> A\<^sup>\<star>; t \<in> A\<^sup>\<omega>\<rbrakk> \<Longrightarrow> s @@ t \<in> A\<^sup>\<omega>"
  by (induct rule: finlsts.induct)
     (auto intro: inflstsI2)

lemma app_invT:
  assumes "r \<in> A\<^sup>\<star>" shows "r @@ s \<in> A\<^sup>\<omega> \<Longrightarrow> s \<in> A\<^sup>\<omega>"
using assms
proof (induct arbitrary: s)
  case LNil_fin thus ?case by simp
next
  case (LCons_fin a l)
  from \<open>(a ## l) @@ s \<in> A\<^sup>\<omega>\<close>
  have "a ## (l @@ s) \<in> A\<^sup>\<omega>" by simp
  hence "l @@ s \<in> A\<^sup>\<omega>" by (auto elim: inflsts_cases)
  with LCons_fin show "s \<in> A\<^sup>\<omega>" by blast
qed

lemma lapp_inv2T:
  assumes rsinf: "r @@ s \<in> A\<^sup>\<omega>"
  shows "r \<in> A\<^sup>\<star> \<and> s \<in> A\<^sup>\<omega> \<or> r \<in> A\<^sup>\<omega>"
proof (rule disjCI)
  assume rnotinf: "r \<notin> A\<^sup>\<omega>"
  moreover from rsinf have rsall: "r@@s \<in> A\<^sup>\<infinity>"
    by auto
  hence "r \<in> A\<^sup>\<infinity>" by (rule lapp_all_invT)
  hence "r \<in> A\<^sup>\<star>" using rnotinf by (auto elim: alllstsE)
  ultimately show "r \<in> A\<^sup>\<star> \<and> s \<in> A\<^sup>\<omega>" using rsinf
    by (auto  intro: app_invT)
qed

lemma lapp_infT:
  "(r @@ s \<in> A\<^sup>\<omega>) = (r \<in> A\<^sup>\<star> \<and> s \<in> A\<^sup>\<omega> \<or> r \<in> A\<^sup>\<omega>)"
  by (auto dest: lapp_inv2T intro: lapp_fin_infT)

lemma lapp_allT_iff:
  "(r @@ s \<in> A\<^sup>\<infinity>) = (r \<in> A\<^sup>\<star> \<and> s \<in> A\<^sup>\<infinity> \<or> r \<in> A\<^sup>\<omega>)"
  (is "?L = ?R")
proof
  assume ?L thus ?R by (cases rule: alllstsE) (auto simp: lapp_infT intro: finsubsetall)
next
  assume ?R thus ?L by (auto dest: finsubsetall intro: lappT)
qed

subsection\<open>Length, indexing, prefixes, and suffixes of llists\<close>

primrec ll2f :: "'a llist \<Rightarrow> nat \<Rightarrow> 'a option" (infix "!!" 100)
where
  "l!!0 = (case l of LNil \<Rightarrow> None | x ## xs \<Rightarrow> Some x)"
| "l!!(Suc i) = (case l of LNil \<Rightarrow> None | x ## xs \<Rightarrow> xs!!i)"

primrec ltake :: "'a llist \<Rightarrow> nat \<Rightarrow> 'a llist"  (infixl "\<down>" 110)
where
  "l \<down> 0     = LNil"
| "l \<down> Suc i = (case l of LNil \<Rightarrow> LNil | x ## xs \<Rightarrow> x ## ltake xs i)"

primrec ldrop :: "'a llist \<Rightarrow> nat \<Rightarrow> 'a llist"  (infixl "\<up>" 110)
where
  "l \<up> 0     = l"
| "l \<up> Suc i = (case l of LNil \<Rightarrow> LNil | x ## xs \<Rightarrow> ldrop xs i)"

definition lset :: "'a llist \<Rightarrow> 'a set"
where "lset l \<equiv> ran (ll2f l)"

definition llength :: "'a llist \<Rightarrow> nat"
where "llength \<equiv> finlsts_rec 0 (\<lambda> a r n. Suc n)"

definition llast :: "'a llist \<Rightarrow> 'a"
where "llast \<equiv> finlsts_rec undefined (\<lambda> x xs l. if xs = LNil then x else l)"

definition lbutlast :: "'a llist \<Rightarrow> 'a llist"
where "lbutlast \<equiv> finlsts_rec LNil (\<lambda> x xs l. if xs = LNil then LNil else x##l)"

definition lrev :: "'a llist \<Rightarrow> 'a llist"
where "lrev \<equiv> finlsts_rec LNil (\<lambda> x xs l. l @@ x ## LNil)"

lemmas llength_LNil  = llength_def [THEN finlsts_rec_LNil_def]
  and  llength_LCons = llength_def [THEN finlsts_rec_LCons_def]
lemmas llength_simps [simp] = llength_LNil llength_LCons

lemmas llast_LNil  = llast_def [THEN finlsts_rec_LNil_def]
  and  llast_LCons = llast_def [THEN finlsts_rec_LCons_def]
lemmas llast_simps [simp] = llast_LNil llast_LCons

lemmas lbutlast_LNil = lbutlast_def [THEN finlsts_rec_LNil_def]
  and lbutlast_LCons = lbutlast_def [THEN finlsts_rec_LCons_def]
lemmas lbutlast_simps [simp] = lbutlast_LNil lbutlast_LCons

lemmas lrev_LNil = lrev_def [THEN finlsts_rec_LNil_def]
  and lrev_LCons = lrev_def [THEN finlsts_rec_LCons_def]
lemmas lrev_simps [simp] = lrev_LNil lrev_LCons

lemma lrevT [simp, intro!]:
  "xs \<in> A\<^sup>\<star> \<Longrightarrow> lrev xs \<in> A\<^sup>\<star>"
  by (induct rule: finlsts.induct) auto

lemma lrev_lappend [simp]:
  assumes fin: "xs \<in> UNIV\<^sup>\<star>" "ys \<in> UNIV\<^sup>\<star>"
  shows "lrev (xs @@ ys) = (lrev ys) @@ (lrev xs)"
  using fin
  by induct (auto simp: lrev_LCons [of _ UNIV] lappend_assoc)

lemma lrev_lrev_ident [simp]:
  assumes fin: "xs \<in> UNIV\<^sup>\<star>"
  shows "lrev (lrev xs) = xs"
  using fin
proof (induct)
  case (LCons_fin a l)
  have "a ## LNil \<in> UNIV\<^sup>\<star>" by auto
  thus ?case using LCons_fin
    by auto
qed simp

lemma lrev_is_LNil_conv [iff]:
  "xs \<in> UNIV\<^sup>\<star> \<Longrightarrow> (lrev xs = LNil) = (xs = LNil)"
  by (induct rule: finlsts.induct) auto

lemma LNil_is_lrev_conv [iff]: 
"xs \<in> UNIV\<^sup>\<star> \<Longrightarrow> (LNil = lrev xs) = (xs = LNil)"
by (induct rule: finlsts.induct) auto

lemma lrev_is_lrev_conv [iff]:
assumes fin: "xs \<in> UNIV\<^sup>\<star>" "ys \<in> UNIV\<^sup>\<star>"
  shows "(lrev xs = lrev ys) = (xs = ys)"
  (is "?L = ?R")
proof
  assume L: ?L
  hence "lrev (lrev xs) = lrev (lrev ys)" by simp
  thus ?R using fin by simp
qed simp

lemma lrev_induct [case_names LNil snocl, consumes 1]:
  assumes fin: "xs \<in> A\<^sup>\<star>"
  and init: "P LNil"
  and step: "\<And>x xs. \<lbrakk> xs \<in> A\<^sup>\<star>; P xs; x \<in> A \<rbrakk> \<Longrightarrow> P (xs @@ x##LNil)"
  shows "P xs"
proof-
  define l where "l = lrev xs"
  with fin have "l \<in> A\<^sup>\<star>" by simp
  hence "P (lrev l)"
  proof (induct l)
    case LNil_fin with init show ?case by simp
  next
    case (LCons_fin a l) thus ?case by (auto intro: step)
  qed
  thus ?thesis using fin l_def by simp
qed

lemma finlsts_rev_cases:
  assumes tfin: "t \<in> A\<^sup>\<star>"
  obtains (LNil) "t = LNil"
    |    (snocl) a l where "l \<in> A\<^sup>\<star>" "a \<in> A" "t = l @@ a ## LNil"
  using assms
  by (induct rule: lrev_induct) auto

lemma ll2f_LNil [simp]: "LNil!!x = None"
  by (cases "x") auto

lemma None_lfinite: "t!!i = None \<Longrightarrow> t \<in> UNIV\<^sup>\<star>"
proof (induct "i" arbitrary: t)
  case 0 thus ?case
    by(cases t) auto
next
  case (Suc n)
  show ?case
  proof(cases t)
    case LNil thus ?thesis by auto
  next
    case (LCons x l')
    with \<open>l' !! n = None \<Longrightarrow> l' \<in> UNIV\<^sup>\<star>\<close> \<open>t !! Suc n = None\<close>
    show ?thesis by auto
  qed
qed

lemma infinite_Some: "t \<in> A\<^sup>\<omega> \<Longrightarrow> \<exists>a. t!!i = Some a"
  by (rule ccontr) (auto dest: None_lfinite)

lemmas infinite_idx_SomeE = exE [OF infinite_Some]

lemma Least_True [simp]:
  "(LEAST (n::nat). True) = 0"
  by (auto simp: Least_def)

lemma  ll2f_llength [simp]: "r \<in> A\<^sup>\<star> \<Longrightarrow> r!!(llength r) = None"
  by (erule finlsts.induct) auto

lemma llength_least_None:
  assumes rA: "r \<in> A\<^sup>\<star>"
  shows "llength r = (LEAST i. r!!i = None)"
using rA
proof induct
  case LNil_fin thus ?case by simp
next
  case (LCons_fin a l)
  hence "(LEAST i. (a ## l) !! i = None) = llength (a ## l)"
    by (auto intro!: ll2f_llength Least_Suc2)
  thus ?case by rule
qed

lemma ll2f_lem1:
 "t !! (Suc i) = Some x \<Longrightarrow> \<exists> y. t !! i = Some y"
proof (induct i arbitrary: x t)
  case 0 thus ?case by (auto split: llist.splits)
next
  case (Suc k) thus ?case
    by (cases t) auto
qed

lemmas ll2f_Suc_Some = ll2f_lem1 [THEN exE]

lemma ll2f_None_Suc: "t !! i = None \<Longrightarrow> t !! Suc i = None"
proof (induct i arbitrary: t)
  case 0 thus ?case by (auto split: llist.split)
next
  case (Suc k) thus ?case by (cases t) auto
qed

lemma ll2f_None_le:
  "\<lbrakk> t!!j = None; j \<le> i \<rbrakk> \<Longrightarrow> t!!i = None"
proof (induct i arbitrary: t j)
  case 0 thus ?case by simp
next
  case (Suc k) thus ?case by (cases j) (auto split: llist.split)
qed

lemma ll2f_Some_le:
  assumes jlei: "j \<le> i"
  and tisome: "t !! i = Some x"
  and H: "\<And> y. t !! j = Some y \<Longrightarrow> Q"
  shows "Q"
proof -
  have  "\<exists> y. t !! j = Some y" (is "?R")
  proof (rule ccontr)
    assume "\<not> ?R"
    hence "t !! j = None" by auto
    with tisome jlei show False
      by (auto dest:  ll2f_None_le)
  qed
  thus ?thesis using H by auto
qed

lemma ltake_LNil [simp]: "LNil \<down> i = LNil"
  by (cases "i") auto

lemma ltake_LCons_Suc: "(a ## l) \<down> (Suc i) = a ## l \<down> i"
  by simp

lemma take_fin [iff]: "t \<in> A\<^sup>\<infinity> \<Longrightarrow> t\<down>i \<in> A\<^sup>\<star>"
proof (induct i arbitrary: t)
  case 0 show ?case by auto
next
  case (Suc j) thus ?case
    by (cases "t") auto
qed

lemma ltake_fin [iff]:
  "r \<down> i \<in> UNIV\<^sup>\<star>"
  by simp

lemma llength_take [simp]: "t \<in> A\<^sup>\<omega> \<Longrightarrow> llength (t\<down>i) = i"
proof (induct "i" arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc j)
  from \<open>t \<in> A\<^sup>\<omega>\<close> \<open>\<And>t. t \<in> A\<^sup>\<omega> \<Longrightarrow> llength (t \<down> j) = j\<close> show ?case
    by(cases) (auto simp: llength_LCons [of _ UNIV])
qed

lemma ltake_ldrop_id: "(x \<down> i) @@ (x \<up> i) = x"
proof (induct "i" arbitrary: x)
  case 0 thus ?case by simp
next
  case (Suc j) thus ?case
    by (cases x) auto
qed

lemma ltake_ldrop: 
  "(xs \<up> m) \<down> n =(xs \<down> (n + m)) \<up> m"
proof (induct "m" arbitrary: xs)
  case 0 show ?case by simp
next
  case (Suc l) thus ?case
    by (cases "xs") auto
qed

lemma ldrop_LNil [simp]: "LNil \<up> i = LNil"
  by (cases "i") auto

lemma ldrop_add: "t \<up> (i + k) = t \<up> i \<up> k"
proof (induct "i" arbitrary: t)
  case (Suc j) thus ?case
    by (cases "t") auto
qed simp

lemma ldrop_fun: "t \<up> i !! j = t!!(i + j)"
proof (induct i arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc k) then show ?case
    by (cases "t") auto
qed

lemma ldropT[simp]: "t \<in> A\<^sup>\<infinity> \<Longrightarrow> t \<up> i \<in> A\<^sup>\<infinity>"
proof (induct i arbitrary: t)
  case 0 thus ?case by simp
next case (Suc j)
  thus ?case by (cases "t") auto
qed

lemma ldrop_finT[simp]: "t \<in> A\<^sup>\<star> \<Longrightarrow> t \<up> i \<in> A\<^sup>\<star>"
proof (induct i arbitrary: t)
  case 0 thus ?case by simp
next
  fix n t assume "t \<in> A\<^sup>\<star>" and 
    "\<And>t::'a llist. t \<in> A\<^sup>\<star> \<Longrightarrow> t \<up> n \<in> A\<^sup>\<star>"
  thus "t \<up> Suc n \<in> A\<^sup>\<star>"
    by (cases "t") auto
qed

lemma ldrop_infT[simp]: "t \<in> A\<^sup>\<omega> \<Longrightarrow> t \<up> i \<in> A\<^sup>\<omega>"
proof (induct i arbitrary: t)
  case 0 thus ?case by simp
next
  case (Suc n)
  from \<open>t \<in> A\<^sup>\<omega>\<close> \<open>\<And>t. t \<in> A\<^sup>\<omega> \<Longrightarrow> t \<up> n \<in> A\<^sup>\<omega>\<close> show ?case
    by (cases "t") auto
qed

lemma lapp_suff_llength: "r \<in> A\<^sup>\<star> \<Longrightarrow> (r@@s) \<up> llength r = s"
  by (induct rule: finlsts.induct) auto

lemma ltake_lappend_llength [simp]:
  "r \<in> A\<^sup>\<star> \<Longrightarrow> (r @@ s) \<down> llength r = r"
  by (induct rule: finlsts.induct) auto

lemma ldrop_LNil_less:
  "\<lbrakk>j \<le> i; t \<up> j = LNil\<rbrakk> \<Longrightarrow> t \<up> i = LNil"
proof (induct i arbitrary: j t)
  case 0 thus ?case by auto
next case (Suc n) thus ?case
    by (cases j, simp) (cases t, simp_all)
qed

lemma ldrop_inf_iffT [iff]: "(t \<up> i \<in> UNIV\<^sup>\<omega>)  =  (t \<in> UNIV\<^sup>\<omega>)"
proof
  show "t\<up>i \<in> UNIV\<^sup>\<omega> \<Longrightarrow> t \<in> UNIV\<^sup>\<omega>"
    by (rule ccontr) (auto dest: ldrop_finT)
qed auto

lemma ldrop_fin_iffT [iff]: "(t \<up> i \<in> UNIV\<^sup>\<star>) = (t \<in> UNIV\<^sup>\<star>)"
  by auto

lemma drop_nonLNil: "t\<up>i \<noteq> LNil \<Longrightarrow> t \<noteq> LNil"
  by (auto)

lemma llength_drop_take:
  "t\<up>i \<noteq> LNil \<Longrightarrow> llength (t\<down>i) = i"
proof (induct i arbitrary: t)
  case 0 show ?case by simp
next
  case (Suc j) thus ?case by (cases t) (auto simp: llength_LCons [of _ UNIV])
qed

lemma fps_induct [case_names LNil LCons, induct set: fpslsts, consumes 1]:
  assumes fps: "l \<in> A\<^sup>\<clubsuit>"
  and    init: "\<And>a. a \<in> A \<Longrightarrow> P (a##LNil)"
  and    step: "\<And>a l. \<lbrakk> l \<in> A\<^sup>\<clubsuit>; P l; a \<in> A \<rbrakk> \<Longrightarrow> P (a ## l)"
  shows "P l"
proof-
  from fps have "l \<in> A\<^sup>\<star>" and "l \<noteq> LNil" by auto
  thus ?thesis
    by (induct, simp) (cases, auto intro: init step)
qed

lemma lbutlast_lapp_llast:
assumes "l \<in> A\<^sup>\<clubsuit>"
  shows "l = lbutlast l @@ (llast l ## LNil)"
  using assms by induct auto

lemma llast_snoc [simp]:
  assumes fin: "xs \<in> A\<^sup>\<star>"
  shows "llast (xs @@ x ## LNil) = x"
  using fin
proof induct
  case LNil_fin thus ?case by simp
next
  case (LCons_fin a l) 
  have "x ## LNil \<in> UNIV\<^sup>\<star>" by auto
  with LCons_fin show ?case
    by (auto simp: llast_LCons [of _ UNIV])
qed

lemma lbutlast_snoc [simp]:
  assumes fin: "xs \<in> A\<^sup>\<star>"
  shows "lbutlast (xs @@ x ## LNil) = xs"
  using fin
proof induct
  case LNil_fin thus ?case by simp
next
  case (LCons_fin a l)
  have "x ## LNil \<in> UNIV\<^sup>\<star>" by auto
  with LCons_fin show ?case
    by (auto simp: lbutlast_LCons [of _ UNIV])
qed

lemma llast_lappend [simp]:
"\<lbrakk> x \<in> UNIV\<^sup>\<star>; y \<in> UNIV\<^sup>\<star> \<rbrakk> \<Longrightarrow> llast (x @@ a ## y) = llast (a ## y)"
proof (induct rule: finlsts.induct)
  case LNil_fin thus ?case by simp
next case (LCons_fin l b)
  hence "l @@ a ## y \<in> UNIV\<^sup>\<star>" by auto 
  thus ?case using LCons_fin 
    by (auto simp: llast_LCons [of _ UNIV])
qed

lemma llast_llength:
  assumes tfin: "t \<in> UNIV\<^sup>\<star>"
  shows "t \<noteq> LNil \<Longrightarrow> t !! (llength t - (Suc 0)) = Some (llast t)"
  using tfin
proof induct
  case (LNil_fin l) thus ?case by auto
next
  case (LCons_fin a l) note consal = this thus ?case
  proof (cases l)
    case LNil_fin thus ?thesis using consal by simp
  next
    case (LCons_fin aa la) 
    thus ?thesis using consal by simp
  qed
qed


subsection\<open>The constant llist\<close>

definition lconst :: "'a \<Rightarrow> 'a llist" where
  "lconst a \<equiv> iterates (\<lambda>x. x) a"

lemma lconst_unfold: "lconst a = a ## lconst a"
  by (auto simp: lconst_def intro: iterates)

lemma lconst_LNil [iff]: "lconst a \<noteq> LNil"
  by (clarify,frule subst [OF lconst_unfold]) simp

lemma lconstT:
  assumes aA: "a \<in> A"
  shows "lconst a \<in> A\<^sup>\<omega>"
proof (rule inflstsI)
  show "lconst a \<in> A\<^sup>\<infinity>"
  proof (rule alllsts.coinduct [of "\<lambda>x. x = lconst a"], simp_all)
    have "lconst a = a ## lconst a"
      by (rule lconst_unfold)
    with aA
    show "\<exists>l aa. lconst a = aa ## l \<and> (l = lconst a \<or> l \<in> A\<^sup>\<infinity>) \<and> aa \<in> A"
      by blast
  qed
next assume lconst: "lconst a \<in> UNIV\<^sup>\<star>"
  moreover have "\<And>l. l \<in> UNIV\<^sup>\<star> \<Longrightarrow> lconst a \<noteq> l"
  proof-
    fix l::"'a llist" assume "l\<in>UNIV\<^sup>\<star>"
    thus "lconst a \<noteq> l"
    proof (rule finlsts_induct, simp_all)
      fix a' l' assume 
        al': "lconst a \<noteq> l'" and
        l'A: "l' \<in> UNIV\<^sup>\<star>"
      from al' show  "lconst a \<noteq> a' ## l'"
      proof (rule contrapos_np)
        assume notal: "\<not> lconst a \<noteq> a' ## l'"
        hence "lconst a = a' ## l'" by simp
        hence "a ## lconst a = a' ## l'"
          by (rule subst [OF lconst_unfold])
        thus "lconst a = l'" by auto
      qed
    qed
  qed
  ultimately show "False" using aA by auto
qed


subsection\<open>The prefix order of llists\<close>

instantiation llist :: (type) order
begin

definition
  llist_le_def: "(s :: 'a llist) \<le> t \<longleftrightarrow> (\<exists>d. t = s @@ d)"

definition
  llist_less_def: "(s :: 'a llist) < t \<longleftrightarrow> (s \<le> t \<and> s \<noteq> t)"

lemma not_LCons_le_LNil [iff]:
  "\<not> (a##l) \<le> LNil"
  by (unfold llist_le_def) auto

lemma LNil_le [iff]:"LNil \<le> s"
  by (auto simp: llist_le_def)

lemma le_LNil [iff]: "(s \<le> LNil) = (s = LNil)"
  by (auto simp: llist_le_def)

lemma llist_inf_le:
  "s \<in> A\<^sup>\<omega>  \<Longrightarrow> (s\<le>t) = (s=t)"
  by (unfold llist_le_def) auto

lemma le_LCons [iff]: "(x ## xs \<le> y ## ys) = (x = y \<and> xs \<le> ys)"
  by (unfold llist_le_def) auto

lemma llist_le_refl [iff]:
  "(s:: 'a llist) \<le> s"
  by (unfold llist_le_def) (rule exI [of _ "LNil"], simp)

lemma llist_le_trans [trans]:
  fixes r:: "'a llist"
  shows "r \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> r \<le> t"
  by (auto simp: llist_le_def lappend_assoc)

lemma llist_le_anti_sym:
  fixes s:: "'a llist"
  assumes st: "s \<le> t"
  and ts: "t \<le> s"
  shows "s = t"
proof-
  have "s \<in> UNIV\<^sup>\<infinity>" by auto
  thus ?thesis
  proof (cases rule: alllstsE)
    case finite
    hence "\<forall> t.  s \<le> t \<and> t \<le> s \<longrightarrow> s = t"
    proof (induct rule: finlsts.induct)
      case LNil_fin thus ?case by auto
    next      
      case (LCons_fin l a) show ?case
      proof
        fix t from LCons_fin show  "a ## l \<le> t \<and> t \<le> a ## l \<longrightarrow> a ## l = t"
          by (cases "t") blast+
      qed
    qed
    thus ?thesis using st ts by blast
  next case infinite thus ?thesis using st by (simp add: llist_inf_le)
  qed
qed

lemma llist_less_le_not_le:
  fixes s :: "'a llist"
  shows "(s < t) = (s \<le> t \<and> \<not> t \<le> s)"
  by (auto simp add: llist_less_def dest: llist_le_anti_sym)

instance
  by standard
    (assumption | rule llist_le_refl
      llist_le_trans llist_le_anti_sym llist_less_le_not_le)+

end


subsubsection\<open>Typing rules\<close>

lemma llist_le_finT [simp]:
 "r\<le>s \<Longrightarrow> s \<in> A\<^sup>\<star> \<Longrightarrow> r \<in> A\<^sup>\<star>"
proof-
  assume rs: "r\<le>s" and sfin: "s \<in> A\<^sup>\<star>"
  from sfin have "\<forall>r. r\<le>s \<longrightarrow> r\<in>A\<^sup>\<star>"
  proof (induct "s")
    case LNil_fin thus ?case by auto
  next
    case (LCons_fin a l) show  ?case
    proof (clarify)
      fix r assume ral: "r \<le> a ## l"
      thus "r \<in> A\<^sup>\<star>" using LCons_fin
        by (cases r) auto
    qed
  qed
  with rs show ?thesis by auto
qed

lemma llist_less_finT [iff]:
 "r<s \<Longrightarrow> s \<in> A\<^sup>\<star> \<Longrightarrow> r \<in> A\<^sup>\<star>"
  by (auto simp: less_le)


subsubsection\<open>More simplification rules\<close>

lemma LNil_less_LCons [iff]: "LNil < a ## t"
  by (simp add: less_le)

lemma not_less_LNil [iff]:
  "\<not> r < LNil"
  by (auto simp: less_le)

lemma less_LCons [iff]:
  " (a ## r < b ## t) = (a = b \<and> r < t)"
  by (auto simp: less_le)

lemma llength_mono [iff]:
  assumes"r \<in> A\<^sup>\<star>"
  shows "s<r \<Longrightarrow> llength s < llength r"
  using assms
proof(induct "r" arbitrary: s)
  case LNil_fin thus ?case by simp
next
  case (LCons_fin a l)
  thus ?case
    by (cases s) (auto simp: llength_LCons [of _ UNIV])
qed

lemma le_lappend [iff]: "r \<le> r @@ s"
  by (auto simp: llist_le_def)

lemma take_inf_less:
  "t \<in> UNIV\<^sup>\<omega> \<Longrightarrow> t \<down> i < t"
proof (induct i arbitrary: t)
  case 0 thus ?case by (auto elim: inflsts_cases)
next
  case (Suc i) 
  from \<open>t \<in> UNIV\<^sup>\<omega>\<close> show ?case
  proof (cases "t")
    case (LCons a l) with Suc show ?thesis
      by auto
  qed
qed

lemma lapp_take_less:
  assumes iless: "i < llength r"
  shows "(r @@ s) \<down> i < r"
proof (cases "r \<in> UNIV\<^sup>\<star>")
  case True
  thus ?thesis using iless
  proof(induct i arbitrary: r)
    case 0 thus ?case by (cases "r") auto
  next
    case (Suc j)
    from \<open>r \<in> UNIV\<^sup>\<star>\<close> \<open>Suc j < llength r\<close> \<open>\<And>r. \<lbrakk>r \<in> UNIV\<^sup>\<star>; j < llength r\<rbrakk> \<Longrightarrow> lappend r s \<down> j < r\<close>
    show ?case by (cases) auto
  qed
next
  case False thus ?thesis by (simp add: take_inf_less)
qed


subsubsection\<open>Finite prefixes and infinite suffixes\<close>

definition finpref :: "'a set \<Rightarrow> 'a llist \<Rightarrow> 'a llist set"
where "finpref A s \<equiv> {r. r \<in> A\<^sup>\<star> \<and> r \<le> s}"

definition suff :: "'a set \<Rightarrow> 'a llist \<Rightarrow> 'a llist set"
where "suff A s \<equiv> {r. r \<in> A\<^sup>\<infinity> \<and> s \<le> r}"

definition infsuff :: "'a set \<Rightarrow> 'a llist \<Rightarrow> 'a llist set"
where "infsuff A s \<equiv> {r. r \<in> A\<^sup>\<omega> \<and> s \<le> r}"

definition prefix_closed :: "'a llist set \<Rightarrow> bool"
where "prefix_closed A \<equiv> \<forall> t \<in> A. \<forall> s \<le> t. s \<in> A"

definition pprefix_closed :: "'a llist set \<Rightarrow> bool"
where "pprefix_closed A \<equiv> \<forall> t \<in> A. \<forall> s. s \<le> t \<and> s \<noteq> LNil \<longrightarrow> s \<in> A"

definition suffix_closed :: "'a llist set \<Rightarrow> bool"
where "suffix_closed A \<equiv> \<forall> t \<in> A. \<forall> s. t \<le> s \<longrightarrow> s \<in> A"

lemma finpref_LNil [simp]:
  "finpref A LNil = {LNil}"
  by (auto simp: finpref_def)

lemma finpref_fin: "x \<in> finpref A s \<Longrightarrow> x \<in> A\<^sup>\<star>"
  by (auto simp: finpref_def)

lemma finpref_mono2: "s \<le> t \<Longrightarrow> finpref A s \<subseteq> finpref A t"
  by (unfold finpref_def) (auto dest: llist_le_trans)

lemma suff_LNil [simp]:
  "suff A LNil = A\<^sup>\<infinity>"
  by (simp add: suff_def)

lemma suff_all: "x \<in> suff A s \<Longrightarrow> x \<in> A\<^sup>\<infinity>"
  by (auto simp: suff_def)

lemma suff_mono2: "s \<le> t \<Longrightarrow> suff A t \<subseteq> suff A s"
  by (unfold suff_def) (auto dest: llist_le_trans)

lemma suff_appE:
  assumes rA: "r \<in> A\<^sup>\<star>"
  and  tsuff: "t \<in> suff A r"
  obtains s where "s \<in> A\<^sup>\<infinity>" "t = r@@s"
proof-
  from tsuff obtain s where
    tA: "t \<in> A\<^sup>\<infinity>" and trs: "t = r @@ s"
    by (auto simp: suff_def llist_le_def)
  from rA trs tA have "s \<in> A\<^sup>\<infinity>"
    by (auto simp: lapp_allT_iff)
  thus ?thesis using trs
    by (rule that)
qed

lemma LNil_suff [iff]: "(LNil \<in> suff A s) = (s = LNil)"
  by (auto simp: suff_def)

lemma finpref_suff [dest]:
  "\<lbrakk> r \<in> finpref A t; t\<in>A\<^sup>\<infinity> \<rbrakk> \<Longrightarrow> t \<in> suff A r"
  by (auto simp: finpref_def suff_def)

lemma suff_finpref:
  "\<lbrakk> t \<in> suff A r; r\<in>A\<^sup>\<star> \<rbrakk> \<Longrightarrow> r \<in> finpref A t"
  by (auto simp: finpref_def suff_def)

lemma suff_finpref_iff:
  "\<lbrakk> r\<in>A\<^sup>\<star>; t\<in>A\<^sup>\<infinity> \<rbrakk> \<Longrightarrow> (r \<in> finpref A t) = (t \<in> suff A r)"
  by (auto simp: finpref_def suff_def)

lemma infsuff_LNil [simp]:
  "infsuff A LNil = A\<^sup>\<omega>"
  by (simp add: infsuff_def)

lemma infsuff_inf: "x \<in> infsuff A s \<Longrightarrow> x \<in> A\<^sup>\<omega>"
  by (auto simp: infsuff_def)

lemma infsuff_mono2: "s \<le> t \<Longrightarrow> infsuff A t \<subseteq> infsuff A s"
  by (unfold infsuff_def) (auto dest: llist_le_trans)

lemma infsuff_appE:
  assumes   rA: "r \<in> A\<^sup>\<star>"
  and tinfsuff: "t \<in> infsuff A r"
  obtains s where "s \<in> A\<^sup>\<omega>" "t = r@@s"
proof-
  from tinfsuff obtain s where
    tA: "t \<in> A\<^sup>\<omega>" and trs: "t = r @@ s"
    by (auto simp: infsuff_def llist_le_def)
  from rA trs tA have "s \<in> A\<^sup>\<omega>"
    by (auto dest: app_invT)
  thus ?thesis using trs
    by (rule that)
qed

lemma finpref_infsuff [dest]:
  "\<lbrakk> r \<in> finpref A t; t\<in>A\<^sup>\<omega> \<rbrakk> \<Longrightarrow> t \<in> infsuff A r"
  by (auto simp: finpref_def infsuff_def)

lemma infsuff_finpref:
  "\<lbrakk> t \<in> infsuff A r; r\<in>A\<^sup>\<star> \<rbrakk> \<Longrightarrow> r \<in> finpref A t"
  by (auto simp: finpref_def infsuff_def)

lemma infsuff_finpref_iff [iff]:
  "\<lbrakk> r\<in>A\<^sup>\<star>; t\<in>A\<^sup>\<omega> \<rbrakk> \<Longrightarrow> (t \<in> finpref A r) = (r \<in> infsuff A t)"
  by (auto simp: finpref_def infsuff_def)

lemma prefix_lemma:
  assumes xinf: "x \<in> A\<^sup>\<omega>"
  and yinf: "y \<in> A\<^sup>\<omega>"
  and R: "\<And> s. \<lbrakk> s \<in> A\<^sup>\<star>; s \<le> x\<rbrakk> \<Longrightarrow> s \<le> y"
  shows "x = y"
proof-
  let ?r = "\<lambda>x y. x\<in>A\<^sup>\<omega> \<and> y\<in>A\<^sup>\<omega> \<and> finpref A x \<subseteq> finpref A y"
  have "?r x y" using xinf yinf
    by (auto simp: finpref_def intro: R)
  thus ?thesis
  proof (coinduct rule: llist.coinduct_strong)
    case (Eq_llist a b)
    hence ainf: "a \<in> A\<^sup>\<omega>"
      and binf: "b \<in> A\<^sup>\<omega>" and pref: "finpref A a \<subseteq> finpref A b" by auto
    from ainf show ?case
    proof cases
      case (LCons a' l')
      note acons = this with binf show ?thesis
      proof (cases b)
        case (LCons b' l'')
        with acons pref have "a' = b'" "finpref A l' \<subseteq> finpref A l''"
          by (auto simp: finpref_def)
        thus ?thesis using acons LCons by auto
      qed
    qed
  qed
qed 

lemma inf_neqE:
"\<lbrakk> x \<in>  A\<^sup>\<omega>; y \<in> A\<^sup>\<omega>; x \<noteq> y;
  \<And>s. \<lbrakk> s\<in>A\<^sup>\<star>; s \<le> x; \<not> s \<le> y\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto intro!: prefix_lemma)

lemma pref_locally_linear:
  fixes s::"'a llist"
  assumes sx: "s \<le> x"
  and   tx: "t \<le> x"
  shows "s \<le> t \<or> t \<le> s"
proof-
  have "s \<in> UNIV\<^sup>\<infinity>" by auto
  thus ?thesis
  proof (cases rule: alllstsE)
    case infinite with sx tx show ?thesis
      by (auto simp: llist_inf_le)
  next
    case finite
    thus ?thesis using sx tx
    proof (induct "s" arbitrary: x t)
      case LNil_fin thus ?case by simp
    next
      case (LCons_fin a l)
      note alx = \<open>a ## l \<le> x\<close>
      note tx = \<open>t \<le> x\<close>
      show ?case
      proof(rule disjCI)
        assume tal: "\<not> t \<le> a ## l"
        show "LCons a l \<le> t"
        proof (cases t)
          case LNil thus ?thesis using tal by auto
        next case (LCons b ts) note tcons = this show ?thesis
          proof (cases x)
            case LNil thus ?thesis using alx by auto
          next
            case (LCons c xs)
            from alx  LCons have ac: "a = c" and lxs: "l \<le> xs"
              by auto
            from tx tcons LCons have bc: "b = c" and tsxs: "ts \<le> xs"
              by auto
            from tcons tal ac bc have tsl: "\<not> ts \<le> l"
              by auto
            from LCons_fin lxs tsxs tsl have "l \<le> ts"
              by auto
            with tcons ac bc show ?thesis
              by auto
          qed
        qed
      qed
    qed
  qed
qed

definition pfinpref :: "'a set \<Rightarrow> 'a llist \<Rightarrow> 'a llist set"
where "pfinpref A s \<equiv> finpref A s - {LNil}"

lemma pfinpref_iff [iff]:
  "(x \<in> pfinpref A s) = (x \<in> finpref A s \<and> x \<noteq> LNil)"
  by (auto simp: pfinpref_def)

subsection\<open>Safety and Liveness\<close>

definition infsafety :: "'a set \<Rightarrow> 'a llist set \<Rightarrow> bool"
where "infsafety A P \<equiv> \<forall> t \<in> A\<^sup>\<omega>. (\<forall> r \<in> finpref A t. \<exists> s \<in> A\<^sup>\<omega>. r @@ s \<in> P) \<longrightarrow> t \<in> P"

definition infliveness :: "'a set \<Rightarrow> 'a llist set \<Rightarrow> bool"
where "infliveness A P \<equiv> \<forall> t \<in> A\<^sup>\<star>. \<exists> s \<in> A\<^sup>\<omega>. t @@ s \<in> P"

definition possafety :: "'a set \<Rightarrow> 'a llist set \<Rightarrow> bool"
where "possafety A P \<equiv> \<forall> t \<in> A\<^sup>\<spadesuit>. (\<forall> r \<in> pfinpref A t. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P) \<longrightarrow> t \<in> P"

definition posliveness :: "'a set \<Rightarrow> 'a llist set \<Rightarrow> bool"
where "posliveness A P \<equiv> \<forall> t \<in> A\<^sup>\<clubsuit>. \<exists> s \<in> A\<^sup>\<infinity>. t @@ s \<in> P"

definition safety :: "'a set \<Rightarrow> 'a llist set \<Rightarrow> bool"
where "safety A P \<equiv> \<forall> t \<in> A\<^sup>\<infinity>. (\<forall> r \<in> finpref A t. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P) \<longrightarrow> t \<in> P"

definition liveness :: "'a set \<Rightarrow> 'a llist set \<Rightarrow> bool"
where "liveness A P \<equiv> \<forall> t \<in> A\<^sup>\<star>. \<exists> s \<in> A\<^sup>\<infinity>. t @@ s \<in> P"

lemma safetyI:
  "(\<And>t. \<lbrakk>t \<in>  A\<^sup>\<infinity>; \<forall> r \<in> finpref A t. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P\<rbrakk> \<Longrightarrow> t \<in> P)
  \<Longrightarrow> safety A P"
  by (unfold safety_def) blast

lemma safetyD:
  "\<lbrakk> safety A P;  t \<in> A\<^sup>\<infinity>;
    \<And>r. r \<in> finpref A t \<Longrightarrow> \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P
  \<rbrakk> \<Longrightarrow> t \<in> P"
  by (unfold safety_def) blast

lemma safetyE:
  "\<lbrakk> safety A P;
    \<forall> t \<in> A\<^sup>\<infinity>. (\<forall> r \<in> finpref A t. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P) \<longrightarrow> t \<in> P \<Longrightarrow> R
   \<rbrakk> \<Longrightarrow> R"
  by (unfold safety_def) blast

lemma safety_prefix_closed:
  "safety UNIV P \<Longrightarrow> prefix_closed P"
  by (auto dest!: safetyD
       simp: prefix_closed_def finpref_def llist_le_def lappend_assoc)
    blast

lemma livenessI:
  "(\<And>s. s\<in> A\<^sup>\<star> \<Longrightarrow> \<exists> t \<in> A\<^sup>\<infinity>. s @@ t \<in> P) \<Longrightarrow> liveness A P"
  by (auto simp: liveness_def)

lemma livenessE:
  "\<lbrakk> liveness A P; \<And>t. \<lbrakk>  t \<in> A\<^sup>\<infinity>; s @@ t \<in> P\<rbrakk> \<Longrightarrow> R; s \<notin> A\<^sup>\<star> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp: liveness_def)

lemma possafetyI:
  "(\<And>t. \<lbrakk>t \<in>  A\<^sup>\<spadesuit>; \<forall> r \<in> pfinpref A t. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P\<rbrakk> \<Longrightarrow> t \<in> P)
  \<Longrightarrow> possafety A P"
  by (unfold possafety_def) blast

lemma possafetyD:
  "\<lbrakk> possafety A P;  t \<in> A\<^sup>\<spadesuit>;
    \<And>r. r \<in> pfinpref A t \<Longrightarrow> \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P
  \<rbrakk> \<Longrightarrow> t \<in> P"
  by (unfold possafety_def) blast

lemma possafetyE:
  "\<lbrakk> possafety A P;
    \<forall> t \<in> A\<^sup>\<spadesuit>. (\<forall> r \<in> pfinpref A t. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P) \<longrightarrow> t \<in> P \<Longrightarrow> R
   \<rbrakk> \<Longrightarrow> R"
  by (unfold possafety_def) blast

lemma possafety_pprefix_closed:
  assumes psafety: "possafety UNIV P"
  shows "pprefix_closed P"
unfolding pprefix_closed_def
proof(intro ballI allI impI, erule conjE)
  fix t s assume tP: "t \<in> P" and st: "s \<le> t" and spos: "s \<noteq> LNil"
  from psafety show "s \<in> P"
  proof (rule possafetyD)
    from spos show  "s \<in> UNIV\<^sup>\<spadesuit>" by auto
  next fix r assume "r \<in> pfinpref UNIV s"
    then obtain u where scons: "s = r @@ u"
      by (auto simp: pfinpref_def finpref_def llist_le_def)
    with st obtain v where "t = r @@ u @@ v"
      by (auto simp: lappend_assoc llist_le_def)
    with tP show "\<exists>s\<in>UNIV\<^sup>\<infinity>. r @@ s \<in> P" by auto
  qed
qed

lemma poslivenessI:
  "(\<And>s. s\<in> A\<^sup>\<clubsuit> \<Longrightarrow> \<exists> t \<in> A\<^sup>\<infinity>. s @@ t \<in> P) \<Longrightarrow> posliveness A P"
  by (auto simp: posliveness_def)

lemma poslivenessE:
  "\<lbrakk> posliveness A P; \<And>t. \<lbrakk>  t \<in> A\<^sup>\<infinity>; s @@ t \<in> P\<rbrakk> \<Longrightarrow> R; s \<notin> A\<^sup>\<clubsuit> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp: posliveness_def)

end
