(*  Author:     Tobias Nipkow, 2007  *)

section\<open>Logic\<close>

theory Logic
imports Main "HOL-Library.FuncSet"
begin

text\<open>\noindent
We start with a generic formalization of quantified logical formulae
using de Bruijn notation. The syntax is parametric in the type of atoms.\<close>

declare Let_def[simp]

datatype (atoms: 'a) fm =
  TrueF | FalseF | Atom 'a | And "'a fm" "'a fm" | Or "'a fm" "'a fm" |
  Neg "'a fm" | ExQ "'a fm"

notation map_fm ("map\<^sub>f\<^sub>m")

abbreviation Imp where "Imp \<phi>\<^sub>1 \<phi>\<^sub>2 \<equiv> Or (Neg \<phi>\<^sub>1) \<phi>\<^sub>2"
abbreviation AllQ where "AllQ \<phi> \<equiv> Neg(ExQ(Neg \<phi>))"

definition neg where
"neg \<phi> = (if \<phi>=TrueF then FalseF else if \<phi>=FalseF then TrueF else Neg \<phi>)"

definition "and" :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
"and \<phi>\<^sub>1 \<phi>\<^sub>2 =
 (if \<phi>\<^sub>1=TrueF then \<phi>\<^sub>2 else if \<phi>\<^sub>2=TrueF then \<phi>\<^sub>1 else
  if \<phi>\<^sub>1=FalseF \<or> \<phi>\<^sub>2=FalseF then FalseF else And \<phi>\<^sub>1 \<phi>\<^sub>2)"

definition or :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
"or \<phi>\<^sub>1 \<phi>\<^sub>2 =
 (if \<phi>\<^sub>1=FalseF then \<phi>\<^sub>2 else if \<phi>\<^sub>2=FalseF then \<phi>\<^sub>1 else
  if \<phi>\<^sub>1=TrueF \<or> \<phi>\<^sub>2=TrueF then TrueF else Or \<phi>\<^sub>1 \<phi>\<^sub>2)"

definition list_conj :: "'a fm list \<Rightarrow> 'a fm" where
"list_conj fs = foldr and fs TrueF"

definition list_disj :: "'a fm list \<Rightarrow> 'a fm" where
"list_disj fs = foldr or fs FalseF"

abbreviation "Disj is f \<equiv> list_disj (map f is)"

lemmas atoms_map_fm[simp] = fm.set_map

fun amap_fm :: "('a \<Rightarrow> 'b fm) \<Rightarrow> 'a fm \<Rightarrow> 'b fm" ("amap\<^sub>f\<^sub>m") where
"amap\<^sub>f\<^sub>m h TrueF = TrueF" |
"amap\<^sub>f\<^sub>m h FalseF = FalseF" |
"amap\<^sub>f\<^sub>m h (Atom a) = h a" |
"amap\<^sub>f\<^sub>m h (And \<phi>\<^sub>1 \<phi>\<^sub>2) = and (amap\<^sub>f\<^sub>m h \<phi>\<^sub>1) (amap\<^sub>f\<^sub>m h \<phi>\<^sub>2)" |
"amap\<^sub>f\<^sub>m h (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = or (amap\<^sub>f\<^sub>m h \<phi>\<^sub>1) (amap\<^sub>f\<^sub>m h \<phi>\<^sub>2)" |
"amap\<^sub>f\<^sub>m h (Neg \<phi>) = neg (amap\<^sub>f\<^sub>m h \<phi>)"

lemma amap_fm_list_disj:
  "amap\<^sub>f\<^sub>m h (list_disj fs) = list_disj (map (amap\<^sub>f\<^sub>m h) fs)"
by(induct fs) (auto simp:list_disj_def or_def)

fun qfree :: "'a fm \<Rightarrow> bool" where
"qfree(ExQ f) = False" |
"qfree(And \<phi>\<^sub>1 \<phi>\<^sub>2) = (qfree \<phi>\<^sub>1 \<and> qfree \<phi>\<^sub>2)" |
"qfree(Or \<phi>\<^sub>1 \<phi>\<^sub>2) = (qfree \<phi>\<^sub>1 \<and> qfree \<phi>\<^sub>2)" |
"qfree(Neg \<phi>) = (qfree \<phi>)" |
"qfree \<phi> = True"

lemma qfree_and[simp]: "\<lbrakk> qfree \<phi>\<^sub>1; qfree \<phi>\<^sub>2 \<rbrakk> \<Longrightarrow> qfree(and \<phi>\<^sub>1 \<phi>\<^sub>2)"
by(simp add:and_def)

lemma qfree_or[simp]: "\<lbrakk> qfree \<phi>\<^sub>1; qfree \<phi>\<^sub>2 \<rbrakk> \<Longrightarrow> qfree(or \<phi>\<^sub>1 \<phi>\<^sub>2)"
by(simp add:or_def)

lemma qfree_neg[simp]: "qfree(neg \<phi>) = qfree \<phi>"
by(simp add:neg_def)

lemma qfree_foldr_Or[simp]:
 "qfree(foldr Or fs \<phi>) = (qfree \<phi> \<and> (\<forall>\<phi> \<in> set fs. qfree \<phi>))"
by (induct fs) auto

lemma qfree_list_conj[simp]:
assumes "\<forall>\<phi> \<in> set fs. qfree \<phi>" shows "qfree(list_conj fs)"
proof -
  { fix fs \<phi>
    have "\<lbrakk> \<forall>\<phi> \<in> set fs. qfree \<phi>; qfree \<phi> \<rbrakk> \<Longrightarrow> qfree(foldr and fs \<phi>)"
      by (induct fs) auto
  } thus ?thesis using assms by (fastforce simp add:list_conj_def)
qed

lemma qfree_list_disj[simp]:
assumes "\<forall>\<phi> \<in> set fs. qfree \<phi>" shows "qfree(list_disj fs)"
proof -
  { fix fs \<phi>
    have "\<lbrakk> \<forall>\<phi> \<in> set fs. qfree \<phi>; qfree \<phi> \<rbrakk> \<Longrightarrow> qfree(foldr or fs \<phi>)"
      by (induct fs) auto
  } thus ?thesis using assms by (fastforce simp add:list_disj_def)
qed

lemma qfree_map_fm: "qfree (map\<^sub>f\<^sub>m f \<phi>) = qfree \<phi>"
by (induct \<phi>) simp_all

lemma atoms_list_disjE:
  "a \<in> atoms(list_disj fs) \<Longrightarrow> a \<in> (\<Union>\<phi> \<in> set fs. atoms \<phi>)"
apply(induct fs)
 apply (simp add:list_disj_def)
apply (auto simp add:list_disj_def Logic.or_def split:if_split_asm)
done

lemma atoms_list_conjE:
  "a \<in> atoms(list_conj fs) \<Longrightarrow> a \<in> (\<Union>\<phi> \<in> set fs. atoms \<phi>)"
apply(induct fs)
 apply (simp add:list_conj_def)
apply (auto simp add:list_conj_def Logic.and_def split:if_split_asm)
done


fun dnf :: "'a fm \<Rightarrow> 'a list list" where
"dnf TrueF = [[]]" |
"dnf FalseF = []" |
"dnf (Atom \<phi>) = [[\<phi>]]" |
"dnf (And \<phi>\<^sub>1 \<phi>\<^sub>2) = [d1 @ d2. d1 \<leftarrow> dnf \<phi>\<^sub>1, d2 \<leftarrow> dnf \<phi>\<^sub>2]" |
"dnf (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = dnf \<phi>\<^sub>1 @ dnf \<phi>\<^sub>2"

fun nqfree :: "'a fm \<Rightarrow> bool" where
"nqfree(Atom a) = True" |
"nqfree TrueF = True" |
"nqfree FalseF = True" |
"nqfree (And \<phi>\<^sub>1 \<phi>\<^sub>2) = (nqfree \<phi>\<^sub>1 \<and> nqfree \<phi>\<^sub>2)" |
"nqfree (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = (nqfree \<phi>\<^sub>1 \<and> nqfree \<phi>\<^sub>2)" |
"nqfree \<phi> = False"

lemma nqfree_qfree[simp]: "nqfree \<phi> \<Longrightarrow> qfree \<phi>"
by (induct \<phi>) simp_all

lemma nqfree_map_fm: "nqfree (map\<^sub>f\<^sub>m f \<phi>) = nqfree \<phi>"
by (induct \<phi>) simp_all


fun "interpret" :: "('a \<Rightarrow> 'b list \<Rightarrow> bool) \<Rightarrow> 'a fm \<Rightarrow> 'b list \<Rightarrow> bool" where
"interpret h TrueF xs = True" |
"interpret h FalseF xs = False" |
"interpret h (Atom a) xs = h a xs" |
"interpret h (And \<phi>\<^sub>1 \<phi>\<^sub>2) xs = (interpret h \<phi>\<^sub>1 xs \<and> interpret h \<phi>\<^sub>2 xs)" |
"interpret h (Or \<phi>\<^sub>1 \<phi>\<^sub>2) xs = (interpret h \<phi>\<^sub>1 xs \<or> interpret h \<phi>\<^sub>2 xs)" |
"interpret h (Neg \<phi>) xs = (\<not> interpret h \<phi> xs)" |
"interpret h (ExQ \<phi>) xs = (\<exists>x. interpret h \<phi> (x#xs))"

subsection\<open>Atoms\<close>

text\<open>The locale ATOM of atoms provides a minimal framework for the
generic formulation of theory-independent algorithms, in particular
quantifier elimination.\<close>

locale ATOM =
fixes aneg :: "'a \<Rightarrow> 'a fm"
fixes anormal :: "'a \<Rightarrow> bool"
assumes nqfree_aneg: "nqfree(aneg a)"
assumes anormal_aneg: "anormal a \<Longrightarrow> \<forall>b\<in>atoms(aneg a). anormal b"

fixes I\<^sub>a :: "'a \<Rightarrow> 'b list \<Rightarrow> bool"
assumes I\<^sub>a_aneg: "interpret I\<^sub>a (aneg a) xs = (\<not> I\<^sub>a a xs)"

fixes depends\<^sub>0 :: "'a \<Rightarrow> bool"
and decr :: "'a \<Rightarrow> 'a" 
assumes not_dep_decr: "\<not>depends\<^sub>0 a \<Longrightarrow> I\<^sub>a a (x#xs) = I\<^sub>a (decr a) xs"
assumes anormal_decr: "\<not> depends\<^sub>0 a \<Longrightarrow> anormal a \<Longrightarrow> anormal(decr a)"

begin

fun atoms\<^sub>0 :: "'a fm \<Rightarrow> 'a list" where
"atoms\<^sub>0 TrueF = []" |
"atoms\<^sub>0 FalseF = []" |
"atoms\<^sub>0 (Atom a) = (if depends\<^sub>0 a then [a] else [])" |
"atoms\<^sub>0 (And \<phi>\<^sub>1 \<phi>\<^sub>2) = atoms\<^sub>0 \<phi>\<^sub>1 @ atoms\<^sub>0 \<phi>\<^sub>2" |
"atoms\<^sub>0 (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = atoms\<^sub>0 \<phi>\<^sub>1 @ atoms\<^sub>0 \<phi>\<^sub>2" |
"atoms\<^sub>0 (Neg \<phi>) = atoms\<^sub>0 \<phi>"

abbreviation I where "I \<equiv> interpret I\<^sub>a"

fun nnf :: "'a fm \<Rightarrow> 'a fm" where
"nnf (And \<phi>\<^sub>1 \<phi>\<^sub>2) = And (nnf \<phi>\<^sub>1) (nnf \<phi>\<^sub>2)" |
"nnf (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = Or (nnf \<phi>\<^sub>1) (nnf \<phi>\<^sub>2)" |
"nnf (Neg TrueF) = FalseF" |
"nnf (Neg FalseF) = TrueF" |
"nnf (Neg (Neg \<phi>)) = (nnf \<phi>)" |
"nnf (Neg (And \<phi>\<^sub>1 \<phi>\<^sub>2)) = (Or (nnf (Neg \<phi>\<^sub>1)) (nnf (Neg \<phi>\<^sub>2)))" |
"nnf (Neg (Or \<phi>\<^sub>1 \<phi>\<^sub>2)) = (And (nnf (Neg \<phi>\<^sub>1)) (nnf (Neg \<phi>\<^sub>2)))" |
"nnf (Neg (Atom a)) = aneg a" |
"nnf \<phi> = \<phi>"

lemma nqfree_nnf: "qfree \<phi> \<Longrightarrow> nqfree(nnf \<phi>)"
by(induct \<phi> rule:nnf.induct)
  (simp_all add: nqfree_aneg and_def or_def)

lemma qfree_nnf[simp]: "qfree(nnf \<phi>) = qfree \<phi>"
by (induct \<phi> rule:nnf.induct)(simp_all add: nqfree_aneg)


lemma I_neg[simp]: "I (neg \<phi>) xs = I (Neg \<phi>) xs"
by(simp add:neg_def)

lemma I_and[simp]: "I (and \<phi>\<^sub>1 \<phi>\<^sub>2) xs = I (And \<phi>\<^sub>1 \<phi>\<^sub>2) xs"
by(simp add:and_def)

lemma I_list_conj[simp]:
 "I (list_conj fs) xs = (\<forall>\<phi> \<in> set fs. I \<phi> xs)"
proof -
  { fix fs \<phi>
    have "I (foldr and fs \<phi>) xs = (I \<phi> xs \<and> (\<forall>\<phi> \<in> set fs. I \<phi> xs))"
      by (induct fs) auto
  } thus ?thesis by(simp add:list_conj_def)
qed

lemma I_or[simp]: "I (or \<phi>\<^sub>1 \<phi>\<^sub>2) xs = I (Or \<phi>\<^sub>1 \<phi>\<^sub>2) xs"
by(simp add:or_def)

lemma I_list_disj[simp]:
 "I (list_disj fs) xs = (\<exists>\<phi> \<in> set fs. I \<phi> xs)"
proof -
  { fix fs \<phi>
    have "I (foldr or fs \<phi>) xs = (I \<phi> xs \<or> (\<exists>\<phi> \<in> set fs. I \<phi> xs))"
      by (induct fs) auto
  } thus ?thesis by(simp add:list_disj_def)
qed

lemma I_nnf: "I (nnf \<phi>) xs = I \<phi> xs"
by(induct rule:nnf.induct)(simp_all add: I\<^sub>a_aneg)

lemma I_dnf:
"nqfree \<phi> \<Longrightarrow> (\<exists>as\<in>set (dnf \<phi>). \<forall>a\<in>set as. I\<^sub>a a xs) = I \<phi> xs"
by (induct \<phi>) (fastforce)+

definition "normal \<phi> = (\<forall>a \<in> atoms \<phi>. anormal a)"

lemma normal_simps[simp]:
"normal TrueF"
"normal FalseF"
"normal (Atom a) \<longleftrightarrow> anormal a"
"normal (And \<phi>\<^sub>1 \<phi>\<^sub>2) \<longleftrightarrow> normal \<phi>\<^sub>1 \<and> normal \<phi>\<^sub>2"
"normal (Or \<phi>\<^sub>1 \<phi>\<^sub>2) \<longleftrightarrow> normal \<phi>\<^sub>1 \<and> normal \<phi>\<^sub>2"
"normal (Neg \<phi>) \<longleftrightarrow> normal \<phi>"
"normal (ExQ \<phi>) \<longleftrightarrow> normal \<phi>"
by(auto simp:normal_def)

lemma normal_aneg[simp]: "anormal a \<Longrightarrow> normal (aneg a)"
by (simp add:anormal_aneg normal_def)

lemma normal_and[simp]:
  "normal \<phi>\<^sub>1 \<Longrightarrow> normal \<phi>\<^sub>2 \<Longrightarrow> normal (and \<phi>\<^sub>1 \<phi>\<^sub>2)"
by (simp add:Logic.and_def)

lemma normal_or[simp]:
  "normal \<phi>\<^sub>1 \<Longrightarrow> normal \<phi>\<^sub>2 \<Longrightarrow> normal (or \<phi>\<^sub>1 \<phi>\<^sub>2)"
by (simp add:Logic.or_def)

lemma normal_list_disj[simp]:
  "\<forall>\<phi>\<in>set fs. normal \<phi> \<Longrightarrow> normal (list_disj fs)"
apply(induct fs)
 apply (simp add:list_disj_def)
apply (simp add:list_disj_def)
done

lemma normal_nnf: "normal \<phi> \<Longrightarrow> normal(nnf \<phi>)"
by(induct \<phi> rule:nnf.induct) simp_all

lemma normal_map_fm:
  "\<forall>a. anormal(f a) = anormal(a) \<Longrightarrow> normal (map\<^sub>f\<^sub>m f \<phi>) = normal \<phi>"
by(induct \<phi>) auto


lemma anormal_nnf:
  "qfree \<phi> \<Longrightarrow> normal \<phi> \<Longrightarrow> \<forall>a\<in>atoms(nnf \<phi>). anormal a"
apply(induct \<phi> rule:nnf.induct)
apply(unfold normal_def)
apply(simp_all)
apply (blast dest:anormal_aneg)+
done

lemma atoms_dnf: "nqfree \<phi> \<Longrightarrow> as \<in> set(dnf \<phi>) \<Longrightarrow> a \<in> set as \<Longrightarrow> a \<in> atoms \<phi>"
by(induct \<phi> arbitrary: as a rule:nqfree.induct)(auto)

lemma anormal_dnf_nnf:
  "as \<in> set(dnf(nnf \<phi>)) \<Longrightarrow> qfree \<phi> \<Longrightarrow> normal \<phi> \<Longrightarrow> a \<in> set as \<Longrightarrow> anormal a"
apply(induct \<phi> arbitrary: a as rule:nnf.induct)
            apply(simp_all add: normal_def)
    apply clarify
    apply (metis UnE set_append)
   apply metis
  apply metis
 apply fastforce
apply (metis anormal_aneg atoms_dnf nqfree_aneg)
done

end

end
