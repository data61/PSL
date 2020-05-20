(*
  File:     Regexp_Constructions.thy
  Author:   Manuel Eberl <eberlm@in.tum.de>

  Some simple constructions on regular expressions to illustrate closure properties of regular
  languages: reversal, substitution, prefixes, suffixes, subwords ("fragments")
*)
section \<open>Basic constructions on regular expressions\<close>
theory Regexp_Constructions
imports
  Main
  "HOL-Library.Sublist"
  Regular_Exp
begin

subsection \<open>Reverse language\<close>

lemma rev_conc [simp]: "rev ` (A @@ B) = rev ` B @@ rev ` A"
  unfolding conc_def image_def by force

lemma rev_compower [simp]: "rev ` (A ^^ n) = (rev ` A) ^^ n"
  by (induction n) (simp_all add: conc_pow_comm)

lemma rev_star [simp]: "rev ` star A = star (rev ` A)"
  by (simp add: star_def image_UN)


subsection \<open>Substituting characters in a language\<close>    

definition subst_word :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "subst_word f xs = concat (map f xs)"
  
lemma subst_word_Nil [simp]: "subst_word f [] = []"
  by (simp add: subst_word_def)
    
lemma subst_word_singleton [simp]: "subst_word f [x] = f x"
  by (simp add: subst_word_def)
    
lemma subst_word_append [simp]: "subst_word f (xs @ ys) = subst_word f xs @ subst_word f ys"
  by (simp add: subst_word_def)
    
lemma subst_word_Cons [simp]: "subst_word f (x # xs) = f x @ subst_word f xs"
  by (simp add: subst_word_def)
    
lemma subst_word_conc [simp]: "subst_word f ` (A @@ B) = subst_word f ` A @@ subst_word f ` B"
  unfolding conc_def image_def by force 

lemma subst_word_compower [simp]: "subst_word f ` (A ^^ n) = (subst_word f ` A) ^^ n"
  by (induction n) simp_all
    
lemma subst_word_star [simp]: "subst_word f ` (star A) = star (subst_word f ` A)"
  by (simp add: star_def image_UN)
    

text \<open>Suffix language\<close>

definition Suffixes :: "'a list set \<Rightarrow> 'a list set" where
  "Suffixes A = {w. \<exists>q. q @ w \<in> A}"

lemma Suffixes_altdef [code]: "Suffixes A = (\<Union>w\<in>A. set (suffixes w))"
  unfolding Suffixes_def set_suffixes_eq suffix_def by blast

lemma Nil_in_Suffixes_iff [simp]: "[] \<in> Suffixes A \<longleftrightarrow> A \<noteq> {}"
  by (auto simp: Suffixes_def)

lemma Suffixes_empty [simp]: "Suffixes {} = {}"
  by (auto simp: Suffixes_def)
    
lemma Suffixes_empty_iff [simp]: "Suffixes A = {} \<longleftrightarrow> A = {}"
  by (auto simp: Suffixes_altdef)
    
lemma Suffixes_singleton [simp]: "Suffixes {xs} = set (suffixes xs)"
  by (auto simp: Suffixes_altdef)
    
lemma Suffixes_insert: "Suffixes (insert xs A) = set (suffixes xs) \<union> Suffixes A"
  by (simp add: Suffixes_altdef)

lemma Suffixes_conc [simp]: "A \<noteq> {} \<Longrightarrow> Suffixes (A @@ B) = Suffixes B \<union> (Suffixes A @@ B)"
  unfolding Suffixes_altdef conc_def by (force simp: suffix_append)
    
lemma Suffixes_union [simp]: "Suffixes (A \<union> B) = Suffixes A \<union> Suffixes B"
  by (auto simp: Suffixes_def)
  
lemma Suffixes_UNION [simp]: "Suffixes (\<Union>(f ` A)) = \<Union>((\<lambda>x. Suffixes (f x)) ` A)"
  by (auto simp: Suffixes_def)

lemma Suffixes_compower: 
  assumes "A \<noteq> {}"
  shows   "Suffixes (A ^^ n) = insert [] (Suffixes A @@ (\<Union>k<n. A ^^ k))"
proof (induction n)
  case (Suc n)
  from Suc have "Suffixes (A ^^ Suc n) = 
                   insert [] (Suffixes A @@ ((\<Union>k<n. A ^^ k) \<union> A ^^ n))"
    by (simp_all add: assms conc_Un_distrib)
  also have "(\<Union>k<n. A ^^ k) \<union> A ^^ n = (\<Union>k\<in>insert n {..<n}. A ^^ k)"  by blast
  also have "insert n {..<n} = {..<Suc n}" by auto
  finally show ?case .
qed simp_all

lemma Suffixes_star [simp]: 
  assumes "A \<noteq> {}"
  shows   "Suffixes (star A) = Suffixes A @@ star A"
proof -
  have "star A = (\<Union>n. A ^^ n)" unfolding star_def ..
  also have "Suffixes \<dots> = (\<Union>x. Suffixes (A ^^ x))" by simp
  also have "\<dots> = (\<Union>n. insert [] (Suffixes A @@ (\<Union>k<n. A ^^ k)))"
    using assms by (subst Suffixes_compower) auto
  also have "\<dots> = insert [] (Suffixes A @@ (\<Union>n. (\<Union>k<n. A ^^ k)))"
    by (simp_all add: conc_UNION_distrib)
  also have "(\<Union>n. (\<Union>k<n. A ^^ k)) = (\<Union>n. A ^^ n)" by auto
  also have "\<dots> = star A" unfolding star_def ..
  also have "insert [] (Suffixes A @@ star A) = Suffixes A @@ star A" 
    using assms by auto
  finally show ?thesis .
qed
  
text \<open>Prefix language\<close>

definition Prefixes :: "'a list set \<Rightarrow> 'a list set" where
  "Prefixes A = {w. \<exists>q. w @ q \<in> A}"

lemma Prefixes_altdef [code]: "Prefixes A = (\<Union>w\<in>A. set (prefixes w))"
  unfolding Prefixes_def set_prefixes_eq prefix_def by blast

lemma Nil_in_Prefixes_iff [simp]: "[] \<in> Prefixes A \<longleftrightarrow> A \<noteq> {}"
  by (auto simp: Prefixes_def)

lemma Prefixes_empty [simp]: "Prefixes {} = {}"
  by (auto simp: Prefixes_def)
    
lemma Prefixes_empty_iff [simp]: "Prefixes A = {} \<longleftrightarrow> A = {}"
  by (auto simp: Prefixes_altdef)
    
lemma Prefixes_singleton [simp]: "Prefixes {xs} = set (prefixes xs)"
  by (auto simp: Prefixes_altdef)
    
lemma Prefixes_insert: "Prefixes (insert xs A) = set (prefixes xs) \<union> Prefixes A"
  by (simp add: Prefixes_altdef)

lemma Prefixes_conc [simp]: "B \<noteq> {} \<Longrightarrow> Prefixes (A @@ B) = Prefixes A \<union> (A @@ Prefixes B)"
  unfolding Prefixes_altdef conc_def by (force simp: prefix_append)
    
lemma Prefixes_union [simp]: "Prefixes (A \<union> B) = Prefixes A \<union> Prefixes B"
  by (auto simp: Prefixes_def)
  
lemma Prefixes_UNION [simp]: "Prefixes (\<Union>(f ` A)) = \<Union>((\<lambda>x. Prefixes (f x)) ` A)"
  by (auto simp: Prefixes_def)


lemma Prefixes_rev: "Prefixes (rev ` A) = rev ` Suffixes A"
  by (auto simp: Prefixes_altdef prefixes_rev Suffixes_altdef)

lemma Suffixes_rev: "Suffixes (rev ` A) = rev ` Prefixes A"
  by (auto simp: Prefixes_altdef suffixes_rev Suffixes_altdef)    


lemma Prefixes_compower:
  assumes "A \<noteq> {}"
  shows   "Prefixes (A ^^ n) = insert [] ((\<Union>k<n. A ^^ k) @@ Prefixes A)"
proof -
  have "A ^^ n = rev ` ((rev ` A) ^^ n)" by (simp add: image_image)
  also have "Prefixes \<dots> = insert [] ((\<Union>k<n. A ^^ k) @@ Prefixes A)"
    unfolding Prefixes_rev 
    by (subst Suffixes_compower) (simp_all add: image_UN image_image Suffixes_rev assms)
  finally show ?thesis .
qed

lemma Prefixes_star [simp]:
  assumes "A \<noteq> {}"
  shows   "Prefixes (star A) = star A @@ Prefixes A"
proof -
  have "star A = rev ` star (rev ` A)" by (simp add: image_image)
  also have "Prefixes \<dots> = star A @@ Prefixes A"
    unfolding Prefixes_rev
    by (subst Suffixes_star) (simp_all add: assms image_image Suffixes_rev)
  finally show ?thesis .
qed
  

subsection \<open>Subword language\<close>

text \<open>
  The language of all sub-words, i.e. all words that are a contiguous sublist of a word in
  the original language.
\<close>
definition Sublists :: "'a list set \<Rightarrow> 'a list set" where
  "Sublists A = {w. \<exists>q\<in>A. sublist w q}"

lemma Sublists_altdef [code]: "Sublists A = (\<Union>w\<in>A. set (sublists w))"
  by (auto simp: Sublists_def)

lemma Sublists_empty [simp]: "Sublists {} = {}"
  by (auto simp: Sublists_def)
    
lemma Sublists_singleton [simp]: "Sublists {w} = set (sublists w)"
  by (auto simp: Sublists_altdef)

lemma Sublists_insert: "Sublists (insert w A) = set (sublists w) \<union> Sublists A"
  by (auto simp: Sublists_altdef)
    
lemma Sublists_Un [simp]: "Sublists (A \<union> B) = Sublists A \<union> Sublists B"
  by (auto simp: Sublists_altdef)

lemma Sublists_UN [simp]: "Sublists (\<Union>(f ` A)) = \<Union>((\<lambda>x. Sublists (f x)) ` A)"
  by (auto simp: Sublists_altdef)

lemma Sublists_conv_Prefixes: "Sublists A = Prefixes (Suffixes A)"
  by (auto simp: Sublists_def Prefixes_def Suffixes_def sublist_def)
    
lemma Sublists_conv_Suffixes: "Sublists A = Suffixes (Prefixes A)"
  by (auto simp: Sublists_def Prefixes_def Suffixes_def sublist_def)

lemma Sublists_conc [simp]: 
  assumes "A \<noteq> {}" "B \<noteq> {}"
  shows   "Sublists (A @@ B) = Sublists A \<union> Sublists B \<union> Suffixes A @@ Prefixes B"
  using assms unfolding Sublists_conv_Suffixes by auto

lemma star_not_empty [simp]: "star A \<noteq> {}"
  by auto
    
lemma Sublists_star:
  "A \<noteq> {} \<Longrightarrow> Sublists (star A) = Sublists A \<union> Suffixes A @@ star A @@ Prefixes A"
  by (simp add: Sublists_conv_Prefixes)

lemma Prefixes_subset_Sublists: "Prefixes A \<subseteq> Sublists A"
  unfolding Prefixes_def Sublists_def by auto

lemma Suffixes_subset_Sublists: "Suffixes A \<subseteq> Sublists A"
  unfolding Suffixes_def Sublists_def by auto


subsection \<open>Fragment language\<close>
  
text \<open>
  The following is the fragment language of a given language, i.e. the set of all words that
  are (not necessarily contiguous) sub-sequences of a word in the original language.
\<close>
definition Subseqs where "Subseqs A = (\<Union>w\<in>A. set (subseqs w))"

lemma Subseqs_empty [simp]: "Subseqs {} = {}"
  by (simp add: Subseqs_def)

lemma Subseqs_insert [simp]: "Subseqs (insert xs A) = set (subseqs xs) \<union> Subseqs A"
  by (simp add: Subseqs_def)
    
lemma Subseqs_singleton [simp]: "Subseqs {xs} = set (subseqs xs)"
  by simp
    
lemma Subseqs_Un [simp]: "Subseqs (A \<union> B) = Subseqs A \<union> Subseqs B"
  by (simp add: Subseqs_def)
    
lemma Subseqs_UNION [simp]: "Subseqs (\<Union>(f ` A)) = \<Union>((\<lambda>x. Subseqs (f x)) ` A)"
  by (simp add: Subseqs_def)
  
lemma Subseqs_conc [simp]: "Subseqs (A @@ B) = Subseqs A @@ Subseqs B"
proof safe
  fix xs assume "xs \<in> Subseqs (A @@ B)"
  then obtain ys zs where *: "ys \<in> A" "zs \<in> B" "subseq xs (ys @ zs)" 
    by (auto simp: Subseqs_def conc_def)
  from *(3) obtain xs1 xs2 where "xs = xs1 @ xs2" "subseq xs1 ys" "subseq xs2 zs"
    by (rule subseq_appendE)
  with *(1,2) show "xs \<in> Subseqs A @@ Subseqs B" by (auto simp: Subseqs_def set_subseqs_eq)
next
  fix xs assume "xs \<in> Subseqs A @@ Subseqs B"
  then obtain xs1 xs2 ys zs 
    where "xs = xs1 @ xs2" "subseq xs1 ys" "subseq xs2 zs" "ys \<in> A" "zs \<in> B"
    by (auto simp: conc_def Subseqs_def)
  thus "xs \<in> Subseqs (A @@ B)" by (force simp: Subseqs_def conc_def intro: list_emb_append_mono)
qed

lemma Subseqs_compower [simp]: "Subseqs (A ^^ n) = Subseqs A ^^ n"
  by (induction n) simp_all
    
lemma Subseqs_star [simp]: "Subseqs (star A) = star (Subseqs A)"
  by (simp add: star_def)
    
lemma Sublists_subset_Subseqs: "Sublists A \<subseteq> Subseqs A"
  by (auto simp: Sublists_def Subseqs_def dest!: sublist_imp_subseq)


subsection \<open>Various regular expression constructions\<close>

text \<open>A construction for language reversal of a regular expression:\<close>

primrec rexp_rev where
  "rexp_rev Zero = Zero"
| "rexp_rev One = One"
| "rexp_rev (Atom x) = Atom x"
| "rexp_rev (Plus r s) = Plus (rexp_rev r) (rexp_rev s)"
| "rexp_rev (Times r s) = Times (rexp_rev s) (rexp_rev r)"
| "rexp_rev (Star r) = Star (rexp_rev r)"

lemma lang_rexp_rev [simp]: "lang (rexp_rev r) = rev ` lang r"
  by (induction r) (simp_all add: image_Un)  
    

text \<open>The obvious construction for a singleton-language regular expression:\<close>

fun rexp_of_word where
  "rexp_of_word [] = One"
| "rexp_of_word [x] = Atom x"
| "rexp_of_word (x#xs) = Times (Atom x) (rexp_of_word xs)"
  
lemma lang_rexp_of_word [simp]: "lang (rexp_of_word xs) = {xs}"
  by (induction xs rule: rexp_of_word.induct) (simp_all add: conc_def)

lemma size_rexp_of_word [simp]: "size (rexp_of_word xs) = Suc (2 * (length xs - 1))"
  by (induction xs rule: rexp_of_word.induct) auto


text \<open>Character substitution in a regular expression:\<close>

primrec rexp_subst where
  "rexp_subst f Zero = Zero"
| "rexp_subst f One = One"
| "rexp_subst f (Atom x) = rexp_of_word (f x)"
| "rexp_subst f (Plus r s) = Plus (rexp_subst f r) (rexp_subst f s)"
| "rexp_subst f (Times r s) = Times (rexp_subst f r) (rexp_subst f s)"
| "rexp_subst f (Star r) = Star (rexp_subst f r)"

lemma lang_rexp_subst: "lang (rexp_subst f r) = subst_word f ` lang r"
  by (induction r) (simp_all add: image_Un)


text \<open>Suffix language of a regular expression:\<close>

primrec suffix_rexp :: "'a rexp \<Rightarrow> 'a rexp" where
  "suffix_rexp Zero = Zero"
| "suffix_rexp One = One"
| "suffix_rexp (Atom a) = Plus (Atom a) One"
| "suffix_rexp (Plus r s) = Plus (suffix_rexp r) (suffix_rexp s)"
| "suffix_rexp (Times r s) =
    (if rexp_empty r then Zero else Plus (Times (suffix_rexp r) s) (suffix_rexp s))"
| "suffix_rexp (Star r) =
    (if rexp_empty r then One else Times (suffix_rexp r) (Star r))"

theorem lang_suffix_rexp [simp]:
  "lang (suffix_rexp r) = Suffixes (lang r)"
  by (induction r) (auto simp: rexp_empty_iff)


text \<open>Prefix language of a regular expression:\<close>

primrec prefix_rexp :: "'a rexp \<Rightarrow> 'a rexp" where
  "prefix_rexp Zero = Zero"
| "prefix_rexp One = One"
| "prefix_rexp (Atom a) = Plus (Atom a) One"
| "prefix_rexp (Plus r s) = Plus (prefix_rexp r) (prefix_rexp s)"
| "prefix_rexp (Times r s) =
    (if rexp_empty s then Zero else Plus (Times r (prefix_rexp s)) (prefix_rexp r))"
| "prefix_rexp (Star r) =
    (if rexp_empty r then One else Times (Star r) (prefix_rexp r))"

theorem lang_prefix_rexp [simp]:
  "lang (prefix_rexp r) = Prefixes (lang r)"
  by (induction r) (auto simp: rexp_empty_iff)


text \<open>Sub-word language of a regular expression\<close>    

primrec sublist_rexp :: "'a rexp \<Rightarrow> 'a rexp" where
  "sublist_rexp Zero = Zero"
| "sublist_rexp One = One"
| "sublist_rexp (Atom a) = Plus (Atom a) One"
| "sublist_rexp (Plus r s) = Plus (sublist_rexp r) (sublist_rexp s)"
| "sublist_rexp (Times r s) =
    (if rexp_empty r \<or> rexp_empty s then Zero else 
       Plus (sublist_rexp r) (Plus (sublist_rexp s) (Times (suffix_rexp r) (prefix_rexp s))))"
| "sublist_rexp (Star r) =
    (if rexp_empty r then One else 
       Plus (sublist_rexp r) (Times (suffix_rexp r) (Times (Star r) (prefix_rexp r))))"

theorem lang_sublist_rexp [simp]:
  "lang (sublist_rexp r) = Sublists (lang r)"
  by (induction r) (auto simp: rexp_empty_iff Sublists_star)


text \<open>Fragment language of a regular expression:\<close>
  
primrec subseqs_rexp :: "'a rexp \<Rightarrow> 'a rexp" where
  "subseqs_rexp Zero = Zero"
| "subseqs_rexp One = One"
| "subseqs_rexp (Atom x) = Plus (Atom x) One"
| "subseqs_rexp (Plus r s) = Plus (subseqs_rexp r) (subseqs_rexp s)"
| "subseqs_rexp (Times r s) = Times (subseqs_rexp r) (subseqs_rexp s)"
| "subseqs_rexp (Star r) = Star (subseqs_rexp r)"

lemma lang_subseqs_rexp [simp]: "lang (subseqs_rexp r) = Subseqs (lang r)"
  by (induction r) auto


text \<open>Subword language of a regular expression\<close>


end
