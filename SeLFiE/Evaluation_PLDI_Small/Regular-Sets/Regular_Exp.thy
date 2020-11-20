(*  Author: Tobias Nipkow *)

section "Regular expressions"

theory Regular_Exp
imports Regular_Set
begin

datatype (atoms: 'a) rexp =
  is_Zero: Zero |
  is_One: One |
  Atom 'a |
  Plus "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)"

primrec lang :: "'a rexp => 'a lang" where
"lang Zero = {}" |
"lang One = {[]}" |
"lang (Atom a) = {[a]}" |
"lang (Plus r s) = (lang r) Un (lang s)" |
"lang (Times r s) = conc (lang r) (lang s)" |
"lang (Star r) = star(lang r)"

abbreviation (input) regular_lang where "regular_lang A \<equiv> (\<exists>r. lang r = A)"

primrec nullable :: "'a rexp \<Rightarrow> bool" where
"nullable Zero = False" |
"nullable One = True" |
"nullable (Atom c) = False" |
"nullable (Plus r1 r2) = (nullable r1 \<or> nullable r2)" |
"nullable (Times r1 r2) = (nullable r1 \<and> nullable r2)" |
"nullable (Star r) = True"

lemma nullable_iff [code_abbrev]: "nullable r \<longleftrightarrow> [] \<in> lang r"
  by (induct r) (auto simp add: conc_def split: if_splits)

primrec rexp_empty where
  "rexp_empty Zero \<longleftrightarrow> True"
| "rexp_empty One \<longleftrightarrow> False"
| "rexp_empty (Atom a) \<longleftrightarrow> False"
| "rexp_empty (Plus r s) \<longleftrightarrow> rexp_empty r \<and> rexp_empty s"
| "rexp_empty (Times r s) \<longleftrightarrow> rexp_empty r \<or> rexp_empty s"
| "rexp_empty (Star r) \<longleftrightarrow> False"

(* TODO Fixme: This code_abbrev rule does not work. Why? *)
lemma rexp_empty_iff [code_abbrev]: "rexp_empty r \<longleftrightarrow> lang r = {}"
  by (induction r) auto



text\<open>Composition on rhs usually complicates matters:\<close>
lemma map_map_rexp:
  "map_rexp f (map_rexp g r) = map_rexp (\<lambda>r. f (g r)) r"
  unfolding rexp.map_comp o_def ..

lemma map_rexp_ident[simp]: "map_rexp (\<lambda>x. x) = (\<lambda>r. r)"
  unfolding id_def[symmetric] fun_eq_iff rexp.map_id id_apply by (intro allI refl)

lemma atoms_lang: "w : lang r \<Longrightarrow> set w \<subseteq> atoms r"
proof(induction r arbitrary: w)
  case Times thus ?case by fastforce
next
  case Star thus ?case by (fastforce simp add: star_conv_concat)
qed auto

lemma lang_eq_ext: "(lang r = lang s) =
  (\<forall>w \<in> lists(atoms r \<union> atoms s). w \<in> lang r \<longleftrightarrow> w \<in> lang s)"
  by (auto simp: atoms_lang[unfolded subset_iff])

lemma lang_eq_ext_Nil_fold_Deriv:
  fixes r s
  defines "\<BB> \<equiv> {(fold Deriv w (lang r), fold Deriv w (lang s))| w. w\<in>lists (atoms r \<union> atoms s)}"
  shows "lang r = lang s \<longleftrightarrow> (\<forall>(K, L) \<in> \<BB>. [] \<in> K \<longleftrightarrow> [] \<in> L)"
  unfolding lang_eq_ext \<BB>_def by (subst (1 2) in_fold_Deriv[of "[]", simplified, symmetric]) auto


subsection \<open>Term ordering\<close>

instantiation rexp :: (order) "{order}"
begin

fun le_rexp :: "('a::order) rexp \<Rightarrow> ('a::order) rexp \<Rightarrow> bool"
where
  "le_rexp Zero _ = True"
| "le_rexp _ Zero = False"
| "le_rexp One _ = True"
| "le_rexp _ One = False"
| "le_rexp (Atom a) (Atom b) = (a <= b)"
| "le_rexp (Atom _) _ = True"
| "le_rexp _ (Atom _) = False"
| "le_rexp (Star r) (Star s) = le_rexp r s"
| "le_rexp (Star _) _ = True"
| "le_rexp _ (Star _) = False"
| "le_rexp (Plus r r') (Plus s s') =
    (if r = s then le_rexp r' s' else le_rexp r s)"
| "le_rexp (Plus _ _) _ = True"
| "le_rexp _ (Plus _ _) = False"
| "le_rexp (Times r r') (Times s s') =
    (if r = s then le_rexp r' s' else le_rexp r s)"

(* The class instance stuff is by Dmitriy Traytel *)

definition less_eq_rexp where "r \<le> s \<equiv> le_rexp r s"
definition less_rexp where "r < s \<equiv> le_rexp r s \<and> r \<noteq> s"

lemma le_rexp_Zero: "le_rexp r Zero \<Longrightarrow> r = Zero"
by (induction r) auto

lemma le_rexp_refl: "le_rexp r r"
by (induction r) auto

lemma le_rexp_antisym: "\<lbrakk>le_rexp r s; le_rexp s r\<rbrakk> \<Longrightarrow> r = s"
by (induction r s rule: le_rexp.induct) (auto dest: le_rexp_Zero)

lemma le_rexp_trans: "\<lbrakk>le_rexp r s; le_rexp s t\<rbrakk> \<Longrightarrow> le_rexp r t"
proof (induction r s arbitrary: t rule: le_rexp.induct)
  fix v t assume "le_rexp (Atom v) t" thus "le_rexp One t" by (cases t) auto
next
  fix s1 s2 t assume "le_rexp (Plus s1 s2) t" thus "le_rexp One t" by (cases t) auto
next
  fix s1 s2 t assume "le_rexp (Times s1 s2) t" thus "le_rexp One t" by (cases t) auto
next
  fix s t assume "le_rexp (Star s) t" thus "le_rexp One t" by (cases t) auto
next
  fix v u t assume "le_rexp (Atom v) (Atom u)" "le_rexp (Atom u) t"
  thus "le_rexp (Atom v) t" by (cases t) auto
next
  fix v s1 s2 t assume "le_rexp (Plus s1 s2) t" thus "le_rexp (Atom v) t" by (cases t) auto
next
  fix v s1 s2 t assume "le_rexp (Times s1 s2) t" thus "le_rexp (Atom v) t" by (cases t) auto
next
  fix v s t assume "le_rexp (Star s) t" thus "le_rexp (Atom v) t" by (cases t) auto
next
  fix r s t
  assume IH: "\<And>t. le_rexp r s \<Longrightarrow> le_rexp s t \<Longrightarrow> le_rexp r t"
    and "le_rexp (Star r) (Star s)" "le_rexp (Star s) t"
  thus "le_rexp (Star r) t" by (cases t) auto
next
  fix r s1 s2 t assume "le_rexp (Plus s1 s2) t" thus "le_rexp (Star r) t" by (cases t) auto
next
  fix r s1 s2 t assume "le_rexp (Times s1 s2) t" thus "le_rexp (Star r) t" by (cases t) auto
next
  fix r1 r2 s1 s2 t
  assume "\<And>t. r1 = s1 \<Longrightarrow> le_rexp r2 s2 \<Longrightarrow> le_rexp s2 t \<Longrightarrow> le_rexp r2 t"
         "\<And>t. r1 \<noteq> s1 \<Longrightarrow> le_rexp r1 s1 \<Longrightarrow> le_rexp s1 t \<Longrightarrow> le_rexp r1 t"
         "le_rexp (Plus r1 r2) (Plus s1 s2)" "le_rexp (Plus s1 s2) t"
  thus "le_rexp (Plus r1 r2) t" by (cases t) (auto split: if_split_asm intro: le_rexp_antisym)
next
  fix r1 r2 s1 s2 t assume "le_rexp (Times s1 s2) t" thus "le_rexp (Plus r1 r2) t" by (cases t) auto
next
  fix r1 r2 s1 s2 t
  assume "\<And>t. r1 = s1 \<Longrightarrow> le_rexp r2 s2 \<Longrightarrow> le_rexp s2 t \<Longrightarrow> le_rexp r2 t"
         "\<And>t. r1 \<noteq> s1 \<Longrightarrow> le_rexp r1 s1 \<Longrightarrow> le_rexp s1 t \<Longrightarrow> le_rexp r1 t"
         "le_rexp (Times r1 r2) (Times s1 s2)" "le_rexp (Times s1 s2) t"
  thus "le_rexp (Times r1 r2) t" by (cases t) (auto split: if_split_asm intro: le_rexp_antisym)
qed auto

instance proof
qed (auto simp add: less_eq_rexp_def less_rexp_def
       intro: le_rexp_refl le_rexp_antisym le_rexp_trans)

end

instantiation rexp :: (linorder) "{linorder}"
begin

lemma le_rexp_total: "le_rexp (r :: 'a :: linorder rexp) s \<or> le_rexp s r"
by (induction r s rule: le_rexp.induct) auto

instance proof
qed (unfold less_eq_rexp_def less_rexp_def, rule le_rexp_total)

end

end
