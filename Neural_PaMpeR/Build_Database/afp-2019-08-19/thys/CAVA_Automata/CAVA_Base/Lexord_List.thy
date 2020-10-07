theory Lexord_List
imports Main
begin

typedef 'a lexlist = "{xs::'a list. True}"
  morphisms unlex Lex
by auto

definition "lexlist \<equiv> Lex"

lemma lexlist_ext:
  "Lex xs = Lex ys \<Longrightarrow> xs = ys"
by (auto simp: Lex_inject)

lemma Lex_unlex [simp, code abstype]:
  "Lex (unlex lxs) = lxs"
  by (metis unlex_inverse)

lemma unlex_lexlist [simp, code abstract]:
  "unlex (lexlist xs) = xs"
  by (metis lexlist_ext unlex_inverse lexlist_def)

definition list_less :: "'a :: ord list \<Rightarrow> 'a list \<Rightarrow> bool" where 
  "list_less xs ys \<longleftrightarrow> (xs, ys) \<in> lexord {(u, v). u < v}"

definition list_le where
  "list_le xs ys \<longleftrightarrow> list_less xs ys \<or> xs = ys"

lemma not_less_Nil [simp]: "\<not> list_less x []"
  by (simp add: list_less_def)

lemma Nil_less_Cons [simp]: "list_less [] (a # x)"
  by (simp add: list_less_def)

lemma Cons_less_Cons [simp]: "list_less (a # x) (b # y) \<longleftrightarrow> a < b \<or> a = b \<and> list_less x y"
  by (simp add: list_less_def)

lemma le_Nil [simp]: "list_le x [] \<longleftrightarrow> x = []"
  unfolding list_le_def by (cases x) auto

lemma Nil_le_Cons [simp]: "list_le [] x"
  unfolding list_le_def by (cases x) auto

lemma Cons_le_Cons [simp]: "list_le (a # x) (b # y) \<longleftrightarrow> a < b \<or> a = b \<and> list_le x y"
  unfolding list_le_def by auto

lemma less_list_code [code]:
  "list_less xs [] \<longleftrightarrow> False"
  "list_less [] (x # xs) \<longleftrightarrow> True"
  "list_less (x # xs) (y # ys) \<longleftrightarrow> x < y \<or> x = y \<and> list_less xs ys"
  by simp_all

lemma less_eq_list_code [code]:
  "list_le (x # xs) [] \<longleftrightarrow> False"
  "list_le [] xs \<longleftrightarrow> True"
  "list_le (x # xs) (y # ys) \<longleftrightarrow> x < y \<or> x = y \<and> list_le xs ys"
  by simp_all

instantiation  lexlist :: (ord) ord
begin

definition
  lexlist_less_def: "xs < ys \<longleftrightarrow> list_less (unlex xs) (unlex ys)"

definition
  lexlist_le_def: "(xs :: _ lexlist) \<le> ys \<longleftrightarrow> list_le (unlex xs) (unlex ys)"

instance ..

lemmas lexlist_ord_defs = lexlist_le_def lexlist_less_def list_le_def list_less_def

end

instance lexlist :: (order) order
proof
  fix xs :: "'a lexlist"
  show "xs \<le> xs" by (simp add: lexlist_le_def list_le_def)
next
  fix xs ys zs :: "'a lexlist"
  assume "xs \<le> ys" and "ys \<le> zs"
  then show "xs \<le> zs"
    apply (auto simp add: lexlist_ord_defs)
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "'a lexlist"
  assume "xs \<le> ys" and "ys \<le> xs"
  then show "xs = ys"
    apply (auto simp add: lexlist_ord_defs)
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI simp: unlex_inject)
    done
next
  fix xs ys :: "'a lexlist"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    apply (auto simp add: lexlist_ord_defs)
    defer
    apply (rule lexord_irreflexive [THEN notE])
    apply auto
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
qed

instance lexlist :: (linorder) linorder
proof
  fix xs ys :: "'a lexlist"
  have "(unlex xs, unlex ys) \<in> lexord {(u, v). u < v} \<or> unlex xs = unlex ys \<or> (unlex ys, unlex xs) \<in> lexord {(u, v). u < v}"
    by (rule lexord_linear) auto
  then show "xs \<le> ys \<or> ys \<le> xs"
    by (auto simp add: lexlist_ord_defs unlex_inject)
qed

end
