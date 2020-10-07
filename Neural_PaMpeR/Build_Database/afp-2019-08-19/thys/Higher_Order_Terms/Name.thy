chapter \<open>Names as a unique datatype\<close>

theory Name
imports Main
begin

text \<open>
  I would like to model names as @{typ string}s. Unfortunately, there is no default order on lists,
  as there could be multiple reasonable implementations: e.g.\ lexicographic and point-wise.
  For both choices, users can import the corresponding instantiation.

  In Isabelle, only at most one implementation of a given type class for a given type may be present
  in the same theory. Consequently, I avoided importing a list ordering from the library, because it
  may cause conflicts with users who use another ordering. The general approach for these situations
  is to introduce a type copy.

  The full flexibility of strings (i.e.\ string manipulations) is only required where fresh names
  are being produced. Otherwise, only a linear order on terms is needed. Conveniently, Sternagel and
  Thiemann @{cite sternagel2015deriving} provide tooling to automatically generate such a
  lexicographic order.
\<close>

datatype name = Name (as_string: string)

\<comment> \<open>Mostly copied from \<open>List_Lexorder\<close>\<close>

instantiation name :: ord
begin

definition less_name where
"xs < ys \<longleftrightarrow> (as_string xs, as_string ys) \<in> lexord {(u, v). (of_char u :: nat) < of_char v}"

definition less_eq_name where
"(xs :: name) \<le> ys \<longleftrightarrow> xs < ys \<or> xs = ys"

instance ..

end

instance name :: order
proof
  fix xs :: "name"
  show "xs \<le> xs" by (simp add: less_eq_name_def)
next
  fix xs ys zs :: "name"
  assume "xs \<le> ys" and "ys \<le> zs"
  then show "xs \<le> zs"
    apply (auto simp add: less_eq_name_def less_name_def)
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "name"
  assume "xs \<le> ys" and "ys \<le> xs"
  then show "xs = ys"
    apply (auto simp add: less_eq_name_def less_name_def)
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
next
  fix xs ys :: "name"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    apply (auto simp add: less_name_def less_eq_name_def)
    defer
    apply (rule lexord_irreflexive [THEN notE])
    apply auto
    apply (rule lexord_irreflexive [THEN notE])
    defer
    apply (rule lexord_trans)
    apply (auto intro: transI)
    done
qed

instance name :: linorder
proof
  fix xs ys :: "name"
  have "(as_string xs, as_string ys) \<in> lexord {(u, v). (of_char u::nat) < of_char v} \<or> xs = ys \<or> (as_string ys, as_string xs) \<in> lexord {(u, v). (of_char u::nat) < of_char v}"
    by (metis (no_types, lifting) case_prodI lexord_linear linorder_neqE_nat mem_Collect_eq name.expand of_char_eq_iff)
  then show "xs \<le> ys \<or> ys \<le> xs"
    by (auto simp add: less_eq_name_def less_name_def)
qed

lemma less_name_code[code]:
  "Name xs < Name [] \<longleftrightarrow> False"
  "Name [] < Name (x # xs) \<longleftrightarrow> True"
  "Name (x # xs) < Name (y # ys) \<longleftrightarrow> (of_char x::nat) < of_char y \<or> x = y \<and> Name xs < Name ys"
unfolding less_name_def by auto

lemma le_name_code[code]:
  "Name (x # xs) \<le> Name [] \<longleftrightarrow> False"
  "Name [] \<le> Name (x # xs) \<longleftrightarrow> True"
  "Name (x # xs) \<le> Name (y # ys) \<longleftrightarrow> (of_char x::nat) < of_char y \<or> x = y \<and> Name xs \<le> Name ys"
unfolding less_eq_name_def less_name_def by auto

context begin

qualified definition append :: "name \<Rightarrow> name \<Rightarrow> name" where
"append v1 v2 = Name (as_string v1 @ as_string v2)"

lemma name_append_less:
  assumes "xs \<noteq> Name []"
  shows "append ys xs > ys"
proof -
  have "Name (ys @ xs) > Name ys" if "xs \<noteq> []" for xs ys
    using that
    proof (induction ys)
      case Nil
      thus ?case
        unfolding less_name_def
        by (cases xs) auto
    next
      case (Cons y ys)
      thus ?case
        unfolding less_name_def
        by auto
    qed
  with assms show ?thesis
    unfolding append_def
    by (cases xs, cases ys) auto
qed

end

end