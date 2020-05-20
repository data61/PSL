(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Sequence.thy                                                         *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Infinite Sequences \<close>

theory Sequence
imports
  HOL.Real
  List_Extra
  "HOL-Library.Sublist"
  "HOL-Library.Nat_Bijection"
begin

typedef 'a seq = "UNIV :: (nat \<Rightarrow> 'a) set"
  by (auto)

setup_lifting type_definition_seq

definition ssubstr :: "nat \<Rightarrow> nat \<Rightarrow> 'a seq \<Rightarrow> 'a list" where
"ssubstr i j xs = map (Rep_seq xs) [i ..< j]"

lift_definition nth_seq :: "'a seq \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!\<^sub>s" 100)
is "\<lambda> f i. f i" .

abbreviation sinit :: "nat \<Rightarrow> 'a seq \<Rightarrow> 'a list" where
"sinit i xs \<equiv> ssubstr 0 i xs"

lemma sinit_len [simp]:
  "length (sinit i xs) = i"
  by (simp add: ssubstr_def)

lemma sinit_0 [simp]: "sinit 0 xs = []"
  by (simp add: ssubstr_def)

lemma prefix_upt_0 [intro]:
  "i \<le> j \<Longrightarrow> prefix [0..<i] [0..<j]"
  by (induct i, auto, metis append_prefixD le0 prefix_order.lift_Suc_mono_le prefix_order.order_refl upt_Suc)

lemma sinit_prefix:
  "i \<le> j \<Longrightarrow> prefix (sinit i xs) (sinit j xs)"
  by (simp add: map_mono_prefix prefix_upt_0 ssubstr_def)

lemma sinit_strict_prefix:
  "i < j \<Longrightarrow> strict_prefix (sinit i xs) (sinit j xs)"
  by (metis sinit_len sinit_prefix le_less nat_neq_iff prefix_order.dual_order.strict_iff_order)

lemma nth_sinit:
  "i < n \<Longrightarrow> sinit n xs ! i = xs !\<^sub>s i"
  apply (auto simp add: ssubstr_def)
  apply (transfer, auto)
  done

lemma sinit_append_split:
  assumes "i < j"
  shows "sinit j xs = sinit i xs @ ssubstr i j xs"
proof -
  have "[0..<i] @ [i..<j] = [0..<j]"
    by (metis assms le0 le_add_diff_inverse le_less upt_add_eq_append)
  thus ?thesis
    by (auto simp add: ssubstr_def, transfer, simp add: map_append[THEN sym])
qed

lemma sinit_linear_asym_lemma1:
  assumes "asym R" "i < j" "(sinit i xs, sinit i ys) \<in> lexord R" "(sinit j ys, sinit j xs) \<in> lexord R"
  shows False
proof -
  have sinit_xs: "sinit j xs = sinit i xs @ ssubstr i j xs"
    by (metis assms(2) sinit_append_split)
  have sinit_ys: "sinit j ys = sinit i ys @ ssubstr i j ys"
    by (metis assms(2) sinit_append_split)
  from sinit_xs sinit_ys assms(4)
  have "(sinit i ys, sinit i xs) \<in> lexord R \<or> (sinit i ys = sinit i xs \<and> (ssubstr i j ys, ssubstr i j xs) \<in> lexord R)"
    by (auto dest: lexord_append)
  with assms lexord_asymmetric show False
    by (force)
qed

lemma sinit_linear_asym_lemma2:
  assumes "asym R" "(sinit i xs, sinit i ys) \<in> lexord R" "(sinit j ys, sinit j xs) \<in> lexord R"
  shows False
proof (cases i j rule: linorder_cases)
  case less with assms show ?thesis
    by (auto dest: sinit_linear_asym_lemma1)
next
  case equal with assms show ?thesis
    by (simp add: lexord_asymmetric)
next
  case greater with assms show ?thesis
    by (auto dest: sinit_linear_asym_lemma1)
qed

lemma range_ext:
  assumes "\<forall>i :: nat. \<forall>x\<in>{0..<i}. f(x) = g(x)"
  shows "f = g"
proof (rule ext)
  fix x :: nat
  obtain i :: nat where "i > x"
    by (metis lessI)
  with assms show "f(x) = g(x)"
    by (auto)
qed

lemma sinit_ext:
  "(\<forall> i. sinit i xs = sinit i ys) \<Longrightarrow> xs = ys"
  by (simp add: ssubstr_def, transfer, auto intro: range_ext)

definition seq_lexord :: "'a rel \<Rightarrow> ('a seq) rel" where
"seq_lexord R = {(xs, ys). (\<exists> i. (sinit i xs, sinit i ys) \<in> lexord R)}"

lemma seq_lexord_irreflexive:
  "\<forall>x. (x, x) \<notin> R \<Longrightarrow> (xs, xs) \<notin> seq_lexord R"
  by (auto dest: lexord_irreflexive simp add: irrefl_def seq_lexord_def)

lemma seq_lexord_irrefl:
  "irrefl R \<Longrightarrow> irrefl (seq_lexord R)"
  by (simp add: irrefl_def seq_lexord_irreflexive)

lemma seq_lexord_transitive:
  assumes "trans R"
  shows "trans (seq_lexord R)"
unfolding seq_lexord_def
proof (rule transI, clarify)
  fix xs ys zs :: "'a seq" and m n :: nat
  assume las: "(sinit m xs, sinit m ys) \<in> lexord R" "(sinit n ys, sinit n zs) \<in> lexord R"
  hence inz: "m > 0"
    using gr0I by force
  from las(1) obtain i where sinitm: "(sinit m xs!i, sinit m ys!i) \<in> R" "i < m" "\<forall> j<i. sinit m xs!j = sinit m ys!j"
    using lexord_eq_length by force
  from las(2) obtain j where sinitn: "(sinit n ys!j, sinit n zs!j) \<in> R" "j < n" "\<forall> k<j. sinit n ys!k = sinit n zs!k"
    using lexord_eq_length by force
  show "\<exists>i. (sinit i xs, sinit i zs) \<in> lexord R"
  proof (cases "i \<le> j")
    case True note lt = this
    with sinitm sinitn have "(sinit n xs!i, sinit n zs!i) \<in> R"
      by (metis assms le_eq_less_or_eq le_less_trans nth_sinit transD)
    moreover from lt sinitm sinitn have "\<forall> j<i. sinit m xs!j = sinit m zs!j"
      by (metis less_le_trans less_trans nth_sinit)
    ultimately have "(sinit n xs, sinit n zs) \<in> lexord R" using sinitm(2) sinitn(2) lt
      apply (rule_tac lexord_intro_elems)
         apply (auto)
      apply (metis less_le_trans less_trans nth_sinit)
      done
    thus ?thesis by auto
  next
    case False
    then have ge: "i > j" by auto
    with assms sinitm sinitn have "(sinit n xs!j, sinit n zs!j) \<in> R"
      by (metis less_trans nth_sinit)
    moreover from ge sinitm sinitn have "\<forall> k<j. sinit m xs!k = sinit m zs!k"
      by (metis dual_order.strict_trans nth_sinit)
    ultimately have "(sinit n xs, sinit n zs) \<in> lexord R" using sinitm(2) sinitn(2) ge
      apply (rule_tac lexord_intro_elems)
         apply (auto)
      apply (metis less_trans nth_sinit)
      done
    thus ?thesis by auto
  qed
qed

lemma seq_lexord_trans:
  "\<lbrakk> (xs, ys) \<in> seq_lexord R; (ys, zs) \<in> seq_lexord R; trans R \<rbrakk> \<Longrightarrow> (xs, zs) \<in> seq_lexord R"
  by (meson seq_lexord_transitive transE)

lemma seq_lexord_antisym:
  "\<lbrakk> asym R; (a, b) \<in> seq_lexord R \<rbrakk> \<Longrightarrow> (b, a) \<notin> seq_lexord R"
  by (auto dest: sinit_linear_asym_lemma2 simp add: seq_lexord_def)

lemma seq_lexord_asym:
  assumes "asym R"
  shows "asym (seq_lexord R)"
  by (meson assms asym.simps seq_lexord_antisym seq_lexord_irrefl)

lemma seq_lexord_total:
  assumes "total R"
  shows "total (seq_lexord R)"
  using assms by (auto simp add: total_on_def seq_lexord_def, meson lexord_linear sinit_ext)

lemma seq_lexord_strict_linear_order:
  assumes "strict_linear_order R"
  shows "strict_linear_order (seq_lexord R)"
  using assms
  by (auto simp add: strict_linear_order_on_def partial_order_on_def preorder_on_def
           intro: seq_lexord_transitive seq_lexord_irrefl seq_lexord_total)

lemma seq_lexord_linear:
  assumes "(\<forall> a b. (a,b)\<in> R \<or> a = b \<or> (b,a) \<in> R)"
  shows "(x,y) \<in> seq_lexord R \<or> x = y \<or> (y,x) \<in> seq_lexord R"
proof -
  have "total R"
    using assms total_on_def by blast
  hence "total (seq_lexord R)"
    using seq_lexord_total by blast
  thus ?thesis
    by (auto simp add: total_on_def)
qed

instantiation seq :: (ord) ord
begin

definition less_seq :: "'a seq \<Rightarrow> 'a seq \<Rightarrow> bool" where
"less_seq xs ys \<longleftrightarrow> (xs, ys) \<in> seq_lexord {(xs, ys). xs < ys}"

definition less_eq_seq :: "'a seq \<Rightarrow> 'a seq \<Rightarrow> bool" where
"less_eq_seq xs ys = (xs = ys \<or> xs < ys)"

instance ..

end

instance seq :: (order) order
proof
  fix xs :: "'a seq"
  show "xs \<le> xs" by (simp add: less_eq_seq_def)
next
  fix xs ys zs :: "'a seq"
  assume "xs \<le> ys" and "ys \<le> zs"
  then show "xs \<le> zs"
    by (force dest: seq_lexord_trans simp add: less_eq_seq_def less_seq_def trans_def)
next
  fix xs ys :: "'a seq"
  assume "xs \<le> ys" and "ys \<le> xs"
  then show "xs = ys"
    apply (auto simp add: less_eq_seq_def less_seq_def)
    apply (rule seq_lexord_irreflexive [THEN notE])
     defer
     apply (rule seq_lexord_trans)
       apply (auto intro: transI)
    done
next
  fix xs ys :: "'a seq"
  show "xs < ys \<longleftrightarrow> xs \<le> ys \<and> \<not> ys \<le> xs"
    apply (auto simp add: less_seq_def less_eq_seq_def)
     defer
     apply (rule seq_lexord_irreflexive [THEN notE])
      apply auto
     apply (rule seq_lexord_irreflexive [THEN notE])
      defer
      apply (rule seq_lexord_trans)
        apply (auto intro: transI)
    apply (simp add: seq_lexord_irreflexive)
    done
qed

instance seq :: (linorder) linorder
proof
  fix xs ys :: "'a seq"
  have "(xs, ys) \<in> seq_lexord {(u, v). u < v} \<or> xs = ys \<or> (ys, xs) \<in> seq_lexord {(u, v). u < v}"
    by (rule seq_lexord_linear) auto
  then show "xs \<le> ys \<or> ys \<le> xs"
    by (auto simp add: less_eq_seq_def less_seq_def)
qed

lemma seq_lexord_mono [mono]:
  "(\<And> x y. f x y \<longrightarrow> g x y) \<Longrightarrow> (xs, ys) \<in> seq_lexord {(x, y). f x y} \<longrightarrow> (xs, ys) \<in> seq_lexord {(x, y). g x y}"
  apply (auto simp add: seq_lexord_def)
  apply (metis case_prodD case_prodI lexord_take_index_conv mem_Collect_eq)
done

fun insort_rel :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insort_rel R x [] = [x]" |
"insort_rel R x (y # ys) = (if (x = y \<or> (x,y) \<in> R) then x # y # ys else y # insort_rel R x ys)"

inductive sorted_rel :: "'a rel \<Rightarrow> 'a list \<Rightarrow> bool" where
Nil_rel [iff]: "sorted_rel R []" |
Cons_rel: "\<forall> y \<in> set xs. (x = y \<or> (x, y) \<in> R) \<Longrightarrow> sorted_rel R xs \<Longrightarrow> sorted_rel R (x # xs)"

definition list_of_set :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a list" where
"list_of_set R = folding.F (insort_rel R) []"

lift_definition seq_inj :: "'a seq seq \<Rightarrow> 'a seq" is
"\<lambda> f i. f (fst (prod_decode i)) (snd (prod_decode i))" .

lift_definition seq_proj :: "'a seq \<Rightarrow> 'a seq seq" is
"\<lambda> f i j. f (prod_encode (i, j))" .

lemma seq_inj_inverse: "seq_proj (seq_inj x) = x"
  by (transfer, simp)

lemma seq_proj_inverse: "seq_inj (seq_proj x) = x"
  by (transfer, simp)

lemma seq_inj: "inj seq_inj"
  by (metis injI seq_inj_inverse)

lemma seq_inj_surj: "bij seq_inj"
  apply (rule bijI)
   apply (auto simp add: seq_inj)
  apply (metis rangeI seq_proj_inverse)
  done
end