(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
section \<open>Transitive Closures\<close>
theory Transitive_Closure_Ext
  imports "HOL-Library.FuncSet"
begin

(*** Basic Properties *******************************************************)

subsection \<open>Basic Properties\<close>

text \<open>
  @{text "R\<^sup>+\<^sup>+"} is a transitive closure of a relation @{text R}.
  @{text "R\<^sup>*\<^sup>*"} is a reflexive transitive closure of a relation @{text R}.\<close>

text \<open>
  A function @{text f} is surjective on @{text "R\<^sup>+\<^sup>+"} iff for any
  two elements in the range of @{text f}, related through @{text "R\<^sup>+\<^sup>+"},
  all their intermediate elements belong to the range of @{text f}.\<close>

abbreviation "surj_on_trancl R f \<equiv>
  (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"

text \<open>
  A function @{text f} is bijective on @{text "R\<^sup>+\<^sup>+"} iff
  it is injective and surjective on @{text "R\<^sup>+\<^sup>+"}.\<close>

abbreviation "bij_on_trancl R f \<equiv> inj f \<and> surj_on_trancl R f"

(*** Helper Lemmas **********************************************************)

subsection \<open>Helper Lemmas\<close>

lemma rtranclp_eq_rtranclp [iff]:
  "(\<lambda>x y. P x y \<or> x = y)\<^sup>*\<^sup>* = P\<^sup>*\<^sup>*"
proof (intro ext iffI)
  fix x y
  have "(\<lambda>x y. P x y \<or> x = y)\<^sup>*\<^sup>* x y \<longrightarrow> P\<^sup>=\<^sup>=\<^sup>*\<^sup>* x y"
    by (rule mono_rtranclp) simp
  thus "(\<lambda>x y. P x y \<or> x = y)\<^sup>*\<^sup>* x y \<Longrightarrow> P\<^sup>*\<^sup>* x y"
    by simp
  show "P\<^sup>*\<^sup>* x y \<Longrightarrow> (\<lambda>x y. P x y \<or> x = y)\<^sup>*\<^sup>* x y"
    by (metis (no_types, lifting) mono_rtranclp)
qed

lemma tranclp_eq_rtranclp [iff]:
  "(\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ = P\<^sup>*\<^sup>*"
proof (intro ext iffI)
  fix x y
  have "(\<lambda>x y. P x y \<or> x = y)\<^sup>*\<^sup>* x y \<longrightarrow> P\<^sup>=\<^sup>=\<^sup>*\<^sup>* x y"
    by (rule mono_rtranclp) simp
  thus "(\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ x y \<Longrightarrow> P\<^sup>*\<^sup>* x y"
    using tranclp_into_rtranclp by force
  show "P\<^sup>*\<^sup>* x y \<Longrightarrow> (\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ x y"
    by (metis (mono_tags, lifting) mono_rtranclp rtranclpD tranclp.r_into_trancl)
qed

lemma rtranclp_eq_rtranclp' [iff]:
  "(\<lambda>x y. P x y \<and> x \<noteq> y)\<^sup>*\<^sup>* = P\<^sup>*\<^sup>*"
proof (intro ext iffI)
  fix x y
  show "(\<lambda>x y. P x y \<and> x \<noteq> y)\<^sup>*\<^sup>* x y \<Longrightarrow> P\<^sup>*\<^sup>* x y"
    by (metis (no_types, lifting) mono_rtranclp)
  assume "P\<^sup>*\<^sup>* x y"
  hence "(inf P (\<noteq>))\<^sup>*\<^sup>* x y"
    by (simp add: rtranclp_r_diff_Id)
  also have "(inf P (\<noteq>))\<^sup>*\<^sup>* x y \<longrightarrow> (\<lambda>x y. P x y \<and> x \<noteq> y)\<^sup>*\<^sup>* x y"
    by (rule mono_rtranclp) simp
  finally show "P\<^sup>*\<^sup>* x y \<Longrightarrow> (\<lambda>x y. P x y \<and> x \<noteq> y)\<^sup>*\<^sup>* x y" by simp
qed

lemma tranclp_tranclp_to_tranclp_r:
  assumes "(\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> P x \<Longrightarrow> P z \<Longrightarrow> P y)"
  assumes "R\<^sup>+\<^sup>+ x y" and "R\<^sup>+\<^sup>+ y z"
  assumes "P x" and "P z"
  shows "P y"
proof -
  have "(\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> P x \<Longrightarrow> P z \<Longrightarrow> P y) \<Longrightarrow>
         R\<^sup>+\<^sup>+ y z \<Longrightarrow> R\<^sup>+\<^sup>+ x y \<Longrightarrow> P x \<longrightarrow> P z \<longrightarrow> P y"
    by (erule tranclp_induct, auto) (meson tranclp_trans)
  thus ?thesis using assms by auto
qed

(*** Transitive Closure Preservation & Reflection ***************************)

subsection \<open>Transitive Closure Preservation\<close>

text \<open>
  A function @{text f} preserves @{text "R\<^sup>+\<^sup>+"} if it preserves @{text R}.\<close>

text \<open>
  The proof was derived from the accepted answer on the website
  Stack Overflow that is available at
  @{url "https://stackoverflow.com/a/52573551/632199"}
  and provided with the permission of the author of the answer.\<close>

lemma preserve_tranclp:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
  assumes "R\<^sup>+\<^sup>+ x y"
  shows "S\<^sup>+\<^sup>+ (f x) (f y)"
proof -
  define P where P: "P = (\<lambda>x y. S\<^sup>+\<^sup>+ (f x) (f y))" 
  define r where r: "r = (\<lambda>x y. S (f x) (f y))"
  have "r\<^sup>+\<^sup>+ x y" by (insert assms r; erule tranclp_trans_induct; auto)
  moreover have "\<And>x y. r x y \<Longrightarrow> P x y" unfolding P r by simp
  moreover have "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    unfolding P by auto
  ultimately have "P x y" by (rule tranclp_trans_induct)
  with P show ?thesis by simp
qed

text \<open>
  A function @{text f} preserves @{text "R\<^sup>*\<^sup>*"} if it preserves @{text R}.\<close>

lemma preserve_rtranclp:
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>*\<^sup>* (f x) (f y)"
  unfolding Nitpick.rtranclp_unfold
  by (metis preserve_tranclp)

text \<open>
  If one needs to prove that @{text "(f x)"} and @{text "(g y)"}
  are related through @{text "S\<^sup>*\<^sup>*"} then one can use the previous
  lemma and add a one more step from @{text "(f y)"} to @{text "(g y)"}.\<close>

lemma preserve_rtranclp':
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>*\<^sup>* (f x) (g y)"
  by (metis preserve_rtranclp rtranclp.rtrancl_into_rtrancl)

lemma preserve_rtranclp'':
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>+\<^sup>+ (f x) (g y)"
  apply (rule_tac ?b="f y" in rtranclp_into_tranclp1, auto)
  by (rule preserve_rtranclp, auto)

subsection \<open>Transitive Closure Reflection\<close>

text \<open>
  A function @{text f} reflects @{text "S\<^sup>+\<^sup>+"} if it reflects
  @{text S} and is bijective on @{text "S\<^sup>+\<^sup>+"}.\<close>

text \<open>
  The proof was derived from the accepted answer on the website
  Stack Overflow that is available at
  @{url "https://stackoverflow.com/a/52573551/632199"}
  and provided with the permission of the author of the answer.\<close>

lemma reflect_tranclp:
  assumes refl_f: "\<And>x y. S (f x) (f y) \<Longrightarrow> R x y"
  assumes bij_f: "bij_on_trancl S f"
  assumes prem: "S\<^sup>+\<^sup>+ (f x) (f y)"
  shows "R\<^sup>+\<^sup>+ x y"
proof -
  define B where B: "B = range f"
  define g where g: "g = the_inv_into UNIV f"
  define gr where gr: "gr = restrict g B"
  define P where P: "P = (\<lambda>x y. x \<in> B \<longrightarrow> y \<in> B \<longrightarrow> R\<^sup>+\<^sup>+ (gr x) (gr y))"
  from prem have major: "S\<^sup>+\<^sup>+ (f x) (f y)" by blast
  from refl_f bij_f have cases_1: "\<And>x y. S x y \<Longrightarrow> P x y"
    unfolding B P g gr
    by (simp add: f_the_inv_into_f tranclp.r_into_trancl)
  from refl_f bij_f
  have "(\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> x \<in> B \<Longrightarrow> z \<in> B \<Longrightarrow> y \<in> B)"
    unfolding B
    by (rule_tac ?z="z" in tranclp_tranclp_to_tranclp_r, auto, blast)
  with P have cases_2:
    "\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    unfolding B
    by auto
  from major cases_1 cases_2 have "P (f x) (f y)"
    by (rule tranclp_trans_induct)
  with bij_f show ?thesis unfolding P B g gr by (simp add: the_inv_f_f)
qed

text \<open>
  A function @{text f} reflects @{text "S\<^sup>*\<^sup>*"} if it reflects
  @{text S} and is bijective on @{text "S\<^sup>+\<^sup>+"}.\<close>

lemma reflect_rtranclp:
  "(\<And>x y. S (f x) (f y) \<Longrightarrow> R x y) \<Longrightarrow>
   bij_on_trancl S f \<Longrightarrow>
   S\<^sup>*\<^sup>* (f x) (f y) \<Longrightarrow> R\<^sup>*\<^sup>* x y"
  unfolding Nitpick.rtranclp_unfold
  by (metis (full_types) injD reflect_tranclp)

end
