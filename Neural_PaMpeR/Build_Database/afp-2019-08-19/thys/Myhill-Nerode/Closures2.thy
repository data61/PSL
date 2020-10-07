theory Closures2
imports 
  Closures
  Well_Quasi_Orders.Well_Quasi_Orders
begin

section \<open>Closure under \<open>SUBSEQ\<close> and \<open>SUPSEQ\<close>\<close>

text \<open>Properties about the embedding relation\<close>

lemma subseq_strict_length:
  assumes a: "subseq x y" "x \<noteq> y" 
  shows "length x < length y"
using a
by (induct) (auto simp add: less_Suc_eq)

lemma subseq_wf:
  shows "wf {(x, y). subseq x y \<and> x \<noteq> y}"
proof -
  have "wf (measure length)" by simp
  moreover
  have "{(x, y). subseq x y \<and> x \<noteq> y} \<subseteq> measure length"
    unfolding measure_def by (auto simp add: subseq_strict_length)
  ultimately 
  show "wf {(x, y). subseq x y \<and> x \<noteq> y}" by (rule wf_subset)
qed

lemma subseq_good:
  shows "good subseq (f :: nat \<Rightarrow> ('a::finite) list)"
using wqo_on_imp_good[where f="f", OF wqo_on_lists_over_finite_sets]
by simp

lemma subseq_Higman_antichains:
  assumes a: "\<forall>(x::('a::finite) list) \<in> A. \<forall>y \<in> A. x \<noteq> y \<longrightarrow> \<not>(subseq x y) \<and> \<not>(subseq y x)"
  shows "finite A"
proof (rule ccontr)
  assume "infinite A"
  then obtain f::"nat \<Rightarrow> 'a::finite list" where b: "inj f" and c: "range f \<subseteq> A"
    by (auto simp add: infinite_iff_countable_subset)
  from subseq_good[where f="f"] 
  obtain i j where d: "i < j" and e: "subseq (f i) (f j) \<or> f i = f j" 
    unfolding good_def
    by auto
  have "f i \<noteq> f j" using b d by (auto simp add: inj_on_def)
  moreover
  have "f i \<in> A" using c by auto
  moreover
  have "f j \<in> A" using c by auto
  ultimately have "\<not>(subseq (f i) (f j))" using a by simp
  with e show "False" by auto
qed

subsection \<open>Sub- and Supersequences\<close>

definition
 "SUBSEQ A \<equiv> {x::('a::finite) list. \<exists>y \<in> A. subseq x y}"

definition
 "SUPSEQ A \<equiv> {x::('a::finite) list. \<exists>y \<in> A. subseq y x}"

lemma SUPSEQ_simps [simp]:
  shows "SUPSEQ {} = {}"
  and   "SUPSEQ {[]} = UNIV"
unfolding SUPSEQ_def by auto

lemma SUPSEQ_atom [simp]:
  shows "SUPSEQ {[c]} = UNIV \<cdot> {[c]} \<cdot> UNIV"
unfolding SUPSEQ_def conc_def
by (auto dest: list_emb_ConsD)

lemma SUPSEQ_union [simp]:
  shows "SUPSEQ (A \<union> B) = SUPSEQ A \<union> SUPSEQ B"
unfolding SUPSEQ_def by auto

lemma SUPSEQ_conc [simp]:
  shows "SUPSEQ (A \<cdot> B) = SUPSEQ A \<cdot> SUPSEQ B"
unfolding SUPSEQ_def conc_def
apply(auto)
apply(drule list_emb_appendD)
apply(auto)
by (metis list_emb_append_mono)

lemma SUPSEQ_star [simp]:
  shows "SUPSEQ (A\<star>) = UNIV"
apply(subst star_unfold_left)
apply(simp only: SUPSEQ_union) 
apply(simp)
done

subsection \<open>Regular expression that recognises every character\<close>

definition
  Allreg :: "'a::finite rexp"
where
  "Allreg \<equiv> \<Uplus>(Atom ` UNIV)"

lemma Allreg_lang [simp]:
  shows "lang Allreg = (\<Union>a. {[a]})"
unfolding Allreg_def by auto

lemma [simp]:
  shows "(\<Union>a. {[a]})\<star> = UNIV"
apply(auto)
apply(induct_tac x)
apply(auto)
apply(subgoal_tac "[a] @ list \<in> (\<Union>a. {[a]})\<star>")
apply(simp)
apply(rule append_in_starI)
apply(auto)
done

lemma Star_Allreg_lang [simp]:
  shows "lang (Star Allreg) = UNIV"
by simp

fun 
  UP :: "'a::finite rexp \<Rightarrow> 'a rexp"
where
  "UP (Zero) = Zero"
| "UP (One) = Star Allreg"
| "UP (Atom c) = Times (Star Allreg) (Times (Atom c) (Star Allreg))"   
| "UP (Plus r1 r2) = Plus (UP r1) (UP r2)"
| "UP (Times r1 r2) = Times (UP r1) (UP r2)"
| "UP (Star r) = Star Allreg"

lemma lang_UP:
  fixes r::"'a::finite rexp"
  shows "lang (UP r) = SUPSEQ (lang r)"
by (induct r) (simp_all)

lemma SUPSEQ_regular: 
  fixes A::"'a::finite lang"
  assumes "regular A"
  shows "regular (SUPSEQ A)"
proof -
  from assms obtain r::"'a::finite rexp" where "lang r = A" by auto
  then have "lang (UP r) = SUPSEQ A" by (simp add: lang_UP)
  then show "regular (SUPSEQ A)" by auto
qed

lemma SUPSEQ_subset:
  fixes A::"'a::finite list set"
  shows "A \<subseteq> SUPSEQ A"
unfolding SUPSEQ_def by auto

lemma SUBSEQ_complement:
  shows "- (SUBSEQ A) = SUPSEQ (- (SUBSEQ A))"
proof -
  have "- (SUBSEQ A) \<subseteq> SUPSEQ (- (SUBSEQ A))"
    by (rule SUPSEQ_subset)
  moreover 
  have "SUPSEQ (- (SUBSEQ A)) \<subseteq> - (SUBSEQ A)"
  proof (rule ccontr)
    assume "\<not> (SUPSEQ (- (SUBSEQ A)) \<subseteq> - (SUBSEQ A))"
    then obtain x where 
       a: "x \<in> SUPSEQ (- (SUBSEQ A))" and 
       b: "x \<notin> - (SUBSEQ A)" by auto

    from a obtain y where c: "y \<in> - (SUBSEQ A)" and d: "subseq y x"
      by (auto simp add: SUPSEQ_def)

    from b have "x \<in> SUBSEQ A" by simp
    then obtain x' where f: "x' \<in> A" and e: "subseq x x'"
      by (auto simp add: SUBSEQ_def)
    
    from d e have "subseq y x'"
      by (rule subseq_order.order_trans)
    then have "y \<in> SUBSEQ A" using f
      by (auto simp add: SUBSEQ_def)
    with c show "False" by simp
  qed
  ultimately show "- (SUBSEQ A) = SUPSEQ (- (SUBSEQ A))" by simp
qed

definition
  minimal :: "'a::finite list \<Rightarrow> 'a lang \<Rightarrow> bool"
where
  "minimal x A \<equiv> (\<forall>y \<in> A. subseq y x \<longrightarrow> subseq x y)"

lemma main_lemma:
  shows "\<exists>M. finite M \<and> SUPSEQ A = SUPSEQ M"
proof -
  define M where "M = {x \<in> A. minimal x A}"
  have "finite M"
    unfolding M_def minimal_def
    by (rule subseq_Higman_antichains) (auto simp add: subseq_order.antisym)
  moreover
  have "SUPSEQ A \<subseteq> SUPSEQ M"
  proof
    fix x
    assume "x \<in> SUPSEQ A"
    then obtain y where "y \<in> A" and "subseq y x" by (auto simp add: SUPSEQ_def)
    then have a: "y \<in> {y' \<in> A. subseq y' x}" by simp
    obtain z where b: "z \<in> A" "subseq z x" and c: "\<forall>y. subseq y z \<and> y \<noteq> z \<longrightarrow> y \<notin> {y' \<in> A. subseq y' x}"
      using wfE_min[OF subseq_wf a] by auto
    then have "z \<in> M"
      unfolding M_def minimal_def
      by (auto intro: subseq_order.order_trans)
    with b(2) show "x \<in> SUPSEQ M"
      by (auto simp add: SUPSEQ_def)
  qed
  moreover
  have "SUPSEQ M \<subseteq> SUPSEQ A"
    by (auto simp add: SUPSEQ_def M_def)
  ultimately
  show "\<exists>M. finite M \<and> SUPSEQ A = SUPSEQ M" by blast
qed

subsection \<open>Closure of @{const SUBSEQ} and @{const SUPSEQ}\<close>

lemma closure_SUPSEQ:
  fixes A::"'a::finite lang" 
  shows "regular (SUPSEQ A)"
proof -
  obtain M where a: "finite M" and b: "SUPSEQ A = SUPSEQ M"
    using main_lemma by blast
  have "regular M" using a by (rule finite_regular)
  then have "regular (SUPSEQ M)" by (rule SUPSEQ_regular)
  then show "regular (SUPSEQ A)" using b by simp
qed

lemma closure_SUBSEQ:
  fixes A::"'a::finite lang"
  shows "regular (SUBSEQ A)"
proof -
  have "regular (SUPSEQ (- SUBSEQ A))" by (rule closure_SUPSEQ)
  then have "regular (- SUBSEQ A)" by (subst SUBSEQ_complement) (simp)
  then have "regular (- (- (SUBSEQ A)))" by (rule closure_complement)
  then show "regular (SUBSEQ A)" by simp
qed

end
