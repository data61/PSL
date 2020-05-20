(* Author: Xingyuan Zhang, Chunhan Wu, Christian Urban *)
theory Myhill_2
  imports Myhill_1 "HOL-Library.Sublist"
begin

section \<open>Second direction of MN: \<open>regular language \<Rightarrow> finite partition\<close>\<close>

subsection \<open>Tagging functions\<close>

definition 
   tag_eq :: "('a list \<Rightarrow> 'b) \<Rightarrow> ('a list \<times> 'a list) set" ("=_=")
where
   "=tag= \<equiv> {(x, y). tag x = tag y}"

abbreviation
   tag_eq_applied :: "'a list \<Rightarrow> ('a list \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> bool" ("_ =_= _")
where
   "x =tag= y \<equiv> (x, y) \<in> =tag="

lemma [simp]:
  shows "(\<approx>A) `` {x} = (\<approx>A) `` {y} \<longleftrightarrow> x \<approx>A y"
unfolding str_eq_def by auto

lemma refined_intro:
  assumes "\<And>x y z. \<lbrakk>x =tag= y; x @ z \<in> A\<rbrakk> \<Longrightarrow> y @ z \<in> A"
  shows "=tag= \<subseteq> \<approx>A"
using assms unfolding str_eq_def tag_eq_def
apply(clarify, simp (no_asm_use))
by metis

lemma finite_eq_tag_rel:
  assumes rng_fnt: "finite (range tag)"
  shows "finite (UNIV // =tag=)"
proof -
  let "?f" =  "\<lambda>X. tag ` X" and ?A = "(UNIV // =tag=)"
  have "finite (?f ` ?A)" 
  proof -
    have "range ?f \<subseteq> (Pow (range tag))" unfolding Pow_def by auto
    moreover 
    have "finite (Pow (range tag))" using rng_fnt by simp
    ultimately 
    have "finite (range ?f)" unfolding image_def by (blast intro: finite_subset)
    moreover
    have "?f ` ?A \<subseteq> range ?f" by auto
    ultimately show "finite (?f ` ?A)" by (rule rev_finite_subset) 
  qed
  moreover
  have "inj_on ?f ?A"
  proof -
    { fix X Y
      assume X_in: "X \<in> ?A"
        and  Y_in: "Y \<in> ?A"
        and  tag_eq: "?f X = ?f Y"
      then obtain x y 
        where "x \<in> X" "y \<in> Y" "tag x = tag y"
        unfolding quotient_def Image_def image_def tag_eq_def
        by (simp) (blast)
      with X_in Y_in 
      have "X = Y"
        unfolding quotient_def tag_eq_def by auto
    } 
    then show "inj_on ?f ?A" unfolding inj_on_def by auto
  qed
  ultimately show "finite (UNIV // =tag=)" by (rule finite_imageD)
qed

lemma refined_partition_finite:
  assumes fnt: "finite (UNIV // R1)"
  and refined: "R1 \<subseteq> R2"
  and eq1: "equiv UNIV R1" and eq2: "equiv UNIV R2"
  shows "finite (UNIV // R2)"
proof -
  let ?f = "\<lambda>X. {R1 `` {x} | x. x \<in> X}" 
    and ?A = "UNIV // R2" and ?B = "UNIV // R1"
  have "?f ` ?A \<subseteq> Pow ?B"
    unfolding image_def Pow_def quotient_def by auto
  moreover
  have "finite (Pow ?B)" using fnt by simp
  ultimately  
  have "finite (?f ` ?A)" by (rule finite_subset)
  moreover
  have "inj_on ?f ?A"
  proof -
    { fix X Y
      assume X_in: "X \<in> ?A" and Y_in: "Y \<in> ?A" and eq_f: "?f X = ?f Y"
      from quotientE [OF X_in]
      obtain x where "X = R2 `` {x}" by blast
      with equiv_class_self[OF eq2] have x_in: "x \<in> X" by simp
      then have "R1 ``{x} \<in> ?f X" by auto
      with eq_f have "R1 `` {x} \<in> ?f Y" by simp
      then obtain y 
        where y_in: "y \<in> Y" and eq_r1_xy: "R1 `` {x} = R1 `` {y}" by auto
      with eq_equiv_class[OF _ eq1] 
      have "(x, y) \<in> R1" by blast
      with refined have "(x, y) \<in> R2" by auto
      with quotient_eqI [OF eq2 X_in Y_in x_in y_in]
      have "X = Y" .
    } 
    then show "inj_on ?f ?A" unfolding inj_on_def by blast 
  qed
  ultimately show "finite (UNIV // R2)" by (rule finite_imageD)
qed

lemma tag_finite_imageD:
  assumes rng_fnt: "finite (range tag)" 
  and     refined: "=tag=  \<subseteq> \<approx>A"
  shows "finite (UNIV // \<approx>A)"
proof (rule_tac refined_partition_finite [of "=tag="])
  show "finite (UNIV // =tag=)" by (rule finite_eq_tag_rel[OF rng_fnt])
next
  show "=tag= \<subseteq> \<approx>A" using refined .
next
  show "equiv UNIV =tag="
  and  "equiv UNIV (\<approx>A)" 
    unfolding equiv_def str_eq_def tag_eq_def refl_on_def sym_def trans_def
    by auto
qed


subsection \<open>Base cases: @{const Zero}, @{const One} and @{const Atom}\<close>

lemma quot_zero_eq:
  shows "UNIV // \<approx>{} = {UNIV}"
unfolding quotient_def Image_def str_eq_def by auto

lemma quot_zero_finiteI [intro]:
  shows "finite (UNIV // \<approx>{})"
unfolding quot_zero_eq by simp


lemma quot_one_subset:
  shows "UNIV // \<approx>{[]} \<subseteq> {{[]}, UNIV - {[]}}"
proof
  fix x
  assume "x \<in> UNIV // \<approx>{[]}"
  then obtain y where h: "x = {z. y \<approx>{[]} z}" 
    unfolding quotient_def Image_def by blast
  { assume "y = []"
    with h have "x = {[]}" by (auto simp: str_eq_def)
    then have "x \<in> {{[]}, UNIV - {[]}}" by simp }
  moreover
  { assume "y \<noteq> []"
    with h have "x = UNIV - {[]}" by (auto simp: str_eq_def)
    then have "x \<in> {{[]}, UNIV - {[]}}" by simp }
  ultimately show "x \<in> {{[]}, UNIV - {[]}}" by blast
qed

lemma quot_one_finiteI [intro]:
  shows "finite (UNIV // \<approx>{[]})"
by (rule finite_subset[OF quot_one_subset]) (simp)


lemma quot_atom_subset:
  "UNIV // (\<approx>{[c]}) \<subseteq> {{[]},{[c]}, UNIV - {[], [c]}}"
proof 
  fix x 
  assume "x \<in> UNIV // \<approx>{[c]}"
  then obtain y where h: "x = {z. (y, z) \<in> \<approx>{[c]}}" 
    unfolding quotient_def Image_def by blast
  show "x \<in> {{[]},{[c]}, UNIV - {[], [c]}}"
  proof -
    { assume "y = []" hence "x = {[]}" using h 
        by (auto simp: str_eq_def) } 
    moreover 
    { assume "y = [c]" hence "x = {[c]}" using h 
        by (auto dest!: spec[where x = "[]"] simp: str_eq_def) } 
    moreover 
    { assume "y \<noteq> []" and "y \<noteq> [c]"
      hence "\<forall> z. (y @ z) \<noteq> [c]" by (case_tac y, auto)
      moreover have "\<And> p. (p \<noteq> [] \<and> p \<noteq> [c]) = (\<forall> q. p @ q \<noteq> [c])" 
        by (case_tac p, auto)
      ultimately have "x = UNIV - {[],[c]}" using h
        by (auto simp add: str_eq_def)
    } 
    ultimately show ?thesis by blast
  qed
qed

lemma quot_atom_finiteI [intro]:
  shows "finite (UNIV // \<approx>{[c]})"
by (rule finite_subset[OF quot_atom_subset]) (simp)


subsection \<open>Case for @{const Plus}\<close>

definition 
  tag_Plus :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> 'a list \<Rightarrow> ('a lang \<times> 'a lang)"
where
  "tag_Plus A B \<equiv> \<lambda>x. (\<approx>A `` {x}, \<approx>B `` {x})"

lemma quot_plus_finiteI [intro]:
  assumes finite1: "finite (UNIV // \<approx>A)"
  and     finite2: "finite (UNIV // \<approx>B)"
  shows "finite (UNIV // \<approx>(A \<union> B))"
proof (rule_tac tag = "tag_Plus A B" in tag_finite_imageD)
  have "finite ((UNIV // \<approx>A) \<times> (UNIV // \<approx>B))" 
    using finite1 finite2 by auto
  then show "finite (range (tag_Plus A B))"
    unfolding tag_Plus_def quotient_def
    by (rule rev_finite_subset) (auto)
next
  show "=tag_Plus A B= \<subseteq> \<approx>(A \<union> B)"
    unfolding tag_eq_def tag_Plus_def str_eq_def by auto
qed


subsection \<open>Case for \<open>Times\<close>\<close>

definition
  "Partitions x \<equiv> {(x\<^sub>p, x\<^sub>s). x\<^sub>p @ x\<^sub>s = x}"

lemma conc_partitions_elim:
  assumes "x \<in> A \<cdot> B"
  shows "\<exists>(u, v) \<in> Partitions x. u \<in> A \<and> v \<in> B"
using assms unfolding conc_def Partitions_def
by auto

lemma conc_partitions_intro:
  assumes "(u, v) \<in> Partitions x \<and> u \<in> A \<and>  v \<in> B"
  shows "x \<in> A \<cdot> B"
using assms unfolding conc_def Partitions_def
by auto

lemma equiv_class_member:
  assumes "x \<in> A"
  and "\<approx>A `` {x} = \<approx>A `` {y}" 
  shows "y \<in> A"
using assms
apply(simp)
apply(simp add: str_eq_def)
apply(metis append_Nil2)
done

definition 
  tag_Times :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> 'a list \<Rightarrow> 'a lang \<times> 'a lang set"
where
  "tag_Times A B \<equiv> \<lambda>x. (\<approx>A `` {x}, {(\<approx>B `` {x\<^sub>s}) | x\<^sub>p x\<^sub>s. x\<^sub>p \<in> A \<and> (x\<^sub>p, x\<^sub>s) \<in> Partitions x})"

lemma tag_Times_injI:
  assumes a: "tag_Times A B x = tag_Times A B y"
  and     c: "x @ z \<in> A \<cdot> B"
  shows "y @ z \<in> A \<cdot> B"
proof -
  from c obtain u v where 
    h1: "(u, v) \<in> Partitions (x @ z)" and
    h2: "u \<in> A" and
    h3: "v \<in> B" by (auto dest: conc_partitions_elim)
  from h1 have "x @ z = u @ v" unfolding Partitions_def by simp
  then obtain us 
    where "(x = u @ us \<and> us @ z = v) \<or> (x @ us = u \<and> z = us @ v)"
    by (auto simp add: append_eq_append_conv2)
  moreover
  { assume eq: "x = u @ us" "us @ z = v"
    have "(\<approx>B `` {us}) \<in> snd (tag_Times A B x)"
      unfolding Partitions_def tag_Times_def using h2 eq 
      by (auto simp add: str_eq_def)
    then have "(\<approx>B `` {us}) \<in> snd (tag_Times A B y)"
      using a by simp
    then obtain u' us' where
      q1: "u' \<in> A" and
      q2: "\<approx>B `` {us} = \<approx>B `` {us'}" and
      q3: "(u', us') \<in> Partitions y" 
      unfolding tag_Times_def by auto
    from q2 h3 eq 
    have "us' @ z \<in> B"
      unfolding Image_def str_eq_def by auto
    then have "y @ z \<in> A \<cdot> B" using q1 q3 
      unfolding Partitions_def by auto
  }
  moreover
  { assume eq: "x @ us = u" "z = us @ v"
    have "(\<approx>A `` {x}) = fst (tag_Times A B x)" 
      by (simp add: tag_Times_def)
    then have "(\<approx>A `` {x}) = fst (tag_Times A B y)"
      using a by simp
    then have "\<approx>A `` {x} = \<approx>A `` {y}" 
      by (simp add: tag_Times_def)
    moreover 
    have "x @ us \<in> A" using h2 eq by simp
    ultimately 
    have "y @ us \<in> A" using equiv_class_member 
      unfolding Image_def str_eq_def by blast
    then have "(y @ us) @ v \<in> A \<cdot> B" 
      using h3 unfolding conc_def by blast
    then have "y @ z \<in> A \<cdot> B" using eq by simp 
  }
  ultimately show "y @ z \<in> A \<cdot> B" by blast
qed

lemma quot_conc_finiteI [intro]:
  assumes fin1: "finite (UNIV // \<approx>A)" 
  and     fin2: "finite (UNIV // \<approx>B)" 
  shows "finite (UNIV // \<approx>(A \<cdot> B))"
proof (rule_tac tag = "tag_Times A B" in tag_finite_imageD)
  have "\<And>x y z. \<lbrakk>tag_Times A B x = tag_Times A B y; x @ z \<in> A \<cdot> B\<rbrakk> \<Longrightarrow> y @ z \<in> A \<cdot> B"
    by (rule tag_Times_injI)
       (auto simp add: tag_Times_def tag_eq_def)
  then show "=tag_Times A B= \<subseteq> \<approx>(A \<cdot> B)"
    by (rule refined_intro)
       (auto simp add: tag_eq_def)
next
  have *: "finite ((UNIV // \<approx>A) \<times> (Pow (UNIV // \<approx>B)))" 
    using fin1 fin2 by auto
  show "finite (range (tag_Times A B))" 
    unfolding tag_Times_def
    apply(rule finite_subset[OF _ *])
    unfolding quotient_def
    by auto
qed


subsection \<open>Case for @{const "Star"}\<close>

lemma star_partitions_elim:
  assumes "x @ z \<in> A\<star>" "x \<noteq> []"
  shows "\<exists>(u, v) \<in> Partitions (x @ z). strict_prefix u x \<and> u \<in> A\<star> \<and> v \<in> A\<star>"
proof -
  have "([], x @ z) \<in> Partitions (x @ z)" "strict_prefix [] x" "[] \<in> A\<star>" "x @ z \<in> A\<star>"
    using assms by (auto simp add: Partitions_def strict_prefix_def)
  then show "\<exists>(u, v) \<in> Partitions (x @ z). strict_prefix u x \<and> u \<in> A\<star> \<and> v \<in> A\<star>"
    by blast
qed

lemma finite_set_has_max2: 
  "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists> max \<in> A. \<forall> a \<in> A. length a \<le> length max"
apply(induct rule:finite.induct)
apply(simp)
by (metis (no_types) all_not_in_conv insert_iff linorder_le_cases order_trans)

lemma finite_strict_prefix_set: 
  shows "finite {xa. strict_prefix xa (x::'a list)}"
apply (induct x rule:rev_induct, simp)
apply (subgoal_tac "{xa. strict_prefix xa (xs @ [x])} = {xa. strict_prefix xa xs} \<union> {xs}")
by (auto simp:strict_prefix_def)

lemma append_eq_cases:
  assumes a: "x @ y = m @ n" "m \<noteq> []"  
  shows "prefix x m \<or> strict_prefix m x"
unfolding prefix_def strict_prefix_def using a
by (auto simp add: append_eq_append_conv2)

lemma star_spartitions_elim2:
  assumes a: "x @ z \<in> A\<star>" 
  and     b: "x \<noteq> []"
  shows "\<exists>(u, v) \<in> Partitions x. \<exists> (u', v') \<in> Partitions z. strict_prefix u x \<and> u \<in> A\<star> \<and> v @ u' \<in> A \<and> v' \<in> A\<star>"
proof -
  define S where "S = {u | u v. (u, v) \<in> Partitions x \<and> strict_prefix u x \<and> u \<in> A\<star> \<and> v @ z \<in> A\<star>}"
  have "finite {u. strict_prefix u x}" by (rule finite_strict_prefix_set)
  then have "finite S" unfolding S_def
    by (rule rev_finite_subset) (auto)
  moreover 
  have "S \<noteq> {}" using a b unfolding S_def Partitions_def
    by (auto simp: strict_prefix_def)
  ultimately have "\<exists> u_max \<in> S. \<forall> u \<in> S. length u \<le> length u_max"  
    using finite_set_has_max2 by blast
  then obtain u_max v 
    where h0: "(u_max, v) \<in> Partitions x"
    and h1: "strict_prefix u_max x" 
    and h2: "u_max \<in> A\<star>" 
    and h3: "v @ z \<in> A\<star>"  
    and h4: "\<forall> u v. (u, v) \<in> Partitions x \<and> strict_prefix u x \<and> u \<in> A\<star> \<and> v @ z \<in> A\<star> \<longrightarrow> length u \<le> length u_max"
    unfolding S_def Partitions_def by blast
  have q: "v \<noteq> []" using h0 h1 b unfolding Partitions_def by auto
  from h3 obtain a b
    where i1: "(a, b) \<in> Partitions (v @ z)"
    and   i2: "a \<in> A"
    and   i3: "b \<in> A\<star>"
    and   i4: "a \<noteq> []"
    unfolding Partitions_def
    using q by (auto dest: star_decom)
  have "prefix v a"
  proof (rule ccontr)
    assume a: "\<not>(prefix v a)"
    from i1 have i1': "a @ b = v @ z" unfolding Partitions_def by simp
    then have "prefix a v \<or> strict_prefix v a" using append_eq_cases q by blast
    then have q: "strict_prefix a v" using a unfolding strict_prefix_def prefix_def by auto
    then obtain as where eq: "a @ as = v" unfolding strict_prefix_def prefix_def by auto
    have "(u_max @ a, as) \<in> Partitions x" using eq h0 unfolding Partitions_def by auto
    moreover
    have "strict_prefix (u_max @ a) x" using h0 eq q unfolding Partitions_def prefix_def strict_prefix_def by auto
    moreover
    have "u_max @ a \<in> A\<star>" using i2 h2 by simp
    moreover
    have "as @ z \<in> A\<star>" using i1' i2 i3 eq by auto
    ultimately have "length (u_max @ a) \<le> length u_max" using h4 by blast
    with i4 show "False" by auto
  qed
  with i1 obtain za zb
    where k1: "v @ za = a"
    and   k2: "(za, zb) \<in> Partitions z" 
    and   k4: "zb = b" 
    unfolding Partitions_def prefix_def
    by (auto simp add: append_eq_append_conv2)
  show "\<exists> (u, v) \<in> Partitions x. \<exists> (u', v') \<in> Partitions z. strict_prefix u x \<and> u \<in> A\<star> \<and> v @ u' \<in> A \<and> v' \<in> A\<star>"
    using h0 h1 h2 i2 i3 k1 k2 k4 unfolding Partitions_def by blast
qed

definition 
  tag_Star :: "'a lang \<Rightarrow> 'a list \<Rightarrow> ('a lang) set"
where
  "tag_Star A \<equiv> \<lambda>x. {\<approx>A `` {v} | u v. strict_prefix u x \<and> u \<in> A\<star> \<and> (u, v) \<in> Partitions x}"

lemma tag_Star_non_empty_injI:
  assumes a: "tag_Star A x = tag_Star A y"
  and     c: "x @ z \<in> A\<star>"
  and     d: "x \<noteq> []"
  shows "y @ z \<in> A\<star>"
proof -
  obtain u v u' v' 
    where a1: "(u,  v) \<in> Partitions x" "(u', v')\<in> Partitions z"
    and   a2: "strict_prefix u x"
    and   a3: "u \<in> A\<star>"
    and   a4: "v @ u' \<in> A" 
    and   a5: "v' \<in> A\<star>"
    using c d by (auto dest: star_spartitions_elim2)
  have "(\<approx>A) `` {v} \<in> tag_Star A x" 
    apply(simp add: tag_Star_def Partitions_def str_eq_def)
    using a1 a2 a3 by (auto simp add: Partitions_def)
  then have "(\<approx>A) `` {v} \<in> tag_Star A y" using a by simp
  then obtain u1 v1 
    where b1: "v \<approx>A v1"
    and   b3: "u1 \<in> A\<star>"
    and   b4: "(u1, v1) \<in> Partitions y"
    unfolding tag_Star_def by auto
  have c: "v1 @ u' \<in> A\<star>" using b1 a4 unfolding str_eq_def by simp
  have "u1 @ (v1 @ u') @ v' \<in> A\<star>"
    using b3 c a5 by (simp only: append_in_starI)
  then show "y @ z \<in> A\<star>" using b4 a1 
    unfolding Partitions_def by auto
qed
    
lemma tag_Star_empty_injI:
  assumes a: "tag_Star A x = tag_Star A y"
  and     c: "x @ z \<in> A\<star>"
  and     d: "x = []"
  shows "y @ z \<in> A\<star>"
proof -
  from a have "{} = tag_Star A y" unfolding tag_Star_def using d by auto 
  then have "y = []"
    unfolding tag_Star_def Partitions_def strict_prefix_def prefix_def
    by (auto) (metis Nil_in_star append_self_conv2)
  then show "y @ z \<in> A\<star>" using c d by simp
qed

lemma quot_star_finiteI [intro]:
  assumes finite1: "finite (UNIV // \<approx>A)"
  shows "finite (UNIV // \<approx>(A\<star>))"
proof (rule_tac tag = "tag_Star A" in tag_finite_imageD)
  have "\<And>x y z. \<lbrakk>tag_Star A x = tag_Star A y; x @ z \<in> A\<star>\<rbrakk> \<Longrightarrow> y @ z \<in> A\<star>"
    by (case_tac "x = []") (blast intro: tag_Star_empty_injI tag_Star_non_empty_injI)+
  then show "=(tag_Star A)= \<subseteq> \<approx>(A\<star>)"
    by (rule refined_intro) (auto simp add: tag_eq_def)
next
  have *: "finite (Pow (UNIV // \<approx>A))" 
     using finite1 by auto
  show "finite (range (tag_Star A))"
    unfolding tag_Star_def 
    by (rule finite_subset[OF _ *])
       (auto simp add: quotient_def)
qed

subsection \<open>The conclusion of the second direction\<close>

lemma Myhill_Nerode2:
  fixes r::"'a rexp"
  shows "finite (UNIV // \<approx>(lang r))"
by (induct r) (auto)

end
