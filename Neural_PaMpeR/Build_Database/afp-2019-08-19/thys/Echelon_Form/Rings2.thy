(*
    Title:      Rings2.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Rings\<close>

theory Rings2
imports
   "HOL-Analysis.Analysis"
   "HOL-Computational_Algebra.Polynomial_Factorial"
begin

subsection\<open>Previous lemmas and results\<close>

lemma chain_le:
  fixes I::"nat => 'a set"
  assumes inc: "\<forall>n. I(n) \<subseteq> I(n+1)"
  shows "\<forall>n\<le>m. I(n) \<subseteq> I(m)"
  using assms
proof (induct m)
  case 0
  show ?case by auto
next
  case (Suc m)
  show ?case by (metis Suc_eq_plus1 inc lift_Suc_mono_le)
qed

context Rings.ring
begin

lemma sum_add:
  assumes A: "finite A"
  and B: "finite B"
  shows "sum f A + sum g B = sum f (A - B) + sum g (B - A) + sum (\<lambda>x. f x + g x) (A \<inter> B)"
proof -
  have 1: "sum f A = sum f (A - B) + sum f (A \<inter> B)"
    by (metis A Int_Diff_disjoint Un_Diff_Int finite_Diff finite_Int inf_sup_aci(1) local.sum.union_disjoint)
  have 2: "sum g B = sum g (B - A) + sum g (A \<inter> B)"
    by (metis B Int_Diff_disjoint Int_commute Un_Diff_Int finite_Diff finite_Int local.sum.union_disjoint)
  have 3: "sum f (A \<inter> B) + sum g (A \<inter> B) = sum (\<lambda>x. f x + g x) (A \<inter> B)"
    by (simp add: sum.distrib)
  show ?thesis
    by (simp add: "1" "2" "3" add.assoc add.left_commute)
qed

text\<open>This lemma is presented in the library but for additive abelian groups\<close>

lemma sum_negf:
  "sum (%x. - (f x)::'a) A = - sum f A"
proof (cases "finite A")
  case True thus ?thesis by (induct set: finite) auto
next
  case False thus ?thesis by simp
qed


text\<open>The following lemmas are presented in the library but for other type classes (semiring\_0)\<close>

lemma sum_distrib_left:
  shows "r * sum f A = sum (%n. r * f n) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: distrib_left)
  qed
next
  case False thus ?thesis by simp
qed

lemma sum_distrib_right:
  "sum f A * r = (\<Sum>n\<in>A. f n * r)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: distrib_right)
  qed
next
  case False thus ?thesis by simp
qed

end


context comm_monoid_add
begin

lemma sum_two_elements:
  assumes "a \<noteq> b"
  shows "sum f {a,b} = f a + f b"
  by (metis Diff_cancel assms empty_Diff finite.emptyI infinite_remove add_0_right
    sum.empty sum.insert sum.insert_remove singletonD)

lemma sum_singleton: "sum f {x} = f x"
  by simp

end

subsection\<open>Subgroups\<close>

context group_add
begin
definition "subgroup A \<equiv> (0 \<in> A \<and> (\<forall>a\<in>A. \<forall>b \<in> A. a + b \<in> A) \<and> (\<forall>a\<in>A. -a \<in> A))"

lemma subgroup_0: "subgroup {0}"
  unfolding subgroup_def by auto

lemma subgroup_UNIV: "subgroup (UNIV)"
  unfolding subgroup_def by auto

lemma subgroup_inter:
  assumes "subgroup A" and "subgroup B"
  shows "subgroup (A \<inter> B)"
  using assms unfolding subgroup_def by blast

lemma subgroup_Inter:
  assumes "\<forall>I\<in>S. subgroup I"
  shows "subgroup (\<Inter>S)"
  using assms unfolding subgroup_def by auto

lemma subgroup_Union:
  fixes I::"nat => 'a set"
  defines S: "S\<equiv>{I n|n. n\<in>UNIV}"
  assumes all_subgroup: "\<forall>A\<in>S. subgroup A"
  and inc: "\<forall>n. I(n) \<subseteq> I(n+1)"
  shows "subgroup (\<Union>S)"
unfolding subgroup_def
proof (safe; (unfold Union_iff)?)
  show "\<exists>X\<in>S. 0 \<in> X"
  proof (rule bexI[of _ "I 0"])
    show "I 0 \<in> S" unfolding S by auto
    thus "0 \<in> I 0" using all_subgroup unfolding subgroup_def by auto
  qed
  fix y a ya b assume y: "y \<in> S" and a: "a \<in> y" and ya: "ya \<in> S" and b: "b \<in> ya"
  obtain n m where In: "y=I n" and Im: "ya = I m" using y ya S by auto
  have In_I_max:"I n \<subseteq> I (max n m)" using chain_le[OF inc] by auto
  have Im_I_max:"I m \<subseteq> I (max n m)" using chain_le[OF inc] by auto
  show "\<exists>x\<in>S. a + b \<in> x"
  proof (rule bexI[of _ "I (max n m)"])
    show "a + b \<in> I (max n m)"
      by (metis Im Im_I_max In In_I_max a all_subgroup b in_mono max_def subgroup_def y ya)
    show "I (max n m) \<in> S" using S by auto
  qed
  show "\<exists>x\<in>S. - a \<in> x"
  proof (rule bexI[of _ "I (max n m)"])
    show "- a \<in> I (max n m)" by (metis In In_I_max a all_subgroup in_mono subgroup_def y)
    show "I (max n m) \<in> S" using S by auto
  qed
qed



end

subsection\<open>Ideals\<close>

context Rings.ring
begin

lemma subgroup_left_principal_ideal: "subgroup {r*a|r. r\<in>UNIV}"
proof (unfold subgroup_def, auto)
  show "\<exists>r. 0 = r * a" by (rule exI[of _ 0], simp)
  fix r ra show "\<exists>rb. r * a + ra * a = rb * a"
    by (metis add_0_right combine_common_factor)
  show "\<exists>ra. - (r * a) = ra * a" by (metis minus_mult_left)
qed


definition "left_ideal I = (subgroup I \<and> (\<forall>x\<in>I. \<forall>r. r*x \<in> I))"
definition "right_ideal I = (subgroup I \<and> (\<forall>x\<in>I. \<forall>r. x*r \<in> I))"
definition "ideal I= (left_ideal I \<and> right_ideal I)"

definition "left_ideal_generated S = \<Inter>{I. left_ideal I \<and> S \<subseteq> I}"
definition "right_ideal_generated S = \<Inter>{I. right_ideal I \<and> S \<subseteq> I}"
definition "ideal_generated S = \<Inter>{I. ideal I \<and> S \<subseteq> I}"

definition "left_principal_ideal S =  (\<exists>a. left_ideal_generated {a} = S)"
definition "right_principal_ideal S = (right_ideal S \<and> (\<exists>a. right_ideal_generated {a} = S))"
definition "principal_ideal S = (\<exists>a. ideal_generated {a} = S)"

lemma ideal_inter:
  assumes "ideal I" and "ideal J" shows "ideal (I \<inter> J)"
  using assms
  unfolding ideal_def left_ideal_def right_ideal_def subgroup_def
  by auto

lemma ideal_Inter:
  assumes "\<forall>I\<in>S. ideal I"
  shows "ideal (\<Inter>S)"
proof (unfold ideal_def left_ideal_def right_ideal_def, auto)
  show "subgroup (\<Inter>S)" and "subgroup (\<Inter>S)"
    using subgroup_Inter assms
    unfolding ideal_def left_ideal_def by auto
  fix x r xa assume X: "\<forall>X\<in>S. x \<in> X" and xa: "xa \<in> S"
  show "r * x \<in> xa" by (metis X assms ideal_def left_ideal_def xa)
next
  fix x r xa assume X: "\<forall>X\<in>S. x \<in> X" and xa: "xa \<in> S"
  show "x * r \<in> xa" by (metis X assms ideal_def right_ideal_def xa)
qed


lemma ideal_Union:
  fixes I::"nat => 'a set"
  defines S: "S\<equiv>{I n|n. n\<in>UNIV}"
  assumes all_ideal: "\<forall>A\<in>S. ideal A"
  and inc: "\<forall>n. I(n) \<subseteq> I(n+1)"
  shows "ideal (\<Union>S)"
unfolding ideal_def left_ideal_def right_ideal_def
proof (safe; (unfold Union_iff)?)
  fix y x r
  assume y: "y \<in> S" and x: "x \<in> y"
  obtain n where n: "y=I n" using y S by auto
  show "\<exists>xa\<in>S. r * x \<in> xa"
  proof (rule bexI[of _ "I n"])
    show "r * x \<in> I n" by (metis n assms(2) ideal_def left_ideal_def x y)
    show "I n \<in> S" by (metis n y)
  qed
  show "\<exists>xa\<in>S. x * r \<in> xa"
  proof (rule bexI[of _ "I n"])
    show "x * r \<in> I n" by (metis n assms(2) ideal_def right_ideal_def x y)
    show "I n \<in> S" by (metis n y)
  qed
next
  show "subgroup (\<Union>S)" and "subgroup (\<Union>S)"
    using subgroup_Union
    by (metis (mono_tags) S all_ideal ideal_def inc right_ideal_def)+
qed



lemma ideal_not_empty:
  assumes "ideal I"
  shows "I \<noteq> {}"
  using assms unfolding ideal_def left_ideal_def subgroup_def by auto

lemma ideal_0: "ideal {0}"
  unfolding ideal_def left_ideal_def right_ideal_def using subgroup_0 by auto

lemma ideal_UNIV: "ideal UNIV"
  unfolding ideal_def left_ideal_def right_ideal_def using subgroup_UNIV by auto

lemma ideal_generated_0: "ideal_generated {0} = {0}"
  unfolding ideal_generated_def using ideal_0 by auto

lemma ideal_generated_subset_generator:
  assumes "ideal_generated A = I"
  shows "A \<subseteq> I"
  using assms unfolding ideal_generated_def by auto

lemma left_ideal_minus:
  assumes "left_ideal I"
  and "a\<in>I" and "b\<in>I"
  shows "a - b \<in> I"
  by (metis assms(1) assms(2) assms(3) diff_minus_eq_add left_ideal_def minus_minus subgroup_def)

lemma right_ideal_minus:
  assumes "right_ideal I"
  and "a\<in>I" and "b\<in>I"
  shows "a - b \<in> I"
  by (metis assms(1) assms(2) assms(3) diff_minus_eq_add minus_minus right_ideal_def subgroup_def)

lemma ideal_minus:
  assumes "ideal I"
  and "a\<in>I" and "b\<in>I"
  shows "a - b \<in> I"
  by (metis assms(1) assms(2) assms(3) ideal_def right_ideal_minus)


lemma ideal_ideal_generated: "ideal (ideal_generated S)"
  unfolding ideal_generated_def
  unfolding ideal_def left_ideal_def subgroup_def right_ideal_def
  by blast

lemma sum_left_ideal:
  assumes li_X: "left_ideal X"
  and U_X: "U \<subseteq> X" and U: "finite U"
  shows "(\<Sum>i\<in>U. f i * i) \<in> X"
  using U U_X
proof (induct U)
  case empty show ?case using li_X by (simp add:  left_ideal_def subgroup_def)
next
  case (insert x U)
  have x_in_X: "x \<in> X" using insert.prems by simp
  have fx_x_X: "f x * x \<in> X" using li_X x_in_X unfolding left_ideal_def by simp
  have sum_in_X: "(\<Sum>i\<in>U. f i * i) \<in> X" using insert.prems insert.hyps(3) by simp
  have "(\<Sum>i\<in>(insert x U). f i * i) = f x * x + (\<Sum>i\<in>U. f i * i)"
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "... \<in> X" using li_X fx_x_X sum_in_X unfolding left_ideal_def subgroup_def by auto
  finally show "(\<Sum>i\<in>(insert x U). f i * i) \<in> X" .
qed

lemma sum_right_ideal:
  assumes li_X: "right_ideal X"
  and U_X: "U \<subseteq> X" and U: "finite U"
  shows "(\<Sum>i\<in>U. i * f i) \<in> X"
  using U U_X
proof (induct U)
  case empty show ?case using li_X by (simp add: right_ideal_def subgroup_def)
next
  case (insert x U)
  have x_in_X: "x \<in> X" using insert.prems by simp
  have fx_x_X: "x * f x \<in> X" using li_X x_in_X unfolding right_ideal_def by simp
  have sum_in_X: "(\<Sum>i\<in>U. i * f i) \<in> X" using insert.prems insert.hyps(3) by simp
  have "(\<Sum>i\<in>(insert x U). i * f i) =  x * f x + (\<Sum>i\<in>U. i * f i)"
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "... \<in> X" using li_X fx_x_X sum_in_X unfolding right_ideal_def subgroup_def by auto
  finally show "(\<Sum>i\<in>(insert x U). i * f i) \<in> X" .
qed

lemma left_ideal_generated_subset:
  assumes "S \<subseteq> T"
  shows "left_ideal_generated S \<subseteq> left_ideal_generated T"
  unfolding left_ideal_generated_def using assms by auto

lemma right_ideal_generated_subset:
  assumes "S \<subseteq> T"
  shows "right_ideal_generated S \<subseteq> right_ideal_generated T"
  unfolding right_ideal_generated_def using assms by auto

lemma ideal_generated_subset:
  assumes "S \<subseteq> T"
  shows "ideal_generated S \<subseteq> ideal_generated T"
  unfolding ideal_generated_def using assms by auto

lemma ideal_generated_in:
  assumes "a \<in> A"
  shows "a \<in> ideal_generated A"
  unfolding ideal_generated_def using assms by auto

lemma ideal_generated_repeated: "ideal_generated {a,a} = ideal_generated {a}"
  unfolding ideal_generated_def by auto

end

context ring_1
begin

lemma left_ideal_explicit:
  "left_ideal_generated S = {y. \<exists>f U. finite U \<and> U \<subseteq> S \<and> sum (\<lambda>i. f i * i) U = y}" (is "?S = ?B")
proof
  have S_in_B: "S \<subseteq> ?B"
  proof (auto)
    fix x assume x: "x\<in>S"
    show "\<exists>f U. finite U \<and> U \<subseteq> S \<and> (\<Sum>i\<in>U. f i * i) = x"
      by (rule exI[of _ "\<lambda>i. 1"], rule exI[of _ "{x}"], simp add: x)
  qed
  have left_ideal_B: "left_ideal ?B"
  proof (unfold left_ideal_def, auto)
    show "subgroup ?B"
    proof (unfold subgroup_def, auto)
      show "\<exists>f U. finite U \<and> U \<subseteq> S \<and> (\<Sum>i\<in>U. f i * i) = 0"
        by (rule exI[of _ "id"], rule exI[of _ "{}"], auto)
      fix f A assume A: "finite A" and AS: "A \<subseteq> S"
      show"\<exists>fa Ua. finite Ua \<and> Ua \<subseteq> S \<and> (\<Sum>i\<in>Ua. fa i * i) = - (\<Sum>i\<in>A. f i * i)"
        by (rule exI[of _ "\<lambda>i. - f i"], rule exI[of _ A],
            auto simp add: A AS sum_negf[of "\<lambda>i. f i * i" A])
      fix fa B assume B: "finite B" and BS: "B \<subseteq> S"
      let ?g="\<lambda>i. if i \<in> A - B then f i else if i \<in> B - A then fa i else f i + fa i"
      show "\<exists>fb Ub. finite Ub \<and> Ub \<subseteq> S \<and> (\<Sum>i\<in>Ub. fb i * i)
        = (\<Sum>i\<in>A. f i * i) + (\<Sum>i\<in>B. fa i * i)"
      proof (rule exI[of _ ?g], rule exI[of _ "A \<union> B"], simp add: A B AS BS)
        let ?g2 = "(\<lambda>i. (if i \<in> A \<and> i \<notin> B then f i else
          if i \<in> B - A then fa i else f i + fa i) * i)"
        have "(\<Sum>i\<in>A. f i * i) + (\<Sum>i\<in>B. fa i * i)
          = (\<Sum>i\<in>A - B. f i * i) + (\<Sum>i\<in>B - A. fa i * i) + (\<Sum>i\<in>A\<inter>B. (f i * i) + (fa i * i))"
          by (rule sum_add[OF A B])
        also have "... = (\<Sum>i\<in>A - B. f i * i) + (\<Sum>i\<in>B - A. fa i * i)
          + (\<Sum>i\<in>A \<inter> B. (f i + fa i) * i)"
          by (simp add: distrib_right)
        also have "... =  sum ?g2 (A - B) + sum ?g2 (B - A) + sum ?g2 (A \<inter> B)" by auto
        also have "... = sum ?g2 (A \<union> B)" by (rule sum.union_diff2[OF A B, symmetric])
        finally show "sum ?g2 (A \<union> B) = (\<Sum>i\<in>A. f i * i) + (\<Sum>i\<in>B. fa i * i)" ..
      qed
    qed
    fix f U r assume U: "finite U" and U_in_S: "U \<subseteq> S"
    show "\<exists>fa Ua. finite Ua \<and> Ua \<subseteq> S \<and> (\<Sum>i\<in>Ua. fa i * i) = r * (\<Sum>i\<in>U. f i * i)"
      by (rule exI[of _ "\<lambda>i. r * f i"], rule exI[of _ U])
    (simp add: U U_in_S sum_distrib_left mult_assoc)
  qed
  thus "?S \<subseteq> ?B" using S_in_B unfolding left_ideal_generated_def by auto
next
  show "?B \<subseteq> ?S"
  proof (unfold left_ideal_generated_def, auto)
    fix X f U
    assume li_X: "left_ideal X" and S_X: "S \<subseteq> X" and U: "finite U" and U_in_S: "U \<subseteq> S"
    have U_in_X: "U \<subseteq> X" using U_in_S S_X by simp
    show "(\<Sum>i\<in>U. f i * i) \<in> X"
      by (rule sum_left_ideal[OF li_X U_in_X U])
  qed
qed


lemma right_ideal_explicit:
  "right_ideal_generated S = {y. \<exists>f U. finite U \<and> U \<subseteq> S \<and> sum (\<lambda>i. i * f i) U = y}" (is "?S = ?B")
proof
  have S_in_B: "S \<subseteq> ?B"
  proof (auto)
    fix x assume x: "x\<in>S"
    show "\<exists>f U. finite U \<and> U \<subseteq> S \<and> (\<Sum>i\<in>U. i * f i) = x"
      by (rule exI[of _ "\<lambda>i. 1"], rule exI[of _ "{x}"], simp add: x)
  qed
  have right_ideal_B: "right_ideal ?B"
  proof (unfold right_ideal_def, auto)
    show "subgroup ?B"
    proof (unfold subgroup_def, auto)
      show "\<exists>f U. finite U \<and> U \<subseteq> S \<and> (\<Sum>i\<in>U. i * f i) = 0"
        by (rule exI[of _ "id"], rule exI[of _ "{}"], auto)
      fix f A assume A: "finite A" and AS: "A \<subseteq> S"
      show"\<exists>fa Ua. finite Ua \<and> Ua \<subseteq> S \<and> (\<Sum>i\<in>Ua.  i * fa i) = - (\<Sum>i\<in>A.  i * f i)"
        by (rule exI[of _ "\<lambda>i. - f i"], rule exI[of _ A],
            auto simp add: A AS sum_negf[of "\<lambda>i. i * f i" A])
      fix fa B assume B: "finite B" and BS: "B \<subseteq> S"
      let ?g="\<lambda>i. if i \<in> A - B then f i else if i \<in> B - A then fa i else f i + fa i"
      show "\<exists>fb Ub. finite Ub \<and> Ub \<subseteq> S \<and> (\<Sum>i\<in>Ub. i * fb i)
        = (\<Sum>i\<in>A. i * f i) + (\<Sum>i\<in>B. i * fa i)"
      proof (rule exI[of _ ?g], rule exI[of _ "A \<union> B"], simp add: A B AS BS)
        let ?g2 = "(\<lambda>i. i * (if i \<in> A \<and> i \<notin> B then f i else
          if i \<in> B - A then fa i else f i + fa i))"
        have "(\<Sum>i\<in>A.  i * f i) + (\<Sum>i\<in>B.  i * fa i)
          = (\<Sum>i\<in>A - B.  i * f i) + (\<Sum>i\<in>B - A.  i * fa i) + (\<Sum>i\<in>A\<inter>B. (i * f i) + (i * fa i))"
          by (rule sum_add[OF A B])
        also have "... = (\<Sum>i\<in>A - B. i * f i) + (\<Sum>i\<in>B - A.  i * fa i)
          + (\<Sum>i\<in>A \<inter> B. i * (f i + fa i))"
          by (simp add: distrib_left)
        also have "... =  sum ?g2 (A - B) + sum ?g2 (B - A) + sum ?g2 (A \<inter> B)" by auto
        also have "... = sum ?g2 (A \<union> B)" by (rule sum.union_diff2[OF A B, symmetric])
        finally show "sum ?g2 (A \<union> B) = (\<Sum>i\<in>A. i * f i) + (\<Sum>i\<in>B. i * fa i)" ..
      qed
    qed
    fix f U r assume U: "finite U" and U_in_S: "U \<subseteq> S"
    show "\<exists>fa Ua. finite Ua \<and> Ua \<subseteq> S \<and> (\<Sum>i\<in>Ua. i * fa i) = (\<Sum>i\<in>U. i * f i) * r"
      by (rule exI[of _ "\<lambda>i. f i * r"], rule exI[of _ U])
    (simp add: U U_in_S sum_distrib_right mult_assoc)
  qed
  thus "?S \<subseteq> ?B" using S_in_B unfolding right_ideal_generated_def by auto
next
  show "?B \<subseteq> ?S"
  proof (unfold right_ideal_generated_def, auto)
    fix X f U
    assume li_X: "right_ideal X" and S_X: "S \<subseteq> X" and U: "finite U" and U_in_S: "U \<subseteq> S"
    have U_in_X: "U \<subseteq> X" using U_in_S S_X by simp
    show "(\<Sum>i\<in>U. i * f i) \<in> X"
      by (rule sum_right_ideal[OF li_X U_in_X U])
  qed
qed

end

context comm_ring
begin

lemma left_ideal_eq_right_ideal: "left_ideal I = right_ideal I"
  unfolding left_ideal_def right_ideal_def subgroup_def
  by auto (metis mult_commute)+

corollary ideal_eq_left_ideal: "ideal I = left_ideal I"
  by (metis ideal_def left_ideal_eq_right_ideal)

lemma ideal_eq_right_ideal: "ideal I = right_ideal I"
  by (metis ideal_def left_ideal_eq_right_ideal)

lemma principal_ideal_eq_left:
  "principal_ideal S = (\<exists>a. left_ideal_generated {a} = S)"
  unfolding principal_ideal_def ideal_generated_def left_ideal_generated_def
  unfolding ideal_eq_left_ideal ..

end

context comm_ring_1
begin

lemma ideal_generated_eq_left_ideal: "ideal_generated A = left_ideal_generated A"
  unfolding ideal_generated_def ideal_def
  by (metis (no_types, lifting) Collect_cong left_ideal_eq_right_ideal left_ideal_generated_def)

lemma ideal_generated_eq_right_ideal: "ideal_generated A = right_ideal_generated A"
  unfolding ideal_generated_def ideal_def
  by (metis (no_types, lifting) Collect_cong left_ideal_eq_right_ideal right_ideal_generated_def)


lemma obtain_sum_ideal_generated:
  assumes a: "a \<in> ideal_generated A" and A: "finite A"
  obtains f where "sum (\<lambda>i. f i * i) A = a"
proof -
  obtain g U where g: "sum (\<lambda>i. g i * i) U = a" and UA: "U \<subseteq> A" and U: "finite U"
    using a unfolding ideal_generated_eq_left_ideal
    unfolding left_ideal_explicit by blast
  let ?f="\<lambda>i. if i \<in> A - U then 0 else g i"
  have A_union: "A = (A - U) \<union> U" using UA by auto
  have "sum (\<lambda>i. ?f i * i) A = sum (\<lambda>i. ?f i * i) ((A - U) \<union> U)" using A_union by simp
  also have "... = sum (\<lambda>i. ?f i * i) (A - U) + sum (\<lambda>i. ?f i * i) U"
    by (rule sum.union_disjoint[OF _ U], auto simp add: A U UA)
  also have "... = sum (\<lambda>i. ?f i * i) U" by auto
  also have "... = a" using g by auto
  finally have "sum (\<lambda>i. ?f i * i) A = a" .
  with that show ?thesis .
qed

lemma dvd_ideal_generated_singleton:
  assumes subset: "ideal_generated {a} \<subseteq> ideal_generated {b}"
  shows "b dvd a"
proof -
 have "a \<in> ideal_generated {a}" by (simp add: ideal_generated_in)
 hence a: "a \<in> ideal_generated {b}" by (metis subset subsetCE)
 obtain f where "sum (\<lambda>i. f i * i) {b} = a" by (rule obtain_sum_ideal_generated[OF a], simp)
 hence fb_b_a: "f b * b = a" unfolding sum_singleton .
 show ?thesis unfolding dvd_def by (rule exI[of _ "f b"], metis fb_b_a mult_commute)
qed

lemma ideal_generated_singleton: "ideal_generated {a} = {k*a|k. k \<in> UNIV}"
proof (auto simp add: ideal_generated_eq_left_ideal left_ideal_explicit)
  fix f U
  assume U: "finite U" and U_in_a: "U \<subseteq> {a}"
  show "\<exists>k. (\<Sum>i\<in>U. f i * i) = k * a"
  proof (cases "U={}")
    case True show ?thesis by (rule exI[of _ 0], simp add: True)
  next
    case False
    hence Ua: "U = {a}" using U_in_a by auto
    show ?thesis by (rule exI[of _ "f a"]) (simp add: Ua sum_singleton)
  qed
next
  fix k
  show " \<exists>f U. finite U \<and> U \<subseteq> {a} \<and> (\<Sum>i\<in>U. f i * i) = k * a"
    by (rule exI[of _ "\<lambda>i. k"], rule exI[of _ "{a}"], simp)
qed


lemma dvd_ideal_generated_singleton':
  assumes b_dvd_a: "b dvd a"
  shows "ideal_generated {a} \<subseteq> ideal_generated {b}"
  apply (simp only: ideal_generated_singleton)
  using assms unfolding dvd_def
  apply auto
  apply (simp_all only: mult_commute)
  unfolding mult_assoc[symmetric]
  apply blast
  done


lemma ideal_generated_subset2:
  assumes ac: "ideal_generated {a} \<subseteq> ideal_generated {c}"
  and bc: "ideal_generated {b} \<subseteq> ideal_generated {c}"
  shows "ideal_generated {a,b} \<subseteq> ideal_generated {c}"
proof
  fix x
  assume x: "x \<in> ideal_generated {a, b}"
  show " x \<in> ideal_generated {c}"
  proof (cases "a=b")
    case True
    show ?thesis using x bc unfolding True ideal_generated_repeated by fast
  next
    case False
    obtain k where k: "a = c * k"
      using dvd_ideal_generated_singleton[OF ac] unfolding dvd_def by auto
    obtain k' where k': "b = c * k'"
      using dvd_ideal_generated_singleton[OF bc] unfolding dvd_def by auto
    obtain f where f: "sum (\<lambda>i. f i * i) {a,b} = x"
      by (rule obtain_sum_ideal_generated[OF x], simp)
    hence "x = f a * a + f b * b " unfolding sum_two_elements[OF False] by simp
    also have "... = f a * (c * k) + f b * (c * k')" unfolding k k' by simp
    also have "... = (f a * k) * c + (f b * k') * c"
      by (simp only: mult_assoc) (simp only: mult_commute)
    also have "... = (f a * k +  f b * k') * c"
      by (simp only: mult_commute) (simp only: distrib_left)
    finally have "x = (f a * k + f b * k') * c" .
    thus ?thesis unfolding ideal_generated_singleton by auto
  qed
qed

end

lemma ideal_kZ: "ideal {k*x|x. x\<in>(UNIV::int set)}"
  unfolding ideal_def left_ideal_def right_ideal_def subgroup_def
  apply auto
  apply (metis int_distrib(2))
  apply (metis minus_mult_right)
  apply (metis int_distrib(2))
  apply (metis minus_mult_right)
  done

subsection\<open>GCD Rings and Bezout Domains\<close>

text\<open>To define GCD rings and Bezout rings, there are at least two options:
fix the operation gcd or just assume its existence. We have chosen the second one in order to be
able to use subclasses (if we fix a gcd in the bezout ring class, then we couln't prove that
principal ideal rings are a subclass of bezout rings).\<close>

class GCD_ring = comm_ring_1
  + assumes exists_gcd: "\<exists>d. d dvd a \<and> d dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d)"
begin

text\<open>In this structure, there is always a gcd for each pair of elements, but maybe not unique.
The following definition essentially says if a function satisfies the condition to be a gcd.\<close>

definition is_gcd :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "is_gcd (gcd') = (\<forall>a b. (gcd' a b dvd a)
                          \<and> (gcd' a b dvd b)
                          \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd' a b))"

lemma gcd'_dvd1:
  assumes "is_gcd gcd'" shows "gcd' a b dvd a" using assms unfolding is_gcd_def by auto

lemma gcd'_dvd2:
  assumes "is_gcd gcd'" shows "gcd' a b dvd b"
  using assms unfolding is_gcd_def by auto

lemma gcd'_greatest:
  assumes "is_gcd gcd'" and "l dvd a" and "l dvd b"
  shows "l dvd gcd' a b"
  using assms unfolding is_gcd_def by auto

lemma gcd'_zero [simp]:
  assumes "is_gcd gcd'"
  shows "gcd' x y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (metis dvd_0_left dvd_refl gcd'_dvd1 gcd'_dvd2 gcd'_greatest assms)+

end

class GCD_domain = GCD_ring + idom

class bezout_ring = comm_ring_1 +
        assumes exists_bezout: "\<exists>p q d. (p*a + q*b = d)
                    \<and> (d dvd a)
                    \<and> (d dvd b)
                    \<and> (\<forall>d'. (d' dvd a \<and> d' dvd b) \<longrightarrow> d' dvd d)"
begin

subclass GCD_ring
proof
  fix a b
  show "\<exists>d. d dvd a \<and> d dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d)"
    using exists_bezout[of a b] by auto
qed

text\<open>In this structure, there is always a bezout decomposition for each pair of elements, but it is
not unique. The following definition essentially says if a function satisfies the condition to be a
bezout decomposition.\<close>

definition is_bezout :: "('a \<Rightarrow>'a \<Rightarrow> ('a \<times> 'a \<times> 'a)) \<Rightarrow> bool"
  where "is_bezout (bezout) = (\<forall>a b. let (p, q, gcd_a_b) = bezout a b
                                      in
                                        p * a + q * b = gcd_a_b
                                        \<and> (gcd_a_b dvd a)
                                        \<and> (gcd_a_b dvd b)
                                        \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd_a_b))"

text\<open>The following definition is similar to the previous one, and checks if the input is a
function that given two parameters \<open>a b\<close> returns 5 elements \<open>(p,q,u,v,d)\<close>
where \<open>d\<close> is a gcd of \<open>a\<close> and \<open>b\<close>, \<open>p\<close> and \<open>q\<close> are the
bezout coefficients such that \<open>p*a+q*b=d\<close>, \<open>d*u = -b\<close> and \<open>d*v= a\<close>.
The elements \<open>u\<close> and \<open>v\<close> are useful for defining the bezout matrix.\<close>

definition is_bezout_ext :: "('a \<Rightarrow>'a \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a)) \<Rightarrow> bool"
  where "is_bezout_ext (bezout) = (\<forall>a b. let (p, q, u, v, gcd_a_b) = bezout a b
                                          in
                                            p * a + q * b = gcd_a_b
                                            \<and> (gcd_a_b dvd a)
                                            \<and> (gcd_a_b dvd b)
                                            \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd_a_b)
                                            \<and> gcd_a_b * u = -b
                                            \<and> gcd_a_b * v = a)"

lemma is_gcd_is_bezout_ext:
  assumes "is_bezout_ext bezout"
  shows "is_gcd (\<lambda>a b. case bezout a b of (x, xa,u,v, gcd') \<Rightarrow> gcd')"
  unfolding is_gcd_def using assms unfolding is_bezout_ext_def Let_def by (simp add: split_beta)

lemma is_bezout_ext_is_bezout:
  assumes "is_bezout_ext bezout"
  shows "is_bezout (\<lambda>a b. case bezout a b of (x,xa,u,v, gcd') \<Rightarrow> (x,xa,gcd'))"
  unfolding is_bezout_def using assms unfolding is_bezout_ext_def Let_def by (simp add: split_beta)

lemma is_gcd_is_bezout:
  assumes "is_bezout bezout"
  shows "is_gcd (\<lambda>a b. (case bezout a b of (_, _, gcd') \<Rightarrow> (gcd')))"
  unfolding is_gcd_def using assms unfolding is_bezout_def Let_def by (simp add: split_beta)

text\<open>The assumptions of the Bezout rings say that there exists a bezout operation.
  Now we will show that there also exists an operation satisfying \<open>is_bezout_ext\<close>\<close>

lemma exists_bezout_ext_aux:
  fixes a and b
  shows "\<exists>p q u v d. (p * a + q * b = d)
                    \<and> (d dvd a)
                    \<and> (d dvd b)
                    \<and> (\<forall>d'. (d' dvd a \<and> d' dvd b) \<longrightarrow> d' dvd d) \<and> d * u = -b \<and> d * v = a"
proof -
  obtain p q d where prems01: "(p * a + q * b = d)
                    \<and> (d dvd a)
                    \<and> (d dvd b)
                    \<and> (\<forall>d'. (d' dvd a \<and> d' dvd b) \<longrightarrow> d' dvd d)"
                    using exists_bezout [of a b] by fastforce
  hence db: "d dvd b" and da: "d dvd a" by blast+
  obtain u v where prems02: "d * u = -b" and prems03: "d * v = a" using db and da
    by (metis local.dvdE local.minus_mult_right)
  show ?thesis using exI [of _ "(p,q,u,v,d)"] prems01 prems02 prems03
  by metis
qed

lemma exists_bezout_ext: "\<exists>bezout_ext. is_bezout_ext bezout_ext"
proof -
  define bezout_ext where "bezout_ext a b = (SOME (p,q,u,v,d). p * a + q * b = d
    \<and> (d dvd a) \<and> (d dvd b) \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d) \<and> d * u = -b \<and> d * v = a)"
    for a b
  show ?thesis
  proof (rule exI [of _ bezout_ext], unfold is_bezout_ext_def, rule+)
    fix a b
    obtain p q u v d where foo: "p * a + q * b = d \<and>
              d dvd a \<and>
              d dvd b \<and>
              (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d) \<and>
              d * u = - b \<and> d * v = a" using exists_bezout_ext_aux [of a b] by fastforce
    show "let (p, q, u, v, gcd_a_b) = bezout_ext a b
           in p * a + q * b = gcd_a_b \<and>
              gcd_a_b dvd a \<and>
              gcd_a_b dvd b \<and>
              (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd_a_b) \<and>
              gcd_a_b * u = - b \<and> gcd_a_b * v = a"
      by (unfold bezout_ext_def Let_def, rule someI [of _ "(p,q,u,v,d)"], clarify, rule foo)
   qed
qed

end

class bezout_domain = bezout_ring + idom

subclass (in bezout_domain) GCD_domain
proof
qed

class bezout_ring_div = bezout_ring + euclidean_semiring
class bezout_domain_div = bezout_domain + euclidean_semiring

subclass (in bezout_ring_div) bezout_domain_div
proof qed

subsection\<open>Principal Ideal Domains\<close>

class pir = comm_ring_1 + assumes all_ideal_is_principal: "ideal I \<Longrightarrow> principal_ideal I"
class pid = idom + pir

text\<open>Thanks to the following proof, we will show that there exist bezout and gcd operations
in principal ideal rings for each pair of elements.\<close>

subclass (in pir) bezout_ring
proof
  fix a b
  define S where "S = ideal_generated {a,b}"
  have ideal_S: "ideal S" using ideal_ideal_generated unfolding S_def by simp
  obtain d where d: "ideal_generated {d} = S" using all_ideal_is_principal[OF ideal_S]
    unfolding principal_ideal_def by blast
  have ideal_d: "ideal (ideal_generated {d})" using ideal_ideal_generated by simp
  have a_subset_d: "ideal_generated {a} \<subseteq> ideal_generated {d}"
    by (metis S_def d insertI1 ideal_generated_subset singletonD subsetI)
  have b_subset_d: "ideal_generated {b} \<subseteq> ideal_generated {d}"
    by (metis S_def d insert_iff ideal_generated_subset subsetI)
  have d_in_S: "d \<in> S" by (metis d insert_subset ideal_generated_subset_generator)
  obtain f U where U: "U \<subseteq> {a,b}" and f: "sum (\<lambda>i. f i * i) U = d"
    using left_ideal_explicit[of "{a,b}"] d_in_S unfolding S_def ideal_generated_eq_left_ideal
    by auto
  define g where "g i = (if i \<in> U then f i else 0)" for i
  show "\<exists>p q d. p * a + q * b = d \<and> d dvd a \<and> d dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d)"
  proof (cases "a = b")
    case True
    show ?thesis
    proof (rule exI[of _ "g a"], rule exI[of _ "0"], rule exI[of _ d], auto)
      show ga_a_d: "g a * a = d"
        unfolding g_def
      proof auto
        assume "a \<in> U"
        hence Ua: "U = {a}" using U True by auto
        show "f a * a = d" using f unfolding Ua
          unfolding sum_singleton .
      next
        assume "a \<notin> U"
        hence U_empty: "U = {}" using U True by auto
        show "0 = d" using f unfolding U_empty by auto
      qed
      show "d dvd a" by (rule dvd_ideal_generated_singleton[OF a_subset_d])
      show "d dvd b" by (rule dvd_ideal_generated_singleton[OF b_subset_d])
      fix d' assume d'_dvd_a: "d' dvd a" and d'_dvd_b: "d' dvd b"
      show "d' dvd d" by (metis ga_a_d d'_dvd_a dvd_mult2 mult_commute)
    qed
  next
    case False
    show ?thesis
    proof (rule exI[of _ "g a"], rule exI[of _ "g b"], rule exI[of _ d], auto)
      show "g a * a + g b * b = d"
      proof (auto simp add: g_def)
        assume a: "a \<in> U" and b: "b \<in> U"
        hence U_ab: "U = {a,b}" using U by auto
        show "f a * a + f b * b = d"  using f unfolding U_ab sum_two_elements[OF False] .
      next
        assume a: "a \<in> U" and b: "b \<notin> U"
        hence U_a: "U = {a}" using U by auto
        show "f a * a = d" using f unfolding U_a sum_singleton .
      next
        assume a: "a \<notin> U" and b: "b \<in> U"
        hence U_b: "U = {b}" using U by auto
        show "f b * b = d" using f unfolding U_b sum_singleton .
      next
        assume a: "a \<notin> U" and b: "b \<notin> U"
        hence "U = {}" using U by auto
        thus "0 = d" using f by auto
      qed
      show "d dvd a" by (rule dvd_ideal_generated_singleton[OF a_subset_d])
      show "d dvd b" by (rule dvd_ideal_generated_singleton[OF b_subset_d])
      fix d' assume d'a: "d' dvd a" and d'b: "d' dvd b"
      have ad': "ideal_generated {a} \<subseteq> ideal_generated {d'}"
        by (rule dvd_ideal_generated_singleton'[OF d'a])
      have bd': "ideal_generated {b} \<subseteq> ideal_generated {d'}"
        by (rule dvd_ideal_generated_singleton'[OF d'b])
      have abd': "ideal_generated {a,b} \<subseteq> ideal_generated {d'}"
        by (rule ideal_generated_subset2[OF ad' bd'])
      hence dd': "ideal_generated {d} \<subseteq> ideal_generated {d'}"
        by (simp add: S_def d)
      show "d' dvd d" by (rule dvd_ideal_generated_singleton[OF dd'])
    qed
  qed
qed

subclass (in pid) bezout_domain
proof
qed

context pir
begin

lemma ascending_chain_condition:
  fixes I::"nat=>'a set"
  assumes all_ideal: "\<forall>n. ideal (I(n))"
  and inc: "\<forall>n. I(n) \<subseteq> I(n+1)"
  shows "\<exists>n. I(n)=I(n+1)"
proof -
  let ?I = "\<Union>{I(n)|n. n\<in>(UNIV::nat set)}"
  have "ideal ?I" using ideal_Union[of I] all_ideal inc by fast
  from this obtain a where a: "ideal_generated {a} = ?I"
    using all_ideal_is_principal
    unfolding principal_ideal_def by fastforce
  have "a \<in> ?I" using a ideal_generated_subset_generator[of "{a}" "?I"] by simp
  from this obtain k where a_Ik: "a \<in> I(k)" using Union_iff[of a "{I n |n. n \<in> UNIV}"] by auto
  show ?thesis
  proof (rule exI[of _ k], rule)
    show "I k \<subseteq> I (k + 1)" using inc by simp
    show "I (k + 1) \<subseteq> I k"
    proof (auto)
      fix x assume x: "x \<in> I (Suc k)"
      have "ideal_generated {a} = I k"
      proof
        have ideal_Ik: "ideal (I (k))" using all_ideal by simp
        show "I k \<subseteq> ideal_generated {a}" using a by auto
        show "ideal_generated {a} \<subseteq> I k"
          by (metis (lifting) a_Ik all_ideal ideal_generated_def
            le_Inf_iff mem_Collect_eq singleton_iff subsetI)
      qed
      thus "x \<in> I k" using x unfolding a by auto
    qed
  qed
qed


lemma ascending_chain_condition2:
  "\<nexists>I::(nat \<Rightarrow> 'a set). (\<forall>n. ideal (I n) \<and> I n \<subset> I (n + 1))"
proof (rule ccontr, auto)
  fix I assume a: "\<forall>n. ideal (I n) \<and> I n \<subset> I (Suc n)"
  hence "\<forall>n. ideal (I n)" "\<forall>n. I n \<subseteq> I (Suc n)" by auto
  hence "\<exists>n. I(n)=I(n+1)" using ascending_chain_condition by auto
  thus False using a by auto
qed

end

class pir_div = pir + euclidean_semiring
class pid_div = pid + euclidean_semiring

subclass (in pir_div) pid_div
proof qed

subclass (in pir_div) bezout_ring_div
proof qed

subclass (in pid_div) bezout_domain_div
proof qed

subsection\<open>Euclidean Domains\<close>

text\<open>We make use of the euclidean ring (domain) class developed by Manuel Eberl.\<close>

subclass (in euclidean_ring) pid
proof
  fix I assume I: "ideal I"
  show "principal_ideal I"
  proof (cases "I={0}")
    case True show ?thesis unfolding principal_ideal_def True
      using ideal_generated_0 ideal_0 by auto
  next
    case False
    have fI_not_empty: "(euclidean_size` (I-{0}))\<noteq>{}" using False ideal_not_empty[OF I] by auto
    from this obtain d where fd: "euclidean_size d
      = Least (\<lambda>i. i \<in> (euclidean_size`(I-{0})))" and d: "d\<in>(I-{0})"
      by (metis (lifting, mono_tags) LeastI_ex imageE ex_in_conv)
    have d_not_0: "d\<noteq>0" using d by simp
    have fd_le: "\<forall>x\<in>I-{0}. euclidean_size d \<le> euclidean_size x"
      by (metis (mono_tags) Least_le fd image_eqI)
    show "principal_ideal I"
    proof (unfold principal_ideal_def, rule exI[of _ d], auto)
      fix x assume x:"x \<in> ideal_generated {d}" show "x \<in> I"
        using x unfolding ideal_generated_def
        by (auto, metis Diff_iff I d)
    next
      fix a assume a: "a \<in> I"
      obtain q r where "a = q * d + r"
        and fr_fd: "euclidean_size r < euclidean_size d"
        using div_mult_mod_eq [of a d, symmetric] d_not_0 mod_size_less
        by blast
      show "a \<in> ideal_generated {d}"
      proof (cases "r=0")
        case True hence "a = q * d" using \<open>a = q * d + r\<close>
          by auto
        then show ?thesis unfolding ideal_generated_def
          unfolding ideal_def right_ideal_def
          by (simp add: ac_simps)
      next
        case False
        hence r_noteq_0: "r \<noteq> 0" by simp
        have "r = a - d * q" using \<open>a = q * d + r\<close>
          by (simp add: algebra_simps)
        also have "... \<in> I"
        proof (rule left_ideal_minus)
          show "left_ideal I" using I unfolding ideal_def by simp
          show "a \<in> I" using a .
          show "d * q \<in> I" using d I unfolding ideal_def right_ideal_def by simp
        qed
        finally have "r \<in> I-{0}" using r_noteq_0 by auto
        hence "euclidean_size d \<le> euclidean_size r" using fd_le by auto
        thus ?thesis using fr_fd by auto
      qed
    qed
  qed
qed

context euclidean_ring_gcd
begin

text\<open>This is similar to the \<open>euclid_ext\<close> operation, but involving two more parameters
to satisfy that \<open>is_bezout_ext euclid_ext2\<close>\<close>

definition euclid_ext2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"
  where "euclid_ext2 a b =
   (fst (bezout_coefficients a b), snd (bezout_coefficients a b), - b div gcd a b, a div gcd a b, gcd a b)"

lemma is_bezout_ext_euclid_ext2: "is_bezout_ext (euclid_ext2)"
proof (unfold is_bezout_ext_def Let_def, clarify, intro conjI)
  fix a b p q u v d
  assume e: "euclid_ext2 a b = (p, q, u, v, d)"
  then have "bezout_coefficients a b = (p, q)" and "gcd a b = d"
    by (auto simp add: euclid_ext2_def)
  then show "p * a + q * b = d"
    by (simp add: bezout_coefficients)
  from \<open>gcd a b = d\<close> show "d dvd a" and "d dvd b"
    by auto
  from \<open>gcd a b = d\<close> show "\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d"
    by auto
  have "a div d = v" and "-b div d = u"
    using e by (auto simp add: euclid_ext2_def)
  then show "d * v = a" and "d * u = - b"
    using \<open>d dvd a\<close> and \<open>d dvd b\<close> by auto
qed

lemma is_bezout_euclid_ext: "is_bezout (\<lambda>a b. (fst (bezout_coefficients a b), snd (bezout_coefficients a b), gcd a b))"
  by (auto simp add: is_bezout_def bezout_coefficients)

end

subclass (in euclidean_ring) pid_div ..


subsection\<open>More gcd structures\<close>

text\<open>The following classes represent structures where there exists a gcd
  for each pair of elements and the operation is fixed.\<close>

class pir_gcd = pir + semiring_gcd
class pid_gcd = pid + pir_gcd

subclass (in euclidean_ring_gcd) pid_gcd ..



subsection\<open>Field\<close>

text\<open>Proving that any field is a euclidean domain. There are alternatives to do this,
see @{url "https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2014-October/msg00034.html"}\<close>

(* TODO Remove *)
class field_euclidean = field + euclidean_ring +
  assumes "euclidean_size = (\<lambda>i. if i = 0 then 0 else 1::nat)"
  and "normalisation_factor = id"

end


(*********** Possible future work: ***********)
(*
  - Prime elements, irreducible elements...
  - Prufer Domain, Noetherian...
*)
