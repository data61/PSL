section \<open>Sums in monoids\<close>

theory MonoidSums

imports Main
  "HOL-Algebra.Module"
  RingModuleFacts
  FunctionLemmas
begin

text \<open>We build on the finite product simplifications in FiniteProduct.thy and the analogous ones
for finite sums (see "lemmas" in Ring.thy).\<close>

text \<open>Use as an intro rule\<close>
lemma (in comm_monoid) factors_equal:
  "\<lbrakk>a=b; c=d\<rbrakk> \<Longrightarrow> a\<otimes>\<^bsub>G\<^esub>c =  b\<otimes>\<^bsub>G\<^esub>d"
  by simp


lemma (in comm_monoid) extend_prod:
  fixes a A S
  assumes fin: "finite S" and subset: "A\<subseteq>S" and a: "a\<in>A\<rightarrow>carrier G"
  shows "(\<Otimes>\<^bsub>G\<^esub> x\<in>S. (if x\<in>A then a x else \<one>\<^bsub>G\<^esub>)) = (\<Otimes>\<^bsub>G\<^esub> x\<in>A. a x)"
  (is "(\<Otimes>\<^bsub>G\<^esub> x\<in>S. ?b x) = (\<Otimes>\<^bsub>G\<^esub> x\<in>A. a x)")
proof - 
  from subset have uni:"S = A \<union> (S-A)" by auto
  from assms subset show ?thesis
    apply (subst uni)
    apply (subst finprod_Un_disjoint, auto)
    by (auto cong: finprod_cong if_cong elim: finite_subset simp add:Pi_def finite_subset)
(*Pi_def is key for automation here*)
qed

text \<open>Scalar multiplication distributes over scalar multiplication (on left).\<close>(*Add to module.*)
lemma (in module) finsum_smult:
  "[| c\<in> carrier R; g \<in> A \<rightarrow> carrier M |] ==>
   (c \<odot>\<^bsub>M\<^esub> finsum M g A) = finsum M (%x. c \<odot>\<^bsub>M\<^esub> g x) A "
proof (induct A rule: infinite_finite_induct)
  case (insert a A)
  from insert.hyps insert.prems have 1: "finsum M g (insert a A) = g a \<oplus>\<^bsub>M\<^esub> finsum M g A"
    by (intro finsum_insert, auto)
  from insert.hyps insert.prems have 2: "(\<Oplus>\<^bsub>M\<^esub>x\<in>insert a A. c \<odot>\<^bsub>M\<^esub> g x) = c \<odot>\<^bsub>M\<^esub> g a \<oplus>\<^bsub>M\<^esub>(\<Oplus>\<^bsub>M\<^esub>x\<in>A. c \<odot>\<^bsub>M\<^esub> g x)" 
    by (intro finsum_insert, auto)
  from insert.hyps insert.prems show ?case 
    by (auto simp add:1 2 smult_r_distr)
qed auto

text \<open>Scalar multiplication distributes over scalar multiplication (on right).\<close>(*Add to module.*)
lemma (in module) finsum_smult_r:
  "[| v\<in> carrier M; f \<in> A \<rightarrow> carrier R |] ==>
   (finsum R f A \<odot>\<^bsub>M\<^esub> v) = finsum M (%x. f x \<odot>\<^bsub>M\<^esub> v) A "
proof (induct A rule: infinite_finite_induct)
  case (insert a A)
  from insert.hyps insert.prems have 1: "finsum R f (insert a A) = f a \<oplus>\<^bsub>R\<^esub> finsum R f A"
    by (intro R.finsum_insert, auto)
  from insert.hyps insert.prems have 2: "(\<Oplus>\<^bsub>M\<^esub>x\<in>insert a A. f x \<odot>\<^bsub>M\<^esub> v) = f a \<odot>\<^bsub>M\<^esub> v \<oplus>\<^bsub>M\<^esub>(\<Oplus>\<^bsub>M\<^esub>x\<in>A. f x \<odot>\<^bsub>M\<^esub> v)" 
    by (intro finsum_insert, auto)
  from insert.hyps insert.prems show ?case 
    by (auto simp add:1 2 smult_l_distr)
qed auto

text \<open>A sequence of lemmas that shows that the product does not depend on the ambient group. 
Note I had to dig back into the definitions of foldSet to show this.\<close>
(*Add the following 2 lemmas to Group.*)
lemma foldSet_not_depend:
  fixes A E 
  assumes h1: "D\<subseteq>E"
  shows "foldSetD D f e \<subseteq>foldSetD E f e"
proof -
  from h1 have 1: "\<And>x1 x2. (x1,x2) \<in> foldSetD D f e \<Longrightarrow> (x1, x2) \<in> foldSetD E f e" 
  proof -
    fix x1 x2 
    assume 2: "(x1,x2) \<in> foldSetD D f e"
    from h1 2 show "?thesis x1 x2"
    apply (intro foldSetD.induct[where ?D="D" and ?f="f" and ?e="e" and ?x1.0="x1" and ?x2.0="x2"
        and ?P = "\<lambda>x1 x2. ((x1, x2)\<in> foldSetD E f e)"]) 
      apply auto
     apply (intro emptyI, auto)
    by (intro insertI, auto)
  qed
  from 1 show ?thesis by auto
qed 

lemma foldD_not_depend:
  fixes D E B f e A
  assumes h1: "LCD B D f" and h2: "LCD B E f" and h3: "D\<subseteq>E" and h4: "e\<in>D" and h5: "A\<subseteq>B" and h6: "finite B"
  shows "foldD D f e A = foldD E f e A"
proof - 
  from assms have 1: "\<exists>y. (A,y)\<in>foldSetD D f e"
    apply (intro finite_imp_foldSetD, auto)
     apply (metis finite_subset)
    by (unfold LCD_def, auto)
  from 1 obtain y where 2: "(A,y)\<in>foldSetD D f e" by auto
  from assms 2 have 3: "foldD D f e A = y" by (intro LCD.foldD_equality[of B], auto)
  from h3 have 4: "foldSetD D f e \<subseteq> foldSetD E f e" by (rule foldSet_not_depend)
  from 2 4 have 5: "(A,y)\<in>foldSetD E f e" by auto
  from assms 5 have 6: "foldD E f e A = y" by (intro LCD.foldD_equality[of B], auto)
(*(A,y)\<in>f*)
  from 3 6 show ?thesis by auto
qed

lemma (in comm_monoid) finprod_all1[simp]:
  assumes all1:" \<And>a. a\<in>A\<Longrightarrow>f a = \<one>\<^bsub>G\<^esub>"
  shows "(\<Otimes>\<^bsub>G\<^esub> a\<in>A. f a) = \<one>\<^bsub>G\<^esub>"
(*  "[| \<And>a. a\<in>A\<Longrightarrow>f a = \<one>\<^bsub>G\<^esub> |] ==> (\<Otimes>\<^bsub>G\<^esub> a\<in>A. f a) = \<one>\<^bsub>G\<^esub>" won't work with proof - *)
proof - 
  from assms show ?thesis
    by (simp cong: finprod_cong)
qed

context abelian_monoid
begin
lemmas summands_equal = add.factors_equal
lemmas extend_sum = add.extend_prod
lemmas finsum_all0 = add.finprod_all1
end

end
