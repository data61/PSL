(*
Author: Alexander Katovsky
*)

section "Universe"

theory Universe
imports "HOL-ZF.MainZF"
begin


locale Universe = 
  fixes U :: ZF (structure)
  assumes Uempty  : "Elem Empty U"
  and     Usubset : "Elem u U \<Longrightarrow> subset u U"
  and     Usingle : "Elem u U \<Longrightarrow> Elem (Singleton u) U"
  and     Upow    : "Elem u U \<Longrightarrow> Elem (Power u) U"
  and     Uim     : "\<lbrakk>Elem I U ; Elem u (Fun I U) \<rbrakk> \<Longrightarrow> Elem (Sum (Range u)) U"
  and     Unat    : "Elem Nat U"
(*
axiomatization where
  Grothendieck: "\<forall> x . \<exists> uni . (Universe uni) \<and> Elem x uni"
*)
lemma ElemLambdaFun : "(\<And> x .Elem x u \<Longrightarrow> Elem (f x) U) \<Longrightarrow> Elem (Lambda u f) (Fun u U)"
apply (subst Elem_Lambda_Fun)
apply simp
done

lemma RangeRepl: "Range (Lambda A f) = Repl A f"
apply (subst Ext)
apply (subst Range)
apply (simp add: Repl Opair Lambda_def)
done

lemma (in Universe) Utrans: "\<lbrakk>Elem a U ; Elem b a\<rbrakk> \<Longrightarrow> Elem b U"
apply (drule Usubset)
apply (insert HOLZF.subset_def [of a U])
apply (auto simp add: Usubset)
done

lemma ReplId: "Repl A id = A"
by (subst Ext, simp add: Repl)

lemma (in Universe) UniverseSum : "Elem u U \<Longrightarrow> Elem (Sum u) U"
apply (frule_tac u = "Lambda u id" in Uim)
apply (subst Elem_Lambda_Fun)
apply (frule Usubset)
apply (simp add: subset_def)
apply (simp only: RangeRepl ReplId)
done

lemma (in Universe) UniverseUnion: 
  assumes "Elem u U" and "Elem v U"
  shows "Elem (union u v) U"
proof-
  let ?f = "(% x. if x = Empty then u else v)" 
    and ?S = "(Power (Power Empty))"
  have 1: "(Upair u v) = Range (Lambda ?S ?f)"
    by (subst RangeRepl, simp add: Upair_def)
  have 2: "\<lbrakk>Elem u U; Elem v U\<rbrakk> \<Longrightarrow> Elem (Lambda ?S ?f) (Fun ?S U)"
    by (rule ElemLambdaFun, simp)
  show ?thesis using assms
    apply (subst HOLZF.union_def)
    apply (subst 1)
    apply (rule_tac I="?S" in Uim)
    apply (rule Upow)+
    apply (rule Uempty)
    apply (rule 2)
    apply simp+
    done
qed

lemma UPairSingleton: "Upair u v = union (Singleton u) (Singleton v)"
apply (subst Ext)
apply (subst Upair)
apply (subst union)
apply (subst Singleton)+
apply (simp)
done

lemma (in Universe) UniverseUPair: "\<lbrakk>Elem u U ; Elem v U\<rbrakk> \<Longrightarrow> Elem (Upair u v) U"
apply (subst UPairSingleton)
apply (rule UniverseUnion)
apply (rule Usingle, simp)+
done

lemma (in Universe) UniversePair: "\<lbrakk>Elem u U ; Elem v U\<rbrakk> \<Longrightarrow> Elem (Opair u v) U"
apply (subst Opair_def)
apply ((rule UniverseUPair)+, simp+)+
done

lemma (in Universe) "\<lbrakk>Elem u U ; Elem v U\<rbrakk> \<Longrightarrow> Elem (Sum (Repl u (%x . Singleton (Opair x v)))) U"
apply (rule RangeRepl [THEN subst])
apply (rule Uim [of u], simp)
apply (rule ElemLambdaFun)
apply (rule Usingle)
apply (rule UniversePair)
apply (rule Utrans)
apply simp+
done

lemma SumRepl: "Sum (Repl A (Singleton o f)) = Repl A f"
proof-
  show ?thesis
    apply (subst Ext)
    apply (subst Sum)
    apply (subst Repl)+
    apply (auto simp add: Singleton)
    proof-
      fix a
      show "Elem a A \<Longrightarrow> \<exists>y. Elem (f a) y \<and> (\<exists>a. Elem a A \<and> y = Singleton (f a))"
        apply (rule exI [of _ "Singleton (f a)"])
        apply (subst Singleton, simp+)
        apply (rule exI [of _ "a"], simp+)
        done
      qed
    qed


lemma (in Universe) UniverseProd: 
  assumes "Elem u U" and "Elem v U" 
  shows   "Elem (CartProd u v) U"
proof-
  show ?thesis using assms
    apply (subst CartProd_def)
    apply (rule RangeRepl [of u "% x . (Repl v (Opair x))", THEN subst])
    apply (rule Uim [of u], simp)
    apply (rule ElemLambdaFun)
    proof-
      fix x
      show "\<lbrakk>Elem u U; Elem v U; Elem x u\<rbrakk> \<Longrightarrow> Elem (Repl v (Opair x)) U"
        apply (drule Utrans [of u x], simp)
        apply (rule SumRepl [THEN subst])
        apply (rule RangeRepl [THEN subst])
        apply (rule Uim [of v], simp)
        apply (rule ElemLambdaFun,simp)
        apply (rule Usingle)
        apply (rule UniversePair)
        apply (drule Usubset, simp)
        proof-
          fix xa
          show "\<lbrakk>Elem v U; Elem x u; Elem x U; Elem xa v\<rbrakk> \<Longrightarrow> Elem xa U"
            by (rule Utrans, simp+)
        qed
      qed
    qed
          
lemma (in Universe) UniverseSubset: "\<lbrakk>subset u v ; Elem v U\<rbrakk> \<Longrightarrow> Elem u U"
  apply (drule_tac HOLZF.Power [of u v, THEN ssubst])
  apply (drule Upow)
  apply (rule Utrans, simp+)
  done

definition
  Product :: "ZF \<Rightarrow> ZF" where
  "Product U = Sep (Fun U (Sum U)) (%f . (\<forall> u . Elem u U \<longrightarrow> Elem (app f u) u))"

lemma SepSubset: "subset (Sep A p) A"
apply (subst subset_def)
apply (subst Sep, simp)
done

lemma SubsetSmall: 
  assumes "subset A' A" and "subset A B" shows "subset A' B"
  proof-
    have "(subset A' A \<and> subset A B) \<longrightarrow> subset A' B"
      by ((subst subset_def)+, simp+)
    thus ?thesis using assms by simp
  qed

lemma SubsetTrans: 
  assumes "(subset a b)" and "(subset b c)"
  shows "(subset a c)"
proof-
  have "(subset a b) \<and> (subset b c) \<longrightarrow> (subset a c)"
    by ((subst subset_def)+, simp)
  thus ?thesis using assms by simp
qed

lemma SubsetSepTrans: "subset A B \<Longrightarrow> subset (Sep A p) B"
apply (rule SubsetSmall [of "Sep A p" A B])
apply (rule SepSubset)
by simp

lemma ProductSubset: "subset (Product u) (Power (CartProd u (Sum u)))"
apply (subst Product_def)
apply (subst Fun_def)
apply (subst PFun_def)
apply (rule SubsetSepTrans)+
apply (subst subset_def)
by simp

lemma (in Universe) UniverseProduct: "Elem u U \<Longrightarrow> Elem (Product u) U"
apply (rule_tac u="(Product u)" and v="Power (CartProd u (Sum u))" in UniverseSubset)
apply (rule ProductSubset)
apply (rule Upow)
apply (rule UniverseProd, simp)
apply (rule UniverseSum,simp)
done

lemma ZFImageRangeExplode: "x \<in> range explode \<Longrightarrow> f ` x \<in> range explode"
proof-
  assume "x \<in> range explode"
  from this obtain y where "x = explode y" using range_ex1_eq by auto
  hence "f ` x = explode (Repl y f)" using explode_Repl_eq by simp
  thus "f ` x \<in> range explode" by auto
qed

definition "subsetFn X Y \<equiv> \<lambda> x . (if x \<in> Y then x else SOME y . y \<in> Y)"

lemma subsetFn: "\<lbrakk>Y \<noteq> {} ; Y \<subseteq> X \<rbrakk> \<Longrightarrow> (subsetFn X Y) ` X = Y"
proof(auto simp add: subsetFn_def)
  fix x assume "x \<in> Y"
  thus "(SOME y. y \<in> Y) \<in> Y" using someI_ex[of "\<lambda> x . x \<in> Y"] by auto
qed

lemma ZFSubsetRangeExplode: "\<lbrakk>X \<in> range explode ; Y \<subseteq> X\<rbrakk> \<Longrightarrow> Y \<in> range explode"
proof(cases "Y = {}", simp)
  have "explode Empty = {}" using explode_Empty by simp
  thus "{} \<in> range explode" by (auto simp add: explode_def) 
  assume "Y \<noteq> {}" and "Y \<subseteq> X" and "X \<in> range explode" thus "Y \<in> range explode" 
    using ZFImageRangeExplode[of X "subsetFn X Y"] subsetFn[of Y X] by simp
qed

lemma ZFUnionRangeExplode: 
  assumes "\<And> x . x \<in> A \<Longrightarrow> f x \<in> range explode" and "A \<in> range explode" 
  shows "(\<Union> x \<in> A . f x) \<in> range explode"
proof-
  let ?S = "Sep (Sum (Repl (implode A) (implode o f))) (\<lambda> y . \<exists> x  . (Elem x (implode A)) \<and> (Elem y (implode (f x))))"
  have "explode ?S = (\<Union> x \<in> A . f x)"
  proof (auto simp add: UNION_eq explode_def Sep Sum Repl assms Elem_implode cong del: image_cong_simp)
    fix x y assume a: "y \<in> A" and b: "x \<in> f y"
    show "\<exists>z. Elem x z \<and> (\<exists>a. a \<in> A \<and> z = implode (f a))"
      apply (rule exI [where ?x = "implode (f y)"])
      apply (auto simp add: explode_def Sep Sum Repl assms Elem_implode a b cong del: image_cong_simp)
      apply (rule exI [where ?x = y])
      apply (simp add: a)
      done
  qed
  thus ?thesis by auto
qed


lemma ZFUnionNatInRangeExplode: "(\<And> (n :: nat) . f n \<in> range explode) \<Longrightarrow> (\<Union> n . f n) \<in> range explode"
proof-
  assume a: "(\<And> (n :: nat) . f n \<in> range explode)"
  have "explode Nat \<in> range explode" by simp
  moreover have "\<And> n . n \<in> (explode Nat) \<Longrightarrow> (f o Nat2nat) n \<in> range explode" using a
    by(auto simp add: explode_def)
  moreover have "(\<Union> n . f n) = (\<Union> n \<in> (explode Nat) . (f o Nat2nat) n)" 
  proof(auto simp add: Nat2nat_def)
    fix x n assume aa: "x \<in> f n" show "\<exists> n \<in> (explode Nat) . x \<in> f (inv nat2Nat n)"
      apply(rule bexI[where ?x = "nat2Nat n"])
      by(auto simp add: aa inj_nat2Nat explode_Elem)
  qed
  ultimately show "(\<Union> n . f n) \<in> range explode" using ZFUnionRangeExplode by simp
qed

lemma ZFProdFnInRangeExplode: "\<lbrakk>A \<in> range explode ; B \<in> range explode\<rbrakk> \<Longrightarrow> f ` (A \<times> B) \<in> range explode"
proof-
  assume a: "A \<in> range explode" and b: "B \<in> range explode"
  let ?X = "(explode (CartProd (implode A) (implode B)))"
  have "f ` (A \<times> B) = (f  o (\<lambda> z . (Fst z, Snd z))) ` ?X"
  proof(auto simp add: explode_def CartProd image_def Fst Snd)
    {
      fix z y assume z: "z \<in> A" and y: "y \<in> B" show "\<exists>x. (\<exists>a. Elem a (implode A) \<and>
        (\<exists>b. Elem b (implode B) \<and> x = Opair a b)) \<and> f (z, y) = f (Fst x, Snd x)" 
        apply(insert z y a b)
        apply(rule exI[where ?x = "Opair z y"])
        apply(auto simp add: Opair explode_Elem Fst Snd)
        done
    }
    {
      fix a b assume aa: "Elem a (implode A)" and bb: "Elem b (implode B)"
      show "\<exists> x \<in> A . \<exists> y \<in> B . f (a,b) = f (x,y)"
        by(rule bexI[where ?x = a], rule bexI[where ?x = b], simp, insert a b aa bb, auto simp add: explode_Elem)
    }
  qed
  moreover have "?X \<in> range explode" by simp
  ultimately show "f ` (A \<times> B) \<in> range explode" using ZFImageRangeExplode by simp
qed

lemma ZFUnionInRangeExplode: "\<lbrakk>A \<in> range explode ; B \<in> range explode\<rbrakk> \<Longrightarrow> A \<union> B \<in> range explode"
proof-
  assume "A \<in> range explode" and "B \<in> range explode"
  from this obtain A' B' where A': "A = explode A'" and B': "B = explode B'" by auto
  have "A \<union> B = explode (union (implode A) (implode B))"
    by(auto simp add: explode_union  union explode_Elem A' B')
  thus "A \<union> B \<in> range explode" by auto
qed

lemma SingletonInRangeExplode: "{x} \<in> range explode"
proof-
  have "explode (Singleton x) = {x}" by(auto simp add: explode_def Singleton)
  thus ?thesis by auto
qed

definition ZFTriple :: "[ZF,ZF,ZF] \<Rightarrow> ZF" where
  "ZFTriple a b c = Opair (Opair a b) c"
definition "ZFTFst = Fst o Fst"
definition "ZFTSnd = Snd o Fst"
definition "ZFTThd = Snd"

lemma ZFTFst: "ZFTFst (ZFTriple a b c) = a" 
  by(auto simp add: ZFTriple_def ZFTFst_def Fst)
lemma ZFTSnd: "ZFTSnd (ZFTriple a b c) = b"
  by(auto simp add: ZFTriple_def ZFTSnd_def Snd Fst)
lemma ZFTThd: "ZFTThd (ZFTriple a b c) = c" 
  by(auto simp add: ZFTriple_def ZFTThd_def Snd Fst)

lemma ZFTriple: "ZFTriple a b c = ZFTriple a' b' c' \<Longrightarrow> (a = a' \<and> b = b' \<and> c = c')"
by(auto simp add: ZFTriple_def Opair)

lemma ZFSucZero: "Nat2nat (SucNat Empty) = 1"
proof-
  have "nat2Nat 0 = Empty" by auto
  hence "(SucNat Empty) = nat2Nat (Suc 0)" by auto
  hence "Nat2nat (SucNat Empty) = Nat2nat (nat2Nat (Suc 0))" by simp
  also have "... = Suc 0" using Nat2nat_nat2Nat[of "Suc 0"] by simp
  finally show ?thesis by simp
qed

lemma ZFZero: "Nat2nat Empty = 0"
proof-
  have "nat2Nat 0 = Empty" by auto
  hence "Nat2nat Empty = Nat2nat (nat2Nat 0)" by simp
  thus ?thesis using Nat2nat_nat2Nat[of "0"] by simp
qed

lemma ZFSucNeq0: "Elem x Nat \<Longrightarrow> Nat2nat (SucNat x) \<noteq> 0"
by(auto simp add: Nat2nat_SucNat)

end
