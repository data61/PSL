(*
Author: Alexander Katovsky
*)

section "The Category of Sets"

theory SetCat
imports Functors Universe
begin

notation Elem (infixl "|\<in>|" 70)
notation HOLZF.subset (infixl "|\<subseteq>|" 71)
notation CartProd (infixl "|\<times>|" 75)

definition 
  ZFfun :: "ZF \<Rightarrow> ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "ZFfun d r f \<equiv> Opair (Opair d r) (Lambda d f)"

definition
  ZFfunDom :: "ZF \<Rightarrow> ZF" ("|dom|_" [72] 72) where
  "ZFfunDom f \<equiv> Fst (Fst f)"

definition
  ZFfunCod :: "ZF \<Rightarrow> ZF" ("|cod|_" [72] 72) where
  "ZFfunCod f \<equiv> Snd (Fst f)"

definition
  ZFfunApp :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" (infixl "|@|" 73) where
  "ZFfunApp f x \<equiv> app (Snd f) x"

definition 
  ZFfunComp :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF" (infixl "|o|" 72) where
  "ZFfunComp f g \<equiv> ZFfun ( |dom| f) ( |cod| g) (\<lambda>x. g |@| (f |@| x))"

definition 
  isZFfun :: "ZF \<Rightarrow> bool" where
  "isZFfun drf \<equiv> let f = Snd drf in
                 isOpair drf \<and> isOpair (Fst drf) \<and> isFun f \<and> (f |\<subseteq>| (Domain f) |\<times>| (Range f))
                 \<and> (Domain f = |dom| drf) \<and> (Range f |\<subseteq>| |cod| drf)"

lemma isZFfunE[elim]: "\<lbrakk>isZFfun f ; 
  \<lbrakk>isOpair f ; isOpair (Fst f) ; isFun (Snd f) ; 
  ((Snd f) |\<subseteq>| (Domain (Snd f)) |\<times>| (Range (Snd f))) ; 
  (Domain (Snd f) = |dom| f) \<and> (Range (Snd f) |\<subseteq>| |cod| f)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp add: isZFfun_def Let_def)

definition  
  SET' :: "(ZF, ZF) Category" where
  "SET' \<equiv> \<lparr>
      Category.Obj = {x . True} , 
      Category.Mor = {f . isZFfun f} ,
      Category.Dom = ZFfunDom , 
      Category.Cod = ZFfunCod , 
      Category.Id = \<lambda>x. ZFfun x x (\<lambda>x . x) , 
      Category.Comp = ZFfunComp
  \<rparr>"

definition "SET \<equiv> MakeCat SET'"

lemma ZFfunDom: "|dom| (ZFfun A B f) = A"
by (auto simp add: ZFfun_def ZFfunDom_def Fst)

lemma ZFfunCod: "|cod| (ZFfun A B f) = B"
by (auto simp add: ZFfun_def ZFfunCod_def Snd Fst)

lemma SETfun: 
  assumes "\<forall> x . x |\<in>| A \<longrightarrow> (f x) |\<in>| B"
  shows   "isZFfun (ZFfun A B f)"
proof(auto simp add: isZFfun_def ZFfun_def isOpair Fst Snd 
    ZFfunCod_def ZFfunDom_def isFun_Lambda domain_Lambda Let_def)
  {
    fix x
    have "x |\<in>| Range (Lambda A f) \<Longrightarrow> x |\<in>| B"
      apply(insert isFun_Lambda[of A f])
      apply (drule fun_range_witness[of "Lambda A f" x], simp)
      by (auto simp add: domain_Lambda Lambda_app assms)
  }
  thus "subset (Range (Lambda A f)) B"
    by (auto simp add: subset_def)
  {
    fix x
    have "x |\<in>| (Lambda A f) \<Longrightarrow> x |\<in>| A |\<times>| Range (Lambda A f)" 
      by(auto simp add: CartProd Lambda_def Repl Range)
  }
  thus "(Lambda A f) |\<subseteq>| (A |\<times>| Range (Lambda A f))"
    by (auto simp add: HOLZF.subset_def)
qed

lemma ZFCartProd: 
  assumes "x |\<in>| A |\<times>| B"
  shows   "Fst x |\<in>| A \<and> Snd x |\<in>| B \<and> isOpair x"
proof-
  from CartProd obtain a b 
    where "a |\<in>| A" 
    and   "b |\<in>| B" 
    and   "x = Opair a b" using assms by auto
  thus ?thesis using assms by (auto simp add: Fst Snd isOpair_def)
qed

lemma ZFfunDomainOpair:
  assumes "isFun f"
  and     "x |\<in>| Domain f"
  shows   "Opair x (app f x) |\<in>| f"
proof-
  have "\<exists>! y . Opair x y |\<in>| f" using assms by (auto simp add: unique_fun_value)
  thus "Opair x (app f x) |\<in>| f" by (auto simp add: app_def intro: theI')
qed
  
lemma ZFFunToLambda: 
  assumes 1: "isFun f"
  and     2: "f |\<subseteq>| (Domain f) |\<times>| (Range f)"
  shows   "f = Lambda (Domain f) (\<lambda>x. app f x)"
proof(subst Ext, rule allI, rule iffI)
  {
    fix x assume a: "x |\<in>| f" show "x |\<in>| Lambda (Domain f) (\<lambda>x. app f x)" 
    proof(simp add: Lambda_def Repl, rule exI[of _ "(Fst x)"], rule conjI)
      have b:"isOpair x \<and> Fst x |\<in>| Domain f" using 2 a by (auto simp add: subset_def ZFCartProd)
      thus "Fst x |\<in>| Domain f" ..
      hence "Opair (Fst x) (app f (Fst x)) |\<in>| f" using 1 by (simp add: ZFfunDomainOpair)
      moreover have "Opair (Fst x) (Snd x) |\<in>| f" using a 2 by (auto simp add: FstSnd subset_def b)
      ultimately have "Snd x = (app f (Fst x))" using 1 by (auto simp add: isFun_def)
      hence "Opair (Fst x) (app f (Fst x)) = Opair (Fst x) (Snd x)" by simp
      also have "... = x"  using b by (simp add: FstSnd)
      finally show "x = Opair (Fst x) (app f (Fst x))" ..
    qed
  }
  moreover 
  {
    fix x assume a: "x |\<in>| Lambda (Domain f) (\<lambda>x. app f x)" show "x |\<in>| f"
      proof-
        from Lambda_def obtain a where "a |\<in>| Domain f \<and> x = Opair a (app f a)" 
          using a by (auto simp add: Repl)
        thus ?thesis using a 1 by (auto simp add: ZFfunDomainOpair)
      qed
  }
qed   

lemma ZFfunApp: 
  assumes "x |\<in>| A"
  shows   "(ZFfun A B f) |@| x = f x"
proof-
  have "(ZFfun A B f) |@| x = app (Lambda A f) x" by (simp add: ZFfun_def ZFfunApp_def Snd)
  also have "... = f x" using assms by (simp add: Lambda_app)
  finally show ?thesis .
qed

lemma ZFfun: 
  assumes "isZFfun f" 
  shows   "f = ZFfun ( |dom| f) ( |cod| f) (\<lambda>x. f |@| x)"
proof(auto simp add: ZFfun_def)
  have "isOpair f \<and> isOpair (Fst f)" using assms by (simp add: isZFfun_def[of f] Let_def)
  hence "f = Opair (Opair (Fst (Fst f)) (Snd (Fst f))) (Snd f)" by (simp add: FstSnd)
  hence "f = Opair (Opair ( |dom| f) ( |cod| f)) (Snd f)" using assms by (simp add: ZFfunDom_def ZFfunCod_def)
  moreover have "Snd f = Lambda ( |dom| f) (\<lambda>x . f |@| x)" 
  proof-
    have "|dom| f = Domain (Snd f)" using assms by (simp add: isZFfun_def[of f] Let_def)
    moreover have "isFun (Snd f)" using assms by (simp add: isZFfun_def[of f] Let_def)
    moreover have "(\<lambda>x . f |@| x) = (\<lambda>x . app (Snd f) x)"  by(simp add: ZFfunApp_def)
    moreover have "(Snd f) |\<subseteq>| (Domain (Snd f)) |\<times>| (Range (Snd f))" using assms
      by (auto simp add: isZFfun_def[of f] Let_def)
    ultimately show ?thesis apply simp by(rule ZFFunToLambda[of "Snd f"])
  qed
  ultimately show "f = Opair (Opair ( |dom| f) ( |cod| f)) (Lambda ( |dom| f) (\<lambda>x . f |@| x))" by simp
qed

lemma ZFfun_ext: 
  assumes "\<forall> x . x |\<in>| A \<longrightarrow> f x = g x" 
  shows   "(ZFfun A B f) = (ZFfun A B g)"
proof-
  have "Lambda A f = Lambda A g" using assms by (auto simp add: Lambda_ext)
  thus ?thesis by (simp add: ZFfun_def)
qed

lemma ZFfunExt:
  assumes "|dom| f = |dom| g" and "|cod| f = |cod| g" and funf: "isZFfun f" and fung: "isZFfun g"
  and "\<And> x . x |\<in>| ( |dom| f) \<Longrightarrow> f |@| x = g |@| x"
  shows "f = g"
proof-
  have 1: "f = ZFfun ( |dom| f) ( |cod| f) (\<lambda>x. f |@| x)" using funf by (rule ZFfun)
  have "g = ZFfun ( |dom| g) ( |cod| g) (\<lambda>x. g |@| x)" using fung by (rule ZFfun)
  hence 2: "g = ZFfun ( |dom| f) ( |cod| f) (\<lambda>x. g |@| x)" using assms by simp
  have "ZFfun ( |dom| f) ( |cod| f) (\<lambda>x. f |@| x) = ZFfun ( |dom| f) ( |cod| f) (\<lambda>x. g |@| x)" 
    using assms by (simp add: ZFfun_ext)
  thus ?thesis using 1 2 by simp
qed  

lemma ZFfunDomAppCod: 
  assumes "isZFfun f"
  and     "x |\<in>| |dom|f"
  shows   "f |@| x |\<in>| |cod|f"
proof(simp add: ZFfunApp_def)
  have "app (Snd f) x |\<in>| Range (Snd f)" using assms by (auto simp add: fun_value_in_range )
  thus "app (Snd f) x |\<in>| |cod|f" using assms by (auto simp add: HOLZF.subset_def)
qed

lemma ZFfunComp: 
  assumes "\<forall> x . x |\<in>| A \<longrightarrow> f x |\<in>| B"
  shows   "(ZFfun A B f) |o| (ZFfun B C g) = ZFfun A C (g o f)"
proof (simp add: ZFfunComp_def ZFfunDom ZFfunCod)
  {
    fix x assume a: "x |\<in>| A"
    have "ZFfun B C g  |@| (ZFfun A B f |@| x) = (g o f) x" 
      proof-
        have "(ZFfun A B f |@| x) = f x" using a by (simp add: ZFfunApp)
        hence "ZFfun B C g  |@| (ZFfun A B f |@| x) = g (f x)" using assms a by (simp add: ZFfunApp)
        thus ?thesis by simp
      qed
  }
  thus "ZFfun A C (\<lambda>x. ZFfun B C g |@| (ZFfun A B f |@| x)) = ZFfun A C (g \<circ> f)"
    by (simp add: ZFfun_ext)
qed

lemma ZFfunCompApp: 
  assumes a:"isZFfun f" and b:"isZFfun g" and c:"|dom|g = |cod|f"
  shows "f |o| g = ZFfun ( |dom| f) ( |cod| g) (\<lambda> x . g |@| (f |@| x))"
proof-
  have 1: "f = ZFfun ( |dom| f) ( |cod| f) (\<lambda> x . f |@| x)" using a by (rule ZFfun)
  have 2: "g = ZFfun ( |dom| g) ( |cod| g) (\<lambda> x . g |@| x)" using b by (rule ZFfun)
  have 3: "\<forall> x . x |\<in>| |dom|f \<longrightarrow> (\<lambda>x. f |@| x) x |\<in>| |cod|f" using a by (simp add: ZFfunDomAppCod)
  hence 4: "\<forall> x . x |\<in>| |dom|f \<longrightarrow> (\<lambda>x. g |@| (f |@| x)) x |\<in>| |cod|g" 
    using a b c by (simp add: ZFfunDomAppCod)
  have "f |o| g = ZFfun ( |dom| f) ( |cod| f) (\<lambda> x . f |@| x) |o|
    ZFfun ( |cod| f) ( |cod| g) (\<lambda> x . g |@| x)" using 1 2 c by simp
  hence "f |o| g = ZFfun ( |dom| f) ( |cod| g) (\<lambda> x . g |@| (f |@| x))"
    using 3 by (simp add: ZFfunComp comp_def)
  thus ?thesis using 4 by (simp add: SETfun)
qed  

lemma ZFfunCompAppZFfun: 
  assumes "isZFfun f" and "isZFfun g" and "|dom|g = |cod|f"
  shows   "isZFfun (f |o| g)"
proof-
  have "f |o| g = ZFfun ( |dom| f) ( |cod| g) (\<lambda> x . g |@| (f |@| x))" using assms
    by (simp add: ZFfunCompApp)
  moreover have "\<forall> x . x |\<in>| |dom|f \<longrightarrow> ((\<lambda> x . g |@| (f |@| x)) x) |\<in>| |cod|g" using assms
    by (simp add: ZFfunDomAppCod)
  ultimately show ?thesis by (simp add: SETfun)
qed

lemma ZFfunCompAssoc:
  assumes a: "isZFfun f" and b:"isZFfun h" and c:"|cod|g = |dom|h" 
  and d:"isZFfun g" and e:"|cod|f = |dom|g"
  shows "f |o| g |o| h = f |o| (g |o| h)"
proof-
  have 1: "f = ZFfun ( |dom| f) ( |cod| f) (\<lambda> x . f |@| x)" using a by (rule ZFfun)
  have 2: "g = ZFfun ( |dom| g) ( |cod| g) (\<lambda> x . g |@| x)" using d by (rule ZFfun)
  have 3: "h = ZFfun ( |dom| h) ( |cod| h) (\<lambda> x . h |@| x)" using b by (rule ZFfun)
  have 4: "\<forall> x . x |\<in>| |dom|f \<longrightarrow> (\<lambda>x. f |@| x) x |\<in>| |cod|f" using a by (simp add: ZFfunDomAppCod)
  have "(f |o| g) |o| h = ZFfun ( |dom| f) ( |cod| h) (\<lambda> x . h |@| (g |@| (f |@| x)))"
  proof-
    have 5: "\<forall> x . x |\<in>| |dom|f \<longrightarrow> (\<lambda>x. g |@| (f |@| x)) x |\<in>| |cod|g" 
      using 4 e d by (simp add: ZFfunDomAppCod)
    have "(f |o| g) |o| h = (ZFfun ( |dom| f) ( |cod| f) (\<lambda> x . f |@| x) |o|
      ZFfun ( |cod| f) ( |cod| g) (\<lambda> x . g |@| x)) |o|
      ZFfun ( |cod| g) ( |cod| h) (\<lambda> x . h |@| x)" 
      using 1 2 3 c e by (simp)
    thus ?thesis using 4 5 by (simp add: ZFfunComp comp_def)
  qed
  moreover have "f |o| (g |o| h) = ZFfun ( |dom| f) ( |cod| h) (\<lambda> x . h |@| (g |@| (f |@| x)))"
  proof-
    have 5: "\<forall> x . x |\<in>| |dom|g \<longrightarrow> (\<lambda>x. g |@| x) x |\<in>| |cod|g" using d by (simp add: ZFfunDomAppCod)
    have "f |o| (g |o| h) = ZFfun ( |dom| f) ( |dom| g) (\<lambda> x . f |@| x) |o|
      (ZFfun ( |dom| g) ( |cod| g) (\<lambda> x . g |@| x) |o|
      ZFfun ( |cod| g) ( |cod| h) (\<lambda> x . h |@| x))" 
      using 1 2 3 c e by (simp)
    thus ?thesis using 4 e 5 by (simp add: ZFfunComp comp_def)
  qed
  ultimately show ?thesis by simp
qed
  
lemma ZFfunCompAppDomCod: 
  assumes "isZFfun f" and "isZFfun g" and "|dom|g = |cod|f"
  shows   "|dom| (f |o| g) = |dom| f \<and> |cod| (f |o| g) = |cod| g"
proof-
  have "f |o| g = ZFfun ( |dom| f) ( |cod| g) (\<lambda> x . g |@| (f |@| x))" using assms
    by (simp add: ZFfunCompApp)
  thus ?thesis by (simp add: ZFfunDom ZFfunCod)
qed

lemma ZFfunIdLeft: 
  assumes a: "isZFfun f" shows "(ZFfun ( |dom|f) ( |dom|f) (\<lambda>x. x)) |o| f = f"
proof-
  let ?g = "(ZFfun ( |dom|f) ( |dom|f) (\<lambda>x. x))"
  have "ZFfun ( |dom| f) ( |cod| f) (\<lambda> x . f |@| x) = ?g |o| f" using a 
    by (simp add: ZFfun_ext ZFfunApp ZFfunCompApp SETfun ZFfunCod ZFfunDom)
  moreover have "f = ZFfun ( |dom| f) ( |cod| f) (\<lambda> x . f |@| x)" using a by (rule ZFfun)
  ultimately show ?thesis by simp
qed

lemma ZFfunIdRight:
  assumes a: "isZFfun f" shows "f |o| (ZFfun ( |cod|f) ( |cod|f) (\<lambda>x. x)) = f"
proof-
  let ?g = "(ZFfun ( |cod|f) ( |cod|f) (\<lambda>x. x))"
  have 1: "\<forall> x . x |\<in>| |dom|f \<longrightarrow> (\<lambda>x. f |@| x) x |\<in>| |cod|f" using a by (simp add: ZFfunDomAppCod)
  have "ZFfun ( |dom| f) ( |cod| f) (\<lambda> x . f |@| x) = f |o| ?g" using a 1
    by (simp add: ZFfun_ext ZFfunApp ZFfunCompApp SETfun ZFfunCod ZFfunDom)
  moreover have "f = ZFfun ( |dom| f) ( |cod| f) (\<lambda> x . f |@| x)" using a by (rule ZFfun)
  ultimately show ?thesis by simp
qed

lemma SETCategory: "Category(SET)"
proof-
  have "Category_axioms SET'"  
    by (auto simp add: Category_axioms_def SET'_def ZFfunCompAppDomCod 
      ZFfunCompAppZFfun ZFfunCompAssoc ZFfunIdLeft ZFfunIdRight ZFfunDom ZFfunCod SETfun MapsTo_def CompDefined_def)
  thus ?thesis by (auto simp add: SET_def MakeCat)
qed

lemma SETobj: "X \<in> Obj (SET)"
by (simp add: SET_def SET'_def MakeCat_def)

lemma SETcod: "isZFfun (ZFfun A B f) \<Longrightarrow> cod\<^bsub>SET\<^esub> ZFfun A B f = B"
by(simp add: SET_def MakeCat_def SET'_def ZFfunCod)

lemma SETmor: "(isZFfun f) = (f \<in> mor\<^bsub>SET\<^esub>)"
by(simp add: SET_def MakeCat_def SET'_def)

lemma SETdom: "isZFfun (ZFfun A B f) \<Longrightarrow> dom\<^bsub>SET\<^esub> ZFfun A B f = A"
by(simp add: SET_def MakeCat_def SET'_def ZFfunDom)

lemma SETId: assumes "x |\<in>| X" shows "(Id SET X) |@| x = x"
proof-
  have "X \<in> Obj SET" by (simp add: SET_def SET'_def MakeCat_def)
  hence "isZFfun(Id SET X)" by (simp add: SETCategory Category.CatIdInMor SETmor)
  moreover have "(Id SET X) = ZFfun X X (\<lambda>x. x)" using assms by (simp add: SET_def SET'_def MakeCat_def)
  ultimately show ?thesis using assms by (simp add: ZFfunApp)
qed

lemma SETCompE[elim]: "\<lbrakk>f \<approx>>\<^bsub>SET\<^esub> g ; \<lbrakk>isZFfun f ; isZFfun g ; |cod| f = |dom| g\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (auto simp add: SET_def SET'_def MakeCat_def)

lemma SETmapsTo: "f maps\<^bsub>SET\<^esub> X to Y \<Longrightarrow> isZFfun f \<and> |dom| f = X \<and> |cod| f = Y"
by(auto simp add: MapsTo_def SET_def SET'_def MakeCat_def)

lemma SETComp: assumes "f \<approx>>\<^bsub>SET\<^esub> g" shows "f ;;\<^bsub>SET\<^esub> g = f |o| g"
proof-
  have a: "f \<approx>>\<^bsub>MakeCat SET'\<^esub> g" using assms by (simp add: SET_def)
  have "f ;;\<^bsub>SET\<^esub> g = f ;;\<^bsub>MakeCat SET'\<^esub> g" by (simp add: SET_def)
  also have "... = f ;;\<^bsub>SET'\<^esub> g" using a  by (simp  add: MakeCatComp2)
  finally show ?thesis by (simp add: SET'_def)
qed

lemma SETCompAt:
  assumes "f \<approx>>\<^bsub>SET \<^esub>g" and "x |\<in>|  |dom| f" shows "(f ;;\<^bsub>SET \<^esub>g) |@| x = g |@| (f |@| x)"
proof-
  have "f ;;\<^bsub>SET\<^esub> g = f |o| g" using assms by (simp add: SETComp)
  also have "... = ZFfun ( |dom| f) ( |cod| g) (\<lambda> x . g |@| (f |@| x))" using assms by (auto simp add: ZFfunCompApp)
  finally show ?thesis using assms by (simp add: ZFfunApp)
qed

lemma SETZFfun: 
  assumes "f maps\<^bsub>SET\<^esub> X to Y" shows "f = ZFfun X Y (\<lambda>x . f |@| x)"
proof-
  have "isZFfun f"  using assms by (auto simp add: SETmor)
  hence "f = ZFfun ( |dom| f) ( |cod| f) (\<lambda>x. f |@| x)" by (simp add: ZFfun)
  moreover have "|dom| f = X" and "|cod| f = Y" using assms by (auto simp add: SET_def SET'_def MakeCat_def)
  ultimately show ?thesis by (simp)
qed  

lemma SETfunDomAppCod:
  assumes "f maps\<^bsub>SET \<^esub>X to Y" and "x |\<in>| X"
  shows "f |@| x |\<in>| Y"
proof-
  have 1: "isZFfun f" and "|dom| f = X" and 2: "|cod| f = Y" using assms by (auto simp add: SETmapsTo)
  hence "x |\<in>| |dom| f" using assms by simp
  hence "f |@| x |\<in>| |cod| f" using 1 by (simp add: ZFfunDomAppCod)  
  thus ?thesis using 2 by simp
qed

(*Locally Small Category has an injective map from the morphisms to ZF*)
record ('o,'m) LSCategory = "('o,'m) Category" +
  mor2ZF :: "'m \<Rightarrow> ZF" ("m2z\<index>_" [70] 70)

definition 
  ZF2mor ("z2m\<index>_" [70] 70) where
  "ZF2mor C f \<equiv> THE m . m \<in> mor\<^bsub>C\<^esub> \<and> m2z\<^bsub>C\<^esub> m = f"

definition
  "HOMCollection C X Y \<equiv> {m2z\<^bsub>C\<^esub> f | f . f maps\<^bsub>C\<^esub> X to Y}"

definition
  HomSet ("Hom\<index> _ _" [65, 65] 65)  where
  "HomSet C X Y \<equiv> implode (HOMCollection C X Y)"

locale LSCategory = Category +
  assumes mor2ZFInj: "\<lbrakk>x \<in> mor ; y \<in> mor ; m2z x = m2z y\<rbrakk> \<Longrightarrow> x = y"
  and HOMSetIsSet: "\<lbrakk>X \<in> obj ; Y \<in> obj\<rbrakk> \<Longrightarrow> HOMCollection C X Y \<in> range explode"
  and m2zExt: "mor2ZF C \<in> extensional (Mor C)"

lemma [elim]: "\<lbrakk>LSCategory C ; 
  \<lbrakk>Category C ; \<lbrakk>x \<in> mor\<^bsub>C\<^esub> ; y \<in> mor\<^bsub>C\<^esub> ; m2z\<^bsub>C\<^esub> x = m2z\<^bsub>C\<^esub> y\<rbrakk> \<Longrightarrow>  x = y;
  \<lbrakk>X \<in> obj\<^bsub>C\<^esub> ; Y \<in> obj\<^bsub>C\<^esub>\<rbrakk> \<Longrightarrow> HOMCollection C X Y \<in> range explode\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by(simp add: LSCategory_def LSCategory_axioms_def)

definition
  HomFtorMap :: "('o,'m,'a) LSCategory_scheme \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> ZF" ("Hom\<index>[_,_]" [65,65] 65) where
  "HomFtorMap C X g \<equiv> ZFfun (Hom\<^bsub>C\<^esub> X (dom\<^bsub>C\<^esub> g)) (Hom\<^bsub>C\<^esub> X (cod\<^bsub>C\<^esub> g)) (\<lambda> f . m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> f) ;;\<^bsub>C\<^esub> g))"

definition 
  HomFtor' :: "('o,'m,'a) LSCategory_scheme \<Rightarrow> 'o \<Rightarrow> 
      ('o,ZF,'m,ZF,\<lparr>mor2ZF :: 'm \<Rightarrow> ZF, \<dots> :: 'a\<rparr>,unit) Functor" ("HomP\<index>[_,\<midarrow>]" [65] 65) where
  "HomFtor' C X \<equiv> \<lparr>
        CatDom = C, 
        CatCod = SET ,
        MapM   = \<lambda> g . Hom\<^bsub>C\<^esub>[X,g]
  \<rparr>"

definition HomFtor ("Hom\<index>[_,\<midarrow>]" [65] 65) where "HomFtor C X \<equiv> MakeFtor (HomFtor' C X)"

lemma [simp]: "LSCategory C \<Longrightarrow> Category C"
  by (simp add: LSCategory_def)

lemma (in LSCategory) m2zz2m: 
  assumes "f maps X to Y" shows "(m2z f) |\<in>| (Hom X Y)"
proof-
  have "X \<in> Obj C" and "Y \<in> Obj C" using assms by (simp add: MapsToObj)+
  hence "HOMCollection C X Y \<in> range explode" using assms by (simp add: HOMSetIsSet)
  moreover have "(m2z f) \<in> HOMCollection C X Y" using assms by (auto simp add: HOMCollection_def)
  ultimately have "(m2z f) |\<in>| implode (HOMCollection C X Y)" by (simp add: Elem_implode)
  thus ?thesis by (simp add: HomSet_def) 
qed

lemma (in LSCategory) m2zz2mInv: 
  assumes "f \<in> mor"
  shows "z2m (m2z f) = f"
proof-
  have 1: "f \<in> mor \<and> m2z f = m2z f" using assms by simp
  moreover have "\<exists>! m . m \<in> mor \<and> m2z m = (m2z f)" 
  proof(rule ex_ex1I)
    show "\<exists> m . m \<in> mor \<and> m2z m = (m2z f)" 
      by(rule exI[of _ f], insert 1, simp)
    {
      fix m y assume "m \<in> mor \<and> m2z m = (m2z f)" and "y \<in> mor \<and> m2z y = (m2z f)"
      thus "m = y" by(simp add: mor2ZFInj)
    }
  qed
  ultimately show ?thesis by(simp add: ZF2mor_def the1_equality)
qed

lemma (in LSCategory) z2mm2z: 
  assumes "X \<in> obj" and "Y \<in> obj" and "f |\<in>| (Hom X Y)"
  shows "z2m f maps X to Y \<and> m2z (z2m f) = f"
proof-
  have 1: "\<exists> m . m maps X to Y \<and> m2z m = f"
  proof-
    have "HOMCollection C X Y \<in> range explode" using assms by (simp add: HOMSetIsSet)
    moreover have "f |\<in>| implode (HOMCollection C X Y)" using assms(3) by (simp add: HomSet_def)
    ultimately have "f \<in> HOMCollection C X Y" by (simp add: HOLZF.Elem_implode)
    thus ?thesis by (auto simp add: HOMCollection_def)
  qed
  have 2: "\<exists>! m . m \<in> mor \<and> m2z m = f" 
  proof(rule ex_ex1I)
    show "\<exists> m . m \<in> mor \<and> m2z m = f"
    proof-
      from 1 obtain m where "m \<in> mor \<and> m2z m = f" by auto
      thus ?thesis by auto
    qed
    {
      fix m y assume "m \<in> mor \<and> m2z m = f" and "y \<in> mor \<and> m2z y = f"
      thus "m = y" by(simp add: mor2ZFInj)
    }
  qed
  thus ?thesis
  proof-
    from 1 obtain a where 3: "a maps X to Y \<and> m2z a = f" by auto
    have 4: "a \<in> mor" using 3 by auto
    have "z2m f = a" 
      apply (auto simp add: 3 ZF2mor_def[of _ f])
      apply (rule the1_equality[of "\<lambda> m . m \<in> mor \<and> m2z m = f" a])
      apply (auto simp add: 2 3 4)
      done
    thus ?thesis by (simp add: 3)
  qed
qed

lemma  HomFtorMapLemma1: 
  assumes a: "LSCategory C" and b: "X \<in> obj\<^bsub>C\<^esub>" and c: "f \<in> mor\<^bsub>C\<^esub>" and d: "x |\<in>| (Hom\<^bsub>C\<^esub> X (dom\<^bsub>C\<^esub> f))"
  shows "(m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> f)) |\<in>| (Hom\<^bsub>C\<^esub> X (cod\<^bsub>C\<^esub> f))"
proof-
  have 1: "dom\<^bsub>C\<^esub> f \<in> obj\<^bsub>C\<^esub>" and 2: "cod\<^bsub>C\<^esub> f \<in> obj\<^bsub>C\<^esub>" using a c by (simp add: Category.Simps)+
  have "z2m\<^bsub>C\<^esub> x maps\<^bsub>C\<^esub> X to (dom\<^bsub>C\<^esub> f)"  using a b d 1 by (auto simp add: LSCategory.z2mm2z)
  hence "(z2m\<^bsub>C\<^esub> x) ;;\<^bsub>C\<^esub> f maps\<^bsub>C\<^esub> X to (cod\<^bsub>C\<^esub> f)" using a c by (auto intro: Category.Ccompt)
  hence "(m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> x) ;;\<^bsub>C\<^esub> f)) |\<in>| (Hom\<^bsub>C\<^esub> X (cod\<^bsub>C\<^esub> f))" using a b d 2 
    by (auto simp add: LSCategory.m2zz2m)
  thus ?thesis using c by (simp add: Category.Simps)
qed

lemma HomFtorInMor':
  assumes "LSCategory C" and "X \<in> obj\<^bsub>C\<^esub>" and "f \<in> mor\<^bsub>C\<^esub>"
  shows "Hom\<^bsub>C\<^esub>[X,f] \<in> mor\<^bsub>SET'\<^esub>" 
proof(simp add: HomFtorMap_def)
  {
    fix x assume "x |\<in>| (Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> f)" 
    hence "m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> f) |\<in>| (Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> f)" using assms by (blast intro: HomFtorMapLemma1)
  }
  hence "\<forall> x . x |\<in>| (Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> f) \<longrightarrow> (m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> f)) |\<in>| (Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> f)" by (simp)
  hence "isZFfun (ZFfun (Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> f) (Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> f) (\<lambda> x . m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> f)))"
    by (simp add: SETfun)
  thus "ZFfun (Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> f) (Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> f) (\<lambda> x . m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> f)) \<in> mor\<^bsub>SET'\<^esub>"
    by (simp add: SET'_def)
qed

lemma HomFtorMor':
  assumes "LSCategory C" and "X \<in> obj\<^bsub>C\<^esub>" and "f \<in> mor\<^bsub>C\<^esub>"
  shows   "Hom\<^bsub>C\<^esub>[X,f] maps\<^bsub>SET'\<^esub> Hom\<^bsub>C \<^esub>X (dom\<^bsub>C\<^esub> f) to Hom\<^bsub>C \<^esub>X (cod\<^bsub>C\<^esub> f)"  
proof-
  have "Hom\<^bsub>C\<^esub>[X,f] \<in> mor\<^bsub>SET'\<^esub>" using assms by (simp add: HomFtorInMor')
  moreover have "dom\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,f]) = Hom\<^bsub>C \<^esub>X (dom\<^bsub>C\<^esub> f)"
    by(simp add: HomFtorMap_def SET'_def ZFfunDom)
  moreover have "cod\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,f]) = Hom\<^bsub>C \<^esub>X (cod\<^bsub>C\<^esub> f)"
    by(simp add: HomFtorMap_def SET'_def ZFfunCod)
  ultimately show ?thesis by (auto simp add: SET_def)
qed

lemma HomFtorMapsTo:
  "\<lbrakk>LSCategory C ; X \<in> obj\<^bsub>C \<^esub>; f \<in> mor\<^bsub>C \<^esub>\<rbrakk> \<Longrightarrow> Hom\<^bsub>C\<^esub>[X,f] maps\<^bsub>SET\<^esub> Hom\<^bsub>C \<^esub>X (dom\<^bsub>C\<^esub> f) to Hom\<^bsub>C \<^esub>X (cod\<^bsub>C\<^esub> f)"
by (simp add: HomFtorMor' SET_def MakeCatMapsTo)

lemma HomFtorMor:
  assumes "LSCategory C" and "X \<in> obj\<^bsub>C\<^esub>" and "f \<in> mor\<^bsub>C\<^esub>" 
  shows "Hom\<^bsub>C\<^esub>[X,f] \<in> Mor SET" and "dom\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[X,f]) = Hom\<^bsub>C \<^esub>X (dom\<^bsub>C\<^esub> f)" 
  and "cod\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[X,f]) = Hom\<^bsub>C \<^esub>X (cod\<^bsub>C\<^esub> f)"
proof-
  have "Hom\<^bsub>C\<^esub>[X,f] maps\<^bsub>SET\<^esub> Hom\<^bsub>C \<^esub>X (dom\<^bsub>C\<^esub> f) to Hom\<^bsub>C \<^esub>X (cod\<^bsub>C\<^esub> f)" using assms by (simp add: HomFtorMapsTo)
  thus "Hom\<^bsub>C\<^esub>[X,f] \<in> Mor SET" and "dom\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[X,f]) = Hom\<^bsub>C \<^esub>X (dom\<^bsub>C\<^esub> f)" and "cod\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[X,f]) = Hom\<^bsub>C \<^esub>X (cod\<^bsub>C\<^esub> f)"
    by auto
qed

lemma HomFtorCompDef':
  assumes "LSCategory C" and "X \<in> obj\<^bsub>C\<^esub>" and "f \<approx>>\<^bsub>C\<^esub> g" 
  shows   "(Hom\<^bsub>C\<^esub>[X,f]) \<approx>>\<^bsub>SET' \<^esub>(Hom\<^bsub>C\<^esub>[X,g])"
proof(rule CompDefinedI)
  have a: "f \<in> mor\<^bsub>C\<^esub>" and b: "g \<in> mor\<^bsub>C\<^esub>" using assms(3) by auto 
  thus "Hom\<^bsub>C\<^esub>[X,f] \<in> mor\<^bsub>SET'\<^esub>" and "Hom\<^bsub>C\<^esub>[X,g] \<in> mor\<^bsub>SET'\<^esub>" using assms by (simp add:HomFtorInMor')+
  have "(Hom\<^bsub>C\<^esub>[X,f]) maps\<^bsub>SET'\<^esub> Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> f to Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> f"
    and "(Hom\<^bsub>C\<^esub>[X,g]) maps\<^bsub>SET'\<^esub> Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> g to Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> g" using assms a b by (simp add: HomFtorMor')+
  hence "cod\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,f]) = Hom\<^bsub>C\<^esub> X (cod\<^bsub>C\<^esub> f)" 
    and "dom\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,g]) = Hom\<^bsub>C\<^esub> X (dom\<^bsub>C\<^esub> g)" by auto
  moreover have "(cod\<^bsub>C\<^esub> f) = (dom\<^bsub>C\<^esub> g)" using assms(3) by auto
  ultimately show "cod\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,f]) = dom\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,g])" by simp
qed

lemma HomFtorDist': 
  assumes a: "LSCategory C" and b: "X \<in> obj\<^bsub>C\<^esub>" and c: "f \<approx>>\<^bsub>C\<^esub> g"
  shows   "(Hom\<^bsub>C\<^esub>[X,f]) ;;\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,g]) = Hom\<^bsub>C\<^esub>[X,f ;;\<^bsub>C\<^esub> g]"
proof-
  let ?A = "(Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> f)"
  let ?B = "(Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> g)"
  let ?C = "(Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> g)"
  let ?f = "(\<lambda>h. m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>h) ;;\<^bsub>C\<^esub> f))"
  let ?g = "(\<lambda>f. m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>f) ;;\<^bsub>C\<^esub> g))"
  have 1: "cod\<^bsub>C\<^esub> f = dom\<^bsub>C\<^esub> g" using c by auto
  have 2: "dom\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g) = dom\<^bsub>C\<^esub> f" and 3: "cod\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g) = cod\<^bsub>C\<^esub> g" using assms 
    by (auto simp add: Category.MapsToMorDomCod)
  have "(Hom\<^bsub>C\<^esub>[X,f]) ;;\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,g]) = (ZFfun ?A (Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> f) ?f) |o| (ZFfun ?B ?C ?g)" 
    by (simp add: HomFtorMap_def SET'_def)
  also have "... = (ZFfun ?A ?B ?f) |o| (ZFfun ?B ?C ?g)" using 1 by simp
  also have "... = ZFfun ?A ?C (?g o ?f)" 
  proof(rule ZFfunComp, rule allI, rule impI)
    {
      fix h assume aa: "h |\<in>| ?A" show "?f h |\<in>| ?B"
      proof-
        have "f \<in> mor\<^bsub>C\<^esub>" using assms by auto
        hence "?f h |\<in>| (Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> f)" using assms aa by (simp add: HomFtorMapLemma1)
        thus ?thesis using 1 by simp
      qed
    }
  qed
  also have "... = ZFfun ?A ?C (\<lambda>h. m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>h) ;;\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g)))"
  proof(rule ZFfun_ext, rule allI, rule impI, simp add: comp_def)
    {
      fix h assume aa: "h |\<in>| ?A" 
      show "m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> (m2z\<^bsub>C\<^esub>((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f))) ;;\<^bsub>C\<^esub> g) = m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g))"
      proof-
        have bb: "(z2m\<^bsub>C\<^esub> h) \<approx>>\<^bsub>C\<^esub> f" 
        proof(rule CompDefinedI)
          show "f \<in> mor\<^bsub>C\<^esub>" using c by auto
          hence "dom\<^bsub>C\<^esub> f \<in> obj\<^bsub>C\<^esub>" using a by (simp add: Category.Cdom)
          hence "(z2m\<^bsub>C\<^esub> h) maps\<^bsub>C\<^esub> X to dom\<^bsub>C\<^esub> f" using assms aa by (simp add: LSCategory.z2mm2z)
          thus "(z2m\<^bsub>C\<^esub> h) \<in> mor\<^bsub>C\<^esub>" and "cod\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h) = dom\<^bsub>C\<^esub> f" by auto
        qed
        hence "(z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f \<in> mor\<^bsub>C\<^esub>" using a by (simp add: Category.MapsToMorDomCod)
        hence "z2m\<^bsub>C\<^esub> (m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f)) = (z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f" using a by (simp add: LSCategory.m2zz2mInv)
        hence "m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> (m2z\<^bsub>C\<^esub>((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f))) ;;\<^bsub>C\<^esub> g) = m2z\<^bsub>C\<^esub> (((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f) ;;\<^bsub>C\<^esub> g)" by simp
        also have "... = m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g))" using bb c a by (simp add: Category.Cassoc)
        finally show ?thesis .
      qed
    }
  qed
  also have "... = ZFfun (Hom\<^bsub>C\<^esub> X dom\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g)) (Hom\<^bsub>C\<^esub> X cod\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g)) (\<lambda>h. m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>h) ;;\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g)))"
    using 2 3 by simp
  also have "... = Hom\<^bsub>C\<^esub>[X,f ;;\<^bsub>C\<^esub> g]" by (simp add:  HomFtorMap_def)
  finally show ?thesis by (auto simp add: SET_def)
qed

lemma HomFtorDist:
  assumes "LSCategory C" and "X \<in> obj\<^bsub>C\<^esub>" and "f \<approx>>\<^bsub>C\<^esub> g"
  shows   "(Hom\<^bsub>C\<^esub>[X,f]) ;;\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[X,g]) = Hom\<^bsub>C\<^esub>[X,f ;;\<^bsub>C\<^esub> g]"
proof-
  have "(Hom\<^bsub>C\<^esub>[X,f]) ;;\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,g]) = Hom\<^bsub>C\<^esub>[X,f ;;\<^bsub>C\<^esub> g]" using assms by (simp add: HomFtorDist')
  moreover have "(Hom\<^bsub>C\<^esub>[X,f]) \<approx>>\<^bsub>SET'\<^esub> (Hom\<^bsub>C\<^esub>[X,g])" using assms by (simp add: HomFtorCompDef')
  ultimately show ?thesis by (simp add: MakeCatComp SET_def)
qed

lemma HomFtorId':
  assumes a: "LSCategory C" and b: "X \<in> obj\<^bsub>C\<^esub>" and c: "Y \<in> obj\<^bsub>C\<^esub>"
  shows   "Hom\<^bsub>C\<^esub>[X,id\<^bsub>C\<^esub> Y] = id\<^bsub>SET'\<^esub> (Hom\<^bsub>C \<^esub>X Y)"
proof-
  have "(id\<^bsub>C\<^esub> Y) maps\<^bsub>C\<^esub> Y to Y" using a c by (simp add: Category.Simps)
  hence 1: "(dom\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y)) = Y" and 2: "(cod\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y)) = Y" by auto
  have "Hom\<^bsub>C\<^esub>[X,id\<^bsub>C\<^esub> Y] = ZFfun (Hom\<^bsub>C \<^esub>X (dom\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y))) (Hom\<^bsub>C \<^esub>X (cod\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y))) (\<lambda> f . m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> f) ;;\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y)))"
    by (simp add: HomFtorMap_def)
  also have "... = ZFfun (Hom\<^bsub>C \<^esub>X Y) (Hom\<^bsub>C \<^esub>X Y) (\<lambda> f . m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> f) ;;\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y)))" using 1 2 by simp
  also have "... = ZFfun (Hom\<^bsub>C \<^esub>X Y) (Hom\<^bsub>C \<^esub>X Y) (\<lambda> f . f)" 
  proof(rule ZFfun_ext, rule allI, rule impI)
    {
      fix h assume aa: "h |\<in>| (Hom\<^bsub>C\<^esub> X Y)" show "m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y)) = h"
      proof-
        have "(z2m\<^bsub>C\<^esub> h) maps\<^bsub>C\<^esub> X to Y" and bb: "m2z\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h) = h" 
          using assms aa by (simp add: LSCategory.z2mm2z)+
        hence "(z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y) = (z2m\<^bsub>C\<^esub> h)" using a by (auto simp add: Category.Simps)
        hence "m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> (id\<^bsub>C\<^esub> Y)) = m2z\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h)" by simp
        also have "... = h" using bb .
        finally show ?thesis .
      qed
    }
  qed
  finally show ?thesis by (simp add: SET'_def)
qed

lemma HomFtorId: 
  assumes "LSCategory C" and "X \<in> obj\<^bsub>C\<^esub>" and "Y \<in> obj\<^bsub>C\<^esub>"
  shows   "Hom\<^bsub>C\<^esub>[X,id\<^bsub>C\<^esub> Y] = id\<^bsub>SET\<^esub> (Hom\<^bsub>C \<^esub>X Y)"
proof-
  have "Hom\<^bsub>C\<^esub>[X,id\<^bsub>C\<^esub> Y] = id\<^bsub>SET'\<^esub> (Hom\<^bsub>C \<^esub>X Y)" using assms by (simp add: HomFtorId')
  moreover have "(Hom\<^bsub>C \<^esub>X Y) \<in> obj\<^bsub>SET'\<^esub>" by (simp add: SET'_def)
  ultimately show ?thesis by (simp add: MakeCatId SET_def)
qed

lemma HomFtorObj':
  assumes a: "LSCategory C"
  and     b: "PreFunctor (HomP\<^bsub>C\<^esub>[X,\<midarrow>])"  and c: "X \<in> obj\<^bsub>C\<^esub>" and d: "Y \<in> obj\<^bsub>C\<^esub>"
  shows   "(HomP\<^bsub>C\<^esub>[X,\<midarrow>]) @@ Y = Hom\<^bsub>C \<^esub>X Y" 
proof-
  let ?F = "(HomFtor' C X)"
  have "?F ## (id\<^bsub>CatDom ?F\<^esub> Y) = Hom\<^bsub>C\<^esub>[X,id\<^bsub>C\<^esub> Y]" by (simp add: HomFtor'_def)
  also have "... = id\<^bsub>CatCod ?F\<^esub> (Hom\<^bsub>C \<^esub>X Y)" using assms by (simp add: HomFtorId HomFtor'_def)
  finally have "?F ## (id\<^bsub>CatDom ?F\<^esub> Y) = id\<^bsub>CatCod ?F\<^esub> (Hom\<^bsub>C \<^esub>X Y)" by simp
  moreover have "Hom\<^bsub>C \<^esub>X Y \<in> obj\<^bsub>CatCod ?F\<^esub>" using assms 
    by (simp add: HomFtorId HomFtor'_def SET_def SET'_def MakeCatObj)
  moreover have "Y \<in> obj\<^bsub>CatDom ?F\<^esub>" using d by (simp add: HomFtor'_def)
  ultimately show ?thesis using b by(simp add: PreFunctor.FmToFo[of ?F Y "Hom\<^bsub>C \<^esub>X Y"])
qed

lemma HomFtorFtor': 
  assumes a: "LSCategory C"
  and     b: "X \<in> obj\<^bsub>C\<^esub>"
  shows   "FunctorM (HomP\<^bsub>C\<^esub>[X,\<midarrow>])"
proof(intro_locales)
  show PF: "PreFunctor (HomP\<^bsub>C\<^esub>[X,\<midarrow>])"
  proof(auto simp add: HomFtor'_def PreFunctor_def SETCategory a HomFtorDist b)
    {
      fix Z assume aa: "Z \<in> obj\<^bsub>C\<^esub>" 
      show "\<exists> Y \<in> obj\<^bsub>SET \<^esub>. Hom\<^bsub>C\<^esub>[X,id\<^bsub>C\<^esub> Z] = id\<^bsub>SET\<^esub> Y"
      proof(rule_tac x="Hom\<^bsub>C \<^esub>X Z" in Set.rev_bexI)
        show "Hom\<^bsub>C\<^esub> X Z \<in> obj\<^bsub>SET\<^esub>" by (simp add: SET_def SET'_def MakeCatObj) 
        show "Hom\<^bsub>C\<^esub>[X,id\<^bsub>C\<^esub> Z] = id\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub> X Z)" using assms aa by(simp add:HomFtorId)
      qed
    }
  qed
  {
    fix f Z Y assume aa: "f maps\<^bsub>C \<^esub>Z to Y" 
    have "(HomP\<^bsub>C\<^esub>[X,\<midarrow>]) ## f maps\<^bsub>SET\<^esub> ((HomP\<^bsub>C\<^esub>[X,\<midarrow>]) @@ Z) to ((HomP\<^bsub>C\<^esub>[X,\<midarrow>]) @@ Y)" 
    proof-
      have bb: "Z \<in> obj\<^bsub>C\<^esub>" and cc: "Y \<in> obj\<^bsub>C\<^esub>" using aa a by (simp add: Category.MapsToObj)+
      have dd: "dom\<^bsub>C\<^esub> f = Z" and ee: "cod\<^bsub>C\<^esub> f = Y" and ff: "f \<in> mor\<^bsub>C\<^esub>" using aa by auto
      have "(HomP\<^bsub>C\<^esub>[X,\<midarrow>]) ## f = Hom\<^bsub>C\<^esub>[X,f]" by (simp add: HomFtor'_def)
      moreover have "(HomP\<^bsub>C\<^esub>[X,\<midarrow>]) @@ Z = Hom\<^bsub>C \<^esub>X Z" 
        and "(HomP\<^bsub>C\<^esub>[X,\<midarrow>]) @@ Y = Hom\<^bsub>C \<^esub>X Y" using assms bb cc PF by (simp add: HomFtorObj')+
      moreover have "Hom\<^bsub>C\<^esub>[X,f] maps\<^bsub>SET\<^esub> (Hom\<^bsub>C \<^esub>X (dom\<^bsub>C\<^esub> f)) to (Hom\<^bsub>C \<^esub>X (cod\<^bsub>C\<^esub> f))" 
        using assms ff by (simp add: HomFtorMapsTo)
      ultimately show ?thesis using dd ee by simp
    qed
  }
  thus "FunctorM_axioms (HomP\<^bsub>C\<^esub>[X,\<midarrow>])" using PF by (auto simp add: FunctorM_axioms_def HomFtor'_def)
qed

lemma HomFtorFtor: 
  assumes a: "LSCategory C"
  and     b: "X \<in> obj\<^bsub>C\<^esub>"
  shows   "Functor (Hom\<^bsub>C\<^esub>[X,\<midarrow>])"
proof-
  have "FunctorM (HomP\<^bsub>C\<^esub>[X,\<midarrow>])" using assms by (rule HomFtorFtor')
  thus ?thesis by (simp add: HomFtor_def MakeFtor)
qed 

lemma HomFtorObj:
  assumes "LSCategory C"
  and     "X \<in> obj\<^bsub>C\<^esub>" and "Y \<in> obj\<^bsub>C\<^esub>"
  shows   "(Hom\<^bsub>C\<^esub>[X,\<midarrow>]) @@ Y = Hom\<^bsub>C \<^esub>X Y"
proof-
  have "FunctorM (HomP\<^bsub>C\<^esub>[X,\<midarrow>])" using assms by (simp add: HomFtorFtor')
  hence 1: "PreFunctor (HomP\<^bsub>C\<^esub>[X,\<midarrow>])" by (simp add: FunctorM_def)
  moreover have "CatDom (HomP\<^bsub>C\<^esub>[X,\<midarrow>]) = C" by (simp add: HomFtor'_def)
  ultimately have "(Hom\<^bsub>C\<^esub>[X,\<midarrow>]) @@ Y = (HomP\<^bsub>C\<^esub>[X,\<midarrow>]) @@ Y" using assms by (simp add: MakeFtorObj HomFtor_def)
  thus ?thesis using assms 1 by (simp add: HomFtorObj')
qed

definition
  HomFtorMapContra :: "('o,'m,'a) LSCategory_scheme \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> ZF" ("HomC\<index>[_,_]" [65,65] 65) where
  "HomFtorMapContra C g X \<equiv> ZFfun (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> g) X) (Hom\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> g) X) (\<lambda> f . m2z\<^bsub>C\<^esub> (g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> f)))"

definition 
  HomFtorContra' :: "('o,'m,'a) LSCategory_scheme \<Rightarrow> 'o \<Rightarrow> 
      ('o,ZF,'m,ZF,\<lparr>mor2ZF :: 'm \<Rightarrow> ZF, \<dots> :: 'a\<rparr>,unit) Functor" ("HomP\<index>[\<midarrow>,_]" [65] 65) where
  "HomFtorContra' C X \<equiv> \<lparr>
        CatDom = (Op C), 
        CatCod = SET ,
        MapM   = \<lambda> g . HomC\<^bsub>C\<^esub>[g,X]
  \<rparr>"

definition HomFtorContra ("Hom\<index>[\<midarrow>,_]" [65] 65) where "HomFtorContra C X \<equiv> MakeFtor(HomFtorContra' C X)"

lemma HomContraAt: "x |\<in>| (Hom\<^bsub>C \<^esub>(cod\<^bsub>C\<^esub> f) X) \<Longrightarrow> (HomC\<^bsub>C\<^esub>[f,X]) |@| x = m2z\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> x))"
  by (simp add: HomFtorMapContra_def ZFfunApp)

lemma mor2ZF_Op: "mor2ZF (Op C) = mor2ZF C"  
apply (cases C)
apply (simp add: OppositeCategory_def)
done

lemma mor_Op: "mor\<^bsub>Op C\<^esub> = mor\<^bsub>C\<^esub>" by (simp add: OppositeCategory_def)
lemma obj_Op: "obj\<^bsub>Op C\<^esub> = obj\<^bsub>C\<^esub>" by (simp add: OppositeCategory_def)

lemma ZF2mor_Op: "ZF2mor (Op C) f = ZF2mor C f"
by (simp add: ZF2mor_def mor2ZF_Op mor_Op)

lemma mapsTo_Op: "f maps\<^bsub>Op C\<^esub> Y to X = f maps\<^bsub>C\<^esub> X to Y"
by (auto simp add: OppositeCategory_def mor_Op MapsTo_def)

lemma HOMCollection_Op: "HOMCollection (Op C) X Y = HOMCollection C Y X"
by (simp add: HOMCollection_def mapsTo_Op mor2ZF_Op)

lemma Hom_Op: "Hom\<^bsub>Op C\<^esub> X Y = Hom\<^bsub>C\<^esub> Y X"
by (simp add: HomSet_def HOMCollection_Op)

lemma HomFtorContra': "HomP\<^bsub>C\<^esub>[\<midarrow>,X] = HomP\<^bsub>Op C\<^esub>[X,\<midarrow>]"
apply (simp add:  HomFtorContra'_def 
                      HomFtor'_def HomFtorMapContra_def HomFtorMap_def mor2ZF_Op ZF2mor_Op Hom_Op)
by (simp add: OppositeCategory_def)

lemma HomFtorContra: "Hom\<^bsub>C\<^esub>[\<midarrow>,X] = Hom\<^bsub>Op C\<^esub>[X,\<midarrow>]"
by (auto simp add: HomFtorContra' HomFtorContra_def HomFtor_def)

lemma HomFtorContraDom: "CatDom (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) = Op C"
by(simp add: HomFtorContra_def HomFtorContra'_def MakeFtor_def)

lemma HomFtorContraCod: "CatCod (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) = SET"
by(simp add: HomFtorContra_def HomFtorContra'_def MakeFtor_def)

lemma LSCategory_Op: assumes "LSCategory C" shows "LSCategory (Op C)"
proof(auto simp only: LSCategory_def)
  show "Category (Op C)" using assms by (simp add: OpCatCat)
  show "LSCategory_axioms (Op C)" using assms
    by (simp add: LSCategory_axioms_def mor_Op obj_Op mor2ZF_Op HOMCollection_Op 
                     LSCategory.mor2ZFInj LSCategory.HOMSetIsSet LSCategory.m2zExt)
qed

lemma HomFtorContraFtor:
  assumes "LSCategory C"
  and     "X \<in> obj\<^bsub>C\<^esub>"
  shows   "Ftor (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) : (Op C) \<longrightarrow> SET"
proof(auto simp only: functor_abbrev_def)
  show "Functor (Hom\<^bsub>C\<^esub>[\<midarrow>,X])"
  proof-
    have "Hom\<^bsub>C\<^esub>[\<midarrow>,X] = Hom\<^bsub>Op C\<^esub>[X,\<midarrow>]" by (simp add: HomFtorContra)
    moreover have "LSCategory (Op C)" using assms by (simp add: LSCategory_Op)
    moreover have "X \<in> obj\<^bsub>Op C\<^esub>" using assms by (simp add: OppositeCategory_def)
    ultimately show ?thesis using assms by (simp add: HomFtorFtor)
  qed
  show "CatDom (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) = Op C" by(simp add: HomFtorContra_def HomFtorContra'_def MakeFtor_def)
  show "CatCod (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) = SET" by(simp add: HomFtorContra_def HomFtorContra'_def MakeFtor_def)
qed

lemma HomFtorOpObj:
  assumes "LSCategory C"
  and     "X \<in> obj\<^bsub>C\<^esub>" and "Y \<in> obj\<^bsub>C\<^esub>"
  shows   "(Hom\<^bsub>C\<^esub>[\<midarrow>,X]) @@ Y = Hom\<^bsub>C \<^esub>Y X"
proof-
  have 1: "X \<in> Obj (Op C)" and 2: "Y \<in> Obj (Op C)" using assms by (simp add: OppositeCategory_def)+
  have "(Hom\<^bsub>C\<^esub>[\<midarrow>,X]) @@ Y = (Hom\<^bsub>Op C\<^esub>[X,\<midarrow>]) @@ Y" by (simp add: HomFtorContra)
  also have "... = (Hom\<^bsub>Op C \<^esub>X Y)" using assms(1) 1 2 by (simp add: LSCategory_Op HomFtorObj)
  also have "... = (Hom\<^bsub>C \<^esub>Y X)" by (simp add: Hom_Op)
  finally show ?thesis .
qed
  

lemma HomCHomOp: "HomC\<^bsub>C\<^esub>[g,X] = Hom\<^bsub>Op C\<^esub>[X,g]"
apply (simp add:  HomFtorContra'_def 
                      HomFtor'_def HomFtorMapContra_def HomFtorMap_def mor2ZF_Op ZF2mor_Op Hom_Op)
by (simp add: OppositeCategory_def)

lemma HomFtorContraMapsTo:
  assumes "LSCategory C" and "X \<in> obj\<^bsub>C\<^esub>" and "f \<in> mor\<^bsub>C\<^esub>" 
  shows "HomC\<^bsub>C\<^esub>[f,X] maps\<^bsub>SET\<^esub> Hom\<^bsub>C \<^esub>(cod\<^bsub>C\<^esub> f) X  to Hom\<^bsub>C \<^esub>(dom\<^bsub>C\<^esub> f) X"
proof-
  have "LSCategory (Op C)" using assms by(simp add: LSCategory_Op)
  moreover have "X \<in> Obj (Op C)" using assms by (simp add: OppositeCategory_def)
  moreover have "f \<in> Mor (Op C)" using assms by (simp add: OppositeCategory_def)
  ultimately have "Hom\<^bsub>Op C\<^esub>[X,f] maps\<^bsub>SET\<^esub> Hom\<^bsub>Op C \<^esub>X (dom\<^bsub>Op C\<^esub> f) to Hom\<^bsub>Op C \<^esub>X (cod\<^bsub>Op C\<^esub> f)" using assms
    by (simp add: HomFtorMapsTo)
  moreover have "HomC\<^bsub>C\<^esub>[f,X] = Hom\<^bsub>Op C\<^esub>[X,f]" by (simp add: HomCHomOp)
  moreover have "Hom\<^bsub>Op C \<^esub>X (dom\<^bsub>Op C\<^esub> f) = Hom\<^bsub>C \<^esub>(cod\<^bsub>C\<^esub> f) X" 
  proof-
    have "Hom\<^bsub>Op C \<^esub>X (dom\<^bsub>Op C\<^esub> f) = Hom\<^bsub>C\<^esub> (dom\<^bsub>Op C\<^esub> f) X" by (simp add: Hom_Op)
    thus ?thesis by (simp add:  OppositeCategory_def)
  qed
  moreover have "Hom\<^bsub>Op C \<^esub>X (cod\<^bsub>Op C\<^esub> f) = Hom\<^bsub>C \<^esub>(dom\<^bsub>C\<^esub> f) X"
  proof-
    have "Hom\<^bsub>Op C \<^esub>X (cod\<^bsub>Op C\<^esub> f) = Hom\<^bsub>C\<^esub> (cod\<^bsub>Op C\<^esub> f) X" by (simp add: Hom_Op)
    thus ?thesis by (simp add:  OppositeCategory_def)
  qed
  ultimately show ?thesis by simp
qed

lemma HomFtorContraMor:
  assumes "LSCategory C" and "X \<in> obj\<^bsub>C\<^esub>" and "f \<in> mor\<^bsub>C\<^esub>" 
  shows "HomC\<^bsub>C\<^esub>[f,X] \<in> Mor SET" and "dom\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[f,X]) = Hom\<^bsub>C \<^esub>(cod\<^bsub>C\<^esub> f) X" 
  and "cod\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[f,X]) = Hom\<^bsub>C \<^esub>(dom\<^bsub>C\<^esub> f) X"
proof-
  have "HomC\<^bsub>C\<^esub>[f,X] maps\<^bsub>SET\<^esub> Hom\<^bsub>C \<^esub>(cod\<^bsub>C\<^esub> f) X  to Hom\<^bsub>C \<^esub>(dom\<^bsub>C\<^esub> f) X" using assms by (simp add: HomFtorContraMapsTo)
  thus "HomC\<^bsub>C\<^esub>[f,X] \<in> Mor SET" and "dom\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[f,X]) = Hom\<^bsub>C \<^esub>(cod\<^bsub>C\<^esub> f) X" 
  and "cod\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[f,X]) = Hom\<^bsub>C \<^esub>(dom\<^bsub>C\<^esub> f) X"
    by auto
qed

lemma HomContraMor:
  assumes "LSCategory C" and "f \<in> Mor C" 
  shows "(Hom\<^bsub>C\<^esub>[\<midarrow>,X]) ## f = HomC\<^bsub>C\<^esub>[f,X]"
by(simp add: HomFtorContra_def HomFtorContra'_def MakeFtor_def assms OppositeCategory_def) 



(*This is used in the proof of the naturality of the Yoneda trans*)
lemma HomCHom:
  assumes "LSCategory C" and "f \<in> Mor C" and "g \<in> Mor C"
  shows "(HomC\<^bsub>C\<^esub>[g,dom\<^bsub>C\<^esub> f]) ;;\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[dom\<^bsub>C\<^esub> g,f]) = (Hom\<^bsub>C\<^esub>[cod\<^bsub>C\<^esub> g,f]) ;;\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[g,cod\<^bsub>C\<^esub> f])"
proof-
  have ObjDf: "dom\<^bsub>C\<^esub> f \<in> obj\<^bsub>C\<^esub>" and ObjDg: "dom\<^bsub>C\<^esub> g \<in> obj\<^bsub>C\<^esub>" using assms by (simp add: Category.Cdom)+
  have ObjCg: "cod\<^bsub>C\<^esub> g \<in> obj\<^bsub>C\<^esub>" and ObjCf: "cod\<^bsub>C\<^esub> f \<in> obj\<^bsub>C\<^esub>" using assms by (simp add: Category.Ccod)+
  have "(HomC\<^bsub>C\<^esub>[g,dom\<^bsub>C\<^esub> f]) ;;\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[dom\<^bsub>C\<^esub> g,f]) = (HomC\<^bsub>C\<^esub>[g,dom\<^bsub>C\<^esub> f]) |o| (Hom\<^bsub>C\<^esub>[dom\<^bsub>C\<^esub> g,f])" 
  proof-
    have "(HomC\<^bsub>C\<^esub>[g,dom\<^bsub>C\<^esub> f]) \<approx>>\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[dom\<^bsub>C\<^esub> g,f])" 
    proof(rule CompDefinedI)
      show "Hom\<^bsub>C\<^esub>[dom\<^bsub>C\<^esub> g,f] \<in> Mor SET" using assms ObjDg by (simp add: HomFtorMor)
      show "HomC\<^bsub>C\<^esub>[g,dom\<^bsub>C\<^esub> f] \<in> Mor SET" using assms ObjDf by (simp add: HomFtorContraMor)
      show "cod\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[g,dom\<^bsub>C\<^esub> f]) = dom\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[dom\<^bsub>C\<^esub> g,f])" using assms ObjDg ObjDf
        by (simp add: HomFtorMor HomFtorContraMor)
    qed
    thus ?thesis by(simp add: SET_def SET'_def MakeCatComp2)
  qed
  also have "... = ZFfun (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> g) (dom\<^bsub>C\<^esub> f)) (Hom\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> g) (cod\<^bsub>C\<^esub> f)) 
              ((\<lambda> h . m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f)) o (\<lambda> h . m2z\<^bsub>C\<^esub> (g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h))))" 
  proof(simp add: HomFtorMapContra_def HomFtorMap_def, rule ZFfunComp, rule allI, rule impI)
    {
      fix x assume aa: "x |\<in>| (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> g) (dom\<^bsub>C\<^esub> f))"
      show "(m2z\<^bsub>C \<^esub>(g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>x))) |\<in>| (Hom\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> g) (dom\<^bsub>C\<^esub> f))"
      proof(rule LSCategory.m2zz2m, simp_all add: assms(1) ObjDg ObjDf)
        have "g maps\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> g) to (cod\<^bsub>C\<^esub> g)" using assms by auto
        moreover have "(z2m\<^bsub>C \<^esub>x) maps\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> g) to (dom\<^bsub>C\<^esub> f)" using aa ObjCg ObjDf assms(1) 
          by (simp add: LSCategory.z2mm2z)
        ultimately show "g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>x) maps\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> g) to (dom\<^bsub>C\<^esub> f)" using assms(1)
          by (simp add: Category.Ccompt)
      qed
    }
  qed
  also have "... = ZFfun (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> g) (dom\<^bsub>C\<^esub> f)) (Hom\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> g) (cod\<^bsub>C\<^esub> f)) 
              ((\<lambda> h . m2z\<^bsub>C\<^esub> (g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h))) o (\<lambda> h . m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f)))" 
  proof(rule ZFfun_ext, rule allI, rule impI)
    {
      fix h assume aa: "h |\<in>| (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> g) (dom\<^bsub>C\<^esub> f))"
      show "((\<lambda> h . m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f)) o (\<lambda> h . m2z\<^bsub>C\<^esub> (g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h)))) h = 
        ((\<lambda> h . m2z\<^bsub>C\<^esub> (g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h))) o (\<lambda> h . m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f))) h"
      proof-
        have MapsTo1: "(z2m\<^bsub>C\<^esub> h) maps\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> g) to (dom\<^bsub>C\<^esub> f)" using assms(1) ObjCg ObjDf aa by (simp add: LSCategory.z2mm2z)
        have CompDef1: "(z2m\<^bsub>C\<^esub> h) \<approx>>\<^bsub>C\<^esub> f"
        proof(rule CompDefinedI)
          show "f \<in> mor\<^bsub>C\<^esub>" using assms by simp
          show "(z2m\<^bsub>C\<^esub> h) \<in> mor\<^bsub>C\<^esub>" and "cod\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h) = dom\<^bsub>C\<^esub> f" using MapsTo1 by auto
        qed
        have CompDef2: "g \<approx>>\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h)"
        proof(rule CompDefinedI)
          show "g \<in> mor\<^bsub>C\<^esub>" using assms by simp
          thus "(z2m\<^bsub>C\<^esub> h) \<in> mor\<^bsub>C\<^esub>" and "cod\<^bsub>C\<^esub> g = dom\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h)" using MapsTo1 by auto
        qed
        have c1: "(z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f \<in> Mor C" using assms CompDef1 by (simp add: Category.MapsToMorDomCod)
        have c2: "g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h) \<in> Mor C" using assms CompDef2 by (simp add: Category.MapsToMorDomCod)
        have "g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> (m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f))) = g ;;\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f)" using assms(1) c1
          by (simp add: LSCategory.m2zz2mInv)
        also have "... = (g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h)) ;;\<^bsub>C\<^esub> f" using CompDef1 CompDef2 assms by (simp add: Category.Cassoc)
        also have "... = (z2m\<^bsub>C\<^esub> (m2z\<^bsub>C\<^esub> (g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h)))) ;;\<^bsub>C\<^esub> f" using assms(1) c2
          by (simp add: LSCategory.m2zz2mInv)
        finally have "g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> (m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C\<^esub> h) ;;\<^bsub>C\<^esub> f))) = (z2m\<^bsub>C\<^esub> (m2z\<^bsub>C\<^esub> (g ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> h)))) ;;\<^bsub>C\<^esub> f" .
        thus ?thesis by simp
      qed
    }
  qed
  also have "... = (Hom\<^bsub>C\<^esub>[cod\<^bsub>C\<^esub> g,f]) |o| (HomC\<^bsub>C\<^esub>[g,cod\<^bsub>C\<^esub> f])"
  proof(simp add: HomFtorMapContra_def HomFtorMap_def, rule ZFfunComp[THEN sym], rule allI, rule impI)
    {
      fix x assume aa: "x |\<in>| (Hom\<^bsub>C\<^esub> cod\<^bsub>C\<^esub> g dom\<^bsub>C\<^esub> f)"
      show "m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> f) |\<in>| (Hom\<^bsub>C\<^esub> cod\<^bsub>C\<^esub> g cod\<^bsub>C\<^esub> f)" 
      proof(rule LSCategory.m2zz2m, simp_all add: assms(1) ObjCg ObjCf)
        have "f maps\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> f) to (cod\<^bsub>C\<^esub> f)" using assms by auto
        moreover have "(z2m\<^bsub>C \<^esub>x) maps\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> g) to (dom\<^bsub>C\<^esub> f)" using aa ObjCg ObjDf assms(1) 
          by (simp add: LSCategory.z2mm2z)
        ultimately show "(z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> f maps\<^bsub>C\<^esub> cod\<^bsub>C\<^esub> g to cod\<^bsub>C\<^esub> f" using assms(1)
          by (simp add: Category.Ccompt)
      qed
    }
  qed
  also have "... = (Hom\<^bsub>C\<^esub>[cod\<^bsub>C\<^esub> g,f]) ;;\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[g,cod\<^bsub>C\<^esub> f])"
  proof-
    have "(Hom\<^bsub>C\<^esub>[cod\<^bsub>C\<^esub> g,f]) \<approx>>\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[g,cod\<^bsub>C\<^esub> f])"
    proof(rule CompDefinedI)
      show "Hom\<^bsub>C\<^esub>[cod\<^bsub>C\<^esub> g,f] \<in> Mor SET" using assms ObjCg by (simp add: HomFtorMor)
      show "HomC\<^bsub>C\<^esub>[g,cod\<^bsub>C\<^esub> f] \<in> Mor SET" using assms ObjCf by (simp add: HomFtorContraMor)
      show "cod\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[cod\<^bsub>C\<^esub> g,f]) = dom\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[g,cod\<^bsub>C\<^esub> f])" using assms ObjCg ObjCf
        by (simp add: HomFtorMor HomFtorContraMor)
    qed
    thus ?thesis by(simp add: SET_def SET'_def MakeCatComp2)
  qed
  finally show ?thesis .
qed

end
