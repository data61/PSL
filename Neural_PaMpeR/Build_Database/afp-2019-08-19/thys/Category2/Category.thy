(*
Author: Alexander Katovsky
*)

section "Category"

theory Category
imports "HOL-Library.FuncSet"
begin

record ('o,'m) Category = 
  Obj :: "'o set" ("obj\<index>" 70) 
  Mor :: "'m set" ("mor\<index>" 70)
  Dom :: "'m \<Rightarrow> 'o" ("dom\<index> _" [80] 70)
  Cod :: "'m \<Rightarrow> 'o" ("cod\<index> _" [80] 70)
  Id  :: "'o \<Rightarrow> 'm" ("id\<index> _" [80] 75)
  Comp :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" (infixl ";;\<index>" 70)

definition
  MapsTo :: "('o,'m,'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> bool" ("_ maps\<index> _ to _" [60, 60, 60] 65) where
  "MapsTo CC f X Y \<equiv> f \<in> Mor CC \<and> Dom CC f = X \<and> Cod CC f = Y"

definition
  CompDefined :: "('o,'m,'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" (infixl "\<approx>>\<index>" 65) where
  "CompDefined CC f g \<equiv> f \<in> Mor CC \<and> g \<in> Mor CC \<and> Cod CC f = Dom CC g"

locale ExtCategory = 
  fixes C :: "('o,'m,'a) Category_scheme" (structure)
  assumes CdomExt: "(Dom C) \<in> extensional (Mor C)"
  and     CcodExt: "(Cod C) \<in> extensional (Mor C)"
  and     CidExt:  "(Id C) \<in> extensional (Obj C)"
  and     CcompExt:  "(case_prod (Comp C)) \<in> extensional ({(f,g) | f g . f \<approx>> g})"

locale Category = ExtCategory +
  assumes Cdom : "f \<in> mor \<Longrightarrow> dom f \<in> obj"
  and     Ccod : "f \<in> mor \<Longrightarrow> cod f \<in> obj"
  and     Cidm [dest]: "X \<in> obj \<Longrightarrow> (id X) maps X to X"
  and     Cidl : "f \<in> mor \<Longrightarrow> id (dom f) ;; f = f"
  and     Cidr : "f \<in> mor \<Longrightarrow> f ;; id (cod f) = f"
  and     Cassoc : "\<lbrakk>f \<approx>> g ; g \<approx>> h\<rbrakk> \<Longrightarrow> (f ;; g) ;; h = f ;; (g ;; h)"
  and     Ccompt : "\<lbrakk>f maps X to Y ; g maps Y to Z\<rbrakk> \<Longrightarrow> (f ;; g) maps X to Z"

definition 
  MakeCat :: "('o,'m,'a) Category_scheme \<Rightarrow> ('o,'m,'a) Category_scheme" where
  "MakeCat C \<equiv> \<lparr>
      Obj = Obj C , 
      Mor = Mor C , 
      Dom = restrict (Dom C) (Mor C) , 
      Cod = restrict (Cod C) (Mor C) , 
      Id  = restrict (Id C) (Obj C) , 
      Comp = \<lambda> f g . (restrict (case_prod (Comp C)) ({(f,g) | f g . f \<approx>>\<^bsub>C\<^esub> g})) (f,g), 
      \<dots> = Category.more C
  \<rparr>"

lemma MakeCatMapsTo: "f maps\<^bsub>C\<^esub> X to Y \<Longrightarrow> f maps\<^bsub>MakeCat C\<^esub> X to Y"
by (auto simp add: MapsTo_def MakeCat_def)

lemma MakeCatComp: "f \<approx>>\<^bsub>C\<^esub> g \<Longrightarrow> f ;;\<^bsub>MakeCat C\<^esub> g = f ;;\<^bsub>C\<^esub> g"
by (auto simp add: MapsTo_def MakeCat_def)

lemma MakeCatId: "X \<in> obj\<^bsub>C\<^esub> \<Longrightarrow> id\<^bsub>C\<^esub> X = id\<^bsub>MakeCat C\<^esub> X"
by (auto simp add: MapsTo_def MakeCat_def)

lemma MakeCatObj: "obj\<^bsub>MakeCat C\<^esub> = obj\<^bsub>C\<^esub>"
by (simp add: MakeCat_def)

lemma MakeCatMor: "mor\<^bsub>MakeCat C\<^esub> = mor\<^bsub>C\<^esub>"
by (simp add: MakeCat_def)

lemma MakeCatDom: "f \<in> mor\<^bsub>C\<^esub> \<Longrightarrow> dom\<^bsub>C\<^esub> f = dom\<^bsub>MakeCat C\<^esub> f"
by (simp add: MakeCat_def)

lemma MakeCatCod: "f \<in> mor\<^bsub>C\<^esub> \<Longrightarrow> cod\<^bsub>C\<^esub> f = cod\<^bsub>MakeCat C\<^esub> f"
by (simp add: MakeCat_def)


lemma MakeCatCompDef: "f \<approx>>\<^bsub>MakeCat C\<^esub> g = f \<approx>>\<^bsub>C\<^esub> g"
by (auto simp add: CompDefined_def MakeCat_def)

lemma MakeCatComp2: "f \<approx>>\<^bsub>MakeCat C\<^esub> g \<Longrightarrow> f ;;\<^bsub>MakeCat C\<^esub> g = f ;;\<^bsub>C\<^esub> g"
by (simp add: MakeCatCompDef MakeCatComp)


lemma ExtCategoryMakeCat: "ExtCategory (MakeCat C)"
by (unfold_locales, simp_all add: MakeCat_def extensional_def CompDefined_def)

lemma MakeCat: "Category_axioms C \<Longrightarrow> Category (MakeCat C)"
apply(intro_locales, simp add: ExtCategoryMakeCat)
apply (simp add: Category_axioms_def)
apply (auto simp add: MakeCat_def CompDefined_def MapsTo_def)
done

lemma MapsToE[elim]: "\<lbrakk>f maps\<^bsub>C\<^esub> X to Y ; \<lbrakk>f \<in> mor\<^bsub>C\<^esub> ; dom\<^bsub>C\<^esub> f = X ; cod\<^bsub>C\<^esub> f = Y\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp add: MapsTo_def)

lemma MapsToI[intro]: "\<lbrakk>f \<in> mor\<^bsub>C\<^esub> ; dom\<^bsub>C\<^esub> f = X ; cod\<^bsub>C\<^esub> f = Y\<rbrakk> \<Longrightarrow> f maps\<^bsub>C\<^esub> X to Y"
  by (auto simp add: MapsTo_def)

lemma CompDefinedE[elim]: "\<lbrakk>f \<approx>>\<^bsub>C\<^esub> g ; \<lbrakk>f \<in> mor\<^bsub>C\<^esub> ; g \<in> mor\<^bsub>C\<^esub> ; cod\<^bsub>C\<^esub> f = dom\<^bsub>C\<^esub> g\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto simp add: CompDefined_def)

lemma CompDefinedI[intro]: "\<lbrakk>f \<in> mor\<^bsub>C\<^esub> ; g \<in> mor\<^bsub>C\<^esub> ; cod\<^bsub>C\<^esub> f = dom\<^bsub>C\<^esub> g\<rbrakk> \<Longrightarrow> f \<approx>>\<^bsub>C\<^esub> g"
  by (auto simp add: CompDefined_def)

lemma (in Category) MapsToCompI: assumes "f \<approx>> g" shows "(f ;; g) maps (dom f) to (cod g)"
proof-
  have "f maps (dom f) to (dom g)" 
  and  "g maps (dom g) to (cod g)" using assms by auto
  thus ?thesis by (simp add: Ccompt[of f "dom f" "dom g" g "cod g"])
qed

lemma MapsToCompDef:
  assumes "f maps\<^bsub>C\<^esub> X to Y" and "g maps\<^bsub>C\<^esub> Y to Z"
  shows "f \<approx>>\<^bsub>C\<^esub> g"
proof(rule CompDefinedI)
  show "f \<in> mor\<^bsub>C\<^esub>" and "g \<in> mor\<^bsub>C\<^esub>" using assms by auto
  have "cod\<^bsub>C\<^esub> f = Y" and "dom\<^bsub>C\<^esub> g = Y" using assms by auto
  thus "cod\<^bsub>C\<^esub> f = dom\<^bsub>C\<^esub> g" by simp
qed

lemma (in Category) MapsToMorDomCod: 
  assumes "f \<approx>> g" 
  shows "f ;; g \<in> mor" and "dom (f ;; g) = dom f" and "cod (f ;; g) = cod g"
proof-
  have "(f ;; g) maps (dom f) to (cod g)" using assms by (simp add: MapsToCompI)
  thus "f ;; g \<in> mor" and "dom (f ;; g) = dom f" and "cod (f ;; g) = cod g" by auto
qed

lemma (in Category) MapsToObj: 
  assumes "f maps X to Y"
  shows "X \<in> obj" and "Y \<in> obj"
proof-
  have "dom f = X" and "cod f = Y" and "f \<in> mor" using assms by auto
  thus "X \<in> obj" and "Y \<in> obj" by (auto simp add: Cdom Ccod)
qed

lemma (in Category) IdInj: 
  assumes "X \<in> obj" and "Y \<in> obj" and "id X = id Y"
  shows   "X = Y"
proof-
  have "dom (id X) = dom (id Y)" using assms by simp
  moreover have "dom (id X) = X" and "dom (id Y) = Y" using assms by (auto simp add: MapsTo_def)
  ultimately show ?thesis by simp
qed

lemma (in Category) CompDefComp:
  assumes "f \<approx>> g" and "g \<approx>> h"
  shows "f \<approx>> (g ;; h)" and "(f ;; g) \<approx>> h"
proof(auto simp add: CompDefined_def)
  show "f \<in> mor" and "h \<in> mor" using assms by auto
  have  1: "g ;; h maps (dom g) to (cod h)" 
    and 2: "f ;; g maps (dom f) to (cod g)" using assms by (simp add: MapsToCompI)+
  thus "g ;; h \<in> mor" and "f ;; g \<in> mor" by auto
  have "cod f = dom g" using assms by auto
  also have "... = dom (g ;; h)" using 1 by auto
  finally show "cod f = dom (g ;; h)" .
  have "dom h = cod g" using assms by auto
  also have "... = cod (f ;; g)" using 2 by auto
  finally show "cod (f ;; g) = dom h" by simp
qed

lemma (in Category) CatIdInMor: "X \<in> obj \<Longrightarrow> id X \<in> mor"
by (auto simp add: Cidm)

lemma (in Category) MapsToId: assumes "X \<in> obj" shows "id X \<approx>> id X"
proof(rule CompDefinedI)
  have "id X maps X to X" using assms by (simp add: Cidm)
  thus "id X \<in> mor" and "id X \<in> mor" and "cod (id X) = dom (id X)" by auto
qed

lemmas (in Category) Simps = Cdom Ccod Cidm Cidl Cidr MapsToCompI IdInj MapsToId

lemma (in Category) LeftRightInvUniq: 
  assumes 0: "h \<approx>> f" and  z: "f \<approx>> g"
  assumes 1: "f ;; g = id (dom f)" 
  and     2: "h ;; f = id (cod f)"
  shows   "h = g"
proof-
  have mor: "h \<in> mor \<and> g \<in> mor" 
  and  dc : "dom f = cod h \<and> cod f = dom g" using 0 z by auto
  then have "h = h ;; id (dom f)" by (auto simp add: Simps)
  also have "... = h ;; (f ;; g)" using 1 by simp+
  also have "... = (h ;; f) ;; g" using 0 z by (simp add: Cassoc)
  also have "... = (id (cod f)) ;; g" using 2 by simp+
  also have "... = g" using mor dc by (auto simp add: Simps)
  finally show ?thesis .
qed

lemma (in Category) CatIdDomCod:
  assumes "X \<in> obj"
  shows "dom (id X) = X" and "cod (id X) = X"
proof-
  have "id X maps X to X" using assms
    by (simp add: Simps)
  thus "dom (id X) = X" and "cod (id X) = X" by auto
qed

lemma (in Category) CatIdCompId:
  assumes "X \<in> obj"
  shows   "id X ;; id X = id X"
proof-
  have 0: "id X \<in> mor" using assms by (auto simp add: Simps)
  moreover have "cod (id X) = X" using assms by auto
  moreover have "id X ;; id (cod (id X)) = id X" using 0 by (simp add: Simps)
  ultimately show ?thesis by simp
qed

(*lemmas (in Category) simps2 = simps CatIdCompId Cassoc CatIdDomCod*)

lemma (in Category) CatIdUniqR: 
  assumes iota: "\<iota> maps X to X"
  and     rid:  "\<forall> f . f \<approx>> \<iota> \<longrightarrow> f ;; \<iota> = f"
  shows "id X = \<iota>"
proof(rule LeftRightInvUniq [of "id X" "id X" \<iota> ])
  have 0: "X \<in> obj" using iota by (auto simp add: Simps)
  hence "id X maps X to X" by (simp add: Cidm)
  thus 1: "id X \<approx>> \<iota>" using iota by (auto simp add: Simps)
  show    "id X \<approx>> id X" using 0 by (auto simp add: Simps)
  show    "(id X) ;; \<iota> = (id (dom (id X)))" using 0 1 rid by (auto simp add: Simps CompDefined_def MapsTo_def)
  show    "(id X) ;; (id X) = (id (cod (id X)))" using 0 by (auto simp add: CatIdCompId CompDefined_def MapsTo_def)
qed
  
definition
  inverse_rel :: "('o,'m,'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> bool" ("cinv\<index> _ _" 60) where
  "inverse_rel C f g \<equiv> (f \<approx>>\<^bsub>C\<^esub> g) \<and> (f ;;\<^bsub>C\<^esub> g) = (id\<^bsub>C\<^esub> (dom\<^bsub>C\<^esub> f)) \<and> (g ;;\<^bsub>C\<^esub> f) = (id\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> f))"

definition 
  isomorphism :: "('o,'m,'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> bool" ("ciso\<index> _" [70]) where
  "isomorphism C f \<equiv> \<exists> g . inverse_rel C f g"

lemma (in Category) Inverse_relI: "\<lbrakk>f \<approx>> g ; f ;; g = id (dom f) ; g ;; f = id (cod f)\<rbrakk> \<Longrightarrow> (cinv f g)"
by (auto simp add: inverse_rel_def)

lemma (in Category) Inverse_relE[elim]: "\<lbrakk>cinv f g ; \<lbrakk>f \<approx>> g ; f ;; g = id (dom f) ; g ;; f = id (cod f)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (auto simp add: inverse_rel_def)

lemma (in Category) Inverse_relSym: 
  assumes "cinv f g"
  shows   "cinv g f"
proof(rule Inverse_relI)
  have 1: "f \<approx>> g" using assms by auto
  show 2: "g \<approx>> f"
  proof(rule CompDefinedI)
    show "g \<in> mor" and 0: "f \<in> mor" using assms by auto
    have "f ;; g maps dom f to cod g" using 1 by (simp add: MapsToCompI)
    hence "cod g = cod (f ;; g)" by auto
    also have "... = cod (id (dom f))" using assms by (auto simp add: inverse_rel_def)
    also have "... = dom f"
    proof-
      have "dom f \<in> obj" using 0 by (simp add: Simps)
      hence "id (dom f) maps (dom f) to (dom f)" by (simp add: Simps)
      thus ?thesis by auto
    qed
    finally show 2: "cod g = dom f" by simp
  qed
  show "g ;; f = id (dom g)" using assms by (auto simp add: inverse_rel_def)
  show "f ;; g = id (cod g)"using assms 1 2 by (auto simp add: inverse_rel_def)
qed

lemma (in Category) InverseUnique: 
  assumes 1: "cinv f g"
  and     2: "cinv f h"
  shows   "g = h"
proof(rule LeftRightInvUniq [of g f h])
  have "cinv g f" using 1 2 by (simp only: Inverse_relSym[of f g])
  thus "g \<approx>> f" and
    "g ;; f = id (cod f)" using 1 by auto
  show "f \<approx>> h" using 2 by auto
  show "f ;; h = id (dom f)" using 2 by auto
qed

lemma (in Category) InvId: assumes "X \<in> obj" shows "(cinv (id X) (id X))"
proof(rule Inverse_relI)
  show "id X \<approx>> id X" using assms by (simp add: Simps)
  have "dom (id X) = X" and "dom (id X) = X" using assms by (simp add: CatIdDomCod)+
  thus "id X ;; id X = id (dom (id X))" and "id X ;; id X = id (cod (id X))" 
    using assms by (simp add: CatIdCompId CatIdDomCod)+
qed
    
definition
  inverse :: "('o,'m,'a) Category_scheme \<Rightarrow> 'm \<Rightarrow> 'm" ("Cinv\<index> _" [70]) where
  "inverse C f \<equiv> THE g . inverse_rel C f g"

lemma (in Category) inv2Inv:
  assumes "cinv f g"
  shows   "ciso f" and "Cinv f = g"
proof-
  show "ciso f" using assms by (auto simp add: isomorphism_def)
  hence "\<exists>! g . cinv f g" using assms by (auto simp add: InverseUnique)
  thus "Cinv f = g" using assms by (auto simp add: inverse_def)
qed

lemma (in Category) iso2Inv:
  assumes "ciso f"
  shows   "cinv f (Cinv f)"
proof-
  have "\<exists>! g . cinv f g" using assms by (auto simp add: InverseUnique isomorphism_def)
  thus ?thesis by (auto simp add:  inverse_def intro:theI')
qed

lemma (in Category) InvInv:
  assumes "ciso f" 
  shows   "ciso (Cinv f)" and "(Cinv (Cinv f)) = f"
proof-
  have "cinv f (Cinv f)" using assms by (simp add: iso2Inv)
  hence "cinv (Cinv f) f" by (simp add: Inverse_relSym[of f])
  thus  "ciso (Cinv f)" and "Cinv (Cinv f) = f" by (auto simp add: inv2Inv)
qed

lemma (in Category) InvIsMor: "(cinv f g) \<Longrightarrow> (f \<in> mor \<and> g \<in> mor)"
  by (auto simp add: inverse_rel_def)

lemma (in Category) IsoIsMor: "ciso f \<Longrightarrow> f \<in> mor"
  by (auto simp add: InvIsMor dest: iso2Inv)

lemma (in Category) InvDomCod:
  assumes "ciso f"
  shows "dom (Cinv f) = cod f" and "cod (Cinv f) = dom f" and "Cinv f \<in> mor"
proof-
  have 1: "cinv f (Cinv f)" using assms by (auto simp add: iso2Inv)
  thus "dom (Cinv f) = cod f" by (auto simp add: inverse_rel_def)
  from 1 have "cinv (Cinv f) f" by (auto simp add: Inverse_relSym[of f])
  thus  "cod (Cinv f) = dom f" by (auto simp add: inverse_rel_def)
  show "Cinv f \<in> mor" using 1 by (auto simp add: inverse_rel_def)
qed

lemma (in Category) IsoCompInv: "ciso f \<Longrightarrow> f \<approx>> Cinv f"
  by (auto simp add: IsoIsMor InvDomCod)

lemma (in Category) InvCompIso: "ciso f \<Longrightarrow> Cinv f \<approx>> f"
  by (auto simp add: IsoIsMor InvDomCod)

lemma (in Category) IsoInvId1 : "ciso f \<Longrightarrow> (Cinv f) ;; f = (id (cod f))"
by (auto dest: iso2Inv)

lemma (in Category) IsoInvId2 :  "ciso f \<Longrightarrow> f ;; (Cinv f) = (id (dom f))"
by (auto dest: iso2Inv)

lemma (in Category) IsoCompDef:
  assumes 1: "f \<approx>> g" and 2: "ciso f" and 3: "ciso g"
  shows "(Cinv g) \<approx>> (Cinv f)"
proof(rule CompDefinedI)
  show "Cinv g \<in> mor" and "Cinv f \<in> mor" using assms by (auto simp add: InvDomCod)
  have "cod (Cinv g) = dom g" using 3 by (simp add: InvDomCod)
  also have "... = cod f" using 1 by auto
  also have "... = dom (Cinv f)" using 2 by (simp add: InvDomCod)
  finally show "cod (Cinv g) = dom (Cinv f)" .
qed

lemma (in Category) IsoCompose: 
  assumes 1: "f \<approx>> g" and 2: "ciso f" and 3: "ciso g"
  shows "ciso (f ;; g)" and "Cinv (f ;; g) = (Cinv g) ;; (Cinv f)"
proof-
  have  a: "(Cinv g) \<approx>> (Cinv f)" using assms by (simp add: IsoCompDef)
  hence b: "(Cinv g) ;; (Cinv f) maps (dom (Cinv g)) to (cod (Cinv f))" by (simp add: MapsToCompI)
  hence c: "(Cinv g) ;; (Cinv f) maps (cod g) to (dom f)" using 2 3 by (simp add: InvDomCod) 
  have  d: "f ;; g maps (dom f) to (cod g)" using 1 by (simp add: Simps)
  have "cinv (f ;; g) ((Cinv g) ;; (Cinv f))"
  proof(auto simp add: inverse_rel_def)
    show "f ;; g \<approx>> (Cinv g) ;; (Cinv f)"
    proof(rule CompDefinedI)
      show "f ;; g \<in> mor" using d by auto
      show "(Cinv g) ;; (Cinv f) \<in> mor" using c by auto
      have "cod (f ;; g) = cod g" using d by auto
      also have "... = dom (Cinv g)" using assms by (simp add: InvDomCod)
      also have "... = dom ((Cinv g) ;; (Cinv f))" using b by auto
      finally show "cod (f ;; g) = dom ((Cinv g) ;; (Cinv f))" .
    qed
    show "f ;; g ;; ((Cinv g) ;; (Cinv f)) = id (dom (f ;; g))"
    proof-
      have e: "g \<approx>> (Cinv g)" using assms by (simp add: IsoCompInv)
      have f: "f \<in> mor" using 1 by auto
      have "(f ;; g) ;; ((Cinv g) ;; (Cinv f)) = (f ;; (g ;; (Cinv g))) ;; (Cinv f)" 
        using 1 e a by (auto simp add: Cassoc CompDefComp)
      also have "... = f ;; (id (dom g)) ;; (Cinv f)" using 3 by (simp add: IsoInvId2)
      also have "... = f ;; id (cod f) ;; (Cinv f)" using 1 by (auto simp add: Simps)
      also have "... = f ;; (Cinv f)" using f by (auto simp add: Cidr)
      also have "... = id (dom f)" using 2 by (simp add: IsoInvId2)
      also have "... = id (dom (f ;; g))" using d by auto
      finally show ?thesis by simp
    qed
    show "((Cinv g) ;; (Cinv f)) ;; (f ;; g) = id (cod (f ;; g))"
    proof-
      have e: "(Cinv f) \<approx>> f" using assms by (simp add: InvCompIso)
      have f: "g \<in> mor" using 1 by auto
      have "((Cinv g) ;; (Cinv f)) ;; (f ;; g) = (Cinv g) ;; (((Cinv f) ;; f) ;; g)"
        using 1 e a by (auto simp add: Cassoc CompDefComp)
      also have "... = (Cinv g) ;; ((id (cod f)) ;; g)" using 2 by (simp add: IsoInvId1)
      also have "... = (Cinv g) ;; ((id (dom g)) ;; g)" using 1 by (auto simp add: Simps)
      also have "... = (Cinv g) ;; g" using f by (auto simp add: Cidl)
      also have "... = id (cod g)" using 3 by (simp add: IsoInvId1)
      also have "... = id (cod (f ;; g))" using d by auto
      finally show ?thesis by simp
    qed
  qed
  thus "ciso (f ;; g)" and "Cinv (f ;; g) = (Cinv g) ;; (Cinv f)" by (auto simp add: inv2Inv)
qed

definition "ObjIso C A B \<equiv> \<exists> k . (k maps\<^bsub>C\<^esub> A to B) \<and> ciso\<^bsub>C \<^esub>k"

definition 
  UnitCategory :: "(unit, unit) Category" where
  "UnitCategory = MakeCat \<lparr>
      Obj = {()} , 
      Mor = {()} , 
      Dom = (\<lambda>f.()) , 
      Cod = (\<lambda>f.()) , 
      Id = (\<lambda>f.()) , 
      Comp = (\<lambda>f g. ())
  \<rparr>"

lemma [simp]: "Category(UnitCategory)"
apply (simp add: UnitCategory_def, rule MakeCat)
by (unfold_locales, auto simp add: UnitCategory_def)

definition 
  OppositeCategory :: "('o,'m,'a) Category_scheme \<Rightarrow> ('o,'m,'a) Category_scheme" ("Op _" [65] 65) where
  "OppositeCategory C \<equiv> \<lparr>
      Obj = Obj C , 
      Mor = Mor C , 
      Dom = Cod C , 
      Cod = Dom C , 
      Id  = Id C , 
      Comp = (\<lambda>f g. g ;;\<^bsub>C\<^esub> f), 
      \<dots> = Category.more C
  \<rparr>"

lemma OpCatOpCat: "Op (Op C) = C"
  by (simp add: OppositeCategory_def)


lemma OpCatCatAx: "Category_axioms C \<Longrightarrow> Category_axioms (Op C)"
  by (simp add: OppositeCategory_def Category_axioms_def MapsTo_def CompDefined_def)

lemma OpCatCatExt: "ExtCategory C \<Longrightarrow> ExtCategory (Op C)"
  by (auto simp add: OppositeCategory_def ExtCategory_def MapsTo_def CompDefined_def extensional_def)

lemma OpCatCat: "Category C \<Longrightarrow> Category (Op C)"
  by (intro_locales, simp_all add: Category_def OpCatCatAx OpCatCatExt)


lemma MapsToOp: "f maps\<^bsub>C \<^esub>X to Y \<Longrightarrow> f maps\<^bsub>Op C \<^esub>Y to X"
by (simp add: MapsTo_def OppositeCategory_def)

lemma MapsToOpOp: "f maps\<^bsub>Op C \<^esub>X to Y \<Longrightarrow> f maps\<^bsub>C \<^esub>Y to X"
by (simp add: MapsTo_def OppositeCategory_def)

lemma CompDefOp: "f \<approx>>\<^bsub>C\<^esub> g \<Longrightarrow> g \<approx>>\<^bsub>Op C\<^esub> f"
by (simp add: CompDefined_def OppositeCategory_def)

end
