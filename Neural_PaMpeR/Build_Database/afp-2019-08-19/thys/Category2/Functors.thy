(*
Author: Alexander Katovsky
*)

section "Functor"

theory Functors
imports Category
begin

record ('o1, 'o2, 'm1, 'm2, 'a, 'b) Functor = 
  CatDom :: "('o1,'m1,'a)Category_scheme" 
  CatCod :: "('o2,'m2,'b)Category_scheme" 
  MapM :: "'m1 \<Rightarrow> 'm2" 

abbreviation
  FunctorMorApp :: "('o1, 'o2, 'm1, 'm2, 'a1, 'a2, 'a) Functor_scheme \<Rightarrow> 'm1 \<Rightarrow> 'm2" (infixr "##" 70) where
  "FunctorMorApp F m \<equiv> (MapM F) m"

definition
  MapO :: "('o1, 'o2, 'm1, 'm2, 'a1, 'a2, 'a) Functor_scheme \<Rightarrow> 'o1 \<Rightarrow> 'o2"  where
  "MapO F X \<equiv> THE Y . Y \<in> Obj(CatCod F) \<and>  F ## (Id (CatDom F) X) = Id (CatCod F) Y"

abbreviation
  FunctorObjApp :: "('o1, 'o2, 'm1, 'm2, 'a1, 'a2, 'a) Functor_scheme \<Rightarrow> 'o1 \<Rightarrow> 'o2" (infixr "@@" 70) where
  "FunctorObjApp F X \<equiv> (MapO F X)"

locale PreFunctor = 
  fixes F :: "('o1, 'o2, 'm1, 'm2, 'a1, 'a2, 'a) Functor_scheme"  (structure) 
  assumes FunctorComp: "f \<approx>>\<^bsub>CatDom F\<^esub> g \<Longrightarrow> F ## (f ;;\<^bsub>CatDom F\<^esub> g) = (F ## f) ;;\<^bsub>CatCod F\<^esub> (F ## g)"
  and     FunctorId:   "X \<in> obj\<^bsub>CatDom F\<^esub> \<Longrightarrow> \<exists> Y \<in> obj\<^bsub>CatCod F\<^esub> . F ## (id\<^bsub>CatDom F\<^esub> X) = id\<^bsub>CatCod F\<^esub> Y"
  and     CatDom[simp]:      "Category(CatDom F)"
  and     CatCod[simp]:      "Category(CatCod F)"

locale FunctorM = PreFunctor +
  assumes     FunctorCompM: "f maps\<^bsub>CatDom F\<^esub> X to Y \<Longrightarrow> (F ## f) maps\<^bsub>CatCod F\<^esub> (F @@ X) to (F @@ Y)"

locale FunctorExt = 
  fixes F :: "('o1, 'o2, 'm1, 'm2, 'a1, 'a2, 'a) Functor_scheme"  (structure) 
  assumes FunctorMapExt: "(MapM F) \<in> extensional (Mor (CatDom F))"

locale Functor = FunctorM + FunctorExt

definition 
  MakeFtor :: "('o1, 'o2, 'm1, 'm2, 'a, 'b,'r) Functor_scheme \<Rightarrow> ('o1, 'o2, 'm1, 'm2, 'a, 'b,'r) Functor_scheme" where
  "MakeFtor F \<equiv> \<lparr>
      CatDom = CatDom F , 
      CatCod = CatCod F , 
      MapM = restrict (MapM F) (Mor (CatDom F)) , 
      \<dots> = Functor.more F
  \<rparr>"

lemma PreFunctorFunctor[simp]: "Functor F \<Longrightarrow> PreFunctor F"
by (simp add: Functor_def FunctorM_def)

lemmas functor_simps = PreFunctor.FunctorComp PreFunctor.FunctorId

definition 
  functor_abbrev ("Ftor _ : _ \<longrightarrow> _" [81]) where
  "Ftor F : A \<longrightarrow> B \<equiv> (Functor F) \<and> (CatDom F = A) \<and> (CatCod F = B)"

lemma functor_abbrevE[elim]: "\<lbrakk>Ftor F : A \<longrightarrow> B ; \<lbrakk>(Functor F) ; (CatDom F = A) ; (CatCod F = B)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (auto simp add: functor_abbrev_def)

definition
  functor_comp_def ("_ \<approx>>;;; _" [81]) where
  "functor_comp_def F G \<equiv> (Functor F) \<and> (Functor G) \<and> (CatDom G = CatCod F)"

lemma functor_comp_def[elim]: "\<lbrakk>F \<approx>>;;; G ; \<lbrakk>Functor F ; Functor G ; CatDom G = CatCod F\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (auto simp add: functor_comp_def_def)

lemma (in Functor) FunctorMapsTo:
  assumes "f \<in> mor\<^bsub>CatDom F\<^esub>"
  shows   "F ## f maps\<^bsub>CatCod F\<^esub> (F @@ (dom\<^bsub>CatDom F\<^esub> f)) to (F @@ (cod\<^bsub>CatDom F\<^esub> f))"
proof-
  have "f maps\<^bsub>CatDom F\<^esub> (dom\<^bsub>CatDom F\<^esub> f) to (cod\<^bsub>CatDom F\<^esub> f)" using assms by auto
  thus ?thesis by (simp add: FunctorCompM[of f "dom\<^bsub>CatDom F\<^esub> f" "cod\<^bsub>CatDom F\<^esub> f"])
qed

lemma (in Functor) FunctorCodDom: 
  assumes "f \<in> mor\<^bsub>CatDom F\<^esub>"
  shows "dom\<^bsub>CatCod F\<^esub>(F ## f) = F @@ (dom\<^bsub>CatDom F\<^esub> f)" and "cod\<^bsub>CatCod F\<^esub>(F ## f) = F @@ (cod\<^bsub>CatDom F\<^esub> f)"
proof-
  have "F ## f maps\<^bsub>CatCod F\<^esub> (F @@ (dom\<^bsub>CatDom F\<^esub> f)) to (F @@ (cod\<^bsub>CatDom F\<^esub> f))" using assms by (simp add: FunctorMapsTo)
  thus "dom\<^bsub>CatCod F\<^esub>(F ## f) = F @@ (dom\<^bsub>CatDom F\<^esub> f)" and "cod\<^bsub>CatCod F\<^esub>(F ## f) = F @@ (cod\<^bsub>CatDom F\<^esub> f)"
    by auto
qed

lemma (in Functor) FunctorCompPreserved: "f \<in> mor\<^bsub>CatDom F\<^esub> \<Longrightarrow> F ## f \<in> mor\<^bsub>CatCod F\<^esub>"
by (auto dest:FunctorMapsTo)

lemma (in Functor) FunctorCompDef: 
  assumes "f \<approx>>\<^bsub>CatDom F\<^esub> g" shows "(F ## f) \<approx>>\<^bsub>CatCod F\<^esub> (F ## g)"
proof(auto simp add: CompDefined_def)
  show "F ## f \<in> mor\<^bsub>CatCod F\<^esub>" and "F ## g \<in> mor\<^bsub>CatCod F\<^esub>" using assms by (auto simp add: FunctorCompPreserved)
  have "f \<in> mor\<^bsub>CatDom F\<^esub>" and "g \<in> mor\<^bsub>CatDom F\<^esub>" using assms by auto
  hence a: "cod\<^bsub>CatCod F\<^esub> (F ## f) = F @@ (cod\<^bsub>CatDom F\<^esub> f)" and b: "dom\<^bsub>CatCod F\<^esub>(F ## g) = F @@ (dom\<^bsub>CatDom F\<^esub> g)"
    by (simp add: FunctorCodDom)+
  have "cod\<^bsub>CatCod F\<^esub> (F ## f) = F @@ (dom\<^bsub>CatDom F\<^esub> g)" using assms a by auto
  also have "... = dom\<^bsub>CatCod F\<^esub> (F ## g)" using b by simp
  finally show "cod\<^bsub>CatCod F\<^esub> (F ## f) = dom\<^bsub>CatCod F\<^esub> (F ## g)" .
qed

lemma FunctorComp: "\<lbrakk>Ftor F : A \<longrightarrow> B ; f \<approx>>\<^bsub>A\<^esub> g\<rbrakk> \<Longrightarrow> F ## (f ;;\<^bsub>A\<^esub> g) = (F ## f) ;;\<^bsub>B\<^esub> (F ## g)"
by (auto simp add: PreFunctor.FunctorComp)

lemma FunctorCompDef: "\<lbrakk>Ftor F : A \<longrightarrow> B ; f \<approx>>\<^bsub>A\<^esub> g\<rbrakk> \<Longrightarrow> (F ## f) \<approx>>\<^bsub>B\<^esub> (F ## g)"
by (auto simp add: Functor.FunctorCompDef)

lemma FunctorMapsTo: 
  assumes "Ftor F : A \<longrightarrow> B" and "f maps\<^bsub>A\<^esub> X to Y" 
  shows "(F ## f) maps\<^bsub>B\<^esub> (F @@ X) to (F @@ Y)"
proof-
  have b: "CatCod F = B" and a: "CatDom F = A" and ff: "Functor F" using assms by auto
  have df: "(dom\<^bsub>CatDom F\<^esub> f) = X" and cf: "(cod\<^bsub>CatDom F\<^esub> f) = Y" using a assms by auto
  have "f \<in> mor\<^bsub>CatDom F\<^esub>" using assms by auto
  hence "F ## f maps\<^bsub>CatCod F\<^esub> (F @@ (dom\<^bsub>CatDom F\<^esub> f)) to (F @@ (cod\<^bsub>CatDom F\<^esub> f))" using ff
    by (simp add: Functor.FunctorMapsTo) 
  thus ?thesis using df cf b by simp
qed

lemma (in PreFunctor) FunctorId2: 
  assumes "X \<in> obj\<^bsub>CatDom F\<^esub>"
  shows   "F @@ X \<in> obj\<^bsub>CatCod F\<^esub> \<and> F ## (id\<^bsub>CatDom F\<^esub> X) = id\<^bsub>CatCod F\<^esub> (F @@ X)"
proof-
  let ?Q = "\<lambda> E Y . Y \<in> obj\<^bsub>CatCod F\<^esub> \<and> E = id\<^bsub>CatCod F\<^esub> Y"
  let ?P = "?Q (F ## (id\<^bsub>CatDom F\<^esub> X))"
  from assms FunctorId obtain Y where "?P Y" by auto
  moreover  { 
    fix y e z have "\<lbrakk>?Q e y ; ?Q e z\<rbrakk> \<Longrightarrow> y = z"
      by (auto intro: Category.IdInj[of "CatCod F" y z])
  }
  ultimately have "\<exists>! Z . ?P Z" by auto
  hence "?P (THE Y . ?P Y)" by (rule theI')
  thus ?thesis by (auto simp add: MapO_def)
qed

lemma FunctorId:
  assumes "Ftor F : C \<longrightarrow> D" and "X \<in> Obj C"
  shows "F ## (Id C X) = Id D (F @@ X)"
proof-
  have "CatDom F = C" and "CatCod F = D" and "PreFunctor F" using assms by auto
  thus ?thesis using assms PreFunctor.FunctorId2[of F X] by simp
qed

lemma (in Functor) DomFunctor: "f \<in> mor\<^bsub>CatDom F\<^esub> \<Longrightarrow> dom\<^bsub>CatCod F\<^esub> (F ## f) = F @@ (dom\<^bsub>CatDom F\<^esub> f)"
by (simp add: FunctorCodDom)

lemma (in Functor) CodFunctor: "f \<in> mor\<^bsub>CatDom F\<^esub> \<Longrightarrow> cod\<^bsub>CatCod F\<^esub> (F ## f) = F @@ (cod\<^bsub>CatDom F\<^esub> f)"
by (simp add: FunctorCodDom) 

lemma (in Functor) FunctorId3Dom:
  assumes "f \<in> mor\<^bsub>CatDom F\<^esub>"
  shows   "F ## (id\<^bsub>CatDom F\<^esub> (dom\<^bsub>CatDom F\<^esub> f)) = id\<^bsub>CatCod F\<^esub> (dom\<^bsub>CatCod F\<^esub> (F ## f))"
proof-
  have "(dom\<^bsub>CatDom F\<^esub> f) \<in> obj\<^bsub>CatDom F\<^esub>" using assms by (simp add: Category.Cdom)
  hence "F ## (id\<^bsub>CatDom F\<^esub> (dom\<^bsub>CatDom F\<^esub> f)) = id\<^bsub>CatCod F\<^esub> (F @@ (dom\<^bsub>CatDom F\<^esub> f))" by (simp add: FunctorId2)
  also have "... = id\<^bsub>CatCod F\<^esub> (dom\<^bsub>CatCod F\<^esub> (F ## f))" using assms by (simp add: DomFunctor)
  finally show ?thesis by simp
qed

lemma (in Functor) FunctorId3Cod:
  assumes "f \<in> mor\<^bsub>CatDom F\<^esub>"
  shows   "F ## (id\<^bsub>CatDom F\<^esub> (cod\<^bsub>CatDom F\<^esub> f)) = id\<^bsub>CatCod F\<^esub> (cod\<^bsub>CatCod F\<^esub> (F ## f))"
proof-
  have "(cod\<^bsub>CatDom F\<^esub> f) \<in> obj\<^bsub>CatDom F\<^esub>" using assms by (simp add: Category.Ccod)
  hence "F ## (id\<^bsub>CatDom F\<^esub> (cod\<^bsub>CatDom F\<^esub> f)) = id\<^bsub>CatCod F\<^esub> (F @@ (cod\<^bsub>CatDom F\<^esub> f))" by (simp add: FunctorId2)
  also have "... = id\<^bsub>CatCod F\<^esub> (cod\<^bsub>CatCod F\<^esub> (F ## f))" using assms by (simp add: CodFunctor)
  finally show ?thesis by simp
qed

lemma (in PreFunctor) FmToFo: "\<lbrakk>X \<in> obj\<^bsub>CatDom F\<^esub> ; Y \<in> obj\<^bsub>CatCod F\<^esub> ; F ## (id\<^bsub>CatDom F\<^esub> X) = id\<^bsub>CatCod F\<^esub> Y\<rbrakk> \<Longrightarrow> F @@ X = Y"
  by (auto simp add: FunctorId2 intro: Category.IdInj[of "CatCod F" "F @@ X" Y])

lemma MakeFtorPreFtor: 
  assumes "PreFunctor F" shows "PreFunctor (MakeFtor F)"
proof-
  {
    fix X assume a: "X \<in> obj\<^bsub>CatDom F\<^esub>" have "id\<^bsub>CatDom F \<^esub>X \<in> mor\<^bsub>CatDom F\<^esub>"
    proof-
      have "Category (CatDom F)" using assms by (simp add: PreFunctor_def)
      hence "id\<^bsub>CatDom F \<^esub>X maps\<^bsub>CatDom F\<^esub> X to X" using a by (simp add: Category.Cidm)
      thus ?thesis using a by (auto)
    qed
  }
  thus "PreFunctor (MakeFtor F)" using assms
    by(auto simp add: PreFunctor_def MakeFtor_def Category.MapsToMorDomCod)
qed

lemma MakeFtorMor: "f \<in> mor\<^bsub>CatDom F\<^esub> \<Longrightarrow> MakeFtor F ## f = F ## f"
by(simp add: MakeFtor_def)

lemma MakeFtorObj: 
  assumes "PreFunctor F" and "X \<in> obj\<^bsub>CatDom F\<^esub>"
  shows "MakeFtor F @@ X = F @@ X"
proof-
  have "X \<in> obj\<^bsub>CatDom (MakeFtor F)\<^esub>" using assms(2) by (simp add: MakeFtor_def)
  moreover have "(F @@ X) \<in> obj\<^bsub>CatCod (MakeFtor F)\<^esub>" using assms by (simp add: PreFunctor.FunctorId2 MakeFtor_def)
  moreover have "MakeFtor F ## id\<^bsub>CatDom (MakeFtor F) \<^esub>X = id\<^bsub>CatCod (MakeFtor F) \<^esub>(F @@ X)" 
  proof-
    have "Category (CatDom F)" using assms(1) by (simp add: PreFunctor_def)
    hence "id\<^bsub>CatDom F \<^esub>X  maps\<^bsub>CatDom F\<^esub> X to X" using assms(2) by (auto simp add: Category.Cidm)
    hence "id\<^bsub>CatDom F \<^esub>X \<in> mor\<^bsub>CatDom F\<^esub>" by auto
    hence "MakeFtor F ## id\<^bsub>CatDom (MakeFtor F) \<^esub>X = F ## id\<^bsub>CatDom F \<^esub>X" by (simp add: MakeFtor_def)
    also have "... = id\<^bsub>CatCod F \<^esub>(F @@ X)" using assms by (simp add: PreFunctor.FunctorId2)
    finally show ?thesis by (simp add: MakeFtor_def)
  qed
  moreover have "PreFunctor (MakeFtor F)" using assms(1) by (simp add: MakeFtorPreFtor)
  ultimately show ?thesis by (simp add: PreFunctor.FmToFo)
qed

lemma MakeFtor: assumes "FunctorM F" shows "Functor (MakeFtor F)" 
proof(intro_locales)
  show "PreFunctor (MakeFtor F)" using assms by (simp add: MakeFtorPreFtor FunctorM_def)
  show "FunctorM_axioms (MakeFtor F)"
  proof(auto simp add: FunctorM_axioms_def)
    {
      fix f X Y assume aa: "f maps\<^bsub>CatDom (MakeFtor F)\<^esub> X to Y"
      show "((MakeFtor F) ## f) maps\<^bsub>CatCod (MakeFtor F)\<^esub> ((MakeFtor F) @@ X) to ((MakeFtor F) @@ Y)"
      proof-
        have "((MakeFtor F) ## f) = F ## f" using aa by (auto simp add: MakeFtor_def)
        moreover have "((MakeFtor F) @@ X) = F @@ X" and "((MakeFtor F) @@ Y) = F @@ Y"
        proof-
          have "Category (CatDom F)" using assms by (simp add: FunctorM_def PreFunctor_def)
          hence "X \<in> obj\<^bsub>CatDom F\<^esub>" and "Y \<in> obj\<^bsub>CatDom F\<^esub>" 
            using aa by (auto simp add: Category.MapsToObj MakeFtor_def)
          moreover have "PreFunctor F" using assms(1) by (simp add: FunctorM_def)
          ultimately show "((MakeFtor F) @@ X) = F @@ X" and "((MakeFtor F) @@ Y) = F @@ Y"
            by (simp add: MakeFtorObj)+
        qed
        moreover have "F ## f maps\<^bsub>CatCod F\<^esub> (F @@ X) to (F @@ Y)" using assms(1) aa 
          by (simp add: FunctorM.FunctorCompM MakeFtor_def)
        ultimately show ?thesis by (simp add: MakeFtor_def)
      qed
    }
  qed
  show "FunctorExt (MakeFtor F)" by(simp add: FunctorExt_def MakeFtor_def)
qed

definition 
  IdentityFunctor' :: "('o,'m,'a) Category_scheme \<Rightarrow> ('o,'o,'m,'m,'a,'a) Functor" ("FId' _" [70]) where
  "IdentityFunctor' C \<equiv> \<lparr>CatDom = C , CatCod = C , MapM = (\<lambda> f . f) \<rparr>"

definition 
  IdentityFunctor ("FId _" [70]) where
  "IdentityFunctor C \<equiv> MakeFtor(IdentityFunctor' C)"

lemma IdFtor'PreFunctor: "Category C \<Longrightarrow> PreFunctor (FId' C)"
by(auto simp add: PreFunctor_def IdentityFunctor'_def)

lemma IdFtor'Obj:
  assumes "Category C" and "X \<in> obj\<^bsub>CatDom (FId' C)\<^esub>"
  shows "(FId' C) @@ X = X"
proof-
  have "(FId' C) ## id\<^bsub>CatDom (FId' C)\<^esub> X = id\<^bsub>CatCod (FId' C)\<^esub> X" by(simp add: IdentityFunctor'_def)
  moreover have "X \<in> obj\<^bsub>CatCod (FId' C)\<^esub>" using assms by (simp add: IdentityFunctor'_def)
  ultimately show ?thesis using assms by (simp add: PreFunctor.FmToFo IdFtor'PreFunctor)
qed

lemma IdFtor'FtorM:  
  assumes "Category C" shows "FunctorM (FId' C)"
proof(auto simp add: FunctorM_def IdFtor'PreFunctor assms FunctorM_axioms_def)
  {
    fix f X Y assume a: "f maps\<^bsub>CatDom (FId' C)\<^esub> X to Y" 
    show "((FId' C) ## f) maps\<^bsub>CatCod (FId' C)\<^esub> ((FId' C) @@ X) to ((FId' C) @@ Y)"
    proof-
      have "X \<in> obj\<^bsub>CatDom (FId' C)\<^esub>" and "Y \<in> obj\<^bsub>CatDom (FId' C)\<^esub>"
        using a assms by (simp add: Category.MapsToObj IdentityFunctor'_def)+
      moreover have "(FId' C) ## f = f" and "CatDom (FId' C) = CatCod (FId' C)" by (simp add: IdentityFunctor'_def)+
      ultimately show ?thesis using assms a by(simp add: IdFtor'Obj)
    qed
  }
qed

lemma IdFtorFtor:  "Category C \<Longrightarrow> Functor (FId C)"
by (auto simp add: IdentityFunctor_def IdFtor'FtorM intro: MakeFtor)

definition 
  ConstFunctor' :: "('o1,'m1,'a) Category_scheme \<Rightarrow> 
                  ('o2,'m2,'b) Category_scheme \<Rightarrow> 'o2 \<Rightarrow> ('o1,'o2,'m1,'m2,'a,'b) Functor"  where
  "ConstFunctor' A B b \<equiv> \<lparr>
         CatDom = A , 
         CatCod = B , 
         MapM = (\<lambda> f . (Id B) b)
  \<rparr>"

definition "ConstFunctor A B b \<equiv> MakeFtor(ConstFunctor' A B b)"

lemma ConstFtor' : 
  assumes "Category A" "Category B" "b \<in> (Obj B)"
  shows   "PreFunctor (ConstFunctor' A B b)"
  and     "FunctorM (ConstFunctor' A B b)"
proof-
  show "PreFunctor (ConstFunctor' A B b)" using assms
    apply (subst PreFunctor_def)
    apply (rule conjI)+
    by (auto simp add: ConstFunctor'_def Category.Simps Category.CatIdCompId)
  moreover 
  {
    fix X  assume "X \<in> obj\<^bsub>A\<^esub>" "b \<in> obj\<^bsub>B\<^esub>" "PreFunctor (ConstFunctor' A B b)" 
    hence "(ConstFunctor' A B b) @@ X = b"
      by (auto simp add: ConstFunctor'_def PreFunctor.FmToFo Category.Simps)
  }
  ultimately show "FunctorM (ConstFunctor' A B b)" using assms
    by (intro_locales, auto simp add: ConstFunctor'_def Category.Simps FunctorM_axioms_def)
qed

lemma ConstFtor: 
  assumes "Category A" "Category B" "b \<in> (Obj B)"
  shows "Functor (ConstFunctor A B b)"
by (auto simp add: assms ConstFtor' ConstFunctor_def MakeFtor)

definition 
  UnitFunctor :: "('o,'m,'a) Category_scheme \<Rightarrow> ('o,unit,'m,unit,'a,unit) Functor"  where
  "UnitFunctor C \<equiv> ConstFunctor C UnitCategory ()"

lemma UnitFtor: 
  assumes "Category C" 
  shows "Functor(UnitFunctor C)"
proof-
  have "() \<in> obj\<^bsub>UnitCategory\<^esub>" by (simp add: UnitCategory_def MakeCatObj)
  hence "Functor(ConstFunctor C UnitCategory ())" using assms 
    by (simp add: ConstFtor)
  thus ?thesis by (simp add: UnitFunctor_def)
qed

definition
  FunctorComp' :: "('o1,'o2,'m1,'m2,'a1,'a2) Functor \<Rightarrow> ('o2,'o3,'m2,'m3,'b1,'b2) Functor
                    \<Rightarrow> ('o1,'o3,'m1,'m3,'a1,'b2) Functor" (infixl ";;:" 71) where
  "FunctorComp' F G \<equiv> \<lparr>
        CatDom = CatDom F , 
        CatCod = CatCod G ,
        MapM   = \<lambda> f . (MapM G)((MapM F) f)
  \<rparr>"

definition FunctorComp (infixl ";;;" 71) where "FunctorComp F G \<equiv> MakeFtor (FunctorComp' F G)"

lemma FtorCompComp':
  assumes "f \<approx>>\<^bsub>CatDom F\<^esub> g"
  and "F \<approx>>;;; G"
  shows "G ## (F ## (f ;;\<^bsub>CatDom F\<^esub> g)) = (G ## (F ## f)) ;;\<^bsub>CatCod G\<^esub> (G ## (F ## g))"
proof-
  have [simp]: "PreFunctor G \<and> PreFunctor F" using assms by auto
  have [simp]: "(F ## f) \<approx>>\<^bsub>CatDom G\<^esub> (F ## g)" using assms by (auto simp add: Functor.FunctorCompDef[of F f g])
  have "F ## (f ;;\<^bsub>CatDom F\<^esub> g) = (F ## f) ;;\<^bsub>CatCod F\<^esub> (F ## g)" using assms
    by (auto simp add: PreFunctor.FunctorComp)
  hence "G ## (F ## (f ;;\<^bsub>CatDom F\<^esub> g)) = G ## ((F ## f) ;;\<^bsub>CatCod F\<^esub> (F ## g))" by simp
  also have "... = G ## ((F ## f) ;;\<^bsub>CatDom G\<^esub> (F ## g))" using assms by auto
  also have "... = (G ## (F ## f)) ;;\<^bsub>CatCod G\<^esub> (G ## (F ## g))"
    by (simp add: PreFunctor.FunctorComp[of G "(F ## f)" "(F ## g)"])
  finally show ?thesis by simp
qed

lemma FtorCompId: 
  assumes a: "X \<in> (Obj (CatDom F))"
  and "F \<approx>>;;; G"
  shows "G ## (F ## (id\<^bsub>CatDom F \<^esub>X)) = id\<^bsub>CatCod G\<^esub>(G @@ (F @@ X)) \<and> G @@ (F @@ X) \<in> (Obj (CatCod G))"
proof-
  have [simp]: "PreFunctor G \<and> PreFunctor F" using assms by auto
  have b: "(F @@ X) \<in> obj\<^bsub>CatDom G\<^esub>" using assms
    by (auto simp add: PreFunctor.FunctorId2)
  have "G ## F ## (id\<^bsub>CatDom F \<^esub>X) = G ## (id\<^bsub>CatCod F\<^esub>(F @@ X))" using b a
    by (simp add: PreFunctor.FunctorId2[of F "X"])
  also have "... = G ## (id\<^bsub>CatDom G\<^esub>(F @@ X))" using assms by auto
  also have "... = id\<^bsub>CatCod G\<^esub>(G @@ (F @@ X)) \<and> G @@ (F @@ X) \<in> (Obj (CatCod G))" using b
    by (simp add: PreFunctor.FunctorId2[of G "(F @@ X)"])
  finally show ?thesis by simp
qed

lemma FtorCompIdDef: 
  assumes a: "X \<in> (Obj (CatDom F))" and b: "PreFunctor (F ;;: G)" 
  and "F \<approx>>;;; G"
  shows "(F ;;: G) @@ X = (G @@ (F @@ X))"
proof-
  have "(F ;;: G) ## (id\<^bsub>CatDom (F ;;: G)\<^esub>(X)) = G ## (F ## (id\<^bsub>CatDom F\<^esub>(X)))" using assms
    by (simp add: FunctorComp'_def)
  also have "... = id\<^bsub>CatCod G\<^esub>(G @@ (F @@ (X)))" using assms a
    by(auto simp add: FtorCompId[of _ F G])
  finally have "(F ;;: G) ## (id\<^bsub>CatDom (F ;;: G)\<^esub>(X)) = id\<^bsub>CatCod (F ;;: G)\<^esub>(G @@ (F @@ X))" using assms
    by (simp add: FunctorComp'_def)
  moreover have "G @@ (F @@ (X)) \<in> (Obj (CatCod (F ;;: G)))" using assms a
    by(auto simp add: FtorCompId[of _ F G] FunctorComp'_def)
  moreover have "X \<in> obj\<^bsub>CatDom (F ;;: G)\<^esub>" using a by (simp add: FunctorComp'_def)
  ultimately show ?thesis using b 
    by (simp add: PreFunctor.FmToFo[of "F ;;: G" X "G @@ (F @@ X)"])
qed

lemma FunctorCompMapsTo: 
  assumes "f \<in> mor\<^bsub>CatDom (F ;;: G)\<^esub>" and "F \<approx>>;;; G"
  shows "(G ## (F ## f)) maps\<^bsub>CatCod G\<^esub> (G @@ (F @@ (dom\<^bsub>CatDom F\<^esub> f))) to (G @@ (F @@ (cod\<^bsub>CatDom F\<^esub> f)))"
proof-
  have "f \<in> mor\<^bsub>CatDom F \<^esub>\<and> Functor F" using assms by (auto simp add: FunctorComp'_def)
  hence "(F ## f) maps\<^bsub>CatDom G\<^esub> (F @@ (dom\<^bsub>CatDom F\<^esub> f)) to (F @@ (cod\<^bsub>CatDom F\<^esub> f))" using assms 
    by (auto simp add: Functor.FunctorMapsTo[of F f])
  moreover have "FunctorM G" using assms by (auto simp add: FunctorComp_def Functor_def)
  ultimately show ?thesis by(simp add: FunctorM.FunctorCompM[of G "F ## f" "F @@ (dom\<^bsub>CatDom F\<^esub> f)" "F @@ (cod\<^bsub>CatDom F\<^esub> f)"])
qed

lemma FunctorCompMapsTo2:
  assumes "f \<in> mor\<^bsub>CatDom (F ;;: G)\<^esub>" 
  and "F \<approx>>;;; G"
  and "PreFunctor (F ;;: G)" 
  shows "((F ;;: G) ## f) maps\<^bsub>CatCod (F ;;: G)\<^esub> ((F ;;: G) @@ (dom\<^bsub>CatDom (F ;;: G)\<^esub> f)) to 
                                               ((F ;;: G) @@ (cod\<^bsub>CatDom (F ;;: G)\<^esub> f))"
proof-
  have "Category (CatDom (F ;;: G))" using assms by (simp add: PreFunctor_def) 
  hence 1: "(dom\<^bsub>CatDom (F ;;: G)\<^esub> f) \<in> obj\<^bsub>CatDom F \<^esub>\<and> (cod\<^bsub>CatDom (F ;;: G)\<^esub> f) \<in> obj\<^bsub>CatDom F\<^esub>" using assms 
    by (auto simp add: Category.Simps FunctorComp'_def)
  have "(G ## (F ## f)) maps\<^bsub>CatCod G\<^esub> (G @@ (F @@ (dom\<^bsub>CatDom F\<^esub> f))) to (G @@ (F @@ (cod\<^bsub>CatDom F\<^esub> f)))"
    using assms by (auto simp add: FunctorCompMapsTo[of f F G])
  moreover have "CatDom F = CatDom(F ;;: G) \<and> CatCod G = CatCod(F ;;: G) \<and> (G ## (F ## f)) = ((F ;;: G) ## f)" using assms
    by (simp add: FunctorComp'_def)
  moreover have "(F ;;: G) @@ (dom\<^bsub>CatDom (F ;;: G)\<^esub> f) = (G @@ (F @@ (dom\<^bsub>CatDom(F ;;: G)\<^esub> f))) \<and>
        (F ;;: G) @@ (cod\<^bsub>CatDom (F ;;: G)\<^esub> f) = (G @@ (F @@ (cod\<^bsub>CatDom(F ;;: G)\<^esub> f)))" 
    by (auto simp add: FtorCompIdDef[of _ F G] 1 assms)
  ultimately show ?thesis by auto
qed

lemma FunctorCompMapsTo3:
  assumes "f maps\<^bsub>CatDom (F ;;: G)\<^esub> X to Y"
  and "F \<approx>>;;; G"
  and "PreFunctor (F ;;: G)" 
  shows "F ;;: G ## f maps\<^bsub>CatCod (F ;;: G)\<^esub> F ;;: G @@ X to F ;;: G @@ Y"
proof-
  have  "f \<in> mor\<^bsub>CatDom (F ;;: G)\<^esub>" 
    and "dom\<^bsub>CatDom (F ;;: G)\<^esub> f = X" 
    and "cod\<^bsub>CatDom (F ;;: G)\<^esub> f = Y" using assms by auto
  thus ?thesis using assms by (auto intro: FunctorCompMapsTo2)
qed

lemma FtorCompPreFtor:
  assumes "F \<approx>>;;; G"
  shows   "PreFunctor (F ;;: G)"
proof-
  have 1: "PreFunctor G \<and> PreFunctor F" using assms by auto
  show "PreFunctor (F ;;: G)" using assms
  proof(auto simp add: PreFunctor_def FunctorComp'_def Category.Simps
       FtorCompId[of _ F G] intro:FtorCompComp')
    show "Category (CatDom F)" and "Category (CatCod G)" using assms 1 by (auto simp add: PreFunctor_def)
  qed
qed

lemma FtorCompM : 
  assumes "F \<approx>>;;; G"
  shows   "FunctorM (F ;;: G)"
proof(auto simp only: FunctorM_def)
  show 1: "PreFunctor (F ;;: G)" using assms by (rule FtorCompPreFtor)
  {
    fix X Y f assume a: "f maps\<^bsub>CatDom (F ;;: G)\<^esub> X to Y"
    have "F ;;: G ## f maps\<^bsub>CatCod (F ;;: G)\<^esub> F ;;: G @@ X to F ;;: G @@ Y" 
      using a assms 1 by (rule FunctorCompMapsTo3)
  }
  thus "FunctorM_axioms (F ;;: G)" 
    by(auto simp add: 1 FunctorM_axioms_def)
qed

lemma FtorComp:   
  assumes "F \<approx>>;;; G"
  shows   "Functor (F ;;; G)"
proof-
  have "FunctorM (F ;;: G)" using assms by (rule FtorCompM)
  thus ?thesis by (simp add: FunctorComp_def MakeFtor)
qed

lemma (in Functor) FunctorPreservesIso: 
  assumes     "ciso\<^bsub>CatDom F\<^esub> k"
  shows       "ciso\<^bsub>CatCod F\<^esub> (F ## k)"
proof-
  have [simp]: "k \<in> mor\<^bsub>CatDom F\<^esub>" using assms by (simp add: Category.IsoIsMor)
  have "cinv\<^bsub>CatCod F\<^esub> (F ## k) (F ## (Cinv\<^bsub>CatDom F\<^esub> k))" 
    proof(rule Category.Inverse_relI)
      show "Category (CatCod F)" by simp
      show "(F ## k) \<approx>>\<^bsub>CatCod F\<^esub> (F ## (Cinv\<^bsub>CatDom F\<^esub> k))" 
        by (rule FunctorCompDef, simp add: Category.IsoCompInv assms)
      show "(F ## k) ;;\<^bsub>CatCod F\<^esub> (F ## (Cinv\<^bsub>CatDom F\<^esub> k)) = id\<^bsub>CatCod F\<^esub> (dom\<^bsub>CatCod F\<^esub> (F ## k))" 
      proof-
        have      "(F ## k) ;;\<^bsub>CatCod F\<^esub> (F ## (Cinv\<^bsub>CatDom F\<^esub> k)) = F ## (k ;;\<^bsub>CatDom F\<^esub> (Cinv\<^bsub>CatDom F\<^esub> k))" using assms
          by(auto simp add: FunctorComp Category.IsoCompInv)
        also have "... = F ## (id\<^bsub>CatDom F\<^esub> (dom\<^bsub>CatDom F\<^esub> k))" using assms by (simp add: Category.IsoInvId2)
        also have "... = id\<^bsub>CatCod F\<^esub> (dom\<^bsub>CatCod F\<^esub> (F ## k))" by (simp add: FunctorId3Dom) 
        finally show ?thesis by simp
      qed 
      show "(F ## (Cinv\<^bsub>CatDom F\<^esub> k)) ;;\<^bsub>CatCod F\<^esub> (F ## k) = id\<^bsub>CatCod F\<^esub> (cod\<^bsub>CatCod F\<^esub> (F ## k))" 
      proof-
        have      "(F ## (Cinv\<^bsub>CatDom F\<^esub> k)) ;;\<^bsub>CatCod F\<^esub> (F ## k) = F ## ((Cinv\<^bsub>CatDom F\<^esub> k) ;;\<^bsub>CatDom F\<^esub>  k)" using assms
          by(auto simp add: FunctorComp Category.InvCompIso)
        also have "... = F ## (id\<^bsub>CatDom F\<^esub> (cod\<^bsub>CatDom F\<^esub> k))" using assms by (simp add: Category.IsoInvId1)
        also have "... = id\<^bsub>CatCod F\<^esub> (cod\<^bsub>CatCod F\<^esub> (F ## k))" using assms by (simp add: FunctorId3Cod) 
        finally show ?thesis by simp
      qed   
    qed
  thus ?thesis by(auto simp add: isomorphism_def)
qed

declare PreFunctor.CatDom[simp] PreFunctor.CatCod [simp]

lemma FunctorMFunctor[simp]: "Functor F \<Longrightarrow> FunctorM F"
by (simp add: Functor_def)

locale Equivalence = Functor +
  assumes Full: "\<lbrakk>A \<in> Obj (CatDom F) ; B \<in> Obj (CatDom F) ; 
                  h maps\<^bsub>CatCod F\<^esub> (F @@ A) to (F @@ B)\<rbrakk> \<Longrightarrow>
                 \<exists> f . (f maps\<^bsub>CatDom F\<^esub> A to B) \<and> (F ## f = h)"
  and Faithful: "\<lbrakk>f maps\<^bsub>CatDom F\<^esub> A to B ; g maps\<^bsub>CatDom F\<^esub> A to B ; F ## f = F ## g\<rbrakk> \<Longrightarrow> f = g"
  and IsoDense: "C \<in> Obj (CatCod F) \<Longrightarrow> \<exists> A \<in> Obj (CatDom F) . ObjIso (CatCod F) (F @@ A) C"

end
