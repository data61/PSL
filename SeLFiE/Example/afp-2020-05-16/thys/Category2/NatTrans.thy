(*
Author: Alexander Katovsky
*)

section "Natural Transformation"

theory NatTrans
imports Functors
begin

record ('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans = 
  NTDom :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) Functor" 
  NTCod :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) Functor" 
  NatTransMap :: "'o1 \<Rightarrow> 'm2"

abbreviation
  NatTransApp :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans \<Rightarrow> 'o1 \<Rightarrow> 'm2" (infixr "$$" 70) where
  "NatTransApp \<eta> X \<equiv> (NatTransMap \<eta>) X"

definition  "NTCatDom \<eta> \<equiv> CatDom (NTDom \<eta>)"
definition  "NTCatCod \<eta> \<equiv> CatCod (NTCod \<eta>)"

locale NatTransExt = 
  fixes \<eta> :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans" (structure)
  assumes  NTExt : "NatTransMap \<eta> \<in> extensional (Obj (NTCatDom \<eta>))"

locale NatTransP = 
  fixes \<eta> :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans" (structure)
  assumes NatTransFtor:   "Functor (NTDom \<eta>)"
  and     NatTransFtor2:  "Functor (NTCod \<eta>)"
  and     NatTransFtorDom:   "NTCatDom \<eta> = CatDom (NTCod \<eta>)"
  and     NatTransFtorCod:   "NTCatCod \<eta> = CatCod (NTDom \<eta>)"
  and    NatTransMapsTo:  "X \<in> obj\<^bsub>NTCatDom \<eta>\<^esub> \<Longrightarrow> 
                           (\<eta> $$ X) maps\<^bsub>NTCatCod \<eta>\<^esub> ((NTDom \<eta>) @@ X) to ((NTCod \<eta>) @@ X)"
  and    NatTrans:  "f maps\<^bsub>NTCatDom \<eta>\<^esub> X to Y \<Longrightarrow> 
                     ((NTDom \<eta>) ## f) ;;\<^bsub>NTCatCod \<eta>\<^esub> (\<eta> $$ Y) = (\<eta> $$ X) ;;\<^bsub>NTCatCod \<eta>\<^esub> ((NTCod \<eta>) ## f)"

locale NatTrans = NatTransP + NatTransExt

lemma [simp]: "NatTrans \<eta> \<Longrightarrow> NatTransP \<eta>"
by(simp add: NatTrans_def)

definition MakeNT :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans \<Rightarrow> ('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans" where
"MakeNT \<eta> \<equiv> \<lparr>
      NTDom = NTDom \<eta> , 
      NTCod = NTCod \<eta> , 
      NatTransMap = restrict (NatTransMap \<eta>) (Obj (NTCatDom \<eta>))
  \<rparr>"

definition 
  nt_abbrev ("NT _ : _ \<Longrightarrow> _" [81]) where
  "NT f : F \<Longrightarrow> G \<equiv> (NatTrans f) \<and> (NTDom f = F) \<and> (NTCod f = G)"

lemma nt_abbrevE[elim]: "\<lbrakk>NT f : F \<Longrightarrow> G ; \<lbrakk>(NatTrans f) ; (NTDom f = F) ; (NTCod f = G)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (auto simp add: nt_abbrev_def)

lemma MakeNT: "NatTransP \<eta> \<Longrightarrow> NatTrans (MakeNT \<eta>)"
  by(auto simp add: NatTransP_def NatTrans_def MakeNT_def NTCatDom_def NTCatCod_def Category.MapsToObj
    NatTransExt_def)

lemma MakeNT_comp: "X \<in> Obj (NTCatDom f) \<Longrightarrow> (MakeNT f) $$ X = f $$ X"
by (simp add: MakeNT_def)

lemma MakeNT_dom: "NTCatDom f = NTCatDom (MakeNT f)"
by (simp add: NTCatDom_def MakeNT_def)

lemma MakeNT_cod: "NTCatCod f = NTCatCod (MakeNT f)"
by (simp add: NTCatCod_def MakeNT_def)

lemma MakeNTApp: "X \<in> Obj (NTCatDom (MakeNT f)) \<Longrightarrow> f $$ X = (MakeNT f) $$ X"
by(simp add: MakeNT_def NTCatDom_def)

lemma NatTransMapsTo:
  assumes "NT \<eta> : F \<Longrightarrow> G" and "X \<in> Obj (CatDom F)" 
  shows "\<eta> $$ X maps\<^bsub>CatCod G \<^esub>(F @@ X) to (G @@ X)"
proof-
  have NTP: "NatTransP \<eta>" using assms by auto
  have NTC: "NTCatCod \<eta> = CatCod G" using assms by (auto simp add: NTCatCod_def)
  have NTD: "NTCatDom \<eta> = CatDom F" using assms by (auto simp add: NTCatDom_def)
  hence Obj: "X \<in> Obj (NTCatDom \<eta>)" using assms by simp
  have DF: "NTDom \<eta> = F" and CG: "NTCod \<eta> = G" using assms by auto
  have NTmapsTo: "\<eta> $$ X maps\<^bsub>NTCatCod \<eta> \<^esub>((NTDom \<eta>) @@ X) to ((NTCod \<eta>) @@ X)"
    using NTP Obj by (simp add: NatTransP.NatTransMapsTo)
  thus ?thesis using NTC NTD DF CG by simp
qed

definition  
   NTCompDefined :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans 
                      \<Rightarrow> ('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans \<Rightarrow> bool" (infixl "\<approx>>\<bullet>" 65) where
  "NTCompDefined \<eta>1 \<eta>2 \<equiv> NatTrans \<eta>1 \<and> NatTrans \<eta>2 \<and> NTCatDom \<eta>2 = NTCatDom \<eta>1 \<and> 
                         NTCatCod \<eta>2 = NTCatCod \<eta>1 \<and> NTCod \<eta>1 = NTDom \<eta>2"

lemma NTCompDefinedE[elim]: "\<lbrakk>\<eta>1 \<approx>>\<bullet> \<eta>2 ; \<lbrakk>NatTrans \<eta>1 ; NatTrans \<eta>2 ; NTCatDom \<eta>2 = NTCatDom \<eta>1 ; 
                         NTCatCod \<eta>2 = NTCatCod \<eta>1 ; NTCod \<eta>1 = NTDom \<eta>2\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (simp add: NTCompDefined_def)

lemma NTCompDefinedI: "\<lbrakk>NatTrans \<eta>1 ; NatTrans \<eta>2 ; NTCatDom \<eta>2 = NTCatDom \<eta>1 ; 
                         NTCatCod \<eta>2 = NTCatCod \<eta>1 ; NTCod \<eta>1 = NTDom \<eta>2\<rbrakk> \<Longrightarrow> \<eta>1 \<approx>>\<bullet> \<eta>2"
by (simp add: NTCompDefined_def)

lemma NatTransExt0:
  assumes "NTDom \<eta>1 = NTDom \<eta>2" and "NTCod \<eta>1 = NTCod \<eta>2"
  and     "\<And>X . X \<in> Obj (NTCatDom \<eta>1) \<Longrightarrow> \<eta>1 $$ X = \<eta>2 $$ X"
  and     "NatTransMap \<eta>1 \<in> extensional (Obj (NTCatDom \<eta>1))"
  and     "NatTransMap \<eta>2 \<in> extensional (Obj (NTCatDom \<eta>2))"
  shows   "\<eta>1 = \<eta>2"
proof-
  have "NatTransMap \<eta>1 = NatTransMap \<eta>2"
  proof(rule extensionalityI [of "NatTransMap \<eta>1" "Obj (NTCatDom \<eta>1)"])
    show "NatTransMap \<eta>1 \<in> extensional (Obj (NTCatDom \<eta>1))" using assms by simp
    have "NTCatDom \<eta>1 = NTCatDom \<eta>2" using assms by (simp add: NTCatDom_def)
    moreover have "NatTransMap \<eta>2 \<in> extensional (Obj (NTCatDom \<eta>2))" using assms by simp
    ultimately show "NatTransMap \<eta>2 \<in> extensional (Obj (NTCatDom \<eta>1))" by simp
    {fix X assume "X \<in> Obj (NTCatDom \<eta>1)" thus "\<eta>1 $$ X = \<eta>2 $$ X" using assms by simp}
  qed
  thus ?thesis using assms by (simp)
qed

lemma NatTransExt':
  assumes "NTDom \<eta>1' = NTDom \<eta>2'" and "NTCod \<eta>1' = NTCod \<eta>2'"
  and     "\<And>X . X \<in> Obj (NTCatDom \<eta>1') \<Longrightarrow> \<eta>1' $$ X = \<eta>2' $$ X"
  shows   "MakeNT \<eta>1' = MakeNT \<eta>2'"
proof(rule NatTransExt0)
  show "NatTransMap (MakeNT \<eta>1') \<in> extensional (Obj (NTCatDom (MakeNT \<eta>1')))" and
    "NatTransMap (MakeNT \<eta>2') \<in> extensional (Obj (NTCatDom (MakeNT \<eta>2')))" using assms
    by(simp add: MakeNT_def NTCatDom_def NTCatCod_def NatTransExt_def)+
  show "NTDom (MakeNT \<eta>1') = NTDom (MakeNT \<eta>2')" and 
    "NTCod (MakeNT \<eta>1') = NTCod (MakeNT \<eta>2')" using assms by (simp add: MakeNT_def)+
  {
    fix X assume 1: "X \<in> Obj (NTCatDom (MakeNT \<eta>1'))" 
    show "(MakeNT \<eta>1') $$ X = (MakeNT \<eta>2') $$ X"
    proof-
      have "NTCatDom (MakeNT \<eta>1') = NTCatDom (MakeNT \<eta>2')" using assms by(simp add: NTCatDom_def MakeNT_def)
      hence 2: "X \<in> Obj (NTCatDom (MakeNT \<eta>2'))" using 1 by simp 
      have "(NTCatDom \<eta>1') = (NTCatDom (MakeNT \<eta>1'))" by (rule MakeNT_dom)
      hence "X \<in> Obj (NTCatDom \<eta>1')" using 1 assms by simp 
      hence "\<eta>1' $$ X = \<eta>2' $$ X" using assms by simp
      moreover have "\<eta>1' $$ X = (MakeNT \<eta>1') $$ X" using 1 assms by (simp add: MakeNTApp)
      moreover have "\<eta>2' $$ X = (MakeNT \<eta>2') $$ X" using 2 assms by (simp add: MakeNTApp)
      ultimately have "(MakeNT \<eta>1') $$ X = (MakeNT \<eta>2') $$ X" by simp
      thus ?thesis using assms by simp
    qed
  }
qed

lemma NatTransExt:
  assumes "NatTrans \<eta>1" and "NatTrans \<eta>2" and "NTDom \<eta>1 = NTDom \<eta>2" and "NTCod \<eta>1 = NTCod \<eta>2"
  and     "\<And>X . X \<in> Obj (NTCatDom \<eta>1) \<Longrightarrow> \<eta>1 $$ X = \<eta>2 $$ X"
  shows   "\<eta>1 = \<eta>2"
proof-
  have "NatTransMap \<eta>1 \<in> extensional (Obj (NTCatDom \<eta>1))" and
       "NatTransMap \<eta>2 \<in> extensional (Obj (NTCatDom \<eta>2))" using assms
  by(simp only: NatTransExt_def NatTrans_def)+
  thus ?thesis using assms by (simp add: NatTransExt0)
qed

definition
  IdNatTrans' :: "('o1, 'o2, 'm1, 'm2, 'a1, 'a2) Functor \<Rightarrow> ('o1, 'o2, 'm1, 'm2, 'a1, 'a2) NatTrans" where
  "IdNatTrans' F \<equiv> \<lparr>
      NTDom = F , 
      NTCod = F , 
      NatTransMap = \<lambda> X . id\<^bsub>CatCod F\<^esub> (F @@ X)
  \<rparr>"

definition "IdNatTrans F \<equiv> MakeNT(IdNatTrans' F)"

lemma IdNatTrans_map: "X \<in> obj\<^bsub>CatDom F\<^esub> \<Longrightarrow> (IdNatTrans F) $$ X = id\<^bsub>CatCod F\<^esub> (F @@ X)"
by(auto simp add: IdNatTrans_def IdNatTrans'_def MakeNT_comp MakeNT_def NTCatDom_def)

lemmas IdNatTrans_defs = IdNatTrans_def IdNatTrans'_def MakeNT_def IdNatTrans_map NTCatCod_def NTCatDom_def

lemma IdNatTransNatTrans': "Functor F \<Longrightarrow> NatTransP(IdNatTrans' F)"
proof(auto simp add:NatTransP_def IdNatTrans'_def NTCatDom_def NTCatCod_def Category.Simps 
        PreFunctor.FunctorId2 functor_simps Functor.FunctorMapsTo)
  {
    fix f X Y
    assume a: "Functor F" and b: "f maps\<^bsub>CatDom F\<^esub> X to Y"
    show "(F ## f) ;;\<^bsub>CatCod F\<^esub> (id\<^bsub>CatCod F\<^esub> (F @@ Y)) = (id\<^bsub>CatCod F\<^esub> (F @@ X)) ;;\<^bsub>CatCod F\<^esub> (F ## f)"
    proof-
      have 1: "Category (CatCod F)" using a by simp
      have "F ## f maps\<^bsub>CatCod F\<^esub> (F @@ X) to (F @@ Y)" using a b by (auto simp add: Functor.FunctorMapsTo)
      hence 2: "F ## f \<in> mor\<^bsub>CatCod F\<^esub>" and 3: "cod\<^bsub>CatCod F\<^esub> (F ## f) = (F @@ Y)" 
        and 4: "dom\<^bsub>CatCod F\<^esub> (F ## f) = (F @@ X)" by auto
      have "(F ## f) ;;\<^bsub>CatCod F\<^esub> (id\<^bsub>CatCod F\<^esub> (F @@ Y)) = (F ## f) ;;\<^bsub>CatCod F\<^esub> (id\<^bsub>CatCod F\<^esub> (cod\<^bsub>CatCod F\<^esub> (F ## f)))"
        using 3 by simp
      also have "... = F ## f" using 1 2 by (auto simp add: Category.Cidr)
      also have "... = (id\<^bsub>CatCod F\<^esub> (dom\<^bsub>CatCod F\<^esub> (F ## f))) ;;\<^bsub>CatCod F\<^esub> (F ## f)" 
        using 1 2 by (auto simp add: Category.Cidl)
      also have "... = (id\<^bsub>CatCod F\<^esub> (F @@ X)) ;;\<^bsub>CatCod F\<^esub> (F ## f)" using 4 by simp
      finally show ?thesis .
    qed
  }
qed

lemma IdNatTransNatTrans: "Functor F \<Longrightarrow> NatTrans (IdNatTrans F)"
by (simp add: IdNatTransNatTrans' IdNatTrans_def MakeNT)

definition
  NatTransComp' :: "('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans \<Rightarrow>
                   ('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans \<Rightarrow>
                   ('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans" (infixl "\<bullet>1" 75) where
  "NatTransComp' \<eta>1 \<eta>2 = \<lparr>
      NTDom = NTDom \<eta>1 , 
      NTCod = NTCod \<eta>2 , 
      NatTransMap = \<lambda> X . (\<eta>1 $$ X) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ X)
  \<rparr>"


definition NatTransComp (infixl "\<bullet>" 75) where "\<eta>1 \<bullet> \<eta>2 \<equiv> MakeNT(\<eta>1 \<bullet>1 \<eta>2)"

lemma NatTransComp_Comp1: "\<lbrakk>x \<in> Obj (NTCatDom f) ; f \<approx>>\<bullet> g\<rbrakk> \<Longrightarrow> (f \<bullet> g) $$ x = (f $$ x) ;;\<^bsub>NTCatCod g\<^esub> (g $$ x)"
by(auto simp add: NatTransComp_def NatTransComp'_def MakeNT_def NTCatCod_def NTCatDom_def)

lemma NatTransComp_Comp2: "\<lbrakk>x \<in> Obj (NTCatDom f) ; f \<approx>>\<bullet> g\<rbrakk> \<Longrightarrow> (f \<bullet> g) $$ x = (f $$ x) ;;\<^bsub>NTCatCod f\<^esub> (g $$ x)"
by(auto simp add: NatTransComp_def NatTransComp'_def MakeNT_def NTCatCod_def NTCatDom_def)

lemmas NatTransComp_defs = NatTransComp_def NatTransComp'_def MakeNT_def 
  NatTransComp_Comp1  NTCatCod_def NTCatDom_def

lemma [simp]: "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NatTrans \<eta>1" by auto
lemma [simp]: "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NatTrans \<eta>2" by auto
lemma NTCatDom:        "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NTCatDom \<eta>1 = NTCatDom \<eta>2" by auto
lemma NTCatCod:        "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NTCatCod \<eta>1 = NTCatCod \<eta>2" by auto
lemma [simp]: "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NTCatDom (\<eta>1 \<bullet>1 \<eta>2) = NTCatDom \<eta>1" by (auto simp add: NatTransComp'_def NTCatDom_def)
lemma [simp]: "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NTCatCod (\<eta>1 \<bullet>1 \<eta>2) = NTCatCod \<eta>1" by (auto simp add: NatTransComp'_def NTCatCod_def)
lemma [simp]: "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NTCatDom (\<eta>1 \<bullet> \<eta>2) = NTCatDom \<eta>1" by (auto simp add: NatTransComp_defs)
lemma [simp]: "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NTCatCod (\<eta>1 \<bullet> \<eta>2) = NTCatCod \<eta>1" by (auto simp add: NatTransComp_defs)
lemma [simp]: "NatTrans \<eta> \<Longrightarrow> Category(NTCatDom \<eta>)" by (simp add:  NatTransP.NatTransFtor NTCatDom_def)
lemma [simp]: "NatTrans \<eta> \<Longrightarrow> Category(NTCatCod \<eta>)" by (simp add:  NatTransP.NatTransFtor2 NTCatCod_def)
lemma DDDC: assumes "NatTrans f" shows "CatDom (NTDom f) = CatDom (NTCod f)" 
proof-
  have "CatDom (NTDom f) = NTCatDom f" by (simp add: NTCatDom_def)
  thus ?thesis using assms by (simp add: NatTransP.NatTransFtorDom)
qed
lemma CCCD: assumes "NatTrans f" shows "CatCod (NTCod f) = CatCod (NTDom f)" 
proof-
  have "CatCod (NTCod f) = NTCatCod f" by (simp add: NTCatCod_def)
  thus ?thesis using assms by (simp add: NatTransP.NatTransFtorCod)
qed

lemma IdNatTransCompDefDom: "NatTrans f \<Longrightarrow> (IdNatTrans (NTDom f)) \<approx>>\<bullet> f"
apply(rule NTCompDefinedI)
apply(simp_all add: IdNatTransNatTrans NatTransP.NatTransFtor)
apply(simp_all add: IdNatTrans_defs CCCD)
done

lemma IdNatTransCompDefCod: "NatTrans f \<Longrightarrow> f \<approx>>\<bullet> (IdNatTrans (NTCod f))"
apply(rule NTCompDefinedI)
apply(simp_all add: IdNatTransNatTrans NatTransP.NatTransFtor2)
apply(simp_all add: IdNatTrans_defs DDDC)
done

lemma NatTransCompDefCod:
  assumes "NatTrans \<eta>" and "f maps\<^bsub>NTCatDom \<eta>\<^esub> X to Y"
  shows "(\<eta> $$ X) \<approx>>\<^bsub>NTCatCod \<eta>\<^esub> (NTCod \<eta> ## f)"
proof(rule CompDefinedI)
  have b: "X \<in> obj\<^bsub>NTCatDom \<eta>\<^esub>" and c: "Y \<in> obj\<^bsub>NTCatDom \<eta>\<^esub>" using assms by (auto simp add: Category.MapsToObj)
  have d: "(\<eta> $$ X) maps\<^bsub>NTCatCod \<eta>\<^esub> ((NTDom \<eta>) @@ X) to ((NTCod \<eta>) @@ X)" using assms b 
    by (simp add: NatTransP.NatTransMapsTo)
  thus "\<eta> $$ X \<in> mor\<^bsub>NTCatCod \<eta>\<^esub>" by auto
  have "f maps\<^bsub>CatDom (NTCod \<eta>)\<^esub> X to Y" using assms by (simp add: NatTransP.NatTransFtorDom)
  hence e: "NTCod \<eta> ## f maps\<^bsub>CatCod (NTCod \<eta>)\<^esub> (NTCod \<eta> @@ X) to (NTCod \<eta> @@ Y)" using assms
    by (simp add: FunctorM.FunctorCompM NatTransP.NatTransFtor2)
  thus "NTCod \<eta> ## f \<in> mor\<^bsub>NTCatCod \<eta>\<^esub>" by (auto simp add: NTCatCod_def)
  have "cod\<^bsub>NTCatCod \<eta>\<^esub> (\<eta> $$ X) = (NTCod \<eta> @@ X)" using d by auto
  also have "... = dom\<^bsub>CatCod (NTCod \<eta>)\<^esub> (NTCod \<eta> ## f)" using e by auto
  finally show "cod\<^bsub>NTCatCod \<eta>\<^esub> (\<eta> $$ X) = dom\<^bsub>NTCatCod \<eta>\<^esub> (NTCod \<eta> ## f)" by (auto simp add: NTCatCod_def)
qed

lemma NatTransCompDefDom:
  assumes "NatTrans \<eta>" and "f maps\<^bsub>NTCatDom \<eta>\<^esub> X to Y"
  shows "(NTDom \<eta> ## f)  \<approx>>\<^bsub>NTCatCod \<eta>\<^esub> (\<eta> $$ Y)"
proof(rule CompDefinedI)
  have b: "X \<in> obj\<^bsub>NTCatDom \<eta>\<^esub>" and c: "Y \<in> obj\<^bsub>NTCatDom \<eta>\<^esub>" using assms by (auto simp add: Category.MapsToObj)
  have d: "(\<eta> $$ Y) maps\<^bsub>NTCatCod \<eta>\<^esub> ((NTDom \<eta>) @@ Y) to ((NTCod \<eta>) @@ Y)" using assms c
    by (simp add: NatTransP.NatTransMapsTo)
  thus "\<eta> $$ Y \<in> mor\<^bsub>NTCatCod \<eta>\<^esub>" by auto
  have "f maps\<^bsub>CatDom (NTDom \<eta>)\<^esub> X to Y" using assms by (simp add: NTCatDom_def)
  hence e: "NTDom \<eta> ## f maps\<^bsub>CatCod (NTDom \<eta>)\<^esub> (NTDom \<eta> @@ X) to (NTDom \<eta> @@ Y)" using assms
    by (simp add: FunctorM.FunctorCompM NatTransP.NatTransFtor)
  thus "NTDom \<eta> ## f \<in> mor\<^bsub>NTCatCod \<eta>\<^esub>" using assms by (auto simp add: NatTransP.NatTransFtorCod) 
  have "dom\<^bsub>NTCatCod \<eta>\<^esub> (\<eta> $$ Y) = (NTDom \<eta> @@ Y)" using d by auto
  also have "... = cod\<^bsub>CatCod (NTDom \<eta>)\<^esub> (NTDom \<eta> ## f)" using e by auto
  finally show "cod\<^bsub>NTCatCod \<eta>\<^esub> (NTDom \<eta> ## f) = dom\<^bsub>NTCatCod \<eta>\<^esub> (\<eta> $$ Y)" 
    using assms by (auto simp add: NatTransP.NatTransFtorCod)
qed

lemma NatTransCompCompDef:
  assumes "\<eta>1 \<approx>>\<bullet> \<eta>2" and "X \<in> obj\<^bsub>NTCatDom \<eta>1\<^esub>"
  shows "(\<eta>1 $$ X) \<approx>>\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ X)"
proof(rule CompDefinedI)
  have 1: "(\<eta>1 $$ X) maps\<^bsub>NTCatCod \<eta>1\<^esub> ((NTDom \<eta>1) @@ X) to ((NTCod \<eta>1) @@ X)" using assms
    by (simp add: NatTransP.NatTransMapsTo)
  have "NTCatCod \<eta>1 = NTCatCod \<eta>2" using assms by auto
  hence 2: "(\<eta>2 $$ X) maps\<^bsub>NTCatCod \<eta>1\<^esub> ((NTDom \<eta>2) @@ X) to ((NTCod \<eta>2) @@ X)" using assms
    by (simp add: NatTransP.NatTransMapsTo NTCatDom)
  show "\<eta>1 $$ X \<in> mor\<^bsub>NTCatCod \<eta>1\<^esub>" 
    and "\<eta>2 $$ X \<in> mor\<^bsub>NTCatCod \<eta>1\<^esub>"  using 1 2 by auto
  have "cod\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>1 $$ X) = ((NTCod \<eta>1) @@ X)" using 1 by auto
  also have "... = ((NTDom \<eta>2) @@ X)" using assms by auto
  finally show "cod\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>1 $$ X) = dom\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ X)" using 2 by auto
qed
 
lemma NatTransCompNatTrans': 
  assumes "\<eta>1 \<approx>>\<bullet> \<eta>2"
  shows   "NatTransP (\<eta>1 \<bullet>1 \<eta>2)"
proof(auto simp add: NatTransP_def)
  show "Functor (NTDom (\<eta>1 \<bullet>1 \<eta>2))" and "Functor (NTCod (\<eta>1 \<bullet>1 \<eta>2))" using assms
    by (auto simp add: NatTransComp'_def NatTransP.NatTransFtor NatTransP.NatTransFtor2)
  show "NTCatDom (\<eta>1 \<bullet>1 \<eta>2) = CatDom (NTCod (\<eta>1 \<bullet>1 \<eta>2))" and
       "NTCatCod (\<eta>1 \<bullet>1 \<eta>2) = CatCod (NTDom (\<eta>1 \<bullet>1 \<eta>2))"
  proof (auto simp add: NatTransComp'_def NTCatCod_def NTCatDom_def)
    have "CatDom (NTDom \<eta>1) = NTCatDom \<eta>1" by (simp add: NTCatDom_def)
    thus "CatDom (NTDom \<eta>1) = CatDom (NTCod \<eta>2)" using assms by (auto simp add: NatTransP.NatTransFtorDom)
    have "CatCod (NTCod \<eta>2) = NTCatCod \<eta>2" by (simp add: NTCatCod_def)
    thus "CatCod (NTCod \<eta>2) = CatCod (NTDom \<eta>1)" using assms by (auto simp add: NatTransP.NatTransFtorCod)
  qed
  {
    fix X assume aa: "X \<in> obj\<^bsub>NTCatDom (\<eta>1 \<bullet>1 \<eta>2)\<^esub>"
    show "(\<eta>1 \<bullet>1 \<eta>2) $$ X maps\<^bsub>NTCatCod (\<eta>1 \<bullet>1 \<eta>2)\<^esub> NTDom (\<eta>1 \<bullet>1 \<eta>2) @@ X to NTCod (\<eta>1 \<bullet>1 \<eta>2) @@ X"
    proof-
      have "X \<in> obj\<^bsub>NTCatDom \<eta>1\<^esub>" and "NatTrans \<eta>1" using assms aa by simp+
      hence "(\<eta>1 $$ X) maps\<^bsub>NTCatCod \<eta>1\<^esub> ((NTDom \<eta>1) @@ X) to ((NTCod \<eta>1) @@ X)" 
        by (simp add: NatTransP.NatTransMapsTo)
      moreover have "(\<eta>2 $$ X) maps\<^bsub>NTCatCod \<eta>1\<^esub> ((NTCod \<eta>1) @@ X) to ((NTCod \<eta>2) @@ X)" 
      proof-
        have "X \<in> obj\<^bsub>NTCatDom \<eta>2\<^esub>" and "NatTrans \<eta>2" using assms aa by auto
        hence "(\<eta>2 $$ X) maps\<^bsub>NTCatCod \<eta>2\<^esub> ((NTDom \<eta>2) @@ X) to ((NTCod \<eta>2) @@ X)" 
          by (simp add: NatTransP.NatTransMapsTo)
        thus ?thesis using assms by auto
      qed
      ultimately have "(\<eta>1 $$ X) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ X) maps\<^bsub>NTCatCod \<eta>1\<^esub> ((NTDom \<eta>1) @@ X) to ((NTCod \<eta>2) @@ X)"
        using assms by (simp add: Category.Ccompt)
      thus ?thesis using assms by (auto simp add: NatTransComp'_def NTCatCod_def)
    qed
  }
  {
    fix f X Y assume a: "f maps\<^bsub>(NTCatDom (\<eta>1 \<bullet>1 \<eta>2))\<^esub> X to Y"
    show "(NTDom (\<eta>1 \<bullet>1 \<eta>2) ## f) ;;\<^bsub>NTCatCod (\<eta>1 \<bullet>1 \<eta>2)\<^esub> (\<eta>1 \<bullet>1 \<eta>2 $$ Y) =
       ((\<eta>1 \<bullet>1 \<eta>2) $$ X) ;;\<^bsub>NTCatCod (\<eta>1 \<bullet>1 \<eta>2)\<^esub> (NTCod (\<eta>1 \<bullet>1 \<eta>2) ## f)"
    proof-
      have b: "X \<in> obj\<^bsub>NTCatDom \<eta>1\<^esub>" and c: "Y \<in> obj\<^bsub>NTCatDom \<eta>1\<^esub>" using assms a by (auto simp add: Category.MapsToObj)
      have "((NTDom \<eta>1) ## f) ;;\<^bsub>NTCatCod \<eta>1\<^esub> ((\<eta>1 $$ Y) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ Y)) = 
            (((NTDom \<eta>1) ## f) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>1 $$ Y)) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ Y)" 
      proof-
        have "((NTDom \<eta>1) ## f) \<approx>>\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>1 $$ Y)" using assms a by (auto simp add: NatTransCompDefDom)
        moreover have "(\<eta>1 $$ Y) \<approx>>\<^bsub>NTCatCod \<eta>1\<^esub>  (\<eta>2 $$ Y)" using assms by (simp add: NatTransCompCompDef c)
        ultimately show ?thesis using assms by (simp add: Category.Cassoc)
      qed
      also have "... = ((\<eta>1 $$ X) ;;\<^bsub>NTCatCod \<eta>1\<^esub> ((NTDom \<eta>2) ## f)) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ Y)"
        using assms a by (auto simp add: NatTransP.NatTrans)
      also have "... = (\<eta>1 $$ X) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (((NTDom \<eta>2) ## f) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ Y))" 
      proof-
        have "(\<eta>1 $$ X) \<approx>>\<^bsub>NTCatCod \<eta>1\<^esub> ((NTCod \<eta>1) ## f)" using assms a by (simp add: NatTransCompDefCod)
        moreover have "((NTDom \<eta>2) ## f) \<approx>>\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ Y)" using assms a 
          by (simp add: NatTransCompDefDom NTCatDom NTCatCod)
        ultimately show ?thesis using assms by (auto simp add: Category.Cassoc)
      qed
      also have "... = (\<eta>1 $$ X) ;;\<^bsub>NTCatCod \<eta>1\<^esub> ((\<eta>2 $$ X) ;;\<^bsub>NTCatCod \<eta>1\<^esub> ((NTCod \<eta>2) ## f))" 
        using assms a by (simp add: NatTransP.NatTrans NTCatDom NTCatCod)
      also have "... = (\<eta>1 $$ X) ;;\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ X) ;;\<^bsub>NTCatCod \<eta>1\<^esub> ((NTCod \<eta>2) ## f)"
      proof-
        have "(\<eta>1 $$ X) \<approx>>\<^bsub>NTCatCod \<eta>1\<^esub> (\<eta>2 $$ X)" using assms by (simp add: NatTransCompCompDef b)
        moreover have "(\<eta>2 $$ X) \<approx>>\<^bsub>NTCatCod \<eta>1\<^esub> ((NTCod \<eta>2) ## f)" using assms a 
          by (simp add: NatTransCompDefCod NTCatCod NTCatDom)
        ultimately show ?thesis using assms by (simp add: Category.Cassoc)
      qed
      finally show ?thesis using assms by (auto simp add: NatTransComp'_def NTCatCod_def)
    qed
  }
qed

lemma NatTransCompNatTrans: "\<eta>1 \<approx>>\<bullet> \<eta>2 \<Longrightarrow> NatTrans (\<eta>1 \<bullet> \<eta>2)"
by (simp add: NatTransCompNatTrans' NatTransComp_def MakeNT)

definition
  CatExp' :: "('o1,'m1,'a) Category_scheme \<Rightarrow> ('o2,'m2,'b) Category_scheme \<Rightarrow> 
                     (('o1, 'o2, 'm1, 'm2, 'a, 'b) Functor, 
                      ('o1, 'o2, 'm1, 'm2, 'a, 'b) NatTrans) Category"  where
  "CatExp' A B \<equiv> \<lparr>
      Category.Obj = {F . Ftor F : A \<longrightarrow> B} , 
      Category.Mor = {\<eta> . NatTrans \<eta> \<and> NTCatDom \<eta> = A \<and> NTCatCod \<eta> = B} , 
      Category.Dom = NTDom , 
      Category.Cod = NTCod , 
      Category.Id  = IdNatTrans , 
      Category.Comp = \<lambda>f g. (f \<bullet> g)
  \<rparr>"

definition "CatExp A B \<equiv> MakeCat(CatExp' A B)"

lemma IdNatTransMapL: 
  assumes NT: "NatTrans f"
  shows "IdNatTrans (NTDom f) \<bullet> f = f"
proof(rule NatTransExt)
  show "NatTrans f" using assms .
  show "NatTrans (IdNatTrans (NTDom f) \<bullet> f)" using NT 
    by (simp add: NatTransP.NatTransFtor IdNatTransNatTrans IdNatTransCompDefDom NatTransCompNatTrans)
  show "NTDom (IdNatTrans (NTDom f) \<bullet> f) = NTDom f" and
    "NTCod (IdNatTrans (NTDom f) \<bullet> f) = NTCod f" by (simp add: IdNatTrans_defs NatTransComp_defs)+
  {
    fix x assume aa: "x \<in> Obj (NTCatDom (IdNatTrans (NTDom f) \<bullet> f))"
    show "(IdNatTrans (NTDom f) \<bullet> f) $$ x = f $$ x"
    proof-
      have XObj: "x \<in> Obj(NTCatDom f)" using aa by (simp add: IdNatTrans_defs NatTransComp_defs)
      have fMap: "f $$ x maps\<^bsub>NTCatCod f\<^esub> NTDom f @@ x to NTCod f @@ x" using NT XObj
        by (simp add: NatTransP.NatTransMapsTo)
      have "(IdNatTrans (NTDom f) \<bullet> f) $$ x = (IdNatTrans (NTDom f) $$ x) ;;\<^bsub>NTCatCod f \<^esub>(f $$ x)" 
      proof(rule NatTransComp_Comp1)
        show "x \<in> obj\<^bsub>NTCatDom (IdNatTrans (NTDom f))\<^esub>" using XObj by (simp add: IdNatTrans_defs)
        show "IdNatTrans (NTDom f) \<approx>>\<bullet> f" using NT by (simp add: IdNatTransCompDefDom)
      qed
      also have "... = id\<^bsub>NTCatCod f\<^esub> (dom\<^bsub>NTCatCod f\<^esub> (f $$ x)) ;;\<^bsub>NTCatCod f \<^esub>(f $$ x)" 
        using XObj NT fMap by (auto simp add: IdNatTrans_map NTCatDom_def CCCD NTCatCod_def)
      also have "... = f $$ x"  
      proof-
        have "f $$ x \<in> mor\<^bsub>NTCatCod f\<^esub>" using fMap by (auto)
        thus ?thesis using NT by (simp add: Category.Cidl)
      qed
      finally show ?thesis .
    qed
  }
qed

lemma IdNatTransMapR: 
  assumes NT: "NatTrans f"
  shows "f \<bullet> IdNatTrans (NTCod f) = f" 
proof(rule NatTransExt)
  show "NatTrans f" using assms .
  show "NatTrans (f \<bullet> IdNatTrans (NTCod f))" using NT 
    by (simp add: NatTransP.NatTransFtor IdNatTransNatTrans IdNatTransCompDefCod NatTransCompNatTrans)
  show "NTDom (f \<bullet> IdNatTrans (NTCod f)) = NTDom f" and
    "NTCod (f \<bullet> IdNatTrans (NTCod f)) = NTCod f" by (simp add: IdNatTrans_defs NatTransComp_defs)+
  {
    fix x assume aa: "x \<in> Obj (NTCatDom (f \<bullet> IdNatTrans (NTCod f)))"
    show "(f \<bullet> IdNatTrans (NTCod f)) $$ x = f $$ x" 
    proof-
      have XObj: "x \<in> Obj(NTCatDom f)" using aa by (simp add:  NatTransComp_defs)
      have fMap: "f $$ x maps\<^bsub>NTCatCod f\<^esub> NTDom f @@ x to NTCod f @@ x" using NT XObj
        by (simp add: NatTransP.NatTransMapsTo)
      have "(f \<bullet> IdNatTrans (NTCod f)) $$ x = (f $$ x) ;;\<^bsub>NTCatCod f\<^esub> (IdNatTrans (NTCod f) $$ x)"
        using XObj NT by (auto simp add: NatTransComp_Comp2 IdNatTransCompDefCod)
      also have "... = (f $$ x) ;;\<^bsub>NTCatCod f\<^esub> (id\<^bsub>NTCatCod f\<^esub> (cod\<^bsub>NTCatCod f\<^esub> (f $$ x)))"
      proof-
        have "x \<in> obj\<^bsub>CatDom (NTCod f)\<^esub>" using XObj NT by (simp add: IdNatTrans_defs DDDC)
        moreover have "(cod\<^bsub>NTCatCod f\<^esub> (f $$ x)) = (NTCod f) @@ x" using fMap by auto
        ultimately have "(IdNatTrans (NTCod f) $$ x) = (id\<^bsub>NTCatCod f\<^esub> (cod\<^bsub>NTCatCod f\<^esub> (f $$ x)))" 
          by (simp add: IdNatTrans_map NTCatCod_def)
        thus ?thesis by simp
      qed
      also have "... = f $$ x" 
      proof-
        have "f $$ x \<in> mor\<^bsub>NTCatCod f\<^esub>" using fMap by (auto)
        thus ?thesis using NT by (simp add: Category.Cidr)
      qed
      finally show ?thesis .
    qed
  }
qed

lemma NatTransCompDefined:
  assumes "f \<approx>>\<bullet> g" and "g \<approx>>\<bullet> h" 
  shows "(f \<bullet> g) \<approx>>\<bullet> h" and "f \<approx>>\<bullet> (g \<bullet> h)"
proof-
  show "(f \<bullet> g) \<approx>>\<bullet> h"
  proof(rule NTCompDefinedI)
    show "NatTrans (f \<bullet> g)" and "NatTrans h" using assms by (auto simp add: NatTransCompNatTrans)
    have "NTCatDom f = NTCatDom h" using assms by (simp add: NTCatDom)
    thus "NTCatDom h = NTCatDom (f \<bullet> g)" by (simp add: NatTransComp_defs)
    have "NTCatCod h = NTCatCod g" using assms by (simp add: NTCatCod)
    thus "NTCatCod h = NTCatCod (f \<bullet> g)" by ( simp add: NatTransComp_defs)
    show "NTCod (f \<bullet> g) = NTDom h" using assms by (auto simp add: NatTransComp_defs)
  qed
  show "f \<approx>>\<bullet> (g \<bullet> h)"
  proof(rule NTCompDefinedI)
    show "NatTrans f" and "NatTrans (g \<bullet> h)" using assms by (auto simp add: NatTransCompNatTrans)
    have "NTCatDom f = NTCatDom g" using assms by (simp add: NTCatDom)
    thus "NTCatDom (g \<bullet> h) = NTCatDom f" by (simp add: NatTransComp_defs)
    have "NTCatCod h = NTCatCod f" using assms by (simp add: NTCatCod)
    thus "NTCatCod (g \<bullet> h) = NTCatCod f" by ( simp add: NatTransComp_defs)
    show "NTCod f = NTDom (g \<bullet> h)" using assms by (auto simp add: NatTransComp_defs)
  qed
qed

lemma NatTransCompAssoc:
  assumes "f \<approx>>\<bullet> g" and "g \<approx>>\<bullet> h" 
  shows "(f \<bullet> g) \<bullet> h = f \<bullet> (g \<bullet> h)"
proof(rule NatTransExt)
  show "NatTrans ((f \<bullet> g) \<bullet> h)" using assms by (simp add: NatTransCompNatTrans NatTransCompDefined)
  show "NatTrans (f \<bullet> (g \<bullet> h))" using assms by (simp add: NatTransCompNatTrans NatTransCompDefined)
  show "NTDom (f \<bullet> g \<bullet> h) = NTDom (f \<bullet> (g \<bullet> h))" and "NTCod (f \<bullet> g \<bullet> h) = NTCod (f \<bullet> (g \<bullet> h))"
    by(simp add: NatTransComp_defs)+
  {
    fix x assume aa: "x \<in> obj\<^bsub>NTCatDom (f \<bullet> g \<bullet> h)\<^esub>" show "((f \<bullet> g) \<bullet> h) $$ x = (f \<bullet> (g \<bullet> h)) $$ x"
    proof-
      have ntd1: "NTCatDom (f \<bullet> g) = NTCatDom (f \<bullet> g \<bullet> h)" and ntd2: "NTCatDom f = NTCatDom (f \<bullet> g \<bullet> h)" 
        using assms by (simp add: NatTransCompDefined)+
      have obj1: "x \<in> Obj (NTCatDom f)" using aa ntd2 by simp
      have  1: "(f \<bullet> g) $$ x = (f $$ x) ;;\<^bsub>NTCatCod h\<^esub> (g $$ x)" and 
            2: "(g \<bullet> h) $$ x = (g $$ x) ;;\<^bsub>NTCatCod h\<^esub> (h $$ x)" using obj1
        using assms by (auto simp add: NatTransComp_Comp1)
      have "((f \<bullet> g) \<bullet> h) $$ x = ((f \<bullet> g) $$ x) ;;\<^bsub>NTCatCod h\<^esub> (h $$ x)"
      proof(rule NatTransComp_Comp1)
        show "x \<in> obj\<^bsub>NTCatDom (f \<bullet> g)\<^esub>" using aa ntd1 by simp
        show "f \<bullet> g \<approx>>\<bullet> h" using assms by (simp add: NatTransCompDefined)
      qed
      also have "... = ((f $$ x) ;;\<^bsub>NTCatCod h\<^esub> (g $$ x)) ;;\<^bsub>NTCatCod h\<^esub> (h $$ x)" using 1 by simp
      also have "... = (f $$ x) ;;\<^bsub>NTCatCod h\<^esub> ((g $$ x) ;;\<^bsub>NTCatCod h\<^esub> (h $$ x))" 
      proof-
        have 1: "NTCatCod h = NTCatCod f" and 2: "NTCatCod h = NTCatCod g" using assms by (simp add: NTCatCod)+
        hence "(f $$ x) \<approx>>\<^bsub>NTCatCod h\<^esub> (g $$ x)" using obj1 assms by (simp add: NatTransCompCompDef) 
        moreover have "(g $$ x) \<approx>>\<^bsub>NTCatCod h\<^esub> (h $$ x)" using obj1 assms 2 by (simp add: NatTransCompCompDef NTCatDom)
        moreover have "Category (NTCatCod h)" using assms by auto
        ultimately show ?thesis by (simp add: Category.Cassoc)
      qed
      also have "... = (f $$ x) ;;\<^bsub>NTCatCod h\<^esub> ((g \<bullet> h) $$ x)" using 2 by simp
      also have "... = (f \<bullet> (g \<bullet> h)) $$ x"
      proof-
        have "NTCatCod f = NTCatCod h" using assms by (simp add: NTCatCod)
        moreover have "(f \<bullet> (g \<bullet> h)) $$ x = (f $$ x) ;;\<^bsub>NTCatCod f\<^esub> ((g \<bullet> h) $$ x)"
        proof(rule NatTransComp_Comp2)
          show "x \<in> obj\<^bsub>NTCatDom f\<^esub>" using obj1 assms by (simp add: NTCatDom)
          show "f \<approx>>\<bullet> g \<bullet> h" using assms by (simp add: NatTransCompDefined)
        qed
        ultimately show ?thesis by simp
      qed
      finally show ?thesis .
    qed
  }
qed

lemma CatExpCatAx: 
  assumes "Category A" and "Category B"
  shows "Category_axioms (CatExp' A B)"
proof(auto simp add: Category_axioms_def)
  {
    fix f assume "f \<in> mor\<^bsub>CatExp' A B\<^esub>" 
    thus "dom\<^bsub>CatExp' A B\<^esub> f \<in> obj\<^bsub>CatExp' A B\<^esub>" and 
         "cod\<^bsub>CatExp' A B\<^esub> f \<in> obj\<^bsub>CatExp' A B\<^esub>" 
      by(auto simp add: CatExp'_def NatTransP.NatTransFtor 
        NatTransP.NatTransFtor2 NatTransP.NatTransFtorDom NatTransP.NatTransFtorCod DDDC CCCD functor_abbrev_def)
  }
  {
    fix F assume a: "F \<in> obj\<^bsub>CatExp' A B\<^esub>" 
    show "id\<^bsub>CatExp' A B\<^esub> F maps\<^bsub>CatExp' A B\<^esub> F to F" 
    proof(rule MapsToI)
      have "Ftor F : A \<longrightarrow> B" using a by (simp add: CatExp'_def)
      thus "id\<^bsub>CatExp' A B\<^esub> F \<in> mor\<^bsub>CatExp' A B\<^esub>" 
        apply(simp add: CatExp'_def NTCatDom_def NTCatCod_def IdNatTransNatTrans functor_abbrev_def)
        apply(simp add: IdNatTrans_defs)
        done
      show "dom\<^bsub>CatExp' A B\<^esub> (id\<^bsub>CatExp' A B\<^esub> F) = F" by (simp add: CatExp'_def IdNatTrans_defs)
      show "cod\<^bsub>CatExp' A B\<^esub> (id\<^bsub>CatExp' A B\<^esub> F) = F" by (simp add: CatExp'_def IdNatTrans_defs)
    qed
  }
  {
    fix f assume a: "f \<in> mor\<^bsub>CatExp' A B\<^esub>" 
    show "(id\<^bsub>CatExp' A B\<^esub> (dom\<^bsub>CatExp' A B\<^esub> f)) ;;\<^bsub>CatExp' A B\<^esub> f = f" and
         "f ;;\<^bsub>CatExp' A B\<^esub> (id\<^bsub>CatExp' A B\<^esub> (cod\<^bsub>CatExp' A B\<^esub> f)) = f" 
    proof(simp_all add: CatExp'_def)
      have NT: "NatTrans f" using a by (simp add: CatExp'_def)
      show "IdNatTrans (NTDom f) \<bullet> f = f" using NT by (simp add:IdNatTransMapL)
      show "f \<bullet> IdNatTrans (NTCod f) = f" using NT by (simp add:IdNatTransMapR)
    qed
  }
  {
    fix f g h assume aa: "f \<approx>>\<^bsub>CatExp' A B\<^esub> g" and bb: "g \<approx>>\<^bsub>CatExp' A B\<^esub> h"
    {
      fix f g assume "f \<approx>>\<^bsub>CatExp' A B\<^esub> g" hence "f \<approx>>\<bullet> g"
        apply(simp only: NTCompDefined_def)
        by (auto simp add:  CatExp'_def)
    }
    hence "f \<approx>>\<bullet> g" and "g \<approx>>\<bullet> h" using aa bb by auto
    thus "f ;;\<^bsub>CatExp' A B\<^esub> g ;;\<^bsub>CatExp' A B\<^esub> h = f ;;\<^bsub>CatExp' A B\<^esub> (g ;;\<^bsub>CatExp' A B\<^esub> h)" 
    by(simp add: CatExp'_def NatTransCompAssoc)
  }
  {
    fix f g X Y Z assume a: "f maps\<^bsub>CatExp' A B\<^esub> X to Y" and b: "g maps\<^bsub>CatExp' A B\<^esub> Y to Z"
    show "f ;;\<^bsub>CatExp' A B\<^esub> g maps\<^bsub>CatExp' A B\<^esub> X to Z" 
    proof(rule MapsToI, auto simp add: CatExp'_def)
      have nt1: "NatTrans f" and cd1: "NTCatDom f = A"
        and cc1: "NTCatCod f = B" and d1: "NTDom f = X" and c1: "NTCod f = Y"
        using a by (auto simp add: CatExp'_def)
      moreover have nt2: "NatTrans g" and cd2: "NTCatDom g = A" 
        and cc2: "NTCatCod g = B" and d2: "NTDom g = Y" and c2: "NTCod g = Z"
        using b by (auto simp add: CatExp'_def)
      ultimately have Comp: "f \<approx>>\<bullet> g" by(auto intro: NTCompDefinedI)
      thus "NatTrans (f \<bullet> g)" by (simp add: NatTransCompNatTrans)
      show "NTCatDom (f \<bullet> g) = A" using Comp cd1 by (simp add: NTCatDom)
      show "NTCatCod (f \<bullet> g) = B" using Comp cc2 by (simp add: NTCatCod)
      show "NTDom (f \<bullet> g) = X" using d1 by (simp add: NatTransComp_defs)
      show "NTCod (f \<bullet> g) = Z" using c2 by (simp add: NatTransComp_defs)
    qed
  }
qed

lemma CatExpCat: "\<lbrakk>Category A ; Category B\<rbrakk> \<Longrightarrow> Category (CatExp A B)"
by(simp add: CatExpCatAx CatExp_def MakeCat)

lemmas CatExp_defs = CatExp_def CatExp'_def MakeCat_def

lemma CatExpDom: "f \<in> Mor (CatExp A B) \<Longrightarrow> dom\<^bsub>CatExp A B\<^esub> f = NTDom f"
by (simp add: CatExp_defs)

lemma CatExpCod: "f \<in> Mor (CatExp A B) \<Longrightarrow> cod\<^bsub>CatExp A B\<^esub> f = NTCod f"
by (simp add: CatExp_defs)

lemma CatExpId: "X \<in> Obj (CatExp A B) \<Longrightarrow> Id (CatExp A B) X = IdNatTrans X"
by (simp add: CatExp_defs)

lemma CatExpNatTransCompDef: assumes "f \<approx>>\<^bsub>CatExp A B\<^esub> g" shows "f \<approx>>\<bullet> g"
proof-
  have 1: "f \<approx>>\<^bsub>CatExp' A B\<^esub> g" using assms by (simp add: CatExp_def MakeCatCompDef)
  show "f \<approx>>\<bullet> g"
  proof(rule NTCompDefinedI)
    show "NatTrans f" using 1 by (auto simp add: CatExp'_def)
    show "NatTrans g" using 1 by (auto simp add: CatExp'_def)
    show "NTCatDom g = NTCatDom f" using 1 by (auto simp add: CatExp'_def)
    show "NTCatCod g = NTCatCod f" using 1 by (auto simp add: CatExp'_def)
    show "NTCod f = NTDom g" using 1 by (auto simp add: CatExp'_def)
  qed
qed

lemma CatExpDist:
  assumes "X \<in> Obj A" and "f \<approx>>\<^bsub>CatExp A B\<^esub> g"
  shows "(f ;;\<^bsub>CatExp A B\<^esub> g) $$ X = (f $$ X) ;;\<^bsub>B\<^esub> (g $$ X)"
proof-
  have "f \<in> Mor (CatExp' A B)" using assms by (auto simp add: CatExp_def MakeCatMor)
  hence 1: "NTCatDom f = A" and 2: "NTCatCod f = B" by (simp add: CatExp'_def)+
  hence 4: "X \<in> Obj (NTCatDom f)" using assms by simp
  have 3: "f \<approx>>\<bullet> g" using assms(2) by (simp add: CatExpNatTransCompDef)
  have "(f ;;\<^bsub>CatExp A B\<^esub> g) $$ X = (f ;;\<^bsub>CatExp' A B\<^esub> g) $$ X" using assms(2) by (simp add: CatExp_def MakeCatComp2)
  also have "... = (f \<bullet> g) $$ X" by (simp add: CatExp'_def)
  also have "... = (f $$ X) ;;\<^bsub>B\<^esub> (g $$ X)" using 4 2 3 by (simp add: NatTransComp_Comp2[of X f g])
  finally show ?thesis .
qed    

lemma CatExpMorNT: "f \<in> Mor (CatExp A B) \<Longrightarrow> NatTrans f"
by (simp add: CatExp_defs)

end

