(*
Author: Alexander Katovsky
*)

section "Yoneda"

theory Yoneda
imports NatTrans SetCat
begin

definition "YFtorNT' C f \<equiv> \<lparr>NTDom = Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f] , NTCod = Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> f] ,
                       NatTransMap = \<lambda> B . Hom\<^bsub>C\<^esub>[B,f]\<rparr>"

definition "YFtorNT C f \<equiv> MakeNT (YFtorNT' C f)"

lemmas YFtorNT_defs = YFtorNT'_def YFtorNT_def MakeNT_def

lemma YFtorNTCatDom: "NTCatDom (YFtorNT C f) = Op C"
by (simp add: YFtorNT_defs NTCatDom_def HomFtorContraDom)

lemma YFtorNTCatCod: "NTCatCod (YFtorNT C f) = SET"
by (simp add: YFtorNT_defs NTCatCod_def HomFtorContraCod)

lemma YFtorNTApp1: assumes "X \<in> Obj (NTCatDom (YFtorNT C f))" shows "(YFtorNT C f) $$ X = Hom\<^bsub>C\<^esub>[X,f]"
proof-
  have "(YFtorNT C f) $$ X = (YFtorNT' C f) $$ X" using assms by (simp add: MakeNTApp YFtorNT_def)
  thus ?thesis by (simp add: YFtorNT'_def)
qed

definition 
  "YFtor' C \<equiv> \<lparr>
         CatDom = C , 
         CatCod = CatExp (Op C) SET , 
         MapM = \<lambda> f . YFtorNT C f
  \<rparr>"

definition "YFtor C \<equiv> MakeFtor(YFtor' C)"

lemmas YFtor_defs = YFtor'_def YFtor_def MakeFtor_def

lemma YFtorNTNatTrans':
  assumes "LSCategory C" and "f \<in> Mor C"
  shows "NatTransP (YFtorNT' C f)"
proof(auto simp only: NatTransP_def)
  have Fd: "Ftor (NTDom (YFtorNT' C f)) : (Op C) \<longrightarrow> SET" using assms 
    by (simp add:  HomFtorContraFtor Category.Cdom YFtorNT'_def)
  have Fc: "Ftor (NTCod (YFtorNT' C f)) : (Op C) \<longrightarrow> SET" using assms 
    by (simp add:  HomFtorContraFtor Category.Ccod YFtorNT'_def)
  show "Functor (NTDom (YFtorNT' C f))" using Fd by auto
  show "Functor (NTCod (YFtorNT' C f))" using Fc by auto
  show "NTCatDom (YFtorNT' C f) = CatDom (NTCod (YFtorNT' C f))"
    by(simp add: YFtorNT'_def NTCatDom_def HomFtorContraDom)
  show "NTCatCod (YFtorNT' C f) = CatCod (NTDom (YFtorNT' C f))"
    by(simp add: YFtorNT'_def NTCatCod_def HomFtorContraCod)
  {
    fix X assume a: "X \<in> Obj (NTCatDom (YFtorNT' C f))"
    show "(YFtorNT' C f) $$ X maps\<^bsub>NTCatCod (YFtorNT' C f)\<^esub> (NTDom (YFtorNT' C f) @@ X) to (NTCod (YFtorNT' C f) @@ X)"
    proof-
      have Obj: "X \<in> Obj C" using a by (simp add: NTCatDom_def YFtorNT'_def HomFtorContraDom OppositeCategory_def)
      have H1: "(Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f]) @@ X = Hom\<^bsub>C \<^esub>X dom\<^bsub>C\<^esub> f " using assms Obj by(simp add: HomFtorOpObj Category.Cdom)
      have H2: "(Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> f]) @@ X = Hom\<^bsub>C \<^esub>X cod\<^bsub>C\<^esub> f " using assms Obj by(simp add: HomFtorOpObj Category.Ccod)
      have "Hom\<^bsub>C\<^esub>[X,f] maps\<^bsub>SET\<^esub> (Hom\<^bsub>C \<^esub>X dom\<^bsub>C\<^esub> f) to (Hom\<^bsub>C \<^esub>X cod\<^bsub>C\<^esub> f)" using assms Obj by (simp add: HomFtorMapsTo)
      thus ?thesis using H1 H2 by(simp add: YFtorNT'_def NTCatCod_def NTCatDom_def HomFtorContraCod)
    qed
  }
  {
    fix g X Y assume a: "g maps\<^bsub>NTCatDom (YFtorNT' C f)\<^esub> X to Y"
    show "((NTDom (YFtorNT' C f)) ## g) ;;\<^bsub>NTCatCod (YFtorNT' C f) \<^esub>(YFtorNT' C f $$ Y) =
       ((YFtorNT' C f) $$ X) ;;\<^bsub>NTCatCod (YFtorNT' C f) \<^esub>(NTCod (YFtorNT' C f) ## g)"
    proof-
      have M1: "g maps\<^bsub>Op C\<^esub> X to Y" using a by (auto simp add: NTCatDom_def YFtorNT'_def HomFtorContraDom)
      have D1: "dom\<^bsub>C\<^esub> g = Y" and C1: "cod\<^bsub>C\<^esub> g = X" using M1 by (auto simp add: OppositeCategory_def)
      have morf: "f \<in> Mor C" and morg: "g \<in> Mor C" using assms M1 by (auto simp add: OppositeCategory_def)
      have H1: "(HomC\<^bsub>C\<^esub>[g,dom\<^bsub>C\<^esub> f]) = (Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f]) ## g" 
        and H2: "(HomC\<^bsub>C\<^esub>[g,cod\<^bsub>C\<^esub> f]) = (Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> f]) ## g" using M1 
        by (auto simp add: HomFtorContra_def HomFtorContra'_def MakeFtor_def)
      have "(HomC\<^bsub>C\<^esub>[g,dom\<^bsub>C\<^esub> f]) ;;\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[dom\<^bsub>C\<^esub> g,f]) = (Hom\<^bsub>C\<^esub>[cod\<^bsub>C\<^esub> g,f]) ;;\<^bsub>SET\<^esub> (HomC\<^bsub>C\<^esub>[g,cod\<^bsub>C\<^esub> f])" using assms morf morg
        by (simp add: HomCHom)
      hence "((Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f]) ## g) ;;\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[Y,f]) = (Hom\<^bsub>C\<^esub>[X,f]) ;;\<^bsub>SET\<^esub> ((Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> f]) ## g)"
        using H1 H2 D1 C1 by simp
      thus ?thesis by (simp add: YFtorNT'_def NTCatCod_def HomFtorContraCod)
    qed
  }
qed

lemma YFtorNTNatTrans:
  assumes "LSCategory C" and "f \<in> Mor C"
  shows "NatTrans (YFtorNT C f)"
by (simp add: assms YFtorNTNatTrans' YFtorNT_def MakeNT)

lemma YFtorNTMor:
  assumes "LSCategory C" and "f \<in> Mor C"
  shows "YFtorNT C f \<in> Mor (CatExp (Op C) SET)"
proof(auto simp add: CatExp_def CatExp'_def MakeCatMor)
  have "f \<in> Mor C" using assms by auto
  thus "NatTrans (YFtorNT C f)" using assms by (simp add: YFtorNTNatTrans)
  show "NTCatDom (YFtorNT C f) = Op C" by (simp add: YFtorNTCatDom) 
  show "NTCatCod (YFtorNT C f) = SET" by (simp add: YFtorNTCatCod) 
qed

lemma YFtorNtMapsTo:
  assumes "LSCategory C" and "f \<in> Mor C"
  shows "YFtorNT C f maps\<^bsub>CatExp (Op C) SET\<^esub> (Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f]) to (Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> f])"
proof(rule MapsToI)
  have "f \<in> Mor C"  using assms by auto
  thus 1: "YFtorNT C f \<in> mor\<^bsub>CatExp (Op C) SET\<^esub>" using assms by (simp add: YFtorNTMor)
  show "dom\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C f = Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f]" using 1 by(simp add:CatExpDom YFtorNT_defs)
  show "cod\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C f = Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> f]" using 1 by(simp add:CatExpCod YFtorNT_defs)
qed

lemma YFtorNTCompDef:
  assumes "LSCategory C" and "f \<approx>>\<^bsub>C\<^esub> g"
  shows "YFtorNT C f \<approx>>\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g"
proof(rule CompDefinedI)
  have "f \<in> Mor C" and "g \<in> Mor C" using assms by auto
  hence 1: "YFtorNT C f maps\<^bsub>CatExp (Op C) SET\<^esub> (Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f]) to (Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> f])"
    and 2: "YFtorNT C g maps\<^bsub>CatExp (Op C) SET\<^esub> (Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> g]) to (Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> g])"
    using assms by (simp add: YFtorNtMapsTo)+
  thus "YFtorNT C f \<in> mor\<^bsub>CatExp (Op C) SET\<^esub>"
    and "YFtorNT C g \<in> mor\<^bsub>CatExp (Op C) SET\<^esub>" by auto
  have "cod\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C f = (Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> f])" using 1 by auto
  moreover have "dom\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g = (Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> g])" using 2 by auto
  moreover have "cod\<^bsub>C\<^esub> f = dom\<^bsub>C\<^esub> g" using assms by auto
  ultimately show "cod\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C f = dom\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g" by simp
qed

lemma PreSheafCat: "LSCategory C \<Longrightarrow> Category (CatExp (Op C) SET)"
by(simp add: YFtor'_def OpCatCat SETCategory CatExpCat)

lemma YFtor'Obj1:
  assumes "X \<in> Obj (CatDom (YFtor' C))" and "LSCategory C"
  shows "(YFtor' C) ## (Id (CatDom (YFtor' C)) X) = Id (CatCod (YFtor' C)) (Hom\<^bsub>C \<^esub>[\<midarrow>,X])"
proof(simp add: YFtor'_def, rule NatTransExt)
  have Obj: "X \<in> Obj C" using assms by (simp add: YFtor'_def)
  have HomObj: "(Hom\<^bsub>C\<^esub>[\<midarrow>,X]) \<in> Obj (CatExp (Op C) SET)" using assms Obj by(simp add: CatExp_defs HomFtorContraFtor)
  hence Id: "Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) \<in> Mor (CatExp (Op C) SET)" using assms 
    by (simp add: PreSheafCat Category.CatIdInMor)
  have CAT: "Category(CatExp (Op C) SET)" using assms by (simp add: PreSheafCat)
  have HomObj: "(Hom\<^bsub>C\<^esub>[\<midarrow>,X]) \<in> Obj (CatExp (Op C) SET)" using assms Obj 
    by(simp add: CatExp_defs HomFtorContraFtor)
  show "NatTrans (YFtorNT C (Id C X))"
  proof(rule YFtorNTNatTrans)
    show "LSCategory C" using assms(2) .
    show "Id C X \<in> Mor C" using assms Obj by (simp add: Category.CatIdInMor)
  qed
  show "NatTrans(Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))" using Id by (simp add: CatExp_defs)
  show "NTDom (YFtorNT C (Id C X)) = NTDom (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))"
  proof(simp add: YFtorNT_defs)
    have "Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> (Id C X)] = Hom\<^bsub>C\<^esub>[\<midarrow>,X]" using assms Obj by (simp add: Category.CatIdDomCod)
    also have "... = dom\<^bsub>CatExp (Op C) SET\<^esub>  (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))" using CAT HomObj
      by (simp add: Category.CatIdDomCod)
    also have "... = NTDom (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))" using Id by (simp add: CatExpDom)
    finally show "Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> (Id C X)] = NTDom (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))" .
  qed
  show "NTCod (YFtorNT C (Id C X)) = NTCod (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))"
  proof(simp add: YFtorNT_defs)
    have "Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> (Id C X)] = Hom\<^bsub>C\<^esub>[\<midarrow>,X]" using assms Obj by (simp add: Category.CatIdDomCod)
    also have "... = cod\<^bsub>CatExp (Op C) SET\<^esub>  (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))" using CAT HomObj
      by (simp add: Category.CatIdDomCod)
    also have "... = NTCod (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))" using Id by (simp add: CatExpCod)
    finally show "Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> (Id C X)] = NTCod (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X]))" .
  qed
  {
    fix Y assume a: "Y \<in> Obj (NTCatDom (YFtorNT C (Id C X)))"
    show "(YFtorNT C (Id C X)) $$ Y = (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X])) $$ Y"
    proof-
      have CD: "CatDom (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) = Op C" by (simp add: HomFtorContraDom)
      have CC: "CatCod (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) = SET" by (simp add: HomFtorContraCod)
      have ObjY: "Y \<in> Obj C" and ObjYOp: "Y \<in> Obj (Op C)" using a by(simp add: YFtorNTCatDom OppositeCategory_def)+
      have "(YFtorNT C (Id C X)) $$ Y = (Hom\<^bsub>C\<^esub>[Y,(Id C X)])" using a by (simp add: YFtorNTApp1)
      also have "... = id\<^bsub>SET\<^esub> (Hom\<^bsub>C \<^esub>Y X)" using Obj ObjY assms by (simp add: HomFtorId)
      also have "... = id\<^bsub>SET\<^esub> ((Hom\<^bsub>C\<^esub>[\<midarrow>,X]) @@ Y)" using Obj ObjY assms by (simp add: HomFtorOpObj )
      also have "... = (IdNatTrans (Hom\<^bsub>C\<^esub>[\<midarrow>,X])) $$ Y" using CD CC ObjYOp by (simp add: IdNatTrans_map)
      also have "... = (Id (CatExp (Op C) SET) (Hom\<^bsub>C\<^esub>[\<midarrow>,X])) $$ Y" using HomObj by (simp add: CatExpId)
      finally show ?thesis .
    qed
  }
qed

lemma YFtorPreFtor:
  assumes "LSCategory C"
  shows   "PreFunctor (YFtor' C)"
proof(auto simp only: PreFunctor_def)
  have CAT: "Category(CatExp (Op C) SET)" using assms by (simp add: PreSheafCat)
  {
    fix f g assume a: "f \<approx>>\<^bsub>CatDom (YFtor' C)\<^esub> g"
    show "(YFtor' C) ## (f ;;\<^bsub>CatDom (YFtor' C)\<^esub> g) = ((YFtor' C) ## f) ;;\<^bsub>CatCod (YFtor' C)\<^esub> ((YFtor' C) ## g)" 
    proof(simp add: YFtor'_def, rule NatTransExt)
      have CD: "f \<approx>>\<^bsub>C\<^esub> g" using a by (simp add: YFtor'_def)
      have CD2: "YFtorNT C f \<approx>>\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g" using CD assms by (simp add: YFtorNTCompDef)
      have Mor1: "YFtorNT C f ;;\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g \<in> Mor (CatExp (Op C) SET)" using CAT CD2
        by (simp add: Category.MapsToMorDomCod)
      show "NatTrans (YFtorNT C (f ;;\<^bsub>C\<^esub> g))" using assms by (simp add: Category.MapsToMorDomCod CD YFtorNTNatTrans)
      show "NatTrans (YFtorNT C f ;;\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g)" using Mor1 by (simp add: CatExpMorNT)
      show "NTDom (YFtorNT C (f ;;\<^bsub>C\<^esub> g)) = NTDom (YFtorNT C f ;;\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g)"
      proof-
        have 1: "YFtorNT C f \<in> mor\<^bsub>CatExp (Op C) SET\<^esub>" using CD2 by auto
        have "NTDom (YFtorNT C (f ;;\<^bsub>C\<^esub> g)) = Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g)]" by (simp add: YFtorNT_defs)
        also have "... = Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f]" using CD assms by (simp add: Category.MapsToMorDomCod)
        also have "... = NTDom (YFtorNT C f)" by (simp add: YFtorNT_defs)
        also have "... = dom\<^bsub>CatExp (Op C) SET\<^esub> (YFtorNT C f)" using 1 by (simp add: CatExpDom)
        also have "... = dom\<^bsub>CatExp (Op C) SET\<^esub> (YFtorNT C f ;;\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g)" using CD2 CAT
          by (simp add: Category.MapsToMorDomCod)
        finally show ?thesis using Mor1 by (simp add: CatExpDom)
      qed
      show "NTCod (YFtorNT C (f ;;\<^bsub>C\<^esub> g)) = NTCod (YFtorNT C f ;;\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g)"
      proof-
        have 1: "YFtorNT C g \<in> mor\<^bsub>CatExp (Op C) SET\<^esub>" using CD2 by auto
        have "NTCod (YFtorNT C (f ;;\<^bsub>C\<^esub> g)) = Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> g)]" by (simp add: YFtorNT_defs)
        also have "... = Hom\<^bsub>C\<^esub>[\<midarrow>,cod\<^bsub>C\<^esub> g]" using CD assms by (simp add: Category.MapsToMorDomCod)
        also have "... = NTCod (YFtorNT C g)" by (simp add: YFtorNT_defs)
        also have "... = cod\<^bsub>CatExp (Op C) SET\<^esub> (YFtorNT C g)" using 1 by (simp add: CatExpCod)
        also have "... = cod\<^bsub>CatExp (Op C) SET\<^esub> (YFtorNT C f ;;\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g)" using CD2 CAT
          by (simp add: Category.MapsToMorDomCod)
        finally show ?thesis using Mor1 by (simp add: CatExpCod)
      qed
      {
        fix X assume a: "X \<in> Obj (NTCatDom (YFtorNT C (f ;;\<^bsub>C\<^esub> g)))"
        show "YFtorNT C (f ;;\<^bsub>C\<^esub> g) $$ X = (YFtorNT C f ;;\<^bsub>CatExp (Op C) SET\<^esub> YFtorNT C g) $$ X"
        proof-
          have Obj: "X \<in> Obj C" and ObjOp: "X \<in> Obj (Op C)" using a by (simp add: YFtorNTCatDom OppositeCategory_def)+
          have App1: "(Hom\<^bsub>C\<^esub>[X,f]) = (YFtorNT C f) $$ X" 
            and App2: "(Hom\<^bsub>C\<^esub>[X,g]) = (YFtorNT C g) $$ X" using a by (simp add: YFtorNTApp1 YFtorNTCatDom)+
          have "(YFtorNT C (f ;;\<^bsub>C\<^esub> g)) $$ X = (Hom\<^bsub>C\<^esub>[X,(f ;;\<^bsub>C\<^esub> g)])" using a by (simp add: YFtorNTApp1)
          also have "... = (Hom\<^bsub>C\<^esub>[X,f]) ;;\<^bsub>SET\<^esub> (Hom\<^bsub>C\<^esub>[X,g])" using CD assms Obj by (simp add: HomFtorDist)
          also have "... = ((YFtorNT C f) $$ X) ;;\<^bsub>SET\<^esub> ((YFtorNT C g) $$ X)" using App1 App2 by simp
          finally show ?thesis using ObjOp CD2 by (simp add: CatExpDist)
        qed
      }
    qed
  }
  {
    fix X assume a: "X \<in> Obj (CatDom (YFtor' C))"
    show "\<exists> Y \<in> Obj (CatCod (YFtor' C)) . YFtor' C ## (Id (CatDom (YFtor' C)) X) = Id (CatCod (YFtor' C)) Y"
    proof(rule_tac x="Hom\<^bsub>C \<^esub>[\<midarrow>,X]" in Set.rev_bexI)
      have "X \<in> Obj C" using a by(simp add: YFtor'_def)
      thus "Hom\<^bsub>C \<^esub>[\<midarrow>,X] \<in> Obj (CatCod (YFtor' C))" using assms by(simp add: YFtor'_def CatExp_defs HomFtorContraFtor)
      show "(YFtor' C) ## (Id (CatDom (YFtor' C)) X) = Id (CatCod (YFtor' C)) (Hom\<^bsub>C \<^esub>[\<midarrow>,X])" using a assms
        by (simp add: YFtor'Obj1)
    qed
  }
  show "Category (CatDom (YFtor' C))" using assms by (simp add: YFtor'_def)
  show "Category (CatCod (YFtor' C))" using CAT by (simp add: YFtor'_def)
qed

lemma YFtor'Obj:
  assumes "X \<in> Obj (CatDom (YFtor' C))"
  and     "LSCategory C" 
  shows   "(YFtor' C) @@ X = Hom\<^bsub>C \<^esub>[\<midarrow>,X]"
proof(rule PreFunctor.FmToFo, simp_all add: assms YFtor'Obj1 YFtorPreFtor)
  have "X \<in> Obj C" using assms by(simp add: YFtor'_def)
  thus "Hom\<^bsub>C \<^esub>[\<midarrow>,X] \<in> Obj (CatCod (YFtor' C))" using assms by(simp add: YFtor'_def CatExp_defs HomFtorContraFtor)
qed

lemma YFtorFtor':
  assumes "LSCategory C"
  shows   "FunctorM (YFtor' C)"
proof(auto simp only: FunctorM_def)
  show "PreFunctor (YFtor' C)" using assms by (rule YFtorPreFtor)
  show "FunctorM_axioms (YFtor' C)" 
  proof(auto simp add:FunctorM_axioms_def)
    {
      fix f X Y assume aa: "f maps\<^bsub>CatDom (YFtor' C) \<^esub>X to Y"
      show "YFtor' C ## f maps\<^bsub>CatCod (YFtor' C)\<^esub> YFtor' C @@ X to YFtor' C @@ Y"
      proof-
        have Mor1: "f maps\<^bsub>C\<^esub> X to Y" using aa by (simp add: YFtor'_def)
        have "Category (CatDom (YFtor' C))" using assms by (simp add: YFtor'_def)
        hence Obj1: "X \<in> Obj (CatDom (YFtor' C))" and
              Obj2: "Y \<in> Obj (CatDom (YFtor' C))" using aa assms by (simp add: Category.MapsToObj)+
        have "(YFtor' C ## f) = YFtorNT C f" by (simp add: YFtor'_def)
        moreover have "YFtor' C @@ X = Hom\<^bsub>C \<^esub>[\<midarrow>,X]" 
          and "YFtor' C @@ Y = Hom\<^bsub>C \<^esub>[\<midarrow>,Y]" using Obj1 Obj2 assms by (simp add: YFtor'Obj)+
        moreover have "CatCod (YFtor' C) = CatExp (Op C) SET" by (simp add: YFtor'_def)
        moreover have "YFtorNT C f maps\<^bsub>CatExp (Op C) SET\<^esub> (Hom\<^bsub>C \<^esub>[\<midarrow>,X]) to (Hom\<^bsub>C \<^esub>[\<midarrow>,Y])" 
          using assms Mor1 by (auto simp add: YFtorNtMapsTo)
        ultimately show ?thesis by simp 
      qed
    }
  qed
qed

lemma YFtorFtor: assumes "LSCategory C" shows "Ftor (YFtor C) : C \<longrightarrow> (CatExp (Op C) SET)"
proof(auto simp only: functor_abbrev_def)
  show "Functor (YFtor C)" using assms by(simp add: MakeFtor YFtor_def YFtorFtor')
  show "CatDom (YFtor C) = C" and "CatCod (YFtor C) = (CatExp (Op C) SET)" 
    using assms by(simp add: MakeFtor_def YFtor_def YFtor'_def)+
qed

lemma YFtorObj: 
  assumes "LSCategory C" and "X \<in> Obj C"
  shows "(YFtor C) @@ X = Hom\<^bsub>C \<^esub>[\<midarrow>,X]"
proof-
  have "CatDom (YFtor' C) = C" by (simp add: YFtor'_def)
  moreover hence "(YFtor' C) @@ X = Hom\<^bsub>C \<^esub>[\<midarrow>,X]" using assms by(simp add: YFtor'Obj)
  moreover have "PreFunctor (YFtor' C)" using assms by (simp add: YFtorPreFtor)
  ultimately show ?thesis using assms by (simp add: MakeFtorObj YFtor_def)
qed

lemma YFtorObj2:
  assumes "LSCategory C" and "X \<in> Obj C" and "Y \<in> Obj C"
  shows "((YFtor C) @@ Y) @@ X = Hom\<^bsub>C \<^esub>X Y"
proof-
  have "Hom\<^bsub>C \<^esub>X Y = ((Hom\<^bsub>C\<^esub>[\<midarrow>,Y]) @@ X)" using assms by (simp add: HomFtorOpObj)
  also have "... = ((YFtor C @@ Y) @@ X)" using assms by (simp add: YFtorObj)
  finally show ?thesis by simp
qed

lemma YFtorMor: "\<lbrakk>LSCategory C ; f \<in> Mor C\<rbrakk> \<Longrightarrow> (YFtor C) ## f = YFtorNT C f"
by (simp add: YFtor_defs MakeFtorMor)

(*
We can't do this because the presheaf category may not be locally small
definition 
  NatHom ("Nat\<index> _ _") where
  "NatHom C F G \<equiv> Hom\<^bsub>CatExp (Op C) SET\<^esub> F G"
*)

definition "YMap C X \<eta> \<equiv> (\<eta> $$ X) |@| (m2z\<^bsub>C\<^esub> (id\<^bsub>C \<^esub>X))"
definition "YMapInv' C X F x \<equiv> \<lparr>
      NTDom = ((YFtor C) @@ X), 
      NTCod = F, 
      NatTransMap = \<lambda> B . ZFfun (Hom\<^bsub>C\<^esub> B X) (F @@ B) (\<lambda> f . (F ## (z2m\<^bsub>C\<^esub> f)) |@| x)
  \<rparr>"
definition "YMapInv C X F x \<equiv> MakeNT (YMapInv' C X F x)"

lemma YMapInvApp: 
  assumes "X \<in> Obj C" and "B \<in> Obj C" and "LSCategory C"
  shows "(YMapInv C X F x) $$ B = ZFfun (Hom\<^bsub>C\<^esub> B X) (F @@ B) (\<lambda> f . (F ## (z2m\<^bsub>C\<^esub> f)) |@| x)"
proof-
  have "NTCatDom (MakeNT (YMapInv' C X F x)) = CatDom (NTDom (YMapInv' C X F x))" by (simp add: MakeNT_def NTCatDom_def)
  also have "... = CatDom (Hom\<^bsub>C\<^esub>[\<midarrow>,X])" using assms by (simp add: YFtorObj YMapInv'_def)
  also have "... = Op C" using assms HomFtorContraFtor[of C X] by auto
  finally have "NTCatDom (MakeNT (YMapInv' C X F x)) = Op C" .
  hence 1: "B \<in> Obj (NTCatDom (MakeNT (YMapInv' C X F x)))" using assms by (simp add: OppositeCategory_def)
  have "(YMapInv C X F x) $$ B = (MakeNT (YMapInv' C X F x)) $$ B" by (simp add: YMapInv_def)
  also have "... = (YMapInv' C X F x) $$ B" using 1 by(simp add: MakeNTApp)
  finally show ?thesis by (simp add: YMapInv'_def)
qed 

lemma YMapImage:
  assumes "LSCategory C" and "Ftor F : (Op C) \<longrightarrow> SET" and "X \<in> Obj C"
  and "NT \<eta> : (YFtor C @@ X) \<Longrightarrow> F"
  shows "(YMap C X \<eta>) |\<in>| (F @@ X)"
proof(simp only: YMap_def)
  have "(YFtor C @@ X) = (Hom\<^bsub>C\<^esub>[\<midarrow>,X])" using assms by (auto simp add: YFtorObj)
  moreover have "Ftor (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) : (Op C) \<longrightarrow> SET" using assms by (simp add: HomFtorContraFtor)
  ultimately have "CatDom (YFtor C @@ X) = Op C" by auto
  hence Obj: "X \<in> Obj (CatDom (YFtor C @@ X))" using assms by (simp add: OppositeCategory_def)
  moreover have "CatCod F  = SET" using assms by auto
  moreover have "\<eta> $$ X maps\<^bsub>CatCod F \<^esub>((YFtor C @@ X) @@ X) to (F @@ X)" using assms Obj by (simp add: NatTransMapsTo) 
  ultimately have "\<eta> $$ X maps\<^bsub>SET\<^esub> ((YFtor C @@ X) @@ X) to (F @@ X)" by simp 
  moreover have "(m2z\<^bsub>C \<^esub>(Id C X))  |\<in>| ((YFtor C @@ X) @@ X)" 
  proof-
    have "(Id C X) maps\<^bsub>C \<^esub>X to X" using assms by (simp add: Category.Simps)
    moreover have "((YFtor C @@ X) @@ X) = Hom\<^bsub>C\<^esub> X X" using assms by (simp add: YFtorObj2)
    ultimately show ?thesis using assms by (simp add: LSCategory.m2zz2m)
  qed
  ultimately show "((\<eta> $$ X) |@| (m2z\<^bsub>C \<^esub>(Id C X))) |\<in>| (F @@ X)" by (simp add: SETfunDomAppCod)
qed

lemma YMapInvNatTransP:
  assumes "LSCategory C" and "Ftor F : (Op C) \<longrightarrow> SET" and xobj: "X \<in> Obj C" and xinF: "x |\<in>| (F @@ X)"
  shows "NatTransP (YMapInv' C X F x)"
proof(auto simp only: NatTransP_def, simp_all add: YMapInv'_def NTCatCod_def NTCatDom_def)
  have yf: "(YFtor C @@ X) = Hom\<^bsub>C\<^esub>[\<midarrow>,X]" using assms by (simp add: YFtorObj)
  hence hf: "Ftor (YFtor C @@ X) : (Op C) \<longrightarrow> SET" using assms by (simp add: HomFtorContraFtor)
  thus "Functor (YFtor C @@ X)" by auto
  show ftf: "Functor F" using assms by auto
  have df: "CatDom F = Op C" and cf: "CatCod F = SET" using assms by auto
  have dy: "CatDom ((YFtor C) @@ X) = Op C" and cy: "CatCod ((YFtor C) @@ X) = SET" using hf by auto
  show "CatDom ((YFtor C) @@ X) = CatDom F" using df dy by simp
  show "CatCod F = CatCod ((YFtor C) @@ X)" using cf cy by simp
  {
    fix Y assume yobja: "Y \<in> Obj (CatDom ((YFtor C) @@ X))"
    show "ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>f. (F ## (z2m\<^bsub>C \<^esub>f)) |@| x) maps\<^bsub>CatCod F\<^esub> ((YFtor C @@ X) @@ Y) to (F @@ Y)"
    proof(simp add: cf, rule MapsToI)
      have yobj: "Y \<in> Obj C" using yobja dy by (simp add: OppositeCategory_def)
      have zffun: "isZFfun (ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>f. (F ## z2m\<^bsub>C\<^esub>f) |@| x))" 
      proof(rule SETfun, rule allI, rule impI)
        {
          fix y assume yhom: "y |\<in>| (Hom\<^bsub>C\<^esub> Y X)" show "(F ## (z2m\<^bsub>C \<^esub>y)) |@| x |\<in>| (F @@ Y)"
          proof-
            let ?f = "(F ## (z2m\<^bsub>C \<^esub>y))"
            have "(z2m\<^bsub>C \<^esub>y) maps\<^bsub>C\<^esub> Y to X" using yhom yobj assms by (simp add: LSCategory.z2mm2z)
            hence "(z2m\<^bsub>C \<^esub>y) maps\<^bsub>Op C\<^esub> X to Y" by (simp add: MapsToOp)
            hence "?f maps\<^bsub>SET\<^esub> (F @@ X) to (F @@ Y)" using assms by (simp add: FunctorMapsTo)
            hence "isZFfun (?f)" and "|dom| ?f = F @@ X" and "|cod| ?f = F @@ Y" by (simp add: SETmapsTo)+
            thus "(?f |@| x) |\<in>| (F @@ Y)" using assms ZFfunDomAppCod[of ?f x] by simp
          qed
        }
      qed
      show "ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>f. (F ## z2m\<^bsub>C\<^esub>f) |@| x) \<in> mor\<^bsub>SET\<^esub>" using zffun
        by(simp add: SETmor)
      show "cod\<^bsub>SET\<^esub> ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>f. (F ## z2m\<^bsub>C\<^esub>f) |@| x) = F @@ Y" using zffun
        by(simp add: SETcod)
      have "(Hom\<^bsub>C\<^esub> Y X) = (YFtor C @@ X) @@ Y" using assms yobj by (simp add: YFtorObj2)
      thus "dom\<^bsub>SET\<^esub> ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>f. (F ## z2m\<^bsub>C\<^esub>f) |@| x) = (YFtor C @@ X) @@ Y" using zffun
        by(simp add: SETdom)
    qed
  }
  {
    fix f Z Y assume fmaps: "f maps\<^bsub>CatDom ((YFtor C ) @@ X)\<^esub> Z to Y" 
    have fmapsa: "f maps\<^bsub>Op C\<^esub> Z to Y" using fmaps dy by simp
    hence fmapsb: "f maps\<^bsub>C\<^esub> Y to Z" by (rule MapsToOpOp)
    hence fmor: "f \<in> Mor C" and fdom: "dom\<^bsub>C\<^esub> f = Y" and fcod: "cod\<^bsub>C\<^esub> f = Z" by (auto simp add: OppositeCategory_def)
    hence hc: "(Hom\<^bsub>C\<^esub>[\<midarrow>,X]) ## f = (HomC\<^bsub>C\<^esub>[f,X])" using assms by (simp add: HomContraMor)
    have yobj: "Y \<in> Obj C" and zobj: "Z \<in> Obj C" using fmapsb assms by (simp add: Category.MapsToObj)+
    have Ffmaps: "(F ## f) maps\<^bsub>SET\<^esub> (F @@ Z) to (F @@ Y)" using assms fmapsa by (simp add: FunctorMapsTo)
    have Fzmaps: "\<And> h A B . \<lbrakk>h |\<in>| (Hom\<^bsub>C\<^esub> A B) ; A \<in> Obj C ; B \<in> Obj C\<rbrakk> \<Longrightarrow> 
      (F ## (z2m\<^bsub>C \<^esub>h)) maps\<^bsub>SET\<^esub> (F @@ B) to (F @@ A)"
    proof-
      fix h A B assume h: "h |\<in>| (Hom\<^bsub>C\<^esub> A B)" and oA: "A \<in> Obj C" and oB: "B \<in> Obj C"  
      have "(z2m\<^bsub>C \<^esub>h) maps\<^bsub>C\<^esub> A to B" using assms h oA oB by (simp add: LSCategory.z2mm2z)
      hence "(z2m\<^bsub>C \<^esub>h) maps\<^bsub>Op C\<^esub> B to A" by (rule MapsToOp)
      thus "(F ## (z2m\<^bsub>C \<^esub>h)) maps\<^bsub>SET\<^esub> (F @@ B) to (F @@ A)" using assms by (simp add: FunctorMapsTo)
    qed
    have hHomF: "\<And>h. h |\<in>| (Hom\<^bsub>C\<^esub> Z X) \<Longrightarrow> (F ## (z2m\<^bsub>C \<^esub>h)) |@| x |\<in>| (F @@ Z)" using xobj zobj xinF
    proof-
      fix h assume h: "h |\<in>| (Hom\<^bsub>C\<^esub> Z X)"
      have "(F ## (z2m\<^bsub>C \<^esub>h)) maps\<^bsub>SET\<^esub> (F @@ X) to (F @@ Z)" using xobj zobj h by (simp add: Fzmaps)
      thus "(F ## (z2m\<^bsub>C \<^esub>h)) |@| x |\<in>| (F @@ Z)"  using assms by (simp add: SETfunDomAppCod)
    qed
    have Ff: "F ## f = ZFfun (F @@ Z) (F @@ Y) (\<lambda>h. (F ## f) |@| h)" using Ffmaps by (simp add: SETZFfun)
    have compdefa: "ZFfun (Hom\<^bsub>C\<^esub> Z X) (Hom\<^bsub>C\<^esub> Y X) (\<lambda>h. m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))) \<approx>>\<^bsub>SET\<^esub> 
          ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x)" 
    proof(rule CompDefinedI, simp_all add: SETmor[THEN sym])
      show "isZFfun (ZFfun (Hom\<^bsub>C\<^esub> Z X) (Hom\<^bsub>C\<^esub> Y X) (\<lambda>h. m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))))"
      proof(rule SETfun, rule allI, rule impI)
        fix h assume h: "h |\<in>| (Hom\<^bsub>C\<^esub> Z X)"
        have "(z2m\<^bsub>C \<^esub>h) maps\<^bsub>C\<^esub> Z to X" using assms h xobj zobj by (simp add: LSCategory.z2mm2z)
        hence "f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h) maps\<^bsub>C\<^esub> Y to X" using fmapsb assms(1) by (simp add: Category.Ccompt)
        thus "(m2z\<^bsub>C\<^esub> (f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))) |\<in>| (Hom\<^bsub>C\<^esub> Y X)" using assms by (simp add: LSCategory.m2zz2m)
      qed
      moreover show "isZFfun (ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x))" 
      proof(rule SETfun, rule allI, rule impI)
        fix h assume h: "h |\<in>| (Hom\<^bsub>C\<^esub> Y X)"
        have "(F ## (z2m\<^bsub>C \<^esub>h)) maps\<^bsub>SET\<^esub> (F @@ X) to (F @@ Y)" using xobj yobj h by (simp add: Fzmaps)
        thus "(F ## (z2m\<^bsub>C \<^esub>h)) |@| x |\<in>| (F @@ Y)" using assms by (simp add: SETfunDomAppCod)
      qed
      ultimately show "cod\<^bsub>SET\<^esub>(ZFfun (Hom\<^bsub>C\<^esub> Z X) (Hom\<^bsub>C\<^esub> Y X) (\<lambda>h. m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h)))) = 
        dom\<^bsub>SET\<^esub>(ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x))" by (simp add: SETcod SETdom)
    qed      
    have compdefb: "ZFfun (Hom\<^bsub>C\<^esub> Z X) (F @@ Z) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x) \<approx>>\<^bsub>SET\<^esub> 
          ZFfun (F @@ Z) (F @@ Y) (\<lambda>h. (F ## f) |@| h)" 
    proof(rule CompDefinedI, simp_all add: SETmor[THEN sym])
      show "isZFfun (ZFfun (Hom\<^bsub>C\<^esub> Z X) (F @@ Z) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x))" using hHomF by (simp add: SETfun)
      moreover show "isZFfun (ZFfun (F @@ Z) (F @@ Y) (\<lambda>h. (F ## f) |@| h))" 
      proof(rule SETfun, rule allI, rule impI)
        fix h assume h: "h |\<in>| (F @@ Z)"
        have "F ## f maps\<^bsub>SET\<^esub> F @@ Z to F @@ Y" using Ffmaps .
        thus "(F ## f) |@| h |\<in>| (F @@ Y)" using h by (simp add: SETfunDomAppCod)
      qed
      ultimately show "cod\<^bsub>SET\<^esub> (ZFfun (Hom\<^bsub>C\<^esub> Z X) (F @@ Z) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x)) = 
            dom\<^bsub>SET\<^esub> (ZFfun (F @@ Z) (F @@ Y) (\<lambda>h. (F ## f) |@| h))" by (simp add: SETcod SETdom)
    qed
    have "ZFfun (Hom\<^bsub>C\<^esub> Z X) (Hom\<^bsub>C\<^esub> Y X) (\<lambda>h. m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))) ;;\<^bsub>SET\<^esub> 
          ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x) = 
          ZFfun (Hom\<^bsub>C\<^esub> Z X) (Hom\<^bsub>C\<^esub> Y X) (\<lambda>h. m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))) |o| 
          ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x)" using Ff compdefa by (simp add: SETComp)
    also have "... = ZFfun (Hom\<^bsub>C\<^esub> Z X) (F @@ Y) ((\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x) o (\<lambda>h. m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))))"
    proof(rule ZFfunComp, rule allI, rule impI) 
      {
        fix h assume h: "h |\<in>| (Hom\<^bsub>C\<^esub> Z X)" 
        show "(m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))) |\<in>| (Hom\<^bsub>C\<^esub> Y X)" 
        proof-
          have "Z \<in> Obj C" using fmapsb assms by (simp add: Category.MapsToObj)
          hence "(z2m\<^bsub>C \<^esub>h) maps\<^bsub>C\<^esub> Z to X" using assms h by (simp add: LSCategory.z2mm2z)
          hence "f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h) maps\<^bsub>C\<^esub> Y to X" using fmapsb assms(1) by (simp add: Category.Ccompt)
          thus ?thesis using assms by (simp add: LSCategory.m2zz2m)
        qed
      } 
    qed
    also have "... = ZFfun (Hom\<^bsub>C\<^esub> Z X) (F @@ Y) ((\<lambda>h. (F ## f) |@| h) o (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x))"
    proof(rule ZFfun_ext, rule allI, rule impI, simp)
      {
        fix h assume h: "h |\<in>| (Hom\<^bsub>C\<^esub> Z X)" 
        have zObj: "Z \<in> Obj C" using fmapsb assms by (simp add: Category.MapsToObj)
        hence hmaps: "(z2m\<^bsub>C \<^esub>h) maps\<^bsub>C\<^esub> Z to X" using assms h by (simp add: LSCategory.z2mm2z) 
        hence "(z2m\<^bsub>C \<^esub>h) \<in> Mor C" and "dom\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h) = cod\<^bsub>C\<^esub> f" using fcod by auto
        hence CompDef_hf: "f \<approx>>\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h)" using fmor by auto
        hence CompDef_hfOp: "(z2m\<^bsub>C \<^esub>h) \<approx>>\<^bsub>Op C\<^esub> f" by (simp add: CompDefOp)
        hence CompDef_FhfOp: "(F ## (z2m\<^bsub>C \<^esub>h)) \<approx>>\<^bsub>SET\<^esub> (F ## f)" using assms by (simp add: FunctorCompDef)
        hence "(z2m\<^bsub>C \<^esub>h) maps\<^bsub>Op C\<^esub> X to Z" using hmaps by (simp add: MapsToOp) 
        hence "(F ## (z2m\<^bsub>C \<^esub>h)) maps\<^bsub>SET\<^esub> (F @@ X) to (F @@ Z)" using assms by (simp add: FunctorMapsTo)
        hence xin: "x |\<in>| |dom|(F ## (z2m\<^bsub>C \<^esub>h))" using assms by (simp add: SETmapsTo)
        have "(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h)) \<in> Mor C" using CompDef_hf assms by(simp add: Category.MapsToMorDomCod)
        hence "(F ## (z2m\<^bsub>C \<^esub>(m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))))) |@| x = (F ## (f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))) |@| x" 
          using assms by (simp add: LSCategory.m2zz2mInv)
        also have "... = (F ## ((z2m\<^bsub>C \<^esub>h) ;;\<^bsub>Op C\<^esub> f)) |@| x" by (simp add: OppositeCategory_def)
        also have "... = ((F ## (z2m\<^bsub>C \<^esub>h)) ;;\<^bsub>SET \<^esub>(F ## f)) |@| x" using assms CompDef_hfOp by (simp add: FunctorComp)
        also have "... = (F ## f) |@| ((F ## (z2m\<^bsub>C \<^esub>h)) |@| x)" using CompDef_FhfOp xin by(rule SETCompAt)
        finally show "(F ## (z2m\<^bsub>C \<^esub>(m2z\<^bsub>C \<^esub>(f ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>h))))) |@| x = (F ## f) |@| ((F ## (z2m\<^bsub>C \<^esub>h)) |@| x)" .
      }
    qed
    also have "... = ZFfun (Hom\<^bsub>C\<^esub> Z X) (F @@ Z) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x) |o| 
          ZFfun (F @@ Z) (F @@ Y) (\<lambda>h. (F ## f) |@| h)"
      by(rule ZFfunComp[THEN sym], rule allI, rule impI, simp add: hHomF) 
    also have "... = ZFfun (Hom\<^bsub>C\<^esub> Z X) (F @@ Z) (\<lambda>h. (F ## (z2m\<^bsub>C \<^esub>h)) |@| x) ;;\<^bsub>SET\<^esub> (F ## f)"
      using Ff compdefb by (simp add: SETComp)
    finally show "(((YFtor C) @@ X) ## f) ;;\<^bsub>CatCod F\<^esub> ZFfun (Hom\<^bsub>C\<^esub> Y X) (F @@ Y) (\<lambda>f. (F ## (z2m\<^bsub>C \<^esub>f)) |@| x) =
             ZFfun (Hom\<^bsub>C\<^esub> Z X) (F @@ Z) (\<lambda>f. (F ## (z2m\<^bsub>C \<^esub>f)) |@| x) ;;\<^bsub>CatCod F\<^esub> (F ## f)"
      by(simp add: cf yf hc fdom fcod HomFtorMapContra_def)
  }
qed

lemma YMapInvNatTrans:
  assumes "LSCategory C" and "Ftor F : (Op C) \<longrightarrow> SET" and "X \<in> Obj C" and "x |\<in>| (F @@ X)"
  shows "NatTrans (YMapInv C X F x)"
by (simp add: assms YMapInv_def MakeNT YMapInvNatTransP)

lemma YMapInvImage:
  assumes "LSCategory C" and "Ftor F : (Op C) \<longrightarrow> SET" and "X \<in> Obj C"
  and "x |\<in>| (F @@ X)"
  shows "NT (YMapInv C X F x) : (YFtor C @@ X) \<Longrightarrow> F"
proof(auto simp only: nt_abbrev_def)
  show "NatTrans (YMapInv C X F x)" using assms by (simp add: YMapInvNatTrans)
  show "NTDom (YMapInv C X F x) = YFtor C @@ X" by(simp add: YMapInv_def MakeNT_def YMapInv'_def)
  show "NTCod (YMapInv C X F x) = F" by(simp add: YMapInv_def MakeNT_def YMapInv'_def)
qed

lemma YMap1:
  assumes LSCat: "LSCategory C" and Fftor: "Ftor F : (Op C) \<longrightarrow> SET" and XObj: "X \<in> Obj C"
  and NT: "NT \<eta> : (YFtor C @@ X) \<Longrightarrow> F"
  shows "YMapInv C X F (YMap C X \<eta>) = \<eta>"
proof(rule NatTransExt)
  have "(YMap C X \<eta>) |\<in>| (F @@ X)" using assms by (simp add: YMapImage)
  hence 1: "NT (YMapInv C X F (YMap C X \<eta>)) : (YFtor C @@ X) \<Longrightarrow> F" using assms by (simp add: YMapInvImage)
  thus "NatTrans (YMapInv C X F (YMap C X \<eta>))" by auto
  show "NatTrans \<eta>" using assms by auto
  have NTDYI: "NTDom (YMapInv C X F (YMap C X \<eta>)) = (YFtor C @@ X)" using 1 by auto
  moreover have NTDeta: "NTDom \<eta> = (YFtor C @@ X)" using assms by auto
  ultimately show "NTDom (YMapInv C X F (YMap C X \<eta>)) = NTDom \<eta>" by simp
  have "NTCod (YMapInv C X F (YMap C X \<eta>)) = F" using 1 by auto
  moreover have NTCeta: "NTCod \<eta> = F" using assms by auto
  ultimately show "NTCod (YMapInv C X F (YMap C X \<eta>)) = NTCod \<eta>" by simp
  {
    fix Y assume Yobja: "Y \<in> Obj (NTCatDom (YMapInv C X F (YMap C X \<eta>)))"
    have CCF: "CatCod F = SET" using assms by auto
    have "Ftor (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) : (Op C) \<longrightarrow> SET" using LSCat XObj by (simp add: HomFtorContraFtor)
    hence CDH: "CatDom (Hom\<^bsub>C\<^esub>[\<midarrow>,X]) = Op C" by auto
    hence CDYF: "CatDom (YFtor C @@ X) = Op C" using XObj LSCat by (auto simp add: YFtorObj)
    hence "NTCatDom (YMapInv C X F (YMap C X \<eta>)) = Op C" using LSCat XObj NTDYI CDH  by (simp add: NTCatDom_def)
    hence YObjOp: "Y \<in> Obj (Op C)" using Yobja by simp
    hence YObj: "Y \<in> Obj C" and XObjOp: "X \<in> Obj (Op C)" using XObj by (simp add: OppositeCategory_def)+
    have yinv_mapsTo: "((YMapInv C X F (YMap C X \<eta>)) $$ Y) maps\<^bsub>SET\<^esub> (Hom\<^bsub>C \<^esub>Y X) to (F @@ Y)" 
    proof-
      have "((YMapInv C X F (YMap C X \<eta>)) $$ Y) maps\<^bsub>SET\<^esub> ((YFtor C @@ X) @@ Y) to (F @@ Y)" 
        using 1 CCF CDYF YObjOp NatTransMapsTo[of "(YMapInv C X F (YMap C X \<eta>))" "(YFtor C @@ X)" F Y] by simp
      thus ?thesis using LSCat XObj YObj by (simp add: YFtorObj2)
    qed
    have eta_mapsTo: "(\<eta> $$ Y) maps\<^bsub>SET\<^esub> (Hom\<^bsub>C \<^esub>Y X) to (F @@ Y)" 
    proof-
      have "(\<eta> $$ Y) maps\<^bsub>SET\<^esub> ((YFtor C @@ X) @@ Y) to (F @@ Y)" 
        using NT CDYF CCF YObjOp NatTransMapsTo[of \<eta> "(YFtor C @@ X)" F Y] by simp
      thus ?thesis using LSCat XObj YObj by (simp add: YFtorObj2)
    qed
    show "(YMapInv C X F (YMap C X \<eta>)) $$ Y = \<eta> $$ Y"
    proof(rule ZFfunExt)
      show "|dom|(YMapInv C X F (YMap C X \<eta>) $$ Y) = |dom|(\<eta> $$ Y)"  
        using yinv_mapsTo eta_mapsTo by (simp add: SETmapsTo)
      show "|cod|(YMapInv C X F (YMap C X \<eta>) $$ Y) = |cod|(\<eta> $$ Y)" 
        using yinv_mapsTo eta_mapsTo by (simp add: SETmapsTo)
      show "isZFfun (YMapInv C X F (YMap C X \<eta>) $$ Y)" 
        using yinv_mapsTo by (simp add: SETmapsTo)
      show "isZFfun (\<eta> $$ Y)" 
        using eta_mapsTo by (simp add: SETmapsTo)
      {
        fix f assume fdomYinv: "f |\<in>| |dom|(YMapInv C X F (YMap C X \<eta>) $$ Y)"
        have fHom: "f |\<in>| (Hom\<^bsub>C\<^esub> Y X)" using yinv_mapsTo fdomYinv by (simp add: SETmapsTo)
        hence fMapsTo: "(z2m\<^bsub>C \<^esub>f) maps\<^bsub>C \<^esub>Y to X" using assms YObj by (simp add: LSCategory.z2mm2z)
        hence fCod: "(cod\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>f)) = X" and fDom: "(dom\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>f)) = Y" and fMor: "(z2m\<^bsub>C \<^esub>f) \<in> Mor C" by auto
        have "(YMapInv C X F (YMap C X \<eta>) $$ Y) |@| f = 
              (F ## (z2m\<^bsub>C \<^esub>f)) |@| ((\<eta> $$ X) |@| (m2z\<^bsub>C \<^esub>(Id C X)))" 
          using fHom assms YObj by (simp add: ZFfunApp YMapInvApp YMap_def)
        also have "... = ((\<eta> $$ X) ;;\<^bsub>SET\<^esub> (F ## (z2m\<^bsub>C \<^esub>f))) |@| (m2z\<^bsub>C \<^esub>(Id C X))" 
        proof-
          have aa: "(\<eta> $$ X) maps\<^bsub>SET\<^esub> ((YFtor C @@ X) @@ X) to (F @@ X)" 
            using NT CDYF CCF YObjOp XObjOp NatTransMapsTo[of \<eta> "(YFtor C @@ X)" F X] by simp
          have bb: "(F ## (z2m\<^bsub>C \<^esub>f)) maps\<^bsub>SET\<^esub> (F @@ X) to (F @@ Y)" 
            using fMapsTo Fftor by (simp add: MapsToOp FunctorMapsTo)
          have "(\<eta> $$ X) \<approx>>\<^bsub>SET\<^esub> (F ## (z2m\<^bsub>C \<^esub>f))" using aa bb by (simp add: MapsToCompDef)
          moreover have "(m2z\<^bsub>C \<^esub>(Id C X)) |\<in>| |dom| (\<eta> $$ X)" using assms aa 
            by (simp add: SETmapsTo YFtorObj2 Category.Cidm LSCategory.m2zz2m)
          ultimately show ?thesis by (simp add: SETCompAt)
        qed
        also have "... = ((HomC\<^bsub>C\<^esub>[z2m\<^bsub>C \<^esub>f,X]) ;;\<^bsub>SET\<^esub> (\<eta> $$ Y)) |@| (m2z\<^bsub>C \<^esub>(Id C X))" 
        proof-
          have "NTDom \<eta> = (Hom\<^bsub>C\<^esub>[\<midarrow>,X])" using NTDeta assms by (simp add: YFtorObj)
          moreover hence "NTCatDom \<eta> = Op C" by (simp add: NTCatDom_def HomFtorContraDom)
          moreover have "NTCatCod \<eta> = SET" using assms by (auto simp add: NTCatCod_def)
          moreover have "NatTrans \<eta>" and "NTCod \<eta> = F" using assms by auto
          moreover have "(z2m\<^bsub>C \<^esub>f) maps\<^bsub>Op C \<^esub>X to Y" 
            using fMapsTo MapsToOp[where ?f = "(z2m\<^bsub>C \<^esub>f)" and ?X = Y and ?Y = X and ?C = C] by simp
          ultimately have "(\<eta> $$ X) ;;\<^bsub>SET\<^esub> (F ## (z2m\<^bsub>C \<^esub>f)) = ((Hom\<^bsub>C\<^esub>[\<midarrow>,X]) ## (z2m\<^bsub>C \<^esub>f)) ;;\<^bsub>SET\<^esub> (\<eta> $$ Y)"
            using NatTransP.NatTrans[of \<eta> "(z2m\<^bsub>C \<^esub>f)" X Y] by simp
          moreover have "((Hom\<^bsub>C\<^esub>[\<midarrow>,X]) ## (z2m\<^bsub>C \<^esub>f)) = (HomC\<^bsub>C\<^esub>[(z2m\<^bsub>C \<^esub>f),X])" using assms fMor by (simp add: HomContraMor)
          ultimately show ?thesis by simp
        qed
        also have "... = (\<eta> $$ Y) |@| ((HomC\<^bsub>C\<^esub>[z2m\<^bsub>C \<^esub>f,X]) |@| (m2z\<^bsub>C \<^esub>(Id C X)))" 
        proof-
          have "(HomC\<^bsub>C\<^esub>[z2m\<^bsub>C \<^esub>f,X]) \<approx>>\<^bsub>SET\<^esub> (\<eta> $$ Y)" 
            using fCod fDom XObj LSCat fMor HomFtorContraMapsTo[of C X "z2m\<^bsub>C \<^esub>f"] eta_mapsTo by (simp add: MapsToCompDef)
          moreover have "|dom| (HomC\<^bsub>C\<^esub>[z2m\<^bsub>C \<^esub>f,X]) = (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>f)) X)" 
            by (simp add: ZFfunDom HomFtorMapContra_def)
          moreover have "(m2z\<^bsub>C \<^esub>(Id C X)) |\<in>| (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>f)) X)" 
            using assms fCod by (simp add: Category.Cidm LSCategory.m2zz2m)
          ultimately show ?thesis by (simp add: SETCompAt)
        qed
        also have "... = (\<eta> $$ Y) |@| (m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C \<^esub>f) ;;\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> (m2z\<^bsub>C \<^esub>(Id C X)))))" 
        proof-
          have "(Id C X) maps\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>f)) to X" using assms fCod by (simp add: Category.Cidm)
          hence "(m2z\<^bsub>C \<^esub>(Id C X)) |\<in>| (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>f)) X)" using assms by (simp add: LSCategory.m2zz2m)
          thus ?thesis by (simp add: HomContraAt)
        qed
        also have "... = (\<eta> $$ Y) |@| (m2z\<^bsub>C\<^esub> ((z2m\<^bsub>C \<^esub>f) ;;\<^bsub>C\<^esub> (Id C X)))" 
          using assms by (simp add: LSCategory.m2zz2mInv Category.CatIdInMor)
        also have "... = (\<eta> $$ Y) |@| (m2z\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>f))" using assms(1) fCod fMor Category.Cidr[of C "(z2m\<^bsub>C \<^esub>f)"] by (simp)
        also have "... = (\<eta> $$ Y) |@| f" using assms YObj fHom by (simp add: LSCategory.z2mm2z)
        finally show "(YMapInv C X F (YMap C X \<eta>) $$ Y) |@| f = (\<eta> $$ Y) |@| f" .
      }
    qed
  }
qed

lemma YMap2:
  assumes "LSCategory C" and "Ftor F : (Op C) \<longrightarrow> SET" and "X \<in> Obj C"
  and "x |\<in>| (F @@ X)"
  shows "YMap C X (YMapInv C X F x) = x"
proof(simp only: YMap_def)
  let ?\<eta> = "(YMapInv C X F x)"
  have "(?\<eta> $$ X) = ZFfun (Hom\<^bsub>C\<^esub> X X) (F @@ X) (\<lambda> f . (F ## (z2m\<^bsub>C\<^esub> f)) |@| x)" using assms by (simp add: YMapInvApp)
  moreover have "(m2z\<^bsub>C \<^esub>(Id C X)) |\<in>| (Hom\<^bsub>C\<^esub> X X)" using assms by (simp add: Category.Simps LSCategory.m2zz2m)
  ultimately have "(?\<eta> $$ X) |@| (m2z\<^bsub>C \<^esub>(Id C X)) = (F ## (z2m\<^bsub>C\<^esub> (m2z\<^bsub>C \<^esub>(Id C X)))) |@| x" 
    by (simp add: ZFfunApp)
  also have "... = (F ## (Id C X)) |@| x" using assms by (simp add: Category.CatIdInMor LSCategory.m2zz2mInv)
  also have "... = (Id SET (F @@ X)) |@| x" 
  proof-
    have "X \<in> Obj (Op C)" using assms by (auto simp add: OppositeCategory_def)
    hence "(F ## (Id (Op C) X)) = (Id SET (F @@ X))" 
      using assms by(simp add: FunctorId)
    moreover have "(Id (Op C) X) = (Id C X)" using assms by (auto simp add: OppositeCategory_def)
    ultimately show ?thesis by simp
  qed
  also have "... = x" using assms by (simp add: SETId)
  finally show "(?\<eta> $$ X) |@| (m2z\<^bsub>C \<^esub>(Id C X)) = x" .
qed

lemma YFtorNT_YMapInv:
  assumes "LSCategory C" and "f maps\<^bsub>C\<^esub> X to Y"
  shows "YFtorNT C f = YMapInv C X (Hom\<^bsub>C\<^esub>[\<midarrow>,Y]) (m2z\<^bsub>C\<^esub> f)"
proof(simp only: YFtorNT_def YMapInv_def, rule NatTransExt')
  have Cf: "cod\<^bsub>C\<^esub> f = Y" and Df: "dom\<^bsub>C\<^esub> f = X" using assms by auto
  thus "NTCod (YFtorNT' C f) = NTCod (YMapInv' C X (Hom\<^bsub>C\<^esub>[\<midarrow>,Y]) (m2z\<^bsub>C\<^esub>f))"
    by(simp add: YFtorNT'_def YMapInv'_def )
  have "Hom\<^bsub>C\<^esub>[\<midarrow>,dom\<^bsub>C\<^esub> f] = YFtor C @@ X" using Df assms by (simp add: YFtorObj Category.MapsToObj)
  thus "NTDom (YFtorNT' C f) = NTDom (YMapInv' C X (Hom\<^bsub>C\<^esub>[\<midarrow>,Y]) (m2z\<^bsub>C\<^esub>f))"
    by(simp add: YFtorNT'_def YMapInv'_def )
  {
    fix Z assume ObjZ1: "Z \<in> Obj (NTCatDom (YFtorNT' C f))"
    have ObjZ2: "Z \<in> Obj C" using ObjZ1 by (simp add: YFtorNT'_def NTCatDom_def OppositeCategory_def HomFtorContraDom) 
    moreover have ObjX: "X \<in> Obj C" and ObjY: "Y \<in> Obj C" using assms by (simp add: Category.MapsToObj)+
    moreover 
    {
      fix x assume x: "x |\<in>| (Hom\<^bsub>C\<^esub> Z X)"
      have "m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> f) = ((Hom\<^bsub>C\<^esub>[\<midarrow>,Y]) ## (z2m\<^bsub>C \<^esub>x)) |@| (m2z\<^bsub>C\<^esub>f)"
      proof-
        have morf: "f \<in> Mor C" using assms by auto
        have mapsx: "(z2m\<^bsub>C \<^esub>x) maps\<^bsub>C\<^esub> Z to X" using x assms(1) ObjZ2 ObjX by (simp add: LSCategory.z2mm2z)
        hence morx: "(z2m\<^bsub>C \<^esub>x) \<in> Mor C" by auto
        hence "(Hom\<^bsub>C\<^esub>[\<midarrow>,Y]) ## (z2m\<^bsub>C \<^esub>x) = (HomC\<^bsub>C\<^esub>[(z2m\<^bsub>C \<^esub>x),Y])" using assms by (simp add: HomContraMor)
        moreover have "(HomC\<^bsub>C\<^esub>[(z2m\<^bsub>C \<^esub>x),Y]) |@| (m2z\<^bsub>C \<^esub>f) = m2z\<^bsub>C \<^esub>((z2m\<^bsub>C \<^esub>x) ;;\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>(m2z\<^bsub>C \<^esub>f)))"
        proof (rule HomContraAt)
          have "cod\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>x) = X" using mapsx by auto
          thus "(m2z\<^bsub>C \<^esub>f) |\<in>| (Hom\<^bsub>C\<^esub> (cod\<^bsub>C\<^esub> (z2m\<^bsub>C \<^esub>x)) Y)" using assms by (simp add: LSCategory.m2zz2m)
        qed
        moreover have "(z2m\<^bsub>C \<^esub>(m2z\<^bsub>C \<^esub>f)) = f" using assms morf by (simp add: LSCategory.m2zz2mInv) 
        ultimately show ?thesis by simp
      qed
    }
    ultimately show "(YFtorNT' C f) $$ Z = (YMapInv' C X (Hom\<^bsub>C\<^esub>[\<midarrow>,Y]) (m2z\<^bsub>C\<^esub>f)) $$ Z" using Cf Df assms
      apply(simp add: YFtorNT'_def YMapInv'_def HomFtorMap_def HomFtorOpObj)
      apply(rule ZFfun_ext, rule allI, rule impI, simp)
      done
  }
qed

lemma YMapYoneda:
  assumes "LSCategory C" and "f maps\<^bsub>C\<^esub> X to Y"
  shows "YFtor C ## f = YMapInv C X (YFtor C @@ Y) (m2z\<^bsub>C\<^esub> f)"
proof-
  have "f \<in> Mor C" using assms by auto
  moreover have "Y \<in> Obj C" using assms by (simp add: Category.MapsToObj)
  moreover have "YFtorNT C f = YMapInv C X (Hom\<^bsub>C\<^esub>[\<midarrow>,Y]) (m2z\<^bsub>C\<^esub> f)" using assms by (simp add: YFtorNT_YMapInv)
  ultimately show ?thesis using assms by (simp add: YFtorMor YFtorObj)
qed

lemma YonedaFull: 
  assumes "LSCategory C" and "X \<in> Obj C" and "Y \<in> Obj C"
  and "NT \<eta> : (YFtor C @@ X) \<Longrightarrow> (YFtor C @@ Y)"
  shows "YFtor C ## (z2m\<^bsub>C\<^esub> (YMap C X \<eta>)) = \<eta>"
  and "z2m\<^bsub>C\<^esub> (YMap C X \<eta>) maps\<^bsub>C\<^esub> X to Y"
proof-
  have ftor: "Ftor (YFtor C @@ Y) : (Op C) \<longrightarrow> SET" using assms by (simp add: YFtorObj HomFtorContraFtor)
  hence "(YMap C X \<eta>) |\<in>| ((YFtor C @@ Y) @@ X)" using assms by (simp add: YMapImage)
  hence yh: "(YMap C X \<eta>) |\<in>| (Hom\<^bsub>C\<^esub> X Y)" using assms by (simp add: YFtorObj2)
  thus "(z2m\<^bsub>C\<^esub> (YMap C X \<eta>)) maps\<^bsub>C\<^esub> X to Y" using assms by (simp add: LSCategory.z2mm2z)
  hence "YFtor C ## (z2m\<^bsub>C\<^esub> (YMap C X \<eta>)) = YMapInv C X (YFtor C @@ Y) (m2z\<^bsub>C\<^esub> (z2m\<^bsub>C\<^esub> (YMap C X \<eta>)))"
    using assms yh by (simp add: YMapYoneda)
  also have "... = YMapInv C X (YFtor C @@ Y) (YMap C X \<eta>)" 
    using assms yh by (simp add: LSCategory.z2mm2z)
  finally show "YFtor C ## (z2m\<^bsub>C\<^esub> (YMap C X \<eta>)) = \<eta>" using assms ftor by (simp add: YMap1)
qed

lemma YonedaFaithful:
  assumes "LSCategory C" and "f maps\<^bsub>C\<^esub> X to Y" and "g maps\<^bsub>C\<^esub> X to Y"
  and "YFtor C ## f = YFtor C ## g"
  shows "f = g"
proof-
  have ObjX: "X \<in> Obj C" and ObjY: "Y \<in> Obj C" using assms by (simp add: Category.MapsToObj)+
  have M2Zf: "(m2z\<^bsub>C\<^esub> f) |\<in>| ((YFtor C @@ Y) @@ X)" and M2Zg: "(m2z\<^bsub>C\<^esub> g) |\<in>| ((YFtor C @@ Y) @@ X)"
    using assms ObjX ObjY by (simp add: LSCategory.m2zz2m YFtorObj2)+
  have Ftor: "Ftor (YFtor C @@ Y) : (Op C) \<longrightarrow> SET" using assms ObjY by (simp add: YFtorObj HomFtorContraFtor)
  have Morf: "f \<in> Mor C" and Morg: "g \<in> Mor C" using assms by auto
  have "YMapInv C X (YFtor C @@ Y) (m2z\<^bsub>C\<^esub> f) = YMapInv C X (YFtor C @@ Y) (m2z\<^bsub>C\<^esub> g)"
    using assms by (simp add: YMapYoneda)
  hence "YMap C X (YMapInv C X (YFtor C @@ Y) (m2z\<^bsub>C\<^esub> f)) = YMap C X (YMapInv C X (YFtor C @@ Y) (m2z\<^bsub>C\<^esub> g))"
    by simp
  hence "(m2z\<^bsub>C\<^esub> f) = (m2z\<^bsub>C\<^esub> g)" using assms ObjX ObjY M2Zf M2Zg Ftor by (simp add: YMap2)
  thus "f = g" using assms Morf Morg by (simp add: LSCategory.mor2ZFInj)
qed

lemma YonedaEmbedding:
  assumes "LSCategory C" and "A \<in> Obj C" and "B \<in> Obj C" and "(YFtor C) @@ A = (YFtor C) @@ B"
  shows "A = B"
proof-
  have AObjOp: "A \<in> Obj (Op C)" and BObjOp: "B \<in> Obj (Op C)" using assms by (simp add: OppositeCategory_def)+
  hence FtorA: "Ftor (Hom\<^bsub>C\<^esub>[\<midarrow>,A]) : (Op C) \<longrightarrow> SET" and FtorB: "Ftor (Hom\<^bsub>C\<^esub>[\<midarrow>,B]) : (Op C) \<longrightarrow> SET" 
    using assms by (simp add: HomFtorContraFtor)+
  have "Hom\<^bsub>C\<^esub>[\<midarrow>,A] = Hom\<^bsub>C\<^esub>[\<midarrow>,B]" using assms by (simp add: YFtorObj)
  hence "(Hom\<^bsub>C\<^esub>[\<midarrow>,A]) ## (Id (Op C) A) = (Hom\<^bsub>C\<^esub>[\<midarrow>,B]) ## (Id (Op C) A)" by simp
  hence "Id SET ((Hom\<^bsub>C\<^esub>[\<midarrow>,A]) @@ A) = Id SET ((Hom\<^bsub>C\<^esub>[\<midarrow>,B]) @@ A)" 
    using AObjOp BObjOp FtorA FtorB by (simp add: FunctorId)
  hence "Id SET (Hom\<^bsub>C \<^esub>A A) = Id SET (Hom\<^bsub>C \<^esub>A B)" using assms by (simp add: HomFtorOpObj)
  hence "Hom\<^bsub>C \<^esub>A A = Hom\<^bsub>C \<^esub>A B" using SETCategory by (simp add: Category.IdInj SETobj[of "Hom\<^bsub>C \<^esub>A A"] SETobj[of "Hom\<^bsub>C \<^esub>A B"])
  moreover have "(m2z\<^bsub>C\<^esub> (Id C A)) |\<in>| (Hom\<^bsub>C \<^esub>A A)" using assms by (simp add: Category.Cidm LSCategory.m2zz2m)
  ultimately have "(m2z\<^bsub>C\<^esub> (Id C A)) |\<in>| (Hom\<^bsub>C \<^esub>A B)" by simp
  hence "(z2m\<^bsub>C\<^esub> (m2z\<^bsub>C\<^esub> (Id C A))) maps\<^bsub>C\<^esub> A to B" using assms by (simp add: LSCategory.z2mm2z)
  hence "(Id C A) maps\<^bsub>C\<^esub> A to B" using assms by (simp add: Category.CatIdInMor LSCategory.m2zz2mInv)
  hence "cod\<^bsub>C\<^esub> (Id C A) = B" by auto
  thus ?thesis using assms by (simp add: Category.CatIdDomCod)
qed

end
