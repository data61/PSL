(*
Author: Alexander Katovsky
*)

section "Monadic Equational Theory"

theory MonadicEquationalTheory
imports Category Universe
begin

record ('t,'f) Signature = 
  BaseTypes :: "'t set" ("Ty\<index>")
  BaseFunctions :: "'f set" ("Fn\<index>")
  SigDom :: "'f \<Rightarrow> 't" ("sDom\<index>")
  SigCod :: "'f \<Rightarrow> 't" ("sCod\<index>")

locale Signature = 
  fixes S :: "('t,'f) Signature" (structure)
  assumes Domt: "f \<in> Fn \<Longrightarrow> sDom f \<in> Ty"
  and     Codt: "f \<in> Fn \<Longrightarrow> sCod f \<in> Ty"

definition funsignature_abbrev ("_ \<in> Sig _ : _ \<rightarrow> _" ) where
  "f \<in> Sig S : A \<rightarrow> B \<equiv> f \<in> (BaseFunctions S) \<and> A \<in> (BaseTypes S) \<and> B \<in> (BaseTypes S) \<and> 
                        (SigDom S f) = A \<and> (SigCod S f) = B \<and> Signature S"

lemma funsignature_abbrevE[elim]: 
"\<lbrakk>f \<in> Sig S : A \<rightarrow> B ; \<lbrakk>f \<in> (BaseFunctions S) ; A \<in> (BaseTypes S) ; B \<in> (BaseTypes S) ; 
                        (SigDom S f) = A ; (SigCod S f) = B ; Signature S\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by (simp add: funsignature_abbrev_def)

datatype ('t,'f) Expression = ExprVar ("Vx") | ExprApp 'f "('t,'f) Expression" ("_ E@ _")
datatype ('t,'f) Language = Type 't ("\<turnstile> _ Type") | Term 't "('t,'f) Expression" 't ("Vx : _ \<turnstile> _ : _") | 
                            Equation 't "('t,'f) Expression" "('t,'f) Expression" 't ("Vx : _ \<turnstile> _\<equiv>_ : _")

inductive
  WellDefined :: "('t,'f) Signature \<Rightarrow> ('t,'f) Language \<Rightarrow> bool" ("Sig _ \<triangleright> _") where
    WellDefinedTy: "A \<in> BaseTypes S \<Longrightarrow> Sig S \<triangleright> \<turnstile> A Type"
  | WellDefinedVar: "Sig S \<triangleright> \<turnstile> A Type \<Longrightarrow> Sig S \<triangleright> (Vx : A  \<turnstile> Vx : A)" 
  | WellDefinedFn: "\<lbrakk>Sig S \<triangleright> (Vx : A  \<turnstile> e : B)  ; f \<in> Sig S : B \<rightarrow> C\<rbrakk> \<Longrightarrow> Sig S \<triangleright> (Vx : A  \<turnstile> (f E@ e) : C)"
  | WellDefinedEq: "\<lbrakk>Sig S \<triangleright> (Vx : A  \<turnstile> e1 : B) ; Sig S \<triangleright> (Vx : A  \<turnstile> e2 : B)\<rbrakk> \<Longrightarrow> Sig S \<triangleright> (Vx : A \<turnstile> e1 \<equiv> e2 : B)"

lemmas WellDefined.intros [intro]
inductive_cases WellDefinedTyE [elim!]: "Sig S \<triangleright> \<turnstile> A Type"
inductive_cases WellDefinedVarE [elim!]: "Sig S \<triangleright> (Vx : A  \<turnstile> Vx : A)"
inductive_cases WellDefinedFnE [elim!]: "Sig S \<triangleright> (Vx : A  \<turnstile> (f E@ e) : C)"
inductive_cases WellDefinedEqE [elim!]: "Sig S \<triangleright> (Vx : A \<turnstile> e1 \<equiv> e2 : B)"

lemma SigId: "Sig S \<triangleright> (Vx : A  \<turnstile> Vx : B) \<Longrightarrow> A = B"
apply(rule WellDefined.cases)
by simp+

lemma SigTyId: "Sig S \<triangleright> (Vx : A  \<turnstile> Vx : A) \<Longrightarrow> A \<in> BaseTypes S"
apply(rule WellDefined.cases)
by auto

lemma (in Signature) SigTy: "\<And> B . Sig S \<triangleright> (Vx : A  \<turnstile> e : B) \<Longrightarrow> (A \<in> BaseTypes S \<and> B \<in> BaseTypes S)"
proof(induct e)
  {
    fix B assume a: "Sig S \<triangleright> Vx : A \<turnstile> Vx : B"
    have "A = B" using a SigId[of S] by simp
    thus "A \<in> Ty \<and> B \<in> Ty" using a by auto
  }
  {
    fix B f e assume ih: "\<And>B'. Sig S \<triangleright> (Vx : A \<turnstile> e : B') \<Longrightarrow> A \<in> Ty \<and> B' \<in> Ty"
    and a: "Sig S \<triangleright> (Vx : A \<turnstile> (f E@ e) : B)"
    from a obtain B' where f: "f \<in> Sig S : B' \<rightarrow> B" and "Sig S \<triangleright> (Vx : A \<turnstile> e : B')" by auto
    hence "A \<in> Ty" using ih by auto
    moreover have "B \<in> Ty" using f by (auto simp add: funsignature_abbrev_def Codt)
    ultimately show "A \<in> Ty \<and> B \<in> Ty" by simp
  }
qed

(*An interpretation is an object, a morphism or a boolean*)
datatype ('o,'m) IType = IObj 'o | IMor 'm | IBool bool

record ('t,'f,'o,'m) Interpretation = 
  ISignature :: "('t,'f) Signature" ("iS\<index>")
  ICategory  :: "('o,'m) Category"  ("iC\<index>")
  ITypes     :: "'t \<Rightarrow> 'o" ("Ty\<lbrakk>_\<rbrakk>\<index>")
  IFunctions :: "'f \<Rightarrow> 'm" ("Fn\<lbrakk>_\<rbrakk>\<index>")

locale Interpretation = 
  fixes I :: "('t,'f,'o,'m) Interpretation" (structure)
  assumes ICat: "Category  iC"
  and     ISig: "Signature iS" 
  and     It  : "A \<in> BaseTypes iS \<Longrightarrow> Ty\<lbrakk>A\<rbrakk> \<in> Obj iC"
  and     If  : "(f \<in> Sig iS : A \<rightarrow> B) \<Longrightarrow> Fn\<lbrakk>f\<rbrakk> maps\<^bsub>iC\<^esub> Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>"

inductive Interp  ("L\<lbrakk>_\<rbrakk>\<index> \<rightarrow> _") where
    InterpTy: "Sig iS\<^bsub>I\<^esub> \<triangleright> \<turnstile> A Type \<Longrightarrow> 
                       L\<lbrakk>\<turnstile> A Type\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IObj Ty\<lbrakk>A\<rbrakk>\<^bsub>I\<^esub>)"
  | InterpVar: "L\<lbrakk>\<turnstile> A Type\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IObj c) \<Longrightarrow> 
                       L\<lbrakk>Vx : A  \<turnstile> Vx : A\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IMor (Id iC\<^bsub>I\<^esub> c))" 
  | InterpFn: "\<lbrakk>Sig iS\<^bsub>I\<^esub> \<triangleright> Vx : A  \<turnstile> e : B ; 
               f \<in> Sig iS\<^bsub>I\<^esub> : B \<rightarrow> C ; 
               L\<lbrakk>Vx : A  \<turnstile> e : B\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IMor g)\<rbrakk> \<Longrightarrow> 
               L\<lbrakk>Vx : A  \<turnstile> (f E@ e) : C\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IMor (g ;;\<^bsub>ICategory I\<^esub> Fn\<lbrakk>f\<rbrakk>\<^bsub>I\<^esub>))"
  | InterpEq: "\<lbrakk>L\<lbrakk>Vx : A  \<turnstile> e1 : B\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IMor g1) ; 
                L\<lbrakk>Vx : A  \<turnstile> e2 : B\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IMor g2)\<rbrakk> \<Longrightarrow> 
                L\<lbrakk>Vx : A  \<turnstile> e1 \<equiv> e2 : B\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IBool (g1 = g2))"

lemmas  Interp.intros [intro]
inductive_cases  InterpTyE [elim!]: "L\<lbrakk>\<turnstile> A Type\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> i"
inductive_cases  InterpVarE [elim!]: "L\<lbrakk>Vx : A  \<turnstile> Vx : A\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> i"
inductive_cases  InterpFnE [elim!]: "L\<lbrakk>Vx : A  \<turnstile> (f E@ e) : C\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> i"
inductive_cases  InterpEqE [elim!]: "L\<lbrakk>Vx : A  \<turnstile> e1 \<equiv> e2 : B\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> i"

lemma (in Interpretation) InterpEqEq[intro]: 
  "\<lbrakk>L\<lbrakk>Vx : A  \<turnstile> e1 : B\<rbrakk> \<rightarrow> (IMor g) ; L\<lbrakk>Vx : A  \<turnstile> e2 : B\<rbrakk> \<rightarrow> (IMor g)\<rbrakk> \<Longrightarrow> L\<lbrakk>Vx : A  \<turnstile> e1 \<equiv> e2 : B\<rbrakk> \<rightarrow> (IBool True)"
proof-
  assume a: "L\<lbrakk>Vx : A  \<turnstile> e1 : B\<rbrakk> \<rightarrow> (IMor g)" and b: "L\<lbrakk>Vx : A  \<turnstile> e2 : B\<rbrakk> \<rightarrow> (IMor g)"
  thus ?thesis using InterpEq[of I A e1 B g e2 g] by simp
qed

lemma (in Interpretation) InterpExprWellDefined:
"L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk> \<rightarrow> i \<Longrightarrow> Sig iS \<triangleright> Vx : A  \<turnstile> e : B"
apply (rule Interp.cases)
by auto

lemma (in Interpretation) WellDefined: "L\<lbrakk>\<phi>\<rbrakk> \<rightarrow> i \<Longrightarrow> Sig iS \<triangleright> \<phi>"
apply(rule Interp.cases)
by (auto simp add: InterpExprWellDefined)

lemma (in Interpretation) Bool: "L\<lbrakk>\<phi>\<rbrakk> \<rightarrow> (IBool i) \<Longrightarrow> \<exists> A B e d . \<phi> = (Vx : A \<turnstile> e \<equiv> d : B)"
apply(rule Interp.cases)
by auto

lemma (in Interpretation) FunctionalExpr:
"\<And>i j A B.\<lbrakk>L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk> \<rightarrow> i; L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk> \<rightarrow> j\<rbrakk> \<Longrightarrow> i = j"
apply (induct e)
apply (rule Interp.cases)
apply auto
apply (auto simp add: funsignature_abbrev_def)
done

lemma (in Interpretation) Functional: "\<lbrakk>L\<lbrakk>\<phi>\<rbrakk> \<rightarrow> i1 ; L\<lbrakk>\<phi>\<rbrakk> \<rightarrow> i2\<rbrakk> \<Longrightarrow> i1 = i2"
proof(induct \<phi>)
  {
    fix t show "\<lbrakk>L\<lbrakk>\<turnstile> t Type\<rbrakk> \<rightarrow> i1 ; L\<lbrakk>\<turnstile> t Type\<rbrakk> \<rightarrow> i2\<rbrakk> \<Longrightarrow> i1 = i2" by auto
  }
  {
    fix t1 t2 e 
    show "\<lbrakk>L\<lbrakk>Vx : t1 \<turnstile> e : t2\<rbrakk> \<rightarrow> i1; L\<lbrakk>Vx : t1 \<turnstile> e : t2\<rbrakk> \<rightarrow> i2\<rbrakk> \<Longrightarrow> i1 = i2" by (simp add: FunctionalExpr)
  }
  {
    fix t1 t2 e1 e2 show "\<lbrakk>L\<lbrakk>Vx : t1 \<turnstile> e1 \<equiv> e2 : t2\<rbrakk> \<rightarrow> i1; L\<lbrakk>Vx : t1 \<turnstile> e1 \<equiv> e2 : t2\<rbrakk> \<rightarrow> i2\<rbrakk> \<Longrightarrow> i1 = i2" 
    proof(auto)
      {
        fix f g h assume f1: "L\<lbrakk>Vx : t1 \<turnstile> e1 : t2\<rbrakk> \<rightarrow> (IMor f)" and f2: "L\<lbrakk>Vx : t1 \<turnstile> e2 : t2\<rbrakk> \<rightarrow> (IMor f)"
          and g1: "L\<lbrakk>Vx : t1 \<turnstile> e1 : t2\<rbrakk> \<rightarrow> (IMor g)" and g2: "L\<lbrakk>Vx : t1 \<turnstile> e2 : t2\<rbrakk> \<rightarrow> (IMor h)"
        have "f = g" using f1 g1 FunctionalExpr[of t1 e1 t2 "IMor f" "IMor g"] by simp
        moreover have "f = h" using f2 g2 FunctionalExpr[of t1 e2 t2 "IMor f" "IMor h"] by simp
        ultimately show "g = h" by simp
      }
      moreover 
      {
        fix f g h assume f1: "L\<lbrakk>Vx : t1 \<turnstile> e1 : t2\<rbrakk> \<rightarrow> (IMor f)" and f2: "L\<lbrakk>Vx : t1 \<turnstile> e2 : t2\<rbrakk> \<rightarrow> (IMor g)"
          and g1: "L\<lbrakk>Vx : t1 \<turnstile> e1 : t2\<rbrakk> \<rightarrow> (IMor h)" and g2: "L\<lbrakk>Vx : t1 \<turnstile> e2 : t2\<rbrakk> \<rightarrow> (IMor h)"
        have "f = h" using f1 g1 FunctionalExpr[of t1 e1 t2 "IMor f" "IMor h"] by simp
        moreover have "g = h" using f2 g2 FunctionalExpr[of t1 e2 t2 "IMor g" "IMor h"] by simp
        ultimately show "f = g" by simp
      }
    qed 
  }
qed

lemma (in Interpretation) MorphismsPreserved:
"\<And> B i . L\<lbrakk>Vx : A  \<turnstile> e : B\<rbrakk> \<rightarrow> i \<Longrightarrow> \<exists> g . i = (IMor g) \<and> (g maps\<^bsub>iC \<^esub>Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>)"
proof(induct e)
  {
    fix B i assume a: "L\<lbrakk>Vx : A \<turnstile> Vx : B\<rbrakk> \<rightarrow> i" show "\<exists> g. i = IMor g \<and> g maps\<^bsub>iC\<^esub> Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>"
    proof(rule exI[where ?x="Id iC Ty\<lbrakk>A\<rbrakk>"], rule conjI)
      have sig: "Sig iS \<triangleright> Vx : A  \<turnstile> Vx : B" using a by (simp add: InterpExprWellDefined) 
      hence aEqb: "A = B" by (simp add: SigId)
      have ty: "A \<in> BaseTypes iS" using aEqb sig SigTyId by simp
      hence "L\<lbrakk>Vx : A \<turnstile> Vx : A\<rbrakk> \<rightarrow> (IMor (Id iC Ty\<lbrakk>A\<rbrakk>))" by auto
      thus "i = IMor (Category.Id iC Ty\<lbrakk>A\<rbrakk>)" using a aEqb Functional by simp
      show "(Id iC Ty\<lbrakk>A\<rbrakk>) maps\<^bsub>iC\<^esub> Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>" using aEqb ICat It[of A] Category.Cidm[of iC "Ty\<lbrakk>A\<rbrakk>"] ty by simp
    qed
  }
  {
    fix f e B i assume a: "\<And> B i . L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk> \<rightarrow> i \<Longrightarrow> \<exists>g. i = IMor g \<and> g maps\<^bsub>iC\<^esub> Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>"
               and b: "L\<lbrakk>Vx : A \<turnstile> f E@ e : B\<rbrakk> \<rightarrow> i"
    show "\<exists>g. i = IMor g \<and> g maps\<^bsub>iC\<^esub> Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>" using a b 
    proof-
      from b obtain g B' where g: "(Sig iS \<triangleright> Vx : A \<turnstile> e : B') \<and> (f \<in> Sig iS : B' \<rightarrow> B) \<and> (L\<lbrakk>Vx : A \<turnstile> e : B'\<rbrakk> \<rightarrow> (IMor g))"
        by auto
      from a have gmaps: "g maps\<^bsub>iC\<^esub> Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B'\<rbrakk>" using g by auto
      have fmaps: "Fn\<lbrakk>f\<rbrakk> maps\<^bsub>iC\<^esub> Ty\<lbrakk>B'\<rbrakk> to Ty\<lbrakk>B\<rbrakk>" using g If by simp
      have "(g ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>) maps\<^bsub>iC\<^esub> Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>" using ICat fmaps gmaps Category.Ccompt[of "iC" g] by simp
      moreover have "L\<lbrakk>Vx : A \<turnstile> f E@ e : B\<rbrakk> \<rightarrow> (IMor (g ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>))" using g by auto
      ultimately show ?thesis using b Functional exI[where ?x = "(g ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>)"] by simp
    qed
  }
qed

lemma (in Interpretation) Expr2Mor: "L\<lbrakk>Vx : A  \<turnstile> e : B\<rbrakk> \<rightarrow> (IMor g) \<Longrightarrow> (g maps\<^bsub>iC \<^esub>Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>)"
proof-
  assume a: "L\<lbrakk>Vx : A  \<turnstile> e : B\<rbrakk> \<rightarrow> (IMor g)"
  from MorphismsPreserved[of A e B "(IMor g)"] obtain g' where "(IMor g) = (IMor g') \<and> (g' maps\<^bsub>iC \<^esub>Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>)"
    using a by auto
  thus ?thesis by simp
qed

lemma (in Interpretation) WellDefinedExprInterp: "\<And> B . (Sig iS \<triangleright> Vx : A  \<turnstile> e : B) \<Longrightarrow> (\<exists> i . L\<lbrakk>Vx : A  \<turnstile> e : B\<rbrakk> \<rightarrow> i)"
proof(induct e)
  {
    fix B assume sig: "(Sig iS \<triangleright> Vx : A  \<turnstile> Vx : B)" show "\<exists>i. L\<lbrakk>Vx : A \<turnstile> Vx : B\<rbrakk> \<rightarrow> i"
    proof-
      have aEqb: "A = B" using sig by (simp add: SigId)
      hence ty: "A \<in> BaseTypes iS" using sig SigTyId by simp
      hence "L\<lbrakk>Vx : A \<turnstile> Vx : A\<rbrakk> \<rightarrow> (IMor (Id iC Ty\<lbrakk>A\<rbrakk>))" by auto
      thus ?thesis using aEqb by auto
    qed
  }
  {
    fix f e B assume a: "\<And> B . (Sig iS \<triangleright> Vx : A  \<turnstile> e : B) \<Longrightarrow> (\<exists> i . L\<lbrakk>Vx : A  \<turnstile> e : B\<rbrakk> \<rightarrow> i)"
      and b: "(Sig iS \<triangleright> Vx : A  \<turnstile> f E@ e : B)"
    show "\<exists> i . L\<lbrakk>Vx : A  \<turnstile> f E@ e : B\<rbrakk> \<rightarrow> i"
    proof-
      from b obtain B' where B': "(Sig iS \<triangleright> (Vx : A  \<turnstile> e : B')) \<and> (f \<in> Sig iS : B' \<rightarrow> B)" by auto
      from B' a obtain i where i: "L\<lbrakk>Vx : A  \<turnstile> e : B'\<rbrakk> \<rightarrow> i" by auto
      from MorphismsPreserved[of A e B' i] i obtain g where g: "i = (IMor g)" by auto
      thus ?thesis using B' i by auto
    qed
  }
qed

lemma (in Interpretation) Sig2Mor: assumes "(Sig iS \<triangleright> Vx : A  \<turnstile> e : B)" shows "\<exists> g . L\<lbrakk>Vx : A  \<turnstile> e : B\<rbrakk> \<rightarrow> (IMor g)"
proof-
  from WellDefinedExprInterp[of A e B] assms obtain i where i: "L\<lbrakk>Vx : A  \<turnstile> e : B\<rbrakk> \<rightarrow> i" by auto
  thus ?thesis using MorphismsPreserved[of A e B i] i by auto
qed

record ('t,'f) Axioms = 
  aAxioms :: "('t,'f) Language set" 
  aSignature :: "('t,'f) Signature" ("aS\<index>")

locale Axioms = 
  fixes Ax :: "('t,'f) Axioms" (structure)
  assumes AxT: "(aAxioms Ax) \<subseteq> {(Vx : A \<turnstile> e1 \<equiv> e2 : B) | A B e1 e2 . Sig (aSignature Ax) \<triangleright> (Vx : A \<turnstile> e1 \<equiv> e2 : B)}"
  assumes AxSig: "Signature (aSignature Ax)"

primrec Subst :: "('t,'f) Expression \<Rightarrow> ('t,'f) Expression \<Rightarrow> ('t,'f) Expression" ("sub _ in _" [81,81] 81) where
  "(sub e in Vx) = e" | "sub e in (f E@ d) = (f E@ (sub e in d))"

lemma SubstXinE: "(sub Vx in e) = e"
by(induct e, auto simp add: Subst_def)

lemma SubstAssoc: "sub a in (sub b in c) = sub (sub a in b) in c"
by(induct c, (simp add: Subst_def)+)

lemma SubstWellDefined: "\<And> C . \<lbrakk>Sig S \<triangleright> (Vx : A \<turnstile> e : B); Sig S \<triangleright> (Vx : B \<turnstile> d : C)\<rbrakk>
       \<Longrightarrow> Sig S \<triangleright> (Vx : A \<turnstile> (sub e in d) : C)"
proof(induct d)
  {
    fix C assume a: "Sig S \<triangleright> Vx : A \<turnstile> e : B" and b: "Sig S \<triangleright> Vx : B \<turnstile> Vx : C"
    have BCeq: "B = C" using b SigId[of S] by simp
    thus "Sig S \<triangleright> Vx : A \<turnstile> sub e in Vx : C" using a by simp
  }
  {
    fix f d C assume ih: "\<And>B'. \<lbrakk>Sig S \<triangleright> Vx : A \<turnstile> e : B; Sig S \<triangleright> Vx : B \<turnstile> d : B'\<rbrakk>
            \<Longrightarrow> Sig S \<triangleright> Vx : A \<turnstile> sub e in d : B'" and a: "Sig S \<triangleright> Vx : A \<turnstile> e : B" 
    and b: "Sig S \<triangleright> Vx : B \<turnstile> f E@ d : C"
    from b obtain B' where B': "f \<in> Sig S : B' \<rightarrow> C" and d: "Sig S \<triangleright> Vx : B \<turnstile> d : B'" by auto
    hence "Sig S \<triangleright> Vx : A \<turnstile> sub e in d : B'" using ih a by simp
    hence "Sig S \<triangleright> Vx : A \<turnstile> f E@ (sub e in d) : C" using B' by auto
    thus "Sig S \<triangleright> Vx : A \<turnstile> (sub e in (f E@ d)) : C" by auto
  }
qed

inductive_set (in Axioms) Theory where
  Ax: "A \<in> (aAxioms Ax) \<Longrightarrow> A \<in> Theory"
| Refl: "Sig (aSignature Ax) \<triangleright> (Vx : A \<turnstile> e : B) \<Longrightarrow> (Vx : A \<turnstile> e \<equiv> e : B) \<in> Theory"
| Symm: "(Vx : A \<turnstile> e1 \<equiv> e2 : B) \<in> Theory \<Longrightarrow> (Vx : A \<turnstile> e2 \<equiv> e1 : B) \<in> Theory" 
| Trans: "\<lbrakk>(Vx : A \<turnstile> e1 \<equiv> e2 : B) \<in> Theory ; (Vx : A \<turnstile> e2 \<equiv> e3 : B) \<in> Theory\<rbrakk> \<Longrightarrow>
           (Vx : A \<turnstile> e1 \<equiv> e3 : B) \<in> Theory"
| Congr: "\<lbrakk>(Vx : A \<turnstile> e1 \<equiv> e2 : B) \<in> Theory ; f \<in> Sig (aSignature Ax) : B \<rightarrow> C\<rbrakk> \<Longrightarrow> 
           (Vx : A \<turnstile> (f E@ e1) \<equiv> (f E@ e2) : C) \<in> Theory"
| Subst: "\<lbrakk>Sig (aSignature Ax) \<triangleright> (Vx : A \<turnstile> e1 : B) ; (Vx : B \<turnstile> e2 \<equiv> e3 : C) \<in> Theory\<rbrakk> \<Longrightarrow>
           (Vx : A \<turnstile> (sub e1 in e2) \<equiv> (sub e1 in e3) : C) \<in> Theory"

lemma (in Axioms) Equiv2WellDefined: "\<phi> \<in> Theory \<Longrightarrow> Sig aS \<triangleright> \<phi>"
proof(rule Theory.induct,auto simp add: SubstWellDefined)
  {
    fix \<phi> assume ax: "\<phi> \<in> aAxioms Ax"
    from AxT obtain A e1 e2 B where "Sig aS \<triangleright> Vx : A \<turnstile> e1 \<equiv> e2 : B" and "\<phi> = Vx : A \<turnstile> e1 \<equiv> e2 : B" using ax by blast
    thus "Sig aS \<triangleright> \<phi>" by simp    
  }
qed

lemma (in Axioms) Subst':
  "\<And> C . \<lbrakk>Sig aS \<triangleright> Vx : B \<turnstile> d : C ; (Vx : A \<turnstile> e1 \<equiv> e2 : B) \<in> Theory\<rbrakk> \<Longrightarrow> 
  (Vx : A \<turnstile> (sub e1 in d) \<equiv> (sub e2 in d) : C) \<in> Theory"
proof(induct d)
  {
    fix C assume a: "Sig aS \<triangleright> Vx : B \<turnstile> Vx : C" and b: "(Vx : A \<turnstile> e1\<equiv>e2 : B) \<in> Theory"
    have BCeq: "B = C" using a SigId[of aS B C] by simp
    thus "(Vx : A \<turnstile> (sub e1 in Vx) \<equiv> (sub e2 in Vx) : C) \<in> Theory" using b by (simp add: Subst_def)
  }
  {
    fix C f d assume ih: "\<And> B' . \<lbrakk>Sig aS \<triangleright> Vx : B \<turnstile> d : B'; (Vx : A \<turnstile> e1\<equiv>e2 : B) \<in> Theory\<rbrakk>
      \<Longrightarrow> (Vx : A \<turnstile> (sub e1 in d) \<equiv> (sub e2 in d) : B') \<in> Theory" and wd: "Sig aS \<triangleright> Vx : B \<turnstile> f E@ d : C" and
      eq: "(Vx : A \<turnstile> e1 \<equiv> e2 : B) \<in> Theory"
    from wd obtain B' where B': "f \<in> Sig aS : B' \<rightarrow> C" and d: "Sig aS \<triangleright> Vx : B \<turnstile> d : B'" by auto
    hence "(Vx : A \<turnstile> (sub e1 in d) \<equiv> (sub e2 in d) : B') \<in> Theory" using ih eq by simp
    hence "(Vx : A \<turnstile> f E@ (sub e1 in d) \<equiv> f E@ (sub e2 in d) : C) \<in> Theory" using B' by (simp add: Congr)
    thus "(Vx : A \<turnstile> (sub e1 in (f E@ d)) \<equiv> (sub e2 in (f E@ d)) : C) \<in> Theory" by (simp add: Subst_def)
  }
qed

(*This is the diamond problem in multiple inheritance -- both Interpretation and Axioms share a Signature*)
locale Model = Interpretation I + Axioms Ax
  for I :: "('t,'f,'o,'m) Interpretation" (structure)
  and Ax :: "('t,'f) Axioms" +
  assumes AxSound: "\<phi> \<in> (aAxioms Ax) \<Longrightarrow> L\<lbrakk>\<phi>\<rbrakk> \<rightarrow> (IBool True)"
  and Seq[simp]: "(aSignature Ax) = iS"

lemma (in Interpretation) Equiv:
  assumes "L\<lbrakk>Vx : A \<turnstile> e1 \<equiv> e2 : B\<rbrakk> \<rightarrow> (IBool True)"
  shows "\<exists> g . (L\<lbrakk>Vx : A \<turnstile> e1 : B\<rbrakk> \<rightarrow> (IMor g)) \<and> (L\<lbrakk>Vx : A \<turnstile> e2 : B\<rbrakk> \<rightarrow> (IMor g))"
proof-
  from assms Sig2Mor[of A e1 B] obtain g1 where g1: "L\<lbrakk>Vx : A \<turnstile> e1 : B\<rbrakk> \<rightarrow> (IMor g1)" by auto
  from assms Sig2Mor[of A e2 B] obtain g2 where g2: "L\<lbrakk>Vx : A \<turnstile> e2 : B\<rbrakk> \<rightarrow> (IMor g2)" by auto
  have "L\<lbrakk>Vx : A \<turnstile> e1\<equiv>e2 : B\<rbrakk> \<rightarrow> (IBool (g1 = g2))" using g1 g2 by auto
  hence "g1 = g2" using assms Functional[of "Vx : A \<turnstile> e1\<equiv>e2 : B" "(IBool True)" "IBool (g1=g2)"] by simp
  thus ?thesis using g1 g2 by auto
qed

lemma (in Interpretation) SubstComp: "\<And> h C . \<lbrakk>(L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk> \<rightarrow> (IMor g)) ; (L\<lbrakk>Vx : B \<turnstile> d : C\<rbrakk> \<rightarrow> (IMor h))\<rbrakk> \<Longrightarrow>
  (L\<lbrakk>Vx : A \<turnstile> (sub e in d) : C\<rbrakk> \<rightarrow> (IMor (g ;;\<^bsub>iC\<^esub> h)))"
proof(induct d,auto)
  {
    fix h C assume a: "L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk> \<rightarrow> IMor g" and b: "L\<lbrakk>Vx : B \<turnstile> Vx : C\<rbrakk> \<rightarrow> (IMor h)"
    show "L\<lbrakk>Vx : A \<turnstile> e : C\<rbrakk> \<rightarrow> IMor (g ;;\<^bsub>iC\<^esub> h)"
    proof-
      have beqc: "B = C" using b SigId[of iS B C] InterpExprWellDefined by simp
      have "L\<lbrakk>Vx : B \<turnstile> Vx : B\<rbrakk> \<rightarrow> (IMor (Id iC Ty\<lbrakk>B\<rbrakk>))" using beqc b by auto
      hence h: "h = Id iC Ty\<lbrakk>B\<rbrakk>" using b beqc by (auto simp add: Functional)
      have "g maps\<^bsub>iC \<^esub>Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>" using a MorphismsPreserved by auto
      hence "g \<in> Mor iC" and "cod\<^bsub>iC\<^esub> g = Ty\<lbrakk>B\<rbrakk>" by auto
      hence "(g ;;\<^bsub>iC\<^esub> h) = g" using h ICat Category.Cidr[of iC g] by simp
      thus ?thesis using beqc a by simp
    qed
  }
  {
    fix f d C' h C assume 
      i: "\<And> h C' . L\<lbrakk>Vx : B \<turnstile> d : C'\<rbrakk> \<rightarrow> IMor h \<Longrightarrow> L\<lbrakk>Vx : A \<turnstile> (sub e in d) : C'\<rbrakk> \<rightarrow> (IMor (g ;;\<^bsub>iC\<^esub> h))" and
      a: "L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk> \<rightarrow> IMor g" "f \<in> Sig iS : C' \<rightarrow> C" "L\<lbrakk>Vx : B \<turnstile> d : C'\<rbrakk> \<rightarrow> IMor h"
    show "L\<lbrakk>Vx : A \<turnstile> f E@ (sub e in d) : C\<rbrakk> \<rightarrow> (IMor (g ;;\<^bsub>iC\<^esub> (h ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>)))"
    proof-
      have "L\<lbrakk>Vx : A \<turnstile> (sub e in d) : C'\<rbrakk> \<rightarrow> (IMor (g ;;\<^bsub>iC\<^esub> h))" using i a by auto
      moreover hence "Sig iS \<triangleright> Vx : A \<turnstile> (sub e in d) : C'" using InterpExprWellDefined by simp
      ultimately have 1: "L\<lbrakk>Vx : A \<turnstile> f E@ (sub e in d) : C\<rbrakk> \<rightarrow> (IMor ((g ;;\<^bsub>iC\<^esub> h) ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>))" using a(2) by auto
      have "g maps\<^bsub>iC\<^esub> Ty\<lbrakk>A\<rbrakk> to Ty\<lbrakk>B\<rbrakk>" and "h maps\<^bsub>iC\<^esub> Ty\<lbrakk>B\<rbrakk> to Ty\<lbrakk>C'\<rbrakk>" and "Fn\<lbrakk>f\<rbrakk> maps\<^bsub>iC\<^esub> Ty\<lbrakk>C'\<rbrakk> to Ty\<lbrakk>C\<rbrakk>"
        using a If Expr2Mor by simp+
      hence "g \<approx>>\<^bsub>iC\<^esub> h" and "h \<approx>>\<^bsub>iC\<^esub> (Fn\<lbrakk>f\<rbrakk>)" using MapsToCompDef[of iC] by simp+
      hence "(g ;;\<^bsub>iC\<^esub> h) ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk> = g ;;\<^bsub>iC\<^esub> (h ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>)" using ICat Category.Cassoc[of iC] by simp
      thus ?thesis using 1 by simp
    qed
  }
qed

lemma (in Model) Sound: "\<phi> \<in> Theory \<Longrightarrow>  L\<lbrakk>\<phi>\<rbrakk> \<rightarrow> (IBool True)"
proof(rule Theory.induct, (simp_all add: AxSound)+)
  {
    fix A e B assume sig: "Sig iS \<triangleright> Vx : A \<turnstile> e : B" show "L\<lbrakk>Vx : A \<turnstile> e\<equiv>e : B\<rbrakk> \<rightarrow> (IBool True)"
    proof-
      from sig Sig2Mor[of A e B] obtain g where g: "L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk> \<rightarrow> (IMor g)" by auto
      thus ?thesis using InterpEq[of I A e B g e g] by simp
    qed
  }
  {
    fix A e1 e2 B assume a: "L\<lbrakk>Vx : A \<turnstile> e1\<equiv>e2 : B\<rbrakk> \<rightarrow> (IBool True)" show "L\<lbrakk>Vx : A \<turnstile> e2\<equiv>e1 : B\<rbrakk> \<rightarrow> (IBool True)"
    proof-
      from a obtain g where g1: "L\<lbrakk>Vx : A \<turnstile> e1 : B\<rbrakk> \<rightarrow> (IMor g)" and g2: "L\<lbrakk>Vx : A \<turnstile> e2 : B\<rbrakk> \<rightarrow> (IMor g)"
        using Equiv by auto
      thus ?thesis by auto
    qed
  }
  {
    fix A e1 e2 B e3 assume a: "L\<lbrakk>Vx : A \<turnstile> e1\<equiv>e2 : B\<rbrakk> \<rightarrow> (IBool True)" and b: "L\<lbrakk>Vx : A \<turnstile> e2\<equiv>e3 : B\<rbrakk> \<rightarrow> (IBool True)"
    show "L\<lbrakk>Vx : A \<turnstile> e1\<equiv>e3 : B\<rbrakk> \<rightarrow> (IBool True)"
    proof-
      from a obtain g where g1: "L\<lbrakk>Vx : A \<turnstile> e1 : B\<rbrakk> \<rightarrow> (IMor g)" and g2: "L\<lbrakk>Vx : A \<turnstile> e2 : B\<rbrakk> \<rightarrow> (IMor g)"
        using Equiv by auto
      from b obtain g' where g1': "L\<lbrakk>Vx : A \<turnstile> e2 : B\<rbrakk> \<rightarrow> (IMor g')" and g2': "L\<lbrakk>Vx : A \<turnstile> e3 : B\<rbrakk> \<rightarrow> (IMor g')"
        using Equiv by auto
      have eq: "g = g'" using g2 g1' using Functional by auto
      thus ?thesis using eq g1 g2' by auto
    qed
  }
  {
    fix A e1 e2 B f C assume a: "L\<lbrakk>Vx : A \<turnstile> e1\<equiv>e2 : B\<rbrakk> \<rightarrow> (IBool True)" and b: "f \<in> Sig iS : B \<rightarrow> C"
    show "L\<lbrakk>Vx : A \<turnstile> (f E@ e1) \<equiv> (f E@ e2) : C\<rbrakk> \<rightarrow> (IBool True)"
    proof-
      from a obtain g where g1: "L\<lbrakk>Vx : A \<turnstile> e1 : B\<rbrakk> \<rightarrow> (IMor g)" and g2: "L\<lbrakk>Vx : A \<turnstile> e2 : B\<rbrakk> \<rightarrow> (IMor g)"
        using Equiv by auto      
      have s1: "Sig iS \<triangleright> Vx : A  \<turnstile> e1 : B" and s2: "Sig iS \<triangleright> Vx : A  \<turnstile> e2 : B" using g1 g2 InterpExprWellDefined by simp+
      have "L\<lbrakk>Vx : A  \<turnstile> (f E@ e1) : C\<rbrakk> \<rightarrow> (IMor (g ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>))"
        and "L\<lbrakk>Vx : A  \<turnstile> (f E@ e2) : C\<rbrakk> \<rightarrow> (IMor (g ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>))" using b g1 s1 g2 s2 by auto
      thus ?thesis using InterpEqEq[of A "(f E@ e1)" C "(g ;;\<^bsub>iC\<^esub> Fn\<lbrakk>f\<rbrakk>)"] by simp
    qed
  }
  {
    fix A e1 B e2 e3 C assume a: "Sig iS \<triangleright> (Vx : A \<turnstile> e1 : B)" and b: "L\<lbrakk>Vx : B \<turnstile> e2\<equiv>e3 : C\<rbrakk> \<rightarrow> (IBool True)"
    show "L\<lbrakk>Vx : A \<turnstile> (sub e1 in e2) \<equiv> (sub e1 in e3) : C\<rbrakk> \<rightarrow> (IBool True)"
    proof-
      from b obtain g where g1: "L\<lbrakk>Vx : B \<turnstile> e2 : C\<rbrakk> \<rightarrow> (IMor g)" and g2: "L\<lbrakk>Vx : B \<turnstile> e3 : C\<rbrakk> \<rightarrow> (IMor g)"
        using Equiv by auto
      from a Sig2Mor[of A e1 B] obtain f where f: "L\<lbrakk>Vx : A \<turnstile> e1 : B\<rbrakk> \<rightarrow> (IMor f)" by auto
      have "L\<lbrakk>Vx : A \<turnstile> (sub e1 in e2) : C\<rbrakk> \<rightarrow> (IMor (f ;;\<^bsub>iC\<^esub> g))" using SubstComp g1 f by simp
      moreover have "L\<lbrakk>Vx : A \<turnstile> (sub e1 in e3) : C\<rbrakk> \<rightarrow> (IMor (f ;;\<^bsub>iC\<^esub> g))" using SubstComp g2 f by simp
      ultimately show ?thesis using InterpEqEq by simp
    qed
  }
qed

record ('t,'f) TermEquivClT = 
  TDomain :: 't
  TExprSet :: "('t,'f) Expression set"
  TCodomain :: 't

locale ZFAxioms = Ax : Axioms Ax for Ax :: "(ZF,ZF) Axioms" (structure) +
  assumes     fnzf: "BaseFunctions (aSignature Ax) \<in> range explode"

lemma [simp]: "ZFAxioms T \<Longrightarrow> Axioms T" by (simp add: ZFAxioms_def)

(*(tree depth, rule number, components)*)
primrec Expr2ZF :: "(ZF,ZF) Expression \<Rightarrow> ZF" where
    Expr2ZFVx: "Expr2ZF Vx = ZFTriple (nat2Nat 0) (nat2Nat 0) Empty" 
  | Expr2ZFfe: "Expr2ZF (f E@ e) = ZFTriple (SucNat (ZFTFst (Expr2ZF e)))
                                 (nat2Nat 1)
                                 (Opair f (Expr2ZF e))"

definition ZF2Expr :: "ZF \<Rightarrow> (ZF,ZF) Expression" where
  "ZF2Expr = inv Expr2ZF"

definition "ZFDepth = Nat2nat o ZFTFst"
definition "ZFType = Nat2nat o ZFTSnd"
definition "ZFData = ZFTThd"

lemma Expr2ZFType0: "ZFType (Expr2ZF e) = 0 \<Longrightarrow> e = Vx"
by(cases e,auto simp add: ZFType_def ZFTSnd Elem_Empty_Nat Elem_SucNat_Nat ZFSucNeq0)

lemma ZFDepthInNat: "Elem (ZFTFst (Expr2ZF e)) Nat"
by(induct e, auto simp add:  ZFTFst HOLZF.Elem_Empty_Nat Elem_SucNat_Nat)

lemma Expr2ZFType1: "ZFType (Expr2ZF e) = 1 \<Longrightarrow> 
  \<exists> f e' . e = (f E@ e') \<and> (Suc (ZFDepth (Expr2ZF e'))) = (ZFDepth (Expr2ZF e))"
by(cases e,auto simp add: ZFType_def ZFTSnd ZFDepth_def ZFTFst ZFZero ZFDepthInNat Nat2nat_SucNat)

lemma Expr2ZFDepth0: "ZFDepth (Expr2ZF e) = 0 \<Longrightarrow> ZFType (Expr2ZF e) = 0"
by(cases e, auto simp add: ZFDepth_def ZFTFst ZFType_def ZFTSnd ZFSucNeq0 ZFDepthInNat)

lemma Expr2ZFDepthSuc: "ZFDepth (Expr2ZF e) = Suc n \<Longrightarrow> ZFType (Expr2ZF e) = 1"
by(cases e, auto simp add: ZFDepth_def ZFTFst ZFType_def ZFTSnd ZFSucZero ZFSucNeq0 ZFZero)

lemma Expr2Data: "ZFData (Expr2ZF (f E@ e)) = Opair f (Expr2ZF e)"
by(auto simp add: ZFData_def ZFTThd)

lemma Expr2ZFinj: "inj Expr2ZF"
proof(auto simp add: inj_on_def)
  have a: "\<And> n e d . \<lbrakk>n = ZFDepth (Expr2ZF e) ; Expr2ZF e = Expr2ZF d\<rbrakk> \<Longrightarrow> e = d"
  proof-
    fix n show "\<And> e d . \<lbrakk>n = ZFDepth (Expr2ZF e) ; Expr2ZF e = Expr2ZF d\<rbrakk> \<Longrightarrow> e = d"
    proof(induct n)
      {
        fix e d assume a: "0 = ZFDepth (Expr2ZF e)" and b: "Expr2ZF e = Expr2ZF d"
        have "0 = ZFDepth (Expr2ZF d)" using a b by simp 
        hence "e = Vx" and "d = Vx" using a by (simp add: Expr2ZFDepth0 Expr2ZFType0)+
        thus "e = d" by simp
      }
      {
        fix n e d assume ih: "\<And> e' d' . \<lbrakk>n = ZFDepth (Expr2ZF e') ; Expr2ZF e' = Expr2ZF d'\<rbrakk> \<Longrightarrow> e' = d'"
          and a: "Suc n = ZFDepth (Expr2ZF e)" and b: "Expr2ZF e = Expr2ZF d"
        have "ZFType (Expr2ZF e) = 1" and "ZFType (Expr2ZF d) = 1" using a b Expr2ZFDepthSuc[of e n] by simp+
        from this Expr2ZFType1[of e] Expr2ZFType1[of d] obtain fe fd e' d' 
          where e: "e = (fe E@ e') \<and> (Suc (ZFDepth (Expr2ZF e'))) = (ZFDepth (Expr2ZF e))" and
          d: "d = (fd E@ d') \<and> (Suc (ZFDepth (Expr2ZF d'))) = (ZFDepth (Expr2ZF d))" by auto
        hence "Suc (ZFDepth (Expr2ZF e')) = Suc n" using a by simp
        hence ne: "(ZFDepth (Expr2ZF e')) = n" by (rule Suc_inject)
        have edat: "ZFData (Expr2ZF e) = Opair fe (Expr2ZF e')" using e Expr2Data by simp
        have ddat: "ZFData (Expr2ZF d) = Opair fd (Expr2ZF d')" using d Expr2Data by simp
        have fd_eq_fe: "fe = fd" and "(Expr2ZF e') = (Expr2ZF d')" using edat ddat Opair b by auto
        hence "e' = d'" using ne ih by auto
        thus "e = d" using e d fd_eq_fe by auto
      }
    qed
  qed
  fix e d show "Expr2ZF e = Expr2ZF d \<Longrightarrow> e = d" using a by auto
qed

definition "TermEquivClGen T A e B \<equiv> {e' . (Vx : A \<turnstile> e' \<equiv> e : B) \<in> Axioms.Theory T}"
definition "TermEquivCl' T A e B \<equiv> \<lparr> TDomain = A , TExprSet = TermEquivClGen T A e B , TCodomain = B\<rparr>"

definition m2ZF :: "(ZF,ZF) TermEquivClT \<Rightarrow> ZF" where
  "m2ZF t \<equiv> ZFTriple (TDomain t) (implode (Expr2ZF ` (TExprSet t))) (TCodomain t)"

definition ZF2m :: "(ZF,ZF) Axioms \<Rightarrow> ZF \<Rightarrow> (ZF,ZF) TermEquivClT" where
  "ZF2m T \<equiv> inv_into {TermEquivCl' T A e B | A e B . True} m2ZF"

lemma TDomain: "TDomain (TermEquivCl' T A e B) = A" by (simp add: TermEquivCl'_def)
lemma TCodomain: "TCodomain (TermEquivCl' T A e B) = B" by (simp add: TermEquivCl'_def)

primrec WellFormedToSet :: "(ZF,ZF) Signature \<Rightarrow> nat \<Rightarrow> (ZF,ZF) Expression set" where
  WFS0: "WellFormedToSet S 0 = {Vx}"
| WFSS: "WellFormedToSet S (Suc n) = (WellFormedToSet S n) \<union>
                { f E@ e | f e . f \<in> BaseFunctions S \<and> e \<in> (WellFormedToSet S n)}"

lemma WellFormedToSetInRangeExplode: "ZFAxioms T \<Longrightarrow> (Expr2ZF ` (WellFormedToSet aS\<^bsub>T\<^esub> n)) \<in> range explode"
proof((induct n),(simp add: WellFormedToSet_def SingletonInRangeExplode))
  fix n assume zfx: "ZFAxioms T" and ih: "ZFAxioms T \<Longrightarrow> Expr2ZF ` WellFormedToSet aS\<^bsub>T\<^esub> n \<in> range explode"
  hence a: "Expr2ZF ` WellFormedToSet aS\<^bsub>T\<^esub> n \<in> range explode" by simp
  have "Expr2ZF ` { f E@ e | f e . f \<in> BaseFunctions aS\<^bsub>T\<^esub> \<and> e \<in> (WellFormedToSet aS\<^bsub>T\<^esub> n)}
    = (\<lambda> (f, ze) . Expr2ZF (f E@ (ZF2Expr ze))) ` ((BaseFunctions aS\<^bsub>T\<^esub>) \<times> Expr2ZF ` (WellFormedToSet aS\<^bsub>T\<^esub> n))"
  proof (auto simp add: image_Collect image_def ZF2Expr_def Expr2ZFinj)
    fix f e
    assume f: "f \<in> BaseFunctions aS\<^bsub>T\<^esub>" and e: "e \<in> WellFormedToSet aS\<^bsub>T\<^esub> n"
    show "\<exists> x \<in> BaseFunctions aS\<^bsub>T\<^esub>.\<exists>y. (\<exists> x \<in> WellFormedToSet aS\<^bsub>T\<^esub> n. y = Expr2ZF x) \<and>
      ZFTriple (SucNat (ZFTFst (Expr2ZF e))) (SucNat Empty) (Opair f (Expr2ZF e)) =
      ZFTriple (SucNat (ZFTFst (Expr2ZF (inv Expr2ZF y)))) (SucNat Empty) (Opair x (Expr2ZF (inv Expr2ZF y)))"
      apply(rule bexI[where ?x = f], rule exI[where ?x = "Expr2ZF e"])
      apply (auto simp add: Expr2ZFinj f e)
      done
    show "\<exists>x. (\<exists>f e. x = f E@ e \<and> f \<in> (BaseFunctions aS\<^bsub>T\<^esub>) \<and> e \<in> WellFormedToSet aS\<^bsub>T\<^esub> n) \<and>
              ZFTriple (SucNat (ZFTFst (Expr2ZF e))) (SucNat Empty) (Opair f (Expr2ZF e)) = Expr2ZF x"
      apply(rule exI[where ?x = "f E@ e"])
      apply (auto simp add: f e)
      done
  qed
  moreover have "(BaseFunctions aS\<^bsub>T\<^esub>) \<in> range explode" using zfx ZFAxioms.fnzf by simp 
  ultimately have "Expr2ZF ` { f E@ e | f e . f \<in> BaseFunctions aS\<^bsub>T\<^esub> \<and> e \<in> (WellFormedToSet aS\<^bsub>T\<^esub> n)} \<in> range explode"
    using a ZFProdFnInRangeExplode by simp
  moreover have "Expr2ZF ` WellFormedToSet aS\<^bsub>T\<^esub> (Suc n) = (Expr2ZF ` (WellFormedToSet aS\<^bsub>T\<^esub> n)) \<union>
                (Expr2ZF  ` { f E@ e | f e . f \<in> BaseFunctions aS\<^bsub>T\<^esub> \<and> e \<in> (WellFormedToSet aS\<^bsub>T\<^esub> n)})" by auto
  ultimately show "Expr2ZF ` WellFormedToSet aS\<^bsub>T\<^esub> (Suc n) \<in> range explode" using ZFUnionInRangeExplode a by simp
qed

lemma WellDefinedToWellFormedSet: "\<And> B . (Sig S \<triangleright> (Vx : A \<turnstile> e : B)) \<Longrightarrow> \<exists>n. e \<in> WellFormedToSet S n"
proof(induct e)
  {
    fix B assume "Sig S \<triangleright> Vx : A \<turnstile> Vx : B"
    show "\<exists>n. Vx \<in> WellFormedToSet S n" by (rule exI[of _ 0], auto)
  }
  {
    fix f e B assume ih: "\<And>B'. Sig S \<triangleright> Vx : A \<turnstile> e : B' \<Longrightarrow> \<exists>n. e \<in> WellFormedToSet S n"
      and "Sig S \<triangleright> Vx : A \<turnstile> (f E@ e) : B"
    from this obtain B' where "Sig S \<triangleright> (Vx : A \<turnstile> e : B')" and f: "f \<in> Sig S : B' \<rightarrow> B" by auto
    from this obtain n where a: "e \<in> WellFormedToSet S n" using ih by auto
    have ff: "f \<in> BaseFunctions S" using f by auto
    show "\<exists>n. (f E@ e) \<in> WellFormedToSet S n" by(rule exI[of _ "Suc n"], auto simp add: a ff)
  }
qed

lemma TermSetInSet: "ZFAxioms T \<Longrightarrow> Expr2ZF ` (TermEquivClGen T A e B) \<in> range explode"
proof-
  assume zfax: "ZFAxioms T"
  have "(TermEquivClGen T A e B) \<subseteq> {e' . (Sig aS\<^bsub>T\<^esub> \<triangleright> (Vx : A \<turnstile> e' : B))}"
  proof(auto simp add: TermEquivClGen_def)
    fix x assume "Vx : A \<turnstile> x\<equiv>e : B \<in> Axioms.Theory T" 
    hence "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : A \<turnstile> x\<equiv>e : B" by (auto simp add: Axioms.Equiv2WellDefined zfax)
    thus "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : A \<turnstile> x : B" by auto
  qed
  also have "... \<subseteq> (\<Union> n . (WellFormedToSet aS\<^bsub>T\<^esub> n))" by (auto simp add: WellDefinedToWellFormedSet)
  finally have "Expr2ZF ` (TermEquivClGen T A e B) \<subseteq> Expr2ZF ` (\<Union> n . (WellFormedToSet aS\<^bsub>T\<^esub> n))" by auto
  also have "... = (\<Union> n . (Expr2ZF ` (WellFormedToSet aS\<^bsub>T\<^esub> n)))" by auto
  finally have "Expr2ZF ` (TermEquivClGen T A e B) \<subseteq> (\<Union> n . (Expr2ZF ` (WellFormedToSet aS\<^bsub>T\<^esub> n)))" by auto
  moreover have "(\<Union> n . (Expr2ZF ` (WellFormedToSet aS\<^bsub>T\<^esub> n))) \<in> range explode" 
    using zfax ZFUnionNatInRangeExplode WellFormedToSetInRangeExplode by auto
  ultimately show ?thesis using  ZFSubsetRangeExplode[of 
    "(\<Union> n . (Expr2ZF ` (WellFormedToSet aS\<^bsub>T\<^esub> n)))" "Expr2ZF ` (TermEquivClGen T A e B)"] by simp
qed

lemma m2ZFinj_on: "ZFAxioms T \<Longrightarrow> inj_on m2ZF {TermEquivCl' T A e B | A e B . True}"
apply(auto simp only: inj_on_def m2ZF_def)
apply(drule ZFTriple)
apply(auto simp add: TDomain TCodomain implode_def)
apply(simp add: TermEquivCl'_def)
apply(drule inv_into_injective)
apply(auto simp add: TermSetInSet inj_image_eq_iff Expr2ZFinj)
done

lemma ZF2m: "ZFAxioms T \<Longrightarrow> ZF2m T (m2ZF (TermEquivCl' T A e B)) = (TermEquivCl' T A e B)"
proof-
  assume zfax: "ZFAxioms T"
  let ?A = "{TermEquivCl' T A e B | A e B . True}" and ?x = "TermEquivCl' T A e B"
  have "?x \<in> ?A" by auto
  thus ?thesis using m2ZFinj_on[of T] inv_into_f_f zfax by (simp add:  ZF2m_def )
qed

definition TermEquivCl ("[_,_,_]\<index>") where "[A,e,B]\<^bsub>T\<^esub> \<equiv> m2ZF (TermEquivCl' T A e B)"

definition "CLDomain T \<equiv> TDomain o ZF2m T"
definition "CLCodomain T \<equiv> TCodomain o ZF2m T"

definition "CanonicalComp T f g \<equiv> 
  THE h . \<exists> e e' . h = [CLDomain T f,sub e in e',CLCodomain T g]\<^bsub>T\<^esub> \<and>  
  f = [CLDomain T f,e,CLCodomain T f]\<^bsub>T\<^esub> \<and> g = [CLDomain T g,e',CLCodomain T g]\<^bsub>T\<^esub>"

lemma CLDomain: "ZFAxioms T \<Longrightarrow> CLDomain T [A,e,B]\<^bsub>T\<^esub> = A"  by (simp add: TermEquivCl_def CLDomain_def ZF2m TDomain)
lemma CLCodomain: "ZFAxioms T \<Longrightarrow> CLCodomain T [A,e,B]\<^bsub>T\<^esub> = B"  by (simp add: TermEquivCl_def CLCodomain_def ZF2m TCodomain)

lemma Equiv2Cl: assumes "Axioms T" and "(Vx : A \<turnstile> e \<equiv> d : B) \<in> Axioms.Theory T" shows  "[A,e,B]\<^bsub>T\<^esub> = [A,d,B]\<^bsub>T\<^esub>"
proof-
  have "{e'. (Vx : A \<turnstile> e'\<equiv>e : B) \<in> Axioms.Theory T} = {e'. (Vx : A \<turnstile> e'\<equiv>d : B) \<in> Axioms.Theory T}"
    using assms by(blast intro: Axioms.Trans Axioms.Symm)
  thus ?thesis by(auto simp add: TermEquivCl_def TermEquivCl'_def TermEquivClGen_def)
qed

lemma Cl2Equiv: 
  assumes axt: "ZFAxioms T" and sa: "Sig aS\<^bsub>T\<^esub> \<triangleright> (Vx : A \<turnstile> e : B)" and cl: "[A,e,B]\<^bsub>T\<^esub> = [A,d,B]\<^bsub>T\<^esub>"
  shows "(Vx : A \<turnstile> e \<equiv> d : B) \<in> Axioms.Theory T"
proof-
  have "ZF2m T (m2ZF (TermEquivCl' T A e B)) = ZF2m T (m2ZF (TermEquivCl' T A d B))" using cl by (simp add: TermEquivCl_def)
  hence a:"TermEquivCl' T A e B = TermEquivCl' T A d B" using assms by (simp add: ZF2m)
  have "(Vx : A \<turnstile> e \<equiv> e : B) \<in> Axioms.Theory T" using axt sa Axioms.Refl[of T] by simp
  hence "e \<in> TermEquivClGen T A e B" by (simp add: TermEquivClGen_def)
  hence "e \<in> TermEquivClGen T A d B" using a by (simp add: TermEquivCl'_def)
  thus ?thesis by (simp add: TermEquivClGen_def)
qed 

lemma CanonicalCompWellDefined: 
  assumes zaxt: "ZFAxioms T" and "Sig aS\<^bsub>T\<^esub> \<triangleright> (Vx : A \<turnstile> d : B)" and "Sig aS\<^bsub>T\<^esub> \<triangleright> (Vx : B \<turnstile> d' : C)" 
  shows "CanonicalComp T [A,d,B]\<^bsub>T\<^esub> [B,d',C]\<^bsub>T\<^esub> = [A,sub d in d',C]\<^bsub>T\<^esub>"
proof((simp only: zaxt CanonicalComp_def CLDomain CLCodomain),(rule the_equality),
    (rule exI[of _ d], rule exI[of _ d'], auto))
  fix e e' assume de: "[A,d,B]\<^bsub>T\<^esub> = [A,e,B]\<^bsub>T\<^esub>" and de': "[B,d',C]\<^bsub>T\<^esub> = [B,e',C]\<^bsub>T\<^esub>"
  have axt: "Axioms T" using assms by simp
  have a: "(Vx : A \<turnstile> d \<equiv> e : B) \<in> Axioms.Theory T" using assms de Cl2Equiv by simp
  hence sa: "(Vx : A \<turnstile> (sub d in d') \<equiv> (sub e in d') : C) \<in> Axioms.Theory T" 
    using assms Axioms.Subst'[of T] by simp
  have b: "(Vx : B \<turnstile> d'\<equiv> e' : C) \<in> Axioms.Theory T" using assms de' Cl2Equiv by simp
  have "Sig aS\<^bsub>T\<^esub> \<triangleright> (Vx : A \<turnstile> d \<equiv> e : B)" using a axt Axioms.Equiv2WellDefined[of T] by simp
  hence "Sig aS\<^bsub>T\<^esub> \<triangleright> (Vx : A \<turnstile> e : B)" by auto
  hence "(Vx : A \<turnstile> (sub e in d') \<equiv> (sub e in e') : C) \<in> Axioms.Theory T" using b Axioms.Subst[of T] axt by simp
  hence "(Vx : A \<turnstile> (sub e in e') \<equiv> (sub d in d') : C) \<in> Axioms.Theory T" using sa axt
    by (blast intro: Axioms.Symm[of T] Axioms.Trans[of T])
  thus "[A,sub e in e',C]\<^bsub>T\<^esub> = [A,sub d in d',C]\<^bsub>T\<^esub>" using zaxt Equiv2Cl by simp
qed

definition "CanonicalCat' T \<equiv> \<lparr>
  Obj = BaseTypes (aS\<^bsub>T\<^esub>), 
  Mor = {[A,e,B]\<^bsub>T\<^esub> | A e B . Sig aS\<^bsub>T\<^esub> \<triangleright> (Vx : A \<turnstile> e : B)}, 
  Dom = CLDomain T, 
  Cod = CLCodomain T, 
  Id  = (\<lambda> A . [A,Vx,A]\<^bsub>T\<^esub>), 
  Comp = CanonicalComp T
  \<rparr>"

definition "CanonicalCat T \<equiv> MakeCat (CanonicalCat' T)"

lemma CanonicalCat'MapsTo: 
  assumes "f maps\<^bsub>CanonicalCat' T\<^esub> X to Y" and zx: "ZFAxioms T"
  shows "\<exists> ef . f = [X,ef,Y]\<^bsub>T\<^esub> \<and> Sig (aSignature T) \<triangleright> (Vx : X \<turnstile> ef : Y)"
proof-
  have fm: "f \<in> Mor (CanonicalCat' T)" and fd: "Dom (CanonicalCat' T) f = X" and fc: "Cod (CanonicalCat' T) f = Y"
    using assms by auto
  from fm obtain ef A B where ef: "f = [A,ef,B]\<^bsub>T\<^esub>" and efsig: "Sig (aSignature T) \<triangleright> (Vx : A \<turnstile> ef : B)" 
    by (auto simp add: CanonicalCat'_def)
  have "A = X" and "B = Y" using fd fc ef zx CLDomain[of T] CLCodomain[of T]  by (simp add: CanonicalCat'_def)+
  thus ?thesis using ef efsig by auto
qed

lemma CanonicalCatCat': "ZFAxioms T \<Longrightarrow> Category_axioms (CanonicalCat' T)"
proof(auto simp only: Category_axioms_def)
  have obj: "obj\<^bsub>CanonicalCat' T\<^esub> = BaseTypes (aSignature T)" by (simp add: CanonicalCat'_def)
  assume zx: "ZFAxioms T"
  hence axt: "Axioms T" by simp
  {
    fix f assume a: "f \<in> mor\<^bsub>CanonicalCat' T\<^esub>" 
    from a obtain A e B where f: "f = [A,e,B]\<^bsub>T\<^esub>" and fwd: "Sig (aSignature T) \<triangleright> (Vx : A \<turnstile> e : B)"
      by (auto simp add: CanonicalCat'_def)
    have domf: "dom\<^bsub>CanonicalCat' T\<^esub> f = CLDomain T f" and codf: "cod\<^bsub>CanonicalCat' T\<^esub> f = CLCodomain T f" 
      by (simp add: CanonicalCat'_def)+
    have absig: "A \<in> Ty\<^bsub>aSignature T\<^esub> \<and> B \<in> Ty\<^bsub>aSignature T\<^esub>" using fwd Signature.SigTy[of "(aSignature T)"] Axioms.AxSig axt
      by auto
    have Awd: "Sig (aSignature T) \<triangleright> (Vx : A \<turnstile> Vx : A)" and Bwd: "Sig (aSignature T) \<triangleright> (Vx : B \<turnstile> Vx : B)" 
      using absig by auto
    show "dom\<^bsub>CanonicalCat' T\<^esub> f \<in> obj\<^bsub>CanonicalCat' T\<^esub>" using domf f obj CLDomain[of T A e B] absig zx
      by simp
    show "cod\<^bsub>CanonicalCat' T\<^esub> f \<in> obj\<^bsub>CanonicalCat' T\<^esub>" using codf f obj CLCodomain[of T A e B] absig zx
      by simp
    have idA: "Id (CanonicalCat' T) A = [A,Vx,A]\<^bsub>T\<^esub>" and idB: "Id (CanonicalCat' T) B = [B,Vx,B]\<^bsub>T\<^esub>" 
      by (simp add: CanonicalCat'_def)+
    have "(Id (CanonicalCat' T) (dom\<^bsub>CanonicalCat' T\<^esub> f)) ;;\<^bsub>CanonicalCat' T\<^esub> f = [A, sub Vx in e, B]\<^bsub>T\<^esub>" 
      using f domf CLDomain[of T A e B] idA axt CanonicalCompWellDefined[of T] Awd fwd zx
      by (simp add: CanonicalCat'_def)
    thus "(Id (CanonicalCat' T) (dom\<^bsub>CanonicalCat' T\<^esub> f)) ;;\<^bsub>CanonicalCat' T\<^esub> f = f" using f SubstXinE[of e] by simp
    have "f ;;\<^bsub>CanonicalCat' T\<^esub> (Id (CanonicalCat' T) (cod\<^bsub>CanonicalCat' T\<^esub> f)) = [A, sub e in Vx, B]\<^bsub>T\<^esub>" 
      using f codf CLCodomain[of T A e B] idB axt CanonicalCompWellDefined[of T] Bwd fwd zx
      by (simp add: CanonicalCat'_def)
    thus "f ;;\<^bsub>CanonicalCat' T\<^esub> (Id (CanonicalCat' T) (cod\<^bsub>CanonicalCat' T\<^esub> f)) = f" using f Subst_def by simp
  }
  {
    fix X assume a: "X \<in> obj\<^bsub>CanonicalCat' T\<^esub>"
    have "X \<in> BaseTypes (aSignature T)" using a by (simp add: CanonicalCat'_def)
    hence b: "Sig (aSignature T) \<triangleright> (Vx : X \<turnstile> Vx : X)" by auto
    show "Id (CanonicalCat' T) X maps\<^bsub>CanonicalCat' T\<^esub> X to X"
      apply(rule MapsToI)
      apply(auto simp add: CanonicalCat'_def CLDomain CLCodomain zx)
      apply(rule exI)+
      apply(auto simp add: b)
      done
  }
  {
    fix f g h assume a: "f \<approx>>\<^bsub>CanonicalCat' T\<^esub> g" and b: "g \<approx>>\<^bsub>CanonicalCat' T\<^esub> h"
    from a b have fm: "f \<in> Mor (CanonicalCat' T)" and gm: "g \<in> Mor (CanonicalCat' T)" 
      and hm: "h \<in> Mor (CanonicalCat' T)" and fg: "Cod (CanonicalCat' T) f = Dom (CanonicalCat' T) g" 
      and gh: "Cod (CanonicalCat' T) g = Dom (CanonicalCat' T) h" by auto
    from fm obtain A ef B where f: "f = [A,ef,B]\<^bsub>T\<^esub>" and fwd: "Sig (aSignature T) \<triangleright> (Vx : A \<turnstile> ef : B)"
      by (auto simp add: CanonicalCat'_def)
    from gm obtain B' eg C where g: "g = [B',eg,C]\<^bsub>T\<^esub>" and gwd: "Sig (aSignature T) \<triangleright> (Vx : B' \<turnstile> eg : C)"
      by (auto simp add: CanonicalCat'_def)
    from hm obtain C' eh D where h: "h = [C',eh,D]\<^bsub>T\<^esub>" and hwd: "Sig (aSignature T) \<triangleright> (Vx : C' \<turnstile> eh : D)"
      by (auto simp add: CanonicalCat'_def)
    from fg have Beq: "B = B'" using f g zx CLCodomain[of T A ef B] CLDomain[of T B' eg C] by (simp add: CanonicalCat'_def)
    from gh have Ceq: "C = C'" using g h zx CLCodomain[of T B' eg C] CLDomain[of T C' eh D] by (simp add: CanonicalCat'_def)
    have "CanonicalComp T (CanonicalComp T f g) h = CanonicalComp T f (CanonicalComp T g h)"
    proof-
      have "(CanonicalComp T f g) = [A,sub ef in eg,C]\<^bsub>T\<^esub>" 
        using axt fwd gwd Beq zx CanonicalCompWellDefined[of T A ef B eg C] f g by simp
      moreover have "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : A \<turnstile> sub ef in eg : C" using fwd gwd SubstWellDefined Beq by simp
      ultimately have a: "CanonicalComp T (CanonicalComp T f g) h = [A,(sub (sub ef in eg) in eh),D]\<^bsub>T\<^esub>"
        using CanonicalCompWellDefined[of T A "sub ef in eg" C eh D] axt hwd h Beq Ceq zx by simp
      have "(CanonicalComp T g h) = [B,sub eg in eh,D]\<^bsub>T\<^esub>"
        using axt gwd hwd Ceq Beq CanonicalCompWellDefined[of T B eg C eh D] g h zx by simp
      moreover have "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : B \<turnstile> sub eg in eh : D" using gwd hwd SubstWellDefined Beq Ceq by simp
      ultimately have b: "CanonicalComp T f (CanonicalComp T g h) = [A,(sub ef in (sub eg in eh)),D]\<^bsub>T\<^esub>"
        using CanonicalCompWellDefined[of T A ef B "sub eg in eh" D] axt fwd f zx by simp
      show ?thesis using a b by (simp add: SubstAssoc)
    qed
    thus "(f ;;\<^bsub>CanonicalCat' T\<^esub> g) ;;\<^bsub>CanonicalCat' T\<^esub> h = f ;;\<^bsub>CanonicalCat' T\<^esub> (g ;;\<^bsub>CanonicalCat' T\<^esub> h)"
      by(simp add: CanonicalCat'_def)
  }
  {
    fix f X Y g Z assume a: "f maps\<^bsub>CanonicalCat' T\<^esub> X to Y" and b: "g maps\<^bsub>CanonicalCat' T\<^esub> Y to Z"
    from a CanonicalCat'MapsTo[of T f X Y] obtain ef 
      where f: "f = [X,ef,Y]\<^bsub>T\<^esub>" and fwd: "Sig (aSignature T) \<triangleright> (Vx : X \<turnstile> ef : Y)" using zx by auto
    from b CanonicalCat'MapsTo[of T g Y Z] obtain eg
      where g: "g = [Y,eg,Z]\<^bsub>T\<^esub>" and gwd: "Sig (aSignature T) \<triangleright> (Vx : Y \<turnstile> eg : Z)" using zx by auto
    have fg: "CanonicalComp T f g = [X,sub ef in eg,Z]\<^bsub>T\<^esub>" 
      using CanonicalCompWellDefined[of T X ef Y eg Z] f g fwd gwd zx by simp
    have fgwd: "Sig (aSignature T) \<triangleright> (Vx : X \<turnstile> sub ef in eg : Z)" 
      using fwd gwd SubstWellDefined[of "aS\<^bsub>T\<^esub>"] by simp
    have "(CanonicalComp T f g) maps\<^bsub>CanonicalCat' T\<^esub> X to Z"
    proof(rule MapsToI)
      show "Dom (CanonicalCat' T) (CanonicalComp T f g) = X" 
        using fg CLDomain[of T] zx by (simp add: CanonicalCat'_def)
      show "CanonicalComp T f g \<in> Mor (CanonicalCat' T)" using fg fgwd by (auto simp add: CanonicalCat'_def)
      show "Cod (CanonicalCat' T) (CanonicalComp T f g) = Z" 
        using fg CLCodomain[of T] zx by (simp add: CanonicalCat'_def)
    qed
    thus "f ;;\<^bsub>CanonicalCat' T\<^esub> g maps\<^bsub>CanonicalCat' T\<^esub> X to Z" by (simp add: CanonicalCat'_def)
  }
qed

lemma CanonicalCatCat: "ZFAxioms T \<Longrightarrow> Category (CanonicalCat T)"
by (simp add: CanonicalCat_def CanonicalCatCat' MakeCat)

definition CanonicalInterpretation where 
"CanonicalInterpretation T \<equiv> \<lparr>
  ISignature = aSignature T,
  ICategory  = CanonicalCat T,
  ITypes     = \<lambda> A . A,
  IFunctions = \<lambda> f . [SigDom (aSignature T) f, f E@ Vx, SigCod (aSignature T) f]\<^bsub>T\<^esub>
\<rparr>"

abbreviation "CI T \<equiv> CanonicalInterpretation T"

lemma CIObj: "Obj (CanonicalCat T) = BaseTypes (aSignature T)"
by (simp add: MakeCat_def CanonicalCat_def CanonicalCat'_def)

lemma CIMor: "ZFAxioms T \<Longrightarrow> [A,e,B]\<^bsub>T\<^esub> \<in> Mor (CanonicalCat T) = Sig (aSignature T) \<triangleright> (Vx : A \<turnstile> e : B)"
proof(auto simp add: MakeCat_def CanonicalCat_def CanonicalCat'_def)
  fix A' e' B' assume zx: "ZFAxioms T" and b: "[A,e,B]\<^bsub>T\<^esub> = [A',e',B']\<^bsub>T\<^esub>" and c: "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : A' \<turnstile> e' : B'"
  have "CLDomain T [A,e,B]\<^bsub>T\<^esub> = CLDomain T [A',e',B']\<^bsub>T\<^esub>" 
    and "CLCodomain T [A,e,B]\<^bsub>T\<^esub> = CLCodomain T [A',e',B']\<^bsub>T\<^esub>" using b by simp+
  hence "A = A'" and "B = B'" by (simp add: CLDomain CLCodomain zx)+
  hence "(Vx : A \<turnstile> e' \<equiv> e : B) \<in> Axioms.Theory T" using zx b c Cl2Equiv[of T A e' B e] by simp
  hence "Sig aS\<^bsub>T\<^esub> \<triangleright> (Vx : A \<turnstile> e' \<equiv> e : B)" using Axioms.Equiv2WellDefined[of T] zx by simp
  thus "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : A \<turnstile> e : B" by auto
qed

lemma CIDom: "\<lbrakk>ZFAxioms T ; [A,e,B]\<^bsub>T\<^esub> \<in> Mor(CanonicalCat T)\<rbrakk> \<Longrightarrow>  Dom (CanonicalCat T) [A,e,B]\<^bsub>T\<^esub> = A"
proof-
  assume "[A,e,B]\<^bsub>T\<^esub> \<in> Mor(CanonicalCat T)" and "ZFAxioms T"
  thus "Dom (CanonicalCat T) [A,e,B]\<^bsub>T\<^esub> = A" 
    by (simp add: CLDomain MakeCatMor CanonicalCat_def MakeCat_def CanonicalCat'_def)
qed

lemma CICod: "\<lbrakk>ZFAxioms T ; [A,e,B]\<^bsub>T\<^esub> \<in> Mor(CanonicalCat T)\<rbrakk> \<Longrightarrow> Cod (CanonicalCat T) [A,e,B]\<^bsub>T\<^esub> = B"
proof-
  assume "[A,e,B]\<^bsub>T\<^esub> \<in> Mor(CanonicalCat T)" and "ZFAxioms T"
  thus "Cod (CanonicalCat T) [A,e,B]\<^bsub>T\<^esub> = B" 
    by (simp add: CLCodomain MakeCatMor CanonicalCat_def MakeCat_def CanonicalCat'_def)
qed

lemma CIId: "\<lbrakk>A \<in> BaseTypes (aSignature T)\<rbrakk> \<Longrightarrow> Id (CanonicalCat T) A = [A,Vx,A]\<^bsub>T\<^esub>"
by(simp add: MakeCat_def CanonicalCat_def CanonicalCat'_def)

lemma CIComp: 
  assumes "ZFAxioms T" and "Sig (aSignature T) \<triangleright> (Vx : A \<turnstile> e : B)" and "Sig (aSignature T) \<triangleright> (Vx : B \<turnstile> d : C)"
  shows "[A,e,B]\<^bsub>T\<^esub> ;;\<^bsub>CanonicalCat T\<^esub> [B,d,C]\<^bsub>T\<^esub> = [A,sub e in d,C]\<^bsub>T\<^esub>"
proof-
  have "[A,e,B]\<^bsub>T\<^esub> \<approx>>\<^bsub>CanonicalCat' T\<^esub> [B,d,C]\<^bsub>T\<^esub>"
  proof(rule CompDefinedI)
    show "[A,e,B]\<^bsub>T\<^esub> \<in> Mor (CanonicalCat' T)" and "[B,d,C]\<^bsub>T\<^esub> \<in> Mor (CanonicalCat' T)"
      using assms by (auto simp add:  CanonicalCat'_def)
    have "cod\<^bsub>CanonicalCat' T\<^esub> [A,e,B]\<^bsub>T\<^esub> = B" using assms by (simp add: CanonicalCat'_def CLCodomain)
    moreover have "dom\<^bsub>CanonicalCat' T\<^esub> [B,d,C]\<^bsub>T\<^esub> = B" using assms by (simp add: CanonicalCat'_def CLDomain)
    ultimately show "cod\<^bsub>CanonicalCat' T\<^esub> [A,e,B]\<^bsub>T\<^esub> = dom\<^bsub>CanonicalCat' T\<^esub> [B,d,C]\<^bsub>T\<^esub>" by simp
  qed
  hence "[A,e,B]\<^bsub>T\<^esub> ;;\<^bsub>CanonicalCat T\<^esub> [B,d,C]\<^bsub>T\<^esub> = [A,e,B]\<^bsub>T\<^esub> ;;\<^bsub>CanonicalCat' T\<^esub> [B,d,C]\<^bsub>T\<^esub>"
    by (auto simp add: MakeCatComp CanonicalCat_def)
  thus "[A,e,B]\<^bsub>T\<^esub> ;;\<^bsub>CanonicalCat T\<^esub> [B,d,C]\<^bsub>T\<^esub> = [A, sub e in d, C]\<^bsub>T\<^esub>" 
    using CanonicalCompWellDefined[of T] assms by (simp add: CanonicalCat'_def)
qed

lemma [simp]: "ZFAxioms T \<Longrightarrow> Category iC\<^bsub>CI T\<^esub>" by(simp add: CanonicalInterpretation_def CanonicalCatCat[of T])
lemma [simp]: "ZFAxioms T \<Longrightarrow> Signature iS\<^bsub>CI T\<^esub>" by(simp add: CanonicalInterpretation_def Axioms.AxSig)

lemma CIInterpretation: "ZFAxioms T \<Longrightarrow> Interpretation (CI T)"
proof(auto simp only: Interpretation_def)
  assume xt: "ZFAxioms T"
  show "Category iC\<^bsub>CI T\<^esub>" and "Signature iS\<^bsub>CI T\<^esub>" using xt by simp+
  {
    fix A assume "A \<in> BaseTypes (iS\<^bsub>CI T\<^esub>)" thus "Ty\<lbrakk>A\<rbrakk>\<^bsub>CI T\<^esub> \<in> Obj (iC\<^bsub>CI T\<^esub>)"
      by(simp add: CanonicalInterpretation_def CIObj[of T])
  }
  {
    fix f A B assume a: "f \<in> Sig iS\<^bsub>CI T\<^esub> : A \<rightarrow> B"
    hence "[sDom\<^bsub>ISignature (CI T)\<^esub> f,f E@ Vx,sCod\<^bsub>ISignature (CI T)\<^esub> f]\<^bsub>T\<^esub> \<in> mor\<^bsub>CanonicalCat T\<^esub>"
      using xt by(auto simp add: CanonicalInterpretation_def CIMor)
    thus "Fn\<lbrakk>f\<rbrakk>\<^bsub>CI T\<^esub> maps\<^bsub>ICategory (CI T) \<^esub>Ty\<lbrakk>A\<rbrakk>\<^bsub>CI T\<^esub> to Ty\<lbrakk>B\<rbrakk>\<^bsub>CI T\<^esub>" using a xt
      by(auto simp add: CanonicalInterpretation_def MapsTo_def funsignature_abbrev_def CIDom CICod)
  }
qed

lemma CIInterp2Mor: "ZFAxioms T \<Longrightarrow> (\<And> B . Sig iS\<^bsub>CI T\<^esub> \<triangleright> (Vx : A \<turnstile> e : B) \<Longrightarrow>  L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A, e, B]\<^bsub>T\<^esub>))"
proof(induct e)
  assume xt: "ZFAxioms T"
  {
    fix B assume a: "Sig iS\<^bsub>CI T\<^esub> \<triangleright> Vx : A \<turnstile> Vx : B" 
    have aeqb: "A = B" using a SigId[of "iS\<^bsub>CI T\<^esub>" A B] Interpretation.InterpExprWellDefined[of "CI T"] by simp
    moreover have bt: "A \<in> BaseTypes iS\<^bsub>CI T\<^esub>" using a SigTyId aeqb by simp
    ultimately have b: "L\<lbrakk>Vx : A \<turnstile> Vx : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor (Id iC\<^bsub>CI T\<^esub> Ty\<lbrakk>A\<rbrakk>\<^bsub>CI T\<^esub>))" by auto
    have "Ty\<lbrakk>A\<rbrakk>\<^bsub>CI T\<^esub> = A" by (simp add: CanonicalInterpretation_def)
    hence "(Id iC\<^bsub>CI T\<^esub> Ty\<lbrakk>A\<rbrakk>\<^bsub>CI T\<^esub>) = [A,Vx,A]\<^bsub>T\<^esub>" using bt CIId by(simp add: CanonicalInterpretation_def)
    thus "L\<lbrakk>Vx : A \<turnstile> Vx : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A,Vx,B]\<^bsub>T\<^esub>)" using aeqb b by simp
  }
  {
    fix f e B assume ih: "\<And>B'. \<lbrakk>ZFAxioms T ; Sig iS\<^bsub>CI T\<^esub> \<triangleright> (Vx : A \<turnstile> e : B')\<rbrakk> \<Longrightarrow> (L\<lbrakk>Vx : A \<turnstile> e : B'\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A,e,B']\<^bsub>T\<^esub>))"
    and a: "Sig iS\<^bsub>CI T\<^esub> \<triangleright> Vx : A \<turnstile> f E@ e : B"
    from a obtain B' where sig: "Sig iS\<^bsub>CI T\<^esub> \<triangleright> (Vx : A \<turnstile> e : B')" and f: "f \<in> Sig iS\<^bsub>CI T\<^esub> : B' \<rightarrow> B" by auto 
    hence "L\<lbrakk>Vx : A \<turnstile> e : B'\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A,e,B']\<^bsub>T\<^esub>)" using ih xt by auto
    hence b: "L\<lbrakk>Vx : A \<turnstile> f E@ e : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor ([A,e,B']\<^bsub>T\<^esub> ;;\<^bsub>ICategory (CI T)\<^esub> Fn\<lbrakk>f\<rbrakk>\<^bsub>CI T\<^esub>))" using sig f by auto
    have "[A,e,B']\<^bsub>T\<^esub> ;;\<^bsub>ICategory (CI T)\<^esub> Fn\<lbrakk>f\<rbrakk>\<^bsub>CI T\<^esub> = [A,f E@ e,B]\<^bsub>T\<^esub>" 
    proof-
      have aa: "Fn\<lbrakk>f\<rbrakk>\<^bsub>CI T\<^esub> = [B', f E@ Vx, B]\<^bsub>T\<^esub>" using f by (simp add: CanonicalInterpretation_def funsignature_abbrev_def)
      have "Sig iS\<^bsub>CI T\<^esub> \<triangleright> Vx : A \<turnstile> e : B'" and "Sig iS\<^bsub>CI T\<^esub> \<triangleright> Vx : B' \<turnstile> f E@ Vx : B"  using sig f by auto
      hence "[A,e,B']\<^bsub>T\<^esub> ;;\<^bsub>ICategory (CI T)\<^esub> [B', f E@ Vx, B]\<^bsub>T\<^esub> = [A, sub e in (f E@ Vx), B]\<^bsub>T\<^esub>" 
        using CIComp[of T] xt by (simp add: CanonicalInterpretation_def)
      moreover have "sub e in (f E@ Vx) = f E@ e" by (auto simp add: Subst_def)
      ultimately show ?thesis using aa by simp
    qed
    thus "L\<lbrakk>Vx : A \<turnstile> f E@ e : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A,f E@ e,B]\<^bsub>T\<^esub>)" using b by simp
  }
qed

lemma CIModel: "ZFAxioms T \<Longrightarrow> Model (CI T) T"
proof(auto simp add: Model_def Model_axioms_def )
  assume xt: "ZFAxioms T"
  have axt: "Axioms T" using xt by simp
  show ii: "Interpretation (CI T)" using xt by (simp add: CIInterpretation)
  show aeq: "aS\<^bsub>T\<^esub> = iS\<^bsub>CI T\<^esub>" by (simp add: CanonicalInterpretation_def)
  {
    fix \<phi> assume a: "\<phi> \<in> aAxioms T"
    from a Axioms.AxT obtain A B e d where \<phi>: "\<phi> = Vx : A \<turnstile> e \<equiv> d : B" and sig: "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : A \<turnstile> e \<equiv> d : B" 
      using axt by blast
    have "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : A \<turnstile> e : B" using sig by auto
    hence e: "L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A, e, B]\<^bsub>T\<^esub>)" using aeq CIInterp2Mor xt by simp
    have "Sig aS\<^bsub>T\<^esub> \<triangleright> Vx : A \<turnstile> d : B" using sig by auto
    hence d: "L\<lbrakk>Vx : A \<turnstile> d : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A, d, B]\<^bsub>T\<^esub>)" using aeq CIInterp2Mor xt by simp
    have "\<phi> \<in> Axioms.Theory T" using a axt by (simp add: Axioms.Theory.Ax)
    hence "[A, e, B]\<^bsub>T\<^esub> = [A, d, B]\<^bsub>T\<^esub>" using \<phi> Equiv2Cl axt by simp
    thus "L\<lbrakk>\<phi>\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IBool True)" using e d \<phi> ii InterpEq[of "CI T" A e B "[A, e, B]\<^bsub>T\<^esub>" d "[A, d, B]\<^bsub>T\<^esub>"] by simp
  }
qed

lemma CIComplete: assumes "ZFAxioms T" and "L\<lbrakk>\<phi>\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IBool True)" shows "\<phi> \<in> Axioms.Theory T"
proof-
  have ii: "Interpretation (CI T)" using assms by (simp add: CIInterpretation)
  hence aeq: "aS\<^bsub>T\<^esub> = iS\<^bsub>CI T\<^esub>" by (simp add: CanonicalInterpretation_def)
  from Interpretation.Bool[of "CI T" \<phi> True] obtain A B e d where \<phi>: "\<phi> = (Vx : A \<turnstile> e \<equiv> d : B)" using ii assms by auto
  from Interpretation.Equiv[of "CI T" A e d B] obtain g 
    where g1: "L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor g)" 
    and   g2: "L\<lbrakk>Vx : A \<turnstile> d : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor g)" using ii \<phi> assms by auto
  have ewd: "Sig iS\<^bsub>CI T\<^esub> \<triangleright> (Vx : A \<turnstile> e : B)" and dwd: "Sig iS\<^bsub>CI T\<^esub> \<triangleright> (Vx : A \<turnstile> d : B)" 
    using g1 g2 Interpretation.InterpExprWellDefined[of "CI T"] ii by simp+
  have ie: "L\<lbrakk>Vx : A \<turnstile> e : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A, e, B]\<^bsub>T\<^esub>)" using ewd CIInterp2Mor assms by simp
  have id: "L\<lbrakk>Vx : A \<turnstile> d : B\<rbrakk>\<^bsub>CI T\<^esub> \<rightarrow> (IMor [A, d, B]\<^bsub>T\<^esub>)" using dwd CIInterp2Mor assms by simp
  have "[A, e, B]\<^bsub>T\<^esub> = g" 
    using g1 ie ii Interpretation.Functional[of "CI T" "Vx : A \<turnstile> e : B" "IMor [A, e, B]\<^bsub>T\<^esub>" "IMor g"] by simp
  moreover have "[A, d, B]\<^bsub>T\<^esub> = g" 
    using g2 id ii Interpretation.Functional[of "CI T" "Vx : A \<turnstile> d : B" "IMor [A, d, B]\<^bsub>T\<^esub>" "IMor g"] by simp
  ultimately have "[A, e, B]\<^bsub>T\<^esub> = [A, d, B]\<^bsub>T\<^esub>" by simp
  thus ?thesis using \<phi> ewd Cl2Equiv aeq assms by simp
qed

lemma Complete: 
  assumes "ZFAxioms T" 
  and "\<And> (I :: (ZF,ZF,ZF,ZF) Interpretation) . Model I T \<Longrightarrow> (L\<lbrakk>\<phi>\<rbrakk>\<^bsub>I\<^esub> \<rightarrow> (IBool True))" 
  shows "\<phi> \<in> Axioms.Theory T"
proof-
  have "Model (CI T) T" using assms CIModel by simp
  thus ?thesis using CIComplete[of T \<phi>] assms by auto
qed

end
