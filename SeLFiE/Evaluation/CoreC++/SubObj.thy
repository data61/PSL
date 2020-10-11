(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section \<open>Definition of Subobjects\<close>

theory SubObj
imports ClassRel
begin


subsection \<open>General definitions\<close>

type_synonym
  subobj = "cname  \<times> path"

definition mdc :: "subobj \<Rightarrow> cname" where
  "mdc S = fst S"

definition ldc :: "subobj \<Rightarrow> cname" where
  "ldc S = last (snd S)"


lemma mdc_tuple [simp]: "mdc (C,Cs) = C"
by(simp add:mdc_def)

lemma ldc_tuple [simp]: "ldc (C,Cs) = last Cs"
by(simp add:ldc_def)


subsection \<open>Subobjects according to Rossie-Friedman\<close>

fun is_subobj :: "prog \<Rightarrow> subobj \<Rightarrow> bool" \<comment> \<open>legal subobject to class hierarchie\<close> where
  "is_subobj P (C, []) \<longleftrightarrow> False"
| "is_subobj P (C, [D]) \<longleftrightarrow> (is_class P C \<and> C = D) 
                                \<or> (\<exists> X. P \<turnstile> C \<preceq>\<^sup>* X \<and> P \<turnstile> X \<prec>\<^sub>S D)"
| "is_subobj P (C, D # E # Xs) = (let Ys=butlast (D # E # Xs); 
                                      Y=last (D # E # Xs); 
                                      X=last Ys 
                                in is_subobj P (C, Ys) \<and> P \<turnstile> X \<prec>\<^sub>R Y)"

lemma subobj_aux_rev:
assumes 1:"is_subobj P ((C,C'#rev Cs@[C'']))"
shows "is_subobj P ((C,C'#rev Cs))"
proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  hence rev:"Cs'@[C''] = rev Cs@[C'']" by simp
  from this obtain D Ds where DDs:"Cs'@[C''] = D#Ds" by (cases Cs') auto
  with 1 rev have subo:"is_subobj P ((C,C'#D#Ds))" by simp
  from DDs have "butlast (C'#D#Ds) = C'#Cs'" by (cases Cs') auto
  with subo have "is_subobj P ((C,C'#Cs'))" by simp
  with Cs' show ?thesis by simp
qed



lemma subobj_aux:
assumes 1:"is_subobj P ((C,C'#Cs@[C'']))"
shows "is_subobj P ((C,C'#Cs))"
proof -
  from 1 obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with 1 have "is_subobj P ((C,C'#rev Cs'@[C'']))" by simp
  hence "is_subobj P ((C,C'#rev Cs'))" by (rule subobj_aux_rev)
  with Cs' show ?thesis by simp
qed



lemma isSubobj_isClass:
assumes 1:"is_subobj P (R)"
shows "is_class P (mdc R)"

proof -
  obtain C' Cs' where R:"R = (C',Cs')" by(cases R) auto
  with 1 have ne:"Cs' \<noteq> []" by (cases Cs') auto
  from this obtain C'' Cs'' where C''Cs'':"Cs' = C''#Cs''" by (cases Cs') auto
  from this obtain Ds where "Ds = rev Cs''" by simp
  with 1 R C''Cs'' have subo1:"is_subobj P ((C',C''#rev Ds))" by simp
  with R show ?thesis
    by (induct Ds,auto simp:mdc_def split:if_split_asm dest:subobj_aux,
      auto elim:converse_rtranclE dest!:subclsS_subcls1 elim:subcls1_class)
qed




lemma isSubobjs_subclsR_rev:
assumes 1:"is_subobj P ((C,Cs@[D,D']@(rev Cs')))"
shows "P \<turnstile> D \<prec>\<^sub>R D'"
using 1
proof (induct Cs')
  case Nil
  from this obtain Cs' X Y Xs where Cs'1:"Cs' = Cs@[D,D']" 
    and "X = hd(Cs@[D,D'])" and "Y = hd(tl(Cs@[D,D']))"
    and "Xs =  tl(tl(Cs@[D,D']))" by simp
  hence Cs'2:"Cs' = X#Y#Xs" by (cases Cs) auto
  from Cs'1 have last:"last Cs' = D'" by simp
  from Cs'1 have butlast:"last(butlast Cs') = D" by (simp add:butlast_tail)
  from Nil Cs'1 Cs'2 have "is_subobj P ((C,X#Y#Xs))" by simp
  with last butlast Cs'2 show ?case by simp
next
  case (Cons C'' Cs'')
  have IH:"is_subobj P ( (C, Cs @ [D, D'] @ rev Cs'')) \<Longrightarrow> P \<turnstile> D \<prec>\<^sub>R D'" by fact
  from Cons obtain Cs' X Y Xs where Cs'1:"Cs' = Cs@[D,D']@(rev (C''#Cs''))" 
    and "X = hd(Cs@[D,D']@(rev (C''#Cs'')))" 
    and "Y = hd(tl(Cs@[D,D']@(rev (C''#Cs''))))"
    and "Xs =  tl(tl(Cs@[D,D']@(rev (C''#Cs''))))" by simp
  hence Cs'2:"Cs' = X#Y#Xs" by (cases Cs) auto
  from Cons Cs'1 Cs'2 have "is_subobj P ((C,X#Y#Xs))" by simp
  hence sub:"is_subobj P ((C,butlast (X#Y#Xs)))" by simp
  from Cs'1 obtain E Es where Cs'3:"Cs' = Es@[E]" by (cases Cs') auto
  with Cs'1 have butlast:"Es = Cs@[D,D']@(rev Cs'')" by simp
  from Cs'3 have "butlast Cs' = Es" by simp
  with butlast have "butlast Cs' = Cs@[D,D']@(rev Cs'')" by simp
  with Cs'2 sub have "is_subobj P ((C,Cs@[D,D']@(rev Cs'')))"
    by simp
  with IH show ?case by simp
qed



lemma isSubobjs_subclsR:
assumes 1:"is_subobj P ((C,Cs@[D,D']@Cs'))"
shows "P \<turnstile> D \<prec>\<^sub>R D'"

proof -
  from 1 obtain Cs'' where "Cs'' = rev Cs'" by simp
  with 1 have "is_subobj P ((C,Cs@[D,D']@(rev Cs'')))" by simp
  thus ?thesis by (rule isSubobjs_subclsR_rev)
qed




lemma mdc_leq_ldc_aux:
assumes 1:"is_subobj P ((C,C'#rev Cs'))"
shows "P \<turnstile> C \<preceq>\<^sup>* last (C'#rev Cs')"
using 1
proof (induct Cs')
  case Nil
  from 1 have "is_class P C"
    by (drule_tac R="(C,C'#rev Cs')" in isSubobj_isClass, simp add:mdc_def)
  with Nil show ?case
    proof (cases "C=C'")
      case True
      thus ?thesis by simp
    next
      case False
      with Nil show ?thesis 
        by (auto dest!:subclsS_subcls1)
    qed
  next
    case (Cons C'' Cs'')
    have IH:"is_subobj P ( (C, C' # rev Cs'')) \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* last (C' # rev Cs'')"
      and subo:"is_subobj P ( (C, C' # rev (C'' # Cs'')))" by fact+
    hence "is_subobj P ( (C, C' # rev Cs''))" by (simp add:subobj_aux_rev)
    with IH have rel:"P \<turnstile> C \<preceq>\<^sup>* last (C' # rev Cs'')" by simp
    from subo obtain D Ds where DDs:"C' # rev Cs'' = Ds@[D]"
      by (cases Cs'') auto
    hence " C' # rev (C'' # Cs'') = Ds@[D,C'']" by simp
    with subo have "is_subobj P ((C,Ds@[D,C'']))" by (cases Ds) auto
    hence "P \<turnstile> D \<prec>\<^sub>R C''" by (rule_tac Cs'="[]" in isSubobjs_subclsR) simp
    hence rel1:"P \<turnstile> D \<prec>\<^sup>1 C''" by (rule subclsR_subcls1)
    from DDs have "D = last (C' # rev Cs'')" by simp
    with rel1 have lastrel1:"P \<turnstile> last (C' # rev Cs'') \<prec>\<^sup>1 C''" by simp
    with rel have "P \<turnstile> C \<preceq>\<^sup>* C''"
      by(rule_tac b="last (C' # rev Cs'')" in rtrancl_into_rtrancl) simp
    thus ?case by simp
qed



lemma mdc_leq_ldc:
assumes 1:"is_subobj P (R)"
shows "P \<turnstile> mdc R \<preceq>\<^sup>* ldc R"

proof -
  from 1 obtain C Cs where R:"R = (C,Cs)" by (cases R) auto
  with 1 have ne:"Cs \<noteq> []" by (cases Cs) auto
  from this obtain C' Cs' where Cs:"Cs = C'#Cs'" by (cases Cs) auto
  from this obtain Cs'' where Cs':"Cs'' = rev Cs'" by simp
  with R Cs 1 have "is_subobj P ((C,C'#rev Cs''))" by simp
  hence rel:"P \<turnstile> C \<preceq>\<^sup>* last (C'#rev Cs'')" by (rule mdc_leq_ldc_aux)
  from R Cs Cs' have ldc:"last (C'#rev Cs'') = ldc R" by(simp add:ldc_def)
  from R have "mdc R = C" by(simp add:mdc_def)
  with ldc rel show ?thesis by simp
qed



text\<open>Next three lemmas show subobject property as presented in literature\<close>

lemma class_isSubobj:
  "is_class P C \<Longrightarrow> is_subobj P ((C,[C]))"
by simp


lemma repSubobj_isSubobj:
assumes 1:"is_subobj P ((C,Xs@[X]))" and 2:"P \<turnstile> X \<prec>\<^sub>R Y"
shows "is_subobj P ((C,Xs@[X,Y]))"

using 1
proof -
  obtain Cs D E Cs' where Cs1:"Cs = Xs@[X,Y]" and  "D = hd(Xs@[X,Y])"
    and "E = hd(tl(Xs@[X,Y]))" and "Cs' = tl(tl(Xs@[X,Y]))"by simp
  hence Cs2:"Cs = D#E#Cs'" by (cases Xs) auto
  with 1 Cs1 have subobj_butlast:"is_subobj P ((C,butlast(D#E#Cs')))" 
    by (simp add:butlast_tail)
  with 2 Cs1 Cs2 have "P \<turnstile> (last(butlast(D#E#Cs'))) \<prec>\<^sub>R last(D#E#Cs')"
    by (simp add:butlast_tail)
  with subobj_butlast have "is_subobj P ((C,(D#E#Cs')))" by simp
  with Cs1 Cs2 show ?thesis by simp
qed



lemma shSubobj_isSubobj:
assumes 1:  "is_subobj P ((C,Xs@[X]))" and 2:"P \<turnstile> X \<prec>\<^sub>S Y"
shows "is_subobj P ((C,[Y]))"

using 1
proof -
  from 1 have classC:"is_class P C" 
    by (drule_tac R="(C,Xs@[X])" in isSubobj_isClass, simp add:mdc_def)
  from 1 have "P \<turnstile> C \<preceq>\<^sup>* X" 
    by (drule_tac R="(C,Xs@[X])" in mdc_leq_ldc, simp add:mdc_def ldc_def)
  with classC 2 show ?thesis by fastforce
qed



text\<open>Auxiliary lemmas\<close>


lemma build_rec_isSubobj_rev:
assumes 1:"is_subobj P ((D,D#rev Cs))" and 2:" P \<turnstile> C \<prec>\<^sub>R D"
shows "is_subobj P ((C,C#D#rev Cs))"
using 1
proof (induct Cs)
  case Nil
  from 2 have "is_class P C" by (auto dest:subclsRD simp add:is_class_def)
  with 1 2 show ?case by simp
next
  case (Cons C' Cs')
  have suboD:"is_subobj P ((D,D#rev (C'#Cs')))" 
    and IH:"is_subobj P ((D,D#rev Cs')) \<Longrightarrow> is_subobj P ((C,C#D#rev Cs'))" by fact+
  obtain E Es where E:"E = hd (rev (C'#Cs'))" and Es:"Es = tl (rev (C'#Cs'))"
    by simp
  with E have E_Es:"rev (C'#Cs') = E#Es" by simp
  with E Es have butlast:"butlast (D#E#Es) = D#rev Cs'" by simp
  from E_Es suboD have suboDE:"is_subobj P ((D,D#E#Es))" by simp
  hence "is_subobj P ((D,butlast (D#E#Es)))" by simp
  with butlast have "is_subobj P ((D,D#rev Cs'))" by simp
  with IH have suboCD:"is_subobj P ( (C, C#D#rev Cs'))" by simp
  from suboDE obtain Xs X Y Xs' where Xs':"Xs' = D#E#Es"
    and bb:"Xs = butlast (butlast (D#E#Es))" 
    and lb:"X = last(butlast (D#E#Es))" and l:"Y = last (D#E#Es)" by simp
  from this obtain Xs'' where Xs'':"Xs'' = Xs@[X]" by simp
  with bb lb have "Xs'' = butlast (D#E#Es)" by simp
  with l have "D#E#Es = Xs''@[Y]" by simp
  with Xs'' have "D#E#Es = Xs@[X]@[Y]" by simp
  with suboDE have "is_subobj P ((D,Xs@[X,Y]))" by simp
  hence subR:"P \<turnstile> X \<prec>\<^sub>R Y"  by(rule_tac Cs="Xs" and Cs'="[]" in isSubobjs_subclsR) simp
  from E_Es Es have "last (D#E#Es) = C'" by simp
  with subR lb l butlast have "P \<turnstile> last(D#rev Cs') \<prec>\<^sub>R C'"
    by (auto split:if_split_asm)
  with suboCD show ?case by simp
qed



lemma build_rec_isSubobj:
assumes 1:"is_subobj P ((D,D#Cs))" and 2:" P \<turnstile> C \<prec>\<^sub>R D" 
shows "is_subobj P ((C,C#D#Cs))"

proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with 1 have "is_subobj P ((D,D#rev Cs'))" by simp
  with 2 have "is_subobj P ((C,C#D#rev Cs'))" 
    by - (rule build_rec_isSubobj_rev) 
  with Cs' show ?thesis by simp
qed





lemma isSubobj_isSubobj_isSubobj_rev:
assumes 1:"is_subobj P ((C,[D]))" and 2:"is_subobj P ((D,D#(rev Cs)))" 
shows "is_subobj P ((C,D#(rev Cs)))"
using 2
proof (induct Cs)
 case Nil
 with 1 show ?case by simp
next
  case (Cons C' Cs')
  have IH:"is_subobj P ((D,D#rev Cs')) \<Longrightarrow> is_subobj P ((C,D#rev Cs'))"
    and "is_subobj P ((D,D#rev (C'#Cs')))" by fact+
  hence suboD:"is_subobj P ((D,D#rev Cs'@[C']))" by simp
  hence "is_subobj P ((D,D#rev Cs'))" by (rule subobj_aux_rev)
  with IH have suboC:"is_subobj P ((C,D#rev Cs'))" by simp
  obtain C'' where C'': "C'' = last (D # rev Cs')" by simp
  moreover have "D # rev Cs' = butlast (D # rev Cs') @ [last (D # rev Cs')]"
    by (rule append_butlast_last_id [symmetric]) simp
  ultimately have butlast: "D # rev Cs' = butlast (D  #rev Cs') @ [C'']"
    by simp
  hence butlast2:"D#rev Cs'@[C'] = butlast(D#rev Cs')@[C'']@[C']" by simp
  with suboD have "is_subobj P ((D,butlast(D#rev Cs')@[C'']@[C']))"
    by simp
  with C'' have subR:"P \<turnstile> C'' \<prec>\<^sub>R C'"
    by (rule_tac Cs="butlast(D#rev Cs')" and Cs'="[]" in isSubobjs_subclsR)simp
  with C'' suboC butlast have "is_subobj P ((C,butlast(D#rev Cs')@[C'']@[C']))"
    by (auto intro:repSubobj_isSubobj simp del:butlast.simps)
  with butlast2 have "is_subobj P ((C,D#rev Cs'@[C']))"
    by (cases Cs')auto
  thus ?case by simp
qed


lemma isSubobj_isSubobj_isSubobj:
assumes 1:"is_subobj P ((C,[D]))" and 2:"is_subobj P ((D,D#Cs))" 
shows "is_subobj P ((C,D#Cs))"

proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with 2 have "is_subobj P ((D,D#rev Cs'))" by simp
  with 1 have "is_subobj P ((C,D#rev Cs'))"
  by - (rule isSubobj_isSubobj_isSubobj_rev)
with Cs' show ?thesis by simp
qed



subsection \<open>Subobject handling and lemmas\<close>

text\<open>Subobjects consisting of repeated inheritance relations only:\<close>

inductive Subobjs\<^sub>R :: "prog \<Rightarrow> cname \<Rightarrow> path \<Rightarrow> bool" for P :: prog
where
  SubobjsR_Base: "is_class P C \<Longrightarrow> Subobjs\<^sub>R P C [C]"
| SubobjsR_Rep: "\<lbrakk>P \<turnstile> C \<prec>\<^sub>R D; Subobjs\<^sub>R P D Cs\<rbrakk> \<Longrightarrow> Subobjs\<^sub>R P C (C # Cs)"

text\<open>All subobjects:\<close>

inductive Subobjs :: "prog \<Rightarrow> cname \<Rightarrow> path \<Rightarrow> bool" for P :: prog
where
  Subobjs_Rep: "Subobjs\<^sub>R P C Cs \<Longrightarrow> Subobjs P C Cs"
| Subobjs_Sh: "\<lbrakk>P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<prec>\<^sub>S D; Subobjs\<^sub>R P D Cs\<rbrakk>
             \<Longrightarrow> Subobjs P C Cs"


lemma Subobjs_Base:"is_class P C \<Longrightarrow> Subobjs P C [C]"
by (fastforce intro:Subobjs_Rep SubobjsR_Base)

lemma SubobjsR_nonempty: "Subobjs\<^sub>R P C Cs \<Longrightarrow> Cs \<noteq> []"
by (induct rule: Subobjs\<^sub>R.induct, simp_all)

lemma Subobjs_nonempty: "Subobjs P C Cs \<Longrightarrow> Cs \<noteq> []"
by (erule Subobjs.induct)(erule SubobjsR_nonempty)+


lemma hd_SubobjsR:
  "Subobjs\<^sub>R P C Cs \<Longrightarrow> \<exists>Cs'. Cs = C#Cs'"
by(erule Subobjs\<^sub>R.induct,simp+)


lemma SubobjsR_subclassRep: 
  "Subobjs\<^sub>R P C Cs \<Longrightarrow> (C,last Cs) \<in> (subclsR P)\<^sup>*"

apply(erule Subobjs\<^sub>R.induct)
 apply simp
apply(simp add: SubobjsR_nonempty)
done


lemma SubobjsR_subclass: "Subobjs\<^sub>R P C Cs \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* last Cs"

apply(erule Subobjs\<^sub>R.induct)
 apply simp
apply(simp add: SubobjsR_nonempty)
apply(blast intro:subclsR_subcls1 rtrancl_trans)
done


lemma Subobjs_subclass: "Subobjs P C Cs \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* last Cs"

apply(erule Subobjs.induct)
 apply(erule SubobjsR_subclass)
apply(erule rtrancl_trans)
apply(blast intro:subclsS_subcls1 SubobjsR_subclass rtrancl_trans)
done




lemma Subobjs_notSubobjsR:
  "\<lbrakk>Subobjs P C Cs; \<not> Subobjs\<^sub>R P C Cs\<rbrakk>
\<Longrightarrow> \<exists>C' D. P \<turnstile> C \<preceq>\<^sup>* C' \<and> P \<turnstile> C' \<prec>\<^sub>S D \<and> Subobjs\<^sub>R P D Cs"
apply (induct rule: Subobjs.induct)
 apply clarsimp
apply fastforce
done



lemma assumes subo:"Subobjs\<^sub>R P (hd (Cs@ C'#Cs')) (Cs@ C'#Cs')"
  shows SubobjsR_Subobjs:"Subobjs P C' (C'#Cs')"
  using subo
proof (induct Cs)
  case Nil
  thus ?case by -(frule hd_SubobjsR,fastforce intro:Subobjs_Rep)
next
  case (Cons D Ds)
  have subo':"Subobjs\<^sub>R P (hd ((D#Ds) @ C'#Cs')) ((D#Ds) @ C'#Cs')"
    and IH:"Subobjs\<^sub>R P (hd (Ds @ C'#Cs')) (Ds @ C'#Cs') \<Longrightarrow> Subobjs P C' (C'#Cs')" by fact+
  from subo' have "Subobjs\<^sub>R P (hd (Ds @ C' # Cs')) (Ds @ C' # Cs')"
    apply -
    apply (drule Subobjs\<^sub>R.cases)
    apply auto
    apply (rename_tac D')
    apply (subgoal_tac "D' = hd (Ds @ C' # Cs')")
    apply (auto dest:hd_SubobjsR)
    done
  with IH show ?case by simp
qed

lemma Subobjs_Subobjs:"Subobjs P C (Cs@ C'#Cs') \<Longrightarrow> Subobjs P C' (C'#Cs')"
  
  apply -
  apply (drule Subobjs.cases)
  apply auto
   apply (subgoal_tac "C = hd(Cs @ C' # Cs')")
    apply (fastforce intro:SubobjsR_Subobjs)
   apply (fastforce dest:hd_SubobjsR)
  apply (subgoal_tac "D = hd(Cs @ C' # Cs')")
   apply (fastforce intro:SubobjsR_Subobjs)
  apply (fastforce dest:hd_SubobjsR)
  done
  


lemma SubobjsR_isClass:
assumes subo:"Subobjs\<^sub>R P C Cs"
shows "is_class P C"

using subo
proof (induct rule:Subobjs\<^sub>R.induct)
  case SubobjsR_Base thus ?case by assumption
next
  case SubobjsR_Rep thus ?case by (fastforce intro:subclsR_subcls1 subcls1_class)
qed


lemma Subobjs_isClass:
assumes subo:"Subobjs P C Cs"
shows "is_class P C"

using subo
proof (induct rule:Subobjs.induct)
  case Subobjs_Rep thus ?case by (rule SubobjsR_isClass)
next
  case (Subobjs_Sh C C' D Cs)
  have leq:"P \<turnstile> C \<preceq>\<^sup>* C'" and leqS:"P \<turnstile> C' \<prec>\<^sub>S D" by fact+
  hence "(C,D) \<in> (subcls1 P)\<^sup>+" by (fastforce intro:rtrancl_into_trancl1 subclsS_subcls1)
  thus ?case by (induct rule:trancl_induct, fastforce intro:subcls1_class)
qed


lemma Subobjs_subclsR:
assumes subo:"Subobjs P C (Cs@[D,D']@Cs')"
shows "P \<turnstile> D \<prec>\<^sub>R D'"

using subo
proof -
  from subo have "Subobjs P D (D#D'#Cs')" by -(rule Subobjs_Subobjs,simp)
  then obtain C' where subo':"Subobjs\<^sub>R P C' (D#D'#Cs')"
    by (induct rule:Subobjs.induct,blast+)
  hence "C' = D" by -(drule hd_SubobjsR,simp)
  with subo' have "Subobjs\<^sub>R P D (D#D'#Cs')" by simp
  thus ?thesis by (fastforce elim:Subobjs\<^sub>R.cases dest:hd_SubobjsR)
qed




lemma assumes subo:"Subobjs\<^sub>R P (hd Cs) (Cs@[D])" and notempty:"Cs \<noteq> []"
  shows butlast_Subobjs_Rep:"Subobjs\<^sub>R P (hd Cs) Cs"
using subo notempty
proof (induct Cs)
  case Nil thus ?case by simp
next
  case (Cons C' Cs')
  have subo:"Subobjs\<^sub>R P (hd(C'#Cs')) ((C'#Cs')@[D])"
    and IH:"\<lbrakk>Subobjs\<^sub>R P (hd Cs') (Cs'@[D]); Cs' \<noteq> []\<rbrakk> \<Longrightarrow> Subobjs\<^sub>R P (hd Cs') Cs'" by fact+
  from subo have subo':"Subobjs\<^sub>R P C' (C'#Cs'@[D])" by simp
  show ?case
  proof (cases "Cs' = []")
    case True
    with subo' have "Subobjs\<^sub>R P C' [C',D]" by simp
    hence "is_class P C'" by(rule SubobjsR_isClass)
    hence "Subobjs\<^sub>R P C' [C']" by (rule SubobjsR_Base)
    with True show ?thesis by simp
  next
    case False
    with subo' obtain D' where subo'':"Subobjs\<^sub>R P D' (Cs'@[D])"
      and subR:"P \<turnstile> C' \<prec>\<^sub>R D'"
      by (auto elim:Subobjs\<^sub>R.cases)
    from False subo'' have hd:"D' = hd Cs'"
      by (induct Cs',auto dest:hd_SubobjsR)
    with subo'' False IH have "Subobjs\<^sub>R P (hd Cs') Cs'" by simp 
    with subR hd have "Subobjs\<^sub>R P C' (C'#Cs')" by (fastforce intro:SubobjsR_Rep)
    thus ?thesis by simp
  qed
qed



lemma assumes subo:"Subobjs P C (Cs@[D])" and notempty:"Cs \<noteq> []"
  shows butlast_Subobjs:"Subobjs P C Cs"

using subo
proof (rule Subobjs.cases,auto)
  assume suboR:"Subobjs\<^sub>R P C (Cs@[D])" and "Subobjs P C (Cs@[D])"
  from suboR notempty have hd:"C = hd Cs"
    by (induct Cs,auto dest:hd_SubobjsR)
  with suboR notempty have "Subobjs\<^sub>R P (hd Cs) Cs"
    by(fastforce intro:butlast_Subobjs_Rep)
  with hd show "Subobjs P C Cs" by (fastforce intro:Subobjs_Rep)
next
  fix C' D' assume leq:"P \<turnstile> C \<preceq>\<^sup>* C'" and subS:"P \<turnstile> C' \<prec>\<^sub>S D'"
  and suboR:"Subobjs\<^sub>R P D' (Cs@[D])" and "Subobjs P C (Cs@[D])"
  from suboR notempty have hd:"D' = hd Cs"
    by (induct Cs,auto dest:hd_SubobjsR)
  with suboR notempty have "Subobjs\<^sub>R P (hd Cs) Cs"
    by(fastforce intro:butlast_Subobjs_Rep)
  with hd leq subS show "Subobjs P C Cs"
    by(fastforce intro:Subobjs_Sh)
qed




lemma assumes subo:"Subobjs P C (Cs@(rev Cs'))" and notempty:"Cs \<noteq> []"
  shows rev_appendSubobj:"Subobjs P C Cs"
using subo
proof(induct Cs')
  case Nil thus ?case by simp
next
  case (Cons D Ds)
  have subo':"Subobjs P C (Cs@rev(D#Ds))"
    and IH:"Subobjs P C (Cs@rev Ds) \<Longrightarrow> Subobjs P C Cs" by fact+
  from notempty subo' have "Subobjs P C (Cs@rev Ds)"
    by (fastforce intro:butlast_Subobjs)
  with IH show ?case by simp
qed



lemma appendSubobj:
assumes subo:"Subobjs P C (Cs@Cs')" and notempty:"Cs \<noteq> []"
shows "Subobjs P C Cs"

proof -
  obtain Cs'' where Cs'':"Cs'' = rev Cs'" by simp
  with subo have "Subobjs P C (Cs@(rev Cs''))" by simp
  with notempty show ?thesis by - (rule rev_appendSubobj)
qed




lemma SubobjsR_isSubobj:
  "Subobjs\<^sub>R P C Cs \<Longrightarrow> is_subobj P ((C,Cs))"
by(erule Subobjs\<^sub>R.induct,simp,
  auto dest:hd_SubobjsR intro:build_rec_isSubobj)

lemma leq_SubobjsR_isSubobj:
  "\<lbrakk>P \<turnstile> C \<preceq>\<^sup>* C'; P \<turnstile> C' \<prec>\<^sub>S D; Subobjs\<^sub>R P D Cs\<rbrakk> 
\<Longrightarrow> is_subobj P ((C,Cs))"

apply (subgoal_tac "is_subobj P ((C,[D]))")
 apply (frule hd_SubobjsR)
 apply (drule SubobjsR_isSubobj)
 apply (erule exE)
 apply (simp del: is_subobj.simps)
 apply (erule isSubobj_isSubobj_isSubobj)
 apply simp
apply auto
done


lemma Subobjs_isSubobj:
  "Subobjs P C Cs \<Longrightarrow> is_subobj P ((C,Cs))"
by (auto elim:Subobjs.induct SubobjsR_isSubobj 
  simp add:leq_SubobjsR_isSubobj)



subsection \<open>Paths\<close>


subsection \<open>Appending paths\<close>

text\<open>Avoided name clash by calling one path Path.\<close>

definition path_via :: "prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> path \<Rightarrow> bool" ("_ \<turnstile> Path _ to _ via _ " [51,51,51,51] 50) where
  "P \<turnstile> Path C to D via Cs \<equiv> Subobjs P C Cs \<and> last Cs = D"

definition path_unique :: "prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool" ("_ \<turnstile> Path _ to _ unique" [51,51,51] 50) where
  "P \<turnstile> Path C to D unique \<equiv> \<exists>!Cs. Subobjs P C Cs \<and> last Cs = D"

definition appendPath :: "path \<Rightarrow> path \<Rightarrow> path" (infixr "@\<^sub>p" 65) where
  "Cs @\<^sub>p Cs' \<equiv> if (last Cs = hd Cs') then Cs @ (tl Cs') else Cs'"


lemma appendPath_last: "Cs \<noteq> [] \<Longrightarrow> last Cs = last (Cs'@\<^sub>pCs)"
by(auto simp:appendPath_def last_append)(cases Cs, simp_all)+



inductive
  casts_to :: "prog \<Rightarrow> ty \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool"
    ("_ \<turnstile> _ casts _ to _ " [51,51,51,51] 50)
  for P :: prog
where

  casts_prim: "\<forall>C. T \<noteq> Class C \<Longrightarrow> P \<turnstile> T casts v to v"

| casts_null: "P \<turnstile> Class C casts Null to Null"

| casts_ref: "\<lbrakk> P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P \<turnstile> Class C casts Ref(a,Cs) to Ref(a,Ds)"


inductive
  Casts_to :: "prog \<Rightarrow> ty list \<Rightarrow> val list \<Rightarrow> val list \<Rightarrow> bool"
    ("_ \<turnstile> _ Casts _ to _ " [51,51,51,51] 50)
  for P :: prog
where

  Casts_Nil: "P \<turnstile> [] Casts [] to []"

| Casts_Cons: "\<lbrakk> P \<turnstile> T casts v to v'; P \<turnstile> Ts Casts vs to vs' \<rbrakk>
  \<Longrightarrow> P \<turnstile> (T#Ts) Casts (v#vs) to (v'#vs')"



lemma length_Casts_vs:
  "P \<turnstile> Ts Casts vs to vs' \<Longrightarrow> length Ts = length vs"
by (induct rule:Casts_to.induct,simp_all)

lemma length_Casts_vs':
  "P \<turnstile> Ts Casts vs to vs' \<Longrightarrow> length Ts = length vs'"
by (induct rule:Casts_to.induct,simp_all)



subsection \<open>The relation on paths\<close>

inductive_set
  leq_path1 :: "prog \<Rightarrow> cname \<Rightarrow> (path \<times> path) set"
  and leq_path1' :: "prog \<Rightarrow> cname \<Rightarrow> [path, path] \<Rightarrow> bool" ("_,_ \<turnstile> _ \<sqsubset>\<^sup>1 _" [71,71,71] 70)
  for P :: prog and C :: cname
where
  "P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Ds \<equiv> (Cs,Ds) \<in> leq_path1 P C"
| leq_pathRep: "\<lbrakk> Subobjs P C Cs; Subobjs P C Ds; Cs = butlast Ds\<rbrakk>
  \<Longrightarrow> P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Ds"
| leq_pathSh:  "\<lbrakk> Subobjs P C Cs; P \<turnstile> last Cs \<prec>\<^sub>S D \<rbrakk>
  \<Longrightarrow> P,C \<turnstile> Cs \<sqsubset>\<^sup>1 [D]"

abbreviation
  leq_path :: "prog \<Rightarrow> cname \<Rightarrow> [path, path] \<Rightarrow> bool" ("_,_ \<turnstile> _ \<sqsubseteq> _"  [71,71,71] 70) where
  "P,C \<turnstile> Cs \<sqsubseteq> Ds \<equiv> (Cs,Ds) \<in> (leq_path1 P C)\<^sup>*"


lemma leq_path_rep:
  "\<lbrakk> Subobjs P C (Cs@[C']); Subobjs P C (Cs@[C',C''])\<rbrakk> 
\<Longrightarrow> P,C \<turnstile> (Cs@[C']) \<sqsubset>\<^sup>1 (Cs@[C',C''])"
by(rule leq_pathRep,simp_all add:butlast_tail)

lemma leq_path_sh:
  "\<lbrakk> Subobjs P C (Cs@[C']); P \<turnstile> C' \<prec>\<^sub>S C''\<rbrakk> 
\<Longrightarrow> P,C \<turnstile> (Cs@[C']) \<sqsubset>\<^sup>1 [C'']"
by(erule leq_pathSh)simp




subsection\<open>Member lookups\<close>

definition FieldDecls :: "prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> (path \<times> ty) set" where
  "FieldDecls P C F \<equiv> 
   {(Cs,T). Subobjs P C Cs \<and> (\<exists>Bs fs ms. class P (last Cs) = Some(Bs,fs,ms)
                                    \<and> map_of fs F = Some T)}"

definition LeastFieldDecl  :: "prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> path \<Rightarrow> bool"
    ("_ \<turnstile> _ has least _:_ via _" [51,0,0,0,51] 50) where
  "P \<turnstile> C has least F:T via Cs \<equiv>
   (Cs,T) \<in> FieldDecls P C F \<and>
   (\<forall>(Cs',T') \<in> FieldDecls P C F. P,C \<turnstile> Cs \<sqsubseteq> Cs')"

definition MethodDefs :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> (path \<times> method)set" where
  "MethodDefs P C M \<equiv>
   {(Cs,mthd). Subobjs P C Cs \<and> (\<exists>Bs fs ms. class P (last Cs) = Some(Bs,fs,ms)
                                    \<and> map_of ms M = Some mthd)}"

  \<comment> \<open>needed for well formed criterion\<close>
definition HasMethodDef :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> method \<Rightarrow> path \<Rightarrow> bool"
    ("_ \<turnstile> _ has _ = _ via _" [51,0,0,0,51] 50) where
  "P \<turnstile> C has M = mthd via Cs \<equiv> (Cs,mthd) \<in> MethodDefs P C M"

definition LeastMethodDef :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> method \<Rightarrow> path \<Rightarrow> bool"
    ("_ \<turnstile> _ has least _ = _ via _" [51,0,0,0,51] 50) where
  "P \<turnstile> C has least M = mthd via Cs \<equiv>
   (Cs,mthd) \<in> MethodDefs P C M \<and>
   (\<forall>(Cs',mthd') \<in> MethodDefs P C M. P,C \<turnstile> Cs \<sqsubseteq> Cs')"

definition MinimalMethodDefs :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> (path \<times> method)set" where
  "MinimalMethodDefs P C M \<equiv> 
      {(Cs,mthd). (Cs,mthd) \<in> MethodDefs P C M \<and> 
         (\<forall>(Cs',mthd')\<in> MethodDefs P C M. P,C \<turnstile> Cs' \<sqsubseteq> Cs \<longrightarrow> Cs' = Cs)}"

definition OverriderMethodDefs :: "prog \<Rightarrow> subobj \<Rightarrow> mname \<Rightarrow> (path \<times> method)set" where
  "OverriderMethodDefs P R M \<equiv>
      {(Cs,mthd). \<exists>Cs' mthd'. P \<turnstile> (ldc R) has least M = mthd' via Cs' \<and>
                      (Cs,mthd) \<in> MinimalMethodDefs P (mdc R) M \<and> 
                      P,mdc R \<turnstile> Cs \<sqsubseteq> (snd R)@\<^sub>pCs'}"

definition FinalOverriderMethodDef :: "prog \<Rightarrow> subobj \<Rightarrow> mname \<Rightarrow> method \<Rightarrow> path \<Rightarrow> bool"
    ("_ \<turnstile> _ has overrider _ = _ via _" [51,0,0,0,51] 50) where
  "P \<turnstile> R has overrider M = mthd via Cs \<equiv> 
      (Cs,mthd) \<in> OverriderMethodDefs P R M \<and> 
      card(OverriderMethodDefs P R M) = 1"
      (*(\<forall>(Cs',mthd') \<in> OverriderMethodDefs P R M. Cs = Cs' \<and> mthd = mthd')"*)


inductive
  SelectMethodDef :: "prog \<Rightarrow> cname \<Rightarrow> path \<Rightarrow> mname \<Rightarrow> method \<Rightarrow> path \<Rightarrow> bool"
     ("_ \<turnstile> '(_,_') selects _ = _ via _" [51,0,0,0,0,51] 50)
  for P :: prog
where

  dyn_unique:
    "P \<turnstile> C has least M = mthd via Cs' \<Longrightarrow> P \<turnstile> (C,Cs) selects M = mthd via Cs'"

| dyn_ambiguous:
    "\<lbrakk>\<forall>mthd Cs'. \<not> P \<turnstile> C has least M = mthd via Cs'; 
      P \<turnstile> (C,Cs) has overrider M = mthd via Cs'\<rbrakk>
  \<Longrightarrow> P \<turnstile> (C,Cs) selects M = mthd via Cs'"



lemma sees_fields_fun:
  "(Cs,T) \<in> FieldDecls P C F \<Longrightarrow> (Cs,T') \<in> FieldDecls P C F \<Longrightarrow> T = T'"
by(fastforce simp:FieldDecls_def)

lemma sees_field_fun:
  "\<lbrakk>P \<turnstile> C has least F:T via Cs; P \<turnstile> C has least F:T' via Cs\<rbrakk>
  \<Longrightarrow> T = T'"
by (fastforce simp:LeastFieldDecl_def dest:sees_fields_fun)


lemma has_least_method_has_method:
  "P \<turnstile> C has least M = mthd via Cs \<Longrightarrow> P \<turnstile> C has M = mthd via Cs"
by (simp add:LeastMethodDef_def HasMethodDef_def)


lemma visible_methods_exist:
  "(Cs,mthd) \<in> MethodDefs P C M \<Longrightarrow>
  (\<exists>Bs fs ms. class P (last Cs) = Some(Bs,fs,ms) \<and> map_of ms M = Some mthd)"
by(auto simp:MethodDefs_def)


lemma sees_methods_fun:
  "(Cs,mthd) \<in> MethodDefs P C M \<Longrightarrow> (Cs,mthd') \<in> MethodDefs P C M \<Longrightarrow> mthd = mthd'"
by(fastforce simp:MethodDefs_def)

lemma sees_method_fun:
  "\<lbrakk>P \<turnstile> C has least M = mthd via Cs; P \<turnstile> C has least M = mthd' via Cs\<rbrakk>
  \<Longrightarrow> mthd = mthd'"
by (fastforce simp:LeastMethodDef_def dest:sees_methods_fun)


lemma overrider_method_fun:
assumes overrider:"P \<turnstile> (C,Cs) has overrider M = mthd via Cs'"
  and overrider':"P \<turnstile> (C,Cs) has overrider M = mthd' via Cs''"
shows "mthd = mthd' \<and> Cs' = Cs''"
proof -
  from overrider' have omd:"(Cs'',mthd') \<in> OverriderMethodDefs P (C,Cs) M"
    by(simp_all add:FinalOverriderMethodDef_def)
  from overrider have "(Cs',mthd) \<in> OverriderMethodDefs P (C,Cs) M"
    and "card(OverriderMethodDefs P (C,Cs) M) = 1" 
    by(simp_all add:FinalOverriderMethodDef_def)
  hence "\<forall>(Ds,mthd'') \<in> OverriderMethodDefs P (C,Cs) M. (Cs',mthd) = (Ds,mthd'')"
    by(fastforce simp:card_Suc_eq)
  with omd show ?thesis by fastforce
qed


end
