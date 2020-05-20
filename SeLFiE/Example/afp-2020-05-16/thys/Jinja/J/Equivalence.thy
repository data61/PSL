(*  Title:      Jinja/J/Equivalence.thy
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

section \<open>Equivalence of Big Step and Small Step Semantics\<close>

theory Equivalence imports BigStep SmallStep WWellForm begin

subsection\<open>Small steps simulate big step\<close>

subsubsection "Cast"

lemma CastReds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>Cast C e',s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule CastRed)
done
(*>*)

lemma CastRedsNull:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CastReds)
apply(rule RedCastNull)
done
(*>*)

lemma CastRedsAddr:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>addr a,s'\<rangle>; hp s' a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>addr a,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CastReds)
apply(erule (1) RedCast)
done
(*>*)

lemma CastRedsFail:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>addr a,s'\<rangle>; hp s' a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>THROW ClassCast,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CastReds)
apply(erule (1) RedCastFail)
done
(*>*)

lemma CastRedsThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CastReds)
apply(rule red_reds.CastThrow)
done
(*>*)

subsubsection "LAss"

lemma LAssReds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle> V:=e,s\<rangle> \<rightarrow>* \<langle> V:=e',s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule LAssRed)
done
(*>*)

lemma LAssRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Val v,(h',l')\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle> V:=e,s\<rangle> \<rightarrow>* \<langle>unit,(h',l'(V\<mapsto>v))\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule LAssReds)
apply(rule RedLAss)
done
(*>*)

lemma LAssRedsThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle> V:=e,s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule LAssReds)
apply(rule red_reds.LAssThrow)
done
(*>*)

subsubsection "BinOp"

lemma BinOp1Reds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle> e \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>e' \<guillemotleft>bop\<guillemotright> e\<^sub>2, s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule BinOpRed1)
done
(*>*)

lemma BinOp2Reds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e, s\<rangle> \<rightarrow>* \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule BinOpRed2)
done
(*>*)

lemma BinOpRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v\<^sub>2,s\<^sub>2\<rangle>; binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule BinOp1Reds)
apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp2Reds)
apply(rule RedBinOp)
apply simp
done
(*>*)

lemma BinOpRedsThrow1:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>throw e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>throw e', s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp1Reds)
apply(rule red_reds.BinOpThrow1)
done
(*>*)

lemma BinOpRedsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule BinOp1Reds)
apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp2Reds)
apply(rule red_reds.BinOpThrow2)
done
(*>*)

subsubsection "FAcc"

lemma FAccReds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D}, s\<rangle> \<rightarrow>* \<langle>e'\<bullet>F{D}, s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule FAccRed)
done
(*>*)

lemma FAccRedsVal:
  "\<lbrakk>P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>addr a,s'\<rangle>; hp s' a = Some(C,fs); fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<rangle> \<rightarrow>* \<langle>Val v,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(erule (1) RedFAcc)
done
(*>*)

lemma FAccRedsNull:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(rule RedFAccNull)
done
(*>*)

lemma FAccRedsThrow:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(rule red_reds.FAccThrow)
done
(*>*)

subsubsection "FAss"

lemma FAssReds1:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D}:=e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>e'\<bullet>F{D}:=e\<^sub>2, s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule FAssRed1)
done
(*>*)

lemma FAssReds2:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Val v\<bullet>F{D}:=e, s\<rangle> \<rightarrow>* \<langle>Val v\<bullet>F{D}:=e', s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule FAssRed2)
done
(*>*)

lemma FAssRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2)\<rangle>; Some(C,fs) = h\<^sub>2 a \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>unit, (h\<^sub>2(a\<mapsto>(C,fs((F,D)\<mapsto>v))),l\<^sub>2)\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(rule RedFAss)
apply simp
done
(*>*)

lemma FAssRedsNull:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW NullPointer, s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(rule RedFAssNull)
done
(*>*)

lemma FAssRedsThrow1:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>throw e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D}:=e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>throw e', s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds1)
apply(rule red_reds.FAssThrow1)
done
(*>*)

lemma FAssRedsThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(rule red_reds.FAssThrow2)
done
(*>*)

subsubsection";;"

lemma  SeqReds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e;;e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>e';;e\<^sub>2, s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule SeqRed)
done
(*>*)

lemma SeqRedsThrow:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>throw e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e;;e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>throw e', s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule SeqReds)
apply(rule red_reds.SeqThrow)
done
(*>*)

lemma SeqReds2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2',s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1;;e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2',s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule SeqReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedSeq)
apply assumption
done
(*>*)


subsubsection"If"

lemma CondReds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<rangle> \<rightarrow>* \<langle>if (e') e\<^sub>1 else e\<^sub>2,s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule CondRed)
done
(*>*)

lemma CondRedsThrow:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(rule red_reds.CondThrow)
done
(*>*)

lemma CondReds2T:
  "\<lbrakk>P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>1, s\<^sub>1\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedCondT)
apply assumption
done
(*>*)

lemma CondReds2F:
  "\<lbrakk>P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>false,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2, s\<^sub>1\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedCondF)
apply assumption
done
(*>*)


subsubsection "While"

lemma WhileFReds:
  "P \<turnstile> \<langle>b,s\<rangle> \<rightarrow>* \<langle>false,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>while (b) c,s\<rangle> \<rightarrow>* \<langle>unit,s'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedWhile)
apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(rule RedCondF)
done
(*>*)

lemma WhileRedsThrow:
  "P \<turnstile> \<langle>b,s\<rangle> \<rightarrow>* \<langle>throw e,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>while (b) c,s\<rangle> \<rightarrow>* \<langle>throw e,s'\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedWhile)
apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(rule red_reds.CondThrow)
done
(*>*)

lemma WhileTReds:
  "\<lbrakk> P \<turnstile> \<langle>b,s\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>; P \<turnstile> \<langle>while (b) c,s\<^sub>2\<rangle> \<rightarrow>* \<langle>e,s\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (b) c,s\<^sub>0\<rangle> \<rightarrow>* \<langle>e,s\<^sub>3\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedWhile)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedCondT)
apply(rule rtrancl_trans)
 apply(erule SeqReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedSeq)
apply assumption
done
(*>*)

lemma WhileTRedsThrow:
  "\<lbrakk> P \<turnstile> \<langle>b,s\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (b) c,s\<^sub>0\<rangle> \<rightarrow>* \<langle>throw e,s\<^sub>2\<rangle>"
(*<*)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedWhile)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedCondT)
apply(rule rtrancl_into_rtrancl)
 apply(erule SeqReds)
apply(rule red_reds.SeqThrow)
done
(*>*)

subsubsection"Throw"

lemma ThrowReds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>throw e,s\<rangle> \<rightarrow>* \<langle>throw e',s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule ThrowRed)
done
(*>*)

lemma ThrowRedsNull:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>throw e,s\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule ThrowReds)
apply(rule RedThrowNull)
done
(*>*)

lemma ThrowRedsThrow:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>throw e,s\<rangle> \<rightarrow>* \<langle>throw a,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule ThrowReds)
apply(rule red_reds.ThrowThrow)
done
(*>*)

subsubsection "InitBlock"

lemma InitBlockReds_aux:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow>
  \<forall>h l h' l' v. s = (h,l(V\<mapsto>v)) \<longrightarrow> s' = (h',l') \<longrightarrow>
  P \<turnstile> \<langle>{V:T := Val v; e},(h,l)\<rangle> \<rightarrow>* \<langle>{V:T := Val(the(l' V)); e'},(h',l'(V:=(l V)))\<rangle>"
(*<*)
apply(erule converse_rtrancl_induct2)
 apply(fastforce simp: fun_upd_same simp del:fun_upd_apply)
apply clarify
apply(rename_tac e0 X Y e1 h1 l1 h0 l0 h2 l2 v0)
apply(subgoal_tac "V \<in> dom l1")
 prefer 2
 apply(drule red_lcl_incr)
 apply simp
apply clarsimp
apply(rename_tac v1)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule InitBlockRed)
  apply assumption
 apply simp
apply(erule_tac x = "l1(V := l0 V)" in allE)
apply(erule_tac x = v1 in allE)
apply(erule impE)
 apply(rule ext)
 apply(simp add:fun_upd_def)
apply(simp add:fun_upd_def)
done
(*>*)

lemma InitBlockReds:
 "P \<turnstile> \<langle>e, (h,l(V\<mapsto>v))\<rangle> \<rightarrow>* \<langle>e', (h',l')\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>{V:T := Val v; e}, (h,l)\<rangle> \<rightarrow>* \<langle>{V:T := Val(the(l' V)); e'}, (h',l'(V:=(l V)))\<rangle>"
(*<*)by(blast dest:InitBlockReds_aux)(*>*)

lemma InitBlockRedsFinal:
  "\<lbrakk> P \<turnstile> \<langle>e,(h,l(V\<mapsto>v))\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>; final e' \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>{V:T := Val v; e},(h,l)\<rangle> \<rightarrow>* \<langle>e',(h', l'(V := l V))\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule InitBlockReds)
apply(fast elim!:finalE intro:RedInitBlock InitBlockThrow)
done
(*>*)


subsubsection "Block"

lemma BlockRedsFinal:
assumes reds: "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2)\<rangle>" and fin: "final e\<^sub>2"
shows "\<And>h\<^sub>0 l\<^sub>0. s\<^sub>0 = (h\<^sub>0,l\<^sub>0(V:=None)) \<Longrightarrow> P \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2(V:=l\<^sub>0 V))\<rangle>"
(*<*)
using reds
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case
    by(fastforce intro:finalE[OF fin] RedBlock BlockThrow
                simp del:fun_upd_apply)
next
  case (step e\<^sub>0 s\<^sub>0 e\<^sub>1 s\<^sub>1)
  have red: "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle>"
   and reds: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2)\<rangle>"
   and IH: "\<And>h l. s\<^sub>1 = (h,l(V := None))
                \<Longrightarrow> P \<turnstile> \<langle>{V:T; e\<^sub>1},(h,l)\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2, l\<^sub>2(V := l V))\<rangle>"
   and s\<^sub>0: "s\<^sub>0 = (h\<^sub>0, l\<^sub>0(V := None))" by fact+
  obtain h\<^sub>1 l\<^sub>1 where s\<^sub>1: "s\<^sub>1 = (h\<^sub>1,l\<^sub>1)" by fastforce
  show ?case
  proof cases
    assume "assigned V e\<^sub>0"
    then obtain v e where e\<^sub>0: "e\<^sub>0 = V := Val v;; e"
      by (unfold assigned_def)blast
    from red e\<^sub>0 s\<^sub>0 have e\<^sub>1: "e\<^sub>1 = unit;;e" and s\<^sub>1: "s\<^sub>1 = (h\<^sub>0, l\<^sub>0(V \<mapsto> v))"
      by auto
    from e\<^sub>1 fin have "e\<^sub>1 \<noteq> e\<^sub>2" by (auto simp:final_def)
    then obtain e' s' where red1: "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
      and reds': "P \<turnstile> \<langle>e',s'\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2)\<rangle>"
      using converse_rtranclE2[OF reds] by blast
    from red1 e\<^sub>1 have es': "e' = e" "s' = s\<^sub>1" by auto
    show ?case using e\<^sub>0 s\<^sub>1 es' reds'
      by(fastforce intro!: InitBlockRedsFinal[OF _ fin] simp del:fun_upd_apply)
  next
    assume unass: "\<not> assigned V e\<^sub>0"
    show ?thesis
    proof (cases "l\<^sub>1 V")
      assume None: "l\<^sub>1 V = None"
      hence "P \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow> \<langle>{V:T; e\<^sub>1},(h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V))\<rangle>"
        using s\<^sub>0 s\<^sub>1 red by(simp add: BlockRedNone[OF _ _ unass])
      moreover
      have "P \<turnstile> \<langle>{V:T; e\<^sub>1},(h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V))\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2, l\<^sub>2(V := l\<^sub>0 V))\<rangle>"
        using IH[of _ "l\<^sub>1(V := l\<^sub>0 V)"] s\<^sub>1 None by(simp add:fun_upd_idem)
      ultimately show ?case by(rule converse_rtrancl_into_rtrancl)
    next
      fix v assume Some: "l\<^sub>1 V = Some v"
      hence "P \<turnstile> \<langle>{V:T;e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow> \<langle>{V:T := Val v; e\<^sub>1},(h\<^sub>1,l\<^sub>1(V := l\<^sub>0 V))\<rangle>"
        using s\<^sub>0 s\<^sub>1 red by(simp add: BlockRedSome[OF _ _ unass])
      moreover
      have "P \<turnstile> \<langle>{V:T := Val v; e\<^sub>1},(h\<^sub>1,l\<^sub>1(V:= l\<^sub>0 V))\<rangle> \<rightarrow>*
                \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2(V:=l\<^sub>0 V))\<rangle>"
        using InitBlockRedsFinal[OF _ fin,of _ _ "l\<^sub>1(V:=l\<^sub>0 V)" V]
              Some reds s\<^sub>1 by(simp add:fun_upd_idem)
      ultimately show ?case by(rule converse_rtrancl_into_rtrancl)
    qed
  qed
qed
(*>*)


subsubsection "try-catch"

lemma TryReds:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>try e catch(C V) e\<^sub>2,s\<rangle> \<rightarrow>* \<langle>try e' catch(C V) e\<^sub>2,s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule TryRed)
done
(*>*)

lemma TryRedsVal:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Val v,s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>try e catch(C V) e\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Val v,s'\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule TryReds)
apply(rule RedTry)
done
(*>*)

lemma TryCatchRedsFinal:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Throw a,(h\<^sub>1,l\<^sub>1)\<rangle>;  h\<^sub>1 a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C;
     P \<turnstile> \<langle>e\<^sub>2, (h\<^sub>1, l\<^sub>1(V \<mapsto> Addr a))\<rangle> \<rightarrow>* \<langle>e\<^sub>2', (h\<^sub>2,l\<^sub>2)\<rangle>; final e\<^sub>2' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2', (h\<^sub>2, l\<^sub>2(V := l\<^sub>1 V))\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule TryReds)
apply(rule converse_rtrancl_into_rtrancl)
 apply(rule RedTryCatch)
  apply fastforce
 apply assumption
apply(rule InitBlockRedsFinal)
 apply assumption
apply(simp)
done
(*>*)

lemma TryRedsFail:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<rangle> \<rightarrow>* \<langle>Throw a,(h,l)\<rangle>; h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<rangle> \<rightarrow>* \<langle>Throw a,(h,l)\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule TryReds)
apply(fastforce intro!: RedTryFail)
done
(*>*)

subsubsection "List"

lemma ListReds1:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e#es,s\<rangle> [\<rightarrow>]* \<langle>e' # es,s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule ListRed1)
done
(*>*)

lemma ListReds2:
  "P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>Val v # es,s\<rangle> [\<rightarrow>]* \<langle>Val v # es',s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule ListRed2)
done
(*>*)

lemma ListRedsVal:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>es',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e#es,s\<^sub>0\<rangle> [\<rightarrow>]* \<langle>Val v # es',s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule ListReds1)
apply(erule ListReds2)
done
(*>*)

subsubsection"Call"

text\<open>First a few lemmas on what happens to free variables during redction.\<close>

lemma assumes wf: "wwf_J_prog P"
shows Red_fv: "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> fv e' \<subseteq> fv e"
  and  "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> fvs es' \<subseteq> fvs es"
(*<*)
proof (induct rule:red_reds_inducts)
  case (RedCall h l a C fs M Ts T pns body D vs)
  hence "fv body \<subseteq> {this} \<union> set pns"
    using assms by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)
  with RedCall.hyps show ?case by fastforce
qed auto
(*>*)


lemma Red_dom_lcl:
  "P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fv e" and
  "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fvs es"
(*<*)
proof (induct rule:red_reds_inducts)
  case RedLAss thus ?case by(force split:if_splits)
next
  case CallParams thus ?case by(force split:if_splits)
next
  case BlockRedNone thus ?case by clarsimp (fastforce split:if_splits)
next
  case BlockRedSome thus ?case by clarsimp (fastforce split:if_splits)
next
  case InitBlockRed thus ?case by clarsimp (fastforce split:if_splits)
qed auto
(*>*)

lemma Reds_dom_lcl:
  "\<lbrakk> wwf_J_prog P; P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle> \<rbrakk> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fv e"
(*<*)
apply(erule converse_rtrancl_induct_red)
 apply blast
apply(blast dest: Red_fv Red_dom_lcl)
done
(*>*)

text\<open>Now a few lemmas on the behaviour of blocks during reduction.\<close>

(* If you want to avoid the premise "distinct" further down \<dots>
consts upd_vals :: "locals \<Rightarrow> vname list \<Rightarrow> val list \<Rightarrow> val list"
primrec
"upd_vals l [] vs = []"
"upd_vals l (V#Vs) vs = (if V \<in> set Vs then hd vs else the(l V)) #
                        upd_vals l Vs (tl vs)"

lemma [simp]: "\<And>vs. length(upd_vals l Vs vs) = length Vs"
by(induct Vs, auto)
*)
lemma override_on_upd_lemma:
  "(override_on f (g(a\<mapsto>b)) A)(a := g a) = override_on f g (insert a A)"
(*<*)
apply(rule ext)
apply(simp add:override_on_def)
done

declare fun_upd_apply[simp del] map_upds_twist[simp del]
(*>*)


lemma blocksReds:
  "\<And>l. \<lbrakk> length Vs = length Ts; length vs = length Ts; distinct Vs;
         P \<turnstile> \<langle>e, (h,l(Vs [\<mapsto>] vs))\<rangle> \<rightarrow>* \<langle>e', (h',l')\<rangle> \<rbrakk>
        \<Longrightarrow> P \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l)\<rangle> \<rightarrow>* \<langle>blocks(Vs,Ts,map (the \<circ> l') Vs,e'), (h',override_on l' l (set Vs))\<rangle>"
(*<*)
proof(induct Vs Ts vs e rule:blocks_induct)
  case (1 V Vs T Ts v vs e) show ?case
    using InitBlockReds[OF "1.hyps"[of "l(V\<mapsto>v)"]] "1.prems"
    by(auto simp:override_on_upd_lemma)
qed auto
(*>*)


lemma blocksFinal:
 "\<And>l. \<lbrakk> length Vs = length Ts; length vs = length Ts; final e \<rbrakk> \<Longrightarrow>
       P \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l)\<rangle> \<rightarrow>* \<langle>e, (h,l)\<rangle>"
(*<*)
proof(induct Vs Ts vs e rule:blocks_induct)
  case 1
  show ?case using "1.prems" InitBlockReds[OF "1.hyps"]
    by(fastforce elim!:finalE elim: rtrancl_into_rtrancl[OF _ RedInitBlock]
                                   rtrancl_into_rtrancl[OF _ InitBlockThrow])
qed auto
(*>*)


lemma blocksRedsFinal:
assumes wf: "length Vs = length Ts" "length vs = length Ts" "distinct Vs"
    and reds: "P \<turnstile> \<langle>e, (h,l(Vs [\<mapsto>] vs))\<rangle> \<rightarrow>* \<langle>e', (h',l')\<rangle>"
    and fin: "final e'" and l'': "l'' = override_on l' l (set Vs)"
shows "P \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l)\<rangle> \<rightarrow>* \<langle>e', (h',l'')\<rangle>"
(*<*)
proof -
  let ?bv = "blocks(Vs,Ts,map (the o l') Vs,e')"
  have "P \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l)\<rangle> \<rightarrow>* \<langle>?bv, (h',l'')\<rangle>"
    using l'' by simp (rule blocksReds[OF wf reds])
  also have "P \<turnstile> \<langle>?bv, (h',l'')\<rangle> \<rightarrow>* \<langle>e', (h',l'')\<rangle>"
    using wf by(fastforce intro:blocksFinal fin)
  finally show ?thesis .
qed
(*>*)

text\<open>An now the actual method call reduction lemmas.\<close>

lemma CallRedsObj:
 "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<rangle> \<rightarrow>* \<langle>e'\<bullet>M(es),s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule CallObj)
done
(*>*)


lemma CallRedsParams:
 "P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>(Val v)\<bullet>M(es),s\<rangle> \<rightarrow>* \<langle>(Val v)\<bullet>M(es'),s'\<rangle>"
(*<*)
apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(erule CallParams)
done
(*>*)


lemma CallRedsFinal:
assumes wwf: "wwf_J_prog P"
and "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1\<rangle>"
      "P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
      "h\<^sub>2 a = Some(C,fs)" "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
      "size vs = size pns"
and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Addr a, pns[\<mapsto>]vs]"
and body: "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>3)\<rangle>"
and "final ef"
shows "P \<turnstile> \<langle>e\<bullet>M(es), s\<^sub>0\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2)\<rangle>"
(*<*)
proof -
  have wf: "size Ts = size pns \<and> distinct pns \<and> this \<notin> set pns"
    and wt: "fv body \<subseteq> {this} \<union> set pns"
    using assms by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  from body[THEN Red_lcl_add, of l\<^sub>2]
  have body': "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2(this\<mapsto> Addr a, pns[\<mapsto>]vs))\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2++l\<^sub>3)\<rangle>"
    by (simp add:l\<^sub>2')
  have "dom l\<^sub>3 \<subseteq> {this} \<union> set pns"
    using Reds_dom_lcl[OF wwf body] wt l\<^sub>2' set_take_subset by force
  hence eql\<^sub>2: "override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns) = l\<^sub>2"
    by(fastforce simp add:map_add_def override_on_def fun_eq_iff)
  have "P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<rightarrow>* \<langle>(addr a)\<bullet>M(es),s\<^sub>1\<rangle>" by(rule CallRedsObj)(rule assms(2))
  also have "P \<turnstile> \<langle>(addr a)\<bullet>M(es),s\<^sub>1\<rangle> \<rightarrow>*
                 \<langle>(addr a)\<bullet>M(map Val vs),(h\<^sub>2,l\<^sub>2)\<rangle>"
    by(rule CallRedsParams)(rule assms(3))
  also have "P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), (h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow>
                 \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body), (h\<^sub>2,l\<^sub>2)\<rangle>"
    by(rule RedCall)(auto simp: assms wf, rule assms(5))
  also (rtrancl_into_rtrancl) have "P \<turnstile> \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body), (h\<^sub>2,l\<^sub>2)\<rangle>
                 \<rightarrow>* \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns))\<rangle>"
    by(rule blocksRedsFinal, insert assms wf body', simp_all)
  finally show ?thesis using eql\<^sub>2 by simp
qed
(*>*)


lemma CallRedsThrowParams:
  "\<lbrakk> P \<turnstile> \<langle>e,s0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs\<^sub>1 @ throw a # es\<^sub>2,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CallRedsObj)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsParams)
apply(rule CallThrowParams)
apply simp
done
(*>*)


lemma CallRedsThrowObj:
  "P \<turnstile> \<langle>e,s0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s0\<rangle> \<rightarrow>* \<langle>throw a,s\<^sub>1\<rangle>"
(*<*)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsObj)
apply(rule CallThrowObj)
done
(*>*)


lemma CallRedsNull:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s\<^sub>2\<rangle>"
(*<*)
apply(rule rtrancl_trans)
 apply(erule CallRedsObj)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsParams)
apply(rule RedCallNull)
done
(*>*)

subsubsection "The main Theorem"

lemma assumes wwf: "wwf_J_prog P"
shows big_by_small: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
and bigs_by_smalls: "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"
(*<*)
proof (induct rule: eval_evals.inducts)
  case New thus ?case by (auto simp:RedNew)
next
  case NewFail thus ?case by (auto simp:RedNewFail)
next
  case Cast thus ?case by(fastforce intro:CastRedsAddr)
next
  case CastNull thus ?case by(simp add:CastRedsNull)
next
  case CastFail thus ?case by(fastforce intro!:CastRedsFail)
next
  case CastThrow thus ?case by(auto dest!:eval_final simp:CastRedsThrow)
next
  case Val thus ?case by simp
next
  case BinOp thus ?case by(auto simp:BinOpRedsVal)
next
  case BinOpThrow1 thus ?case by(auto dest!:eval_final simp: BinOpRedsThrow1)
next
  case BinOpThrow2 thus ?case by(auto dest!:eval_final simp: BinOpRedsThrow2)
next
  case Var thus ?case by (auto simp:RedVar)
next
  case LAss thus ?case by(auto simp: LAssRedsVal)
next
  case LAssThrow thus ?case by(auto dest!:eval_final simp: LAssRedsThrow)
next
  case FAcc thus ?case by(auto intro:FAccRedsVal)
next
  case FAccNull thus ?case by(simp add:FAccRedsNull)
next
  case FAccThrow thus ?case by(auto dest!:eval_final simp:FAccRedsThrow)
next
  case FAss thus ?case by(auto simp:FAssRedsVal)
next
  case FAssNull thus ?case by(auto simp:FAssRedsNull)
next
  case FAssThrow1 thus ?case by(auto dest!:eval_final simp:FAssRedsThrow1)
next
  case FAssThrow2 thus ?case by(auto dest!:eval_final simp:FAssRedsThrow2)
next
  case CallObjThrow thus ?case by(auto dest!:eval_final simp:CallRedsThrowObj)
next
  case CallNull thus ?case by(simp add:CallRedsNull)
next
  case CallParamsThrow thus ?case
    by(auto dest!:evals_final simp:CallRedsThrowParams)
next
  case (Call e s\<^sub>0 a s\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 C fs M Ts T pns body D l\<^sub>2' e' h\<^sub>3 l\<^sub>3)
  have IHe: "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>addr a,s\<^sub>1\<rangle>"
    and IHes: "P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
    and h\<^sub>2a: "h\<^sub>2 a = Some(C,fs)"
    and "method": "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
    and same_length: "length vs = length pns"
    and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Addr a, pns[\<mapsto>]vs]"
    and eval_body: "P \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle>"
    and IHbody: "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle>" by fact+
  show "P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>2)\<rangle>"
    using "method" same_length l\<^sub>2' h\<^sub>2a IHbody eval_final[OF eval_body]
    by(fastforce intro:CallRedsFinal[OF wwf IHe IHes])
next
  case Block thus ?case by(auto simp: BlockRedsFinal dest:eval_final)
next
  case Seq thus ?case by(auto simp:SeqReds2)
next
  case SeqThrow thus ?case by(auto dest!:eval_final simp: SeqRedsThrow)
next
  case CondT thus ?case by(auto simp:CondReds2T)
next
  case CondF thus ?case by(auto simp:CondReds2F)
next
  case CondThrow thus ?case by(auto dest!:eval_final simp:CondRedsThrow)
next
  case WhileF thus ?case by(auto simp:WhileFReds)
next
  case WhileT thus ?case by(auto simp: WhileTReds)
next
  case WhileCondThrow thus ?case by(auto dest!:eval_final simp: WhileRedsThrow)
next
  case WhileBodyThrow thus ?case by(auto dest!:eval_final simp: WhileTRedsThrow)
next
  case Throw thus ?case by(auto simp:ThrowReds)
next
  case ThrowNull thus ?case by(auto simp:ThrowRedsNull)
next
  case ThrowThrow thus ?case by(auto dest!:eval_final simp:ThrowRedsThrow)
next
  case Try thus ?case by(simp add:TryRedsVal)
next
  case TryCatch thus ?case by(fast intro!: TryCatchRedsFinal dest!:eval_final)
next
  case TryThrow thus ?case by(fastforce intro!:TryRedsFail)
next
  case Nil thus ?case by simp
next
  case Cons thus ?case
    by(fastforce intro!:Cons_eq_appendI[OF refl refl] ListRedsVal)
next
  case ConsThrow thus ?case by(fastforce elim: ListReds1)
qed
(*>*)


subsection\<open>Big steps simulates small step\<close>

text\<open>This direction was carried out by Norbert Schirmer and Daniel
Wasserrab.\<close>

text \<open>The big step equivalent of \<open>RedWhile\<close>:\<close> 

lemma unfold_while: 
  "P \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>  =  P \<turnstile> \<langle>if(b) (c;;while(b) c) else (unit),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
(*<*)
proof
  assume "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  thus "P \<turnstile> \<langle>if (b) (c;; while (b) c) else unit,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    by cases (fastforce intro: eval_evals.intros)+
next
  assume "P \<turnstile> \<langle>if (b) (c;; while (b) c) else unit,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  thus "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  proof (cases)
    fix a
    assume e': "e' = throw a"
    assume "P \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"  
    hence "P \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>" by (rule WhileCondThrow)
    with e' show ?thesis by simp
  next
    fix s\<^sub>1
    assume eval_false: "P \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle>"
    and eval_unit: "P \<turnstile> \<langle>unit,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    with eval_unit have "s' = s\<^sub>1" "e' = unit" by (auto elim: eval_cases)
    moreover from eval_false have "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>unit,s\<^sub>1\<rangle>"
      by - (rule WhileF, simp)
    ultimately show ?thesis by simp
  next
    fix s\<^sub>1
    assume eval_true: "P \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>"
    and eval_rest: "P \<turnstile> \<langle>c;; while (b) c,s\<^sub>1\<rangle>\<Rightarrow>\<langle>e',s'\<rangle>"
    from eval_rest show ?thesis
    proof (cases)
      fix s\<^sub>2 v\<^sub>1
      assume "P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>" "P \<turnstile> \<langle>while (b) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
      with eval_true show "P \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by (rule WhileT)
    next
      fix a
      assume "P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>" "e' = throw a"
      with eval_true show "P \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"        
        by (iprover intro: WhileBodyThrow)
    qed
  qed
qed
(*>*)


lemma blocksEval:
  "\<And>Ts vs l l'. \<lbrakk>size ps = size Ts; size ps = size vs; P \<turnstile> \<langle>blocks(ps,Ts,vs,e),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<rbrakk>
    \<Longrightarrow> \<exists> l''. P \<turnstile> \<langle>e,(h,l(ps[\<mapsto>]vs))\<rangle> \<Rightarrow> \<langle>e',(h',l'')\<rangle>"
(*<*)
proof (induct ps)
  case Nil then show ?case by fastforce
next
  case (Cons p ps')
  have length_eqs: "length (p # ps') = length Ts" 
                   "length (p # ps') = length vs" by fact+
  then obtain T Ts' where Ts: "Ts = T#Ts'" by (cases "Ts") simp
  obtain v vs' where vs: "vs = v#vs'" using length_eqs by (cases "vs") simp
  have "P \<turnstile> \<langle>blocks (p # ps', Ts, vs, e),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h', l')\<rangle>" by fact
  with Ts vs 
  have "P \<turnstile> \<langle>{p:T := Val v; blocks (ps', Ts', vs', e)},(h,l)\<rangle> \<Rightarrow> \<langle>e',(h', l')\<rangle>"
    by simp
  then obtain l''' where
    eval_ps': "P \<turnstile> \<langle>blocks (ps', Ts', vs', e),(h, l(p\<mapsto>v))\<rangle> \<Rightarrow> \<langle>e',(h', l''')\<rangle>"
    and l''': "l'=l'''(p:=l p)"
    by (auto elim!: eval_cases)
  then obtain l'' where 
    hyp: "P \<turnstile> \<langle>e,(h, l(p\<mapsto>v)(ps'[\<mapsto>]vs'))\<rangle> \<Rightarrow> \<langle>e',(h', l'')\<rangle>"
    using length_eqs Ts vs Cons.hyps [OF _ _ eval_ps'] by auto
  from hyp
  show "\<exists>l''. P \<turnstile> \<langle>e,(h, l(p # ps'[\<mapsto>]vs))\<rangle> \<Rightarrow> \<langle>e',(h', l'')\<rangle>"
    using Ts vs by auto
qed
(*>*)
(* FIXME exercise: show precise relationship between l' and l'':
lemma blocksEval:
  "\<And> Ts vs l l'. \<lbrakk>length ps = length Ts; length ps = length vs; 
        P\<turnstile> \<langle>blocks(ps,Ts,vs,e),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<rbrakk>
    \<Longrightarrow> \<exists> l''. P \<turnstile> \<langle>e,(h,l(ps[\<mapsto>]vs))\<rangle> \<Rightarrow> \<langle>e',(h',l'')\<rangle> \<and> l'=l''(l|set ps)"
proof (induct ps)
  case Nil then show ?case by simp
next
  case (Cons p ps')
  have length_eqs: "length (p # ps') = length Ts" 
                   "length (p # ps') = length vs" .
  then obtain T Ts' where Ts: "Ts=T#Ts'" by (cases "Ts") simp
  obtain v vs' where vs: "vs=v#vs'" using length_eqs by (cases "vs") simp
  have "P \<turnstile> \<langle>blocks (p # ps', Ts, vs, e),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h', l')\<rangle>".
  with Ts vs 
  have "P \<turnstile> \<langle>{p:T := Val v; blocks (ps', Ts', vs', e)},(h,l)\<rangle> \<Rightarrow> \<langle>e',(h', l')\<rangle>"
    by simp
  then obtain l''' where
    eval_ps': "P \<turnstile> \<langle>blocks (ps', Ts', vs', e),(h, l(p\<mapsto>v))\<rangle> \<Rightarrow> \<langle>e',(h', l''')\<rangle>"
    and l''': "l'=l'''(p:=l p)"
    by (cases) (auto elim: eval_cases)
 
  then obtain l'' where 
    hyp: "P \<turnstile> \<langle>e,(h, l(p\<mapsto>v)(ps'[\<mapsto>]vs'))\<rangle> \<Rightarrow> \<langle>e',(h', l'')\<rangle>" and
    l'': "l''' = l''(l(p\<mapsto>v)|set ps')"
    using length_eqs Ts vs Cons.hyps [OF _ _ eval_ps'] by auto
  have "l' = l''(l|set (p # ps'))"
  proof -
    have "(l''(l(p\<mapsto>v)|set ps'))(p := l p) = l''(l|insert p (set ps'))"
      by (induct ps') (auto intro: ext simp add: fun_upd_def override_on_def)
    with l''' l'' show ?thesis  by simp
  qed
  with hyp
  show "\<exists>l''. P \<turnstile> \<langle>e,(h, l(p # ps'[\<mapsto>]vs))\<rangle> \<Rightarrow> \<langle>e',(h', l'')\<rangle> \<and>
        l' = l''(l|set (p # ps'))"
    using Ts vs by auto
qed
*)

lemma
assumes wf: "wwf_J_prog P"
shows eval_restrict_lcl:
  "P \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>W. fv e \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e,(h,l|`W)\<rangle> \<Rightarrow> \<langle>e',(h',l'|`W)\<rangle>)"
and "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>W. fvs es \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>es,(h,l|`W)\<rangle> [\<Rightarrow>] \<langle>es',(h',l'|`W)\<rangle>)"
(*<*)
proof(induct rule:eval_evals_inducts)
  case (Block e\<^sub>0 h\<^sub>0 l\<^sub>0 V e\<^sub>1 h\<^sub>1 l\<^sub>1 T)
  have IH: "\<And>W. fv e\<^sub>0 \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0(V:=None)|`W)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1|`W)\<rangle>" by fact
  have "fv({V:T; e\<^sub>0}) \<subseteq> W" by fact+
  hence "fv e\<^sub>0 - {V} \<subseteq> W" by simp_all
  hence "fv e\<^sub>0 \<subseteq> insert V W" by fast
  from IH[OF this]
  have "P \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0, (l\<^sub>0|`W)(V := None))\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1, l\<^sub>1|`insert V W)\<rangle>"
    by fastforce
  from eval_evals.Block[OF this] show ?case by fastforce
next
  case Seq thus ?case by simp (blast intro:eval_evals.Seq)
next
  case New thus ?case by(simp add:eval_evals.intros)
next
  case NewFail thus ?case by(simp add:eval_evals.intros)
next
  case Cast thus ?case by simp (blast intro:eval_evals.Cast)
next
  case CastNull thus ?case by simp (blast intro:eval_evals.CastNull)
next
  case CastFail thus ?case by simp (blast intro:eval_evals.CastFail)
next
  case CastThrow thus ?case by(simp add:eval_evals.intros)
next
  case Val thus ?case by(simp add:eval_evals.intros)
next
  case BinOp thus ?case by simp (blast intro:eval_evals.BinOp)
next
  case BinOpThrow1 thus ?case by simp (blast intro:eval_evals.BinOpThrow1)
next
  case BinOpThrow2 thus ?case by simp (blast intro:eval_evals.BinOpThrow2)
next
  case Var thus ?case by(simp add:eval_evals.intros)
next
  case (LAss e h\<^sub>0 l\<^sub>0 v h l l' V)
  have IH: "\<And>W. fv e \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0|`W)\<rangle> \<Rightarrow> \<langle>Val v,(h,l|`W)\<rangle>"
   and [simp]: "l' = l(V \<mapsto> v)" by fact+
  have "fv (V:=e) \<subseteq> W" by fact
  hence fv: "fv e \<subseteq> W" and VinW: "V \<in> W" by auto
  from eval_evals.LAss[OF IH[OF fv] refl, of V] VinW
  show ?case by simp
next
  case LAssThrow thus ?case by(fastforce intro: eval_evals.LAssThrow)
next
  case FAcc thus ?case by simp (blast intro: eval_evals.FAcc)
next
  case FAccNull thus ?case by(fastforce intro: eval_evals.FAccNull)
next
  case FAccThrow thus ?case by(fastforce intro: eval_evals.FAccThrow)
next
  case FAss thus ?case by simp (blast intro: eval_evals.FAss)
next
  case FAssNull thus ?case by simp (blast intro: eval_evals.FAssNull)
next
  case FAssThrow1 thus ?case by simp (blast intro: eval_evals.FAssThrow1)
next
  case FAssThrow2 thus ?case by simp (blast intro: eval_evals.FAssThrow2)
next
  case CallObjThrow thus ?case by simp (blast intro: eval_evals.intros)
next
  case CallNull thus ?case by simp (blast intro: eval_evals.CallNull)
next
  case CallParamsThrow thus ?case
    by simp (blast intro: eval_evals.CallParamsThrow)
next
  case (Call e h\<^sub>0 l\<^sub>0 a h\<^sub>1 l\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 C fs M Ts T pns body
      D l\<^sub>2' e' h\<^sub>3 l\<^sub>3)
  have IHe: "\<And>W. fv e \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0|`W)\<rangle> \<Rightarrow> \<langle>addr a,(h\<^sub>1,l\<^sub>1|`W)\<rangle>"
   and IHps: "\<And>W. fvs ps \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>ps,(h\<^sub>1,l\<^sub>1|`W)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2|`W)\<rangle>"
   and IHbd: "\<And>W. fv body \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2'|`W)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3|`W)\<rangle>"
   and h\<^sub>2a: "h\<^sub>2 a = Some (C, fs)"
   and "method": "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D"
   and same_len: "size vs = size pns"
   and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Addr a, pns [\<mapsto>] vs]" by fact+
  have "fv (e\<bullet>M(ps)) \<subseteq> W" by fact
  hence fve: "fv e  \<subseteq> W" and fvps: "fvs(ps) \<subseteq> W" by auto
  have wfmethod: "size Ts = size pns \<and> this \<notin> set pns" and
       fvbd: "fv body \<subseteq> {this} \<union> set pns"
    using "method" wf by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  show ?case
    using IHbd[OF fvbd] l\<^sub>2' same_len wfmethod h\<^sub>2a
      eval_evals.Call[OF IHe[OF fve] IHps[OF fvps] _ "method" same_len l\<^sub>2']
    by (simp add:subset_insertI)
next
  case SeqThrow thus ?case by simp (blast intro: eval_evals.SeqThrow)
next
  case CondT thus ?case by simp (blast intro: eval_evals.CondT)
next
  case CondF thus ?case by simp (blast intro: eval_evals.CondF)
next
  case CondThrow thus ?case by simp (blast intro: eval_evals.CondThrow)
next
  case WhileF thus ?case by simp (blast intro: eval_evals.WhileF)
next
  case WhileT thus ?case by simp (blast intro: eval_evals.WhileT)
next
  case WhileCondThrow thus ?case by simp (blast intro: eval_evals.WhileCondThrow)
next
  case WhileBodyThrow thus ?case by simp (blast intro: eval_evals.WhileBodyThrow)
next
  case Throw thus ?case by simp (blast intro: eval_evals.Throw)
next
  case ThrowNull thus ?case by simp (blast intro: eval_evals.ThrowNull)
next
  case ThrowThrow thus ?case by simp (blast intro: eval_evals.ThrowThrow)
next
  case Try thus ?case by simp (blast intro: eval_evals.Try)
next
  case (TryCatch e\<^sub>1 h\<^sub>0 l\<^sub>0 a h\<^sub>1 l\<^sub>1 D fs C e\<^sub>2 V e\<^sub>2' h\<^sub>2 l\<^sub>2)
  have IH\<^sub>1: "\<And>W. fv e\<^sub>1 \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1,(h\<^sub>0,l\<^sub>0|`W)\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,l\<^sub>1|`W)\<rangle>"
   and IH\<^sub>2: "\<And>W. fv e\<^sub>2 \<subseteq> W \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>2,(h\<^sub>1,l\<^sub>1(V\<mapsto>Addr a)|`W)\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,l\<^sub>2|`W)\<rangle>"
   and lookup: "h\<^sub>1 a = Some(D, fs)" and subtype: "P \<turnstile> D \<preceq>\<^sup>* C" by fact+
  have "fv (try e\<^sub>1 catch(C V) e\<^sub>2) \<subseteq> W" by fact
  hence fv\<^sub>1: "fv e\<^sub>1 \<subseteq> W" and fv\<^sub>2: "fv e\<^sub>2 \<subseteq> insert V W" by auto
  have IH\<^sub>2': "P \<turnstile> \<langle>e\<^sub>2,(h\<^sub>1,(l\<^sub>1|`W)(V \<mapsto> Addr a))\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,l\<^sub>2|`insert V W)\<rangle>"
    using IH\<^sub>2[OF fv\<^sub>2] fun_upd_restrict[of l\<^sub>1 W] (*FIXME just l|W instead of l|(W-V) in simp rule??*) by simp
  with eval_evals.TryCatch[OF IH\<^sub>1[OF fv\<^sub>1] _ subtype IH\<^sub>2'] lookup
  show ?case by fastforce
next
  case TryThrow thus ?case by simp (blast intro: eval_evals.TryThrow)
next
  case Nil thus ?case by (simp add: eval_evals.Nil)
next
  case Cons thus ?case by simp (blast intro: eval_evals.Cons)
next
  case ConsThrow thus ?case by simp (blast intro: eval_evals.ConsThrow)
qed
(*>*)


lemma eval_notfree_unchanged:
  "P \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>V. V \<notin> fv e \<Longrightarrow> l' V = l V)"
and "P \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>V. V \<notin> fvs es \<Longrightarrow> l' V = l V)"
(*<*)
proof(induct rule:eval_evals_inducts)
  case LAss thus ?case by(simp add:fun_upd_apply)
next
  case Block thus ?case
    by (simp only:fun_upd_apply split:if_splits) fastforce
next
  case TryCatch thus ?case
    by (simp only:fun_upd_apply split:if_splits) fastforce
qed simp_all
(*>*)


lemma eval_closed_lcl_unchanged:
  "\<lbrakk> P \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>; fv e = {} \<rbrakk> \<Longrightarrow> l' = l"
(*<*)by(fastforce dest:eval_notfree_unchanged simp add:fun_eq_iff [where 'b="val option"])(*>*)


lemma list_eval_Throw: 
assumes eval_e: "P \<turnstile> \<langle>throw x,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "P \<turnstile> \<langle>map Val vs @ throw x # es',s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"
(*<*)
proof -
  from eval_e 
  obtain a where e': "e' = Throw a"
    by (cases) (auto dest!: eval_final)
  {
    fix es
    have "\<And>vs. es = map Val vs @ throw x # es' 
           \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle>[\<Rightarrow>]\<langle>map Val vs @ e' # es',s'\<rangle>"
    proof (induct es type: list)
      case Nil thus ?case by simp
    next
      case (Cons e es vs)
      have e_es: "e # es = map Val vs @ throw x # es'" by fact
      show "P \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"
      proof (cases vs)
        case Nil
        with e_es obtain "e=throw x" "es=es'" by simp
        moreover from eval_e e'
        have "P \<turnstile> \<langle>throw x # es,s\<rangle> [\<Rightarrow>] \<langle>Throw a # es,s'\<rangle>"
          by (iprover intro: ConsThrow)
        ultimately show ?thesis using Nil e' by simp
      next
        case (Cons v vs')
        have vs: "vs = v # vs'" by fact
        with e_es obtain 
          e: "e=Val v" and es:"es= map Val vs' @ throw x # es'"
          by simp
        from e 
        have "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"
          by (iprover intro: eval_evals.Val)
        moreover from es 
        have "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs' @ e' # es',s'\<rangle>"
          by (rule Cons.hyps)
        ultimately show 
          "P \<turnstile> \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"
          using vs by (auto intro: eval_evals.Cons)
      qed
    qed
  }
  thus ?thesis
    by simp
qed
(*>*)
(* Hiermit kann man die ganze pair-Splitterei in den automatischen Taktiken
abschalten. Wieder anschalten siehe nach dem Beweis. *)
(*<*)
declare split_paired_All [simp del] split_paired_Ex [simp del]
(*>*)
(* FIXME
 exercise 1: define a big step semantics where the body of a procedure can
 access not juts this and pns but all of the enclosing l. What exactly is fed
 in? What exactly is returned at the end? Notion: "dynamic binding"

  excercise 2: the semantics of exercise 1 is closer to the small step
  semantics. Reformulate equivalence proof by modifying call lemmas.
*)
text \<open>The key lemma:\<close>

lemma
assumes wf: "wwf_J_prog P"
shows extend_1_eval:
  "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e'',s''\<rangle> \<Longrightarrow>  (\<And>s' e'. P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>)"
and extend_1_evals:
  "P \<turnstile> \<langle>es,t\<rangle> [\<rightarrow>] \<langle>es'',t''\<rangle> \<Longrightarrow> (\<And>t' es'. P \<turnstile> \<langle>es'',t''\<rangle> [\<Rightarrow>] \<langle>es',t'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>es,t\<rangle> [\<Rightarrow>] \<langle>es',t'\<rangle>)"
(*<*)
proof (induct rule: red_reds.inducts)
  case (RedCall s a C fs M Ts T pns body D vs s' e')
  have "P \<turnstile> \<langle>addr a,s\<rangle> \<Rightarrow> \<langle>addr a,s\<rangle>" by (rule eval_evals.intros)
  moreover
  have finals: "finals(map Val vs)" by simp
  obtain h\<^sub>2 l\<^sub>2 where s: "s = (h\<^sub>2,l\<^sub>2)" by (cases s)
  with finals have "P \<turnstile> \<langle>map Val vs,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
    by (iprover intro: eval_finalsId)
  moreover from s have "h\<^sub>2 a = Some (C, fs)" using RedCall by simp
  moreover have "method": "P \<turnstile> C sees M: Ts\<rightarrow>T = (pns, body) in D" by fact
  moreover have same_len\<^sub>1: "length Ts = length pns"
   and this_distinct: "this \<notin> set pns" and fv: "fv body \<subseteq> {this} \<union> set pns"
    using "method" wf by (fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)+
  have same_len: "length vs = length pns" by fact
  moreover
  obtain l\<^sub>2' where l\<^sub>2': "l\<^sub>2' = [this\<mapsto>Addr a,pns[\<mapsto>]vs]" by simp
  moreover
  obtain h\<^sub>3 l\<^sub>3 where s': "s' = (h\<^sub>3,l\<^sub>3)" by (cases s')
  have eval_blocks:
    "P \<turnstile> \<langle>blocks (this # pns, Class D # Ts, Addr a # vs, body),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  hence id: "l\<^sub>3 = l\<^sub>2" using fv s s' same_len\<^sub>1 same_len
    by(fastforce elim: eval_closed_lcl_unchanged)
  from eval_blocks obtain l\<^sub>3' where "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3')\<rangle>"
  proof -
    from same_len\<^sub>1 have "length(this#pns) = length(Class D#Ts)" by simp
    moreover from same_len\<^sub>1 same_len
    have "length (this#pns) = length (Addr a#vs)" by simp
    moreover from eval_blocks
    have "P \<turnstile> \<langle>blocks (this#pns,Class D#Ts,Addr a#vs,body),(h\<^sub>2,l\<^sub>2)\<rangle>
              \<Rightarrow>\<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle>" using s s' by simp
    ultimately obtain l''
      where "P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2(this # pns[\<mapsto>]Addr a # vs))\<rangle>\<Rightarrow>\<langle>e',(h\<^sub>3, l'')\<rangle>"
      by (blast dest:blocksEval)
    from eval_restrict_lcl[OF wf this fv] this_distinct same_len\<^sub>1 same_len
    have "P \<turnstile> \<langle>body,(h\<^sub>2,[this # pns[\<mapsto>]Addr a # vs])\<rangle> \<Rightarrow>
               \<langle>e',(h\<^sub>3, l''|`(set(this#pns)))\<rangle>"
      by(simp add:subset_insert_iff insert_Diff_if)
    thus ?thesis by(fastforce intro!:that simp add: l\<^sub>2')
  qed
  ultimately
  have "P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs),s\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>" by (rule Call)
  with s' id show ?case by simp
next
 case RedNew
  thus ?case
     by (iprover elim: eval_cases intro: eval_evals.intros)
next
  case RedNewFail
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (CastRed e s e'' s'' C s' e')
  thus ?case
    by(cases s, cases s') (erule eval_cases, auto intro: eval_evals.intros)
next
  case RedCastNull
  thus ?case
    by (iprover elim: eval_cases intro: eval_evals.intros)
next
  case (RedCast s a D fs C s'' e'')
  thus ?case
    by (cases s) (auto elim: eval_cases intro: eval_evals.intros)
next
  case (RedCastFail s a D fs C s'' e'')
  thus ?case
    by (cases s) (auto elim!: eval_cases intro: eval_evals.intros)
next
  case (BinOpRed1 e s e' s' bop e\<^sub>2 s'' e')
  thus ?case
    by (cases s'')(erule eval_cases,auto intro: eval_evals.intros)
next
  case BinOpRed2
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros eval_finalId)
next
  case RedBinOp
  thus ?case
    by (iprover elim: eval_cases intro: eval_evals.intros)
next
  case (RedVar s V v s' e')
  thus ?case
    by (cases s)(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (LAssRed e s e' s' V s'')
  thus ?case
    by (cases s'')(erule eval_cases,auto intro: eval_evals.intros)
next
  case RedLAss
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (FAccRed e s e' s' F D s'')
  thus ?case
    by (cases s'')(erule eval_cases,auto intro: eval_evals.intros)
next
  case (RedFAcc s a C fs F D v s' e')
  thus ?case
    by (cases s)(fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedFAccNull
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros)
next
  case (FAssRed1 e s e' s'' F D e\<^sub>2 s' e')
  thus ?case
    by (cases s')(erule eval_cases, auto intro: eval_evals.intros)
next
  case (FAssRed2 e s e' s'' v F D s' e')
  thus ?case
    by (cases s)
       (fastforce elim!: eval_cases intro: eval_evals.intros eval_finalId)
next
  case RedFAss
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros)
next
  case RedFAssNull
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros)
next
  case CallObj
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros)
next
  case CallParams
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros eval_finalId)
next
  case RedCallNull
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros eval_finalsId)
next
  case InitBlockRed
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros eval_finalId
                 simp add: map_upd_triv fun_upd_same)
next
  case (RedInitBlock V T v u s s' e')
  have "P \<turnstile> \<langle>Val u,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  then obtain s': "s'=s" and e': "e'=Val u" by cases simp
  obtain h l where s: "s=(h,l)" by (cases s)
  have "P \<turnstile> \<langle>{V:T :=Val v; Val u},(h,l)\<rangle> \<Rightarrow> \<langle>Val u,(h, (l(V\<mapsto>v))(V:=l V))\<rangle>"
    by (fastforce intro!: eval_evals.intros)
  thus "P \<turnstile> \<langle>{V:T := Val v; Val u},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using s s' e' by simp
next
  case BlockRedNone
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros 
                 simp add: fun_upd_same fun_upd_idem)
next
  case BlockRedSome
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros 
                 simp add:  fun_upd_same fun_upd_idem)
next
 case (RedBlock V T v s s' e') 
 have "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
 then obtain s': "s'=s" and e': "e'=Val v" 
    by cases simp
  obtain h l where s: "s=(h,l)" by (cases s)
 have "P \<turnstile> \<langle>Val v,(h,l(V:=None))\<rangle> \<Rightarrow> \<langle>Val v,(h,l(V:=None))\<rangle>" 
   by (rule eval_evals.intros)
 hence "P \<turnstile> \<langle>{V:T;Val v},(h,l)\<rangle> \<Rightarrow> \<langle>Val v,(h,(l(V:=None))(V:=l V))\<rangle>"
   by (rule eval_evals.Block)
 thus "P \<turnstile> \<langle>{V:T; Val v},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using s s' e'
    by simp
next
  case SeqRed
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedSeq
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case CondRed
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedCondT
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedCondF
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedWhile
  thus ?case
    by (auto simp add: unfold_while intro:eval_evals.intros elim:eval_cases)
next
  case ThrowRed
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedThrowNull
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (TryRed e s e' s' C V e\<^sub>2 s'' e')
  thus ?case
    by (cases s, cases s'', auto elim!: eval_cases intro: eval_evals.intros)
next
  case RedTry
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedTryCatch
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (RedTryFail s a D fs C V e\<^sub>2 s' e')
  thus ?case
    by (cases s)(auto elim!: eval_cases intro: eval_evals.intros)
next
  case ListRed1
  thus ?case
    by (fastforce elim: evals_cases intro: eval_evals.intros)
next
  case ListRed2
  thus ?case
    by (fastforce elim!: evals_cases eval_cases 
                 intro: eval_evals.intros eval_finalId)
next
  case CastThrow
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case BinOpThrow1
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case BinOpThrow2
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case LAssThrow
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case FAccThrow
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case FAssThrow1
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case FAssThrow2
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case CallThrowObj
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (CallThrowParams es vs e es' v M s s' e')
  have "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by (rule eval_evals.intros)
  moreover
  have es: "es = map Val vs @ throw e # es'" by fact
  have eval_e: "P \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  then obtain xa where e': "e' = Throw xa" by (cases) (auto dest!: eval_final)
  with list_eval_Throw [OF eval_e] es
  have "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ Throw xa # es',s'\<rangle>" by simp
  ultimately have "P \<turnstile> \<langle>Val v\<bullet>M(es),s\<rangle> \<Rightarrow> \<langle>Throw xa,s'\<rangle>"
    by (rule eval_evals.CallParamsThrow)
  thus ?case using e' by simp
next
  case (InitBlockThrow V T v a s s' e')
  have "P \<turnstile> \<langle>Throw a,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  then obtain s': "s' = s" and e': "e' = Throw a"
    by cases (auto elim!:eval_cases)
  obtain h l where s: "s = (h,l)" by (cases s)
  have "P \<turnstile> \<langle>{V:T :=Val v; Throw a},(h,l)\<rangle> \<Rightarrow> \<langle>Throw a, (h, (l(V\<mapsto>v))(V:=l V))\<rangle>"
    by(fastforce intro:eval_evals.intros)
  thus "P \<turnstile> \<langle>{V:T := Val v; Throw a},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using s s' e' by simp
next
  case (BlockThrow V T a s s' e')
  have "P \<turnstile> \<langle>Throw a, s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  then obtain s': "s' = s" and e': "e' = Throw a"
    by cases (auto elim!:eval_cases)
  obtain h l where s: "s=(h,l)" by (cases s)
  have "P \<turnstile> \<langle>Throw a, (h,l(V:=None))\<rangle> \<Rightarrow> \<langle>Throw a, (h,l(V:=None))\<rangle>"
    by (simp add:eval_evals.intros eval_finalId)
  hence "P\<turnstile>\<langle>{V:T;Throw a},(h,l)\<rangle>\<Rightarrow>\<langle>Throw a, (h,(l(V:=None))(V:=l V))\<rangle>"
    by (rule eval_evals.Block)
  thus "P \<turnstile> \<langle>{V:T; Throw a},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using s s' e' by simp
next
  case SeqThrow
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case CondThrow
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case ThrowThrow
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
qed
(*>*)
(*<*)
(* ... und wieder anschalten: *)
declare split_paired_All [simp] split_paired_Ex [simp]
(*>*)

text \<open>Its extension to \<open>\<rightarrow>*\<close>:\<close> 

lemma extend_eval:
assumes wf: "wwf_J_prog P"
and reds: "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e'',s''\<rangle>" and eval_rest:  "P \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
(*<*)
using reds eval_rest 
apply (induct rule: converse_rtrancl_induct2)
apply simp
apply simp
apply (rule extend_1_eval)
apply (rule wf)
apply assumption
apply assumption
done
(*>*)


lemma extend_evals:
assumes wf: "wwf_J_prog P"
and reds: "P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es'',s''\<rangle>" and eval_rest:  "P \<turnstile> \<langle>es'',s''\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
shows "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
(*<*)
using reds eval_rest 
apply (induct rule: converse_rtrancl_induct2)
apply simp
apply simp
apply (rule extend_1_evals)
apply (rule wf)
apply assumption
apply assumption
done
(*>*)

text \<open>Finally, small step semantics can be simulated by big step semantics:
\<close>

theorem
assumes wf: "wwf_J_prog P"
shows small_by_big: "\<lbrakk>P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>; final e'\<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
and "\<lbrakk>P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>; finals es'\<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
(*<*)
proof -
  note wf 
  moreover assume "P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
  moreover assume "final e'"
  then have "P \<turnstile> \<langle>e',s'\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    by (rule eval_finalId)
  ultimately show "P \<turnstile> \<langle>e,s\<rangle>\<Rightarrow>\<langle>e',s'\<rangle>"
    by (rule extend_eval)
next
  note wf 
  moreover assume "P \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"
  moreover assume "finals es'"
  then have "P \<turnstile> \<langle>es',s'\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
    by (rule eval_finalsId)
  ultimately show "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
    by (rule extend_evals)
qed
(*>*)

subsection "Equivalence"

text\<open>And now, the crowning achievement:\<close>

corollary big_iff_small:
  "wwf_J_prog P \<Longrightarrow>
  P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>  =  (P \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<and> final e')"
(*<*)by(blast dest: big_by_small eval_final small_by_big)(*>*)


end
