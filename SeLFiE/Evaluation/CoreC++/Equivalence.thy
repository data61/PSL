(*  Title:       CoreC++

    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory J/Equivalence.thy by Tobias Nipkow
*)

section \<open>Equivalence of Big Step and Small Step Semantics\<close>

theory Equivalence imports BigStep SmallStep WWellForm begin


subsection\<open>Some casts-lemmas\<close>

lemma assumes wf:"wf_prog wf_md P"
shows casts_casts:
"P \<turnstile> T casts v to v' \<Longrightarrow> P \<turnstile> T casts v' to v'"

proof(induct rule:casts_to.induct)
  case casts_prim thus ?case by(rule casts_to.casts_prim)
next
  case (casts_null C) thus ?case by(rule casts_to.casts_null)
next
  case (casts_ref Cs C Cs' Ds a)
  have path_via:"P \<turnstile> Path last Cs to C via Cs'" and Ds:"Ds = Cs @\<^sub>p Cs'" by fact+
  with wf have "last Cs' = C" and "Cs' \<noteq> []" and "class": "is_class P C"
    by(auto intro!:Subobjs_nonempty Subobj_last_isClass simp:path_via_def)
  with Ds have last:"last Ds = C"
    by -(drule_tac Cs' = "Cs" in appendPath_last,simp)
  hence Ds':"Ds = Ds @\<^sub>p [C]" by(simp add:appendPath_def)
  from last "class" have "P \<turnstile> Path last Ds to C via [C]"
    by(fastforce intro:Subobjs_Base simp:path_via_def)
  with Ds' show ?case by(fastforce intro:casts_to.casts_ref)
qed



lemma casts_casts_eq:
"\<lbrakk> P \<turnstile> T casts v to v; P \<turnstile> T casts v to v'; wf_prog wf_md P \<rbrakk> \<Longrightarrow> v = v'"

  apply -
  apply(erule casts_to.cases)
    apply clarsimp
    apply(erule casts_to.cases)
      apply simp
     apply simp
    apply (simp (asm_lr))
   apply(erule casts_to.cases)
     apply simp
    apply simp
   apply simp
  apply simp
  apply(erule casts_to.cases)
    apply simp
   apply simp
  apply clarsimp
  apply(erule appendPath_path_via)
  by auto



lemma assumes wf:"wf_prog wf_md P"
shows None_lcl_casts_values:
"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow>
  (\<And>V. \<lbrakk>l V = None; E V = Some T; l' V = Some v'\<rbrakk>
  \<Longrightarrow> P \<turnstile> T casts v' to v')"
and "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow>
  (\<And>V. \<lbrakk>l V = None; E V = Some T; l' V = Some v'\<rbrakk>
  \<Longrightarrow> P \<turnstile> T casts v' to v')"

proof(induct rule:red_reds_inducts)
  case (RedLAss E V T' w w' h l V')
  have env:"E V = Some T'" and env':"E V' = Some T"
    and l:"l V' = None" and lupd:"(l(V \<mapsto> w')) V' = Some v'"
    and casts:"P \<turnstile> T' casts w to w'" by fact+
  show ?case
  proof(cases "V = V'")
    case True
    with lupd have v':"v' = w'" by simp
    from True env env' have "T = T'" by simp
    with v' casts wf show ?thesis by(fastforce intro:casts_casts)
  next
    case False
    with lupd have "l V' = Some v'" by(fastforce split:if_split_asm)
    with l show ?thesis by simp
  qed
next
  case (BlockRedNone E V T' e h l e' h' l' V')
  have l:"l V' = None"
    and l'upd:"(l'(V := l V)) V' = Some v'" and env:"E V' = Some T"
    and IH:"\<And>V'. \<lbrakk>(l(V := None)) V' = None; (E(V \<mapsto> T')) V' = Some T; 
                   l' V' = Some v'\<rbrakk>
            \<Longrightarrow> P \<turnstile> T casts v' to v'" by fact+
  show ?case
  proof(cases "V = V'")
    case True 
    with l'upd l show ?thesis by fastforce
  next
    case False
    with l  l'upd have lnew:"(l(V := None)) V' = None"
      and l'new:"l' V' = Some v'" by (auto split:if_split_asm)
    from env False have env':"(E(V \<mapsto> T')) V' = Some T" by fastforce
    from IH[OF lnew env' l'new] show ?thesis .
  qed
next
  case (BlockRedSome E V T' e h l e' h' l' v V')
  have l:"l V' = None"
    and l'upd:"(l'(V := l V)) V' = Some v'" and env:"E V' = Some T"
    and IH:"\<And>V'. \<lbrakk>(l(V := None)) V' = None; (E(V \<mapsto> T')) V' = Some T; 
                   l' V' = Some v'\<rbrakk>
            \<Longrightarrow> P \<turnstile> T casts v' to v'" by fact+
  show ?case
  proof(cases "V = V'")
    case True
    with l l'upd show ?thesis by fastforce
  next
    case False
    with l  l'upd have lnew:"(l(V := None)) V' = None"
      and l'new:"l' V' = Some v'" by (auto split:if_split_asm)
    from env False have env':"(E(V \<mapsto> T')) V' = Some T" by fastforce
    from IH[OF lnew env' l'new] show ?thesis .
  qed
next
  case (InitBlockRed E V T' e h l w' e' h' l' w'' w V')
  have l:"l V' = None"
    and l'upd:"(l'(V := l V)) V' = Some v'" and env:"E V' = Some T"
    and IH:"\<And>V'. \<lbrakk>(l(V \<mapsto> w')) V' = None; (E(V \<mapsto> T')) V' = Some T; 
                   l' V' = Some v'\<rbrakk>
            \<Longrightarrow> P \<turnstile> T casts v' to v'" by fact+
  show ?case
  proof(cases "V = V'")
    case True
    with l l'upd show ?thesis by fastforce
  next
    case False
    with l  l'upd have lnew:"(l(V \<mapsto> w')) V' = None"
      and l'new:"l' V' = Some v'" by (auto split:if_split_asm)
    from env False have env':"(E(V \<mapsto> T')) V' = Some T" by fastforce
    from IH[OF lnew env' l'new] show ?thesis .
  qed
qed (auto intro:casts_casts wf)



lemma assumes wf:"wf_prog wf_md P"
shows Some_lcl_casts_values:
"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow>
  (\<And>V. \<lbrakk>l V = Some v; E V = Some T;
      P \<turnstile> T casts v'' to v; l' V = Some v'\<rbrakk>
  \<Longrightarrow> P \<turnstile> T casts v' to v')"
and "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow>
  (\<And>V. \<lbrakk>l V = Some v; E V = Some T;
      P \<turnstile> T casts v'' to v; l' V = Some v'\<rbrakk>
  \<Longrightarrow> P \<turnstile> T casts v' to v')"

proof(induct rule:red_reds_inducts)
  case (RedNew h a h' C' E l V)
  have l1:"l V = Some v" and l2:"l V = Some v'"
    and casts:"P \<turnstile> T casts v'' to v " by fact+
  from l1 l2 have eq:"v = v'" by simp
  with casts wf show ?case by(fastforce intro:casts_casts)
next
  case (RedLAss E V T' w w' h l V')
  have l:"l V' = Some v" and lupd:"(l(V \<mapsto> w')) V' = Some v'"
    and T'casts:"P \<turnstile> T' casts w to w'"
    and env:"E V = Some T'" and env':"E V' = Some T"
    and casts:"P \<turnstile> T casts v'' to v" by fact+
  show ?case
  proof (cases "V = V'")
    case True
    with lupd have v':"v' = w'" by simp
    from True env env' have "T = T'" by simp
    with T'casts v' wf show ?thesis by(fastforce intro:casts_casts)
  next
    case False
    with l lupd have "v = v'" by (auto split:if_split_asm)
    with casts wf show ?thesis by(fastforce intro:casts_casts)
  qed
next
  case (RedFAss h a D S Cs' F T' Cs w w' Ds fs E l V)
  have l1:"l V = Some v" and l2:"l V = Some v'"
    and hp:"h a = Some(D, S)"
    and T'casts:"P \<turnstile> T' casts w to w'"
    and casts:"P \<turnstile> T casts v'' to v" by fact+
  from l1 l2 have eq:"v = v'" by simp
  with casts wf show ?case by(fastforce intro:casts_casts)
next
  case (BlockRedNone E V T' e h l e' h' l' V')
  have l':"l' V = None" and l:"l V' = Some v"
    and l'upd:"(l'(V := l V)) V' = Some v'" and env:"E V' = Some T"
    and casts:"P \<turnstile> T casts v'' to v"
    and IH:"\<And>V'. \<lbrakk>(l(V := None)) V' = Some v; (E(V \<mapsto> T')) V' = Some T; 
                  P \<turnstile> T casts v'' to v ; l' V' = Some v'\<rbrakk>
            \<Longrightarrow> P \<turnstile> T casts v' to v'" by fact+
  show ?case
  proof(cases "V = V'")
    case True
    with l' l'upd have "l V = Some v'" by auto
    with True l have eq:"v = v'" by simp
    with casts wf show ?thesis by(fastforce intro:casts_casts)
  next
    case False
    with l  l'upd have lnew:"(l(V := None)) V' = Some v"
      and l'new:"l' V' = Some v'" by (auto split:if_split_asm)
    from env False have env':"(E(V \<mapsto> T')) V' = Some T" by fastforce
    from IH[OF lnew env' casts l'new] show ?thesis .
  qed
next
  case (BlockRedSome E V T' e h l e' h' l' w V')
  have l':"l' V = Some w" and l:"l V' = Some v"
    and l'upd:"(l'(V := l V)) V' = Some v'" and env:"E V' = Some T"
    and casts:"P \<turnstile> T casts v'' to v"
    and IH:"\<And>V'. \<lbrakk>(l(V := None)) V' = Some v; (E(V \<mapsto> T')) V' = Some T; 
                   P \<turnstile> T casts v'' to v ; l' V' = Some v'\<rbrakk>
            \<Longrightarrow> P \<turnstile> T casts v' to v'" by fact+
  show ?case
  proof(cases "V = V'")
    case True
    with l' l'upd have "l V = Some v'" by auto
    with True l have eq:"v = v'" by simp
    with casts wf show ?thesis by(fastforce intro:casts_casts)
  next
    case False
    with l  l'upd have lnew:"(l(V := None)) V' = Some v"
      and l'new:"l' V' = Some v'" by (auto split:if_split_asm)
    from env False have env':"(E(V \<mapsto> T')) V' = Some T" by fastforce
    from IH[OF lnew env' casts l'new] show ?thesis .
  qed
next
  case (InitBlockRed E V T' e h l w' e' h' l' w'' w V')
  have l:"l V' = Some v" and l':"l' V = Some w''"
    and l'upd:"(l'(V := l V)) V' = Some v'" and env:"E V' = Some T"
    and casts:"P \<turnstile> T casts v'' to v"
    and IH:"\<And>V'. \<lbrakk>(l(V \<mapsto> w')) V' = Some v; (E(V \<mapsto> T')) V' = Some T; 
                   P \<turnstile> T casts v'' to v ; l' V' = Some v'\<rbrakk>
            \<Longrightarrow> P \<turnstile> T casts v' to v'" by fact+
  show ?case
  proof(cases "V = V'")
    case True
    with l' l'upd have "l V = Some v'" by auto
    with True l have eq:"v = v'" by simp
    with casts wf show ?thesis by(fastforce intro:casts_casts)
  next
    case False
    with l  l'upd have lnew:"(l(V \<mapsto> w')) V' = Some v"
      and l'new:"l' V' = Some v'" by (auto split:if_split_asm)
    from env False have env':"(E(V \<mapsto> T')) V' = Some T" by fastforce
    from IH[OF lnew env' casts l'new] show ?thesis .
  qed
qed (auto intro:casts_casts wf)

  


subsection\<open>Small steps simulate big step\<close>

subsection \<open>Cast\<close>

lemma StaticCastReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>\<lparr>C\<rparr>e',s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply (simp add:StaticCastRed)
done


lemma StaticCastRedsNull:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule StaticCastReds)
apply(simp add:RedStaticCastNull)
done


lemma StaticUpCastReds:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s'\<rangle>; P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Ds),s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule StaticCastReds)
apply(fastforce intro:RedStaticUpCast)
done


lemma StaticDownCastReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs@[C]@Cs'),s'\<rangle>
  \<Longrightarrow>  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs@[C]),s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule StaticCastReds)
apply simp
apply(subgoal_tac "P,E \<turnstile> \<langle>\<lparr>C\<rparr>ref(a,Cs@[C]@Cs'),s'\<rangle> \<rightarrow> \<langle>ref(a,Cs@[C]),s'\<rangle>")
 apply simp
apply(rule RedStaticDownCast)
done


lemma StaticCastRedsFail:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s'\<rangle>; C \<notin> set Cs; \<not> P \<turnstile> (last Cs) \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>THROW ClassCast,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule StaticCastReds)
apply(fastforce intro:RedStaticCastFail)
done


lemma StaticCastRedsThrow:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule StaticCastReds)
apply(simp add:red_reds.StaticCastThrow)
done


lemma DynCastReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>Cast C e',s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply (simp add:DynCastRed)
done


lemma DynCastRedsNull:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule DynCastReds)
apply(simp add:RedDynCastNull)
done


lemma DynCastRedsRef:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s'\<rangle>; hp s' a = Some (D,S); P \<turnstile> Path D to C via Cs';
     P \<turnstile> Path D to C unique \<rbrakk> 
 \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs'),s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule DynCastReds)
apply(fastforce intro:RedDynCast)
done


lemma StaticUpDynCastReds:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s'\<rangle>; P \<turnstile> Path last Cs to C unique;
  P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>ref(a,Ds),s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule DynCastReds)
apply(fastforce intro:RedStaticUpDynCast)
done


lemma StaticDownDynCastReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs@[C]@Cs'),s'\<rangle>
  \<Longrightarrow>  P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs@[C]),s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule DynCastReds)
apply simp
apply(subgoal_tac "P,E \<turnstile> \<langle>Cast C (ref(a,Cs@[C]@Cs')),s'\<rangle> \<rightarrow> \<langle>ref(a,Cs@[C]),s'\<rangle>")
 apply simp
apply(rule RedStaticDownDynCast)
done


lemma DynCastRedsFail:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s'\<rangle>; hp s' a = Some (D,S); \<not> P \<turnstile> Path D to C unique;
    \<not> P \<turnstile> Path last Cs to C unique; C \<notin> set Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule DynCastReds)
apply(fastforce intro:RedDynCastFail)
done


lemma DynCastRedsThrow:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule DynCastReds)
apply(simp add:red_reds.DynCastThrow)
done


subsection \<open>LAss\<close>

lemma LAssReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>V:=e,s\<rangle> \<rightarrow>* \<langle>V:=e',s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:LAssRed)
done


lemma LAssRedsVal:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Val v,(h',l')\<rangle>; E V = Some T; P \<turnstile> T casts v to v'\<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> \<langle> V:=e,s\<rangle> \<rightarrow>* \<langle>Val v',(h',l'(V\<mapsto>v'))\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule LAssReds)
apply(simp add:RedLAss)
done


lemma LAssRedsThrow:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle> V:=e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule LAssReds)
apply(simp add:red_reds.LAssThrow)
done


subsection \<open>BinOp\<close>

lemma BinOp1Reds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle> e \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>e' \<guillemotleft>bop\<guillemotright> e\<^sub>2, s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:BinOpRed1)
done


lemma BinOp2Reds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e, s\<rangle> \<rightarrow>* \<langle>(Val v) \<guillemotleft>bop\<guillemotright> e', s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:BinOpRed2)
done


lemma BinOpRedsVal:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v\<^sub>2,s\<^sub>2\<rangle>; 
     binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule BinOp1Reds)
apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp2Reds)
apply(simp add:RedBinOp)
done


lemma BinOpRedsThrow1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>Throw r, s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp1Reds)
apply(simp add:red_reds.BinOpThrow1)
done


lemma BinOpRedsThrow2:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Throw r,s\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>Throw r,s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule BinOp1Reds)
apply(rule rtrancl_into_rtrancl)
 apply(erule BinOp2Reds)
apply(simp add:red_reds.BinOpThrow2)
done


subsection \<open>FAcc\<close>

lemma FAccReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs}, s\<rangle> \<rightarrow>* \<langle>e'\<bullet>F{Cs}, s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:FAccRed)
done


lemma FAccRedsVal:
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ref(a,Cs'),s'\<rangle>; hp s' a = Some(D,S); 
    Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S; fs F = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<rangle> \<rightarrow>* \<langle>Val v,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply (fastforce intro:RedFAcc)
done


lemma FAccRedsNull:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(simp add:RedFAccNull)
done


lemma FAccRedsThrow:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule FAccReds)
apply(simp add:red_reds.FAccThrow)
done


subsection \<open>FAss\<close>

lemma FAssReds1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs}:=e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>e'\<bullet>F{Cs}:=e\<^sub>2, s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:FAssRed1)
done


lemma FAssReds2:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>Val v\<bullet>F{Cs}:=e, s\<rangle> \<rightarrow>* \<langle>Val v\<bullet>F{Cs}:=e', s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:FAssRed2)
done


lemma FAssRedsVal:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>ref(a,Cs'),s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v,(h\<^sub>2,l\<^sub>2)\<rangle>; 
    h\<^sub>2 a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs; P \<turnstile> T casts v to v';
    Ds = Cs'@\<^sub>pCs; (Ds,fs) \<in> S \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* 
        \<langle>Val v',(h\<^sub>2(a\<mapsto>(D,insert (Ds,fs(F\<mapsto>v')) (S - {(Ds,fs)}))),l\<^sub>2)\<rangle>"

apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(fastforce intro:RedFAss)
done


lemma FAssRedsNull:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW NullPointer, s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(simp add:RedFAssNull)
done


lemma FAssRedsThrow1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs}:=e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>Throw r, s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds1)
apply(simp add:red_reds.FAssThrow1)
done


lemma FAssRedsThrow2:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Throw r,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Throw r,s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule FAssReds1)
apply(rule rtrancl_into_rtrancl)
 apply(erule FAssReds2)
apply(simp add:red_reds.FAssThrow2)
done


subsection \<open>;;\<close>

lemma  SeqReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e;;e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>e';;e\<^sub>2, s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:SeqRed)
done


lemma SeqRedsThrow:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e;;e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>Throw r, s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule SeqReds)
apply(simp add:red_reds.SeqThrow)
done


lemma SeqReds2:
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2',s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1;;e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2',s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule SeqReds)
apply(rule_tac b="(e\<^sub>2,s\<^sub>1)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedSeq)
apply assumption
done



subsection \<open>If\<close>

lemma CondReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<rangle> \<rightarrow>* \<langle>if (e') e\<^sub>1 else e\<^sub>2,s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:CondRed)
done


lemma CondRedsThrow:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(simp add:red_reds.CondThrow)
done


lemma CondReds2T:
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>1, s\<^sub>1\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule_tac b="(e\<^sub>1, s\<^sub>1)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedCondT)
apply assumption
done


lemma CondReds2F:
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>false,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2, s\<^sub>1\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<rightarrow>* \<langle>e',s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule_tac b="(e\<^sub>2, s\<^sub>1)" in  converse_rtrancl_into_rtrancl)
 apply(simp add:RedCondF)
apply assumption
done



subsection \<open>While\<close>

lemma WhileFReds:
  "P,E \<turnstile> \<langle>b,s\<rangle> \<rightarrow>* \<langle>false,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>while (b) c,s\<rangle> \<rightarrow>* \<langle>unit,s'\<rangle>"

apply(rule_tac b="(if(b) (c;;while(b) c) else unit, s)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedWhile)
apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(simp add:RedCondF)
done


lemma WhileRedsThrow:
  "P,E \<turnstile> \<langle>b,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>while (b) c,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle>"

apply(rule_tac b="(if(b) (c;;while(b) c) else unit, s)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedWhile)
apply(rule rtrancl_into_rtrancl)
 apply(erule CondReds)
apply(simp add:red_reds.CondThrow)
done


lemma WhileTReds:
  "\<lbrakk> P,E \<turnstile> \<langle>b,s\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>; P,E \<turnstile> \<langle>while (b) c,s\<^sub>2\<rangle> \<rightarrow>* \<langle>e,s\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>while (b) c,s\<^sub>0\<rangle> \<rightarrow>* \<langle>e,s\<^sub>3\<rangle>"

apply(rule_tac b="(if(b) (c;;while(b) c) else unit, s\<^sub>0)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedWhile)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule_tac b="(c;;while(b) c,s\<^sub>1)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedCondT)
apply(rule rtrancl_trans)
 apply(erule SeqReds)
apply(rule_tac b="(while(b) c,s\<^sub>2)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedSeq)
apply assumption
done


lemma WhileTRedsThrow:
  "\<lbrakk> P,E \<turnstile> \<langle>b,s\<^sub>0\<rangle> \<rightarrow>* \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<rightarrow>* \<langle>Throw r,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>while (b) c,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Throw r,s\<^sub>2\<rangle>"

apply(rule_tac b="(if(b) (c;;while(b) c) else unit, s\<^sub>0)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedWhile)
apply(rule rtrancl_trans)
 apply(erule CondReds)
apply(rule_tac b="(c;;while(b) c,s\<^sub>1)" in converse_rtrancl_into_rtrancl)
 apply(simp add:RedCondT)
apply(rule rtrancl_trans)
 apply(erule SeqReds)
apply(rule_tac b="(Throw r,s\<^sub>2)" in converse_rtrancl_into_rtrancl)
 apply(simp add:red_reds.SeqThrow)
apply simp
done


subsection \<open>Throw\<close>

lemma ThrowReds:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>throw e,s\<rangle> \<rightarrow>* \<langle>throw e',s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:ThrowRed)
done


lemma ThrowRedsNull:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>null,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>throw e,s\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule ThrowReds)
apply(simp add:RedThrowNull)
done


lemma ThrowRedsThrow:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>throw e,s\<rangle> \<rightarrow>* \<langle>Throw r,s'\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule ThrowReds)
apply(simp add:red_reds.ThrowThrow)
done


subsection \<open>InitBlock\<close>

lemma assumes wf:"wf_prog wf_md P"
shows InitBlockReds_aux:
"P,E(V \<mapsto> T) \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow>
  \<forall>h l h' l' v v'. s = (h,l(V\<mapsto>v')) \<longrightarrow> 
                   P \<turnstile> T casts v to v' \<longrightarrow> s' = (h',l') \<longrightarrow>
                   (\<exists>v'' w. P,E \<turnstile> \<langle>{V:T := Val v; e},(h,l)\<rangle> \<rightarrow>* 
                                \<langle>{V:T := Val v''; e'},(h',l'(V:=(l V)))\<rangle> \<and>
                            P \<turnstile> T casts v'' to w)"
proof (erule converse_rtrancl_induct2)
  { fix h l h' l' v v'
    assume "s' = (h, l(V \<mapsto> v'))" and "s' = (h', l')"
    hence h:"h = h'" and l':"l' = l(V \<mapsto> v')" by simp_all
    hence "P,E \<turnstile> \<langle>{V:T; V:=Val v;; e'},(h, l)\<rangle> \<rightarrow>*
                 \<langle>{V:T; V:=Val v;; e'},(h', l'(V := l V))\<rangle>"
      by(fastforce simp: fun_upd_same simp del:fun_upd_apply) }
  hence "\<forall>h l h' l' v v'.
         s' = (h, l(V \<mapsto> v')) \<longrightarrow>
           P \<turnstile> T casts v to v'  \<longrightarrow>
             s' = (h', l') \<longrightarrow>
               P,E \<turnstile> \<langle>{V:T; V:=Val v;; e'},(h, l)\<rangle> \<rightarrow>*
                     \<langle>{V:T; V:=Val v;; e'},(h', l'(V := l V))\<rangle> \<and>
               P \<turnstile> T casts v to v'"
    by auto
  thus "\<forall>h l h' l' v v'.
       s' = (h, l(V \<mapsto> v')) \<longrightarrow>
         P \<turnstile> T casts v to v'  \<longrightarrow>
           s' = (h', l') \<longrightarrow>
             (\<exists>v'' w. P,E \<turnstile> \<langle>{V:T; V:=Val v;; e'},(h, l)\<rangle> \<rightarrow>*
                            \<langle>{V:T; V:=Val v'';; e'},(h', l'(V := l V))\<rangle> \<and>
                      P \<turnstile> T casts v'' to w)"
    by auto
next
  fix e s e'' s''
  assume Red:"((e,s),e'',s'') \<in> Red P (E(V \<mapsto> T))"
    and reds:"P,E(V \<mapsto> T) \<turnstile> \<langle>e'',s''\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
    and IH:"\<forall>h l h' l' v v'.
           s'' = (h, l(V \<mapsto> v')) \<longrightarrow>
             P \<turnstile> T casts v to v'  \<longrightarrow>
               s' = (h', l') \<longrightarrow>
                 (\<exists>v'' w. P,E \<turnstile> \<langle>{V:T; V:=Val v;; e''},(h, l)\<rangle> \<rightarrow>*
                                \<langle>{V:T; V:=Val v'';; e'},(h', l'(V := l V))\<rangle> \<and>
                          P \<turnstile> T casts v'' to w)"
  { fix h l h' l' v v'
    assume s:"s = (h, l(V \<mapsto> v'))" and s':"s' = (h', l')"
      and casts:"P \<turnstile> T casts v to v'"
    obtain h'' l'' where s'':"s'' = (h'',l'')" by (cases s'') auto
    with Red s have "V \<in> dom l''" by (fastforce dest:red_lcl_incr)
    then obtain v'' where l'':"l'' V = Some v''" by auto
    with Red s s'' casts
    have step:"P,E \<turnstile> \<langle>{V:T := Val v; e},(h, l)\<rangle> \<rightarrow>  
              \<langle>{V:T := Val v''; e''}, (h'',l''(V := l V))\<rangle>"
      by(fastforce intro:InitBlockRed)
    from Red s s'' l'' casts wf
    have casts':"P \<turnstile> T casts v'' to v''" by(fastforce intro:Some_lcl_casts_values)
    with IH s'' s' l'' obtain v''' w
      where "P,E \<turnstile> \<langle>{V:T := Val v''; e''}, (h'',l''(V := l V))\<rangle> \<rightarrow>*
                   \<langle>{V:T := Val v'''; e'},(h', l'(V := l V))\<rangle> \<and>
             P \<turnstile> T casts v''' to w"
      apply simp
      apply (erule_tac x = "l''(V := l V)" in allE)
      apply (erule_tac x = "v''" in allE)
      apply (erule_tac x = "v''" in allE)
      by(auto intro:ext)
    with step have "\<exists>v'' w. P,E \<turnstile> \<langle>{V:T; V:=Val v;; e},(h, l)\<rangle> \<rightarrow>*
                                   \<langle>{V:T; V:=Val v'';; e'},(h', l'(V := l V))\<rangle> \<and>
                            P \<turnstile> T casts v'' to w"
      apply(rule_tac x="v'''" in exI)
      apply auto
       apply (rule converse_rtrancl_into_rtrancl)
      by simp_all }
  thus "\<forall>h l h' l' v v'.
             s = (h, l(V \<mapsto> v')) \<longrightarrow>
             P \<turnstile> T casts v to v'  \<longrightarrow>
             s' = (h', l') \<longrightarrow>
             (\<exists>v'' w. P,E \<turnstile> \<langle>{V:T; V:=Val v;; e},(h, l)\<rangle> \<rightarrow>*
                            \<langle>{V:T; V:=Val v'';; e'},(h', l'(V := l V))\<rangle> \<and>
                      P \<turnstile> T casts v'' to w)"
    by auto
qed



lemma InitBlockReds:
 "\<lbrakk>P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h,l(V\<mapsto>v'))\<rangle> \<rightarrow>* \<langle>e', (h',l')\<rangle>; 
   P \<turnstile> T casts v to v'; wf_prog wf_md P \<rbrakk> \<Longrightarrow>
  \<exists>v'' w. P,E \<turnstile> \<langle>{V:T := Val v; e}, (h,l)\<rangle> \<rightarrow>* 
              \<langle>{V:T := Val v''; e'}, (h',l'(V:=(l V)))\<rangle> \<and>
          P \<turnstile> T casts v'' to w"
by(blast dest:InitBlockReds_aux)

lemma InitBlockRedsFinal:
  assumes reds:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h,l(V\<mapsto>v'))\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle>"
  and final:"final e'" and casts:"P \<turnstile> T casts v to v'"
  and wf:"wf_prog wf_md P"
  shows "P,E \<turnstile> \<langle>{V:T := Val v; e},(h,l)\<rangle> \<rightarrow>* \<langle>e',(h', l'(V := l V))\<rangle>"
proof -
  from reds casts wf obtain v'' and w
    where steps:"P,E \<turnstile> \<langle>{V:T := Val v; e},(h,l)\<rangle> \<rightarrow>* 
                        \<langle>{V:T := Val v''; e'}, (h',l'(V:=(l V)))\<rangle>"
    and casts':"P \<turnstile> T casts v'' to w"
    by (auto dest:InitBlockReds)
  from final casts casts'
  have step:"P,E \<turnstile> \<langle>{V:T := Val v''; e'}, (h',l'(V:=(l V)))\<rangle> \<rightarrow>
                    \<langle>e',(h',l'(V := l V))\<rangle>"
    by(auto elim!:finalE intro:RedInitBlock InitBlockThrow)
  from step steps show ?thesis
    by(fastforce intro:rtrancl_into_rtrancl)
qed



subsection \<open>Block\<close>

lemma BlockRedsFinal:
assumes reds: "P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2)\<rangle>" and fin: "final e\<^sub>2"
  and wf:"wf_prog wf_md P"
shows "\<And>h\<^sub>0 l\<^sub>0. s\<^sub>0 = (h\<^sub>0,l\<^sub>0(V:=None)) \<Longrightarrow> P,E \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2(V:=l\<^sub>0 V))\<rangle>"

using reds
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case
    by(fastforce intro:finalE[OF fin] RedBlock BlockThrow
                simp del:fun_upd_apply)
next
  case (step e\<^sub>0 s\<^sub>0 e\<^sub>1 s\<^sub>1)
  have Red: "((e\<^sub>0,s\<^sub>0),e\<^sub>1,s\<^sub>1) \<in> Red P (E(V \<mapsto> T))"
   and reds: "P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2)\<rangle>"
   and IH: "\<And>h l. s\<^sub>1 = (h,l(V := None))
                \<Longrightarrow> P,E \<turnstile> \<langle>{V:T; e\<^sub>1},(h,l)\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2, l\<^sub>2(V := l V))\<rangle>"
   and s\<^sub>0: "s\<^sub>0 = (h\<^sub>0, l\<^sub>0(V := None))" by fact+
  obtain h\<^sub>1 l\<^sub>1 where s\<^sub>1: "s\<^sub>1 = (h\<^sub>1,l\<^sub>1)" by fastforce
  show ?case
  proof cases
    assume "assigned V e\<^sub>0"
    then obtain v e where e\<^sub>0: "e\<^sub>0 = V:= Val v;; e"
      by (unfold assigned_def)blast
    from Red e\<^sub>0 s\<^sub>0 obtain v' where e\<^sub>1: "e\<^sub>1 = Val v';;e" 
      and s\<^sub>1: "s\<^sub>1 = (h\<^sub>0, l\<^sub>0(V \<mapsto> v'))" and casts:"P \<turnstile> T casts v to v'"
      by auto
    from e\<^sub>1 fin have "e\<^sub>1 \<noteq> e\<^sub>2" by (auto simp:final_def)
    then obtain e' s' where red1: "P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
      and reds': "P,E(V \<mapsto> T) \<turnstile> \<langle>e',s'\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2)\<rangle>"
      using converse_rtranclE2[OF reds] by simp blast
    from red1 e\<^sub>1 have es': "e' = e" "s' = s\<^sub>1" by auto
    show ?thesis using e\<^sub>0 s\<^sub>1 es' reds'
        by(fastforce intro!: InitBlockRedsFinal[OF _ fin casts wf] 
                    simp del:fun_upd_apply)
  next
    assume unass: "\<not> assigned V e\<^sub>0"
    show ?thesis
    proof (cases "l\<^sub>1 V")
      assume None: "l\<^sub>1 V = None"
      hence "P,E \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow> \<langle>{V:T; e\<^sub>1},(h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V))\<rangle>"
        using s\<^sub>0 s\<^sub>1 Red by(simp add: BlockRedNone[OF _ _ unass])
      moreover
      have "P,E \<turnstile> \<langle>{V:T; e\<^sub>1},(h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V))\<rangle> \<rightarrow>* \<langle>e\<^sub>2,(h\<^sub>2, l\<^sub>2(V := l\<^sub>0 V))\<rangle>"
        using IH[of _ "l\<^sub>1(V := l\<^sub>0 V)"] s\<^sub>1 None by(simp add:fun_upd_idem)
      ultimately show ?case
        by(rule_tac b="({V:T; e\<^sub>1},(h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V)))" in converse_rtrancl_into_rtrancl,simp)
    next
      fix v assume Some: "l\<^sub>1 V = Some v"
      with Red Some s\<^sub>0 s\<^sub>1 wf
      have casts:"P \<turnstile> T casts v to v"
        by(fastforce intro:None_lcl_casts_values)
      from Some
      have "P,E \<turnstile> \<langle>{V:T;e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow> \<langle>{V:T := Val v; e\<^sub>1},(h\<^sub>1,l\<^sub>1(V := l\<^sub>0 V))\<rangle>"
        using s\<^sub>0 s\<^sub>1 Red by(simp add: BlockRedSome[OF _ _ unass])
      moreover
      have "P,E \<turnstile> \<langle>{V:T := Val v; e\<^sub>1},(h\<^sub>1,l\<^sub>1(V:= l\<^sub>0 V))\<rangle> \<rightarrow>*
                \<langle>e\<^sub>2,(h\<^sub>2,l\<^sub>2(V:=l\<^sub>0 V))\<rangle>"
        using InitBlockRedsFinal[OF _ fin casts wf,of _ _ "l\<^sub>1(V:=l\<^sub>0 V)" V] 
          Some reds s\<^sub>1
        by (simp add:fun_upd_idem)
      ultimately show ?case 
        by(rule_tac b="({V:T; V:=Val v;; e\<^sub>1},(h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V)))" in converse_rtrancl_into_rtrancl,simp)
    qed
  qed
qed




subsection \<open>List\<close>

lemma ListReds1:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e#es,s\<rangle> [\<rightarrow>]* \<langle>e' # es,s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:ListRed1)
done


lemma ListReds2:
  "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>Val v # es,s\<rangle> [\<rightarrow>]* \<langle>Val v # es',s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:ListRed2)
done


lemma ListRedsVal:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>es',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e#es,s\<^sub>0\<rangle> [\<rightarrow>]* \<langle>Val v # es',s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule ListReds1)
apply(erule ListReds2)
done


subsection \<open>Call\<close>

text\<open>First a few lemmas on what happens to free variables during redction.\<close>


lemma assumes wf: "wwf_prog P"
shows Red_fv: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> fv e' \<subseteq> fv e"
  and  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> fvs es' \<subseteq> fvs es"
proof (induct rule:red_reds_inducts)
  case (RedCall h l a C S Cs M Ts' T' pns' body' Ds Ts T pns body Cs' vs bs new_body E)
  hence "fv body \<subseteq> {this} \<union> set pns"
    using assms by(fastforce dest!:select_method_wf_mdecl simp:wf_mdecl_def)
  with RedCall.hyps show ?case
    by(cases T') auto
next
  case (RedStaticCall Cs C Cs'' M Ts T pns body Cs' Ds vs E a a' b)
  hence "fv body \<subseteq> {this} \<union> set pns"
    using assms by(fastforce dest!:has_least_wf_mdecl simp:wf_mdecl_def)
  with RedStaticCall.hyps show ?case
    by auto
qed auto



lemma Red_dom_lcl:
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fv e" and
  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fvs es"

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



lemma Reds_dom_lcl:
  "\<lbrakk> wwf_prog P; P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow>* \<langle>e',(h',l')\<rangle> \<rbrakk> \<Longrightarrow> dom l' \<subseteq> dom l \<union> fv e"

apply(erule converse_rtrancl_induct_red)
 apply blast
apply(blast dest: Red_fv Red_dom_lcl)
done


text\<open>Now a few lemmas on the behaviour of blocks during reduction.\<close>


lemma override_on_upd_lemma:
  "(override_on f (g(a\<mapsto>b)) A)(a := g a) = override_on f g (insert a A)"

apply(rule ext)
apply(simp add:override_on_def)
done

declare fun_upd_apply[simp del] map_upds_twist[simp del]




lemma assumes wf:"wf_prog wf_md P"
  shows blocksReds:
  "\<And>l\<^sub>0 E vs'. \<lbrakk> length Vs = length Ts; length vs = length Ts; 
        distinct Vs; \<^cancel>\<open>\<forall>T\<in>set Ts. is_type P T;\<close> P \<turnstile> Ts Casts vs to vs';
        P,E(Vs [\<mapsto>] Ts) \<turnstile> \<langle>e, (h\<^sub>0,l\<^sub>0(Vs [\<mapsto>] vs'))\<rangle> \<rightarrow>* \<langle>e', (h\<^sub>1,l\<^sub>1)\<rangle> \<rbrakk>
  \<Longrightarrow> \<exists>vs''. P,E \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow>* 
                   \<langle>blocks(Vs,Ts,vs'',e'), (h\<^sub>1,override_on l\<^sub>1 l\<^sub>0 (set Vs))\<rangle> \<and> 
             (\<exists>ws. P \<turnstile> Ts Casts vs'' to ws) \<and> length vs = length vs''"

proof(induct Vs Ts vs e rule:blocks_old_induct)
  case (5 V Vs T Ts v vs e)
  have length1:"length (V#Vs) = length (T#Ts)"
    and length2:"length (v#vs) = length (T#Ts)"
    and dist:"distinct (V#Vs)"
    and casts:"P \<turnstile> (T#Ts) Casts (v#vs) to vs'"
    and reds:"P,E(V#Vs [\<mapsto>] T#Ts) \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0(V#Vs [\<mapsto>] vs'))\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>1,l\<^sub>1)\<rangle>"
    and IH:"\<And>l\<^sub>0 E vs''. \<lbrakk>length Vs = length Ts; length vs = length Ts; 
       distinct Vs; P \<turnstile> Ts Casts vs to vs'';
       P,E(Vs [\<mapsto>] Ts) \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0(Vs [\<mapsto>] vs''))\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>1,l\<^sub>1)\<rangle>\<rbrakk>
        \<Longrightarrow> \<exists>vs''. P,E \<turnstile> \<langle>blocks (Vs,Ts,vs,e),(h\<^sub>0,l\<^sub>0)\<rangle> \<rightarrow>*
                         \<langle>blocks (Vs,Ts,vs'',e'),(h\<^sub>1, override_on l\<^sub>1 l\<^sub>0 (set Vs))\<rangle> \<and>
                   (\<exists>ws. P \<turnstile> Ts Casts vs'' to ws) \<and> length vs = length vs''" by fact+
  from length1 have length1':"length Vs = length Ts" by simp
  from length2 have length2':"length vs = length Ts" by simp
  from dist have dist':"distinct Vs" by simp
  from casts obtain x xs where vs':"vs' = x#xs"
    by(cases vs',auto dest:length_Casts_vs')
  with reds
  have reds':"P,E(V \<mapsto> T)(Vs [\<mapsto>] Ts) \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0(V \<mapsto> x)(Vs [\<mapsto>] xs))\<rangle> 
                                    \<rightarrow>* \<langle>e',(h\<^sub>1,l\<^sub>1)\<rangle>"
    by simp
  from casts vs' have casts':"P \<turnstile> Ts Casts vs to xs" 
    and cast':"P \<turnstile> T casts v to x"
    by(auto elim:Casts_to.cases)
  from IH[OF length1' length2' dist' casts' reds']
  obtain vs'' ws
    where blocks:"P,E(V \<mapsto> T) \<turnstile> \<langle>blocks (Vs, Ts, vs, e),(h\<^sub>0, l\<^sub>0(V \<mapsto> x))\<rangle> \<rightarrow>*
             \<langle>blocks (Vs, Ts, vs'', e'),(h\<^sub>1, override_on l\<^sub>1 (l\<^sub>0(V \<mapsto> x)) (set Vs))\<rangle>"
    and castsws:"P \<turnstile> Ts Casts vs'' to ws"
    and lengthvs'':"length vs = length vs''" by auto
  from InitBlockReds[OF blocks cast' wf] obtain v'' w where
    blocks':"P,E \<turnstile> \<langle>{V:T; V:=Val v;; blocks (Vs, Ts, vs, e)},(h\<^sub>0, l\<^sub>0)\<rangle> \<rightarrow>*
                   \<langle>{V:T; V:=Val v'';; blocks (Vs, Ts, vs'', e')},
                    (h\<^sub>1, (override_on l\<^sub>1 (l\<^sub>0(V \<mapsto> x)) (set Vs))(V := l\<^sub>0 V))\<rangle>"
    and "P \<turnstile> T casts v'' to w" by auto
  with castsws have "P \<turnstile> T#Ts Casts v''#vs'' to w#ws"
    by -(rule Casts_Cons)
  with blocks' lengthvs'' show ?case
    by(rule_tac x="v''#vs''" in exI,auto simp:override_on_upd_lemma)
next
  case (6 e)
  have casts:"P \<turnstile> [] Casts [] to vs'" 
    and step:"P,E([] [\<mapsto>] []) \<turnstile> \<langle>e,(h\<^sub>0, l\<^sub>0([] [\<mapsto>] vs'))\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>1, l\<^sub>1)\<rangle>" by fact+
  from casts have "vs' = []" by(fastforce dest:length_Casts_vs')
  with step have "P,E \<turnstile> \<langle>e,(h\<^sub>0, l\<^sub>0)\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>1, l\<^sub>1)\<rangle>" by simp
  with casts show ?case by auto
qed simp_all



lemma assumes wf:"wf_prog wf_md P"
  shows blocksFinal:
 "\<And>E l vs'. \<lbrakk> length Vs = length Ts; length vs = length Ts;
           \<^cancel>\<open>\<forall>T\<in>set Ts. is_type P T;\<close> final e; P \<turnstile> Ts Casts vs to vs' \<rbrakk> \<Longrightarrow>
       P,E \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h,l)\<rangle> \<rightarrow>* \<langle>e, (h,l)\<rangle>"

proof(induct Vs Ts vs e rule:blocks_old_induct)
  case (5 V Vs T Ts v vs e)
  have length1:"length (V # Vs) = length (T # Ts)"
    and length2:"length (v # vs) = length (T # Ts)"
    and final:"final e" and casts:"P \<turnstile> T # Ts Casts v # vs to vs'"
    and IH:"\<And>E l vs'. \<lbrakk>length Vs = length Ts; length vs = length Ts; final e;
                   P \<turnstile> Ts Casts vs to vs' \<rbrakk>
                  \<Longrightarrow> P,E \<turnstile> \<langle>blocks (Vs, Ts, vs, e),(h, l)\<rangle> \<rightarrow>* \<langle>e,(h, l)\<rangle>" by fact+
  from length1 length2
  have length1':"length Vs = length Ts" and length2':"length vs = length Ts"
    by simp_all
  from casts obtain x xs where vs':"vs' = x#xs"
    by(cases vs',auto dest:length_Casts_vs')
  with casts have casts':"P \<turnstile> Ts Casts vs to xs" 
    and cast':"P \<turnstile> T casts v to x"
    by(auto elim:Casts_to.cases)
  from InitBlockReds[OF IH[OF length1' length2' final casts'] cast' wf, of V l]
  obtain v'' w
    where blocks:"P,E \<turnstile> \<langle>{V:T; V:=Val v;; blocks (Vs, Ts, vs, e)},(h, l)\<rangle> \<rightarrow>*
                        \<langle>{V:T; V:=Val v'';; e},(h,l)\<rangle>"
    and "P \<turnstile> T casts v'' to w" by auto blast
  with final have "P,E \<turnstile> \<langle>{V:T; V:=Val v'';; e},(h,l)\<rangle> \<rightarrow> \<langle>e,(h,l)\<rangle>"
    by(auto elim!:finalE intro:RedInitBlock InitBlockThrow)
  with blocks show ?case
    by -(rule_tac b="({V:T; V:=Val v'';; e},(h, l))" in rtrancl_into_rtrancl,simp_all)
qed auto



lemma assumes wfmd:"wf_prog wf_md P"
  and wf: "length Vs = length Ts" "length vs = length Ts" "distinct Vs" 
  and casts:"P \<turnstile> Ts Casts vs to vs'"
  and reds: "P,E(Vs [\<mapsto>] Ts) \<turnstile> \<langle>e, (h\<^sub>0, l\<^sub>0(Vs [\<mapsto>] vs'))\<rangle> \<rightarrow>* \<langle>e', (h\<^sub>1, l\<^sub>1)\<rangle>"
  and fin: "final e'" and l2: "l\<^sub>2 = override_on l\<^sub>1 l\<^sub>0 (set Vs)"
shows blocksRedsFinal: "P,E \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h\<^sub>0, l\<^sub>0)\<rangle> \<rightarrow>* \<langle>e', (h\<^sub>1,l\<^sub>2)\<rangle>"

proof -
  obtain vs'' ws where blocks:"P,E \<turnstile> \<langle>blocks(Vs,Ts,vs,e), (h\<^sub>0, l\<^sub>0)\<rangle> \<rightarrow>* 
                                  \<langle>blocks(Vs,Ts,vs'',e'), (h\<^sub>1,l\<^sub>2)\<rangle>"
    and length:"length vs = length vs''"
    and casts':"P \<turnstile> Ts Casts vs'' to ws"
    using l2 blocksReds[OF wfmd wf casts reds]
     by auto
   have "P,E \<turnstile> \<langle>blocks(Vs,Ts,vs'',e'), (h\<^sub>1,l\<^sub>2)\<rangle> \<rightarrow>* \<langle>e', (h\<^sub>1,l\<^sub>2)\<rangle>"
     using blocksFinal[OF wfmd _ _ fin casts'] wf length by simp
   with blocks show ?thesis by simp
qed




text\<open>An now the actual method call reduction lemmas.\<close>

lemma CallRedsObj:
 "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> 
  P,E \<turnstile> \<langle>Call e Copt M es,s\<rangle> \<rightarrow>* \<langle>Call e' Copt M es,s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:CallObj)
done


lemma CallRedsParams:
 "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle> \<Longrightarrow> 
  P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<rightarrow>* \<langle>Call (Val v) Copt M es',s'\<rangle>"

apply(erule rtrancl_induct2)
 apply blast
apply(erule rtrancl_into_rtrancl)
apply(simp add:CallParams)
done




lemma cast_lcl:
  "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l)\<rangle> \<rightarrow> \<langle>Val v',(h,l)\<rangle> \<Longrightarrow>
   P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l')\<rangle> \<rightarrow> \<langle>Val v',(h,l')\<rangle>"

apply(erule red.cases)
apply(auto intro:red_reds.intros)
apply(subgoal_tac "P,E \<turnstile> \<langle>\<lparr>C\<rparr>ref (a,Cs@[C]@Cs'),(h,l')\<rangle> \<rightarrow> \<langle>ref (a,Cs@[C]),(h,l')\<rangle>")
 apply simp
apply(rule RedStaticDownCast)
done


lemma cast_env:
  "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l)\<rangle> \<rightarrow> \<langle>Val v',(h,l)\<rangle> \<Longrightarrow> 
   P,E' \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l)\<rangle> \<rightarrow> \<langle>Val v',(h,l)\<rangle>"

apply(erule red.cases)
apply(auto intro:red_reds.intros)
apply(subgoal_tac "P,E' \<turnstile> \<langle>\<lparr>C\<rparr>ref (a,Cs@[C]@Cs'),(h,l)\<rangle> \<rightarrow> \<langle>ref (a,Cs@[C]),(h,l)\<rangle>")
 apply simp
apply(rule RedStaticDownCast)
done


lemma Cast_step_Cast_or_fin:
"P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> final e' \<or> (\<exists>e''. e' = \<lparr>C\<rparr>e'')"
by(induct rule:rtrancl_induct2,auto elim:red.cases simp:final_def)

lemma Cast_red:"P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<Longrightarrow> 
  (\<And>e\<^sub>1. \<lbrakk>e = \<lparr>C\<rparr>e\<^sub>0; e' = \<lparr>C\<rparr>e\<^sub>1\<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>0,s\<rangle> \<rightarrow>* \<langle>e\<^sub>1,s'\<rangle>)"

proof(induct rule:rtrancl_induct2)
  case refl thus ?case by simp
next
  case (step e'' s'' e' s')
  have step:"P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e'',s''\<rangle>"
    and Red:"((e'', s''), e', s') \<in> Red P E"
    and cast:"e = \<lparr>C\<rparr>e\<^sub>0" and cast':"e' = \<lparr>C\<rparr>e\<^sub>1"
    and IH:"\<And>e\<^sub>1. \<lbrakk>e = \<lparr>C\<rparr>e\<^sub>0; e'' = \<lparr>C\<rparr>e\<^sub>1\<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>0,s\<rangle> \<rightarrow>* \<langle>e\<^sub>1,s''\<rangle>" by fact+
  from Red have red:"P,E \<turnstile> \<langle>e'',s''\<rangle> \<rightarrow> \<langle>e',s'\<rangle>" by simp
  from step cast have "final e'' \<or> (\<exists>ex. e'' = \<lparr>C\<rparr>ex)"
    by simp(rule Cast_step_Cast_or_fin)
  thus ?case
  proof(rule disjE)
    assume "final e''"
    with red show ?thesis by(auto simp:final_def)
  next
    assume "\<exists>ex. e'' = \<lparr>C\<rparr>ex"
    then obtain ex where e'':"e'' = \<lparr>C\<rparr>ex" by blast
    with cast' red have "P,E \<turnstile> \<langle>ex,s''\<rangle> \<rightarrow> \<langle>e\<^sub>1,s'\<rangle>"
      by(auto elim:red.cases)
    with  IH[OF cast e''] show ?thesis
      by(rule_tac b="(ex,s'')" in rtrancl_into_rtrancl,simp_all)
  qed
qed


lemma Cast_final:"\<lbrakk>P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>; final e'\<rbrakk> \<Longrightarrow>
\<exists>e'' s''. P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e'',s''\<rangle> \<and> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e'',s''\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<and> final e''"

proof(induct rule:rtrancl_induct2)
  case refl thus ?case by (simp add:final_def)
next
  case (step e'' s'' e' s')
  have step:"P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<rangle> \<rightarrow>* \<langle>e'',s''\<rangle>"
    and Red:"((e'', s''), e', s') \<in> Red P E"
    and final:"final e'"
    and IH:"final e'' \<Longrightarrow> 
   \<exists>ex sx. P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ex,sx\<rangle> \<and> P,E \<turnstile> \<langle>\<lparr>C\<rparr>ex,sx\<rangle> \<rightarrow> \<langle>e'',s''\<rangle> \<and> final ex" by fact+
  from Red have red:"P,E \<turnstile> \<langle>e'',s''\<rangle> \<rightarrow> \<langle>e',s'\<rangle>" by simp
  from step have "final e'' \<or> (\<exists>ex. e'' = \<lparr>C\<rparr>ex)" by(rule Cast_step_Cast_or_fin)
  thus ?case
  proof(rule disjE)
    assume "final e''"
    with red show ?thesis by(auto simp:final_def)
  next
    assume "\<exists>ex. e'' = \<lparr>C\<rparr>ex"
    then obtain ex where e'':"e'' = \<lparr>C\<rparr>ex" by blast
    with red final have final':"final ex"
      by(auto elim:red.cases simp:final_def)
    from step e'' have "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>ex,s''\<rangle>"
      by(fastforce intro:Cast_red)
    with e'' red final' show ?thesis by blast
  qed
qed


lemma Cast_final_eq:
  assumes red:"P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h,l)\<rangle>"
  and final:"final e" and final':"final e'"
  shows "P,E' \<turnstile> \<langle>\<lparr>C\<rparr>e,(h,l')\<rangle> \<rightarrow> \<langle>e',(h,l')\<rangle>"

proof -
  from red final show ?thesis
  proof(auto simp:final_def)
    fix v assume "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l)\<rangle> \<rightarrow> \<langle>e',(h,l)\<rangle>"
    with final' show "P,E' \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l')\<rangle> \<rightarrow> \<langle>e',(h,l')\<rangle>"
    proof(auto simp:final_def)
      fix v' assume "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l)\<rangle> \<rightarrow> \<langle>Val v',(h,l)\<rangle>"
      thus "P,E' \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l')\<rangle> \<rightarrow> \<langle>Val v',(h,l')\<rangle>"
        by(auto intro:cast_lcl cast_env)
    next
      fix a Cs assume "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l)\<rangle> \<rightarrow> \<langle>Throw (a,Cs),(h,l)\<rangle>"
      thus "P,E' \<turnstile> \<langle>\<lparr>C\<rparr>(Val v),(h,l')\<rangle> \<rightarrow> \<langle>Throw (a,Cs),(h,l')\<rangle>"
        by(auto elim:red.cases intro!:RedStaticCastFail)
    qed
  next
    fix a Cs assume "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Throw (a,Cs)),(h,l)\<rangle> \<rightarrow> \<langle>e',(h,l)\<rangle>"
    with final' show "P,E' \<turnstile> \<langle>\<lparr>C\<rparr>(Throw (a,Cs)),(h,l')\<rangle> \<rightarrow> \<langle>e',(h,l')\<rangle>"
    proof(auto simp:final_def)
      fix v assume "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Throw (a,Cs)),(h,l)\<rangle> \<rightarrow> \<langle>Val v,(h,l)\<rangle>"
      thus "P,E' \<turnstile> \<langle>\<lparr>C\<rparr>(Throw (a,Cs)),(h,l')\<rangle> \<rightarrow> \<langle>Val v,(h,l')\<rangle>"
        by(auto elim:red.cases)
    next
      fix a' Cs'
      assume "P,E \<turnstile> \<langle>\<lparr>C\<rparr>(Throw (a,Cs)),(h,l)\<rangle> \<rightarrow> \<langle>Throw (a',Cs'),(h,l)\<rangle>"
      thus "P,E' \<turnstile> \<langle>\<lparr>C\<rparr>(Throw (a,Cs)),(h,l')\<rangle> \<rightarrow> \<langle>Throw (a',Cs'),(h,l')\<rangle>"
        by(auto elim:red.cases intro:red_reds.StaticCastThrow)
    qed
  qed
qed



lemma CallRedsFinal:
assumes wwf: "wwf_prog P"
and "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s\<^sub>1\<rangle>"
      "P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
and hp: "h\<^sub>2 a = Some(C,S)"
and "method": "P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds"
and select: "P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'"
and size: "size vs = size pns"
and casts: "P \<turnstile> Ts Casts vs to vs'"
and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Ref(a,Cs'), pns[\<mapsto>]vs']"
and body_case:"new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body  | _ \<Rightarrow> body)"
and body: "P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> \<langle>new_body,(h\<^sub>2,l\<^sub>2')\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>3)\<rangle>"
and final:"final ef"
shows "P,E \<turnstile> \<langle>e\<bullet>M(es), s\<^sub>0\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2)\<rangle>"
proof -
  have wf: "size Ts = size pns \<and> distinct pns \<and> this \<notin> set pns"
    and wt: "fv body \<subseteq> {this} \<union> set pns"
    using assms by(fastforce dest!:select_method_wf_mdecl simp:wf_mdecl_def)+
  have "dom l\<^sub>3 \<subseteq> {this} \<union> set pns"
    using Reds_dom_lcl[OF wwf body] wt l\<^sub>2' set_take_subset body_case
    by (cases T') force+
  hence eql\<^sub>2: "override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns) = l\<^sub>2"
    by(fastforce simp add:map_add_def override_on_def fun_eq_iff)
  from wwf select have "is_class P (last Cs')"
    by (auto elim!:SelectMethodDef.cases intro:Subobj_last_isClass 
             simp:LeastMethodDef_def FinalOverriderMethodDef_def 
                  OverriderMethodDefs_def MinimalMethodDefs_def MethodDefs_def)
  hence "P \<turnstile> Class (last Cs') casts Ref(a,Cs') to Ref(a,Cs')"
    by(auto intro!:casts_ref Subobjs_Base simp:path_via_def appendPath_def)
  with casts
  have casts':"P \<turnstile> Class (last Cs')#Ts Casts Ref(a,Cs')#vs to  Ref(a,Cs')#vs'"
    by -(rule Casts_Cons)
  have 1:"P,E \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<rightarrow>* \<langle>(ref(a,Cs))\<bullet>M(es),s\<^sub>1\<rangle>" by(rule CallRedsObj)(rule assms(2))
  have 2:"P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>M(es),s\<^sub>1\<rangle> \<rightarrow>*
                 \<langle>(ref(a,Cs))\<bullet>M(map Val vs),(h\<^sub>2,l\<^sub>2)\<rangle>"
    by(rule CallRedsParams)(rule assms(3))
  from body[THEN Red_lcl_add, of l\<^sub>2]
  have body': "P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> 
             \<langle>new_body,(h\<^sub>2,l\<^sub>2(this\<mapsto> Ref(a,Cs'), pns[\<mapsto>]vs'))\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2++l\<^sub>3)\<rangle>"
    by (simp add:l\<^sub>2')
  show ?thesis
  proof(cases "\<forall>C. T'\<noteq> Class C")
    case True
    hence "P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>M(map Val vs), (h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow> 
                 \<langle>blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body), (h\<^sub>2,l\<^sub>2)\<rangle>"
      using hp "method" select size wf
      by -(rule RedCall,auto,cases T',auto)
    hence 3:"P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>M(map Val vs), (h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow>* 
                   \<langle>blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body), (h\<^sub>2,l\<^sub>2)\<rangle>"
      by(simp add:r_into_rtrancl)
    have "P,E \<turnstile> \<langle>blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body),(h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow>* 
                \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns))\<rangle>"
      using True wf body' wwf size final casts' body_case
      by -(rule_tac vs'="Ref(a,Cs')#vs'" in blocksRedsFinal,simp_all,cases T',auto)
    with 1 2 3 show ?thesis using eql\<^sub>2
      by simp
  next
    case False
    then obtain D where T':"T' = Class D" by auto
    with final body' body_case obtain s' e' where 
      body'':"P,E(this \<mapsto> Class (last Cs'),pns [\<mapsto>] Ts) \<turnstile> 
                           \<langle>body,(h\<^sub>2,l\<^sub>2(this\<mapsto> Ref(a,Cs'), pns[\<mapsto>]vs'))\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
      and final':"final e'" 
      and cast:"P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> \<langle>\<lparr>D\<rparr>e',s'\<rangle> \<rightarrow> 
                                                           \<langle>ef,(h\<^sub>3,l\<^sub>2++l\<^sub>3)\<rangle>"
      by(cases T')(auto dest:Cast_final)
    from T' have "P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>M(map Val vs), (h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow> 
                 \<langle>\<lparr>D\<rparr>blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body), (h\<^sub>2,l\<^sub>2)\<rangle>"
      using hp "method" select size wf
      by -(rule RedCall,auto)
    hence 3:"P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>M(map Val vs), (h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow>* 
                  \<langle>\<lparr>D\<rparr>blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body),(h\<^sub>2,l\<^sub>2)\<rangle>"
      by(simp add:r_into_rtrancl)
    from cast final have eq:"s' = (h\<^sub>3,l\<^sub>2++l\<^sub>3)"
      by(auto elim:red.cases simp:final_def)
    hence "P,E \<turnstile> \<langle>blocks(this#pns, Class (last Cs')#Ts, Ref(a,Cs')#vs,body), (h\<^sub>2,l\<^sub>2)\<rangle>
                 \<rightarrow>* \<langle>e',(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns))\<rangle>"
      using wf body'' wwf size final' casts'
      by -(rule_tac vs'="Ref(a,Cs')#vs'" in blocksRedsFinal,simp_all)
    hence "P,E \<turnstile> \<langle>\<lparr>D\<rparr>(blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body)),(h\<^sub>2,l\<^sub>2)\<rangle>
             \<rightarrow>* \<langle>\<lparr>D\<rparr>e',(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns))\<rangle>"
      by(rule StaticCastReds)
    moreover
    have "P,E \<turnstile> \<langle>\<lparr>D\<rparr>e',(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns))\<rangle> \<rightarrow> 
                \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns))\<rangle>"
      using eq cast final final'
      by(fastforce intro:Cast_final_eq)
    ultimately
    have "P,E \<turnstile> \<langle>\<lparr>D\<rparr>(blocks(this#pns, Class (last Cs')#Ts, Ref(a,Cs')#vs,body)), 
                  (h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns))\<rangle>"
      by(rule_tac b="(\<lparr>D\<rparr>e',(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns)))"
        in rtrancl_into_rtrancl,simp_all)
    with 1 2 3 show ?thesis using eql\<^sub>2
      by simp
  qed
qed


lemma StaticCallRedsFinal:
assumes wwf: "wwf_prog P"
and "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s\<^sub>1\<rangle>"
      "P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
and path_unique: "P \<turnstile> Path (last Cs) to C unique"
and path_via: "P \<turnstile> Path (last Cs) to C via Cs''" 
and Ds: "Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs'"
and least: "P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'"
and size: "size vs = size pns"
and casts: "P \<turnstile> Ts Casts vs to vs'"
and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Ref(a,Ds), pns[\<mapsto>]vs']"
and body: "P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>3)\<rangle>"
and final:"final ef"
shows "P,E \<turnstile> \<langle>e\<bullet>(C::)M(es), s\<^sub>0\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2)\<rangle>"
proof -
  have wf: "size Ts = size pns \<and> distinct pns \<and> this \<notin> set pns \<and> 
            (\<forall>T\<in>set Ts. is_type P T)"
    and wt: "fv body \<subseteq> {this} \<union> set pns"
    using assms by(fastforce dest!:has_least_wf_mdecl simp:wf_mdecl_def)+
  have "dom l\<^sub>3 \<subseteq> {this} \<union> set pns"
    using Reds_dom_lcl[OF wwf body] wt l\<^sub>2' set_take_subset
    by force
  hence eql\<^sub>2: "override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns) = l\<^sub>2"
    by(fastforce simp add:map_add_def override_on_def fun_eq_iff)
  from wwf least have "Cs' \<noteq> []"
    by (auto elim!:Subobjs_nonempty simp:LeastMethodDef_def MethodDefs_def)
  with Ds have "last Cs' = last Ds" by(fastforce intro:appendPath_last)
  with wwf least have "is_class P (last Ds)"
    by(auto dest:Subobj_last_isClass simp:LeastMethodDef_def MethodDefs_def)
  hence "P \<turnstile> Class (last Ds) casts Ref(a,Ds) to Ref(a,Ds)"
    by(auto intro!:casts_ref Subobjs_Base simp:path_via_def appendPath_def)
  with casts
  have casts':"P \<turnstile> Class (last Ds)#Ts Casts Ref(a,Ds)#vs to Ref(a,Ds)#vs'"
    by -(rule Casts_Cons)
  have 1:"P,E \<turnstile> \<langle>e\<bullet>(C::)M(es),s\<^sub>0\<rangle> \<rightarrow>* \<langle>(ref(a,Cs))\<bullet>(C::)M(es),s\<^sub>1\<rangle>"
    by(rule CallRedsObj)(rule assms(2))
  have 2:"P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>(C::)M(es),s\<^sub>1\<rangle> \<rightarrow>*
                 \<langle>(ref(a,Cs))\<bullet>(C::)M(map Val vs),(h\<^sub>2,l\<^sub>2)\<rangle>"
    by(rule CallRedsParams)(rule assms(3))
  from body[THEN Red_lcl_add, of l\<^sub>2]
  have body': "P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> 
              \<langle>body,(h\<^sub>2,l\<^sub>2(this\<mapsto> Ref(a,Ds), pns[\<mapsto>]vs'))\<rangle> \<rightarrow>* \<langle>ef,(h\<^sub>3,l\<^sub>2++l\<^sub>3)\<rangle>"
    by (simp add:l\<^sub>2')
  have "P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>(C::)M(map Val vs), (h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow>
              \<langle>blocks(this#pns, Class (last Ds)#Ts, Ref(a,Ds)#vs, body), (h\<^sub>2,l\<^sub>2)\<rangle>"
    using path_unique path_via least size wf Ds
    by -(rule RedStaticCall,auto)
  hence 3:"P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>(C::)M(map Val vs), (h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow>* 
                   \<langle>blocks(this#pns,Class(last Ds)#Ts,Ref(a,Ds)#vs,body), (h\<^sub>2,l\<^sub>2)\<rangle>"
    by(simp add:r_into_rtrancl)
  have "P,E \<turnstile> \<langle>blocks(this#pns,Class(last Ds)#Ts,Ref(a,Ds)#vs,body),(h\<^sub>2,l\<^sub>2)\<rangle> \<rightarrow>* 
                \<langle>ef,(h\<^sub>3,override_on (l\<^sub>2++l\<^sub>3) l\<^sub>2 ({this} \<union> set pns))\<rangle>"
    using wf body' wwf size final casts'
    by -(rule_tac vs'="Ref(a,Ds)#vs'" in blocksRedsFinal,simp_all)
  with 1 2 3 show ?thesis using eql\<^sub>2
    by simp
qed



lemma CallRedsThrowParams:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Val v,s\<^sub>1\<rangle>;  
    P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs\<^sub>1 @ Throw ex # es\<^sub>2,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Throw ex,s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule CallRedsObj)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsParams)
apply(simp add:CallThrowParams)
done



lemma CallRedsThrowObj:
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Throw ex,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<rightarrow>* \<langle>Throw ex,s\<^sub>1\<rangle>"

apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsObj)
apply(simp add:CallThrowObj)
done



lemma CallRedsNull:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>null,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<rightarrow>* \<langle>THROW NullPointer,s\<^sub>2\<rangle>"

apply(rule rtrancl_trans)
 apply(erule CallRedsObj)
apply(rule rtrancl_into_rtrancl)
 apply(erule CallRedsParams)
apply(simp add:RedCallNull)
done



subsection \<open>The main Theorem\<close>

lemma assumes wwf: "wwf_prog P"
shows big_by_small: "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
and bigs_by_smalls: "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"

proof (induct rule: eval_evals.inducts)
  case New thus ?case by (auto simp:RedNew)
next
  case NewFail thus ?case by (auto simp:RedNewFail)
next
  case StaticUpCast thus ?case by(simp add:StaticUpCastReds)
next
  case StaticDownCast thus ?case by(simp add:StaticDownCastReds)
next
  case StaticCastNull thus ?case by(simp add:StaticCastRedsNull)
next
  case StaticCastFail thus ?case by(simp add:StaticCastRedsFail)
next
  case StaticCastThrow thus ?case by(auto dest!:eval_final simp:StaticCastRedsThrow)
next
  case StaticUpDynCast thus ?case by(simp add:StaticUpDynCastReds)
next
  case StaticDownDynCast thus ?case by(simp add:StaticDownDynCastReds)
next
  case DynCast thus ?case by(fastforce intro:DynCastRedsRef)
next
  case DynCastNull thus ?case by(simp add:DynCastRedsNull)
next
  case DynCastFail thus ?case by(fastforce intro!:DynCastRedsFail)
next
  case DynCastThrow thus ?case by(auto dest!:eval_final simp:DynCastRedsThrow)
next
  case Val thus ?case by simp
next
  case BinOp thus ?case by(fastforce simp:BinOpRedsVal)
next
  case BinOpThrow1 thus ?case by(fastforce dest!:eval_final simp: BinOpRedsThrow1)
next
  case BinOpThrow2 thus ?case by(fastforce dest!:eval_final simp: BinOpRedsThrow2)
next
  case Var thus ?case by (fastforce simp:RedVar)
next
  case LAss thus ?case by(fastforce simp: LAssRedsVal)
next
  case LAssThrow thus ?case by(fastforce dest!:eval_final simp: LAssRedsThrow)
next
  case FAcc thus ?case by(fastforce intro:FAccRedsVal)
next
  case FAccNull thus ?case by(simp add:FAccRedsNull)
next
  case FAccThrow thus ?case by(fastforce dest!:eval_final simp:FAccRedsThrow)
next
  case FAss thus ?case by(fastforce simp:FAssRedsVal)
next
  case FAssNull thus ?case by(fastforce simp:FAssRedsNull)
next
  case FAssThrow1 thus ?case by(fastforce dest!:eval_final simp:FAssRedsThrow1)
next
  case FAssThrow2 thus ?case by(fastforce dest!:eval_final simp:FAssRedsThrow2)
next
  case CallObjThrow thus ?case by(fastforce dest!:eval_final simp:CallRedsThrowObj)
next
  case CallNull thus ?case thm CallRedsNull by(simp add:CallRedsNull)
next
  case CallParamsThrow thus ?case
    by(fastforce dest!:evals_final simp:CallRedsThrowParams)
next
  case (Call E e s\<^sub>0 a Cs s\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 C S M Ts' T' pns' body' Ds Ts T pns
             body Cs' vs' l\<^sub>2' new_body e' h\<^sub>3 l\<^sub>3)
  have IHe: "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s\<^sub>1\<rangle>"
    and IHes: "P,E \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
    and h\<^sub>2a: "h\<^sub>2 a = Some(C,S)"
    and "method": "P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds"
    and select: "P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'"
    and same_length: "length vs = length pns"
    and casts: "P \<turnstile> Ts Casts vs to vs'"
    and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Ref (a,Cs'), pns[\<mapsto>]vs']"
    and body_case: "new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body | _ \<Rightarrow> body)"
    and eval_body: "P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> 
                      \<langle>new_body,(h\<^sub>2, l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle>"
    and IHbody: "P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> 
                      \<langle>new_body,(h\<^sub>2, l\<^sub>2')\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle>" by fact+
  from wwf select same_length have lengthTs:"length Ts = length vs"
    by (fastforce dest!:select_method_wf_mdecl simp:wf_mdecl_def)
  show "P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>2)\<rangle>"
    using "method" select same_length l\<^sub>2' h\<^sub>2a casts body_case
      IHbody eval_final[OF eval_body]
    by(fastforce intro!:CallRedsFinal[OF wwf IHe IHes])
next
  case (StaticCall E e s\<^sub>0 a Cs s\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 C Cs'' M Ts T pns body Cs'
                   Ds vs' l\<^sub>2' e' h\<^sub>3 l\<^sub>3)
 have IHe: "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<rightarrow>* \<langle>ref(a,Cs),s\<^sub>1\<rangle>"
   and IHes: "P,E \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<rightarrow>]* \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
   and path_unique: "P \<turnstile> Path last Cs to C unique"
   and path_via: "P \<turnstile> Path last Cs to C via Cs''"
   and least: "P \<turnstile> C has least M = (Ts, T, pns, body) via Cs'"
   and Ds: "Ds = (Cs @\<^sub>p Cs'') @\<^sub>p Cs'"
   and same_length: "length vs = length pns"
   and casts: "P \<turnstile> Ts Casts vs to vs'"
   and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Ref (a,Ds), pns[\<mapsto>]vs']"
   and eval_body: "P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> 
                         \<langle>body,(h\<^sub>2, l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle>"
   and IHbody: "P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> 
                      \<langle>body,(h\<^sub>2, l\<^sub>2')\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle>" by fact+
 from wwf least same_length have lengthTs:"length Ts = length vs"
    by (fastforce dest!:has_least_wf_mdecl simp:wf_mdecl_def)
  show "P,E \<turnstile> \<langle>e\<bullet>(C::)M(ps),s\<^sub>0\<rangle> \<rightarrow>* \<langle>e',(h\<^sub>3, l\<^sub>2)\<rangle>"
    using path_unique path_via least Ds same_length l\<^sub>2' casts
      IHbody eval_final[OF eval_body]
    by(fastforce intro!:StaticCallRedsFinal[OF wwf IHe IHes])
next
  case Block with wwf show ?case by(fastforce simp: BlockRedsFinal dest:eval_final)
next
  case Seq thus ?case by(fastforce simp:SeqReds2)
next
  case SeqThrow thus ?case by(fastforce dest!:eval_final simp: SeqRedsThrow)
next
  case CondT thus ?case by(fastforce simp:CondReds2T)
next
  case CondF thus ?case by(fastforce simp:CondReds2F)
next
  case CondThrow thus ?case by(fastforce dest!:eval_final simp:CondRedsThrow)
next
  case WhileF thus ?case by(fastforce simp:WhileFReds)
next
  case WhileT thus ?case by(fastforce simp: WhileTReds)
next
  case WhileCondThrow thus ?case by(fastforce dest!:eval_final simp: WhileRedsThrow)
next
  case WhileBodyThrow thus ?case by(fastforce dest!:eval_final simp: WhileTRedsThrow)
next
  case Throw thus ?case by(fastforce simp:ThrowReds)
next
  case ThrowNull thus ?case by(fastforce simp:ThrowRedsNull)
next
  case ThrowThrow thus ?case by(fastforce dest!:eval_final simp:ThrowRedsThrow)
next
  case Nil thus ?case by simp
next
  case Cons thus ?case
    by(fastforce intro!:Cons_eq_appendI[OF refl refl] ListRedsVal)
next
  case ConsThrow thus ?case by(fastforce elim: ListReds1)
qed



subsection\<open>Big steps simulates small step\<close>


text \<open>The big step equivalent of \<open>RedWhile\<close>:\<close> 

lemma unfold_while: 
  "P,E \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>  =  P,E \<turnstile> \<langle>if(b) (c;;while(b) c) else (unit),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

proof
  assume "P,E \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  thus "P,E \<turnstile> \<langle>if (b) (c;; while (b) c) else unit,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    by cases (fastforce intro: eval_evals.intros)+
next
  assume "P,E \<turnstile> \<langle>if (b) (c;; while (b) c) else unit,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  thus "P,E \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
  proof (cases)
    fix ex
    assume e': "e' = throw ex"
    assume "P,E \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>throw ex,s'\<rangle>"  
    hence "P,E \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>throw ex,s'\<rangle>" by (rule WhileCondThrow)
    with e' show ?thesis by simp
  next
    fix s\<^sub>1
    assume eval_false: "P,E \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle>"
    and eval_unit: "P,E \<turnstile> \<langle>unit,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    with eval_unit have "s' = s\<^sub>1" "e' = unit" by (auto elim: eval_cases)
    moreover from eval_false have "P,E \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>unit,s\<^sub>1\<rangle>"
      by - (rule WhileF, simp)
    ultimately show ?thesis by simp
  next
    fix s\<^sub>1
    assume eval_true: "P,E \<turnstile> \<langle>b,s\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>"
    and eval_rest: "P,E \<turnstile> \<langle>c;; while (b) c,s\<^sub>1\<rangle>\<Rightarrow>\<langle>e',s'\<rangle>"
    from eval_rest show ?thesis
    proof (cases)
      fix s\<^sub>2 v\<^sub>1
      assume "P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>" "P,E \<turnstile> \<langle>while (b) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
      with eval_true show "P,E \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by (rule WhileT)
    next
      fix ex
      assume "P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw ex,s'\<rangle>" "e' = throw ex"
      with eval_true show "P,E \<turnstile> \<langle>while(b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
        by (iprover intro: WhileBodyThrow)
    qed
  qed
qed



lemma blocksEval:
  "\<And>Ts vs l l' E. \<lbrakk>size ps = size Ts; size ps = size vs; 
                    P,E \<turnstile> \<langle>blocks(ps,Ts,vs,e),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<rbrakk>
    \<Longrightarrow> \<exists> l'' vs'. P,E(ps [\<mapsto>] Ts) \<turnstile> \<langle>e,(h,l(ps[\<mapsto>]vs'))\<rangle> \<Rightarrow> \<langle>e',(h',l'')\<rangle> \<and>
                   P \<turnstile> Ts Casts vs to vs' \<and> length vs' = length vs"

proof (induct ps)
  case Nil then show ?case by(fastforce intro:Casts_Nil)
next
  case (Cons p ps')
  have length_eqs: "length (p # ps') = length Ts" 
                   "length (p # ps') = length vs"
    and IH:"\<And>Ts vs l l' E. \<lbrakk>length ps' = length Ts; length ps' = length vs;
                             P,E \<turnstile> \<langle>blocks (ps',Ts,vs,e),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>\<rbrakk>
  \<Longrightarrow> \<exists>l'' vs'. P,E(ps' [\<mapsto>] Ts) \<turnstile> \<langle>e,(h,l(ps' [\<mapsto>] vs'))\<rangle> \<Rightarrow> \<langle>e',(h', l'')\<rangle> \<and>
                P \<turnstile> Ts Casts vs to vs' \<and> length vs' = length vs" by fact+
  then obtain T Ts' where Ts: "Ts = T#Ts'" by (cases "Ts") simp
  obtain v vs' where vs: "vs = v#vs'" using length_eqs by (cases "vs") simp
  with length_eqs Ts have length1:"length ps' = length Ts'" 
    and length2:"length ps' = length vs'" by simp_all
  have "P,E \<turnstile> \<langle>blocks (p # ps', Ts, vs, e),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h', l')\<rangle>" by fact
  with Ts vs
  have blocks:"P,E \<turnstile> \<langle>{p:T := Val v; blocks (ps',Ts',vs',e)},(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>"
    by simp
  then obtain l''' v' where
    eval_ps': "P,E(p \<mapsto> T) \<turnstile> \<langle>blocks (ps',Ts',vs',e),(h,l(p\<mapsto>v'))\<rangle> \<Rightarrow> \<langle>e',(h',l''')\<rangle>"
    and l''': "l'=l'''(p:=l p)"
    and casts:"P \<turnstile> T casts v to v'"
    by(auto elim!: eval_cases simp:fun_upd_same)
  from IH[OF length1 length2 eval_ps'] obtain l'' vs'' where
    "P,E(p \<mapsto> T)(ps' [\<mapsto>] Ts') \<turnstile> \<langle>e,(h, l(p\<mapsto>v')(ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                                       \<langle>e',(h',l'')\<rangle>"
    and "P \<turnstile> Ts' Casts vs' to vs''"
    and "length vs'' = length vs'" by auto
  with Ts vs casts show ?case
    by -(rule_tac x="l''" in exI,rule_tac x="v'#vs''" in exI,simp,
         rule Casts_Cons)
qed



lemma CastblocksEval:
  "\<And>Ts vs l l' E. \<lbrakk>size ps = size Ts; size ps = size vs; 
                   P,E \<turnstile> \<langle>\<lparr>C'\<rparr>(blocks(ps,Ts,vs,e)),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<rbrakk>
    \<Longrightarrow> \<exists> l'' vs'. P,E(ps [\<mapsto>] Ts) \<turnstile> \<langle>\<lparr>C'\<rparr>e,(h,l(ps[\<mapsto>]vs'))\<rangle> \<Rightarrow> \<langle>e',(h',l'')\<rangle> \<and>
                   P \<turnstile> Ts Casts vs to vs' \<and> length vs' = length vs"

proof (induct ps)
  case Nil then show ?case by(fastforce intro:Casts_Nil)
next
  case (Cons p ps')
  have length_eqs: "length (p # ps') = length Ts" 
                   "length (p # ps') = length vs" by fact+
  then obtain T Ts' where Ts: "Ts = T#Ts'" by (cases "Ts") simp
  obtain v vs' where vs: "vs = v#vs'" using length_eqs by (cases "vs") simp
  with length_eqs Ts have length1:"length ps' = length Ts'" 
    and length2:"length ps' = length vs'" by simp_all
  have "P,E \<turnstile> \<langle>\<lparr>C'\<rparr>(blocks (p # ps', Ts, vs, e)),(h,l)\<rangle> \<Rightarrow> \<langle>e',(h', l')\<rangle>" by fact
  moreover
  { fix a Cs Cs'
    assume blocks:"P,E \<turnstile> \<langle>blocks(p#ps',Ts,vs,e),(h,l)\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h',l')\<rangle>"
      and path_via:"P \<turnstile> Path last Cs to C' via Cs'"
      and e':"e' = ref(a,Cs@\<^sub>pCs')"
    from blocks length_eqs obtain l'' vs''
      where eval:"P,E(p#ps' [\<mapsto>] Ts) \<turnstile> \<langle>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                                 \<langle>ref (a,Cs),(h',l'')\<rangle>"
      and casts:"P \<turnstile> Ts Casts vs to vs''"
      and length:"length vs'' = length vs"
      by -(drule blocksEval,auto)
    from eval path_via have 
      "P,E(p#ps'[\<mapsto>]Ts) \<turnstile> \<langle>\<lparr>C'\<rparr>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> \<langle>ref(a,Cs@\<^sub>pCs'),(h',l'')\<rangle>"
      by(auto intro:StaticUpCast)
    with e' casts length have ?case by simp blast }
  moreover
  { fix a Cs Cs'
    assume blocks:"P,E \<turnstile> \<langle>blocks(p#ps',Ts,vs,e),(h,l)\<rangle> \<Rightarrow> 
                         \<langle>ref (a,Cs@C'# Cs'),(h',l')\<rangle>"
      and e':"e' = ref (a,Cs@[C'])"
    from blocks length_eqs obtain l'' vs''
      where eval:"P,E(p#ps' [\<mapsto>] Ts) \<turnstile> \<langle>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                                 \<langle>ref (a,Cs@C'# Cs'),(h',l'')\<rangle>"
      and casts:"P \<turnstile> Ts Casts vs to vs''"
      and length:"length vs'' = length vs"
      by -(drule blocksEval,auto)
    from eval have "P,E(p#ps'[\<mapsto>]Ts) \<turnstile> \<langle>\<lparr>C'\<rparr>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                                             \<langle>ref(a,Cs@[C']),(h',l'')\<rangle>"
      by(auto intro:StaticDownCast)
    with e' casts length have ?case by simp blast }
  moreover
  { assume "P,E \<turnstile> \<langle>blocks(p#ps',Ts,vs,e),(h,l)\<rangle> \<Rightarrow> \<langle>null,(h',l')\<rangle>"
    and e':"e' = null"
    with length_eqs obtain l'' vs''
      where eval:"P,E(p#ps' [\<mapsto>] Ts) \<turnstile> \<langle>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                                 \<langle>null,(h',l'')\<rangle>"
      and casts:"P \<turnstile> Ts Casts vs to vs''"
      and length:"length vs'' = length vs"
      by -(drule blocksEval,auto)
    from eval have "P,E(p#ps' [\<mapsto>] Ts) \<turnstile> \<langle>\<lparr>C'\<rparr>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                                               \<langle>null,(h',l'')\<rangle>"
      by(auto intro:StaticCastNull)
    with e' casts length have ?case by simp blast }
  moreover
  { fix a Cs
    assume blocks:"P,E \<turnstile> \<langle>blocks(p#ps',Ts,vs,e),(h,l)\<rangle> \<Rightarrow> \<langle>ref (a,Cs),(h',l')\<rangle>"
      and notin:"C' \<notin> set Cs" and leq:"\<not> P \<turnstile> (last Cs) \<preceq>\<^sup>* C'"
      and  e':"e' = THROW ClassCast"
    from blocks length_eqs obtain l'' vs''
      where eval:"P,E(p#ps' [\<mapsto>] Ts) \<turnstile> \<langle>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                                 \<langle>ref (a,Cs),(h',l'')\<rangle>"
      and casts:"P \<turnstile> Ts Casts vs to vs''"
      and length:"length vs'' = length vs"
      by -(drule blocksEval,auto)
    from eval notin leq have 
      "P,E(p#ps'[\<mapsto>]Ts) \<turnstile> \<langle>\<lparr>C'\<rparr>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                          \<langle>THROW ClassCast,(h',l'')\<rangle>"
      by(auto intro:StaticCastFail)
    with e' casts length have ?case by simp blast }
  moreover
  { fix r assume "P,E \<turnstile> \<langle>blocks(p#ps',Ts,vs,e),(h,l)\<rangle> \<Rightarrow> \<langle>throw r,(h',l')\<rangle>"
    and e':"e' = throw r"
     with length_eqs obtain l'' vs''
      where eval:"P,E(p#ps' [\<mapsto>] Ts) \<turnstile> \<langle>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                                 \<langle>throw r,(h',l'')\<rangle>"
      and casts:"P \<turnstile> Ts Casts vs to vs''"
      and length:"length vs'' = length vs"
      by -(drule blocksEval,auto)
    from eval have 
      "P,E(p#ps'[\<mapsto>]Ts) \<turnstile> \<langle>\<lparr>C'\<rparr>e,(h,l(p#ps'[\<mapsto>]vs''))\<rangle> \<Rightarrow> 
                          \<langle>throw r,(h',l'')\<rangle>"
      by(auto intro:eval_evals.StaticCastThrow)
    with e' casts length have ?case by simp blast }
  ultimately show ?case
    by -(erule eval_cases,fastforce+)
qed



lemma
assumes wf: "wwf_prog P"
shows eval_restrict_lcl:
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>W. fv e \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>e,(h,l|`W)\<rangle> \<Rightarrow> \<langle>e',(h',l'|`W)\<rangle>)"
and "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>W. fvs es \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>es,(h,l|`W)\<rangle> [\<Rightarrow>] \<langle>es',(h',l'|`W)\<rangle>)"

proof(induct rule:eval_evals_inducts)
  case (Block E V T e\<^sub>0 h\<^sub>0 l\<^sub>0 e\<^sub>1 h\<^sub>1 l\<^sub>1)
  have IH: "\<And>W. fv e\<^sub>0 \<subseteq> W \<Longrightarrow> 
                 P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0(V:=None)|`W)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1|`W)\<rangle>" by fact
  (*have type:"is_type P T" .*)
  have "fv({V:T; e\<^sub>0}) \<subseteq> W" by fact
  hence "fv e\<^sub>0 - {V} \<subseteq> W" by simp_all
  hence "fv e\<^sub>0 \<subseteq> insert V W" by fast
  with IH[OF this]
  have "P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0, (l\<^sub>0|`W)(V := None))\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1, l\<^sub>1|`insert V W)\<rangle>"
    by fastforce
  from eval_evals.Block[OF this] show ?case by fastforce
next
  case Seq thus ?case by simp (blast intro:eval_evals.Seq)
next
  case New thus ?case by(simp add:eval_evals.intros)
next
  case NewFail thus ?case by(simp add:eval_evals.intros)
next
  case StaticUpCast thus ?case by simp (blast intro:eval_evals.StaticUpCast)
next
  case (StaticDownCast E e h l a Cs C Cs' h' l')
  have IH:"\<And>W. fv e \<subseteq> W \<Longrightarrow> 
                P,E \<turnstile> \<langle>e,(h,l |` W)\<rangle> \<Rightarrow> \<langle>ref(a,Cs@[C]@Cs'),(h',l' |` W)\<rangle>" by fact
  have "fv (\<lparr>C\<rparr>e) \<subseteq> W" by fact
  hence "fv e \<subseteq> W" by simp
  from IH[OF this] show ?case by(rule eval_evals.StaticDownCast)
next
  case StaticCastNull thus ?case by simp (blast intro:eval_evals.StaticCastNull)
next
  case StaticCastFail thus ?case by simp (blast intro:eval_evals.StaticCastFail)
next
  case StaticCastThrow thus ?case by(simp add:eval_evals.intros)
next
  case DynCast thus ?case by simp (blast intro:eval_evals.DynCast)
next
  case StaticUpDynCast thus ?case by simp (blast intro:eval_evals.StaticUpDynCast)
next
  case (StaticDownDynCast E e h l a Cs C Cs' h' l')
  have IH:"\<And>W. fv e \<subseteq> W \<Longrightarrow> 
                P,E \<turnstile> \<langle>e,(h,l |` W)\<rangle> \<Rightarrow> \<langle>ref(a,Cs@[C]@Cs'),(h',l' |` W)\<rangle>" by fact
  have "fv (Cast C e) \<subseteq> W" by fact
  hence "fv e \<subseteq> W" by simp
  from IH[OF this] show ?case by(rule eval_evals.StaticDownDynCast)
next
  case DynCastNull thus ?case by simp (blast intro:eval_evals.DynCastNull)
next
  case DynCastFail thus ?case by simp (blast intro:eval_evals.DynCastFail)
next
  case DynCastThrow thus ?case by(simp add:eval_evals.intros)
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
  case (LAss E e h\<^sub>0 l\<^sub>0 v h l V T v' l')
  have IH: "\<And>W. fv e \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0|`W)\<rangle> \<Rightarrow> \<langle>Val v,(h,l|`W)\<rangle>"
    and env:"E V = \<lfloor>T\<rfloor>" and casts:"P \<turnstile> T casts v to v'"
    and [simp]: "l' = l(V \<mapsto> v')" by fact+
  have "fv (V:=e) \<subseteq> W" by fact
  hence fv: "fv e \<subseteq> W" and VinW: "V \<in> W" by auto
  from eval_evals.LAss[OF IH[OF fv] _ casts] env VinW
  show ?case by fastforce
next
  case LAssThrow thus ?case by(fastforce intro: eval_evals.LAssThrow)
next
  case FAcc thus ?case by simp (blast intro: eval_evals.FAcc)
next
  case FAccNull thus ?case by(fastforce intro: eval_evals.FAccNull)
next
  case FAccThrow thus ?case by(fastforce intro: eval_evals.FAccThrow)
next
  case (FAss E e\<^sub>1 h l a Cs' h' l' e\<^sub>2 v h\<^sub>2 l\<^sub>2 D S F T Cs v' Ds fs fs' S' h\<^sub>2' W)
  have IH1: "\<And>W. fv e\<^sub>1 \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,(h, l|`W)\<rangle> \<Rightarrow> \<langle>ref (a, Cs'),(h', l'|`W)\<rangle>"
    and IH2: "\<And>W. fv e\<^sub>2 \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>2,(h', l'|`W)\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2, l\<^sub>2|`W)\<rangle>"
    and fv:"fv (e\<^sub>1\<bullet>F{Cs} := e\<^sub>2) \<subseteq> W"
    and h:"h\<^sub>2 a = Some(D,S)" and Ds:"Ds = Cs' @\<^sub>p Cs"
    and S:"(Ds,fs) \<in> S" and fs':"fs' = fs(F \<mapsto> v')"
    and S':"S' = S - {(Ds, fs)} \<union> {(Ds, fs')}" 
    and h':"h\<^sub>2' = h\<^sub>2(a \<mapsto> (D, S'))" 
    and field:"P \<turnstile> last Cs' has least F:T via Cs"
    and casts:"P \<turnstile> T casts v to v'" by fact+
  from fv have fv1:"fv e\<^sub>1 \<subseteq> W" and fv2:"fv e\<^sub>2 \<subseteq> W" by auto
  from eval_evals.FAss[OF IH1[OF fv1] IH2[OF fv2] _ field casts] h Ds S fs' S' h'
  show ?case by simp
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
  case (Call E e h\<^sub>0 l\<^sub>0 a Cs h\<^sub>1 l\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 C S M Ts' T' pns'
             body' Ds Ts T pns body Cs' vs' l\<^sub>2' new_body e' h\<^sub>3 l\<^sub>3 W)
  have IHe: "\<And>W. fv e \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0|`W)\<rangle> \<Rightarrow> \<langle>ref(a,Cs),(h\<^sub>1,l\<^sub>1|`W)\<rangle>"
    and IHps: "\<And>W. fvs ps \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>ps,(h\<^sub>1,l\<^sub>1|`W)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2|`W)\<rangle>"
    and IHbd: "\<And>W. fv new_body \<subseteq> W \<Longrightarrow> P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> 
                                    \<langle>new_body,(h\<^sub>2,l\<^sub>2'|`W)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3|`W)\<rangle>"
    and h\<^sub>2a: "h\<^sub>2 a = Some (C,S)"
    and "method": "P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds"
    and select:"P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'"
    and same_len: "size vs = size pns"
    and casts:"P \<turnstile> Ts Casts vs to vs'"
    and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Ref(a,Cs'), pns [\<mapsto>] vs']"
    and body_case: "new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body | _ \<Rightarrow> body)" by fact+
  have "fv (e\<bullet>M(ps)) \<subseteq> W" by fact
  hence fve: "fv e \<subseteq> W" and fvps: "fvs(ps) \<subseteq> W" by auto
  have wfmethod: "size Ts = size pns \<and> this \<notin> set pns" and
       fvbd: "fv body \<subseteq> {this} \<union> set pns"
    using select wf by(fastforce dest!:select_method_wf_mdecl simp:wf_mdecl_def)+
  from fvbd body_case have fvbd':"fv new_body \<subseteq> {this} \<union> set pns"
    by(cases T') auto
  from l\<^sub>2' have "l\<^sub>2' |` ({this} \<union> set pns) = [this \<mapsto> Ref (a, Cs'), pns [\<mapsto>] vs']"
    by (auto intro!:ext simp:restrict_map_def fun_upd_def)
  with eval_evals.Call[OF IHe[OF fve] IHps[OF fvps] _ "method" select same_len
                          casts _ body_case IHbd[OF fvbd']] h\<^sub>2a
  show ?case by simp
next
  case (StaticCall E e h\<^sub>0 l\<^sub>0 a Cs h\<^sub>1 l\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 C Cs'' M Ts T pns body
                   Cs' Ds vs' l\<^sub>2' e' h\<^sub>3 l\<^sub>3 W)
  have IHe: "\<And>W. fv e \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0|`W)\<rangle> \<Rightarrow> \<langle>ref(a,Cs),(h\<^sub>1,l\<^sub>1|`W)\<rangle>"
    and IHps: "\<And>W. fvs ps \<subseteq> W \<Longrightarrow> P,E \<turnstile> \<langle>ps,(h\<^sub>1,l\<^sub>1|`W)\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2|`W)\<rangle>"
    and IHbd: "\<And>W. fv body \<subseteq> W \<Longrightarrow> P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> 
                                    \<langle>body,(h\<^sub>2,l\<^sub>2'|`W)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3|`W)\<rangle>"
    and path_unique: "P \<turnstile> Path last Cs to C unique"
    and path_via: "P \<turnstile> Path last Cs to C via Cs''"
    and least: "P \<turnstile> C has least M = (Ts, T, pns, body) via Cs'"
    and Ds: "Ds = (Cs @\<^sub>p Cs'') @\<^sub>p Cs'"
    and same_len: "size vs = size pns"
    and casts:"P \<turnstile> Ts Casts vs to vs'"
    and l\<^sub>2': "l\<^sub>2' = [this \<mapsto> Ref(a,Ds), pns [\<mapsto>] vs']" by fact+
  have "fv (e\<bullet>(C::)M(ps)) \<subseteq> W" by fact
  hence fve: "fv e \<subseteq> W" and fvps: "fvs(ps) \<subseteq> W" by auto
  have wfmethod: "size Ts = size pns \<and> this \<notin> set pns" and
       fvbd: "fv body \<subseteq> {this} \<union> set pns"
    using least wf by(fastforce dest!:has_least_wf_mdecl simp:wf_mdecl_def)+
  from fvbd have fvbd':"fv body \<subseteq> {this} \<union> set pns"
    by auto
  from l\<^sub>2' have "l\<^sub>2' |` ({this} \<union> set pns) = [this \<mapsto> Ref(a,Ds), pns [\<mapsto>] vs']"
    by (auto intro!:ext simp:restrict_map_def fun_upd_def)
  with eval_evals.StaticCall[OF IHe[OF fve] IHps[OF fvps] path_unique path_via
                                least Ds same_len casts _ IHbd[OF fvbd']]
  show ?case by simp
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
  case Nil thus ?case by (simp add: eval_evals.Nil)
next
  case Cons thus ?case by simp (blast intro: eval_evals.Cons)
next
  case ConsThrow thus ?case by simp (blast intro: eval_evals.ConsThrow)
qed



lemma eval_notfree_unchanged:
assumes wf:"wwf_prog P"
shows "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>V. V \<notin> fv e \<Longrightarrow> l' V = l V)"
and "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<Rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>V. V \<notin> fvs es \<Longrightarrow> l' V = l V)"

proof(induct rule:eval_evals_inducts)
  case LAss thus ?case by(simp add:fun_upd_apply)
next
  case Block thus ?case
    by (simp only:fun_upd_apply split:if_splits) fastforce
qed simp_all



lemma eval_closed_lcl_unchanged:
  assumes wf:"wwf_prog P"
  and eval:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<Rightarrow> \<langle>e',(h',l')\<rangle>"
  and fv:"fv e = {}"
  shows "l' = l"

proof -
  from wf eval have "\<And>V. V \<notin> fv e \<Longrightarrow> l' V = l V" by (rule eval_notfree_unchanged)
  with fv have "\<And>V. l' V = l V" by simp
  thus ?thesis by(simp add:fun_eq_iff)
qed



(* Hiermit kann man die ganze pair-Splitterei in den automatischen Taktiken
abschalten. Wieder anschalten siehe nach dem Beweis. *)

declare split_paired_All [simp del] split_paired_Ex [simp del]

declaration \<open>K (Simplifier.map_ss (fn ss => ss delloop "split_all_tac"))\<close>
setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac")\<close>


lemma list_eval_Throw: 
assumes eval_e: "P,E \<turnstile> \<langle>throw x,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "P,E \<turnstile> \<langle>map Val vs @ throw x # es',s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"

proof -
  from eval_e 
  obtain a where e': "e' = Throw a"
    by (cases) (auto dest!: eval_final)
  {
    fix es
    have "\<And>vs. es = map Val vs @ throw x # es' 
           \<Longrightarrow> P,E \<turnstile> \<langle>es,s\<rangle>[\<Rightarrow>]\<langle>map Val vs @ e' # es',s'\<rangle>"
    proof (induct es type: list)
      case Nil thus ?case by simp
    next
      case (Cons e es vs)
      have e_es: "e # es = map Val vs @ throw x # es'" by fact
      show "P,E \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"
      proof (cases vs)
        case Nil
        with e_es obtain "e=throw x" "es=es'" by simp
        moreover from eval_e e'
        have "P,E \<turnstile> \<langle>throw x # es,s\<rangle> [\<Rightarrow>] \<langle>Throw a # es,s'\<rangle>"
          by (iprover intro: ConsThrow)
        ultimately show ?thesis using Nil e' by simp
      next
        case (Cons v vs')
        have vs: "vs = v # vs'" by fact
        with e_es obtain 
          e: "e=Val v" and es:"es= map Val vs' @ throw x # es'"
          by simp
        from e 
        have "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"
          by (iprover intro: eval_evals.Val)
        moreover from es 
        have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs' @ e' # es',s'\<rangle>"
          by (rule Cons.hyps)
        ultimately show 
          "P,E \<turnstile> \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ e' # es',s'\<rangle>"
          using vs by (auto intro: eval_evals.Cons)
      qed
    qed
  }
  thus ?thesis
    by simp
qed




text \<open>The key lemma:\<close>

lemma
assumes wf: "wwf_prog P"
shows extend_1_eval:
  "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e'',s''\<rangle> \<Longrightarrow>  (\<And>s' e'. P,E \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>)"
and extend_1_evals:
  "P,E \<turnstile> \<langle>es,t\<rangle> [\<rightarrow>] \<langle>es'',t''\<rangle> \<Longrightarrow> (\<And>t' es'. P,E \<turnstile> \<langle>es'',t''\<rangle> [\<Rightarrow>] \<langle>es',t'\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>es,t\<rangle> [\<Rightarrow>] \<langle>es',t'\<rangle>)"

proof (induct rule: red_reds.inducts)
 case RedNew thus ?case by (iprover elim: eval_cases intro: eval_evals.intros)
next
  case RedNewFail thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (StaticCastRed E e s e'' s'' C s' e') thus ?case
    by -(erule eval_cases,auto intro:eval_evals.intros,
         subgoal_tac "P,E \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>ref(a,Cs@[C]@Cs'),s'\<rangle>",
         rule_tac Cs'="Cs'" in StaticDownCast,auto)
next
  case RedStaticCastNull thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedStaticUpCast thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedStaticDownCast thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedStaticCastFail thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedStaticUpDynCast thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedStaticDownDynCast thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (DynCastRed E e s e'' s'' C s' e')
  have eval:"P,E \<turnstile> \<langle>Cast C e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    and IH:"\<And>ex sx. P,E \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle>" by fact+
  moreover 
  { fix Cs Cs' a
    assume "P,E \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>ref (a, Cs @ C # Cs'),s'\<rangle>"
    from IH[OF this] have "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>ref (a, Cs@[C]@Cs'),s'\<rangle>" by simp
    hence "P,E \<turnstile> \<langle>Cast C e,s\<rangle> \<Rightarrow> \<langle>ref (a, Cs@[C]),s'\<rangle>" by(rule StaticDownDynCast) }
  ultimately show ?case by -(erule eval_cases,auto intro: eval_evals.intros)
next
  case RedDynCastNull thus ?case by (iprover elim:eval_cases intro:eval_evals.intros)
next
  case (RedDynCast s a D S C Cs' E Cs s' e')
  thus ?case by (cases s)(auto elim!:eval_cases intro:eval_evals.intros)
next
  case (RedDynCastFail s a D S C Cs E s'' e'')
  thus ?case by (cases s)(auto elim!: eval_cases intro: eval_evals.intros)
next
  case BinOpRed1 thus ?case by -(erule eval_cases,auto intro: eval_evals.intros)
next
  case BinOpRed2 
  thus ?case by (fastforce elim!:eval_cases intro:eval_evals.intros eval_finalId)
next
  case RedBinOp thus ?case by (iprover elim:eval_cases intro:eval_evals.intros)
next
  case (RedVar s V v E s' e')
  thus ?case by (cases s)(fastforce elim:eval_cases intro:eval_evals.intros)
next
  case LAssRed thus ?case by -(erule eval_cases,auto intro:eval_evals.intros)
next
  case RedLAss
  thus ?case by (fastforce elim:eval_cases intro:eval_evals.intros)
next
  case FAccRed thus ?case by -(erule eval_cases,auto intro:eval_evals.intros)
next
  case (RedFAcc s a D S Ds Cs' Cs fs F v E s' e')
  thus ?case by (cases s)(fastforce elim:eval_cases intro:eval_evals.intros)
next
  case RedFAccNull thus ?case by (fastforce elim!:eval_cases intro:eval_evals.intros)
next
  case (FAssRed1 E e\<^sub>1 s e\<^sub>1' s'' F Cs e\<^sub>2 s' e')
  have eval:"P,E \<turnstile> \<langle>e\<^sub>1'\<bullet>F{Cs} := e\<^sub>2,s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    and IH:"\<And>ex sx. P,E \<turnstile> \<langle>e\<^sub>1',s''\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,s\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle>" by fact+
  { fix Cs' D S T a fs h\<^sub>2 l\<^sub>2 s\<^sub>1 v v'
    assume ref:"P,E \<turnstile> \<langle>e\<^sub>1',s''\<rangle> \<Rightarrow> \<langle>ref (a, Cs'),s\<^sub>1\<rangle>" 
      and rest:"P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2, l\<^sub>2)\<rangle>" "h\<^sub>2 a = \<lfloor>(D, S)\<rfloor>" 
      "P \<turnstile> last Cs' has least F:T via Cs" "P \<turnstile> T casts v to v'"
      "(Cs' @\<^sub>p Cs, fs) \<in> S"
    from IH[OF ref] have "P,E \<turnstile> \<langle>e\<^sub>1,s\<rangle> \<Rightarrow> \<langle>ref (a, Cs'),s\<^sub>1\<rangle>" .
    with rest have "P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs} := e\<^sub>2,s\<rangle> \<Rightarrow>
          \<langle>Val v',(h\<^sub>2(a \<mapsto> (D,insert (Cs'@\<^sub>pCs,fs(F \<mapsto> v'))(S - {(Cs'@\<^sub>pCs,fs)}))),l\<^sub>2)\<rangle>"
      by-(rule FAss,simp_all) }
  moreover
  { fix s\<^sub>1 v 
    assume null:"P,E \<turnstile> \<langle>e\<^sub>1',s''\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>" 
      and rest:"P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,s'\<rangle>"
    from IH[OF null] have "P,E \<turnstile> \<langle>e\<^sub>1,s\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>" .
    with rest have "P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs} := e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s'\<rangle>"
      by-(rule FAssNull,simp_all) }
  moreover
  { fix e' assume throw:"P,E \<turnstile> \<langle>e\<^sub>1',s''\<rangle> \<Rightarrow> \<langle>throw e',s'\<rangle>"
    from IH[OF throw] have "P,E \<turnstile> \<langle>e\<^sub>1,s\<rangle> \<Rightarrow> \<langle>throw e',s'\<rangle>" .
    hence "P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs} := e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw e',s'\<rangle>"
      by-(rule eval_evals.FAssThrow1,simp_all) }
  moreover
  { fix e' s\<^sub>1 v
    assume val:"P,E \<turnstile> \<langle>e\<^sub>1',s''\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>"
      and rest:"P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s'\<rangle>"
    from IH[OF val] have "P,E \<turnstile> \<langle>e\<^sub>1,s\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>" .
    with rest have "P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs} := e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw e',s'\<rangle>"
      by-(rule eval_evals.FAssThrow2,simp_all) }
  ultimately show ?case using eval
    by -(erule eval_cases,auto)
next
  case (FAssRed2 E e\<^sub>2 s e\<^sub>2' s'' v F Cs s' e')
  have eval:"P,E \<turnstile> \<langle>Val v\<bullet>F{Cs} := e\<^sub>2',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    and IH:"\<And>ex sx. P,E \<turnstile> \<langle>e\<^sub>2',s''\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle>" by fact+
  { fix Cs' D S T a fs h\<^sub>2 l\<^sub>2 s\<^sub>1 v' v''
    assume val1:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),s\<^sub>1\<rangle>"
      and val2:"P,E \<turnstile> \<langle>e\<^sub>2',s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v',(h\<^sub>2, l\<^sub>2)\<rangle>"
      and rest:"h\<^sub>2 a = \<lfloor>(D, S)\<rfloor>" "P \<turnstile> last Cs' has least F:T via Cs"
               "P \<turnstile> T casts v' to v''" "(Cs'@\<^sub>pCs,fs) \<in> S"
    from val1 have s'':"s\<^sub>1 = s''" by -(erule eval_cases)
    with val1 have "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>ref (a,Cs'),s\<rangle>"
      by(fastforce elim:eval_cases intro:eval_finalId)
    also from IH[OF val2[simplified s'']] have "P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>Val v',(h\<^sub>2, l\<^sub>2)\<rangle>" .
    ultimately have "P,E \<turnstile> \<langle>Val v\<bullet>F{Cs} := e\<^sub>2,s\<rangle> \<Rightarrow>
           \<langle>Val v'',(h\<^sub>2(a\<mapsto>(D,insert(Cs'@\<^sub>pCs,fs(F \<mapsto> v''))(S - {(Cs'@\<^sub>pCs,fs)}))),l\<^sub>2)\<rangle>"
      using rest by -(rule FAss,simp_all) }
  moreover
  { fix s\<^sub>1 v'
    assume val1:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"
      and val2:"P,E \<turnstile> \<langle>e\<^sub>2',s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v',s'\<rangle>"
    from val1 have s'':"s\<^sub>1 = s''" by -(erule eval_cases)
    with val1 have "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
      by(fastforce elim:eval_cases intro:eval_finalId)
    also from IH[OF val2[simplified s'']] have "P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>Val v',s'\<rangle>" .
    ultimately have "P,E \<turnstile> \<langle>Val v\<bullet>F{Cs} := e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s'\<rangle>"
      by -(rule FAssNull,simp_all) }
  moreover
  { fix r assume val:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>throw r,s'\<rangle>"
    hence s'':"s'' = s'" by -(erule eval_cases,simp)
    with val have "P,E \<turnstile> \<langle>Val v\<bullet>F{Cs} := e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw r,s'\<rangle>" 
      by -(rule eval_evals.FAssThrow1,erule eval_cases,simp) }
  moreover
  { fix r s\<^sub>1 v'
    assume val1:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>Val v',s\<^sub>1\<rangle>"
      and val2:"P,E \<turnstile> \<langle>e\<^sub>2',s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw r,s'\<rangle>"
    from val1 have s'':"s\<^sub>1 = s''" by -(erule eval_cases)
    with val1 have "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v',s\<rangle>"
      by(fastforce elim:eval_cases intro:eval_finalId)
    also from IH[OF val2[simplified s'']] have "P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw r,s'\<rangle>" .
    ultimately have "P,E \<turnstile> \<langle>Val v\<bullet>F{Cs} := e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw r,s'\<rangle>" 
      by -(rule eval_evals.FAssThrow2,simp_all) }
  ultimately show ?case using eval
    by -(erule eval_cases,auto)
next
  case (RedFAss h a D S Cs' F T Cs v v' Ds fs E l s' e')
  have val:"P,E \<turnstile> \<langle>Val v',(h(a \<mapsto> (D,insert (Ds,fs(F \<mapsto> v'))(S - {(Ds,fs)}))),l)\<rangle> \<Rightarrow> 
                  \<langle>e',s'\<rangle>"
    and rest:"h a = \<lfloor>(D, S)\<rfloor>" "P \<turnstile> last Cs' has least F:T via Cs"
             "P \<turnstile> T casts v to v'" "Ds = Cs' @\<^sub>p Cs" "(Ds, fs) \<in> S" by fact+
  from val have "s' = (h(a \<mapsto> (D,insert (Ds,fs(F \<mapsto> v')) (S - {(Ds,fs)}))),l)"
    and "e' = Val v'" by -(erule eval_cases,simp_all)+
  with rest show ?case apply simp
    by(rule FAss,simp_all)(rule eval_finalId,simp)+
next
  case RedFAssNull
  thus ?case by (fastforce elim!: eval_cases intro: eval_evals.intros)
next
  case (CallObj E e s e' s' Copt M es s'' e'')
  thus ?case
    apply -
    apply(cases Copt,simp)
    by(erule eval_cases,auto intro:eval_evals.intros)+
next
  case (CallParams E es s es' s'' v Copt M s' e')
  have call:"P,E \<turnstile> \<langle>Call (Val v) Copt M es',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    and IH:"\<And>esx sx. P,E \<turnstile> \<langle>es',s''\<rangle> [\<Rightarrow>] \<langle>esx,sx\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>esx,sx\<rangle>" by fact+
  show ?case
    proof(cases Copt)
    case None with call have eval:"P,E \<turnstile> \<langle>Val v\<bullet>M(es'),s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by simp
    from eval show ?thesis
    proof(rule eval_cases)
      fix r assume "P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>throw r,s'\<rangle>" "e' = throw r"
      with None show "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
        by(fastforce elim:eval_cases)
    next
      fix es'' r sx v' vs
      assume val:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>Val v',sx\<rangle>"
        and evals:"P,E \<turnstile> \<langle>es',sx\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw r # es'',s'\<rangle>"
        and e':"e' = throw r"
      have val':"P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by(rule Val)
      from val have eq:"v' = v \<and> s'' = sx" by -(erule eval_cases,simp)
      with IH evals have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw r # es'',s'\<rangle>"
        by simp
      with eq CallParamsThrow[OF val'] e' None
      show "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
        by fastforce
    next
      fix C Cs Cs' Ds S T T' Ts Ts' a body body' h\<^sub>2 h\<^sub>3 l\<^sub>2 l\<^sub>3 pns pns' s\<^sub>1 vs vs'
      assume val:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<^sub>1\<rangle>"
        and evals:"P,E \<turnstile> \<langle>es',s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
        and hp:"h\<^sub>2 a = Some(C, S)"
        and "method":"P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds"
        and select:"P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'"
        and length:"length vs = length pns"
        and casts:"P \<turnstile> Ts Casts vs to vs'"
        and body:"P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> 
    \<langle>case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body | _ \<Rightarrow> body,(h\<^sub>2,[this \<mapsto> Ref(a,Cs'),pns [\<mapsto>] vs'])\<rangle>
        \<Rightarrow> \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle>"
        and s':"s' = (h\<^sub>3, l\<^sub>2)"
      from val have val':"P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<rangle>"
        and eq:"s'' = s\<^sub>1 \<and> v = Ref(a,Cs)"
        by(auto elim:eval_cases intro:Val)
      from body obtain new_body 
        where body_case:"new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body | _ \<Rightarrow> body)"
        and body':"P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> 
        \<langle>new_body,(h\<^sub>2,[this \<mapsto> Ref(a,Cs'),pns [\<mapsto>] vs'])\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle>"
        by simp
      from eq IH evals have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>" by simp
      with eq Call[OF val' _ _ "method" select length casts _ body_case] 
           hp body' s' None
      show "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fastforce
    next
      fix s\<^sub>1 vs
      assume val:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"
        and evals:"P,E \<turnstile> \<langle>es',s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s'\<rangle>"
        and e':"e' = THROW NullPointer"
      from val have val':"P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
        and eq:"s'' = s\<^sub>1 \<and> v = Null"
        by(auto elim:eval_cases intro:Val)
      from eq IH evals have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,s'\<rangle>" by simp
      with eq CallNull[OF val'] e' None
      show "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fastforce
    qed
  next
    case (Some C) with call have eval:"P,E \<turnstile> \<langle>Val v\<bullet>(C::)M(es'),s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
      by simp
    from eval show ?thesis
    proof(rule eval_cases)
      fix r assume "P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>throw r,s'\<rangle>" "e' = throw r"
      with Some show "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
        by(fastforce elim:eval_cases)
    next
      fix es'' r sx v' vs
      assume val:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>Val v',sx\<rangle>"
        and evals:"P,E \<turnstile> \<langle>es',sx\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw r # es'',s'\<rangle>"
        and e':"e' = throw r"
      have val':"P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by(rule Val)
      from val have eq:"v' = v \<and> s'' = sx" by -(erule eval_cases,simp)
      with IH evals have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw r # es'',s'\<rangle>"
        by simp
      with eq CallParamsThrow[OF val'] e' Some
      show "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
        by fastforce
    next
      fix Cs Cs' Cs'' T Ts a body h\<^sub>2 h\<^sub>3 l\<^sub>2 l\<^sub>3 pns s\<^sub>1 vs vs'
      assume val:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>ref (a,Cs),s\<^sub>1\<rangle>"
        and evals:"P,E \<turnstile> \<langle>es',s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
        and path_unique:"P \<turnstile> Path last Cs to C unique"
        and path_via:"P \<turnstile> Path last Cs to C via Cs''"
        and least:"P \<turnstile> C has least M = (Ts, T, pns, body) via Cs'"
        and length:"length vs = length pns"
        and casts:"P \<turnstile> Ts Casts vs to vs'"
        and body:"P,E(this \<mapsto> Class (last ((Cs @\<^sub>p Cs'') @\<^sub>p Cs')), pns [\<mapsto>] Ts) \<turnstile> 
           \<langle>body,(h\<^sub>2,[this \<mapsto> Ref(a,(Cs@\<^sub>pCs'')@\<^sub>pCs'),pns [\<mapsto>] vs'])\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle>"
        and s':"s' = (h\<^sub>3,l\<^sub>2)"
      from val have val':"P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<rangle>"
        and eq:"s'' = s\<^sub>1 \<and> v = Ref(a,Cs)"
        by(auto elim:eval_cases intro:Val)
      from eq IH evals have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>" by simp
      with eq StaticCall[OF val' _ path_unique path_via least _ _ casts _ body] 
           length s' Some
      show "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fastforce
    next
      fix s\<^sub>1 vs
      assume val:"P,E \<turnstile> \<langle>Val v,s''\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"
        and evals:"P,E \<turnstile> \<langle>es',s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s'\<rangle>"
        and e':"e' = THROW NullPointer"
      from val have val':"P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
        and eq:"s'' = s\<^sub>1 \<and> v = Null"
        by(auto elim:eval_cases intro:Val)
      from eq IH evals have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,s'\<rangle>" by simp
      with eq CallNull[OF val'] e' Some
      show "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
        by fastforce
    qed
  qed
next
  case (RedCall s a C S Cs M Ts' T' pns' body' Ds Ts T pns body Cs' vs
                bs new_body E s' e')
  obtain h l where "s' = (h,l)" by(cases s') auto
  have "P,E \<turnstile> \<langle>ref(a,Cs),s\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<rangle>" by (rule eval_evals.intros)
  moreover
  have finals: "finals(map Val vs)" by simp
  obtain h\<^sub>2 l\<^sub>2 where s: "s = (h\<^sub>2,l\<^sub>2)" by (cases s)
  with finals have "P,E \<turnstile> \<langle>map Val vs,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
    by (iprover intro: eval_finalsId)
  moreover from s have h\<^sub>2a:"h\<^sub>2 a = Some (C,S)" using RedCall by simp
  moreover have "method": "P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds" by fact
  moreover have select:"P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'" by fact
  moreover have blocks:"bs = blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body)" by fact
  moreover have body_case:"new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>bs | _ \<Rightarrow> bs)" by fact
  moreover have same_len\<^sub>1: "length Ts = length pns"
   and this_distinct: "this \<notin> set pns" and fv: "fv body \<subseteq> {this} \<union> set pns"
    using select wf by (fastforce dest!:select_method_wf_mdecl simp:wf_mdecl_def)+
  have same_len: "length vs = length pns" by fact
  moreover
  obtain h\<^sub>3 l\<^sub>3 where s': "s' = (h\<^sub>3,l\<^sub>3)" by (cases s')
  have eval_blocks:"P,E \<turnstile> \<langle>new_body,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  hence id: "l\<^sub>3 = l\<^sub>2" using fv s s' same_len\<^sub>1 same_len wf blocks body_case
    by(cases T')(auto elim!: eval_closed_lcl_unchanged)
  from same_len\<^sub>1 have same_len':"length(this#pns) = length(Class (last Cs')#Ts)" 
    by simp
  from same_len\<^sub>1 same_len
  have same_len\<^sub>2:"length(this#pns) = length(Ref(a,Cs')#vs)" by simp
  from eval_blocks
  have eval_blocks':"P,E \<turnstile> \<langle>new_body,(h\<^sub>2,l\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle>" using s s' by simp
  have casts_unique:"\<And>vs'. P \<turnstile> Class (last Cs')#Ts Casts Ref(a,Cs')#vs to vs'
                            \<Longrightarrow> vs' = Ref(a,Cs')#tl vs'"
    using wf
    by -(erule Casts_to.cases,auto elim!:casts_to.cases dest!:mdc_eq_last
                                      simp:path_via_def appendPath_def)
  have "\<exists>l'' vs' new_body'. P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> 
              \<langle>new_body',(h\<^sub>2,l\<^sub>2(this # pns[\<mapsto>]Ref(a,Cs')#vs'))\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l'')\<rangle> \<and> 
     P \<turnstile> Class(last Cs')#Ts Casts Ref(a,Cs')#vs to Ref(a,Cs')#vs' \<and>
     length vs' = length vs \<and> fv new_body' \<subseteq> {this} \<union> set pns \<and>
     new_body' = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body  | _  \<Rightarrow> body)"
  proof(cases "\<forall>C. T' \<noteq> Class C")
    case True
    with same_len' same_len\<^sub>2 eval_blocks' casts_unique body_case blocks
    obtain l'' vs'
      where body:"P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> 
                    \<langle>body,(h\<^sub>2,l\<^sub>2(this # pns[\<mapsto>]Ref(a,Cs')#vs'))\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l'')\<rangle>"
      and casts:"P \<turnstile> Class(last Cs')#Ts Casts Ref(a,Cs')#vs to Ref(a,Cs')#vs'"
      and lengthvs':"length vs' = length vs"
      by -(drule_tac vs="Ref(a,Cs')#vs" in blocksEval,assumption,cases T',
           auto simp:length_Suc_conv,blast)
    with fv True show ?thesis by(cases T') auto
  next
    case False
    then obtain D where T':"T' = Class D" by auto
    with same_len' same_len\<^sub>2 eval_blocks' casts_unique body_case blocks
    obtain l'' vs'
      where body:"P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> 
                    \<langle>\<lparr>D\<rparr>body,(h\<^sub>2,l\<^sub>2(this # pns[\<mapsto>]Ref(a,Cs')#vs'))\<rangle> \<Rightarrow> 
                    \<langle>e',(h\<^sub>3, l'')\<rangle>"
      and casts:"P \<turnstile> Class(last Cs')#Ts Casts Ref(a,Cs')#vs to Ref(a,Cs')#vs'"
      and lengthvs':"length vs' = length vs"
      by - (drule_tac vs="Ref(a,Cs')#vs" in CastblocksEval,
            assumption,simp,clarsimp simp:length_Suc_conv,auto)
    from fv have "fv (\<lparr>D\<rparr>body) \<subseteq> {this} \<union> set pns"
      by simp
    with body casts lengthvs' T' show ?thesis by auto
  qed
  then obtain l'' vs' new_body'
    where body:"P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> 
               \<langle>new_body',(h\<^sub>2,l\<^sub>2(this # pns[\<mapsto>]Ref(a,Cs')#vs'))\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l'')\<rangle>"
    and casts:"P \<turnstile> Class(last Cs')#Ts Casts Ref(a,Cs')#vs to Ref(a,Cs')#vs'"
    and lengthvs':"length vs' = length vs"
    and body_case':"new_body' = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body  | _ \<Rightarrow> body)"
    and fv':"fv new_body' \<subseteq> {this} \<union> set pns"
    by auto
  from same_len\<^sub>2 lengthvs'
  have same_len\<^sub>3:"length (this # pns) = length (Ref (a, Cs') # vs')" by simp
  from restrict_map_upds[OF same_len\<^sub>3,of "set(this#pns)" "l\<^sub>2"]
  have "l\<^sub>2(this # pns[\<mapsto>]Ref(a,Cs')#vs')|`(set(this#pns)) = 
          [this # pns[\<mapsto>]Ref(a,Cs')#vs']" by simp
  with eval_restrict_lcl[OF wf body fv'] this_distinct same_len\<^sub>1 same_len
  have "P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> 
   \<langle>new_body',(h\<^sub>2,[this # pns[\<mapsto>]Ref(a,Cs')#vs'])\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l''|`(set(this#pns)))\<rangle>"
    by simp
  with casts obtain l\<^sub>2' l\<^sub>3' vs' where
        "P \<turnstile> Ts Casts vs to vs'"
    and "P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> 
                                      \<langle>new_body',(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3')\<rangle>"
    and "l\<^sub>2' = [this\<mapsto>Ref(a,Cs'),pns[\<mapsto>]vs']"
    by(auto elim:Casts_to.cases)
  ultimately have "P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>M(map Val vs),s\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>"
    using body_case'
    by -(rule Call,simp_all)
  with s' id show ?case by simp
next
  case (RedStaticCall Cs C Cs'' M Ts T pns body Cs' Ds vs E a s s' e')
  have "P,E \<turnstile> \<langle>ref(a,Cs),s\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<rangle>" by (rule eval_evals.intros)
  moreover
  have finals: "finals(map Val vs)" by simp
  obtain h\<^sub>2 l\<^sub>2 where s: "s = (h\<^sub>2,l\<^sub>2)" by (cases s)
  with finals have "P,E \<turnstile> \<langle>map Val vs,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>"
    by (iprover intro: eval_finalsId)
  moreover have path_unique:"P \<turnstile> Path last Cs to C unique" by fact
  moreover have path_via:"P \<turnstile> Path last Cs to C via Cs''" by fact
  moreover have least:"P \<turnstile> C has least M = (Ts, T, pns, body) via Cs'" by fact
  moreover have same_len\<^sub>1: "length Ts = length pns"
   and this_distinct: "this \<notin> set pns" and fv: "fv body \<subseteq> {this} \<union> set pns"
    using least wf by (fastforce dest!:has_least_wf_mdecl simp:wf_mdecl_def)+
  moreover have same_len:"length vs = length pns" by fact
  moreover have Ds:"Ds = (Cs @\<^sub>p Cs'') @\<^sub>p Cs'" by fact
  moreover
  obtain h\<^sub>3 l\<^sub>3 where s': "s' = (h\<^sub>3,l\<^sub>3)" by (cases s')
  have eval_blocks:"P,E \<turnstile> \<langle>blocks(this#pns,Class(last Ds)#Ts,Ref(a,Ds)#vs,body),s\<rangle>
                       \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  hence id: "l\<^sub>3 = l\<^sub>2" using fv s s' same_len\<^sub>1 same_len wf
    by(auto elim!: eval_closed_lcl_unchanged)
  from same_len\<^sub>1 have same_len':"length(this#pns) = length(Class (last Ds)#Ts)"
    by simp
  from same_len\<^sub>1 same_len
  have same_len\<^sub>2:"length(this#pns) = length(Ref(a,Ds)#vs)" by simp
  from eval_blocks
  have eval_blocks':"P,E \<turnstile> \<langle>blocks(this#pns,Class(last Ds)#Ts,Ref(a,Ds)#vs,body),
                               (h\<^sub>2,l\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle>" using s s' by simp
  have casts_unique:"\<And>vs'. P \<turnstile> Class (last Ds)#Ts Casts Ref(a,Ds)#vs to vs'
                            \<Longrightarrow> vs' = Ref(a,Ds)#tl vs'"
    using wf
    by -(erule Casts_to.cases,auto elim!:casts_to.cases dest!:mdc_eq_last
                                      simp:path_via_def appendPath_def)
  from same_len' same_len\<^sub>2 eval_blocks' casts_unique
  obtain l'' vs' where body:"P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> 
               \<langle>body,(h\<^sub>2,l\<^sub>2(this # pns[\<mapsto>]Ref(a,Ds)#vs'))\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l'')\<rangle>"
    and casts:"P \<turnstile> Class(last Ds)#Ts Casts Ref(a,Ds)#vs to Ref(a,Ds)#vs'"
    and lengthvs':"length vs' = length vs"
    by -(drule_tac vs="Ref(a,Ds)#vs" in blocksEval,auto simp:length_Suc_conv,blast)
  from same_len\<^sub>2 lengthvs'
  have same_len\<^sub>3:"length (this # pns) = length (Ref(a,Ds) # vs')" by simp
  from restrict_map_upds[OF same_len\<^sub>3,of "set(this#pns)" "l\<^sub>2"]
  have "l\<^sub>2(this # pns[\<mapsto>]Ref(a,Ds)#vs')|`(set(this#pns)) = 
          [this # pns[\<mapsto>]Ref(a,Ds)#vs']" by simp
  with eval_restrict_lcl[OF wf body fv] this_distinct same_len\<^sub>1 same_len
  have "P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> 
   \<langle>body,(h\<^sub>2,[this#pns [\<mapsto>] Ref(a,Ds)#vs'])\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3, l''|`(set(this#pns)))\<rangle>"
    by simp
  with casts obtain l\<^sub>2' l\<^sub>3' vs' where
        "P \<turnstile> Ts Casts vs to vs'"
    and "P,E(this \<mapsto> Class(last Ds),pns [\<mapsto>] Ts) \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3')\<rangle>"
    and "l\<^sub>2' = [this \<mapsto> Ref(a,Ds),pns [\<mapsto>] vs']"
    by(auto elim:Casts_to.cases)
  ultimately have "P,E \<turnstile> \<langle>(ref(a,Cs))\<bullet>(C::)M(map Val vs),s\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>"
    by -(rule StaticCall,simp_all)
  with s' id show ?case by simp
next
  case RedCallNull
  thus ?case
    by (fastforce elim: eval_cases intro: eval_evals.intros eval_finalsId)
next
  case BlockRedNone
  thus ?case
    by (fastforce elim!: eval_cases intro: eval_evals.intros 
                 simp add: fun_upd_same fun_upd_idem)
next
  case (BlockRedSome E V T e h l e'' h' l' v s' e')
  have eval:"P,E \<turnstile> \<langle>{V:T:=Val v; e''},(h', l'(V := l V))\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    and red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e'',(h', l')\<rangle>"
    and notassigned:"\<not> assigned V e" and l':"l' V = Some v"
    and IH:"\<And>ex sx. P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h', l')\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle> \<Longrightarrow>
                     P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle>" by fact+
  from l' have l'upd:"l'(V \<mapsto> v) = l'" by (rule map_upd_triv)
  from wf red l' have casts:"P \<turnstile> T casts v to v"
    apply -
    apply(erule_tac V="V" in None_lcl_casts_values)
    by(simp add:fun_upd_same)+
  from eval obtain h'' l''
  where "P,E(V \<mapsto> T) \<turnstile> \<langle>V:=Val v;; e'',(h',l'(V:=None))\<rangle> \<Rightarrow> \<langle>e',(h'',l'')\<rangle> \<and> 
    s' = (h'',l''(V:=l V))"
    by (fastforce elim:eval_cases simp:fun_upd_same fun_upd_idem)
  moreover
  { fix T' h\<^sub>0 l\<^sub>0 v' v''
    assume eval':"P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h\<^sub>0,l\<^sub>0(V \<mapsto> v''))\<rangle> \<Rightarrow> \<langle>e',(h'', l'')\<rangle>"
      and val:"P,E(V \<mapsto> T) \<turnstile> \<langle>Val v,(h', l'(V := None))\<rangle> \<Rightarrow> \<langle>Val v',(h\<^sub>0,l\<^sub>0)\<rangle>"
      and env:"(E(V \<mapsto> T)) V = Some T'" and casts':"P \<turnstile> T' casts v' to v''"
    from env have TeqT':"T = T'" by (simp add:fun_upd_same)
    from val have eq:"v = v' \<and> h' = h\<^sub>0 \<and> l'(V := None) = l\<^sub>0"
      by -(erule eval_cases,simp)
    with casts casts' wf TeqT' have "v = v''"
      by clarsimp(rule casts_casts_eq)
    with eq eval'
    have "P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h', l'(V \<mapsto> v))\<rangle> \<Rightarrow> \<langle>e',(h'', l'')\<rangle>"
      by clarsimp }
  ultimately have "P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h',l'(V \<mapsto> v))\<rangle> \<Rightarrow> \<langle>e',(h'',l'')\<rangle>" 
    and s':"s' = (h'',l''(V:=l V))"
    apply auto
    apply(erule eval_cases)
     apply(erule eval_cases) apply auto
    apply(erule eval_cases) apply auto
    apply(erule eval_cases) apply auto
    done
  with l'upd have eval'':"P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h',l')\<rangle> \<Rightarrow> \<langle>e',(h'',l'')\<rangle>"
    by simp
  from IH[OF eval''] have "P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<Rightarrow> \<langle>e',(h'', l'')\<rangle>" .
  with s' show ?case by(fastforce intro:Block)
next
  case (InitBlockRed E V T e h l v' e'' h' l' v'' v s' e')
  have eval:" P,E \<turnstile> \<langle>{V:T:=Val v''; e''},(h', l'(V := l V))\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    and red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V \<mapsto> v'))\<rangle> \<rightarrow> \<langle>e'',(h', l')\<rangle>"
    and casts:"P \<turnstile> T casts v to v'" and l':"l' V = Some v''"
    and IH:"\<And>ex sx. P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h', l')\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle> \<Longrightarrow>
                     P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V \<mapsto> v'))\<rangle> \<Rightarrow> \<langle>ex,sx\<rangle>" by fact+
  from l' have l'upd:"l'(V \<mapsto> v'') = l'" by (rule map_upd_triv)
  from wf casts have "P \<turnstile> T casts v' to v'" by(rule casts_casts)
  with wf red l' have casts':"P \<turnstile> T casts v'' to v''"
    apply -
    apply(erule_tac V="V" in Some_lcl_casts_values)
    by(simp add:fun_upd_same)+
  from eval obtain h'' l''
  where "P,E(V \<mapsto> T) \<turnstile> \<langle>V:=Val v'';; e'',(h',l'(V:=None))\<rangle> \<Rightarrow> \<langle>e',(h'',l'')\<rangle> \<and> 
    s' = (h'',l''(V:=l V))"
    by (fastforce elim:eval_cases simp:fun_upd_same fun_upd_idem)
  moreover
  { fix T' v'''
    assume eval':"P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h',l'(V \<mapsto> v'''))\<rangle> \<Rightarrow> \<langle>e',(h'', l'')\<rangle>"
      and env:"(E(V \<mapsto> T)) V = Some T'" and casts'':"P \<turnstile> T' casts v'' to v'''"
    from env have "T = T'" by (simp add:fun_upd_same)
    with casts' casts'' wf have "v'' = v'''" by simp(rule casts_casts_eq)
    with eval' have "P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h', l'(V \<mapsto> v''))\<rangle> \<Rightarrow> \<langle>e',(h'', l'')\<rangle>" by simp }
  ultimately have "P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h',l'(V \<mapsto> v''))\<rangle> \<Rightarrow> \<langle>e',(h'',l'')\<rangle>"
    and s':"s' = (h'',l''(V:=l V))"
    by(auto elim!:eval_cases)
 with l'upd have eval'':"P,E(V \<mapsto> T) \<turnstile> \<langle>e'',(h',l')\<rangle> \<Rightarrow> \<langle>e',(h'',l'')\<rangle>"
    by simp
  from IH[OF eval'']
  have evale:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V \<mapsto> v'))\<rangle> \<Rightarrow> \<langle>e',(h'', l'')\<rangle>" .
  from casts
  have "P,E(V \<mapsto> T) \<turnstile> \<langle>V:=Val v,(h,l(V:=None))\<rangle> \<Rightarrow> \<langle>Val v',(h,l(V \<mapsto> v'))\<rangle>"
    by -(rule_tac l="l(V:=None)" in LAss,
         auto intro:eval_evals.intros simp:fun_upd_same)
  with evale s' show ?case by(fastforce intro:Block Seq)
next
  case (RedBlock E V T v s s' e')
  have "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  then obtain s': "s'=s" and e': "e'=Val v"
    by cases simp
  obtain h l where s: "s=(h,l)" by (cases s)
  have "P,E(V \<mapsto> T) \<turnstile> \<langle>Val v,(h,l(V:=None))\<rangle> \<Rightarrow> \<langle>Val v,(h,l(V:=None))\<rangle>" 
    by (rule eval_evals.intros)
  hence "P,E \<turnstile> \<langle>{V:T;Val v},(h,l)\<rangle> \<Rightarrow> \<langle>Val v,(h,(l(V:=None))(V:=l V))\<rangle>"
    by (rule eval_evals.Block)
  thus "P,E \<turnstile> \<langle>{V:T; Val v},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    using s s' e'
    by simp
next
  case (RedInitBlock T v v' E V u s s' e')
  have "P,E \<turnstile> \<langle>Val u,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" and casts:"P \<turnstile> T casts v to v'" by fact+
  then obtain s': "s' = s" and e': "e'=Val u" by cases simp
  obtain h l where s: "s=(h,l)" by (cases s)
  have val:"P,E(V \<mapsto> T) \<turnstile> \<langle>Val v,(h,l(V:=None))\<rangle> \<Rightarrow> \<langle>Val v,(h,l(V:=None))\<rangle>"
    by (rule eval_evals.intros)
  with casts
  have "P,E(V \<mapsto> T) \<turnstile> \<langle>V:=Val v,(h,l(V:=None))\<rangle> \<Rightarrow> \<langle>Val v',(h,l(V \<mapsto> v'))\<rangle>"
    by -(rule_tac l="l(V:=None)" in LAss,auto simp:fun_upd_same)
  hence "P,E \<turnstile> \<langle>{V:T :=Val v; Val u},(h,l)\<rangle> \<Rightarrow> \<langle>Val u,(h, (l(V\<mapsto>v'))(V:=l V))\<rangle>"
    by (fastforce intro!: eval_evals.intros)
  thus ?case using s s' e' by simp
next
  case SeqRed thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedSeq thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case CondRed thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedCondT thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedCondF thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedWhile
  thus ?case by (auto simp add: unfold_while intro:eval_evals.intros elim:eval_cases)
next
  case ThrowRed thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case RedThrowNull
  thus ?case by -(auto elim!:eval_cases intro!:eval_evals.ThrowNull eval_finalId)
next
  case ListRed1 thus ?case by (fastforce elim: evals_cases intro: eval_evals.intros)
next
  case ListRed2
  thus ?case by (fastforce elim!: evals_cases eval_cases 
                          intro: eval_evals.intros eval_finalId)
next
  case StaticCastThrow
  thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case DynCastThrow
  thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case BinOpThrow1 thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case BinOpThrow2 thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case LAssThrow thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case FAccThrow thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case FAssThrow1 thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case FAssThrow2 thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case CallThrowObj thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case (CallThrowParams es vs r es' E v Copt M s s' e')
  have "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by (rule eval_evals.intros)
  moreover
  have es: "es = map Val vs @ Throw r # es'" by fact
  have eval_e: "P,E \<turnstile> \<langle>Throw r,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  then obtain s': "s' = s" and e': "e' = Throw r"
    by cases (auto elim!:eval_cases)
  with list_eval_Throw [OF eval_e] es
  have "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs @ Throw r # es',s'\<rangle>" by simp
  ultimately have "P,E \<turnstile> \<langle>Call (Val v) Copt M es,s\<rangle> \<Rightarrow> \<langle>Throw r,s'\<rangle>"
    by (rule eval_evals.CallParamsThrow)
  thus ?case using e' by simp
next
  case (BlockThrow E V T r s s' e')
  have "P,E \<turnstile> \<langle>Throw r, s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" by fact
  then obtain s': "s' = s" and e': "e' = Throw r"
    by cases (auto elim!:eval_cases)
  obtain h l where s: "s=(h,l)" by (cases s)
  have "P,E(V \<mapsto> T) \<turnstile> \<langle>Throw r, (h,l(V:=None))\<rangle> \<Rightarrow> \<langle>Throw r, (h,l(V:=None))\<rangle>"
    by (simp add:eval_evals.intros eval_finalId)
  hence "P,E \<turnstile> \<langle>{V:T;Throw r},(h,l)\<rangle> \<Rightarrow> \<langle>Throw r, (h,(l(V:=None))(V:=l V))\<rangle>"
    by (rule eval_evals.Block)
  thus "P,E \<turnstile> \<langle>{V:T; Throw r},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using s s' e' by simp
next
  case (InitBlockThrow T v v' E V r s s' e')
  have "P,E \<turnstile> \<langle>Throw r,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" and casts:"P \<turnstile> T casts v to v'" by fact+
  then obtain s': "s' = s" and e': "e' = Throw r"
    by cases (auto elim!:eval_cases)
  obtain h l where s: "s = (h,l)" by (cases s)
  have "P,E(V \<mapsto> T) \<turnstile> \<langle>Val v,(h,l(V:=None))\<rangle> \<Rightarrow> \<langle>Val v,(h,l(V:=None))\<rangle>"
    by (rule eval_evals.intros)
  with casts
  have "P,E(V \<mapsto> T) \<turnstile> \<langle>V:=Val v,(h,l(V := None))\<rangle> \<Rightarrow> \<langle>Val v',(h,l(V \<mapsto> v'))\<rangle>"
    by -(rule_tac l="l(V:=None)" in LAss,auto simp:fun_upd_same)
  hence "P,E \<turnstile> \<langle>{V:T := Val v; Throw r},(h,l)\<rangle> \<Rightarrow> \<langle>Throw r, (h, (l(V\<mapsto>v'))(V:=l V))\<rangle>"
    by(fastforce intro:eval_evals.intros)
  thus "P,E \<turnstile> \<langle>{V:T := Val v; Throw r},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" using s s' e' by simp
next
  case SeqThrow thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case CondThrow thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
next
  case ThrowThrow thus ?case by (fastforce elim: eval_cases intro: eval_evals.intros)
qed


(* ... und wieder anschalten: *)
declare split_paired_All [simp] split_paired_Ex [simp]
setup \<open>map_theory_claset (fn ctxt => ctxt addSbefore ("split_all_tac", split_all_tac))\<close>
setup \<open>map_theory_simpset (fn ctxt => ctxt addloop ("split_all_tac", split_all_tac))\<close>


text \<open>Its extension to \<open>\<rightarrow>*\<close>:\<close> 

lemma extend_eval:
assumes wf: "wwf_prog P"
and reds: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e'',s''\<rangle>" and eval_rest:  "P,E \<turnstile> \<langle>e'',s''\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

using reds eval_rest 
apply (induct rule: converse_rtrancl_induct2)
apply simp
apply simp
apply (rule extend_1_eval)
apply (rule wf)
apply assumption+
done



lemma extend_evals:
assumes wf: "wwf_prog P"
and reds: "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es'',s''\<rangle>" and eval_rest:  "P,E \<turnstile> \<langle>es'',s''\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
shows "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"

using reds eval_rest 
apply (induct rule: converse_rtrancl_induct2)
apply simp
apply simp
apply (rule extend_1_evals)
apply (rule wf)
apply assumption+
done


text \<open>Finally, small step semantics can be simulated by big step semantics:
\<close>

theorem
assumes wf: "wwf_prog P"
shows small_by_big: "\<lbrakk>P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>; final e'\<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
and "\<lbrakk>P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>; finals es'\<rbrakk> \<Longrightarrow> P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"

proof -
  note wf 
  moreover assume "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
  moreover assume "final e'"
  then have "P,E \<turnstile> \<langle>e',s'\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
    by (rule eval_finalId)
  ultimately show "P,E \<turnstile> \<langle>e,s\<rangle>\<Rightarrow>\<langle>e',s'\<rangle>"
    by (rule extend_eval)
next
  note wf 
  moreover assume "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"
  moreover assume "finals es'"
  then have "P,E \<turnstile> \<langle>es',s'\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
    by (rule eval_finalsId)
  ultimately show "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>"
    by (rule extend_evals)
qed


subsection \<open>Equivalence\<close>

text\<open>And now, the crowning achievement:\<close>

corollary big_iff_small:
  "wwf_prog P \<Longrightarrow>
  P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>  =  (P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle> \<and> final e')"
by(blast dest: big_by_small eval_final small_by_big)


end
