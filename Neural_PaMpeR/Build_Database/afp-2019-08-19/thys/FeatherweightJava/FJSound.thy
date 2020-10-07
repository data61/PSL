(*  Title:       A theory of Featherweight Java in Isabelle/HOL
    Author:      Nate Foster <jnfoster at cis.upenn.edu>, 
                 Dimitrios Vytiniotis <dimitriv at cis.upenn.edu>, 2006
    Maintainer:  Nate Foster <jnfoster at cis.upenn.edu>,
                 Dimitrios Vytiniotis <dimitriv at cis.upenn.edu>
    License:     LGPL
*)

section \<open>{\tt FJSound}: Type Soundness\<close>

theory FJSound imports FJAux
begin 

text\<open>Type soundness is proved using the standard technique of
progress and subject reduction. The numbered lemmas and theorems in
this section correspond to the same results in the ACM TOPLAS paper.
\<close>

subsection\<open>Method Type and Body Connection\<close>

lemma mtype_mbody:
  fixes Cs :: "nat list"
  assumes "mtype(CT,m,C) = Cs \<rightarrow> C0"
  shows "\<exists>xs e. mbody(CT,m,C) = xs . e \<and> length xs = length Cs"
  using assms
  proof(induct rule:mtype.induct)
    case(mt_class C0 Cs C CDef CT m mDef)
    thus ?case 
      by (force simp add:varDefs_types_def varDefs_names_def elim:mtype.cases intro:mbody.mb_class)
  next
    case(mt_super CT C0 CDef m D Cs C)
    then obtain xs e where "mbody(CT,m,D) = xs . e" and "length xs = length Cs" by auto
    thus ?case using mt_super by (auto intro:mbody.mb_super)    
  qed

lemma mtype_mbody_length: 
  assumes mt:"mtype(CT,m,C) = Cs \<rightarrow> C0"
  and mb:"mbody(CT,m,C) = xs . e"
  shows "length xs = length Cs"
proof -
  from mtype_mbody[OF mt] obtain xs' e' 
    where mb2: "mbody(CT,m,C) = xs' . e'" 
    and  "length xs' = length Cs" 
    by auto
  with mbody_functional[OF mb mb2] show ?thesis by auto
qed

subsection\<open>Method Types and Field Declarations of Subtypes\<close>

lemma A_1_1:
  assumes "CT \<turnstile> C <: D" and "CT OK"
  shows "(mtype(CT,m,D) = Cs \<rightarrow> C0) \<Longrightarrow> (mtype(CT,m,C) = Cs \<rightarrow> C0)"
  using assms
proof (induct rule:subtyping.induct)
  case (s_refl C CT) show ?case by fact
next
  case (s_trans C CT D E) thus ?case by auto
next
  case (s_super CT C CDef D)
  hence "CT \<turnstile> CDef OK" and "cName CDef = C" 
    by(auto elim:ct_typing.cases)
  with s_super obtain M 
    where M: "CT \<turnstile>+ M OK IN C" and cMethods: "cMethods CDef = M" 
    by(auto elim:class_typing.cases)
  let ?lookup_m = "lookup M (\<lambda>md. (mName md =m))"
  show ?case
  proof(cases "\<exists>mDef. ?lookup_m = Some mDef") 
    case True
    then obtain mDef where m: "?lookup_m = Some mDef" by(rule exE)
    hence mDef_name: "mName mDef = m" by (rule lookup_true)
    have "CT \<turnstile> mDef OK IN C" using M m by(auto simp add:method_typings_lookup)
    then obtain CDef' m' D' Cs' C0'
      where CT: "CT C = Some CDef'"
        and "cSuper CDef' = D'"
        and "mName mDef = m'"
        and mReturn: "mReturn mDef = C0'"
        and varDefs_types: "varDefs_types (mParams mDef) = Cs'"
        and "\<forall>Ds D0. (mtype(CT,m',D') = Ds \<rightarrow> D0) \<longrightarrow> Cs'=Ds \<and> C0'=D0"
      by (auto elim: method_typing.cases) 
    with s_super mDef_name have "CDef=CDef'" 
      and "D=D'" 
      and "m=m'" 
      and "\<forall>Ds D0. (mtype(CT,m,D) = Ds \<rightarrow> D0) \<longrightarrow> Cs'=Ds \<and> C0' = D0" 
      by auto
    thus ?thesis using s_super cMethods m CT mReturn varDefs_types by (auto intro:mtype.intros)
  next 
    case False
    hence "?lookup_m = None" by (simp add: lookup_split)
    then show ?thesis using s_super cMethods by (auto simp add:mtype.intros)  
  qed
qed


lemma sub_fields: 
  assumes "CT \<turnstile> C <: D"
  shows "\<And>Dg. fields(CT,D) = Dg \<Longrightarrow> \<exists>Cf. fields(CT,C) = (Dg@Cf)"
using assms
proof induct
  case (s_refl CT C)
  hence "fields(CT,C) = (Dg@[])" by simp
  thus ?case ..
next
  case (s_trans CT C D E)
  then obtain Df Cf where "fields(CT,C) = ((Dg@Df)@Cf)" by force
  thus ?case by auto
next
  case (s_super CT C CDef D Dg) 
  then obtain Cf where "cFields CDef = Cf" by force
  with s_super have "fields(CT,C) = (Dg@Cf)" by(simp add:f_class)
  thus ?case ..
qed

subsection\<open>Substitution Lemma\<close>
 
lemma A_1_2:
  assumes "CT OK"
    and "\<Gamma> = \<Gamma>1 ++ \<Gamma>2"                            
    and "\<Gamma>2 = [xs [\<mapsto>] Bs]"                         
    and "length xs = length ds"
    and "length Bs = length ds"                      
    and "\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs"
  shows "CT;\<Gamma> \<turnstile>+ es:Ds \<Longrightarrow> \<exists>Cs. (CT;\<Gamma>1 \<turnstile>+ ([ds/xs]es):Cs \<and> CT \<turnstile>+ Cs <: Ds)" (is "?TYPINGS \<Longrightarrow> ?P1")
    and "CT;\<Gamma> \<turnstile> e:D \<Longrightarrow> \<exists>C. (CT;\<Gamma>1 \<turnstile> ((ds/xs)e):C \<and> CT \<turnstile> C <: D)" (is "?TYPING \<Longrightarrow> ?P2")
proof -
  let ?COMMON_ASMS = "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and> (\<Gamma>2 = [xs [\<mapsto>] Bs]) \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
  have RESULT:"  (?TYPINGS \<longrightarrow> ?COMMON_ASMS \<longrightarrow> ?P1)
               \<and> (?TYPING \<longrightarrow> ?COMMON_ASMS \<longrightarrow> ?P2)"
  proof(induct rule:typings_typing.induct) 
    case (ts_nil CT \<Gamma>)
    show ?case
    proof (rule impI)
      have "(CT;\<Gamma>1 \<turnstile>+ ([ds/xs][]):[]) \<and> (CT \<turnstile>+ [] <: [])"
        by (auto simp add: typings_typing.intros subtypings.intros)
      then show "\<exists>Cs.(CT;\<Gamma>1 \<turnstile>+ ([ds/xs][]):Cs) \<and> (CT \<turnstile>+ Cs <: [])" by auto
    qed
  next
    case(ts_cons CT \<Gamma> e0 C0 es Cs')
    show ?case
    proof (rule impI)
      assume asms: "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and> (\<Gamma>2 = [xs [\<mapsto>] Bs]) \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
      with ts_cons have e0_typ: "CT;\<Gamma> \<turnstile> e0 : C0" by fastforce
      with ts_cons asms have 
          "\<exists>C.(CT;\<Gamma>1 \<turnstile> (ds/xs) e0 : C) \<and> (CT \<turnstile> C <: C0)" 
        and "\<exists>Cs.(CT;\<Gamma>1 \<turnstile>+ [ds/xs]es : Cs) \<and> (CT \<turnstile>+ Cs <: Cs')" 
        by auto
      then obtain C Cs where
          "(CT;\<Gamma>1 \<turnstile> (ds/xs) e0 : C) \<and> (CT \<turnstile> C <: C0)" 
        and "(CT;\<Gamma>1 \<turnstile>+ [ds/xs]es : Cs) \<and> (CT \<turnstile>+ Cs <: Cs')" by auto
      hence "CT;\<Gamma>1 \<turnstile>+ [ds/xs](e0#es) : (C#Cs)"
        and "CT \<turnstile>+ (C#Cs) <: (C0#Cs')" 
        by (auto simp add: typings_typing.intros subtypings.intros)
      then show "\<exists>Cs. CT;\<Gamma>1 \<turnstile>+ map (substs [xs [\<mapsto>] ds]) (e0 # es) : Cs \<and> CT \<turnstile>+ Cs <: (C0 # Cs')"
        by auto
    qed
  next
    case (t_var \<Gamma> x C' CT)
    show ?case
    proof (rule impI)
      assume asms: "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and> (\<Gamma>2 = [xs [\<mapsto>] Bs]) \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
      hence 
        lengths: "length ds = length Bs"
        and G_def: "\<Gamma> = \<Gamma>1 ++ \<Gamma>2"
        and G2_def : "\<Gamma>2 = [xs[\<mapsto>]Bs]" by auto
      from lengths G2_def have same_doms: "dom([xs[\<mapsto>]ds]) = dom(\<Gamma>2)" by auto
      from asms show "\<exists>C. CT;\<Gamma>1 \<turnstile> substs [xs [\<mapsto>] ds] (Var x) : C \<and> CT \<turnstile> C <: C'"
      proof (cases "\<Gamma>2 x")
        case None
        with G_def t_var have G1_x: "\<Gamma>1 x = Some C'" by(simp add:map_add_Some_iff)
        from None same_doms have "x \<notin> dom([xs[\<mapsto>]ds])" by (auto simp only:domIff)      
        hence "[xs[\<mapsto>]ds]x = None" by(auto simp only:map_add_Some_iff)
        hence "(ds/xs)(Var x) = (Var x)" by auto
        with G1_x have 
          "CT;\<Gamma>1 \<turnstile> (ds/xs)(Var x) : C'" and "CT \<turnstile> C' <: C'"
          by (auto simp add:typings_typing.intros subtyping.intros)
        thus ?thesis by auto
      next
        case (Some Bi)
        with G_def t_var have c'_eq_bi: "C' = Bi" by (auto simp add: map_add_SomeD)
        from \<open>length xs = length ds\<close> asms have "length xs = length Bs" by simp
        with Some G2_def have "\<exists>i.(Bs!i = Bi) \<and> (i < length Bs) \<and>
            (\<forall>l.((length l = length Bs) \<longrightarrow> ([xs[\<mapsto>]l] x = Some (l!i))))" 
          by (auto simp add: map_upds_index)
        then obtain i where bs_i_proj: "(Bs!i = Bi)" 
          and i_len: "i < length Bs"
          and P: "(\<And>(l::exp list).((length l = length Bs) \<longrightarrow> ([xs[\<mapsto>]l] x = Some (l!i))))"
          by fastforce
        from lengths P have subst_x: "([xs[\<mapsto>]ds]x = Some (ds!i))" by auto
        from asms obtain As where as_ex:"CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs" by fastforce
        hence "length As = length Bs" by (auto simp add: subtypings_length)
        hence proj_i:"CT;\<Gamma>1 \<turnstile> ds!i : As!i \<and> CT \<turnstile> As!i <: Bs!i"
          using i_len lengths as_ex by (auto simp add: typings_proj)
        hence "CT;\<Gamma>1 \<turnstile> (ds/xs)(Var x) : As!i \<and> CT \<turnstile> As!i <: C'"
          using c'_eq_bi bs_i_proj subst_x by auto
        thus ?thesis ..
      qed
    qed
  next
    case(t_field CT \<Gamma> e0 C0 Cf fi fDef Ci)
    show ?case
    proof(rule impI)
      assume asms: "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and>
        (\<Gamma>2 = [xs [\<mapsto>] Bs]) \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
      from t_field have flds: "fields(CT,C0) = Cf" by fastforce
      from t_field asms obtain C where e0_typ: "CT;\<Gamma>1 \<turnstile> (ds/xs)e0 : C" and sub: "CT \<turnstile> C <: C0"
        by auto
      from sub_fields[OF sub flds] obtain Dg where flds_C: "fields(CT,C) = (Cf@Dg)" ..
      from t_field have lookup_CfDg: "lookup (Cf@Dg) (\<lambda>fd. vdName fd = fi) = Some fDef"
        by(simp add:lookup_append)
      from e0_typ flds_C lookup_CfDg t_field have "CT;\<Gamma>1 \<turnstile> (ds/xs)(FieldProj e0 fi) : Ci"
        by(simp add:typings_typing.intros)
      moreover have "CT \<turnstile> Ci <: Ci" by (simp add:subtyping.intros)
      ultimately show "\<exists>C. CT;\<Gamma>1 \<turnstile> (ds/xs)(FieldProj e0 fi) : C \<and> CT \<turnstile> C <: Ci" by auto
    qed
  next
    case(t_invk CT \<Gamma> e0 C0 m Ds C es Cs)
    show ?case
    proof(rule impI)
      assume asms: "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and> (\<Gamma>2 = [xs [\<mapsto>] Bs])
          \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
      hence ct_ok: "CT OK" ..
      from t_invk have mtyp: "mtype(CT,m,C0) = Ds \<rightarrow> C" 
        and subs: "CT \<turnstile>+ Cs <: Ds"
        and lens: "length es = length Ds"
        by auto
      from t_invk asms obtain C' where
          e0_typ: "CT;\<Gamma>1 \<turnstile> (ds/xs)e0 : C'" and sub': "CT \<turnstile> C' <: C0" by auto
      from t_invk asms obtain Cs' where
          es_typ: "CT;\<Gamma>1 \<turnstile>+ [ds/xs]es : Cs'" and subs': "CT \<turnstile>+ Cs' <: Cs" by auto
      have subst_e: "(ds/xs)(MethodInvk e0 m es) = MethodInvk ((ds/xs)e0) m ([ds/xs]es)"
        by(auto simp add: subst_list1_eq_map_substs)
      from 
        e0_typ
        A_1_1[OF sub' ct_ok mtyp] 
        es_typ
        subtypings_trans[OF subs' subs] 
        lens 
        subst_e
      have "CT;\<Gamma>1 \<turnstile> (ds/xs)(MethodInvk e0 m es) : C" by(auto simp add:typings_typing.intros)
      moreover have "CT \<turnstile> C <: C" by(simp add:subtyping.intros)
      ultimately show "\<exists>C'. CT;\<Gamma>1 \<turnstile> (ds/xs)(MethodInvk e0 m es) : C' \<and> CT \<turnstile> C' <: C" by auto
    qed
  next
    case(t_new CT C Df es Ds \<Gamma> Cs)
    show ?case
    proof(rule impI)
      assume asms: "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and> (\<Gamma>2 = [xs [\<mapsto>] Bs]) \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
      hence ct_ok: "CT OK" ..
      from t_new have
        subs: "CT \<turnstile>+ Cs <: Ds"
        and flds: "fields(CT,C) = Df"
        and len: "length es = length Df"
        and vdts: "varDefs_types Df = Ds"
        by auto
      from t_new asms obtain Cs' where
        es_typ: "CT;\<Gamma>1 \<turnstile>+ [ds/xs]es : Cs'" and subs': "CT \<turnstile>+ Cs' <: Cs" by auto
      have subst_e: "(ds/xs)(New C es) = New C ([ds/xs]es)" 
        by(auto simp add: subst_list2_eq_map_substs)
      from es_typ subtypings_trans[OF subs' subs] flds subst_e len vdts
      have "CT;\<Gamma>1 \<turnstile> (ds/xs)(New C es) : C" by(auto simp add:typings_typing.intros)
      moreover have "CT \<turnstile> C <: C" by(simp add:subtyping.intros)
      ultimately show "\<exists>C'. CT;\<Gamma>1 \<turnstile> (ds/xs)(New C es) : C' \<and> CT \<turnstile> C' <: C" by auto
    qed
  next
    case(t_ucast CT \<Gamma> e0 D C)
    show ?case
    proof(rule impI)
      assume asms: "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and> (\<Gamma>2 = [xs [\<mapsto>] Bs]) \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
      from t_ucast asms obtain C' where e0_typ: "CT;\<Gamma>1 \<turnstile> (ds/xs)e0 : C'" 
        and  sub1:"CT \<turnstile> C' <: D" 
        and  sub2:"CT \<turnstile> D <: C" by auto
      from sub1 sub2 have "CT \<turnstile> C' <: C" by (rule s_trans)
      with e0_typ have "CT;\<Gamma>1 \<turnstile> (ds/xs)(Cast C e0) : C" by(auto simp add: typings_typing.intros)
      moreover have "CT \<turnstile> C <: C" by (rule s_refl)
      ultimately show "\<exists>C'. CT;\<Gamma>1 \<turnstile> (ds/xs)(Cast C e0) : C' \<and> CT \<turnstile> C' <: C" by auto
    qed
  next
    case(t_dcast CT \<Gamma> e0 D C)
    show ?case
    proof(rule impI)
      assume asms: "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and> (\<Gamma>2 = [xs [\<mapsto>] Bs]) \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
      from t_dcast asms obtain C' where e0_typ:"CT;\<Gamma>1 \<turnstile> (ds/xs)e0 : C'" by auto
      have "(CT \<turnstile> C' <: C)  \<or> 
        (C \<noteq> C' \<and> CT \<turnstile> C <: C') \<or> 
        (CT \<turnstile> C \<not><: C' \<and> CT \<turnstile> C' \<not><: C)" by blast
      moreover 
      { assume "CT \<turnstile> C' <: C" 
        with e0_typ have "CT;\<Gamma>1 \<turnstile> (ds/xs) (Cast C e0) : C" by (auto simp add: typings_typing.intros)
      }
      moreover 
      { assume "(C \<noteq> C' \<and> CT \<turnstile> C <: C')" 
        with e0_typ have "CT;\<Gamma>1 \<turnstile> (ds/xs) (Cast C e0) : C" by (auto simp add: typings_typing.intros)
      }
      moreover 
      { assume "(CT \<turnstile> C \<not><: C' \<and> CT \<turnstile> C' \<not><: C)" 
        with e0_typ have "CT;\<Gamma>1 \<turnstile> (ds/xs) (Cast C e0) : C" by (auto simp add: typings_typing.intros)
      }
      ultimately have "CT;\<Gamma>1 \<turnstile> (ds/xs) (Cast C e0) : C" by auto
      moreover have "CT \<turnstile> C <: C" by(rule s_refl)
      ultimately show "\<exists>C'. CT;\<Gamma>1 \<turnstile> (ds/xs)(Cast C e0) : C' \<and> CT \<turnstile> C' <: C" by auto
    qed
  next
    case(t_scast CT \<Gamma> e0 D C)
    show ?case
    proof(rule impI)
      assume asms: "(CT OK) \<and> (\<Gamma> = \<Gamma>1 ++ \<Gamma>2) \<and> (\<Gamma>2 = [xs [\<mapsto>] Bs]) \<and> (length Bs = length ds) \<and> (\<exists>As. CT;\<Gamma>1 \<turnstile>+ ds : As \<and> CT \<turnstile>+ As <: Bs)"
      from t_scast asms obtain C' where e0_typ:"CT;\<Gamma>1 \<turnstile> (ds/xs)e0 : C'" 
        and sub1: "CT \<turnstile> C' <: D" 
        and nsub1: "CT \<turnstile> C \<not><: D"  
        and nsub2: "CT \<turnstile> D \<not><: C" by auto
      from not_subtypes[OF sub1 nsub1 nsub2] have "CT \<turnstile> C' \<not><: C" by fastforce
      moreover have "CT \<turnstile> C \<not><: C'" proof(rule ccontr)
        assume "\<not> CT \<turnstile> C \<not><: C'"
        hence "CT \<turnstile> C <: C'" by auto
        hence "CT \<turnstile> C <: D" using sub1 by(rule s_trans)
        with nsub1 show "False" by auto
      qed
      ultimately have "CT;\<Gamma>1 \<turnstile> (ds/xs) (Cast C e0) : C" using e0_typ by (auto simp add: typings_typing.intros)
      thus "\<exists>C'. CT;\<Gamma>1 \<turnstile> (ds/xs)(Cast C e0) : C' \<and> CT \<turnstile> C' <: C" by (auto simp add: s_refl)
    qed
  qed
  thus "?TYPINGS \<Longrightarrow> ?P1" and "?TYPING \<Longrightarrow> ?P2" using assms by auto
qed
    

subsection\<open>Weakening Lemma\<close>

text \<open>This lemma is not in the same form as in TOPLAS, but rather as
we need it in subject reduction\<close>

lemma A_1_3:
  shows "(CT;\<Gamma>2 \<turnstile>+ es : Cs) \<Longrightarrow> (CT;\<Gamma>1++\<Gamma>2 \<turnstile>+ es : Cs)" (is "?P1 \<Longrightarrow> ?P2")
  and "CT;\<Gamma>2 \<turnstile> e : C \<Longrightarrow> CT;\<Gamma>1++\<Gamma>2 \<turnstile> e : C" (is "?Q1 \<Longrightarrow> ?Q2")
proof - 
  have "(?P1 \<longrightarrow> ?P2) \<and> (?Q1 \<longrightarrow> ?Q2)" 
  by(induct rule:typings_typing.induct, auto simp add: map_add_find_right typings_typing.intros) 
  thus "?P1 \<Longrightarrow> ?P2" and "?Q1 \<Longrightarrow> ?Q2" by auto
qed


subsection \<open>Method Body Typing Lemma\<close>

lemma A_1_4: 
  assumes ct_ok: "CT OK" 
  and mb:"mbody(CT,m,C) = xs . e" 
  and mt:"mtype(CT,m,C) = Ds \<rightarrow> D"
  shows "\<exists>D0 C0. (CT \<turnstile> C <: D0) \<and> 
                (CT \<turnstile> C0 <: D) \<and> 
                (CT;[xs[\<mapsto>]Ds](this \<mapsto> D0) \<turnstile> e : C0)"
  using mb ct_ok mt proof(induct rule: mbody.induct)
  case (mb_class CT C CDef m mDef xs e)
  hence
    m_param:"varDefs_types (mParams mDef) = Ds" 
    and m_ret:"mReturn mDef = D" 
    and "CT \<turnstile> CDef OK" 
    and "cName CDef = C"
    by (auto elim:mtype.cases ct_typing.cases)  
  hence "CT \<turnstile>+ (cMethods CDef) OK IN C" by (auto elim:class_typing.cases)
  hence "CT \<turnstile> mDef OK IN C" using mb_class by(auto simp add:method_typings_lookup)
  hence "\<exists> E0. ((CT;[xs[\<mapsto>]Ds,this\<mapsto>C] \<turnstile> e : E0) \<and> (CT \<turnstile> E0 <: D))"
    using mb_class m_param m_ret by(auto elim:method_typing.cases)
  then obtain E0 
    where "CT;[xs[\<mapsto>]Ds,this\<mapsto>C] \<turnstile> e : E0"
    and "CT \<turnstile> E0 <: D"
    and "CT \<turnstile> C <: C" by (auto simp add: s_refl)
  thus ?case by blast
next
  case (mb_super CT C CDef m Da xs e)
  hence ct: "CT OK"
    and IH: "\<lbrakk>CT OK; mtype(CT,m,Da) = Ds \<rightarrow> D\<rbrakk> 
    \<Longrightarrow> \<exists>D0 C0. (CT \<turnstile> Da <: D0) \<and> (CT \<turnstile> C0 <: D) 
              \<and> (CT;[xs [\<mapsto>] Ds, this \<mapsto> D0] \<turnstile> e:C0)" by fastforce+
  from mb_super have c_sub_da: "CT \<turnstile> C <: Da" by (auto simp add:s_super)
  from mb_super have mt:"mtype(CT,m,Da) = Ds \<rightarrow> D" by (auto elim: mtype.cases)
  from IH[OF ct mt] obtain D0 C0 
    where s1: "CT \<turnstile> Da <: D0" 
    and "CT \<turnstile> C0 <: D" 
    and "CT;[xs [\<mapsto>] Ds, this \<mapsto> D0] \<turnstile> e : C0" by auto  
  thus ?case using s_trans[OF c_sub_da s1] by blast
qed

subsection \<open>Subject Reduction Theorem\<close>

theorem Thm_2_4_1: 
  assumes "CT \<turnstile> e \<rightarrow> e'" 
  and "CT OK"
  shows "\<And>C. \<lbrakk> CT;\<Gamma> \<turnstile> e : C \<rbrakk> 
  \<Longrightarrow> \<exists>C'. (CT;\<Gamma> \<turnstile> e' : C' \<and> CT \<turnstile> C' <: C)"
  using assms
proof(induct rule: reduction.induct)
  case (r_field CT Ca Cf es fi e')
  hence "CT;\<Gamma> \<turnstile> FieldProj (New Ca es) fi : C" 
    and ct_ok: "CT OK" 
    and flds: "fields(CT,Ca) = Cf" 
    and lkup2: "lookup2 Cf es (\<lambda>fd. vdName fd = fi) = Some e'" by fastforce+
  then obtain Ca' Cf' fDef 
    where new_typ: "CT;\<Gamma> \<turnstile> New Ca es : Ca'" 
    and flds':"fields(CT,Ca') = Cf'" 
    and lkup: "lookup Cf' (\<lambda>fd. vdName fd = fi) = Some fDef" 
    and C_def: "vdType fDef = C" by (auto elim: typing.cases)
  hence Ca_Ca': "Ca = Ca'" by (auto elim:typing.cases)
  with flds' have Cf_Cf': "Cf = Cf'" by(simp add:fields_functional[OF flds ct_ok])
  from new_typ obtain Cs Ds Cf''
    where "fields(CT,Ca') = Cf''" 
    and es_typs: "CT;\<Gamma> \<turnstile>+ es:Cs"
    and Ds_def: "varDefs_types Cf'' = Ds" 
    and length_Cf_es: "length Cf'' = length es" 
    and subs: "CT \<turnstile>+ Cs <: Ds"
    by(auto elim:typing.cases)
  with Ca_Ca' have  Cf_Cf'': "Cf = Cf''" by(auto simp add:fields_functional[OF flds ct_ok])
  from length_Cf_es Cf_Cf'' lookup2_index[OF lkup2] obtain i where 
    i_bound: "i < length es" 
    and "e' = es!i" 
    and "lookup Cf (\<lambda>fd. vdName fd = fi) = Some (Cf!i)" by auto
  moreover
  with C_def Ds_def lkup lkup2 have "Ds!i = C"
    using Ca_Ca' Cf_Cf' Cf_Cf'' i_bound length_Cf_es flds'
    by (auto simp add:nth_map varDefs_types_def fields_functional[OF flds ct_ok])
  moreover with subs es_typs have 
    "CT;\<Gamma> \<turnstile> (es!i):(Cs!i)" and "CT \<turnstile> (Cs!i) <: (Ds!i)" using i_bound
    by(auto simp add:typings_index subtypings_index typings_lengths) 
  ultimately show ?case by auto
next
  case(r_invk CT m Ca xs e ds es e')
  from r_invk have mb: "mbody(CT,m,Ca) = xs . e" by fastforce
  from r_invk obtain Ca' Ds Cs
    where "CT;\<Gamma> \<turnstile> New Ca es : Ca'"
    and "mtype(CT,m,Ca') = Cs \<rightarrow> C" 
    and ds_typs: "CT;\<Gamma> \<turnstile>+ ds : Ds" 
    and Ds_subs: "CT \<turnstile>+ Ds <: Cs" 
    and l1: "length ds = length Cs" by(auto elim:typing.cases)
  hence new_typ: "CT;\<Gamma> \<turnstile> New Ca es : Ca" 
    and mt: "mtype(CT,m,Ca) = Cs \<rightarrow> C" by (auto elim:typing.cases)
  from ds_typs new_typ have "CT;\<Gamma> \<turnstile>+ (ds @[New Ca es]) : (Ds @[Ca])"
    by (simp add:typings_append)
  moreover from A_1_4[OF _ mb mt] r_invk obtain Da E  
    where "CT \<turnstile> Ca <: Da" 
    and E_sub_C: "CT \<turnstile> E <: C" 
    and e0_typ1: "CT;[xs[\<mapsto>]Cs,this\<mapsto>Da] \<turnstile> e : E" by auto
  moreover with Ds_subs have "CT \<turnstile>+ (Ds@[Ca]) <: (Cs@[Da])"
    by(auto simp add:subtyping_append)
  ultimately have ex: "\<exists>As. CT;\<Gamma> \<turnstile>+ (ds @[New Ca es]) : As \<and> CT \<turnstile>+ As <: (Cs@[Da])"
    by auto
  from e0_typ1 have e0_typ2: "CT;(\<Gamma> ++ [xs[\<mapsto>]Cs,this\<mapsto>Da]) \<turnstile> e : E"
    by(simp only:A_1_3)
  from e0_typ2 mtype_mbody_length[OF mt mb]
  have e0_typ3: "CT;(\<Gamma> ++ [(xs@[this])[\<mapsto>](Cs@[Da])]) \<turnstile> e : E"
    by(force simp only:map_shuffle)
  let ?\<Gamma>1 = "\<Gamma>" and ?\<Gamma>2 = "[(xs@[this])[\<mapsto>](Cs@[Da])]"
  have g_def: "(?\<Gamma>1 ++ ?\<Gamma>2) = (?\<Gamma>1 ++ ?\<Gamma>2)" and g2_def: "?\<Gamma>2 = ?\<Gamma>2" by auto
  from A_1_2[OF _ g_def g2_def _ _ ex] e0_typ3 r_invk l1 mtype_mbody_length[OF mt mb]
  obtain E' where e'_typ: "CT;\<Gamma> \<turnstile> substs [(xs@[this])[\<mapsto>](ds@[New Ca es])] e : E'" 
    and E'_sub_E: "CT \<turnstile> E' <: E" by force
  moreover from e'_typ l1 mtype_mbody_length[OF mt mb]
  have "CT;\<Gamma> \<turnstile> substs [xs[\<mapsto>]ds,this\<mapsto>(New Ca es)] e : E'"
    by(auto simp only:map_shuffle)
  moreover from E'_sub_E E_sub_C have "CT \<turnstile> E' <: C" by (rule subtyping.s_trans)
  ultimately show ?case using r_invk by auto
next
  case (r_cast CT Ca D es)
  then obtain Ca' 
    where "C = D" 
    and "CT;\<Gamma> \<turnstile> New Ca es : Ca'" by (auto elim: typing.cases)
  thus ?case using r_cast by (auto elim: typing.cases)
next
  case (rc_field CT e0 e0' f)
  then obtain C0 Cf fd where "CT;\<Gamma> \<turnstile> e0 : C0" 
    and Cf_def: "fields(CT,C0) = Cf" 
    and fd_def:"lookup Cf (\<lambda>fd. (vdName fd = f))  = Some fd"
    and "vdType fd = C" 
    by (auto elim:typing.cases)
  moreover with rc_field obtain C' 
    where "CT;\<Gamma> \<turnstile> e0' : C'" 
    and "CT \<turnstile> C' <: C0" by auto
  moreover from sub_fields[OF _ Cf_def] obtain Cf'
    where "fields(CT,C') = (Cf@Cf')" by rule (rule \<open>CT \<turnstile> C' <: C0\<close>)
  moreover with fd_def have "lookup (Cf@Cf') (\<lambda>fd. (vdName fd = f)) = Some fd" 
    by(simp add:lookup_append)
  ultimately have "CT;\<Gamma> \<turnstile> FieldProj e0' f : C" by(auto simp add:typings_typing.t_field)
  thus ?case by (auto simp add:subtyping.s_refl)
next
  case (rc_invk_recv CT e0 e0' m es C)
  then obtain C0 Ds Cs
    where ct_ok:"CT OK" 
    and "CT;\<Gamma> \<turnstile> e0 : C0" 
    and mt:"mtype(CT,m,C0) = Ds \<rightarrow> C" 
    and "CT;\<Gamma> \<turnstile>+ es : Cs"
    and "length es = length Ds"
    and "CT \<turnstile>+ Cs <: Ds"
    by (auto elim:typing.cases)
  moreover with rc_invk_recv obtain C0' 
    where "CT;\<Gamma> \<turnstile> e0' : C0'" 
    and "CT \<turnstile> C0' <: C0" by auto
  moreover with A_1_1[OF _ ct_ok mt] have "mtype(CT,m,C0') = Ds \<rightarrow> C" by simp
  ultimately have "CT;\<Gamma> \<turnstile> MethodInvk e0' m es : C" by(auto simp add:typings_typing.t_invk)
  thus ?case by (auto simp add:subtyping.s_refl)
next
  case (rc_invk_arg CT ei ei' e0 m el er C)
  then obtain Cs Ds C0
    where typs: "CT;\<Gamma> \<turnstile>+ (el@(ei#er)) : Cs"
    and e0_typ: "CT;\<Gamma> \<turnstile> e0 : C0"
    and mt: "mtype(CT,m,C0) = Ds \<rightarrow> C"
    and Cs_sub_Ds: "CT \<turnstile>+ Cs <: Ds"
    and len: "length (el@(ei#er)) = length Ds"
    by(auto elim:typing.cases)
  hence "CT;\<Gamma> \<turnstile> ei:(Cs!(length el))" by (simp add:ith_typing)
  with rc_invk_arg obtain Ci' 
    where ei_typ: "CT;\<Gamma> \<turnstile> ei':Ci'"
    and Ci_sub: "CT \<turnstile> Ci' <: (Cs!(length el))"
    by auto
  from ith_typing_sub[OF typs ei_typ Ci_sub] obtain Cs'
    where es'_typs: "CT;\<Gamma> \<turnstile>+ (el@(ei'#er)) : Cs'"
    and Cs'_sub_Cs: "CT \<turnstile>+ Cs' <: Cs" by auto
  from len have "length (el@(ei'#er)) = length Ds" by simp
  with es'_typs subtypings_trans[OF Cs'_sub_Cs Cs_sub_Ds]  e0_typ mt have
    "CT;\<Gamma> \<turnstile> MethodInvk e0 m (el@(ei'#er)) : C"      
    by(auto simp add:typings_typing.t_invk)
  thus ?case by (auto simp add:subtyping.s_refl)
next
  case (rc_new_arg CT ei ei' Ca el er C)
  then obtain Cs Df Ds 
    where typs: "CT;\<Gamma> \<turnstile>+ (el@(ei#er)) : Cs"
    and flds: "fields(CT,C) = Df"
    and len: "length (el@(ei#er)) = length Df"
    and Ds_def: "varDefs_types Df = Ds"
    and Cs_sub_Ds: "CT \<turnstile>+ Cs <: Ds"
    and C_def: "Ca = C"
    by(auto elim:typing.cases)
  hence "CT;\<Gamma> \<turnstile> ei:(Cs!(length el))" by (simp add:ith_typing)
  with rc_new_arg obtain Ci' 
    where ei_typ: "CT;\<Gamma> \<turnstile> ei':Ci'"
    and Ci_sub: "CT \<turnstile> Ci' <: (Cs!(length el))"
    by auto
  from ith_typing_sub[OF typs ei_typ Ci_sub] obtain Cs'
    where es'_typs: "CT;\<Gamma> \<turnstile>+ (el@(ei'#er)) : Cs'"
    and Cs'_sub_Cs: "CT \<turnstile>+ Cs' <: Cs" by auto
  from len have "length (el@(ei'#er)) = length Df" by simp
  with es'_typs subtypings_trans[OF Cs'_sub_Cs Cs_sub_Ds] flds Ds_def C_def  have
    "CT;\<Gamma> \<turnstile> New Ca (el@(ei'#er)) : C"      
    by(auto simp add:typings_typing.t_new)
  thus ?case by (auto simp add:subtyping.s_refl)
next
  case (rc_cast CT e0 e0' C Ca)
  then obtain D 
    where "CT;\<Gamma> \<turnstile> e0 : D"
    and Ca_def: "Ca = C"
    by(auto elim:typing.cases)
  with rc_cast obtain D' 
    where e0'_typ: "CT;\<Gamma> \<turnstile> e0':D'" and "CT \<turnstile> D' <: D"
    by auto
  have "(CT \<turnstile> D' <: C)  \<or> 
    (C \<noteq> D' \<and> CT \<turnstile> C <: D') \<or> 
    (CT \<turnstile> C \<not><: D' \<and> CT \<turnstile> D' \<not><: C)" by blast
  moreover { 
    assume "CT \<turnstile> D' <: C" 
    with e0'_typ have "CT;\<Gamma> \<turnstile> Cast C e0' : C" by (auto simp add: typings_typing.t_ucast)
  } moreover {
    assume "(C \<noteq> D' \<and> CT \<turnstile> C <: D')" 
    with e0'_typ have "CT;\<Gamma> \<turnstile> Cast C e0' : C" by (auto simp add: typings_typing.t_dcast)
  } moreover { 
    assume "(CT \<turnstile> C \<not><: D' \<and> CT \<turnstile> D' \<not><: C)" 
    with e0'_typ have "CT;\<Gamma> \<turnstile> Cast C e0' : C" by (auto simp add: typings_typing.t_scast)
  } ultimately have "CT;\<Gamma> \<turnstile> Cast C e0' : C" by auto
  thus ?case using Ca_def by (auto simp add:subtyping.s_refl)
qed

subsection \<open>Multi-Step Subject Reduction Theorem\<close>

corollary Cor_2_4_1_multi:
  assumes "CT \<turnstile> e \<rightarrow>* e'" 
  and "CT OK"
  shows "\<And>C. \<lbrakk> CT;\<Gamma> \<turnstile> e : C \<rbrakk> \<Longrightarrow> \<exists>C'. (CT;\<Gamma> \<turnstile> e' : C' \<and> CT \<turnstile> C' <: C)"
  using assms
proof induct
  case (rs_refl CT e C) thus ?case by (auto simp add:subtyping.s_refl)
next
  case(rs_trans CT e e' e'' C)
  hence e_typ: "CT;\<Gamma> \<turnstile> e : C" 
    and e_step: "CT \<turnstile> e \<rightarrow> e'" 
    and ct_ok: "CT OK" 
    and IH: "\<And>D. \<lbrakk>CT;\<Gamma> \<turnstile> e' : D; CT OK\<rbrakk> \<Longrightarrow> \<exists>E. CT;\<Gamma> \<turnstile> e'' : E \<and> CT \<turnstile> E <: D"
    by auto
  from Thm_2_4_1[OF e_step ct_ok e_typ] obtain D where e'_typ: "CT;\<Gamma> \<turnstile> e' : D" and D_sub_C: "CT \<turnstile> D <: C" by auto
  with IH[OF e'_typ ct_ok] obtain E where "CT;\<Gamma> \<turnstile> e'': E" and E_sub_D: "CT \<turnstile> E <: D" by auto
  moreover from s_trans[OF E_sub_D D_sub_C] have "CT \<turnstile> E <: C" by auto
  ultimately show ?case by auto
qed 


subsection \<open>Progress\<close>

text \<open>The two "progress lemmas" proved in the TOPLAS paper alone are
not quite enough to prove type soundness. We prove an additional lemma
showing that every well-typed expression is either a value or contains
a potential redex as a sub-expression.\<close>

theorem Thm_2_4_2_1: 
  assumes "CT;Map.empty \<turnstile> e : C"
  and "FieldProj (New C0 es) fi \<in> subexprs(e)"
  shows "\<exists>Cf fDef. fields(CT, C0) = Cf \<and> lookup Cf (\<lambda>fd. (vdName fd = fi)) = Some fDef"
proof -
  obtain Ci where "CT;Map.empty \<turnstile> (FieldProj (New C0 es) fi) : Ci" 
    using assms by (force simp add:subexpr_typing)
  then obtain Cf fDef C0'
    where "CT;Map.empty \<turnstile> (New C0 es) : C0'"
    and "fields(CT,C0') = Cf" 
    and "lookup Cf (\<lambda>fd. (vdName fd = fi)) = Some fDef"
    by (auto elim:typing.cases)
  thus ?thesis by (auto elim:typing.cases)
qed

lemma Thm_2_4_2_2: 
  fixes es ds :: "exp list"
  assumes "CT;Map.empty \<turnstile> e : C" 
  and "MethodInvk (New C0 es) m ds \<in> subexprs(e)"
  shows "\<exists>xs e0. mbody(CT,m,C0) = xs . e0 \<and> length xs = length ds"
proof -
  obtain D where "CT;Map.empty \<turnstile> MethodInvk (New C0 es) m ds : D" 
    using assms by (force simp add:subexpr_typing)
  then obtain C0' Cs
    where "CT;Map.empty \<turnstile> (New C0 es) : C0'"
    and mt:"mtype(CT,m,C0') = Cs \<rightarrow> D"
    and "length ds = length Cs"
    by (auto elim:typing.cases)
  with mtype_mbody[OF mt] show ?thesis by (force elim:typing.cases)
qed
     
lemma closed_subterm_split: 
  assumes "CT;\<Gamma> \<turnstile> e : C" and "\<Gamma> = Map.empty"
  shows "
  ((\<exists>C0 es fi. (FieldProj (New C0 es) fi) \<in> subexprs(e))  
  \<or> (\<exists>C0 es m ds. (MethodInvk (New C0 es) m ds) \<in> subexprs(e))
  \<or> (\<exists>C0 D es. (Cast D (New C0 es)) \<in> subexprs(e))
  \<or> val(e))" (is "?F e \<or> ?M e \<or> ?C e \<or> ?V e" is "?IH e")
using assms
proof(induct CT \<Gamma> e C rule:typing_induct)
  case 1 thus ?case using assms by auto
next
  case (2 C CT \<Gamma> x) thus ?case by auto
next
  case (3 C0 Ct Cf Ci \<Gamma> e0 fDef fi) 
  have s1: "e0 \<in> subexprs(FieldProj e0 fi)" by(auto simp add:isubexprs.intros)
  from 3 have "?IH e0" by auto
  moreover
  { assume "?F e0"
    then obtain C0 es fi' where s2: "FieldProj (New C0 es) fi' \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?M e0"
    then obtain C0 es m ds where s2: "MethodInvk (New C0 es) m ds \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?C e0"
    then obtain C0 D es where s2: "Cast D (New C0 es) \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?V e0"
    then obtain C0 es where "e0 = (New C0 es)" and "vals(es)" by (force elim:val.cases)
    hence ?case by(force intro:isubexprs.intros)
  }
  ultimately show ?case by blast
next 
  case (4 C C0 CT Cs Ds \<Gamma> e0 es m)
  have s1: "e0 \<in> subexprs(MethodInvk e0 m es)" by(auto simp add:isubexprs.intros)
  from 4 have "?IH e0" by auto
  moreover
  { assume "?F e0"
    then obtain C0 es fi where s2: "FieldProj (New C0 es) fi \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?M e0"
    then obtain C0 es' m' ds where s2: "MethodInvk (New C0 es') m' ds \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?C e0"
    then obtain C0 D es where s2: "Cast D (New C0 es) \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?V e0"
    then obtain C0 es' where "e0 = (New C0 es')" and "vals(es')" by (force elim:val.cases)
    hence ?case by(force intro:isubexprs.intros)
  }
  ultimately show ?case by blast
next
  case (5 C CT Cs Df Ds \<Gamma> es)
  hence 
    "length es = length Cs"    
    "\<And> i. \<lbrakk>i < length es; CT;\<Gamma> \<turnstile> (es!i) : (Cs!i); \<Gamma> = Map.empty\<rbrakk> \<Longrightarrow> ?IH (es!i)"
    and "CT;\<Gamma> \<turnstile>+ es : Cs"
    by (auto simp add:typings_lengths)
  hence "(\<exists>i < length es. (?F (es!i) \<or> ?M (es!i) \<or> ?C (es!i))) \<or> (vals(es))" (is "?Q es")
  proof(induct "es" "Cs" rule:list_induct2)
    case Nil thus "?Q []" by(auto intro:vals_val.intros)
    next
    case (Cons h t Ch Ct)
      with 5 have h_t_typs: "CT;\<Gamma> \<turnstile>+ (h#t) : (Ch#Ct)"
        and OIH: "\<And> i. \<lbrakk>i < length (h#t); CT;\<Gamma> \<turnstile> ((h#t)!i) : ((Ch#Ct)!i); \<Gamma> = Map.empty\<rbrakk> \<Longrightarrow> ?IH ((h#t)!i)"
        and G_def: "\<Gamma> = Map.empty"
        by auto
      from h_t_typs have 
        h_typ: "CT;\<Gamma> \<turnstile> (h#t)!0 : (Ch#Ct)!0" 
        and t_typs: "CT;\<Gamma> \<turnstile>+ t : Ct"
        by(auto elim:typings.cases)
      { fix i assume "i < length t"
        hence s_i: "Suc i < length (h#t)" by auto
        from OIH[OF s_i] have "\<lbrakk>i < length t; CT;\<Gamma> \<turnstile> (t!i) : (Ct!i); \<Gamma> = Map.empty\<rbrakk> \<Longrightarrow> ?IH (t!i)" by auto }
      with t_typs have "?Q t" using Cons by auto
      moreover { 
        assume "\<exists>i < length t. (?F (t!i) \<or> ?M (t!i) \<or> ?C (t!i))"
        then obtain i 
          where "i < length t" 
          and "?F (t!i) \<or> ?M (t!i) \<or> ?C (t!i)" by force
        hence "(Suc i < length (h#t)) \<and> (?F ((h#t)!(Suc i)) \<or> ?M ((h#t)!(Suc i)) \<or> ?C ((h#t)!(Suc i)))" by auto
        hence "\<exists>i < length (h#t). (?F ((h#t)!i) \<or> ?M ((h#t)!i) \<or> ?C ((h#t)!i))" ..
        hence "?Q (h#t)" by auto
      } moreover {
        assume v_t: "vals(t)"
        from OIH[OF _ h_typ G_def] have "?IH h" by auto
        moreover
        { assume "?F h \<or> ?M h \<or> ?C h"
          hence "?F ((h#t)!0) \<or> ?M ((h#t)!0) \<or> ?C ((h#t)!0)" by auto
          hence "?Q (h#t)" by force
        } moreover {
          assume "?V h"
          with v_t have "vals((h#t))" by (force intro:vals_val.intros)
          hence "?Q(h#t)" by auto
        } ultimately have "?Q(h#t)" by blast
      } ultimately show "?Q(h#t)" by blast
    qed
    moreover {
      assume "\<exists>i<length es. ?F (es!i) \<or> ?M (es!i) \<or> ?C(es!i)"
      then obtain i where i_len: "i < length es" and r: "?F (es!i) \<or> ?M (es!i) \<or> ?C(es!i)" by force
      from ith_mem[OF i_len] have s1:"es!i \<in> subexprs(New C es)" by(auto intro:isubexprs.se_newarg)
      { assume "?F (es!i)"
        then obtain C0 es' fi where s2: "FieldProj (New C0 es') fi \<in> subexprs(es!i)" by auto
        from rtrancl_trans[OF s2 s1] have "?F(New C es) \<or> ?M(New C es) \<or> ?C(New C es)" by auto
      } moreover {
        assume "?M (es!i)"
        then obtain C0 es' m' ds where s2: "MethodInvk (New C0 es') m' ds \<in> subexprs(es!i)" by force
        from rtrancl_trans[OF s2 s1] have "?F(New C es) \<or> ?M(New C es) \<or> ?C(New C es)" by auto
      } moreover {
        assume "?C (es!i)"
        then obtain C0 D es' where s2: "Cast D (New C0 es') \<in> subexprs(es!i)" by auto
        from rtrancl_trans[OF s2 s1] have "?F(New C es) \<or> ?M(New C es) \<or> ?C(New C es)" by auto
      } ultimately have "?F(New C es) \<or> ?M(New C es) \<or> ?C(New C es)" using r by blast
      hence ?case by auto
    } moreover {
      assume "vals(es)" 
      hence ?case by(auto intro:vals_val.intros)
    } ultimately show ?case by blast
  next
    case (6 C CT D \<Gamma> e0)
    have s1: "e0 \<in> subexprs(Cast C e0)" by(auto simp add:isubexprs.intros)
  from 6 have "?IH e0" by auto
  moreover
  { assume "?F e0"
    then obtain C0 es fi where s2: "FieldProj (New C0 es) fi \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?M e0"
    then obtain C0 es m ds where s2: "MethodInvk (New C0 es) m ds \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?C e0"
    then obtain C0 D' es where s2: "Cast D' (New C0 es) \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?V e0"
    then obtain C0 es' where "e0 = (New C0 es')" and "vals(es')" by (force elim:val.cases)
    hence ?case by(force intro:isubexprs.intros)
  }
  ultimately show ?case by blast
next
  case (7 C CT D \<Gamma> e0)
  have s1: "e0 \<in> subexprs(Cast C e0)" by(auto simp add:isubexprs.intros)
  from 7 have "?IH e0" by auto
  moreover
  { assume "?F e0"
    then obtain C0 es fi where s2: "FieldProj (New C0 es) fi \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?M e0"
    then obtain C0 es m ds where s2: "MethodInvk (New C0 es) m ds \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?C e0"
    then obtain C0 D' es where s2: "Cast D' (New C0 es) \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?V e0"
    then obtain C0 es' where "e0 = (New C0 es')" and "vals(es')" by (force elim:val.cases)
    hence ?case by(force intro:isubexprs.intros)
  }
  ultimately show ?case by blast
next 
  case (8 C CT D \<Gamma> e0)
  have s1: "e0 \<in> subexprs(Cast C e0)" by(auto simp add:isubexprs.intros)
  from 8 have "?IH e0" by auto
  moreover
  { assume "?F e0"
    then obtain C0 es fi where s2: "FieldProj (New C0 es) fi \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?M e0"
    then obtain C0 es m ds where s2: "MethodInvk (New C0 es) m ds \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?C e0"
    then obtain C0 D' es where s2: "Cast D' (New C0 es) \<in> subexprs(e0)" by auto
    from rtrancl_trans[OF s2 s1] have ?case by auto
  } moreover {
    assume "?V e0"
    then obtain C0 es' where "e0 = (New C0 es')" and "vals(es')" by (force elim:val.cases)
    hence ?case by(force intro:isubexprs.intros)
  }
  ultimately show ?case by blast
qed

subsection \<open>Type Soundness Theorem\<close>     

theorem Thm_2_4_3: 
  assumes e_typ: "CT;Map.empty \<turnstile> e : C"
  and ct_ok: "CT OK"
  and multisteps: "CT \<turnstile> e \<rightarrow>* e1"
  and no_step: "\<not>(\<exists>e2. CT \<turnstile> e1 \<rightarrow> e2)"
  shows "(val(e1) \<and> (\<exists>D. CT;Map.empty \<turnstile> e1 : D \<and> CT \<turnstile> D <: C))
      \<or> (\<exists>D C es. (Cast D (New C es) \<in> subexprs(e1) \<and> CT \<turnstile> C \<not><: D))" 
proof -  
  from assms Cor_2_4_1_multi[OF multisteps ct_ok e_typ] obtain C1 
    where e1_typ: "CT;Map.empty \<turnstile> e1 : C1" 
    and C1_sub_C: "CT \<turnstile> C1 <: C" by auto
  from e1_typ have "((\<exists>C0 es fi. (FieldProj (New C0 es) fi) \<in> subexprs(e1))  
    \<or> (\<exists>C0 es m ds. (MethodInvk (New C0 es) m ds) \<in> subexprs(e1))
    \<or> (\<exists>C0 D es. (Cast D (New C0 es)) \<in> subexprs(e1))
    \<or> val(e1))" (is "?F e1 \<or> ?M e1 \<or> ?C e1 \<or> ?V e1")  by (simp add: closed_subterm_split)
  moreover 
  { assume "?F e1" 
    then obtain C0 es fi where fp: "FieldProj (New C0 es) fi \<in> subexprs(e1)" by auto
    then obtain Ci where "CT;Map.empty \<turnstile> FieldProj (New C0 es) fi : Ci" using e1_typ by(force simp add:subexpr_typing)
    then obtain C0' where new_typ: "CT;Map.empty \<turnstile> New C0 es : C0'" by (force elim: typing.cases)
    hence "C0 = C0'" by (auto elim:typing.cases)
    with new_typ obtain Df where f1: "fields(CT,C0) = Df" and lens: "length es = length Df" by(auto elim:typing.cases)
    from Thm_2_4_2_1[OF e1_typ fp] obtain Cf fDef 
      where f2: "fields(CT,C0) = Cf" 
      and lkup: "lookup Cf (\<lambda>fd. vdName fd = fi) = Some(fDef)" by force
    moreover from fields_functional[OF f1 ct_ok f2] lens have "length es = length Cf" by auto 
    moreover from lookup_index[OF lkup] obtain i where 
      "i<length Cf" 
      and "fDef = Cf ! i"
      and "(length Cf = length es) \<longrightarrow> lookup2 Cf es (\<lambda>fd. vdName fd = fi) = Some (es ! i)" by auto
    ultimately have "lookup2 Cf es (\<lambda>fd. vdName fd = fi) = Some (es!i)" by auto
    with f2 have "CT \<turnstile> FieldProj(New C0 es) fi \<rightarrow> (es!i)" by(auto intro:reduction.intros)
    with fp have "\<exists>e2. CT \<turnstile> e1 \<rightarrow> e2" by(simp add:subexpr_reduct)
    with no_step have ?thesis by auto 
  } moreover {
    assume "?M e1"
    then obtain C0 es m ds where mi:"MethodInvk (New C0 es) m ds \<in> subexprs(e1)" by auto
    then obtain D where "CT;Map.empty \<turnstile> MethodInvk (New C0 es) m ds : D" using e1_typ by(force simp add:subexpr_typing)
    then obtain C0' Es E 
      where m_typ: "CT;Map.empty \<turnstile> New C0 es : C0'" 
      and "mtype(CT,m,C0') = Es \<rightarrow> E"
      and "length ds = length Es"
      by (auto elim:typing.cases)
    from Thm_2_4_2_2[OF e1_typ mi] obtain xs e0 where mb: "mbody(CT, m, C0) = xs . e0" and "length xs = length ds" by auto
    hence "CT \<turnstile> (MethodInvk (New C0 es) m ds) \<rightarrow> (substs[xs[\<mapsto>]ds,this\<mapsto>(New C0 es)]e0)"  by(auto simp add:reduction.intros)
    with mi have "\<exists>e2. CT \<turnstile> e1 \<rightarrow> e2" by(simp add:subexpr_reduct)
    with no_step have ?thesis by auto 
  } moreover {
    assume "?C e1"
    then obtain C0 D es where c_def: "Cast D (New C0 es) \<in> subexprs(e1)" by auto
    then obtain D' where "CT;Map.empty \<turnstile> Cast D (New C0 es) : D'" using e1_typ by (force simp add:subexpr_typing)
    then obtain C0' where new_typ: "CT;Map.empty \<turnstile> New C0 es : C0'" and D_eq_D': "D = D'" by (auto elim:typing.cases)
    hence C0_eq_C0': "C0 = C0'" by(auto elim:typing.cases)
    hence ?thesis proof(cases "CT \<turnstile> C0 <: D")
      case True
      hence "CT \<turnstile> Cast D (New C0 es) \<rightarrow> (New C0 es)" by(auto simp add:reduction.intros)
      with c_def have "\<exists>e2. CT \<turnstile> e1 \<rightarrow> e2" by (simp add:subexpr_reduct)
      with no_step show ?thesis by auto
    next
      case False
      with c_def show ?thesis by auto
    qed
  } moreover {
    assume "?V e1"
    hence ?thesis using assms by(auto simp add:Cor_2_4_1_multi)
  } ultimately show ?thesis by blast
qed

end 
