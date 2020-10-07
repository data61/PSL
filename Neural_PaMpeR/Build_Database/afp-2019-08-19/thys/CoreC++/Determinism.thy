(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section \<open>Determinism Proof\<close>

theory Determinism
imports TypeSafe
begin

subsection\<open>Some lemmas\<close>

lemma maps_nth:
  "\<lbrakk>(E(xs [\<mapsto>] ys)) x = Some y; length xs = length ys; distinct xs\<rbrakk> 
  \<Longrightarrow> \<forall>i. x = xs!i \<and> i < length xs \<longrightarrow> y = ys!i"
proof (induct xs arbitrary: ys E)
  case Nil thus ?case by simp
next
  case (Cons x' xs')
  have map:"(E(x' # xs' [\<mapsto>] ys)) x = Some y"
    and length:"length (x'#xs') = length ys"
    and dist:"distinct (x'#xs')"
    and IH:"\<And>ys E. \<lbrakk>(E(xs' [\<mapsto>] ys)) x = Some y; length xs' = length ys; 
                     distinct xs'\<rbrakk> 
         \<Longrightarrow> \<forall>i. x = xs'!i \<and> i < length xs' \<longrightarrow> y = ys!i" by fact+
  from length obtain y' ys' where ys:"ys = y'#ys'" by(cases ys) auto
  { fix i assume x:"x = (x'#xs')!i" and i:"i < length(x'#xs')"
    have "y = ys!i"
    proof(cases i)
      case 0 with x map ys dist show ?thesis by simp
    next
      case (Suc n)
      with x i have x':"x = xs'!n" and n:"n < length xs'" by simp_all
      from map ys have map':"(E(x' \<mapsto> y')(xs' [\<mapsto>] ys')) x = Some y" by simp
      from length ys have length':"length xs' = length ys'" by simp
      from dist have dist':"distinct xs'" by simp
      from IH[OF map' length' dist'] 
      have "\<forall>i. x = xs'!i \<and> i < length xs' \<longrightarrow> y = ys'!i" .
      with x' n have "y = ys'!n" by simp
      with ys n Suc show ?thesis by simp
    qed }
  thus ?case by simp
qed


lemma nth_maps:"\<lbrakk>length pns = length Ts; distinct pns; i < length Ts\<rbrakk> 
  \<Longrightarrow> (E(pns [\<mapsto>] Ts)) (pns!i) = Some (Ts!i)"
proof (induct i arbitrary: E pns Ts)
  case 0
  have dist:"distinct pns" and length:"length pns = length Ts"
    and i_length:"0 < length Ts" by fact+
  from i_length obtain T' Ts' where Ts:"Ts = T'#Ts'" by(cases Ts) auto
  with length obtain p' pns' where "pns = p'#pns'" by(cases pns) auto
  with Ts dist show ?case by simp
next
  case (Suc n)
  have i_length:"Suc n < length Ts" and dist:"distinct pns"
    and length:"length pns = length Ts" by fact+
  from Suc obtain T' Ts' where Ts:"Ts = T'#Ts'" by(cases Ts) auto
  with length obtain p' pns' where pns:"pns = p'#pns'" by(cases pns) auto
  with Ts length dist have length':"length pns' = length Ts'" 
    and dist':"distinct pns'" and notin:"p' \<notin> set pns'" by simp_all
  from i_length Ts have n_length:"n < length Ts'" by simp
  with length' dist' have map:"(E(p' \<mapsto> T')(pns' [\<mapsto>] Ts')) (pns'!n) = Some(Ts'!n)" by fact
  with notin have "(E(p' \<mapsto> T')(pns' [\<mapsto>] Ts')) p' = Some T'" by simp
  with pns Ts map show ?case by simp
qed

lemma casts_casts_eq_result:
  fixes s :: state
  assumes casts:"P \<turnstile> T casts v to v'" and casts':"P \<turnstile> T casts v to w'" 
  and type:"is_type P T" and wte:"P,E \<turnstile> e :: T'" and leq:"P \<turnstile> T' \<le> T"
  and eval:"P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v,(h,l)\<rangle>" and sconf:"P,E \<turnstile> s \<surd>"
  and wf:"wf_C_prog P"
  shows "v' = w'"
proof(cases "\<forall>C. T \<noteq> Class C")
  case True
  with casts casts' show ?thesis
    by(auto elim:casts_to.cases)
next
  case False
  then obtain C where T:"T = Class C" by auto
  with type have "is_class P C" by simp
  with wf T leq have "T' = NT \<or> (\<exists>D. T' = Class D \<and> P \<turnstile> Path D to C unique)"
    by(simp add:widen_Class)
  thus ?thesis
  proof(rule disjE)
    assume "T' = NT"
    with wf eval sconf wte have "v = Null"
      by(fastforce dest:eval_preserves_type)
    with casts casts' show ?thesis by(fastforce elim:casts_to.cases)
  next
    assume "\<exists>D. T' = Class D \<and> P \<turnstile> Path D to C unique"
    then obtain D where T':"T' = Class D" 
      and path_unique:"P \<turnstile> Path D to C unique" by auto
    with wf eval sconf wte
    have "P,E,h \<turnstile> Val v : T' \<or> P,E,h \<turnstile> Val v : NT"
      by(fastforce dest:eval_preserves_type)
    thus ?thesis
    proof(rule disjE)
      assume "P,E,h \<turnstile> Val v : T'"
      with T' obtain a Cs C' S where h:"h a = Some(C',S)" and v:"v = Ref(a,Cs)"
        and last:"last Cs = D"
        by(fastforce dest:typeof_Class_Subo)
      from casts' v last T obtain Cs' Ds where "P \<turnstile> Path D to C via Cs'"
        and "Ds = Cs@\<^sub>pCs'" and "w' = Ref(a,Ds)"
        by(auto elim:casts_to.cases)
      with casts T v last path_unique show ?thesis
        by auto(erule casts_to.cases,auto simp:path_via_def path_unique_def)
    next
      assume "P,E,h \<turnstile> Val v : NT"
      with wf eval sconf wte have "v = Null"
        by(fastforce dest:eval_preserves_type)
      with casts casts' show ?thesis by(fastforce elim:casts_to.cases)
    qed
  qed
qed

lemma Casts_Casts_eq_result:
  assumes wf:"wf_C_prog P"
  shows "\<lbrakk>P \<turnstile> Ts Casts vs to vs'; P \<turnstile> Ts Casts vs to ws'; \<forall>T \<in> set Ts. is_type P T;
          P,E \<turnstile> es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts; P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h,l)\<rangle>;
          P,E \<turnstile> s \<surd>\<rbrakk>
      \<Longrightarrow> vs' = ws'"
proof (induct vs arbitrary: vs' ws' Ts Ts' es s)
  case Nil thus ?case by (auto elim!:Casts_to.cases)
next
  case (Cons x xs)
  have CastsCons:"P \<turnstile> Ts Casts x # xs to vs'" 
    and CastsCons':"P \<turnstile> Ts Casts x # xs to ws'"
    and type:"\<forall>T \<in> set Ts. is_type P T" 
    and wtes:"P,E \<turnstile> es [::] Ts'" and subs:"P \<turnstile> Ts' [\<le>] Ts"
    and evals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val (x#xs),(h,l)\<rangle>"
    and sconf:"P,E \<turnstile> s \<surd>"
    and IH:"\<And>vs' ws' Ts Ts' es s. 
    \<lbrakk>P \<turnstile> Ts Casts xs to vs'; P \<turnstile> Ts Casts xs to ws'; \<forall>T \<in> set Ts. is_type P T; 
     P,E \<turnstile> es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts; P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val xs,(h,l)\<rangle>;
     P,E \<turnstile> s \<surd>\<rbrakk> 
     \<Longrightarrow> vs' = ws'" by fact+
  from CastsCons obtain y ys S Ss where vs':"vs' = y#ys" and Ts:"Ts = S#Ss"
    apply -
    apply(frule length_Casts_vs,cases Ts,auto)
    apply(frule length_Casts_vs',cases vs',auto)
    done
  with CastsCons have casts:"P \<turnstile> S casts x to y" and Casts:"P \<turnstile> Ss Casts xs to ys"
    by(auto elim:Casts_to.cases)
  from Ts type have type':"is_type P S" and types':"\<forall>T \<in> set Ss. is_type P T"
    by auto
  from Ts CastsCons' obtain z zs where ws':"ws' = z#zs"
    by simp(frule length_Casts_vs',cases ws',auto)
  with Ts CastsCons' have casts':"P \<turnstile> S casts x to z" 
    and Casts':"P \<turnstile> Ss Casts xs to zs"
    by(auto elim:Casts_to.cases)
  from Ts subs obtain U Us where Ts':"Ts' = U#Us" and subs':"P \<turnstile> Us [\<le>] Ss"
    and sub:"P \<turnstile> U \<le> S" by(cases Ts',auto simp:fun_of_def)
  from wtes Ts' obtain e' es' where es:"es = e'#es'" and wte':"P,E \<turnstile> e' :: U"
    and wtes':"P,E \<turnstile> es' [::] Us" by(cases es) auto
  with evals obtain h' l' where eval:"P,E \<turnstile> \<langle>e',s\<rangle> \<Rightarrow> \<langle>Val x,(h',l')\<rangle>"
    and evals':"P,E \<turnstile> \<langle>es',(h',l')\<rangle> [\<Rightarrow>] \<langle>map Val xs,(h,l)\<rangle>"
    by (auto elim:evals.cases)
  from wf eval wte' sconf have "P,E \<turnstile> (h',l') \<surd>" by(rule eval_preserves_sconf)
  from IH[OF Casts Casts' types' wtes' subs' evals' this] have eq:"ys = zs" .
  from casts casts' type' wte' sub eval sconf wf have "y = z"
    by(rule casts_casts_eq_result)
  with eq vs' ws' show ?case by simp
qed



lemma Casts_conf: assumes wf: "wf_C_prog P"
  shows "P \<turnstile> Ts Casts vs to vs' \<Longrightarrow> 
  (\<And>es s Ts'. \<lbrakk> P,E \<turnstile> es [::] Ts'; P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h,l)\<rangle>; P,E \<turnstile> s \<surd>;
             P \<turnstile> Ts' [\<le>] Ts\<rbrakk> \<Longrightarrow> 
     \<forall>i < length Ts. P,h \<turnstile> vs'!i :\<le> Ts!i)"
proof(induct rule:Casts_to.induct)
  case Casts_Nil thus ?case by simp
next
  case (Casts_Cons T v v' Ts vs vs')
  have casts:"P \<turnstile> T casts v to v'" and wtes:"P,E \<turnstile> es [::] Ts'" 
    and evals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val (v#vs),(h,l)\<rangle>"
    and subs:"P \<turnstile> Ts' [\<le>] (T#Ts)" and sconf:"P,E \<turnstile> s \<surd>"
    and IH:"\<And>es s Ts'.\<lbrakk>P,E \<turnstile> es [::] Ts'; P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h,l)\<rangle>; 
                   P,E \<turnstile> s \<surd>; P \<turnstile> Ts' [\<le>] Ts\<rbrakk>
               \<Longrightarrow> \<forall>i<length Ts. P,h \<turnstile> vs' ! i :\<le> Ts ! i" by fact+
  from subs obtain U Us where Ts':"Ts' = U#Us" by(cases Ts') auto
  with subs have sub':"P \<turnstile> U \<le> T" and subs':"P \<turnstile> Us [\<le>] Ts" 
    by (simp_all add:fun_of_def)
  from wtes Ts' obtain e' es' where es:"es = e'#es'" by(cases es) auto
  with Ts' wtes have wte':"P,E \<turnstile> e' :: U" and wtes':"P,E \<turnstile> es' [::] Us" by auto
  from es evals obtain s' where eval':"P,E \<turnstile> \<langle>e',s\<rangle> \<Rightarrow> \<langle>Val v,s'\<rangle>"
    and evals':"P,E \<turnstile> \<langle>es',s'\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h,l)\<rangle>" 
    by(auto elim:evals.cases)
  from wf eval' wte' sconf have sconf':"P,E \<turnstile> s' \<surd>" by(rule eval_preserves_sconf)
  from evals' have hext:"hp s' \<unlhd> h" by(cases s',auto intro:evals_hext)
  from wf eval' sconf wte' have "P,E,(hp s') \<turnstile> Val v :\<^bsub>NT\<^esub> U"
    by(rule eval_preserves_type)
  with hext have wtrt:"P,E,h \<turnstile> Val v :\<^bsub>NT\<^esub> U"
    by(cases U,auto intro:hext_typeof_mono)
  from casts wtrt sub' have "P,h \<turnstile> v' :\<le> T"
  proof(induct rule:casts_to.induct)
    case (casts_prim T'' v'')
    have "\<forall>C. T'' \<noteq> Class C" and "P,E,h \<turnstile> Val v'' :\<^bsub>NT\<^esub> U" and "P \<turnstile> U \<le> T''" by fact+
    thus ?case by(cases T'') auto
  next
    case (casts_null C) thus ?case by simp
  next
    case (casts_ref Cs C Cs' Ds a)
    have path:"P \<turnstile> Path last Cs to C via Cs'"
      and Ds:"Ds = Cs @\<^sub>p Cs'"
      and wtref:"P,E,h \<turnstile> ref (a, Cs) :\<^bsub>NT\<^esub> U" by fact+
    from wtref obtain D S where subo:"Subobjs P D Cs" and h:"h a = Some(D,S)"
      by(cases U,auto split:if_split_asm)
    from path Ds have last:"C = last Ds"  
      by(fastforce intro!:appendPath_last Subobjs_nonempty simp:path_via_def)
    from subo path Ds wf have "Subobjs P D Ds"
      by(fastforce intro:Subobjs_appendPath simp:path_via_def)
    with last h show ?case by simp
  qed
  with IH[OF wtes' evals' sconf' subs'] show ?case
    by(auto simp:nth_Cons,case_tac i,auto)
qed


lemma map_Val_throw_False:"map Val vs = map Val ws @ throw ex # es \<Longrightarrow> False"
proof (induct vs arbitrary: ws)
  case Nil thus ?case by simp
next
  case (Cons v' vs')
  have eq:"map Val (v'#vs') = map Val ws @ throw ex # es"
    and IH:"\<And>ws'. map Val vs' = map Val ws' @ throw ex # es \<Longrightarrow> False" by fact+
  from eq obtain w' ws' where ws:"ws = w'#ws'" by(cases ws) auto
  from eq have "tl(map Val (v'#vs')) = tl(map Val ws @ throw ex # es)" by simp
  hence "map Val vs' = tl(map Val ws @ throw ex # es)" by simp
  with ws have "map Val vs' = map Val ws' @ throw ex # es" by simp
  from IH[OF this] show ?case .
qed

lemma map_Val_throw_eq:"map Val vs @ throw ex # es = map Val ws @ throw ex' # es' 
  \<Longrightarrow> vs = ws \<and> ex = ex' \<and> es = es'"
  apply(clarsimp simp:append_eq_append_conv2)
  apply(erule disjE)
   apply(case_tac us)
    apply(fastforce elim:map_injective simp:inj_on_def)
   apply(fastforce dest:map_Val_throw_False)
  apply(case_tac us)
   apply(fastforce elim:map_injective simp:inj_on_def)
  apply(fastforce dest:sym[THEN map_Val_throw_False])
  done


subsection \<open>The proof\<close>

lemma deterministic_big_step:
assumes wf:"wf_C_prog P"
shows "P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Longrightarrow> 
       (\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s \<surd>\<rbrakk> 
       \<Longrightarrow> e\<^sub>1 = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2)"
  and "P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es\<^sub>1,s\<^sub>1\<rangle> \<Longrightarrow> 
       (\<And>es\<^sub>2 s\<^sub>2 Ts. \<lbrakk>P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> es [::] Ts; P,E \<turnstile> s \<surd>\<rbrakk> 
        \<Longrightarrow> es\<^sub>1 = es\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2)"
proof (induct rule:eval_evals.inducts)
  case New thus ?case by(auto elim: eval_cases)
next
  case NewFail thus ?case by(auto elim: eval_cases)
next
  case (StaticUpCast E e s\<^sub>0 a Cs s\<^sub>1 C Cs' Ds e\<^sub>2 s\<^sub>2)
  have eval:"P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and path_via:"P \<turnstile> Path last Cs to C via Cs'" and Ds:"Ds = Cs @\<^sub>p Cs'" 
    and wt:"P,E \<turnstile> \<lparr>C\<rparr>e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
            \<Longrightarrow> ref (a,Cs) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where "class":"is_class P C" and wte:"P,E \<turnstile> e :: Class D"
    and disj:"P \<turnstile> Path D to C unique \<or> 
              (P \<turnstile> C \<preceq>\<^sup>* D \<and> (\<forall>Cs. P \<turnstile> Path C to D via Cs \<longrightarrow> Subobjs\<^sub>R P C Cs))"
    by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a',Xs),s\<^sub>2\<rangle>" 
      and path_via':"P \<turnstile> Path last Xs to C via Xs'"
      and ref:"e\<^sub>2 = ref (a',Xs@\<^sub>pXs')"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs \<and> s\<^sub>1 = s\<^sub>2" by simp
    with wf eval_ref sconf wte have last:"last Cs = D"
      by(auto dest:eval_preserves_type split:if_split_asm)
    from disj show "ref (a,Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2"
    proof (rule disjE)
      assume "P \<turnstile> Path D to C unique"
      with path_via path_via' eq last have "Cs' = Xs'"
        by(fastforce simp add:path_via_def path_unique_def)
      with eq ref Ds show ?thesis by simp
    next
      assume "P \<turnstile> C \<preceq>\<^sup>* D \<and> (\<forall>Cs. P \<turnstile> Path C to D via Cs  \<longrightarrow> Subobjs\<^sub>R P C Cs)"
      with "class" wf obtain Cs'' where "P \<turnstile> Path C to D via Cs''"
        by(auto dest:leq_implies_path)
      with path_via path_via' wf eq last have "Cs' = Xs'"
        by(auto dest:path_via_reverse)
      with eq ref Ds show ?thesis by simp
    qed
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
      and ref:"e\<^sub>2 = ref (a',Xs@[C])"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs@C#Xs' \<and> s\<^sub>1 = s\<^sub>2" by simp
    with wf eval_ref sconf wte obtain C' where 
      last:"last Cs = D" and "Subobjs P C' (Xs@C#Xs')"
      by(auto dest:eval_preserves_type split:if_split_asm)
    hence subo:"Subobjs P C (C#Xs')" by(fastforce intro:Subobjs_Subobjs)
    with eq last have leq:"P \<turnstile> C \<preceq>\<^sup>* D" by(fastforce dest:Subobjs_subclass)
    from path_via last have "P \<turnstile> D \<preceq>\<^sup>* C"
      by(auto dest:Subobjs_subclass simp:path_via_def)
    with leq wf have CeqD:"C = D" by(rule subcls_asym2)
    with last path_via wf have "Cs' = [D]" by(fastforce intro:path_via_C)
    with Ds last have Ds':"Ds = Cs" by(simp add:appendPath_def)
    from subo CeqD last eq wf have "Xs' = []" by(auto dest:mdc_eq_last)
    with eq Ds' ref show "ref (a,Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "ref (a,Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>" and notin:"C \<notin> set Xs"
      and notleq:"\<not> P \<turnstile> last Xs \<preceq>\<^sup>* C" and throw:"e\<^sub>2 = THROW ClassCast"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs \<and> s\<^sub>1 = s\<^sub>2" by simp
    with wf eval_ref sconf wte have last:"last Cs = D" and notempty:"Cs \<noteq> []"
      by(auto dest!:eval_preserves_type Subobjs_nonempty split:if_split_asm)
    from disj have "C = D"
    proof(rule disjE)
      assume path_unique:"P \<turnstile> Path D to C unique"
      with last have "P \<turnstile> D \<preceq>\<^sup>* C" 
        by(fastforce dest:Subobjs_subclass simp:path_unique_def)
      with notleq last eq show ?thesis by simp
    next
      assume ass:"P \<turnstile> C \<preceq>\<^sup>* D \<and> 
                  (\<forall>Cs. P \<turnstile> Path C to D via Cs  \<longrightarrow> Subobjs\<^sub>R P C Cs)"
      with "class" wf obtain Cs'' where path_via':"P \<turnstile> Path C to D via Cs''"
        by(auto dest:leq_implies_path)
      with path_via wf eq last have "Cs'' = [D]"
        by(fastforce dest:path_via_reverse)
      with ass path_via' have "Subobjs\<^sub>R P C [D]" by simp
      thus ?thesis by(fastforce dest:hd_SubobjsR)
    qed
    with last notin eq notempty show "ref (a,Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2"
      by(fastforce intro:last_in_set)
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "ref (a,Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (StaticDownCast E e s\<^sub>0 a Cs C Cs' s\<^sub>1 e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>" 
    and eval':"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs@[C]@Cs'),s\<^sub>1\<rangle>"
    and wt:"P,E \<turnstile> \<lparr>C\<rparr>e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                      \<Longrightarrow> ref(a,Cs@[C]@Cs') = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where wte:"P,E \<turnstile> e :: Class D"
    and disj:"P \<turnstile> Path D to C unique \<or> 
              (P \<turnstile> C \<preceq>\<^sup>* D \<and> (\<forall>Cs. P \<turnstile> Path C to D via Cs \<longrightarrow> Subobjs\<^sub>R P C Cs))"
    by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>" 
      and path_via:"P \<turnstile> Path last Xs to C via Xs'"
      and ref:"e\<^sub>2 = ref (a',Xs@\<^sub>pXs')"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs@[C]@Cs' = Xs \<and> s\<^sub>1 = s\<^sub>2"
      by simp
    with wf eval_ref sconf wte obtain C' where 
      last:"last(C#Cs') = D" and "Subobjs P C' (Cs@[C]@Cs')"
      by(auto dest:eval_preserves_type split:if_split_asm)
    hence "P \<turnstile> Path C to D via C#Cs'" 
      by(fastforce intro:Subobjs_Subobjs simp:path_via_def)
    with eq last path_via wf have "Xs' = [C] \<and> Cs' = [] \<and> C = D"
      apply clarsimp
      apply(split if_split_asm)
      by(simp,drule path_via_reverse,simp,simp)+
    with ref eq show "ref(a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by(fastforce simp:appendPath_def)
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
      and ref:"e\<^sub>2 = ref (a',Xs@[C])"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs@[C]@Cs' = Xs@C#Xs' \<and> s\<^sub>1 = s\<^sub>2"
      by simp
    with wf eval_ref sconf wte obtain C' where 
      last:"last(C#Xs') = D" and subo:"Subobjs P C' (Cs@[C]@Cs')"
      by(auto dest:eval_preserves_type split:if_split_asm)
    from subo wf have notin:"C \<notin> set Cs" by -(rule unique2,simp)
    from subo wf have "C \<notin> set Cs'"  by -(rule unique1,simp,simp)
    with notin eq have "Cs = Xs \<and> Cs' = Xs'"
      by -(rule only_one_append,simp+)
    with eq ref show "ref(a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "ref (a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs a' 
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>" and notin:"C \<notin> set Xs"
    from IH[OF eval_ref wte sconf] have "a = a' \<and> Cs@[C]@Cs' = Xs \<and> s\<^sub>1 = s\<^sub>2" 
      by simp
    with notin show "ref(a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fastforce
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "ref (a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (StaticCastNull E e s\<^sub>0 s\<^sub>1 C e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> \<lparr>C\<rparr>e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where wte:"P,E \<turnstile> e :: Class D" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a',Xs),s\<^sub>2\<rangle>" 
    from IH[OF eval_ref wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>" and "e\<^sub>2 = null"
    with IH[OF eval_null wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs a' 
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (StaticCastFail E e s\<^sub>0 a Cs s\<^sub>1 C e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and notleq:"\<not> P \<turnstile> last Cs \<preceq>\<^sup>* C" and notin:"C \<notin> set Cs"
    and wt:"P,E \<turnstile> \<lparr>C\<rparr>e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow>ref (a, Cs) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where wte:"P,E \<turnstile> e :: Class D" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a',Xs),s\<^sub>2\<rangle>" 
      and path_via:"P \<turnstile> Path last Xs to C via Xs'"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs \<and> s\<^sub>1 = s\<^sub>2" by simp
    with path_via wf have "P \<turnstile> last Cs \<preceq>\<^sup>* C" 
      by(auto dest:Subobjs_subclass simp:path_via_def)
    with notleq show "THROW ClassCast = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] have "a = a' \<and> Cs = Xs@C#Xs' \<and> s\<^sub>1 = s\<^sub>2" by simp
    with notin show "THROW ClassCast = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "THROW ClassCast = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs a' 
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>"
      and throw:"e\<^sub>2 = THROW ClassCast"
    from IH[OF eval_ref wte sconf] have "a = a' \<and> Cs = Xs \<and> s\<^sub>1 = s\<^sub>2"
      by simp
    with throw show "THROW ClassCast = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "THROW ClassCast = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed 
next
  case (StaticCastThrow E e s\<^sub>0 e' s\<^sub>1 C e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> \<lparr>C\<rparr>e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                   \<Longrightarrow> throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where wte:"P,E \<turnstile> e :: Class D" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a',Xs),s\<^sub>2\<rangle>" 
    from IH[OF eval_ref wte sconf] show " throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix e'' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e'',s\<^sub>2\<rangle>"
      and throw:"e\<^sub>2 = throw e''"
    from IH[OF eval_throw wte sconf] throw show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (StaticUpDynCast E e s\<^sub>0 a Cs s\<^sub>1 C Cs' Ds e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and path_via:"P \<turnstile> Path last Cs to C via Cs'" 
    and path_unique:"P \<turnstile> Path last Cs to C unique"
    and Ds:"Ds = Cs@\<^sub>pCs'" and wt:"P,E \<turnstile> Cast C e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> ref(a,Cs) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where wte:"P,E \<turnstile> e :: Class D" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a',Xs),s\<^sub>2\<rangle>" 
      and path_via':"P \<turnstile> Path last Xs to C via Xs'"
      and ref:"e\<^sub>2 = ref (a',Xs@\<^sub>pXs')"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs \<and> s\<^sub>1 = s\<^sub>2" by simp
    with wf eval_ref sconf wte have last:"last Cs = D"
      by(auto dest:eval_preserves_type split:if_split_asm)
    with path_unique path_via path_via' eq have "Xs' = Cs'"
      by(fastforce simp:path_via_def path_unique_def)
    with eq Ds ref show "ref (a, Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
      and ref:"e\<^sub>2 = ref (a',Xs@[C])"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs@C#Xs' \<and> s\<^sub>1 = s\<^sub>2" by simp
    with wf eval_ref sconf wte obtain C' where 
      last:"last Cs = D" and "Subobjs P C' (Xs@C#Xs')"
      by(auto dest:eval_preserves_type split:if_split_asm)
    hence "Subobjs P C (C#Xs')" by(fastforce intro:Subobjs_Subobjs)
    with last eq have "P \<turnstile> Path C to D via C#Xs'" 
      by(simp add:path_via_def)
    with path_via wf last have "Xs' = [] \<and> Cs' = [C] \<and> C = D" 
      by(fastforce dest:path_via_reverse)
    with eq Ds ref show "ref (a, Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by (simp add:appendPath_def)
  next
    fix Xs Xs' D' S a' h l
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h,l)\<rangle>"
      and h:"h a' = Some(D',S)" and path_via':"P \<turnstile> Path D' to C via Xs'"
      and path_unique':"P \<turnstile> Path D' to C unique" and s2:"s\<^sub>2 = (h,l)"
      and ref:"e\<^sub>2 = ref(a',Xs')"
    from IH[OF eval_ref wte sconf] s2 have eq:"a = a' \<and> Cs = Xs \<and> s\<^sub>1 = s\<^sub>2" by simp
    with wf eval_ref sconf wte h have "last Cs = D"
      and "Subobjs P D' Cs"
      by(auto dest:eval_preserves_type split:if_split_asm)
    with path_via wf have "P \<turnstile> Path D' to C via Cs@\<^sub>pCs'"
      by(fastforce intro:Subobjs_appendPath appendPath_last[THEN sym] 
                   dest:Subobjs_nonempty simp:path_via_def)
    with path_via' path_unique' Ds have "Xs' = Ds"
      by(fastforce simp:path_via_def path_unique_def)
    with eq ref show "ref (a, Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "ref (a, Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs D' S a' h l
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h,l)\<rangle>"
      and not_unique:"\<not> P \<turnstile> Path last Xs to C unique" and s2:"s\<^sub>2 = (h,l)"
    from IH[OF eval_ref wte sconf] s2 have eq:"a = a' \<and> Cs = Xs \<and> s\<^sub>1 = s\<^sub>2" by simp
    with path_unique not_unique show "ref (a, Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "ref (a, Ds) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (StaticDownDynCast E e s\<^sub>0 a Cs C Cs' s\<^sub>1 e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> Cast C e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> ref(a,Cs@[C]@Cs') = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where wte:"P,E \<turnstile> e :: Class D" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>" 
      and path_via:"P \<turnstile> Path last Xs to C via Xs'"
      and ref:"e\<^sub>2 = ref (a',Xs@\<^sub>pXs')"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs@[C]@Cs' = Xs \<and> s\<^sub>1 = s\<^sub>2"
      by simp
    with wf eval_ref sconf wte obtain C' where 
      last:"last(C#Cs') = D" and "Subobjs P C' (Cs@[C]@Cs')"
      by(auto dest:eval_preserves_type split:if_split_asm)
    hence "P \<turnstile> Path C to D via C#Cs'" 
      by(fastforce intro:Subobjs_Subobjs simp:path_via_def)
    with eq last path_via wf have "Xs' = [C] \<and> Cs' = [] \<and> C = D"
      apply clarsimp
      apply(split if_split_asm)
      by(simp,drule path_via_reverse,simp,simp)+
    with ref eq show "ref(a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by(fastforce simp:appendPath_def)
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
      and ref:"e\<^sub>2 = ref (a',Xs@[C])"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs@[C]@Cs' = Xs@C#Xs' \<and> s\<^sub>1 = s\<^sub>2"
      by simp
    with wf eval_ref sconf wte obtain C' where 
      last:"last(C#Xs') = D" and subo:"Subobjs P C' (Cs@[C]@Cs')"
      by(auto dest:eval_preserves_type split:if_split_asm)
    from subo wf have notin:"C \<notin> set Cs" by -(rule unique2,simp)
    from subo wf have "C \<notin> set Cs'"  by -(rule unique1,simp,simp)
    with notin eq have "Cs = Xs \<and> Cs' = Xs'"
      by -(rule only_one_append,simp+)
    with eq ref show "ref(a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' D' S a' h l
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h,l)\<rangle>"
      and h:"h a' = Some(D',S)" and path_via:"P \<turnstile> Path D' to C via Xs'"
      and path_unique:"P \<turnstile> Path D' to C unique" and s2:"s\<^sub>2 = (h,l)"
      and ref:"e\<^sub>2 = ref(a',Xs')"
    from IH[OF eval_ref wte sconf] s2 have eq:"a = a' \<and> Cs@[C]@Cs' = Xs \<and> s\<^sub>1 = s\<^sub>2"
      by simp
    with wf eval_ref sconf wte h have "Subobjs P D' (Cs@[C]@Cs')"
      by(auto dest:eval_preserves_type split:if_split_asm)
    hence "Subobjs P D' (Cs@[C])" by(fastforce intro:appendSubobj)
    with path_via path_unique have "Xs' = Cs@[C]" 
      by(fastforce simp:path_via_def path_unique_def)
    with eq ref show "ref(a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "ref (a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs D' S a' h l
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h,l)\<rangle>"
      and notin:"C \<notin> set Xs" and s2:"s\<^sub>2 = (h,l)"
    from IH[OF eval_ref wte sconf] s2 have "a = a' \<and> Cs@[C]@Cs' = Xs \<and> s\<^sub>1 = s\<^sub>2"
      by simp
    with notin show "ref (a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fastforce
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "ref (a,Cs@[C]) = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (DynCast E e s\<^sub>0 a Cs h l D S C Cs' e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and path_via:"P \<turnstile> Path D to C via Cs'" and path_unique:"P \<turnstile> Path D to C unique"
    and h:"h a = Some(D,S)" and wt:"P,E \<turnstile> Cast C e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> ref(a,Cs) = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by fact+
  from wt obtain D' where wte:"P,E \<turnstile> e :: Class D'" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>"
      and path_via':"P \<turnstile> Path last Xs to C via Xs'"
      and ref:"e\<^sub>2 = ref (a',Xs@\<^sub>pXs')"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs \<and> (h,l) = s\<^sub>2" by simp
    with wf eval_ref sconf wte h have "last Cs = D'"
      and "Subobjs P D Cs"
      by(auto dest:eval_preserves_type split:if_split_asm)
    with path_via' wf eq have "P \<turnstile> Path D to C via Xs@\<^sub>pXs'"
      by(fastforce intro:Subobjs_appendPath appendPath_last[THEN sym] 
                   dest:Subobjs_nonempty simp:path_via_def)
    with path_via path_unique have "Cs' = Xs@\<^sub>pXs'"
      by(fastforce simp:path_via_def path_unique_def)
    with ref eq show "ref(a,Cs') = e\<^sub>2 \<and> (h, l) = s\<^sub>2" by simp
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
      and ref:"e\<^sub>2 = ref (a',Xs@[C])"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs@C#Xs' \<and> (h,l) = s\<^sub>2"
      by simp
    with wf eval_ref sconf wte h have "Subobjs P D (Xs@[C]@Xs')"
      by(auto dest:eval_preserves_type split:if_split_asm)
    hence "Subobjs P D (Xs@[C])" by(fastforce intro:appendSubobj)
    with path_via path_unique have "Cs' = Xs@[C]" 
      by(fastforce simp:path_via_def path_unique_def)
    with eq ref show "ref(a,Cs') = e\<^sub>2 \<and> (h, l) = s\<^sub>2" by simp
  next
    fix Xs Xs' D'' S' a' h' l'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h',l')\<rangle>"
      and h':"h' a' = Some(D'',S')" and path_via':"P \<turnstile> Path D'' to C via Xs'"
      and s2:"s\<^sub>2 = (h',l')" and ref:"e\<^sub>2 = ref(a',Xs')"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs \<and> h = h' \<and> l = l'"
      by simp
    with h h' path_via path_via' path_unique s2 ref
    show "ref(a,Cs') = e\<^sub>2 \<and> (h,l) = s\<^sub>2"
      by(fastforce simp:path_via_def path_unique_def)
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "ref(a,Cs') = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  next
    fix Xs D'' S' a' h' l'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h',l')\<rangle>"
      and h':"h' a' = Some(D'',S')" and not_unique:"\<not> P \<turnstile> Path D'' to C unique"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs \<and> h = h' \<and> l = l'"
      by simp
    with h h' path_unique not_unique show "ref(a,Cs') = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "ref (a,Cs') = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  qed
next
  case (DynCastNull E e s\<^sub>0 s\<^sub>1 C e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> Cast C e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where wte:"P,E \<turnstile> e :: Class D" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a',Xs),s\<^sub>2\<rangle>" 
    from IH[OF eval_ref wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' D' S a' h l
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h,l)\<rangle>"
    from IH[OF eval_ref wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>" and "e\<^sub>2 = null"
    with IH[OF eval_null wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs D' S a' h l
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h,l)\<rangle>" and s2:"s\<^sub>2 = (h,l)"
    from IH[OF eval_ref wte sconf] s2 show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (DynCastFail E e s\<^sub>0 a Cs h l D S C e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and h:"h a = Some(D,S)" and not_unique1:"\<not> P \<turnstile> Path D to C unique"
    and not_unique2:"\<not> P \<turnstile> Path last Cs to C unique" and notin:"C \<notin> set Cs"
    and wt:"P,E \<turnstile> Cast C e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                   \<Longrightarrow> ref (a, Cs) = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by fact+
  from wt obtain D' where wte:"P,E \<turnstile> e :: Class D'" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<^sub>2\<rangle>"
      and path_unique:"P \<turnstile> Path last Xs to C unique"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs \<and> (h,l) = s\<^sub>2" by simp
    with path_unique not_unique2 show "null = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] have eq:"a = a' \<and> Cs = Xs@C#Xs' \<and> (h,l) = s\<^sub>2"
      by simp
    with notin show "null = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by fastforce
  next
    fix Xs Xs' D'' S' a' h' l'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h',l')\<rangle>"
      and h':"h' a' = Some(D'',S')" and path_unique:"P \<turnstile> Path D'' to C unique"
    from IH[OF eval_ref wte sconf] have "a = a' \<and> Cs = Xs \<and> h = h' \<and> l = l'"
      by simp
    with h h' not_unique1 path_unique show "null = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "null = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  next
    fix Xs D'' S' a' h' l'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h',l')\<rangle>"
      and null:"e\<^sub>2 = null" and s2:"s\<^sub>2 = (h',l')"
    from IH[OF eval_ref wte sconf] null s2 show "null = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "null = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  qed
next
  case (DynCastThrow E e s\<^sub>0 e' s\<^sub>1 C e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> Cast C e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                   \<Longrightarrow> throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain D where wte:"P,E \<turnstile> e :: Class D" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a',Xs),s\<^sub>2\<rangle>" 
    from IH[OF eval_ref wte sconf] show " throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' a'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs@C#Xs'),s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs Xs' D'' S' a' h' l'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h',l')\<rangle>"
    from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix Xs D'' S' a' h' l'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),(h',l')\<rangle>"
    from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix e'' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e'',s\<^sub>2\<rangle>"
      and throw:"e\<^sub>2 = throw e''"
    from IH[OF eval_throw wte sconf] throw show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case Val thus ?case by(auto elim: eval_cases)
next
  case (BinOp E e\<^sub>1 s\<^sub>0 v\<^sub>1 s\<^sub>1 e\<^sub>2 v\<^sub>2 s\<^sub>2 bop v e\<^sub>2' s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    and binop:"binop (bop, v\<^sub>1, v\<^sub>2) = Some v"
    and wt:"P,E \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                     \<Longrightarrow> Val v\<^sub>1 = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>2 :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                     \<Longrightarrow> Val v\<^sub>2 = ei \<and> s\<^sub>2 = si" by fact+
  from wt obtain T\<^sub>1 T\<^sub>2 where wte1:"P,E \<turnstile> e\<^sub>1 :: T\<^sub>1" and wte2:"P,E \<turnstile> e\<^sub>2 :: T\<^sub>2"
    by auto
  from eval show ?case
  proof(rule eval_cases)
    fix s w w\<^sub>1 w\<^sub>2
    assume eval_val1:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w\<^sub>1,s\<rangle>"
      and eval_val2:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>Val w\<^sub>2,s\<^sub>2'\<rangle>"
      and binop':"binop(bop,w\<^sub>1,w\<^sub>2) = Some w" and e2':"e\<^sub>2' = Val w"
    from IH1[OF eval_val1 wte1 sconf] have w1:"v\<^sub>1 = w\<^sub>1" and s:"s = s\<^sub>1" by simp_all
    with wf eval_val1 wte1 sconf have "P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_val2[simplified s] wte2 this] have "v\<^sub>2 = w\<^sub>2" and s2:"s\<^sub>2 = s\<^sub>2'"
      by simp_all
    with w1 binop binop' have "w = v" by simp
    with e2' s2 show "Val v = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix e assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2'\<rangle>"
    from IH1[OF eval_throw wte1 sconf] show "Val v = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix e s w 
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
      and eval_throw:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2'\<rangle>"
    from IH1[OF eval_val wte1 sconf] have s:"s = s\<^sub>1" by simp_all
    with wf eval_val wte1 sconf have "P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_throw[simplified s] wte2 this] show "Val v = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'"
      by simp
  qed
next
  case (BinOpThrow1 E e\<^sub>1 s\<^sub>0 e s\<^sub>1 bop e\<^sub>2 e\<^sub>2' s\<^sub>2 T)
   have eval:"P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2\<rangle>"
     and wt:"P,E \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
     and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                     \<Longrightarrow> throw e = ei \<and> s\<^sub>1 = si" by fact+
   from wt obtain T\<^sub>1 T\<^sub>2 where wte1:"P,E \<turnstile> e\<^sub>1 :: T\<^sub>1" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix s w w\<^sub>1 w\<^sub>2
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w\<^sub>1,s\<rangle>"
    from IH[OF eval_val wte1 sconf] show "throw e = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix e' 
    assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>" and throw:"e\<^sub>2' = throw e'"
    from IH[OF eval_throw wte1 sconf] throw show "throw e = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix e s w 
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
    from IH[OF eval_val wte1 sconf] show "throw e = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (BinOpThrow2 E e\<^sub>1 s\<^sub>0 v\<^sub>1 s\<^sub>1 e\<^sub>2 e s\<^sub>2 bop e\<^sub>2' s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> Val v\<^sub>1 = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>2 :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                    \<Longrightarrow> throw e = ei \<and> s\<^sub>2 = si" by fact+
  from wt obtain T\<^sub>1 T\<^sub>2 where wte1:"P,E \<turnstile> e\<^sub>1 :: T\<^sub>1" and wte2:"P,E \<turnstile> e\<^sub>2 :: T\<^sub>2"
    by auto
  from eval show ?case
  proof(rule eval_cases)
    fix s w w\<^sub>1 w\<^sub>2
    assume eval_val1:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w\<^sub>1,s\<rangle>"
      and eval_val2:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>Val w\<^sub>2,s\<^sub>2'\<rangle>"
    from IH1[OF eval_val1 wte1 sconf] have s:"s = s\<^sub>1" by simp_all
    with wf eval_val1 wte1 sconf have "P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_val2[simplified s] wte2 this] show "throw e = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'"
      by simp
  next
    fix e' 
    assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2'\<rangle>"
    from IH1[OF eval_throw wte1 sconf] show "throw e = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix e' s w 
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
      and eval_throw:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2'\<rangle>"
      and throw:"e\<^sub>2' = throw e'"
    from IH1[OF eval_val wte1 sconf] have s:"s = s\<^sub>1" by simp_all
    with wf eval_val wte1 sconf have "P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_throw[simplified s] wte2 this] throw
    show "throw e = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'"
      by simp
  qed
next
  case Var thus ?case by(auto elim: eval_cases)    
next
  case (LAss E e s\<^sub>0 v h l V T v' l' e\<^sub>2 s\<^sub>2 T')
  have eval:"P,E \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and env:"E V = Some T" and casts:"P \<turnstile> T casts v to v'" and l':"l' = l(V \<mapsto> v')"
    and wt:"P,E \<turnstile> V:=e :: T'" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> Val v = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by fact+
  from wt env obtain T'' where wte:"P,E \<turnstile> e :: T''" and leq:"P \<turnstile> T'' \<le> T" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix U h' l'' w w'
    assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,(h',l'')\<rangle>" and env':"E V = Some U"
      and casts':"P \<turnstile> U casts w to w'" and e2:"e\<^sub>2 = Val w'" 
      and s2:"s\<^sub>2 = (h',l''(V \<mapsto> w'))"
    from env env' have UeqT:"U = T" by simp
    from IH[OF eval_val wte sconf] have eq:"v = w \<and> h = h' \<and> l = l''" by simp
    from sconf env have "is_type P T"
      by(clarsimp simp:sconf_def envconf_def)
    with casts casts' eq UeqT wte leq eval_val sconf wf have "v' = w'"
      by(auto intro:casts_casts_eq_result)
    with e2 s2 l' eq show "Val v' = e\<^sub>2 \<and> (h, l') = s\<^sub>2" by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "Val v' = e\<^sub>2 \<and> (h, l') = s\<^sub>2" by simp
  qed
next
  case (LAssThrow E e s\<^sub>0 e' s\<^sub>1 V e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> V:=e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain T'' where wte:"P,E \<turnstile> e :: T''" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix U h' l'' w w'
    assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,(h',l'')\<rangle>"
    from IH[OF eval_val wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex 
    assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = throw ex"
    from IH[OF eval_throw wte sconf] e2 show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (FAcc E e s\<^sub>0 a Cs' h l D S Ds Cs fs F v e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and eval':"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref (a, Cs'),(h,l)\<rangle>"
    and h:"h a = Some(D,S)" and Ds:"Ds = Cs'@\<^sub>pCs"
    and S:"(Ds,fs) \<in> S" and fs:"fs F = Some v"
    and wt:"P,E \<turnstile> e\<bullet>F{Cs} :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> ref (a, Cs') = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by fact+
  from wt obtain C where wte:"P,E \<turnstile> e :: Class C" by auto
  from eval_preserves_sconf[OF wf eval' wte sconf] h have oconf:"P,h \<turnstile> (D,S) \<surd>"
    by(simp add:sconf_def hconf_def)
  from eval show ?case
  proof(rule eval_cases)
    fix Xs' D' S' a' fs' h' l' v'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs'),(h',l')\<rangle>"
    and h':"h' a' = Some(D',S')" and S':"(Xs'@\<^sub>pCs,fs') \<in> S'"
    and fs':"fs' F = Some v'" and e2:"e\<^sub>2 = Val v'" and s2:"s\<^sub>2 = (h',l')"
    from IH[OF eval_ref wte sconf] h h'
    have eq:"a = a' \<and> Cs' = Xs' \<and> h = h' \<and> l = l' \<and> D = D' \<and> S = S'" by simp
    with oconf S S' Ds have "fs = fs'" by (auto simp:oconf_def)
    with fs fs' have "v = v'" by simp
    with e2 s2 eq show "Val v = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "Val v = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "Val v = e\<^sub>2 \<and> (h,l) = s\<^sub>2" by simp
  qed
next
  case (FAccNull E e s\<^sub>0 s\<^sub>1 F Cs e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> e\<bullet>F{Cs} :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> null = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain C where wte:"P,E \<turnstile> e :: Class C" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs' D' S' a' fs' h' l' v'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs'),(h',l')\<rangle>"
    from IH[OF eval_ref wte sconf] show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = THROW NullPointer"
    from IH[OF eval_null wte sconf] e2 show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" 
      by simp
  next
    fix e' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (FAccThrow E e s\<^sub>0 e' s\<^sub>1 F Cs e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> e\<bullet>F{Cs} :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain C where wte:"P,E \<turnstile> e :: Class C" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs' D' S' a' fs' h' l' v'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs'),(h',l')\<rangle>"
    from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex 
    assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = throw ex"
    from IH[OF eval_throw wte sconf] e2 show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (FAss E e\<^sub>1 s\<^sub>0 a Cs' s\<^sub>1 e\<^sub>2 v h\<^sub>2 l\<^sub>2 D S F T Cs v' Ds fs fs' S' h\<^sub>2' e\<^sub>2' s\<^sub>2 T')
  have eval:"P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs} := e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2\<rangle>"
    and eval':"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs'),s\<^sub>1\<rangle>"
    and eval'':"P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2)\<rangle>"
    and h2:"h\<^sub>2 a = Some(D, S)"
    and has_least:"P \<turnstile> last Cs' has least F:T via Cs"
    and casts:"P \<turnstile> T casts v to v'" and Ds:"Ds = Cs'@\<^sub>pCs"
    and S:"(Ds, fs) \<in> S" and fs':"fs' = fs(F \<mapsto> v')"
    and S':"S' = S - {(Ds, fs)} \<union> {(Ds, fs')}"
    and h2':"h\<^sub>2' = h\<^sub>2(a \<mapsto> (D, S'))"
    and wt:"P,E \<turnstile> e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 :: T'" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                     \<Longrightarrow> ref(a,Cs') = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>2 :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                    \<Longrightarrow> Val v = ei \<and> (h\<^sub>2,l\<^sub>2) = si" by fact+
  from wt obtain C T'' where wte1:"P,E \<turnstile> e\<^sub>1 :: Class C" 
    and has_least':"P \<turnstile> C has least F:T' via Cs"
    and wte2:"P,E \<turnstile> e\<^sub>2 :: T''" and leq:"P \<turnstile> T'' \<le> T'"
    by auto
  from wf eval' wte1 sconf have "last Cs' = C"
    by(auto dest!:eval_preserves_type split:if_split_asm)
  with has_least has_least' have TeqT':"T = T'" by (fastforce intro:sees_field_fun)
  from eval show ?case
  proof(rule eval_cases)
    fix Xs D' S'' U a' fs'' h l s w w'
    assume eval_ref:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
      and eval_val:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>Val w,(h,l)\<rangle>"
      and h:"h a' = Some(D',S'')"
      and has_least'':"P \<turnstile> last Xs has least F:U via Cs"
      and casts':"P \<turnstile> U casts w to w'"
      and S'':"(Xs@\<^sub>pCs,fs'') \<in> S''" and e2':"e\<^sub>2' = Val w'"
      and s2:"s\<^sub>2 = (h(a'\<mapsto>(D',insert (Xs@\<^sub>pCs,fs''(F \<mapsto> w')) 
                                     (S''-{(Xs@\<^sub>pCs,fs'')}))),l)"
    from IH1[OF eval_ref wte1 sconf] have eq:"a = a' \<and> Cs' = Xs \<and> s\<^sub>1 = s" by simp
    with wf eval_ref wte1 sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF _ wte2 this] eval_val eq have eq':"v = w \<and> h = h\<^sub>2 \<and> l = l\<^sub>2" by auto
    from has_least'' eq has_least have UeqT:"U = T" by (fastforce intro:sees_field_fun)
    from has_least wf have "is_type P T" by(rule least_field_is_type)
    with casts casts' eq eq' UeqT TeqT' wte2 leq eval_val sconf' wf have v':"v' = w'"
      by(auto intro!:casts_casts_eq_result)
    from eval_preserves_sconf[OF wf eval'' wte2 sconf'] h2
    have oconf:"P,h\<^sub>2 \<turnstile> (D,S) \<surd>"
      by(simp add:sconf_def hconf_def)
    from eq eq' h2 h have "S = S''" by simp
    with oconf eq S S' S'' Ds have "fs = fs''" by (auto simp:oconf_def)
    with h2' h h2 eq eq' s2 S' Ds fs' v' e2' show "Val v' = e\<^sub>2' \<and> (h\<^sub>2',l\<^sub>2) = s\<^sub>2"
      by simp
  next
    fix s w assume eval_null:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
    from IH1[OF eval_null wte1 sconf] show "Val v' = e\<^sub>2' \<and> (h\<^sub>2',l\<^sub>2) = s\<^sub>2" by simp
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
    from IH1[OF eval_throw wte1 sconf] show "Val v' = e\<^sub>2' \<and> (h\<^sub>2',l\<^sub>2) = s\<^sub>2" by simp
  next
    fix ex s w
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>" 
      and eval_throw:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
    from IH1[OF eval_val wte1 sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_val wte1 sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_throw[simplified eq] wte2 this]
    show "Val v' = e\<^sub>2' \<and> (h\<^sub>2',l\<^sub>2) = s\<^sub>2" by simp
  qed
next
  case (FAssNull E e\<^sub>1 s\<^sub>0 s\<^sub>1 e\<^sub>2 v s\<^sub>2 F Cs e\<^sub>2' s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs} := e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                     \<Longrightarrow> null = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>2 :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                    \<Longrightarrow> Val v = ei \<and> s\<^sub>2 = si" by fact+
  from wt obtain C T'' where wte1:"P,E \<turnstile> e\<^sub>1 :: Class C" 
    and wte2:"P,E \<turnstile> e\<^sub>2 :: T''" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs D' S'' U a' fs'' h l s w w'
    assume eval_ref:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
    from IH1[OF eval_ref wte1 sconf] show "THROW NullPointer = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'"
      by simp
  next
    fix s w 
    assume eval_null:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
      and eval_val:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>Val w,s\<^sub>2'\<rangle>"
      and e2':"e\<^sub>2' = THROW NullPointer"
    from IH1[OF eval_null wte1 sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_null wte1 sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_val[simplified eq] wte2 this] e2'
    show "THROW NullPointer = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
    from IH1[OF eval_throw wte1 sconf] show "THROW NullPointer = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" 
      by simp
  next
    fix ex s w
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
      and eval_throw:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
    from IH1[OF eval_val wte1 sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_val wte1 sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_throw[simplified eq] wte2 this] 
    show "THROW NullPointer = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  qed
next
  case (FAssThrow1 E e\<^sub>1 s\<^sub>0 e' s\<^sub>1 F Cs e\<^sub>2 e\<^sub>2' s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs} := e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2\<rangle>" 
    and wt:"P,E \<turnstile> e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> throw e' = ei \<and> s\<^sub>1 = si" by fact+
  from wt obtain C T'' where wte1:"P,E \<turnstile> e\<^sub>1 :: Class C" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs D' S'' U a' fs'' h l s w w'
    assume eval_ref:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
    from IH[OF eval_ref wte1 sconf] show "throw e' = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix s w 
    assume eval_null:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
    from IH[OF eval_null wte1 sconf] show "throw e' = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex
    assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2':"e\<^sub>2' = throw ex"
    from IH[OF eval_throw wte1 sconf] e2' show "throw e' = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex s w assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
    from IH[OF eval_val wte1 sconf] show "throw e' = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (FAssThrow2 E e\<^sub>1 s\<^sub>0 v s\<^sub>1 e\<^sub>2 e' s\<^sub>2 F Cs e\<^sub>2' s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs} := e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>" 
    and wt:"P,E \<turnstile> e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> Val v = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>2 :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                    \<Longrightarrow> throw e' = ei \<and> s\<^sub>2 = si" by fact+
  from wt obtain C T'' where wte1:"P,E \<turnstile> e\<^sub>1 :: Class C" 
    and wte2:"P,E \<turnstile> e\<^sub>2 :: T''" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix Xs D' S'' U a' fs'' h l s w w'
    assume eval_ref:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
      and eval_val:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>Val w,(h,l)\<rangle>"
    from IH1[OF eval_ref wte1 sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_ref wte1 sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_val[simplified eq] wte2 this] show "throw e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'"
      by simp
  next
    fix s w 
    assume eval_null:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
      and eval_val:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>Val w,s\<^sub>2'\<rangle>"
    from IH1[OF eval_null wte1 sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_null wte1 sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_val[simplified eq] wte2 this] show "throw e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'"
      by simp
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
    from IH1[OF eval_throw wte1 sconf] show "throw e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix ex s w
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
      and eval_throw:"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>" and e2':"e\<^sub>2' = throw ex"
    from IH1[OF eval_val wte1 sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_val wte1 sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval_throw[simplified eq] wte2 this] e2' 
    show "throw e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  qed
next
  case (CallObjThrow E e s\<^sub>0 e' s\<^sub>1 Copt M es e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> Call e Copt M es :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt obtain C where wte:"P,E \<turnstile> e :: Class C" by(cases Copt)auto
  show ?case
  proof(cases Copt)
    assume "Copt = None"
    with eval have "P,E \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>" by simp
    thus ?thesis
    proof(rule eval_cases)
      fix ex
      assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = throw ex"
      from IH[OF eval_throw wte sconf] e2 show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
    next
      fix es' ex' s w ws assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
      from IH[OF eval_val wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
    next
      fix C' Xs Xs' Ds' S' U U' Us Us' a' body'' body''' h h' l l' pns'' pns''' 
          s ws ws'
      assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
      from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
    next
      fix s ws
      assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
      from IH[OF eval_null wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
    qed
  next
    fix C' assume "Copt = Some C'"
    with eval have "P,E \<turnstile> \<langle>e\<bullet>(C'::)M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>" by simp
    thus ?thesis
    proof(rule eval_cases)
      fix ex
      assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = throw ex"
      from IH[OF eval_throw wte sconf] e2 show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
    next
      fix es' ex' s w ws assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
      from IH[OF eval_val wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
    next
      fix C'' Xs Xs' Ds' S' U U' Us Us' a' body'' body''' h h' l l' pns'' pns''' 
          s ws ws'
      assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
      from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
    next
      fix s ws
      assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
      from IH[OF eval_null wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
    qed
  qed
next
  case (CallParamsThrow E e s\<^sub>0 v s\<^sub>1 es vs ex es' s\<^sub>2 Copt M e\<^sub>2 s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> Call e Copt M es :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> Val v = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>esi si Ts. \<lbrakk>P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>esi,si\<rangle>; P,E \<turnstile> es [::] Ts; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                      \<Longrightarrow> map Val vs @ throw ex # es' = esi \<and> s\<^sub>2 = si" by fact+
  from wt obtain C Ts where wte:"P,E \<turnstile> e :: Class C" and wtes:"P,E \<turnstile> es [::] Ts" 
    by(cases Copt)auto
  show ?case
  proof(cases Copt)
    assume "Copt = None"
    with eval have "P,E \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>" by simp
    thus ?thesis
    proof(rule eval_cases)
      fix ex' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex',s\<^sub>2'\<rangle>"
      from IH1[OF eval_throw wte sconf] show "throw ex = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
    next
      fix es'' ex' s w ws
      assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>" 
        and evals_throw:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws@throw ex'#es'',s\<^sub>2'\<rangle>"
        and e2:"e\<^sub>2 = throw ex'"
      from IH1[OF eval_val wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_val wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_throw[simplified eq] wtes this] e2
      have "vs = ws \<and> ex = ex' \<and> es' = es'' \<and> s\<^sub>2 = s\<^sub>2'"
        by(fastforce dest:map_Val_throw_eq)
      with e2 show "throw ex = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
    next
      fix C' Xs Xs' Ds' S' U U' Us Us' a' body'' body''' h h' l l' pns'' pns''' 
          s ws ws'
      assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
        and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws,(h,l)\<rangle>"
      from IH1[OF eval_ref wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_ref wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_vals[simplified eq] wtes this]
      show "throw ex = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'"
        by(fastforce dest:sym[THEN map_Val_throw_False])
    next
      fix s ws
      assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
        and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws,s\<^sub>2'\<rangle>"
        and e2:"e\<^sub>2 = THROW NullPointer"
      from IH1[OF eval_null wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_null wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_vals[simplified eq] wtes this] 
      show "throw ex = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'"
        by(fastforce dest:sym[THEN map_Val_throw_False])
    qed
  next
    fix C' assume "Copt = Some C'"
    with eval have "P,E \<turnstile> \<langle>e\<bullet>(C'::)M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>" by simp
    thus ?thesis
    proof(rule eval_cases)
      fix ex' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex',s\<^sub>2'\<rangle>"
      from IH1[OF eval_throw wte sconf] show "throw ex = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
    next
      fix es'' ex' s w ws
      assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>" 
        and evals_throw:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws@throw ex'#es'',s\<^sub>2'\<rangle>"
        and e2:"e\<^sub>2 = throw ex'"
      from IH1[OF eval_val wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_val wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_throw[simplified eq] wtes this] e2
      have "vs = ws \<and> ex = ex' \<and> es' = es'' \<and> s\<^sub>2 = s\<^sub>2'"
        by(fastforce dest:map_Val_throw_eq)
      with e2 show "throw ex = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
    next
      fix C' Xs Xs' Ds' S' U U' Us Us' a' body'' body''' h h' l l' pns'' pns''' 
          s ws ws'
      assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
        and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws,(h,l)\<rangle>"
      from IH1[OF eval_ref wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_ref wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_vals[simplified eq] wtes this]
      show "throw ex = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'"
        by(fastforce dest:sym[THEN map_Val_throw_False])
    next
      fix s ws
      assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
        and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws,s\<^sub>2'\<rangle>"
        and e2:"e\<^sub>2 = THROW NullPointer"
      from IH1[OF eval_null wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_null wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_vals[simplified eq] wtes this] 
      show "throw ex = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'"
        by(fastforce dest:sym[THEN map_Val_throw_False])
    qed
  qed
next
  case (Call E e s\<^sub>0 a Cs s\<^sub>1 es vs h\<^sub>2 l\<^sub>2 C S M Ts' T' pns' body' Ds Ts T pns
             body Cs' vs' l\<^sub>2' new_body e' h\<^sub>3 l\<^sub>3 e\<^sub>2 s\<^sub>2 T'')
  have eval:"P,E \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and eval':"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<^sub>1\<rangle>"
    and eval'':"P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2)\<rangle>" and h2:"h\<^sub>2 a = Some(C,S)"
    and has_least:"P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds"
    and selects:"P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'"
    and length:"length vs = length pns" and Casts:"P \<turnstile> Ts Casts vs to vs'"
    and l2':"l\<^sub>2' = [this \<mapsto> Ref (a, Cs'), pns [\<mapsto>] vs']"
    and new_body:"new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body | _ \<Rightarrow> body)"
    and eval_body:"P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> 
                                            \<langle>new_body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle>"
    and wt:"P,E \<turnstile> e\<bullet>M(es) :: T''" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                     \<Longrightarrow> ref (a,Cs) = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>esi si Ts. \<lbrakk>P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>esi,si\<rangle>; P,E \<turnstile> es [::] Ts; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                      \<Longrightarrow> map Val vs = esi \<and> (h\<^sub>2,l\<^sub>2) = si"
    and IH3:"\<And>ei si T. 
    \<lbrakk>P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> \<langle>new_body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>;
     P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> new_body :: T;
     P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> (h\<^sub>2,l\<^sub>2') \<surd>\<rbrakk>
  \<Longrightarrow> e' = ei \<and> (h\<^sub>3, l\<^sub>3) = si" by fact+
  from wt obtain D Ss Ss' m Cs'' where wte:"P,E \<turnstile> e :: Class D" 
    and has_least':"P \<turnstile> D has least M = (Ss,T'',m) via Cs''"
    and wtes:"P,E \<turnstile> es [::] Ss'" and subs:"P \<turnstile> Ss' [\<le>] Ss" by auto
  from eval_preserves_type[OF wf eval' sconf wte]
  have last:"last Cs = D" by (auto split:if_split_asm)
  with has_least has_least' wf
  have eq:"Ts' = Ss \<and> T' = T'' \<and> (pns',body') = m \<and> Ds = Cs''"
    by(fastforce dest:wf_sees_method_fun)
  from wf selects have param_type:"\<forall>T \<in> set Ts. is_type P T" 
    and return_type:"is_type P T" and TnotNT:"T \<noteq> NT"
    by(auto dest:select_method_wf_mdecl simp:wf_mdecl_def)
  from selects wf have subo:"Subobjs P C Cs'"
    by(induct rule:SelectMethodDef.induct,
       auto simp:FinalOverriderMethodDef_def OverriderMethodDefs_def 
                 MinimalMethodDefs_def LeastMethodDef_def MethodDefs_def)
  with wf have "class":"is_class P (last Cs')" by(auto intro!:Subobj_last_isClass)
  from eval'' have hext:"hp s\<^sub>1 \<unlhd> h\<^sub>2" by (cases s\<^sub>1,auto intro: evals_hext)
  from wf eval' sconf wte last have "P,E,(hp s\<^sub>1) \<turnstile> ref(a,Cs) :\<^bsub>NT\<^esub> Class(last Cs)"
    by -(rule eval_preserves_type,simp_all)
  with hext have "P,E,h\<^sub>2 \<turnstile> ref(a,Cs) :\<^bsub>NT\<^esub> Class(last Cs)"
    by(auto intro:WTrt_hext_mono dest:hext_objD split:if_split_asm)
  with h2 have "Subobjs P C Cs" by (auto split:if_split_asm)
  hence "P \<turnstile> Path C to (last Cs) via Cs"
    by (auto simp:path_via_def split:if_split_asm)
  with selects has_least wf have param_types:"Ts' = Ts \<and> P \<turnstile> T \<le> T'"
    by -(rule select_least_methods_subtypes,simp_all)
  from wf selects have wt_body:"P,[this\<mapsto>Class(last Cs'),pns[\<mapsto>]Ts] \<turnstile> body :: T"
    and this_not_pns:"this \<notin> set pns" and length:"length pns = length Ts"
    and dist:"distinct pns"
    by(auto dest!:select_method_wf_mdecl simp:wf_mdecl_def)
  have "P,[this\<mapsto>Class(last Cs'),pns[\<mapsto>]Ts] \<turnstile> new_body :: T'"
  proof(cases "\<exists>C. T' = Class C")
    case False with wt_body new_body param_types show ?thesis by(cases T') auto
  next
    case True
    then obtain D' where T':"T' = Class D'" by auto
    with wf has_least have "class":"is_class P D'"
      by(fastforce dest:has_least_wf_mdecl simp:wf_mdecl_def)
    with wf T' TnotNT param_types obtain D'' where T:"T = Class D''"
      by(fastforce dest:widen_Class)
    with wf return_type T' param_types have "P \<turnstile> Path D'' to D' unique"
      by(simp add:Class_widen_Class)
    with wt_body "class" T T' new_body show ?thesis by auto
  qed
  hence wt_new_body:"P,E(this\<mapsto>Class(last Cs'),pns[\<mapsto>]Ts) \<turnstile> new_body :: T'"
    by(fastforce intro:wt_env_mono)
  from eval show ?case
  proof(rule eval_cases)
    fix ex' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex',s\<^sub>2\<rangle>"
    from IH1[OF eval_throw wte sconf] show "e' = e\<^sub>2 \<and> (h\<^sub>3, l\<^sub>2) = s\<^sub>2" by simp
  next
    fix es'' ex' s w ws
    assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>" 
      and evals_throw:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws@throw ex'#es'',s\<^sub>2\<rangle>"
    from IH1[OF eval_val wte sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_val wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF evals_throw[simplified eq] wtes this] show "e' = e\<^sub>2 \<and> (h\<^sub>3, l\<^sub>2) = s\<^sub>2"
      by(fastforce dest:map_Val_throw_False)
  next
    fix C' Xs Xs' Ds' S' U U' Us Us' a' body'' body''' h h' l l' pns'' pns''' s ws ws'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
      and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws,(h,l)\<rangle>"
      and h:"h a' = Some(C',S')" 
      and has_least'':"P \<turnstile> last Xs has least M = (Us',U',pns''',body''') via Ds'"
      and selects':"P \<turnstile> (C',Xs@\<^sub>pDs') selects M = (Us,U,pns'',body'') via Xs'"
      and length':"length ws = length pns''" and Casts':"P \<turnstile> Us Casts ws to ws'"
      and eval_body':"P,E(this \<mapsto> Class (last Xs'), pns'' [\<mapsto>] Us) \<turnstile> 
      \<langle>case U' of Class D \<Rightarrow> \<lparr>D\<rparr>body'' | _ \<Rightarrow> body'',
        (h,[this \<mapsto> Ref(a',Xs'), pns'' [\<mapsto>] ws'])\<rangle> \<Rightarrow> \<langle>e\<^sub>2,(h',l')\<rangle>"
      and s2:"s\<^sub>2 = (h',l)"
    from IH1[OF eval_ref wte sconf] have eq1:"a = a' \<and> Cs = Xs" and s:"s = s\<^sub>1" 
      by simp_all
    with has_least has_least'' wf have eq2:"T' = U' \<and> Ts' = Us' \<and> Ds = Ds'"
      by(fastforce dest:wf_sees_method_fun)
    from s wf eval_ref wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF evals_vals[simplified s] wtes this]
    have eq3:"vs = ws \<and> h\<^sub>2 = h \<and> l\<^sub>2 = l"
      by(fastforce elim:map_injective simp:inj_on_def)
    with eq1 h2 h have eq4:"C = C' \<and> S = S'" by simp
    with eq1 eq2 selects selects' wf
    have eq5:"Ts = Us \<and> T = U \<and> pns'' = pns \<and> body'' = body \<and> Cs' = Xs'"
      by simp(drule_tac mthd'="(Us,U,pns'',body'')" in wf_select_method_fun,auto)
    with subs eq param_types have "P \<turnstile> Ss' [\<le>] Us" by simp
    with wf Casts Casts' param_type wtes evals_vals sconf' s eq eq2 eq3 eq5
    have eq6:"vs' = ws'"
      by(fastforce intro:Casts_Casts_eq_result)
    with eval_body' l2' eq1 eq2 eq3 eq5 new_body  
    have eval_body'':"P,E(this \<mapsto> Class(last Cs'), pns [\<mapsto>] Ts) \<turnstile> 
                           \<langle>new_body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e\<^sub>2,(h',l')\<rangle>"
      by fastforce
    from wf evals_vals wtes sconf' s eq3 have sconf'':"P,E \<turnstile> (h\<^sub>2,l\<^sub>2) \<surd>"
      by(fastforce intro:evals_preserves_sconf)
    have "P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> (h\<^sub>2,l\<^sub>2') \<surd>"
    proof(auto simp:sconf_def)
      from sconf'' show "P \<turnstile> h\<^sub>2 \<surd>" by(simp add:sconf_def)
    next
      { fix V v assume map:"[this \<mapsto> Ref (a,Cs'), pns [\<mapsto>] vs'] V = Some v"
        have "\<exists>T. (E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts)) V = Some T \<and> 
                   P,h\<^sub>2 \<turnstile> v :\<le> T"
        proof(cases "V \<in> set (this#pns)")
          case False with map show ?thesis by simp
        next
          case True
          hence "V = this \<or> V \<in> set pns" by simp
          thus ?thesis
          proof(rule disjE)
            assume V:"V = this"
            with map this_not_pns have "v = Ref(a,Cs')" by simp
            with V h2 subo this_not_pns have 
              "(E(this \<mapsto> Class (last Cs'),pns [\<mapsto>] Ts)) V = Some(Class (last Cs'))"
              and "P,h\<^sub>2 \<turnstile> v :\<le> Class (last Cs')" by simp_all
            thus ?thesis by simp
          next
            assume "V \<in> set pns"
            then obtain i where V:"V = pns!i" and length_i:"i < length pns"
              by(auto simp:in_set_conv_nth)
            from Casts have "length Ts = length vs'"
              by(induct rule:Casts_to.induct,auto)
            with length have "length pns = length vs'" by simp
            with map dist V length_i have v:"v = vs'!i" by(fastforce dest:maps_nth)
            from length dist length_i
            have env:"(E(this \<mapsto> Class (last Cs'))(pns [\<mapsto>] Ts)) (pns!i) = Some(Ts!i)"
              by(rule_tac E="E(this \<mapsto> Class (last Cs'))" in nth_maps,simp_all)
            from wf Casts wtes subs eq param_types eval'' sconf'
            have "\<forall>i < length Ts. P,h\<^sub>2 \<turnstile> vs'!i :\<le> Ts!i"
              by simp(rule Casts_conf,auto)
            with length_i length env V v show ?thesis by simp
          qed
        qed }
      thus "P,h\<^sub>2 \<turnstile> l\<^sub>2' (:\<le>)\<^sub>w E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts)"
        using l2' by(simp add:lconf_def)
    next
      { fix V Tx assume env:"(E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts)) V = Some Tx"
        have "is_type P Tx"
        proof(cases "V \<in> set (this#pns)")
          case False
          with env sconf'' show ?thesis
            by(clarsimp simp:sconf_def envconf_def)
        next
          case True
          hence "V = this \<or> V \<in> set pns" by simp
          thus ?thesis
          proof(rule disjE)
            assume "V = this"
            with env this_not_pns have "Tx = Class(last Cs')" by simp
            with "class" show ?thesis by simp
          next
            assume "V \<in> set pns"
            then obtain i where V:"V = pns!i" and length_i:"i < length pns"
              by(auto simp:in_set_conv_nth)
            with dist length env have "Tx = Ts!i" by(fastforce dest:maps_nth)
            with length_i length have "Tx \<in> set Ts"
              by(fastforce simp:in_set_conv_nth)
            with param_type show ?thesis by simp
          qed
        qed }
      thus "P \<turnstile> E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<surd>" by (simp add:envconf_def)
    qed
    from IH3[OF eval_body'' wt_new_body this] have "e' = e\<^sub>2 \<and> (h\<^sub>3, l\<^sub>3) = (h',l')" .
    with eq3 s2 show "e' = e\<^sub>2 \<and> (h\<^sub>3,l\<^sub>2) = s\<^sub>2" by simp
  next
    fix s ws
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
    from IH1[OF eval_null wte sconf] show "e' = e\<^sub>2 \<and> (h\<^sub>3,l\<^sub>2) = s\<^sub>2" by simp
  qed
next
  case (StaticCall E e s\<^sub>0 a Cs s\<^sub>1 es vs h\<^sub>2 l\<^sub>2 C Cs'' M Ts T pns body  Cs'
                   Ds vs' l\<^sub>2' e' h\<^sub>3 l\<^sub>3 e\<^sub>2 s\<^sub>2 T')
  have eval:"P,E \<turnstile> \<langle>e\<bullet>(C::)M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and eval':"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a,Cs),s\<^sub>1\<rangle>"
    and eval'':"P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2, l\<^sub>2)\<rangle>"
    and path_unique:"P \<turnstile> Path last Cs to C unique" 
    and path_via:"P \<turnstile> Path last Cs to C via Cs''"
    and has_least:"P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'"
    and Ds:"Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs'" and length:"length vs = length pns"
    and Casts:"P \<turnstile> Ts Casts vs to vs'"
    and l2':"l\<^sub>2' = [this \<mapsto> Ref (a, Ds), pns [\<mapsto>] vs']"
    and eval_body:"P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> 
                                             \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle>"
    and wt:"P,E \<turnstile> e\<bullet>(C::)M(es) :: T'" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> ref (a,Cs) = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>esi si Ts. 
             \<lbrakk>P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>esi,si\<rangle>; P,E \<turnstile> es [::] Ts; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                    \<Longrightarrow> map Val vs = esi \<and> (h\<^sub>2,l\<^sub>2) = si"
    and IH3:"\<And>ei si T.
   \<lbrakk>P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>;
    P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> body :: T;
    P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> (h\<^sub>2,l\<^sub>2') \<surd>\<rbrakk>
                    \<Longrightarrow> e' = ei \<and> (h\<^sub>3, l\<^sub>3) = si" by fact+
  from wt has_least wf obtain C' Ts' where wte:"P,E \<turnstile> e :: Class C'"
      and wtes:"P,E \<turnstile> es [::] Ts'" and subs:"P \<turnstile> Ts' [\<le>] Ts"
    by(auto dest:wf_sees_method_fun)
  from eval_preserves_type[OF wf eval' sconf wte]
  have last:"last Cs = C'" by (auto split:if_split_asm)
  from wf has_least have param_type:"\<forall>T \<in> set Ts. is_type P T" 
    and return_type:"is_type P T" and TnotNT:"T \<noteq> NT"
    by(auto dest:has_least_wf_mdecl simp:wf_mdecl_def)
  from path_via have last':"last Cs'' = last(Cs@\<^sub>pCs'')"
    by(fastforce intro!:appendPath_last Subobjs_nonempty simp:path_via_def)
  from eval'' have hext:"hp s\<^sub>1 \<unlhd> h\<^sub>2" by (cases s\<^sub>1,auto intro: evals_hext)
  from wf eval' sconf wte last have "P,E,(hp s\<^sub>1) \<turnstile> ref(a,Cs) :\<^bsub>NT\<^esub> Class(last Cs)"
    by -(rule eval_preserves_type,simp_all)
  with hext have "P,E,h\<^sub>2 \<turnstile> ref(a,Cs) :\<^bsub>NT\<^esub> Class(last Cs)"
    by(auto intro:WTrt_hext_mono dest:hext_objD split:if_split_asm)
  then obtain D S where h2:"h\<^sub>2 a = Some(D,S)" and "Subobjs P D Cs"
    by (auto split:if_split_asm)
  with path_via wf have "Subobjs P D (Cs@\<^sub>pCs'')" and "last Cs'' = C"
    by(auto intro:Subobjs_appendPath simp:path_via_def)
  with has_least wf last' Ds have subo:"Subobjs P D Ds"
    by(fastforce intro:Subobjs_appendPath simp:LeastMethodDef_def MethodDefs_def)
  with wf have "class":"is_class P (last Ds)" by(auto intro!:Subobj_last_isClass)
  from has_least wf obtain D' where "Subobjs P D' Cs'"
    by(auto simp:LeastMethodDef_def MethodDefs_def)
  with Ds have last_Ds:"last Cs' = last Ds"
    by(fastforce intro!:appendPath_last Subobjs_nonempty)
  with wf has_least have "P,[this\<mapsto>Class(last Ds),pns[\<mapsto>]Ts] \<turnstile> body :: T"
    and this_not_pns:"this \<notin> set pns" and length:"length pns = length Ts"
    and dist:"distinct pns"
    by(auto dest!:has_least_wf_mdecl simp:wf_mdecl_def)
  hence wt_body:"P,E(this\<mapsto>Class(last Ds),pns[\<mapsto>]Ts) \<turnstile> body :: T"
    by(fastforce intro:wt_env_mono)
  from eval show ?case
  proof(rule eval_cases)
    fix ex' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex',s\<^sub>2\<rangle>"
    from IH1[OF eval_throw wte sconf] show "e' = e\<^sub>2 \<and> (h\<^sub>3, l\<^sub>2) = s\<^sub>2" by simp
  next
    fix es'' ex' s w ws
    assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>" 
      and evals_throw:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws@throw ex'#es'',s\<^sub>2\<rangle>"
    from IH1[OF eval_val wte sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_val wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF evals_throw[simplified eq] wtes this] show "e' = e\<^sub>2 \<and> (h\<^sub>3, l\<^sub>2) = s\<^sub>2"
      by(fastforce dest:map_Val_throw_False)
  next
    fix Xs Xs' Xs'' U Us a' body' h h' l l' pns' s ws ws'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
      and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws,(h,l)\<rangle>"
      and path_unique':"P \<turnstile> Path last Xs to C unique"
      and path_via':"P \<turnstile> Path last Xs to C via Xs''"
      and has_least':"P \<turnstile> C has least M = (Us,U,pns',body') via Xs'"
      and length':"length ws = length pns'"
      and Casts':"P \<turnstile> Us Casts ws to ws'"
      and eval_body':"P,E(this \<mapsto> Class(last((Xs@\<^sub>pXs'')@\<^sub>pXs')),pns' [\<mapsto>] Us) \<turnstile> 
      \<langle>body',(h,[this \<mapsto> Ref(a',(Xs@\<^sub>pXs'')@\<^sub>pXs'),pns' [\<mapsto>] ws'])\<rangle> \<Rightarrow> \<langle>e\<^sub>2,(h',l')\<rangle>"
      and s2:"s\<^sub>2 = (h',l)"
    from IH1[OF eval_ref wte sconf] have eq1:"a = a' \<and> Cs = Xs" and s:"s = s\<^sub>1" 
      by simp_all
    from has_least has_least' wf 
    have eq2:"T = U \<and> Ts = Us \<and> Cs' = Xs' \<and> pns = pns' \<and> body = body'"
      by(fastforce dest:wf_sees_method_fun)
    from s wf eval_ref wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF evals_vals[simplified s] wtes this]
    have eq3:"vs = ws \<and> h\<^sub>2 = h \<and> l\<^sub>2 = l"
      by(fastforce elim:map_injective simp:inj_on_def)
    from path_unique path_via path_via' eq1 have "Cs'' = Xs''" 
      by(fastforce simp:path_unique_def path_via_def)
    with Ds eq1 eq2 have Ds':"Ds = (Xs@\<^sub>pXs'')@\<^sub>pXs'" by simp
    from wf Casts Casts' param_type wtes subs evals_vals sconf' s eq2 eq3
    have eq4:"vs' = ws'"
      by(fastforce intro:Casts_Casts_eq_result)
    with eval_body' Ds' l2' eq1 eq2 eq3
    have eval_body'':"P,E(this \<mapsto> Class(last Ds),pns [\<mapsto>] Ts) \<turnstile> 
                            \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow> \<langle>e\<^sub>2,(h',l')\<rangle>"
      by simp
    from wf evals_vals wtes sconf' s eq3 have sconf'':"P,E \<turnstile> (h\<^sub>2,l\<^sub>2) \<surd>"
      by(fastforce intro:evals_preserves_sconf)
    have "P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> (h\<^sub>2,l\<^sub>2') \<surd>"
    proof(auto simp:sconf_def)
      from sconf'' show "P \<turnstile> h\<^sub>2 \<surd>" by(simp add:sconf_def)
    next
      { fix V v assume map:"[this \<mapsto> Ref (a,Ds), pns [\<mapsto>] vs'] V = Some v"
        have "\<exists>T. (E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts)) V = Some T \<and> 
                   P,h\<^sub>2 \<turnstile> v :\<le> T"
        proof(cases "V \<in> set (this#pns)")
          case False with map show ?thesis by simp
        next
          case True
          hence "V = this \<or> V \<in> set pns" by simp
          thus ?thesis
          proof(rule disjE)
            assume V:"V = this"
            with map this_not_pns have "v = Ref(a,Ds)" by simp
            with V h2 subo this_not_pns have
              "(E(this \<mapsto> Class (last Ds),pns [\<mapsto>] Ts)) V = Some(Class (last Ds))"
              and "P,h\<^sub>2 \<turnstile> v :\<le> Class (last Ds)" by simp_all
            thus ?thesis by simp
          next
            assume "V \<in> set pns"
            then obtain i where V:"V = pns!i" and length_i:"i < length pns"
              by(auto simp:in_set_conv_nth)
            from Casts have "length Ts = length vs'"
              by(induct rule:Casts_to.induct,auto)
            with length have "length pns = length vs'" by simp
            with map dist V length_i have v:"v = vs'!i" by(fastforce dest:maps_nth)
            from length dist length_i
            have env:"(E(this \<mapsto> Class (last Ds))(pns [\<mapsto>] Ts)) (pns!i) = Some(Ts!i)"
              by(rule_tac E="E(this \<mapsto> Class (last Ds))" in nth_maps,simp_all)
            from wf Casts wtes subs eval'' sconf'
            have "\<forall>i < length Ts. P,h\<^sub>2 \<turnstile> vs'!i :\<le> Ts!i"
              by -(rule Casts_conf,auto)
            with length_i length env V v show ?thesis by simp
          qed
        qed }
      thus "P,h\<^sub>2 \<turnstile> l\<^sub>2' (:\<le>)\<^sub>w E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts)"
        using l2' by(simp add:lconf_def)
    next
      { fix V Tx assume env:"(E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts)) V = Some Tx"
        have "is_type P Tx"
        proof(cases "V \<in> set (this#pns)")
          case False
          with env sconf'' show ?thesis
            by(clarsimp simp:sconf_def envconf_def)
        next
          case True
          hence "V = this \<or> V \<in> set pns" by simp
          thus ?thesis
          proof(rule disjE)
            assume "V = this"
            with env this_not_pns have "Tx = Class(last Ds)" by simp
            with "class" show ?thesis by simp
          next
            assume "V \<in> set pns"
            then obtain i where V:"V = pns!i" and length_i:"i < length pns"
              by(auto simp:in_set_conv_nth)
            with dist length env have "Tx = Ts!i" by(fastforce dest:maps_nth)
            with length_i length have "Tx \<in> set Ts"
              by(fastforce simp:in_set_conv_nth)
            with param_type show ?thesis by simp
          qed
        qed }
      thus "P \<turnstile> E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<surd>" by (simp add:envconf_def)
    qed
    from IH3[OF eval_body'' wt_body this] have "e' = e\<^sub>2 \<and> (h\<^sub>3, l\<^sub>3) = (h',l')" .
    with eq3 s2 show "e' = e\<^sub>2 \<and> (h\<^sub>3, l\<^sub>2) = s\<^sub>2" by simp
  next
    fix s ws
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
    from IH1[OF eval_null wte sconf] show "e' = e\<^sub>2 \<and> (h\<^sub>3,l\<^sub>2) = s\<^sub>2" by simp
  qed
next
  case (CallNull E e s\<^sub>0 s\<^sub>1 es vs s\<^sub>2 Copt M e\<^sub>2 s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> Call e Copt M es :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
    \<Longrightarrow> null = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>esi si Ts. \<lbrakk>P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>esi,si\<rangle>; P,E \<turnstile> es [::] Ts; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
    \<Longrightarrow> map Val vs = esi \<and> s\<^sub>2 = si" by fact+
  from wt obtain C Ts where wte:"P,E \<turnstile> e :: Class C" and wtes:"P,E \<turnstile> es [::] Ts" 
    by(cases Copt)auto
  show ?case
  proof(cases Copt)
    assume "Copt = None"
    with eval have "P,E \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>" by simp
    thus ?thesis
    proof(rule eval_cases)
      fix ex' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex',s\<^sub>2'\<rangle>"
      from IH1[OF eval_throw wte sconf] show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" 
        by simp
    next
      fix es' ex' s w ws
      assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
        and evals_throw:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws@throw ex'#es',s\<^sub>2'\<rangle>"
      from IH1[OF eval_val wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_val wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_throw[simplified eq] wtes this] 
      show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by(fastforce dest:map_Val_throw_False)
    next
      fix C' Xs Xs' Ds' S' U U' Us Us' a' body'' body''' h h' l l' pns'' pns''' 
          s ws ws'
      assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
      from IH1[OF eval_ref wte sconf] show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" 
        by simp
    next
      fix s ws
      assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
        and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws,s\<^sub>2'\<rangle>"
        and e2:"e\<^sub>2 = THROW NullPointer"
      from IH1[OF eval_null wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_null wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_vals[simplified eq] wtes this] e2
      show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
    qed
  next
    fix C' assume "Copt = Some C'"
    with eval have "P,E \<turnstile> \<langle>e\<bullet>(C'::)M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>" by simp
    thus ?thesis
    proof(rule eval_cases)
      fix ex' assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex',s\<^sub>2'\<rangle>"
      from IH1[OF eval_throw wte sconf] show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" 
        by simp
    next
      fix es' ex' s w ws
      assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
        and evals_throw:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws@throw ex'#es',s\<^sub>2'\<rangle>"
      from IH1[OF eval_val wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_val wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_throw[simplified eq] wtes this] 
      show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by(fastforce dest:map_Val_throw_False)
    next
      fix C' Xs Xs' Ds' S' U U' Us Us' a' body'' body''' h h' l l' pns'' pns''' 
          s ws ws'
      assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref(a',Xs),s\<rangle>"
      from IH1[OF eval_ref wte sconf] show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" 
        by simp
    next
      fix s ws
      assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<rangle>"
        and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>map Val ws,s\<^sub>2'\<rangle>"
        and e2:"e\<^sub>2 = THROW NullPointer"
      from IH1[OF eval_null wte sconf] have eq:"s = s\<^sub>1" by simp
      with wf eval_null wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
        by(fastforce intro:eval_preserves_sconf)
      from IH2[OF evals_vals[simplified eq] wtes this] e2
      show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
    qed
  qed
next
  case (Block E V T e\<^sub>0 h\<^sub>0 l\<^sub>0 e\<^sub>1 h\<^sub>1 l\<^sub>1 e\<^sub>2 s\<^sub>2 T')
  have eval:"P,E \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0, l\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> {V:T; e\<^sub>0} :: T'" and sconf:"P,E \<turnstile> (h\<^sub>0, l\<^sub>0) \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T'. \<lbrakk>P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0, l\<^sub>0(V := None))\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; 
               P,E(V \<mapsto> T) \<turnstile> e\<^sub>0 :: T'; P,E(V \<mapsto> T) \<turnstile> (h\<^sub>0, l\<^sub>0(V := None)) \<surd>\<rbrakk>
    \<Longrightarrow> e\<^sub>1 = e\<^sub>2 \<and> (h\<^sub>1, l\<^sub>1) = s\<^sub>2" by fact+
  from wt have type:"is_type P T" and wte:"P,E(V \<mapsto> T) \<turnstile> e\<^sub>0 :: T'" by auto
  from sconf type have sconf':"P,E(V \<mapsto> T) \<turnstile> (h\<^sub>0, l\<^sub>0(V := None)) \<surd>"
    by(auto simp:sconf_def lconf_def envconf_def)
  from eval obtain h l where 
    eval':"P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0(V:=None))\<rangle> \<Rightarrow> \<langle>e\<^sub>2,(h,l)\<rangle>"
    and s2:"s\<^sub>2 = (h,l(V:=l\<^sub>0 V))" by (auto elim:eval_cases)
  from IH[OF eval' wte sconf'] s2 show ?case by simp
next
  case (Seq E e\<^sub>0 s\<^sub>0 v s\<^sub>1 e\<^sub>1 e\<^sub>2 s\<^sub>2 e\<^sub>2' s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>e\<^sub>0;; e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> e\<^sub>0;; e\<^sub>1 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>0 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                     \<Longrightarrow> Val v = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk> 
                     \<Longrightarrow> e\<^sub>2 = ei \<and> s\<^sub>2 = si" by fact+
  from wt obtain T' where wte0:"P,E \<turnstile> e\<^sub>0 :: T'" and wte1:"P,E \<turnstile> e\<^sub>1 :: T" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix s w 
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>" 
      and eval':"P,E \<turnstile> \<langle>e\<^sub>1,s\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    from IH1[OF eval_val wte0 sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_val wte0 sconf have "P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval'[simplified eq] wte1 this] show "e\<^sub>2 = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" .
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
    from IH1[OF eval_throw wte0 sconf] show "e\<^sub>2 = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  qed
next
  case (SeqThrow E e\<^sub>0 s\<^sub>0 e s\<^sub>1 e\<^sub>1 e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>e\<^sub>0;; e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> e\<^sub>0;; e\<^sub>1 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>0 :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                     \<Longrightarrow> throw e = ei \<and> s\<^sub>1 = si" by fact+
  from wt obtain T' where wte0:"P,E \<turnstile> e\<^sub>0 :: T'" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix s w 
    assume eval_val:"P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
    from IH[OF eval_val wte0 sconf] show "throw e = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex 
    assume eval_throw:"P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = throw ex"
    from IH[OF eval_throw wte0 sconf] e2 show "throw e = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (CondT E e s\<^sub>0 s\<^sub>1 e\<^sub>1 e' s\<^sub>2 e\<^sub>2 e\<^sub>2' s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> true = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>1 :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk> 
                    \<Longrightarrow> e' = ei \<and> s\<^sub>2 = si" by fact+
  from wt have wte:"P,E \<turnstile> e :: Boolean" and wte1:"P,E \<turnstile> e\<^sub>1 :: T" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix s 
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>" and eval':"P,E \<turnstile> \<langle>e\<^sub>1,s\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    from IH1[OF eval_true wte sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_true wte sconf have "P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval'[simplified eq] wte1 this] show "e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" .
  next
    fix s assume eval_false:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<rangle>"
    from IH1[OF eval_false wte sconf] show "e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
    from IH1[OF eval_throw wte sconf] show "e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  qed
next
  case (CondF E e s\<^sub>0 s\<^sub>1 e\<^sub>2 e' s\<^sub>2 e\<^sub>1 e\<^sub>2' s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> false = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e\<^sub>2 :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk> 
                    \<Longrightarrow> e' = ei \<and> s\<^sub>2 = si" by fact+
  from wt have wte:"P,E \<turnstile> e :: Boolean" and wte2:"P,E \<turnstile> e\<^sub>2 :: T" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix s 
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>"
    from IH1[OF eval_true wte sconf] show "e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix s
    assume eval_false:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<rangle>"
      and eval':"P,E \<turnstile> \<langle>e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2'\<rangle>"
    from IH1[OF eval_false wte sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_false wte sconf have "P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF eval'[simplified eq] wte2 this] show "e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" .
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
    from IH1[OF eval_throw wte sconf] show "e' = e\<^sub>2' \<and> s\<^sub>2 = s\<^sub>2'" by simp
  qed
next
  case (CondThrow E e s\<^sub>0 e' s\<^sub>1 e\<^sub>1 e\<^sub>2 e\<^sub>2' s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> throw e' = ei \<and> s\<^sub>1 = si" by fact+
  from wt have wte:"P,E \<turnstile> e :: Boolean" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix s 
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>"
    from IH[OF eval_true wte sconf] show "throw e' = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix s assume eval_false:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<rangle>"
    from IH[OF eval_false wte sconf] show "throw e' = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex
    assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2':"e\<^sub>2' = throw ex"
    from IH[OF eval_throw wte sconf] e2' show "throw e' = e\<^sub>2' \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (WhileF E e s\<^sub>0 s\<^sub>1 c e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> while (e) c :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>e\<^sub>2 s\<^sub>2 T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> false = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by fact+
  from wt have wte:"P,E \<turnstile> e :: Boolean" by auto
  from eval show ?case
  proof(rule eval_cases)
    assume eval_false:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = unit"
    from IH[OF eval_false wte sconf] e2 show "unit = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix s s' w
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>"
    from IH[OF eval_true wte sconf] show "unit = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "unit = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex s
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>"
    from IH[OF eval_true wte sconf] show "unit = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (WhileT E e s\<^sub>0 s\<^sub>1 c v\<^sub>1 s\<^sub>2 e\<^sub>3 s\<^sub>3 e\<^sub>2 s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> while (e) c :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> true = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> c :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk> 
                    \<Longrightarrow> Val v\<^sub>1 = ei \<and> s\<^sub>2 = si"
    and IH3:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>while (e) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> while (e) c :: T; 
                         P,E \<turnstile> s\<^sub>2 \<surd>\<rbrakk>
                    \<Longrightarrow> e\<^sub>3 = ei \<and> s\<^sub>3 = si" by fact+
  from wt obtain T' where wte:"P,E \<turnstile> e :: Boolean" and wtc:"P,E \<turnstile> c :: T'" by auto
  from eval show ?case
  proof(rule eval_cases)
    assume eval_false:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>2'\<rangle>"
    from IH1[OF eval_false wte sconf] show "e\<^sub>3 = e\<^sub>2 \<and> s\<^sub>3 = s\<^sub>2'" by simp
  next
    fix s s' w
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>" 
      and eval_val:"P,E \<turnstile> \<langle>c,s\<rangle> \<Rightarrow> \<langle>Val w,s'\<rangle>"
      and eval_while:"P,E \<turnstile> \<langle>while (e) c,s'\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>"
    from IH1[OF eval_true wte sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_true wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
   from IH2[OF eval_val[simplified eq] wtc this] have eq':"s' = s\<^sub>2" by simp
   with wf eval_val wtc sconf' eq have "P,E \<turnstile> s\<^sub>2 \<surd>"
     by(fastforce intro:eval_preserves_sconf)
   from IH3[OF eval_while[simplified eq'] wt this] show "e\<^sub>3 = e\<^sub>2 \<and> s\<^sub>3 = s\<^sub>2'" .
 next
   fix ex assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
   from IH1[OF eval_throw wte sconf] show "e\<^sub>3 = e\<^sub>2 \<and> s\<^sub>3 = s\<^sub>2'" by simp
 next
   fix ex s
   assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>" 
     and eval_throw:"P,E \<turnstile> \<langle>c,s\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
    from IH1[OF eval_true wte sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_true wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
   from IH2[OF eval_throw[simplified eq] wtc this] show "e\<^sub>3 = e\<^sub>2 \<and> s\<^sub>3 = s\<^sub>2'" by simp
 qed
next
  case (WhileCondThrow E e s\<^sub>0 e' s\<^sub>1 c e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> while (e) c :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk>
                    \<Longrightarrow> throw e' = ei \<and> s\<^sub>1 = si" by fact+
  from wt have wte:"P,E \<turnstile> e :: Boolean" by auto
  from eval show ?case
  proof(rule eval_cases)
    assume eval_false:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>2\<rangle>"
    from IH[OF eval_false wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix s s' w
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>"
    from IH[OF eval_true wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex 
    assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = throw ex"
    from IH[OF eval_throw wte sconf] e2 show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex s
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>"
    from IH[OF eval_true wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (WhileBodyThrow E e s\<^sub>0 s\<^sub>1 c e' s\<^sub>2 e\<^sub>2 s\<^sub>2' T)
  have eval:"P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> while (e) c :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> true = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> c :: T; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                   \<Longrightarrow> throw e' = ei \<and> s\<^sub>2 = si" by fact+
  from wt obtain T' where wte:"P,E \<turnstile> e :: Boolean" and wtc:"P,E \<turnstile> c :: T'" by auto
  from eval show ?case
  proof(rule eval_cases)
    assume eval_false:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>2'\<rangle>"
    from IH1[OF eval_false wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix s s' w
    assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>" 
      and eval_val:"P,E \<turnstile> \<langle>c,s\<rangle> \<Rightarrow> \<langle>Val w,s'\<rangle>"
    from IH1[OF eval_true wte sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_true wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
   from IH2[OF eval_val[simplified eq] wtc this] show "throw e' = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'"
     by simp
 next
   fix ex assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
   from IH1[OF eval_throw wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
 next
   fix ex s
   assume eval_true:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<rangle>" 
     and eval_throw:"P,E \<turnstile> \<langle>c,s\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>" and e2:"e\<^sub>2 = throw ex"
   from IH1[OF eval_true wte sconf] have eq:"s = s\<^sub>1" by simp
    with wf eval_true wte sconf have sconf':"P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
   from IH2[OF eval_throw[simplified eq] wtc this] e2 show "throw e' = e\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'"
     by simp
 qed
next
  case (Throw E e s\<^sub>0 r s\<^sub>1 e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> throw e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                   \<Longrightarrow> ref r = ei \<and> s\<^sub>1 = si" by fact+
  from wt obtain C where wte:"P,E \<turnstile> e :: Class C" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix r'
    assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref r',s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = Throw r'"
    from IH[OF eval_ref wte sconf] e2 show "Throw r = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "Throw r = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "Throw r = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (ThrowNull E e s\<^sub>0 s\<^sub>1 e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> throw e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                   \<Longrightarrow> null = ei \<and> s\<^sub>1 = si" by fact+
  from wt obtain C where wte:"P,E \<turnstile> e :: Class C" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix r' assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref r',s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = THROW NullPointer"
    from IH[OF eval_null wte sconf] e2 show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" 
      by simp
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
    from IH[OF eval_throw wte sconf] show "THROW NullPointer = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case (ThrowThrow E e s\<^sub>0 e' s\<^sub>1 e\<^sub>2 s\<^sub>2 T)
  have eval:"P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> throw e :: T" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> throw e' = ei \<and> s\<^sub>1 = si" by fact+
  from wt obtain C where wte:"P,E \<turnstile> e :: Class C" by auto
  from eval show ?case
  proof(rule eval_cases)
    fix r' assume eval_ref:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ref r',s\<^sub>2\<rangle>"
    from IH[OF eval_ref wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    assume eval_null:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>2\<rangle>"
    from IH[OF eval_null wte sconf] show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex 
    assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and e2:"e\<^sub>2 = throw ex"
    from IH[OF eval_throw wte sconf] e2 show "throw e' = e\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
next
  case Nil thus ?case by (auto elim:evals_cases)
next
  case (Cons E e s\<^sub>0 v s\<^sub>1 es es' s\<^sub>2 es\<^sub>2 s\<^sub>2' Ts)
  have evals:"P,E \<turnstile> \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>es\<^sub>2,s\<^sub>2'\<rangle>"
    and wt:"P,E \<turnstile> e#es [::] Ts" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH1:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> Val v = ei \<and> s\<^sub>1 = si"
    and IH2:"\<And>esi si Ts. \<lbrakk>P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>esi,si\<rangle>; P,E \<turnstile> es [::] Ts; P,E \<turnstile> s\<^sub>1 \<surd>\<rbrakk>
                    \<Longrightarrow> es' = esi \<and> s\<^sub>2 = si" by fact+
  from wt obtain T' Ts' where Ts:"Ts = T'#Ts'" by(cases Ts) auto
  with wt have wte:"P,E \<turnstile> e :: T'" and wtes:"P,E \<turnstile> es [::] Ts'" by auto
  from evals show ?case
  proof(rule evals_cases)
    fix es'' s w
    assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
      and evals_vals:"P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es'',s\<^sub>2'\<rangle>" and es2:"es\<^sub>2 = Val w#es''"
    from IH1[OF eval_val wte sconf] have s:"s = s\<^sub>1" and v:"v = w" by simp_all
    with wf eval_val wte sconf have "P,E \<turnstile> s\<^sub>1 \<surd>"
      by(fastforce intro:eval_preserves_sconf)
    from IH2[OF evals_vals[simplified s] wtes this] have "es' = es'' \<and> s\<^sub>2 = s\<^sub>2'" .
    with es2 v show "Val v # es' = es\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
  next
    fix ex assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2'\<rangle>"
    from IH1[OF eval_throw wte sconf] show "Val v # es' = es\<^sub>2 \<and> s\<^sub>2 = s\<^sub>2'" by simp
  qed
next
  case (ConsThrow E e s\<^sub>0 e' s\<^sub>1 es es\<^sub>2 s\<^sub>2 Ts)
  have evals:"P,E \<turnstile> \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>es\<^sub>2,s\<^sub>2\<rangle>"
    and wt:"P,E \<turnstile> e#es [::] Ts" and sconf:"P,E \<turnstile> s\<^sub>0 \<surd>"
    and IH:"\<And>ei si T. \<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>ei,si\<rangle>; P,E \<turnstile> e :: T; P,E \<turnstile> s\<^sub>0 \<surd>\<rbrakk> 
                    \<Longrightarrow> throw e' = ei \<and> s\<^sub>1 = si" by fact+
  from wt obtain T' Ts' where Ts:"Ts = T'#Ts'" by(cases Ts) auto
  with wt have wte:"P,E \<turnstile> e :: T'" by auto
  from evals show ?case
  proof(rule evals_cases)
    fix es'' s w
    assume eval_val:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val w,s\<rangle>"
    from IH[OF eval_val wte sconf] show "throw e'#es = es\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  next
    fix ex 
    assume eval_throw:"P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>" and es2:"es\<^sub>2 = throw ex#es"
    from IH[OF eval_throw wte sconf] es2 show "throw e'#es = es\<^sub>2 \<and> s\<^sub>1 = s\<^sub>2" by simp
  qed
qed


end
