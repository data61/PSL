(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory J/TypeSafe.thy by Tobias Nipkow 
*)

section \<open>Type Safety Proof\<close>

theory TypeSafe
imports HeapExtension CWellForm
begin


subsection\<open>Basic preservation lemmas\<close>

lemma assumes wf:"wwf_prog P" and casts:"P \<turnstile> T casts v to v'"
  and typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T'" and leq:"P \<turnstile> T' \<le> T"
  shows casts_conf:"P,h \<turnstile> v' :\<le> T"

proof -
  { fix a' C Cs S'
    assume leq:"P \<turnstile> Class (last Cs) \<le> T" and subo:"Subobjs P C Cs"
      and casts':"P \<turnstile> T casts Ref (a',Cs) to v'" and h:"h a' = Some(C,S')"
    from subo wf have "is_class P (last Cs)" by(fastforce intro:Subobj_last_isClass)
    with leq wf obtain C' where T:"T = Class C'"
      and path_unique:"P \<turnstile> Path (last Cs) to C' unique"
      by(auto dest:Class_widen)
    from path_unique obtain Cs' where path_via:"P \<turnstile> Path (last Cs) to C' via Cs'"
      by(auto simp:path_via_def path_unique_def)
    with T path_unique casts' have v':"v' = Ref (a',Cs@\<^sub>pCs')"
      by -(erule casts_to.cases,auto simp:path_unique_def path_via_def)
    from subo path_via wf have "Subobjs P C (Cs@\<^sub>pCs')"
      and "last (Cs@\<^sub>pCs') = C'"
      apply(auto intro:Subobjs_appendPath simp:path_via_def)
      apply(drule_tac Cs="Cs'" in Subobjs_nonempty)
      by(rule sym[OF appendPath_last])
    with T h v' have ?thesis by auto }
  with casts typeof wf typeof leq show ?thesis
    by(cases v,auto elim:casts_to.cases split:if_split_asm)
qed



theorem assumes wf:"wwf_prog P"
shows red_preserves_hconf:
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> (\<And>T. \<lbrakk> P,E,h \<turnstile> e : T; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"
and reds_preserves_hconf:
  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> (\<And>Ts. \<lbrakk> P,E,h \<turnstile> es [:] Ts; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"

proof (induct rule:red_reds_inducts)
  case (RedNew h a h' C E l)
  have new: "new_Addr h = Some a" and h':"h' = h(a \<mapsto> (C, Collect (init_obj P C)))"
    and hconf:"P \<turnstile> h \<surd>" and wt_New:"P,E,h \<turnstile> new C : T" by fact+
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  with wf have oconf:"P,h \<turnstile> (C, Collect (init_obj P C)) \<surd>"
    apply (auto simp:oconf_def)
    apply (rule_tac x="init_class_fieldmap P (last Cs)" in exI)
    by (fastforce intro:init_obj.intros fconf_init_fields 
                 elim: init_obj.cases dest!:Subobj_last_isClass simp:is_class_def)+
  thus ?case using h' None by(fast intro: hconf_new[OF hconf])
next
  case (RedFAss h a D S Cs' F T Cs v v' Ds fs' E l T')
  let ?fs' = "fs'(F \<mapsto> v')"
  let ?S' = "insert (Ds, ?fs') (S - {(Ds, fs')})"
  have ha:"h a = Some(D,S)" and hconf:"P \<turnstile> h \<surd>"
    and field:"P \<turnstile> last Cs' has least F:T via Cs"
    and casts:"P \<turnstile> T casts v to v'"
    and Ds:"Ds = Cs' @\<^sub>p Cs" and S:"(Ds,fs') \<in> S"
    and wte:"P,E,h \<turnstile> ref(a,Cs')\<bullet>F{Cs} := Val v : T'" by fact+
  from wte have "P \<turnstile> last Cs' has least F:T' via Cs" by (auto split:if_split_asm)
  with field have eq:"T = T'" by (rule sees_field_fun)
  with casts wte wf have conf:"P,h \<turnstile> v' :\<le> T'"
    by(auto intro:casts_conf)
  from hconf ha have oconf:"P,h \<turnstile> (D,S) \<surd>" by (fastforce simp:hconf_def)
  with S have suboD:"Subobjs P D Ds" by (fastforce simp:oconf_def)
  from field obtain Bs fs ms
    where subo:"Subobjs P (last Cs') Cs"
    and "class": "class P (last Cs) = Some(Bs,fs,ms)"
    and map:"map_of fs F = Some T"
    by (auto simp:LeastFieldDecl_def FieldDecls_def)
  from Ds subo have last:"last Cs = last Ds"
    by(fastforce dest:Subobjs_nonempty intro:appendPath_last simp:appendPath_last)
  with "class" have classDs:"class P (last Ds) = Some(Bs,fs,ms)" by simp
  with S suboD oconf have "P,h \<turnstile> fs' (:\<le>) map_of fs"
    apply (auto simp:oconf_def)
    apply (erule allE)
    apply (erule_tac x="Ds" in allE)
    apply (erule_tac x="fs'" in allE)
    apply clarsimp
    done
  with map conf eq have fconf:"P,h \<turnstile> fs'(F \<mapsto> v') (:\<le>) map_of fs"
    by (simp add:fconf_def)
  from oconf have "\<forall>Cs fs'. (Cs,fs') \<in> S \<longrightarrow> Subobjs P D Cs \<and> 
                    (\<exists>fs Bs ms. class P (last Cs) = Some (Bs,fs,ms) \<and> 
                                P,h \<turnstile> fs' (:\<le>) map_of fs)"
    by(simp add:oconf_def)
  with suboD classDs fconf 
  have oconf':"\<forall>Cs fs'. (Cs,fs') \<in> ?S' \<longrightarrow> Subobjs P D Cs \<and> 
                    (\<exists>fs Bs ms. class P (last Cs) = Some (Bs,fs,ms) \<and> 
                                P,h \<turnstile> fs' (:\<le>) map_of fs)"
    by auto
  from oconf have all:"\<forall>Cs. Subobjs P D Cs \<longrightarrow> (\<exists>!fs'. (Cs,fs') \<in> S)"
    by(simp add:oconf_def)
  with S have "\<forall>Cs. Subobjs P D Cs \<longrightarrow> (\<exists>!fs'. (Cs,fs') \<in> ?S')" by blast
  with oconf' have oconf':"P,h \<turnstile> (D,?S') \<surd>"
    by (simp add:oconf_def)
  with hconf ha show ?case by (rule hconf_upd_obj)
next
  case (CallObj E e h l e' h' l' Copt M es) thus ?case by (cases Copt) auto
next
  case (CallParams E es h l es' h' l' v Copt M) thus ?case by (cases Copt) auto
next
  case (RedCallNull E Copt M vs h l) thus ?case by (cases Copt) auto
qed auto




theorem assumes wf:"wwf_prog P"
shows red_preserves_lconf:
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow>
  (\<And>T. \<lbrakk> P,E,h \<turnstile> e:T; P,h \<turnstile> l (:\<le>)\<^sub>w E; P \<turnstile> E \<surd> \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E)"
and reds_preserves_lconf:
  "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow>
  (\<And>Ts. \<lbrakk> P,E,h \<turnstile> es[:]Ts; P,h \<turnstile> l (:\<le>)\<^sub>w E; P \<turnstile> E \<surd> \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E)"

proof(induct rule:red_reds_inducts)
  case RedNew thus ?case
    by(fast intro:lconf_hext red_hext_incr[OF red_reds.RedNew])
next
  case (RedLAss E V T v v' h l T')
  have casts:"P \<turnstile> T casts v to v'" and env:"E V = Some T"
    and wt:"P,E,h \<turnstile> V:=Val v : T'" and lconf:"P,h \<turnstile> l (:\<le>)\<^sub>w E" by fact+
  from wt env have eq:"T = T'" by auto
  with casts wt wf have conf:"P,h \<turnstile> v' :\<le> T'"
    by(auto intro:casts_conf)
  with lconf env eq show ?case
    by (simp del:fun_upd_apply)(erule lconf_upd,simp_all)
next
  case RedFAss thus ?case
    by(auto intro:lconf_hext red_hext_incr[OF red_reds.RedFAss] 
         simp del:fun_upd_apply)
next
  case (BlockRedNone E V T e h l e' h' l' T')
  have red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH: "\<And>T''. \<lbrakk> P,E(V \<mapsto> T),h \<turnstile> e : T''; P,h \<turnstile> l(V:=None) (:\<le>)\<^sub>w E(V \<mapsto> T);
                      envconf P (E(V \<mapsto> T)) \<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)"
    and lconf: "P,h \<turnstile> l (:\<le>)\<^sub>w E" and wte: "P,E,h \<turnstile> {V:T; e} : T'"
    and envconf:"envconf P E" by fact+
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have lconf':"P,h' \<turnstile> l (:\<le>)\<^sub>w E" .
  from wte have wte':"P,E(V\<mapsto>T),h \<turnstile> e : T'" and type:"is_type P T"
    by (auto elim:WTrt.cases)
  from envconf type have envconf':"envconf P (E(V \<mapsto> T))"
    by(auto simp:envconf_def)
  from lconf have "P,h \<turnstile> (l(V := None)) (:\<le>)\<^sub>w E(V\<mapsto>T)"
    by (simp add:lconf_def fun_upd_apply)
  from IH[OF wte' this envconf'] have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V\<mapsto>T)" .
  with lconf' show ?case
    by (fastforce simp:lconf_def fun_upd_apply split:if_split_asm)
next
  case (BlockRedSome E V T e h l e' h' l' v T')
  have red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH: "\<And>T''. \<lbrakk> P,E(V \<mapsto> T),h \<turnstile> e : T''; P,h \<turnstile> l(V:=None) (:\<le>)\<^sub>w E(V \<mapsto> T);
                      envconf P (E(V \<mapsto> T)) \<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)"
    and lconf: "P,h \<turnstile> l (:\<le>)\<^sub>w E" and wte: "P,E,h \<turnstile> {V:T; e} : T'"
    and envconf:"envconf P E" by fact+
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have lconf':"P,h' \<turnstile> l (:\<le>)\<^sub>w E" .
  from wte have wte':"P,E(V\<mapsto>T),h \<turnstile> e : T'" and type:"is_type P T"
    by (auto elim:WTrt.cases)
  from envconf type have envconf':"envconf P (E(V \<mapsto> T))"
    by(auto simp:envconf_def)
  from lconf have "P,h \<turnstile> (l(V := None)) (:\<le>)\<^sub>w E(V\<mapsto>T)"
    by (simp add:lconf_def fun_upd_apply)
  from IH[OF wte' this envconf'] have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V\<mapsto>T)" .
  with lconf' show ?case
    by (fastforce simp:lconf_def fun_upd_apply split:if_split_asm)
next
  case (InitBlockRed E V T e h l v' e' h' l' v'' v T')
  have red: "P,E(V \<mapsto> T) \<turnstile> \<langle>e, (h, l(V\<mapsto>v'))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
     and IH: "\<And>T''. \<lbrakk> P,E(V \<mapsto> T),h \<turnstile> e : T''; P,h \<turnstile> l(V \<mapsto> v') (:\<le>)\<^sub>w E(V \<mapsto> T); 
                       envconf P (E(V \<mapsto> T)) \<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)"
    and lconf:"P,h \<turnstile> l (:\<le>)\<^sub>w E" and l':"l' V = Some v''"
    and wte:"P,E,h \<turnstile> {V:T; V:=Val v;; e} : T'"
    and casts:"P \<turnstile> T casts v to v'" and envconf:"envconf P E" by fact+
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have lconf':"P,h' \<turnstile> l (:\<le>)\<^sub>w E" .
  from wte obtain T'' where wte':"P,E(V\<mapsto>T),h \<turnstile> e : T'"
    and wt:"P,E(V \<mapsto> T),h \<turnstile> V:=Val v : T''"
    and type:"is_type P T"
    by (auto elim:WTrt.cases)
  from envconf type have envconf':"envconf P (E(V \<mapsto> T))"
    by(auto simp:envconf_def)
  from wt have "T'' = T" by auto
  with wf casts wt have "P,h \<turnstile> v' :\<le> T"
    by(auto intro:casts_conf)
  with lconf have "P,h \<turnstile> l(V \<mapsto> v') (:\<le>)\<^sub>w E(V\<mapsto>T)"
    by -(rule lconf_upd2)
  from IH[OF wte' this envconf'] have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)" .
  with lconf' show ?case
    by (fastforce simp:lconf_def fun_upd_apply split:if_split_asm)
next
  case (CallObj E e h l e' h' l' Copt M es) thus ?case by (cases Copt) auto
next
  case (CallParams E es h l es' h' l' v Copt M) thus ?case by (cases Copt) auto
next
  case (RedCallNull E Copt M vs h l) thus ?case by (cases Copt) auto
qed auto




text\<open>Preservation of definite assignment more complex and requires a
few lemmas first.\<close>

lemma [iff]: "\<And>A. \<lbrakk> length Vs = length Ts; length vs = length Ts\<rbrakk> \<Longrightarrow>
 \<D> (blocks (Vs,Ts,vs,e)) A = \<D> e (A \<squnion> \<lfloor>set Vs\<rfloor>)"

apply(induct Vs Ts vs e rule:blocks_old_induct)
apply(simp_all add:hyperset_defs)
done


lemma red_lA_incr: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A> e \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A> e'"
  and reds_lA_incr: "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A>s es \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A>s es'"
  apply (induct rule:red_reds_inducts)
  apply (simp_all del: fun_upd_apply add: hyperset_defs)
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply auto
  done



text\<open>Now preservation of definite assignment.\<close>

lemma assumes wf: "wf_C_prog P"
shows red_preserves_defass:
  "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow> \<D> e \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom l'\<rfloor>"
and "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow> \<D>s es \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D>s es' \<lfloor>dom l'\<rfloor>"

proof (induct rule:red_reds_inducts)
  case BinOpRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case FAssRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CallObj thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
next
  case (RedCall h l a C S Cs M Ts' T' pns' body' Ds Ts T pns body Cs'
                vs bs new_body E)
  thus ?case
    apply (auto dest!:select_method_wf_mdecl[OF wf] simp:wf_mdecl_def elim!:D_mono')
    apply(cases T') apply auto
    by(rule_tac A="\<lfloor>insert this (set pns)\<rfloor>" in D_mono,clarsimp simp:hyperset_defs,
          assumption)+
next
  case RedStaticCall thus ?case
    apply (auto dest!:has_least_wf_mdecl[OF wf] simp:wf_mdecl_def elim!:D_mono')
    by(auto simp:hyperset_defs)
next
  case InitBlockRed thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case BlockRedNone thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case BlockRedSome thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case SeqRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CondRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case RedWhile thus ?case by(auto simp:hyperset_defs elim!:D_mono')
next
  case ListRed1 thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
qed (auto simp:hyperset_defs)




text\<open>Combining conformance of heap and local variables:\<close>

definition sconf :: "prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> bool"  ("_,_ \<turnstile> _ \<surd>"   [51,51,51]50) where
  "P,E \<turnstile> s \<surd>  \<equiv>  let (h,l) = s in P \<turnstile> h \<surd> \<and> P,h \<turnstile> l (:\<le>)\<^sub>w E \<and> P \<turnstile> E \<surd>"

lemma red_preserves_sconf:
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>; P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd>; wwf_prog P\<rbrakk> 
\<Longrightarrow> P,E \<turnstile> s' \<surd>"

by(fastforce intro:red_preserves_hconf red_preserves_lconf
            simp add:sconf_def)


lemma reds_preserves_sconf:
  "\<lbrakk> P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; P,E \<turnstile> s \<surd>; wwf_prog P\<rbrakk> 
\<Longrightarrow> P,E \<turnstile> s' \<surd>"

by(fastforce intro:reds_preserves_hconf reds_preserves_lconf
            simp add:sconf_def)





subsection "Subject reduction"

lemma wt_blocks:
 "\<And>E. \<lbrakk> length Vs = length Ts; length vs = length Ts;
         \<forall>T' \<in> set Ts. is_type P T'\<rbrakk> \<Longrightarrow>
       (P,E,h \<turnstile> blocks(Vs,Ts,vs,e) : T) =
  (P,E(Vs[\<mapsto>]Ts),h \<turnstile> e:T \<and> 
  (\<exists>Ts'. map (P \<turnstile> typeof\<^bsub>h\<^esub>) vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))"

proof(induct Vs Ts vs e rule:blocks_old_induct)
  case (5 V Vs T' Ts v vs e)
  have length:"length (V#Vs) = length (T'#Ts)" "length (v#vs) = length (T'#Ts)"
    and type:"\<forall>S \<in> set (T'#Ts). is_type P S"
    and IH:"\<And>E. \<lbrakk>length Vs = length Ts; length vs = length Ts;
                  \<forall>S \<in> set Ts. is_type P S\<rbrakk>
     \<Longrightarrow> (P,E,h \<turnstile> blocks (Vs, Ts, vs, e) : T) =
         (P,E(Vs [\<mapsto>] Ts),h \<turnstile> e : T \<and>
            (\<exists>Ts'. map P \<turnstile> typeof\<^bsub>h\<^esub> vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))" by fact+
  from type have typeT':"is_type P T'" and type':"\<forall>S \<in> set Ts. is_type P S"
    by simp_all
  from length have "length Vs = length Ts" "length vs = length Ts"
    by simp_all
  from IH[OF this type'] have eq:"(P,E(V \<mapsto> T'),h \<turnstile> blocks (Vs,Ts,vs,e) : T) =
  (P,E(V \<mapsto> T')(Vs [\<mapsto>] Ts),h \<turnstile> e : T \<and>
   (\<exists>Ts'. map P \<turnstile> typeof\<^bsub>h\<^esub> vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))" .
  show ?case
  proof(rule iffI)
    assume "P,E,h \<turnstile> blocks (V#Vs,T'#Ts,v#vs,e) : T"
    then have wt:"P,E(V \<mapsto> T'),h \<turnstile> V:=Val v : T'"
      and blocks:"P,E(V \<mapsto> T'),h \<turnstile> blocks (Vs,Ts,vs,e) : T" by auto
    from blocks eq obtain Ts' where wte:"P,E(V \<mapsto> T')(Vs [\<mapsto>] Ts),h \<turnstile> e : T"
      and typeof:"map P \<turnstile> typeof\<^bsub>h\<^esub> vs = map Some Ts'" and subs:"P \<turnstile> Ts' [\<le>] Ts"
      by auto
    from wt obtain T'' where "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T''" and "P \<turnstile> T'' \<le> T'"
      by auto
    with wte typeof subs
    show "P,E(V # Vs [\<mapsto>] T' # Ts),h \<turnstile> e : T \<and>
          (\<exists>Ts'. map P \<turnstile> typeof\<^bsub>h\<^esub> (v # vs) = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] (T' # Ts))"
      by auto
  next
    assume "P,E(V # Vs [\<mapsto>] T' # Ts),h \<turnstile> e : T \<and>
      (\<exists>Ts'. map P \<turnstile> typeof\<^bsub>h\<^esub> (v # vs) = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] (T' # Ts))"
    then obtain Ts' where wte:"P,E(V # Vs [\<mapsto>] T' # Ts),h \<turnstile> e : T"
      and typeof:"map P \<turnstile> typeof\<^bsub>h\<^esub> (v # vs) = map Some Ts'"
      and subs:"P \<turnstile> Ts' [\<le>] (T'#Ts)" by auto
    from subs obtain U Us where Ts':"Ts' = U#Us" by(cases Ts') auto
    with wte typeof subs eq have blocks:"P,E(V \<mapsto> T'),h \<turnstile> blocks (Vs,Ts,vs,e) : T"
      by auto
    from Ts' typeof subs have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some U"
      and "P \<turnstile> U \<le> T'" by (auto simp:fun_of_def)
    hence wtval:"P,E(V \<mapsto> T'),h \<turnstile> V:=Val v : T'" by auto
    with blocks typeT' show "P,E,h \<turnstile> blocks (V#Vs,T'#Ts,v#vs,e) : T" by auto
  qed
qed auto




theorem assumes wf: "wf_C_prog P"
shows subject_reduction2: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle> \<Longrightarrow>
  (\<And>T. \<lbrakk> P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T \<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T)"
and subjects_reduction2: "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle> \<Longrightarrow>
  (\<And>Ts.\<lbrakk> P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> es [:] Ts \<rbrakk> \<Longrightarrow> types_conf P E h' es' Ts)"

proof (induct rule:red_reds_inducts)
  case (RedNew h a h' C E l)
  have new:"new_Addr h = Some a" and h':"h' = h(a \<mapsto> (C, Collect (init_obj P C)))" 
    and wt:"P,E,h \<turnstile> new C : T" by fact+
  from wt have eq:"T = Class C" and "class": "is_class P C" by auto
  from "class" have subo:"Subobjs P C [C]" by(rule Subobjs_Base)
  from h' have "h' a = Some(C, Collect (init_obj P C))" by(simp add:map_upd_Some_unfold)
  with subo have "P,E,h' \<turnstile> ref(a,[C]) : Class C" by auto
  with eq show ?case by auto
next
  case (RedNewFail h E C l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" by fact
  from wf have "is_class P OutOfMemory" 
    by (fastforce intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt OutOfMemory,[OutOfMemory])) = Some(Class OutOfMemory)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW OutOfMemory : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (StaticCastRed E e h l e' h' l' C)
  have wt:"P,E,h \<turnstile> \<lparr>C\<rparr>e : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" by fact+
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and isref:"is_refT T'" 
    and "class": "is_class P C" and T:"T = Class C"
    by auto
  from isref have "P,E,h' \<turnstile> \<lparr>C\<rparr>e' : Class C"
  proof(rule refTE)
    assume "T' = NT"
    with IH[OF sconf wte] isref "class" show ?thesis by auto
  next
    fix D assume "T' = Class D"
    with IH[OF sconf wte] isref "class" show ?thesis by auto
  qed
  with T show ?case by (fastforce intro:wt_same_type_typeconf)
next
  case RedStaticCastNull
  thus ?case by (auto elim:WTrt.cases)
next
  case (RedStaticUpCast Cs C Cs' Ds E a h l)
  have wt:"P,E,h \<turnstile> \<lparr>C\<rparr>ref (a,Cs) : T"
    and path_via:"P \<turnstile> Path last Cs to C via Cs'"
    and Ds:"Ds = Cs @\<^sub>p Cs'" by fact+
  from wt have typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs)) = Some(Class(last Cs))"
    and "class": "is_class P C" and T:"T = Class C"
    by auto
  from typeof obtain D S where h:"h a = Some(D,S)" and subo:"Subobjs P D Cs"
    by (auto dest:typeof_Class_Subo split:if_split_asm)
  from path_via subo wf Ds have "Subobjs P D Ds" and last:"last Ds = C"
    by(auto intro!:Subobjs_appendPath appendPath_last[THEN sym] Subobjs_nonempty
            simp:path_via_def)
  with h have "P,E,h \<turnstile> ref (a,Ds) : Class C" by auto
  with T show ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (RedStaticDownCast E C a Cs Cs' h l)
  have "P,E,h \<turnstile> \<lparr>C\<rparr>ref (a,Cs@[C]@Cs') : T" by fact
  hence typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs@[C]@Cs')) = Some(Class(last(Cs@[C]@Cs')))"
    and "class": "is_class P C" and T:"T = Class C"
    by auto
  from typeof obtain D S where h:"h a = Some(D,S)" 
    and subo:"Subobjs P D (Cs@[C]@Cs')"
    by (auto dest:typeof_Class_Subo split:if_split_asm)
  from subo have "Subobjs P D (Cs@[C])" by(fastforce intro:appendSubobj)
  with h have "P,E,h \<turnstile> ref (a,Cs@[C]) : Class C" by auto
  with T show ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (RedStaticCastFail C Cs E a h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" by fact
  from wf have "is_class P ClassCast" 
    by (fastforce intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt ClassCast,[ClassCast])) = Some(Class ClassCast)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW ClassCast : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (DynCastRed E e h l e' h' l' C)
  have wt:"P,E,h \<turnstile> Cast C e : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" by fact+
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and isref:"is_refT T'" 
    and "class": "is_class P C" and T:"T = Class C"
    by auto
  from isref have "P,E,h' \<turnstile> Cast C e' : Class C"
  proof(rule refTE)
    assume "T' = NT"
    with IH[OF sconf wte] isref "class" show ?thesis by auto
  next
    fix D assume "T' = Class D"
    with IH[OF sconf wte] isref "class" show ?thesis by auto
  qed
  with T show ?case by (fastforce intro:wt_same_type_typeconf)
next
  case RedDynCastNull
  thus ?case by (auto elim:WTrt.cases)
next
  case (RedDynCast h l a D S C Cs' E Cs)
  have wt:"P,E,h \<turnstile> Cast C (ref (a,Cs)) : T"
    and path_via:"P \<turnstile> Path D to C via Cs'"
    and hp:"hp (h,l) a = Some(D,S)" by fact+
  from wt have typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs)) = Some(Class(last Cs))"
    and "class": "is_class P C" and T:"T = Class C"
    by auto
  from typeof hp have subo:"Subobjs P D Cs"
    by (auto dest:typeof_Class_Subo split:if_split_asm)
  from path_via subo have "Subobjs P D Cs'" 
    and last:"last Cs' = C" by (auto simp:path_via_def)
  with hp have "P,E,h \<turnstile> ref (a,Cs') : Class C" by auto
  with T show ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (RedStaticUpDynCast Cs C Cs' Ds E a h l)
  have wt:"P,E,h \<turnstile> Cast C (ref (a,Cs)) : T"
    and path_via:"P \<turnstile> Path last Cs to C via Cs'"
    and Ds:"Ds = Cs @\<^sub>p Cs'" by fact+
  from wt have typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs)) = Some(Class(last Cs))"
    and "class": "is_class P C" and T:"T = Class C"
    by auto
  from typeof obtain D S where h:"h a = Some(D,S)" and subo:"Subobjs P D Cs"
    by (auto dest:typeof_Class_Subo split:if_split_asm)
  from path_via subo wf Ds have "Subobjs P D Ds" and last:"last Ds = C"
    by(auto intro!:Subobjs_appendPath appendPath_last[THEN sym] Subobjs_nonempty
            simp:path_via_def)
  with h have "P,E,h \<turnstile> ref (a,Ds) : Class C" by auto
  with T show ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (RedStaticDownDynCast E C a Cs Cs' h l)
  have "P,E,h \<turnstile> Cast C (ref (a,Cs@[C]@Cs')) : T" by fact
  hence typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> (Ref(a,Cs@[C]@Cs')) = Some(Class(last(Cs@[C]@Cs')))"
    and "class": "is_class P C" and T:"T = Class C"
    by auto
  from typeof obtain D S where h:"h a = Some(D,S)" 
    and subo:"Subobjs P D (Cs@[C]@Cs')"
    by (auto dest:typeof_Class_Subo split:if_split_asm)
  from subo have "Subobjs P D (Cs@[C])" by(fastforce intro:appendSubobj)
  with h have "P,E,h \<turnstile> ref (a,Cs@[C]) : Class C" by auto
  with T show ?case by (fastforce intro:wt_same_type_typeconf)
next
  case RedDynCastFail thus ?case by fastforce
next
  case (BinOpRed1 E e h l e' h' l' bop e\<^sub>2)
  have red:"P,E \<turnstile> \<langle>e,(h, l)\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and wt:"P,E,h \<turnstile> e \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" by fact+
  from wt obtain T\<^sub>1 T\<^sub>2 where wte:"P,E,h \<turnstile> e : T\<^sub>1" and wte2:"P,E,h \<turnstile> e\<^sub>2 : T\<^sub>2"
    and binop:"case bop of Eq \<Rightarrow> T = Boolean
                        | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer"
    by auto
  from WTrt_hext_mono[OF wte2 red_hext_incr[OF red]] have wte2':"P,E,h' \<turnstile> e\<^sub>2 : T\<^sub>2" .
  have "P,E,h' \<turnstile> e' \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
  proof (cases bop)
    assume Eq:"bop = Eq"
    from IH[OF sconf wte] obtain T' where "P,E,h' \<turnstile> e' : T'"
      by (cases "T\<^sub>1") auto
    with wte2' binop Eq show ?thesis by(cases bop) auto
  next
    assume Add:"bop = Add"
    with binop have Intg:"T\<^sub>1 = Integer" by simp
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : Integer" by simp
    with wte2' binop Add show ?thesis by(cases bop) auto
  qed
  with binop show ?case by(cases bop) simp_all
next
  case (BinOpRed2 E e h l e' h' l' v\<^sub>1 bop)
  have red:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
    and wt:"P,E,h \<turnstile> Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" by fact+
  from wt obtain T\<^sub>1 T\<^sub>2 where wtval:"P,E,h \<turnstile> Val v\<^sub>1 : T\<^sub>1" and wte:"P,E,h \<turnstile> e : T\<^sub>2"
    and binop:"case bop of Eq \<Rightarrow> T = Boolean
                        | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer"
    by auto
  from WTrt_hext_mono[OF wtval red_hext_incr[OF red]]
  have wtval':"P,E,h' \<turnstile> Val v\<^sub>1 : T\<^sub>1" .
  have "P,E,h' \<turnstile> Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e' : T"
  proof (cases bop)
    assume Eq:"bop = Eq"
    from IH[OF sconf wte] obtain T' where "P,E,h' \<turnstile> e' : T'"
      by (cases "T\<^sub>2") auto
    with wtval' binop Eq show ?thesis by(cases bop) auto
  next
    assume Add:"bop = Add"
    with binop have Intg:"T\<^sub>2 = Integer" by simp
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : Integer" by simp
    with wtval' binop Add show ?thesis by(cases bop) auto
  qed
  with binop show ?case by(cases bop) simp_all
next
  case (RedBinOp bop v\<^sub>1 v\<^sub>2 v E a b) thus ?case
  proof (cases bop)
    case Eq thus ?thesis using RedBinOp by auto
  next
    case Add thus ?thesis using RedBinOp by auto
  qed
next
  case (RedVar h l V v E)
  have l:"lcl (h, l) V = Some v" and sconf:"P,E \<turnstile> (h, l) \<surd>"
    and wt:"P,E,h \<turnstile> Var V : T" by fact+
  hence conf:"P,h \<turnstile> v :\<le> T" by(force simp:sconf_def lconf_def)
  show ?case
  proof(cases "\<forall>C. T \<noteq> Class C")
    case True 
    with conf have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T" by(cases T) auto
    hence "P,E,h \<turnstile> Val v : T" by auto
    thus ?thesis by(rule wt_same_type_typeconf)
  next
    case False
    then obtain C where T:"T = Class C" by auto
    with conf have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C) \<or> P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT"
      by simp
    with T show ?thesis by simp
  qed
next
  case (LAssRed E e h l e' h' l' V)
  have wt:"P,E,h \<turnstile> V:=e : T" and sconf:"P,E \<turnstile> (h, l) \<surd>"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'" by fact+
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and env:"E V = Some T" 
    and sub:"P \<turnstile> T' \<le> T" by auto
  from sconf env have "is_type P T" by(auto simp:sconf_def envconf_def)
  from sub this wf show ?case
  proof(rule subE)
    assume eq:"T' = T" and notclass:"\<forall>C. T' \<noteq> Class C"
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : T" by(cases T) auto
    with eq env have "P,E,h' \<turnstile> V:=e' : T" by auto
    with eq show ?thesis by(cases T) auto
  next
    fix C D
    assume T':"T' = Class C" and T:"T = Class D" 
      and path_unique:"P \<turnstile> Path C to D unique"
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : Class C \<or> P,E,h' \<turnstile> e' : NT"
      by simp
    hence "P,E,h' \<turnstile> V:=e' : T"
    proof(rule disjE)
      assume "P,E,h' \<turnstile> e' : Class C"
      with env T' sub show ?thesis by (fastforce intro:WTrtLAss)
    next
      assume "P,E,h' \<turnstile> e' : NT"
      with env T show ?thesis by (fastforce intro:WTrtLAss)
    qed
    with T show ?thesis by(cases T) auto
  next
    fix C
    assume T':"T' = NT" and T:"T = Class C"
    with IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT" by simp
    with env T show ?thesis by (fastforce intro:WTrtLAss)
  qed
next
  case (RedLAss E V T v v' h l T')
  have env:"E V = Some T" and casts:"P \<turnstile> T casts v to v'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> V:=Val v : T'" by fact+
  show ?case
  proof(cases "\<forall>C. T \<noteq> Class C")
    case True
    with casts wt env show ?thesis
      by(cases T',auto elim!:casts_to.cases)
  next
    case False
    then obtain C where "T = Class C" by auto
    with casts wt env wf show ?thesis
      by(auto elim!:casts_to.cases,
         auto intro!:sym[OF appendPath_last] Subobjs_nonempty split:if_split_asm 
              simp:path_via_def,drule_tac Cs="Cs" in Subobjs_appendPath,auto)
  qed
next
  case (FAccRed E e h l e' h' l' F Cs)
  have red:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
    and wt:"P,E,h \<turnstile> e\<bullet>F{Cs} : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" by fact+
  from wt have "P,E,h' \<turnstile> e'\<bullet>F{Cs} : T"
  proof(rule WTrt_elim_cases)
    fix C assume wte: "P,E,h \<turnstile> e : Class C"
      and field:"P \<turnstile> C has least F:T via Cs"
      and notemptyCs:"Cs \<noteq> []"
    from field have "class": "is_class P C"
      by (fastforce intro:Subobjs_isClass simp add:LeastFieldDecl_def FieldDecls_def)
    from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT \<or> P,E,h' \<turnstile> e' : Class C" by auto
    thus ?thesis
    proof(rule disjE)
      assume "P,E,h' \<turnstile> e' : NT"
      thus ?thesis by (fastforce intro!:WTrtFAccNT)
    next
      assume wte':"P,E,h' \<turnstile> e' : Class C"
      from wte' notemptyCs field show ?thesis by(rule WTrtFAcc)
    qed
  next
    assume wte: "P,E,h \<turnstile> e : NT"
    from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT" by auto
    thus ?thesis by (rule WTrtFAccNT)
  qed
  thus ?case by(rule wt_same_type_typeconf)
next
  case (RedFAcc h l a D S Ds Cs' Cs fs' F v E)
  have h:"hp (h,l) a = Some(D,S)" 
    and Ds:"Ds = Cs'@\<^sub>pCs" and S:"(Ds,fs') \<in> S"
    and fs':"fs' F = Some v" and sconf:"P,E \<turnstile> (h,l) \<surd>"
    and wte:"P,E,h \<turnstile> ref (a,Cs')\<bullet>F{Cs} : T" by fact+
  from wte have field:"P \<turnstile> last Cs' has least F:T via Cs"
    and notemptyCs:"Cs \<noteq> []"
    by (auto split:if_split_asm)
  from h S sconf obtain Bs fs ms where classDs:"class P (last Ds) = Some (Bs,fs,ms)"
    and fconf:"P,h \<turnstile> fs' (:\<le>) map_of fs"
    by (simp add:sconf_def hconf_def oconf_def) blast
  from field Ds have "last Cs = last Ds"
    by (fastforce intro!:appendPath_last Subobjs_nonempty 
                   simp:LeastFieldDecl_def FieldDecls_def)
  with field classDs have map:"map_of fs F =  Some T"
    by (simp add:LeastFieldDecl_def FieldDecls_def)
  with fconf fs' have conf:"P,h \<turnstile> v :\<le> T"
    by (simp add:fconf_def,erule_tac x="F" in allE,fastforce)
  thus ?case by (cases T) auto
next
  case (RedFAccNull E F Cs h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" by fact
  from wf have "is_class P NullPointer" 
    by (fastforce intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt NullPointer,[NullPointer])) = Some(Class NullPointer)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW NullPointer : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastforce intro:wt_same_type_typeconf wf_prog_wwf_prog)
next
  case (FAssRed1 E e h l e' h' l' F Cs e\<^sub>2)
  have red:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
    and wt:"P,E,h \<turnstile> e\<bullet>F{Cs} := e\<^sub>2 : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" by fact+
  from wt have "P,E,h' \<turnstile> e'\<bullet>F{Cs} := e\<^sub>2 : T"
  proof (rule WTrt_elim_cases)
    fix C T' assume wte: "P,E,h \<turnstile> e : Class C"
      and field:"P \<turnstile> C has least F:T via Cs"
      and notemptyCs:"Cs \<noteq> []"
      and wte2:"P,E,h \<turnstile> e\<^sub>2 : T'" and sub:"P \<turnstile> T' \<le> T"
    have wte2': "P,E,h' \<turnstile> e\<^sub>2 : T'"
      by(rule WTrt_hext_mono[OF wte2 red_hext_incr[OF red]])
    from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : Class C \<or> P,E,h' \<turnstile> e' : NT"
      by simp
    thus ?thesis
    proof(rule disjE)
      assume wte':"P,E,h' \<turnstile> e' : Class C"
      from wte' notemptyCs field wte2' sub show ?thesis by (rule WTrtFAss)
    next
      assume wte':"P,E,h' \<turnstile> e' : NT"
      from wte' wte2' sub show ?thesis by (rule WTrtFAssNT)
    qed
  next
    fix T' assume wte:"P,E,h \<turnstile> e : NT"
      and wte2:"P,E,h \<turnstile> e\<^sub>2 : T'" and sub:"P \<turnstile> T' \<le> T"
    have wte2': "P,E,h' \<turnstile> e\<^sub>2 : T'"
      by(rule WTrt_hext_mono[OF wte2 red_hext_incr[OF red]])
    from IH[OF sconf wte] have wte':"P,E,h' \<turnstile> e' : NT" by simp
    from wte' wte2' sub show ?thesis by (rule WTrtFAssNT)
  qed
  thus ?case by(rule wt_same_type_typeconf)
next
  case (FAssRed2 E e h l e' h' l' v F Cs)
  have red:"P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
    and wt:"P,E,h \<turnstile> Val v\<bullet>F{Cs} := e : T"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> 
            \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" by fact+
  from wt have "P,E,h' \<turnstile> Val v\<bullet>F{Cs}:=e' : T"
  proof (rule WTrt_elim_cases)
    fix C T' assume wtval:"P,E,h \<turnstile> Val v : Class C"
      and field:"P \<turnstile> C has least F:T via Cs"
      and notemptyCs:"Cs \<noteq> []"
      and wte:"P,E,h \<turnstile> e : T'"
      and sub:"P \<turnstile> T' \<le> T"
    have wtval':"P,E,h' \<turnstile> Val v : Class C"
      by(rule WTrt_hext_mono[OF wtval red_hext_incr[OF red]])
    from field wf have type:"is_type P T" by(rule least_field_is_type)
    from sub type wf show ?thesis
    proof(rule subE)
      assume "T' = T" and notclass:"\<forall>C. T' \<noteq> Class C"
      from IH[OF sconf wte] notclass have wte':"P,E,h' \<turnstile> e' : T'" 
        by(cases T') auto
      from wtval' notemptyCs field wte' sub show ?thesis
        by(rule WTrtFAss)
    next
      fix C' D assume T':"T' = Class C'" and T:"T = Class D" 
        and path_unique:"P \<turnstile> Path C' to D unique"
      from IH[OF sconf wte] T' have "P,E,h' \<turnstile> e' : Class C' \<or> P,E,h' \<turnstile> e' : NT"
        by simp
      thus ?thesis
      proof(rule disjE)
        assume wte':"P,E,h' \<turnstile> e' : Class C'"
        from wtval' notemptyCs field wte' sub T' show ?thesis 
          by (fastforce intro: WTrtFAss)
      next
        assume wte':"P,E,h' \<turnstile> e' : NT"
        from wtval' notemptyCs field wte' sub T show ?thesis
          by (fastforce intro: WTrtFAss)
      qed
    next
      fix C' assume T':"T' = NT" and T:"T = Class C'"
      from IH[OF sconf wte] T' have wte':"P,E,h' \<turnstile> e' : NT" by simp
      from wtval' notemptyCs field wte' sub T show ?thesis
        by (fastforce intro: WTrtFAss)
    qed
  next
    fix T' assume wtval:"P,E,h \<turnstile> Val v : NT"
      and wte:"P,E,h \<turnstile> e : T'"
      and sub:"P \<turnstile> T' \<le> T"
    have wtval':"P,E,h' \<turnstile> Val v : NT"
      by(rule WTrt_hext_mono[OF wtval red_hext_incr[OF red]])
    from IH[OF sconf wte] sub obtain T'' where wte':"P,E,h' \<turnstile> e' : T''"
      and sub':"P \<turnstile> T'' \<le> T" by (cases T',auto,cases T,auto)
    from wtval' wte' sub' show ?thesis
      by(rule WTrtFAssNT)
  qed
  thus ?case by(rule wt_same_type_typeconf)
next
  case (RedFAss h a D S Cs' F T Cs v v' Ds fs E l T')
  let ?fs' = "fs(F \<mapsto> v')"
  let ?S' = "insert (Ds, ?fs') (S - {(Ds, fs)})"
  let ?h' = "h(a \<mapsto> (D,?S'))"
  have h:"h a = Some(D,S)" and casts:"P \<turnstile> T casts v to v'"
    and field:"P \<turnstile> last Cs' has least F:T via Cs"
    and wt:"P,E,h \<turnstile> ref (a,Cs')\<bullet>F{Cs} := Val v : T'" by fact+
  from wt wf have type:"is_type P T'" 
    by (auto dest:least_field_is_type split:if_split_asm)
  from wt field obtain T'' where wtval:"P,E,h \<turnstile> Val v : T''" and eq:"T = T'" 
    and leq:"P \<turnstile> T'' \<le> T'"
    by (auto dest:sees_field_fun split:if_split_asm)
  from casts eq wtval show ?case
  proof(induct rule:casts_to.induct)
    case (casts_prim T\<^sub>0 w)
    have "T\<^sub>0 = T'" and "\<forall>C. T\<^sub>0 \<noteq> Class C" and wtval':"P,E,h \<turnstile> Val w : T''" by fact+
    with leq have "T' = T''" by(cases T',auto)
    with wtval' have "P,E,h \<turnstile> Val w : T'" by simp
    with h have "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> w))(S-{(Ds,fs)})))) \<turnstile> Val w : T'"
      by(cases w,auto split:if_split_asm)
    thus "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> w))(S-{(Ds,fs)})))) \<turnstile> (Val w) :\<^bsub>NT\<^esub> T'"
      by(rule wt_same_type_typeconf)
  next
    case (casts_null C'')
    have T':"Class C'' = T'" by fact
    have "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> Null))(S-{(Ds,fs)})))) \<turnstile> null : NT"
      by simp
    with sym[OF T']
    show "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> Null))(S-{(Ds,fs)})))) \<turnstile> null :\<^bsub>NT\<^esub> T'"
      by simp
  next
    case (casts_ref Xs C'' Xs' Ds'' a')
    have "Class C'' = T'" and "Ds'' = Xs @\<^sub>p Xs'"
      and "P \<turnstile> Path last Xs to C'' via Xs'"
      and "P,E,h \<turnstile> ref (a', Xs) : T''" by fact+
    with wf have "P,E,h \<turnstile> ref (a',Ds'') : T'"
      by (auto intro!:appendPath_last[THEN sym] Subobjs_nonempty
        split:if_split_asm simp:path_via_def,
        drule_tac Cs="Xs" in Subobjs_appendPath,auto)
    with h have "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> Ref(a',Ds'')))(S-{(Ds,fs)})))) \<turnstile> 
      ref (a',Ds'') : T'"
      by auto
    thus "P,E,(h(a\<mapsto>(D,insert(Ds,fs(F \<mapsto> Ref(a',Ds'')))(S-{(Ds,fs)})))) \<turnstile> 
      ref (a',Ds'') :\<^bsub>NT\<^esub> T'"
      by(rule wt_same_type_typeconf)
  qed
next
  case (RedFAssNull E F Cs v h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" by fact
  from wf have "is_class P NullPointer"
    by (fastforce intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt NullPointer,[NullPointer])) = Some(Class NullPointer)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW NullPointer : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastforce intro:wt_same_type_typeconf wf_prog_wwf_prog)
next
  case (CallObj E e h l e' h' l' Copt M es)
  have red: "P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
   and IH: "\<And>T'. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk>
                 \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
   and sconf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> Call e Copt M es : T" by fact+
  from wt have "P,E,h' \<turnstile> Call e' Copt M es : T"
  proof(cases Copt)
    case None
    with wt have "P,E,h \<turnstile> e\<bullet>M(es) : T" by simp
    hence "P,E,h' \<turnstile> e'\<bullet>M(es) : T"
    proof(rule WTrt_elim_cases)
      fix C Cs Ts Ts' m
      assume wte:"P,E,h \<turnstile> e : Class C"
        and "method":"P \<turnstile> C has least M = (Ts, T, m) via Cs"
        and wtes:"P,E,h \<turnstile> es [:] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts"
      from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT \<or> P,E,h' \<turnstile> e' : Class C" by auto
      thus ?thesis
      proof(rule disjE)
        assume wte':"P,E,h' \<turnstile> e' : NT"
        have "P,E,h' \<turnstile> es [:] Ts'"
          by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
        with wte' show ?thesis by(rule WTrtCallNT)
      next
        assume wte':"P,E,h' \<turnstile> e' : Class C"
        have wtes':"P,E,h' \<turnstile> es [:] Ts'"
          by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
        from wte' "method" wtes' subs show ?thesis by(rule WTrtCall)
      qed
    next
      fix Ts 
      assume wte:"P,E,h \<turnstile> e : NT" and wtes:"P,E,h \<turnstile> es [:] Ts"
      from IH[OF sconf wte] have wte':"P,E,h' \<turnstile> e' : NT" by simp
      have "P,E,h' \<turnstile> es [:] Ts"
        by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
      with wte' show ?thesis by(rule WTrtCallNT)
    qed
    with None show ?thesis by simp
  next
    case (Some C)
    with wt have "P,E,h \<turnstile> e\<bullet>(C::)M(es) : T" by simp
    hence "P,E,h' \<turnstile> e'\<bullet>(C::)M(es) : T"
    proof(rule WTrt_elim_cases)
      fix C' Cs Ts Ts' m
      assume wte:"P,E,h \<turnstile> e : Class C'" and path_unique:"P \<turnstile> Path C' to C unique"
        and "method":"P \<turnstile> C has least M = (Ts, T, m) via Cs"
        and wtes:"P,E,h \<turnstile> es [:] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts"
      from IH[OF sconf wte] have "P,E,h' \<turnstile> e' : NT \<or> P,E,h' \<turnstile> e' : Class C'" by auto
      thus ?thesis
      proof(rule disjE)
        assume wte':"P,E,h' \<turnstile> e' : NT"
        have "P,E,h' \<turnstile> es [:] Ts'"
          by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
        with wte' show ?thesis by(rule WTrtCallNT)
      next
        assume wte':"P,E,h' \<turnstile> e' : Class C'"
        have wtes':"P,E,h' \<turnstile> es [:] Ts'"
          by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
        from wte' path_unique "method" wtes' subs show ?thesis by(rule WTrtStaticCall)
      qed
    next
      fix Ts 
      assume wte:"P,E,h \<turnstile> e : NT" and wtes:"P,E,h \<turnstile> es [:] Ts"
      from IH[OF sconf wte] have wte':"P,E,h' \<turnstile> e' : NT" by simp
      have "P,E,h' \<turnstile> es [:] Ts"
        by(rule WTrts_hext_mono[OF wtes red_hext_incr[OF red]])
      with wte' show ?thesis by(rule WTrtCallNT)
    qed
    with Some show ?thesis by simp
  qed
  thus ?case by (rule wt_same_type_typeconf)
next
  case (CallParams E es h l es' h' l' v Copt M)
  have reds: "P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',(h',l')\<rangle>"
   and IH: "\<And>Ts. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> es [:] Ts\<rbrakk>
                 \<Longrightarrow> types_conf P E h' es' Ts"
   and sconf: "P,E \<turnstile> (h,l) \<surd>" and wt: "P,E,h \<turnstile> Call (Val v) Copt M es : T" by fact+
  from wt have "P,E,h' \<turnstile> Call (Val v) Copt M es' : T"
  proof(cases Copt)
    case None
    with wt have "P,E,h \<turnstile> (Val v)\<bullet>M(es) : T" by simp
    hence "P,E,h' \<turnstile> Val v\<bullet>M(es') : T"
    proof (rule WTrt_elim_cases)
      fix C Cs Ts Ts' m
      assume wte: "P,E,h \<turnstile> Val v : Class C"
        and "method":"P \<turnstile> C has least M = (Ts,T,m) via Cs"
        and wtes: "P,E,h \<turnstile> es [:] Ts'" and subs:"P \<turnstile> Ts' [\<le>] Ts"
      from wtes have "length es = length Ts'" by(rule WTrts_same_length)
      with reds have "length es' = length Ts'"
        by -(drule reds_length,simp)
      with IH[OF sconf wtes] subs obtain Ts'' where wtes':"P,E,h' \<turnstile> es' [:] Ts''"
        and subs':"P \<turnstile> Ts'' [\<le>] Ts" by(auto dest:types_conf_smaller_types)
      have wte':"P,E,h' \<turnstile> Val v : Class C"
        by(rule WTrt_hext_mono[OF wte reds_hext_incr[OF reds]])
      from wte' "method" wtes' subs' show ?thesis
        by(rule WTrtCall)
    next
      fix Ts
      assume wte:"P,E,h \<turnstile> Val v : NT" 
        and wtes:"P,E,h \<turnstile> es [:] Ts"
      from wtes have "length es = length Ts" by(rule WTrts_same_length)
      with reds have "length es' = length Ts"
        by -(drule reds_length,simp)
      with IH[OF sconf wtes] obtain Ts' where wtes':"P,E,h' \<turnstile> es' [:] Ts'"
        and "P \<turnstile> Ts' [\<le>] Ts" by(auto dest:types_conf_smaller_types)
      have wte':"P,E,h' \<turnstile> Val v : NT"
        by(rule WTrt_hext_mono[OF wte reds_hext_incr[OF reds]])
      from wte' wtes' show ?thesis by(rule WTrtCallNT)
    qed
    with None show ?thesis by simp
  next
    case (Some C)
    with wt have "P,E,h \<turnstile> (Val v)\<bullet>(C::)M(es) : T" by simp
    hence "P,E,h' \<turnstile> (Val v)\<bullet>(C::)M(es') : T"
    proof(rule WTrt_elim_cases)
      fix C' Cs Ts Ts' m
      assume wte:"P,E,h \<turnstile> Val v : Class C'" and path_unique:"P \<turnstile> Path C' to C unique"
        and "method":"P \<turnstile> C has least M = (Ts,T,m) via Cs"
        and wtes:"P,E,h \<turnstile> es [:] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts"
      from wtes have "length es = length Ts'" by(rule WTrts_same_length)
      with reds have "length es' = length Ts'"
        by -(drule reds_length,simp)
      with IH[OF sconf wtes] subs obtain Ts'' where wtes':"P,E,h' \<turnstile> es' [:] Ts''"
        and subs':"P \<turnstile> Ts'' [\<le>] Ts" by(auto dest:types_conf_smaller_types)
      have wte':"P,E,h' \<turnstile> Val v : Class C'"
        by(rule WTrt_hext_mono[OF wte reds_hext_incr[OF reds]])
      from wte' path_unique "method" wtes' subs' show ?thesis
        by(rule WTrtStaticCall)
    next
      fix Ts
      assume wte:"P,E,h \<turnstile> Val v : NT" 
        and wtes:"P,E,h \<turnstile> es [:] Ts"
      from wtes have "length es = length Ts" by(rule WTrts_same_length)
      with reds have "length es' = length Ts"
        by -(drule reds_length,simp)
      with IH[OF sconf wtes] obtain Ts' where wtes':"P,E,h' \<turnstile> es' [:] Ts'"
        and "P \<turnstile> Ts' [\<le>] Ts" by(auto dest:types_conf_smaller_types)
      have wte':"P,E,h' \<turnstile> Val v : NT"
        by(rule WTrt_hext_mono[OF wte reds_hext_incr[OF reds]])
      from wte' wtes' show ?thesis by(rule WTrtCallNT)
    qed
    with Some show ?thesis by simp
  qed
  thus ?case by (rule wt_same_type_typeconf)
next
  case (RedCall h l a C S Cs M Ts' T' pns' body' Ds Ts T pns body Cs'
                vs bs new_body E T'')
  have hp:"hp (h,l) a = Some(C,S)"
    and "method":"P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds"
    and select:"P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'"
    and length1:"length vs = length pns" and length2:"length Ts = length pns"
    and bs:"bs = blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body)"
    and body_case:"new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>bs | _ \<Rightarrow> bs)"
    and wt:"P,E,h \<turnstile> ref (a,Cs)\<bullet>M(map Val vs) : T''" by fact+
  from wt hp "method" wf obtain Ts''
    where wtref:"P,E,h \<turnstile> ref (a,Cs) : Class (last Cs)" and eq:"T'' = T'"
    and wtes:"P,E,h \<turnstile> map Val vs [:] Ts''" and subs: "P \<turnstile> Ts'' [\<le>] Ts'"
    by(auto dest:wf_sees_method_fun split:if_split_asm)
  from select wf have "is_class P (last Cs')"
    by(induct rule:SelectMethodDef.induct,
       auto intro:Subobj_last_isClass simp:FinalOverriderMethodDef_def 
      OverriderMethodDefs_def MinimalMethodDefs_def LeastMethodDef_def MethodDefs_def)
  with select_method_wf_mdecl[OF wf select]
  have length_pns:"length (this#pns) = length (Class(last Cs')#Ts)" 
    and notNT:"T \<noteq> NT" and type:"\<forall>T\<in>set (Class(last Cs')#Ts). is_type P T"
    and wtabody:"P,[this\<mapsto>Class(last Cs'),pns[\<mapsto>]Ts] \<turnstile> body :: T"
    by(auto simp:wf_mdecl_def)
  from wtes hp select
  have map:"map (P \<turnstile> typeof\<^bsub>h\<^esub>) (Ref(a,Cs')#vs) = map Some (Class(last Cs')#Ts'')"
    by(auto elim:SelectMethodDef.cases split:if_split_asm 
            simp:FinalOverriderMethodDef_def OverriderMethodDefs_def 
                 MinimalMethodDefs_def LeastMethodDef_def MethodDefs_def)
  from wtref hp have "P \<turnstile> Path C to (last Cs) via Cs"
    by (auto simp:path_via_def split:if_split_asm)
  with select "method" wf have "Ts' = Ts \<and> P \<turnstile> T \<le> T'"
    by -(rule select_least_methods_subtypes,simp_all)
  hence eqs:"Ts' = Ts" and sub:"P \<turnstile> T \<le> T'" by auto
  from wf wtabody have "P,Map.empty(this\<mapsto>Class(last Cs'),pns[\<mapsto>]Ts),h \<turnstile> body : T"
    by -(rule WT_implies_WTrt,simp_all)
  hence wtbody:"P,E(this#pns [\<mapsto>] Class (last Cs')#Ts),h \<turnstile> body : T"
    by(rule WTrt_env_mono) simp
  from wtes have "length vs = length Ts''"
    by (fastforce dest:WTrts_same_length)
  with eqs subs
  have length_vs:"length (Ref(a,Cs')#vs) = length (Class(last Cs')#Ts)"
    by (simp add:list_all2_iff)
  from subs eqs have "P \<turnstile> (Class(last Cs')#Ts'') [\<le>] (Class(last Cs')#Ts)"
    by (simp add:fun_of_def)
  with wt_blocks[OF length_pns length_vs type] wtbody map eq
  have blocks:"P,E,h \<turnstile> blocks(this#pns,Class(last Cs')#Ts,Ref(a,Cs')#vs,body) : T"
    by auto
  have "P,E,h \<turnstile> new_body : T'"
  proof(cases "\<forall>C. T' \<noteq> Class C")
    case True
    with sub notNT have "T = T'" by (cases T') auto
    with blocks True body_case bs show ?thesis by(cases T') auto
  next
    case False
    then obtain D where T':"T' = Class D" by auto
    with "method" sub wf have "class": "is_class P D"
      by (auto elim!:widen.cases dest:least_method_is_type 
               intro:Subobj_last_isClass simp:path_unique_def)
    with blocks T' body_case bs "class" sub show ?thesis
      by(cases T',auto,cases T,auto)
  qed
  with eq show ?case by(fastforce intro:wt_same_type_typeconf)
next
  case (RedStaticCall Cs C Cs'' M Ts T pns body Cs' Ds vs E a h l T')
  have "method":"P \<turnstile> C has least M = (Ts, T, pns, body) via Cs'"
    and length1:"length vs = length pns"
    and length2:"length Ts = length pns"
    and path_unique:"P \<turnstile> Path last Cs to C unique"
    and path_via:"P \<turnstile> Path last Cs to C via Cs''"
    and Ds:"Ds = (Cs @\<^sub>p Cs'') @\<^sub>p Cs'"
    and wt:"P,E,h \<turnstile> ref (a,Cs)\<bullet>(C::)M(map Val vs) : T'" by fact+
  from wt "method" wf obtain Ts'
    where wtref:"P,E,h \<turnstile> ref (a,Cs) : Class (last Cs)"
    and wtes:"P,E,h \<turnstile> map Val vs [:] Ts'" and subs:"P \<turnstile> Ts' [\<le>] Ts"
    and TeqT':"T = T'"
    by(auto dest:wf_sees_method_fun split:if_split_asm)
  from wtref obtain D S where hp:"h a = Some(D,S)" and subo:"Subobjs P D Cs"
    by (auto split:if_split_asm)
  from length1 length2
  have length_vs: "length (Ref(a,Ds)#vs) = length (Class (last Ds)#Ts)" by simp
  from length2 have length_pns:"length (this#pns) = length (Class (last Ds)#Ts)"
    by simp
  from "method" have "Cs' \<noteq> []" 
    by (fastforce intro!:Subobjs_nonempty simp add:LeastMethodDef_def MethodDefs_def)
  with Ds have last:"last Cs' = last Ds"
    by (fastforce dest:appendPath_last)
  with "method" have "is_class P (last Ds)"
    by(auto simp:LeastMethodDef_def MethodDefs_def is_class_def)
  with last has_least_wf_mdecl[OF wf "method"]
  have wtabody: "P,[this#pns [\<mapsto>] Class (last Ds)#Ts] \<turnstile> body :: T"
    and type:"\<forall>T\<in>set (Class(last Ds)#Ts). is_type P T"
    by(auto simp:wf_mdecl_def)
  from path_via have suboCs'':"Subobjs P (last Cs) Cs''" 
    and lastCs'':"last Cs'' = C" 
    by (auto simp add:path_via_def)
  with subo wf have subo':"Subobjs P D (Cs@\<^sub>pCs'')"
     by(fastforce intro: Subobjs_appendPath)
   from lastCs'' suboCs'' have lastC:"C = last(Cs@\<^sub>pCs'')"
     by (fastforce dest:Subobjs_nonempty intro:appendPath_last)
  from "method" have "Subobjs P C Cs'"
    by (auto simp:LeastMethodDef_def MethodDefs_def)
  with subo' wf lastC have "Subobjs P D ((Cs @\<^sub>p Cs'') @\<^sub>p Cs')"
    by (fastforce intro:Subobjs_appendPath)
  with Ds have suboDs:"Subobjs P D Ds" by simp
  from wtabody have "P,Map.empty(this#pns [\<mapsto>] Class (last Ds)#Ts),h \<turnstile> body : T"
    by(rule WT_implies_WTrt)
  hence "P,E(this#pns [\<mapsto>] Class (last Ds)#Ts),h \<turnstile> body : T"
    by(rule WTrt_env_mono) simp
  hence "P,E,h \<turnstile> blocks(this#pns, Class (last Ds)#Ts, Ref(a,Ds)#vs, body) : T"
    using wtes subs wt_blocks[OF length_pns length_vs type] hp suboDs
    by(auto simp add:rel_list_all2_Cons2)
  with TeqT' show ?case by(fastforce intro:wt_same_type_typeconf)
next
  case (RedCallNull E Copt M vs h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" by fact
  from wf have "is_class P NullPointer" 
    by (fastforce intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt NullPointer,[NullPointer])) = Some(Class NullPointer)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW NullPointer : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (BlockRedNone E V T e h l e' h' l' T')
  have IH:"\<And>T'. \<lbrakk>P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>; P,E(V \<mapsto> T),h \<turnstile> e : T'\<rbrakk>
                 \<Longrightarrow> P,E(V \<mapsto> T),h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> {V:T; e} : T'" by fact+
  from wt have type:"is_type P T" and wte:"P,E(V\<mapsto>T),h \<turnstile> e : T'" by auto
  from sconf type have "P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>"
    by (auto simp:sconf_def lconf_def envconf_def)
  from IH[OF this wte] type show ?case by (cases T') auto
next
  case (BlockRedSome E V T e h l e' h' l' v T')
  have red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V := None))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH:"\<And>T'. \<lbrakk>P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>; P,E(V \<mapsto> T),h \<turnstile> e : T'\<rbrakk>
                  \<Longrightarrow> P,E(V \<mapsto> T),h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and Some:"l' V = Some v"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> {V:T; e} : T'" by fact+
  from wt have wte:"P,E(V\<mapsto>T),h \<turnstile> e : T'"  and type:"is_type P T" by auto
  with sconf wf red type have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)"
    by -(auto simp:sconf_def,rule red_preserves_lconf,
         auto intro:wf_prog_wwf_prog simp:envconf_def lconf_def)
  hence conf:"P,h' \<turnstile> v :\<le> T" using Some 
    by(auto simp:lconf_def,erule_tac x="V" in allE,clarsimp)
  have wtval:"P,E(V \<mapsto> T),h' \<turnstile> V:=Val v : T"
  proof(cases T)
    case Void with conf show ?thesis by auto
  next
    case Boolean with conf show ?thesis by auto
  next
    case Integer with conf show ?thesis by auto
  next
    case NT with conf show ?thesis by auto
  next
    case (Class C)
    with conf have "P,E(V \<mapsto> T),h' \<turnstile> Val v : T \<or> P,E(V \<mapsto> T),h' \<turnstile> Val v : NT"
      by auto
    with Class show ?thesis by auto
  qed
  from sconf type have "P,E(V \<mapsto> T) \<turnstile> (h, l(V := None)) \<surd>"
    by (auto simp:sconf_def lconf_def envconf_def)
  from IH[OF this wte] wtval type show ?case by(cases T') auto
next
  case (InitBlockRed E V T e h l v' e' h' l' v'' v T')
  have red:"P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h, l(V \<mapsto> v'))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH:"\<And>T'. \<lbrakk>P,E(V \<mapsto> T) \<turnstile> (h, l(V \<mapsto> v')) \<surd>; P,E(V \<mapsto> T),h \<turnstile> e : T'\<rbrakk>
              \<Longrightarrow> P,E(V \<mapsto> T),h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and Some:"l' V = Some v''" and casts:"P \<turnstile> T casts v to v'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> {V:T := Val v; e} : T'" by fact+
  from wt have wte:"P,E(V \<mapsto> T),h \<turnstile> e : T'" and wtval:"P,E(V \<mapsto> T),h \<turnstile> V:=Val v : T"
    and type:"is_type P T"
    by auto
  from wf casts wtval have "P,h \<turnstile> v' :\<le> T"
    by(fastforce intro!:casts_conf wf_prog_wwf_prog)
  with sconf have lconf:"P,h \<turnstile> l(V \<mapsto> v') (:\<le>)\<^sub>w E(V \<mapsto> T)"
    by (fastforce intro!:lconf_upd2 simp:sconf_def)
  from sconf type have "envconf P (E(V \<mapsto> T))" by(simp add:sconf_def envconf_def)
  from red_preserves_lconf[OF wf_prog_wwf_prog[OF wf] red wte lconf this]
  have "P,h' \<turnstile> l' (:\<le>)\<^sub>w E(V \<mapsto> T)" .
  with Some have "P,h' \<turnstile> v'' :\<le> T"
    by(simp add:lconf_def,erule_tac x="V" in allE,auto)
  hence wtval':"P,E(V \<mapsto> T),h' \<turnstile> V:=Val v'' : T"
    by(cases T) auto
  from lconf sconf type have "P,E(V \<mapsto> T) \<turnstile> (h, l(V \<mapsto> v')) \<surd>"
    by(auto simp:sconf_def envconf_def)
  from IH[OF this wte] wtval' type show ?case by(cases T') auto
next
  case RedBlock thus ?case by (fastforce intro:wt_same_type_typeconf)
next
  case RedInitBlock thus ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (SeqRed E e h l e' h' l' e\<^sub>2 T)
  have red:"P,E \<turnstile> \<langle>e,(h, l)\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH:"\<And>T'. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> e : T'\<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T'"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> e;; e\<^sub>2 : T" by fact+
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and wte2:"P,E,h \<turnstile> e\<^sub>2 : T" by auto
  from WTrt_hext_mono[OF wte2 red_hext_incr[OF red]] have wte2':"P,E,h' \<turnstile> e\<^sub>2 : T" .
  from IH[OF sconf wte] obtain T'' where "P,E,h' \<turnstile> e' : T''" by(cases T') auto
  with wte2' have "P,E,h' \<turnstile> e';; e\<^sub>2 : T" by auto
  thus ?case by(rule wt_same_type_typeconf)
next
  case RedSeq thus ?case by (fastforce intro:wt_same_type_typeconf)
next
  case (CondRed E e h l e' h' l' e\<^sub>1 e\<^sub>2)
  have red:"P,E \<turnstile> \<langle>e,(h, l)\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH: "\<And>T. \<lbrakk>P,E \<turnstile> (h,l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk>
                     \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T"
    and wt:"P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 : T"
    and sconf:"P,E \<turnstile> (h,l) \<surd>" by fact+
  from wt have wte:"P,E,h \<turnstile> e : Boolean"
      and wte1:"P,E,h \<turnstile> e\<^sub>1 : T" and wte2:"P,E,h \<turnstile> e\<^sub>2 : T" by auto
  from IH[OF sconf wte] have wte':"P,E,h' \<turnstile> e' : Boolean" by auto
  from wte' WTrt_hext_mono[OF wte1 red_hext_incr[OF red]]
    WTrt_hext_mono[OF wte2 red_hext_incr[OF red]]
  have "P,E,h' \<turnstile> if (e') e\<^sub>1 else e\<^sub>2 : T"
    by (rule WTrtCond)
  thus ?case by(rule wt_same_type_typeconf)
next
  case RedCondT thus ?case by (fastforce intro: wt_same_type_typeconf)
next
  case RedCondF thus ?case by (fastforce intro: wt_same_type_typeconf)
next
  case RedWhile thus ?case by (fastforce intro: wt_same_type_typeconf)
next
  case (ThrowRed E e h l e' h' l' T)
  have IH:"\<And>T. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> throw e : T" by fact+
  from wt obtain T' where wte:"P,E,h \<turnstile> e : T'" and ref:"is_refT T'"
    by auto
  from ref have "P,E,h' \<turnstile> throw e' : T"
  proof(rule refTE)
    assume T':"T' = NT"
    with wte have "P,E,h \<turnstile> e : NT" by simp
    from IH[OF sconf this] ref T' show ?thesis by auto
    
  next
    fix C assume T':"T' = Class C"
    with wte have "P,E,h \<turnstile> e : Class C" by simp
    from IH[OF sconf this] have "P,E,h' \<turnstile> e' : Class C \<or> P,E,h' \<turnstile> e' : NT"
      by simp
    thus ?thesis
    proof(rule disjE)
      assume wte':"P,E,h' \<turnstile> e' : Class C"
      have "is_refT (Class C)" by simp
      with wte' show ?thesis by auto
    next
      assume wte':"P,E,h' \<turnstile> e' : NT"
      have "is_refT NT" by simp
      with wte' show ?thesis by auto
    qed
  qed
  thus ?case by (rule wt_same_type_typeconf)
next
  case (RedThrowNull E h l)
  have sconf:"P,E \<turnstile> (h, l) \<surd>" by fact
  from wf have "is_class P NullPointer"
    by (fastforce intro:is_class_xcpt wf_prog_wwf_prog)
  hence "preallocated h \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> (Ref (addr_of_sys_xcpt NullPointer,[NullPointer])) = Some(Class NullPointer)"
    by (auto elim: preallocatedE dest!:preallocatedD Subobjs_Base)
  with sconf have "P,E,h \<turnstile> THROW NullPointer : T" by(auto simp:sconf_def hconf_def)
  thus ?case by (fastforce intro:wt_same_type_typeconf wf_prog_wwf_prog)
next
  case (ListRed1 E e h l e' h' l' es Ts)
  have red:"P,E \<turnstile> \<langle>e,(h, l)\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
    and IH:"\<And>T. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> e : T\<rbrakk> \<Longrightarrow> P,E,h' \<turnstile> e' :\<^bsub>NT\<^esub> T"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> e # es [:] Ts" by fact+
  from wt obtain U Us where Ts:"Ts = U#Us" by(cases Ts) auto
  with wt have wte:"P,E,h \<turnstile> e : U" and wtes:"P,E,h \<turnstile> es [:] Us" by simp_all
  from WTrts_hext_mono[OF wtes red_hext_incr[OF red]] 
  have wtes':"P,E,h' \<turnstile> es [:] Us" .
  hence "length es = length Us" by (rule WTrts_same_length)
  with wtes' have "types_conf P E h' es Us"
    by (fastforce intro:wts_same_types_typesconf)
  with IH[OF sconf wte] Ts show ?case by simp
next
  case (ListRed2 E es h l es' h' l' v Ts)
  have reds:"P,E \<turnstile> \<langle>es,(h, l)\<rangle> [\<rightarrow>] \<langle>es',(h', l')\<rangle>"
    and IH:"\<And>Ts. \<lbrakk>P,E \<turnstile> (h, l) \<surd>; P,E,h \<turnstile> es [:] Ts\<rbrakk> \<Longrightarrow> types_conf P E h' es' Ts"
    and sconf:"P,E \<turnstile> (h, l) \<surd>" and wt:"P,E,h \<turnstile> Val v#es [:] Ts" by fact+
  from wt obtain U Us where Ts:"Ts = U#Us" by(cases Ts) auto
  with wt have wtval:"P,E,h \<turnstile> Val v : U" and wtes:"P,E,h \<turnstile> es [:] Us" by simp_all
  from WTrt_hext_mono[OF wtval reds_hext_incr[OF reds]]
  have "P,E,h' \<turnstile> Val v : U" .
  hence "P,E,h' \<turnstile> (Val v) :\<^bsub>NT\<^esub> U" by(rule wt_same_type_typeconf)
  with IH[OF sconf wtes] Ts show ?case by simp
next
  case (CallThrowObj E h l Copt M es h' l')
  thus ?case by(cases Copt)(auto intro:wt_same_type_typeconf)
next
  case (CallThrowParams es vs h l es' E v Copt M h' l')
  thus ?case by(cases Copt)(auto intro:wt_same_type_typeconf)
qed (fastforce intro:wt_same_type_typeconf)+



corollary subject_reduction:
  "\<lbrakk> wf_C_prog P; P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
  \<Longrightarrow> P,E,(hp s') \<turnstile> e' :\<^bsub>NT\<^esub> T"
by(cases s, cases s', fastforce dest:subject_reduction2)

corollary subjects_reduction:
  "\<lbrakk> wf_C_prog P; P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> es[:]Ts \<rbrakk>
  \<Longrightarrow> types_conf P E (hp s') es' Ts"
by(cases s, cases s', fastforce dest:subjects_reduction2)


subsection \<open>Lifting to \<open>\<rightarrow>*\<close>\<close>

text\<open>Now all these preservation lemmas are first lifted to the transitive
closure \dots\<close>

lemma step_preserves_sconf:
assumes wf: "wf_C_prog P" and step: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. \<lbrakk> P,E,hp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"

using step
proof (induct rule:converse_rtrancl_induct2)
  case refl show ?case by fact 
next
  case step
  thus ?case using wf
    apply simp
    apply (frule subject_reduction[OF wf])
      apply (rule step.prems)
      apply (rule step.prems)
      apply (cases T)
      apply (auto dest:red_preserves_sconf intro:wf_prog_wwf_prog)
      done
qed

lemma steps_preserves_sconf:
assumes wf: "wf_C_prog P" and step: "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"
shows "\<And>Ts. \<lbrakk> P,E,hp s \<turnstile> es [:] Ts; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"

using step
proof (induct rule:converse_rtrancl_induct2)
  case refl show ?case by fact
next
  case (step es s es'' s'' Ts)
  have Reds:"((es, s), es'', s'') \<in> Reds P E"
    and reds:"P,E \<turnstile> \<langle>es'',s''\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"
    and wtes:"P,E,hp s \<turnstile> es [:] Ts"
    and sconf:"P,E \<turnstile> s \<surd>"
    and IH:"\<And>Ts. \<lbrakk>P,E,hp s'' \<turnstile> es'' [:] Ts; P,E \<turnstile> s'' \<surd>\<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>" by fact+
  from Reds have reds1:"P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es'',s''\<rangle>" by simp
  from subjects_reduction[OF wf this sconf wtes] 
  have type:"types_conf P E (hp s'') es'' Ts" .
  from reds1 wtes sconf wf have sconf':"P,E \<turnstile> s'' \<surd>" 
    by(fastforce intro:wf_prog_wwf_prog reds_preserves_sconf)
  from type have "\<exists>Ts'. P,E,hp s'' \<turnstile> es'' [:] Ts'"
  proof (induct Ts arbitrary: es'')
    fix esi
    assume "types_conf P E (hp s'') esi []"
    thus "\<exists>Ts'. P,E,hp s'' \<turnstile> esi [:] Ts'"
    proof(induct esi)
      case Nil thus "\<exists>Ts'. P,E,hp s'' \<turnstile> [] [:] Ts'" by simp
    next
      fix ex esx
      assume "types_conf P E (hp s'') (ex#esx) []"
      thus "\<exists>Ts'. P,E,hp s'' \<turnstile> ex#esx [:] Ts'" by simp
    qed
  next
    fix T' Ts' esi
    assume type':"types_conf P E (hp s'') esi (T'#Ts')"
      and IH:"\<And>es''. types_conf P E (hp s'') es'' Ts' \<Longrightarrow>
                      \<exists>Ts''. P,E,hp s'' \<turnstile> es'' [:] Ts''"
    from type' show "\<exists>Ts'. P,E,hp s'' \<turnstile> esi [:] Ts'"
    proof(induct esi)
      case Nil thus "\<exists>Ts'. P,E,hp s'' \<turnstile> [] [:] Ts'" by simp
    next
      fix ex esx
      assume "types_conf P E (hp s'') (ex#esx) (T'#Ts')"
      hence type':"P,E,hp s'' \<turnstile> ex :\<^bsub>NT\<^esub> T'" 
        and types':"types_conf P E (hp s'') esx Ts'" by simp_all
      from type' obtain Tx where type'':"P,E,hp s'' \<turnstile> ex : Tx"
        by(cases T') auto
      from IH[OF types'] obtain Tsx where "P,E,hp s'' \<turnstile> esx [:] Tsx" by auto
      with type'' show "\<exists>Ts'. P,E,hp s'' \<turnstile> ex#esx [:] Ts'" by auto
    qed
  qed
  then obtain Ts' where "P,E,hp s'' \<turnstile> es'' [:] Ts'" by blast
  from IH[OF this sconf'] show ?case .
qed


lemma step_preserves_defass:
assumes wf: "wf_C_prog P" and step: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<D> e \<lfloor>dom(lcl s)\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom(lcl s')\<rfloor>"

using step
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case .
next
  case (step e s e' s') thus ?case
    by(cases s,cases s')(auto dest:red_preserves_defass[OF wf])
qed



lemma step_preserves_type:
assumes wf: "wf_C_prog P" and step: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. \<lbrakk> P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> e:T \<rbrakk>
    \<Longrightarrow> P,E,(hp s') \<turnstile> e' :\<^bsub>NT\<^esub> T"

using step
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case by -(rule wt_same_type_typeconf)
next
  case (step e s e'' s'' T) thus ?case using wf
    apply simp
    apply (frule subject_reduction[OF wf])
    apply (auto dest!:red_preserves_sconf intro:wf_prog_wwf_prog)
    apply(cases T)
    apply fastforce+
    done
qed


text\<open>predicate to show the same lemma for lists\<close>

fun
  conformable :: "ty list \<Rightarrow> ty list \<Rightarrow> bool"
where
  "conformable [] [] \<longleftrightarrow> True"
  | "conformable (T''#Ts'') (T'#Ts') \<longleftrightarrow> (T'' = T'
     \<or> (\<exists>C. T'' = NT \<and> T' = Class C)) \<and> conformable Ts'' Ts'"
  | "conformable _ _ \<longleftrightarrow> False"

lemma types_conf_conf_types_conf:
  "\<lbrakk>types_conf P E h es Ts; conformable Ts Ts'\<rbrakk> \<Longrightarrow> types_conf P E h es Ts'"
proof (induct Ts arbitrary: Ts' es)
  case Nil thus ?case by (cases Ts') (auto split: if_split_asm)
next
  case (Cons T'' Ts'')
  have type:"types_conf P E h es (T''#Ts'')"
    and conf:"conformable (T''#Ts'') Ts'"
    and IH:"\<And>Ts' es. \<lbrakk>types_conf P E h es Ts''; conformable Ts'' Ts'\<rbrakk>
                   \<Longrightarrow> types_conf P E h es Ts'" by fact+
  from type obtain e' es' where es:"es = e'#es'" by (cases es) auto
  with type have type':"P,E,h \<turnstile> e' :\<^bsub>NT\<^esub> T''"
    and types': "types_conf P E h es' Ts''"
    by simp_all
  from conf obtain U Us where Ts': "Ts' = U#Us" by (cases Ts') auto
  with conf have disj:"T'' = U \<or> (\<exists>C. T'' = NT \<and> U = Class C)"
    and conf':"conformable Ts'' Us"
    by simp_all
  from type' disj have "P,E,h \<turnstile> e' :\<^bsub>NT\<^esub> U" by auto
  with IH[OF types' conf'] Ts' es show ?case by simp
qed


lemma types_conf_Wtrt_conf:
  "types_conf P E h es Ts \<Longrightarrow> \<exists>Ts'. P,E,h \<turnstile> es [:] Ts' \<and> conformable Ts' Ts"
proof (induct Ts arbitrary: es)
  case Nil thus ?case by (cases es) (auto split:if_split_asm)
next
  case (Cons T'' Ts'')
  have type:"types_conf P E h es (T''#Ts'')"
    and IH:"\<And>es. types_conf P E h es Ts'' \<Longrightarrow>
                  \<exists>Ts'. P,E,h \<turnstile> es [:] Ts' \<and> conformable Ts' Ts''" by fact+
  from type obtain e' es' where es:"es = e'#es'" by (cases es) auto
  with type have type':"P,E,h \<turnstile> e' :\<^bsub>NT\<^esub> T''"
    and types': "types_conf P E h es' Ts''"
    by simp_all
  from type' obtain T' where "P,E,h \<turnstile> e' : T'" and 
    "T' = T'' \<or> (\<exists>C. T' = NT \<and> T'' = Class C)" by(cases T'') auto
  with IH[OF types'] es show ?case 
    by(auto,rule_tac x="T''#Ts'" in exI,simp,rule_tac x="NT#Ts'" in exI,simp)
qed



lemma steps_preserves_types:
assumes wf: "wf_C_prog P" and steps: "P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"
shows "\<And>Ts. \<lbrakk> P,E \<turnstile> s \<surd>; P,E,hp s \<turnstile> es [:] Ts\<rbrakk>
  \<Longrightarrow> types_conf P E (hp s') es' Ts"
  
using steps
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case by -(rule wts_same_types_typesconf)
next
  case (step es s es'' s'' Ts)
  have Reds:"((es, s), es'', s'') \<in> Reds P E"
    and steps:"P,E \<turnstile> \<langle>es'',s''\<rangle> [\<rightarrow>]* \<langle>es',s'\<rangle>"
    and sconf:"P,E \<turnstile> s \<surd>" and wtes:"P,E,hp s \<turnstile> es [:] Ts"
    and IH:"\<And>Ts. \<lbrakk>P,E \<turnstile> s'' \<surd>; P,E,hp s'' \<turnstile> es'' [:] Ts \<rbrakk> 
               \<Longrightarrow> types_conf P E (hp s') es' Ts" by fact+
  from Reds have step:"P,E \<turnstile> \<langle>es,s\<rangle> [\<rightarrow>] \<langle>es'',s''\<rangle>" by simp
  with wtes sconf wf have sconf':"P,E \<turnstile> s'' \<surd>"
    by(auto intro:reds_preserves_sconf wf_prog_wwf_prog)
  from wtes have "length es = length Ts" by(fastforce dest:WTrts_same_length)
  from step sconf wtes
  have type': "types_conf P E (hp s'') es'' Ts"
    by (rule subjects_reduction[OF wf])
  then obtain Ts' where wtes'':"P,E,hp s'' \<turnstile> es'' [:] Ts'" 
    and conf:"conformable Ts' Ts" by (auto dest:types_conf_Wtrt_conf)
  from IH[OF sconf' wtes''] have "types_conf P E (hp s') es' Ts'" .
  with conf show ?case by(fastforce intro:types_conf_conf_types_conf)
qed
  

subsection \<open>Lifting to \<open>\<Rightarrow>\<close>\<close>

text\<open>\dots and now to the big step semantics, just for fun.\<close>

lemma eval_preserves_sconf:
  "\<lbrakk> wf_C_prog P; P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> e::T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"

by(blast intro:step_preserves_sconf big_by_small WT_implies_WTrt wf_prog_wwf_prog)

lemma evals_preserves_sconf:
  "\<lbrakk> wf_C_prog P; P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>; P,E \<turnstile> es [::] Ts; P,E \<turnstile> s \<surd> \<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> s' \<surd>"
  by(blast intro:steps_preserves_sconf bigs_by_smalls WTs_implies_WTrts 
                 wf_prog_wwf_prog)



lemma eval_preserves_type: assumes wf: "wf_C_prog P"
shows "\<lbrakk> P,E \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E \<turnstile> e::T \<rbrakk>
   \<Longrightarrow> P,E,(hp s') \<turnstile> e' :\<^bsub>NT\<^esub> T"

  using wf
  by (auto dest!:big_by_small[OF wf_prog_wwf_prog[OF wf]] WT_implies_WTrt 
           intro:wf_prog_wwf_prog
           dest!:step_preserves_type[OF wf])


lemma evals_preserves_types: assumes wf: "wf_C_prog P"
shows "\<lbrakk> P,E \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>; P,E \<turnstile> s \<surd>; P,E \<turnstile> es [::] Ts \<rbrakk>
  \<Longrightarrow> types_conf P E (hp s') es' Ts"
using wf
  by (auto dest!:bigs_by_smalls[OF wf_prog_wwf_prog[OF wf]] WTs_implies_WTrts
           intro:wf_prog_wwf_prog
           dest!:steps_preserves_types[OF wf])


subsection \<open>The final polish\<close>

text\<open>The above preservation lemmas are now combined and packed nicely.\<close>

definition wf_config :: "prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_,_ \<turnstile> _ : _ \<surd>"   [51,0,0,0,0]50) where
  "P,E,s \<turnstile> e:T \<surd>  \<equiv>  P,E \<turnstile> s \<surd> \<and> P,E,hp s \<turnstile> e : T"

theorem Subject_reduction: assumes wf: "wf_C_prog P"
shows "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P,E,s \<turnstile> e : T \<surd>
       \<Longrightarrow> P,E,(hp s') \<turnstile> e' :\<^bsub>NT\<^esub> T"

  using wf
  by (force elim!:red_preserves_sconf intro:wf_prog_wwf_prog 
            dest:subject_reduction[OF wf] simp:wf_config_def)



theorem Subject_reductions:
assumes wf: "wf_C_prog P" and reds: "P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
shows "\<And>T. P,E,s \<turnstile> e : T \<surd> \<Longrightarrow> P,E,(hp s') \<turnstile> e' :\<^bsub>NT\<^esub> T"

using reds
proof (induct rule:converse_rtrancl_induct2)
  case refl thus ?case
    by (fastforce intro:wt_same_type_typeconf simp:wf_config_def)
next
  case (step e s e'' s'' T)
  have Red:"((e, s), e'', s'') \<in> Red P E"
    and IH:"\<And>T. P,E,s'' \<turnstile> e'' : T \<surd> \<Longrightarrow> P,E,(hp s') \<turnstile> e' :\<^bsub>NT\<^esub> T"
    and wte:"P,E,s \<turnstile> e : T \<surd>" by fact+
  from Red have red:"P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e'',s''\<rangle>" by simp
  from red_preserves_sconf[OF red] wte wf have sconf:"P,E \<turnstile> s'' \<surd>"
    by(fastforce dest:wf_prog_wwf_prog simp:wf_config_def)
  from wf red wte have type_conf:"P,E,(hp s'') \<turnstile> e'' :\<^bsub>NT\<^esub> T"
    by(rule Subject_reduction)
  show ?case
  proof(cases T)
    case Void
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T" by simp
    with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
    from IH[OF this] show ?thesis .
  next
    case Boolean
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T" by simp
    with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
    from IH[OF this] show ?thesis .
  next
    case Integer
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T" by simp
    with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
    from IH[OF this] show ?thesis .
  next
    case NT
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T" by simp
    with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
    from IH[OF this] show ?thesis .
  next
    case (Class C)
    with type_conf have "P,E,hp s'' \<turnstile> e'' : T \<or> P,E,hp s'' \<turnstile> e'' : NT" by simp
    thus ?thesis
    proof(rule disjE)
      assume "P,E,hp s'' \<turnstile> e'' : T"
      with sconf have "P,E,s'' \<turnstile> e'' : T \<surd>" by(simp add:wf_config_def)
      from IH[OF this] show ?thesis .
    next
      assume "P,E,hp s'' \<turnstile> e'' : NT"
      with sconf have "P,E,s'' \<turnstile> e'' : NT \<surd>" by(simp add:wf_config_def)
      from IH[OF this] have "P,E,hp s' \<turnstile> e' : NT" by simp
      with Class show ?thesis by simp
    qed
  qed
qed



corollary Progress: assumes wf: "wf_C_prog P"
shows "\<lbrakk> P,E,s  \<turnstile> e : T \<surd>; \<D> e \<lfloor>dom(lcl s)\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s'. P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"

using progress[OF wf_prog_wwf_prog[OF wf]]
by(auto simp:wf_config_def sconf_def)


corollary TypeSafety:
fixes s s' :: state
assumes wf:"wf_C_prog P" and sconf:"P,E \<turnstile> s \<surd>" and wte:"P,E \<turnstile> e :: T"
  and D:"\<D> e \<lfloor>dom(lcl s)\<rfloor>" and step:"P,E \<turnstile> \<langle>e,s\<rangle> \<rightarrow>* \<langle>e',s'\<rangle>"
  and nored:"\<not>(\<exists>e'' s''. P,E \<turnstile> \<langle>e',s'\<rangle> \<rightarrow> \<langle>e'',s''\<rangle>)"
shows "(\<exists>v. e' = Val v \<and> P,hp s' \<turnstile> v :\<le> T) \<or>
      (\<exists>r. e' = Throw r \<and> the_addr (Ref r) \<in> dom(hp s'))"
proof -
  from sconf wte wf have wf_config:"P,E,s \<turnstile> e : T \<surd>"
    by(fastforce intro:WT_implies_WTrt simp:wf_config_def)
  with wf step have type_conf:"P,E,(hp s') \<turnstile> e' :\<^bsub>NT\<^esub> T"
    by(rule Subject_reductions)
  from step_preserves_sconf[OF wf step wte[THEN WT_implies_WTrt] sconf] wf
  have sconf':"P,E \<turnstile> s' \<surd>" by simp
  from wf step D have D':"\<D> e' \<lfloor>dom(lcl s')\<rfloor>" by(rule step_preserves_defass)
  show ?thesis
  proof(cases T)
    case Void 
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T" by simp
    with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
    { assume "\<not> final e'"
      from Progress[OF wf wf_config' D' this] nored have False
        by simp }
    hence "final e'" by fast
    with wte' show ?thesis by(auto simp:final_def)
  next
    case Boolean
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T" by simp
    with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
    { assume "\<not> final e'"
      from Progress[OF wf wf_config' D' this] nored have False
        by simp }
    hence "final e'" by fast
    with wte' show ?thesis by(auto simp:final_def)
  next
    case Integer
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T" by simp
    with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
    { assume "\<not> final e'"
      from Progress[OF wf wf_config' D' this] nored have False
        by simp }
    hence "final e'" by fast
    with wte' show ?thesis by(auto simp:final_def)
  next
    case NT
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T" by simp
    with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
    { assume "\<not> final e'"
      from Progress[OF wf wf_config' D' this] nored have False
        by simp }
    hence "final e'" by fast
    with wte' show ?thesis by(auto simp:final_def)
  next
    case (Class C)
    with type_conf have wte':"P,E,hp s' \<turnstile> e' : T \<or> P,E,hp s' \<turnstile> e' : NT" by simp
    thus ?thesis
    proof(rule disjE)
      assume wte':"P,E,hp s' \<turnstile> e' : T"
      with sconf' have wf_config':"P,E,s' \<turnstile> e' : T \<surd>" by(simp add:wf_config_def)
      { assume "\<not> final e'"
        from Progress[OF wf wf_config' D' this] nored have False
          by simp }
      hence "final e'" by fast
      with wte' show ?thesis by(auto simp:final_def)
    next
      assume wte':"P,E,hp s' \<turnstile> e' : NT"
      with sconf' have wf_config':"P,E,s' \<turnstile> e' : NT \<surd>" by(simp add:wf_config_def)
      { assume "\<not> final e'"
        from Progress[OF wf wf_config' D' this] nored have False
          by simp }
      hence "final e'" by fast
      with wte' Class show ?thesis by(auto simp:final_def)
    qed
  qed
qed



end
