(*  Title:       CoreC++

    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory J/Progress.thy by Tobias Nipkow 
*)

section \<open>Progress of Small Step Semantics\<close>

theory Progress imports Equivalence DefAss Conform begin


subsection \<open>Some pre-definitions\<close>

lemma final_refE:
  "\<lbrakk> P,E,h \<turnstile> e : Class C; final e;
    \<And>r. e = ref r \<Longrightarrow> Q;
    \<And>r. e = Throw r \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (simp add:final_def,auto,case_tac v,auto)


lemma finalRefE:
  "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; final e;
  e = null \<Longrightarrow> Q;
  \<And>r. e = ref r \<Longrightarrow> Q;
  \<And>r. e = Throw r \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"

apply (cases T)
apply (simp add:is_refT_def)+
 apply (simp add:final_def)
 apply (erule disjE)
  apply clarsimp
 apply (erule exE)+
apply fastforce
apply (auto simp:final_def is_refT_def)
apply (case_tac v)
apply auto
done


lemma subE:
  "\<lbrakk> P \<turnstile> T \<le> T'; is_type P T'; wf_prog wf_md P;
     \<lbrakk> T = T'; \<forall>C. T \<noteq> Class C \<rbrakk> \<Longrightarrow> Q;
     \<And>C D. \<lbrakk> T = Class C; T' = Class D; P \<turnstile> Path C to D unique \<rbrakk> \<Longrightarrow> Q;
     \<And>C. \<lbrakk> T = NT; T' = Class C \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"

apply(cases T')
apply auto
apply(drule_tac T = "T" in widen_Class)
apply auto
done


lemma assumes wf:"wf_prog wf_md P"
  and typeof:" P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T'"
  and type:"is_type P T"
shows sub_casts:"P \<turnstile> T' \<le> T \<Longrightarrow> \<exists>v'. P \<turnstile> T casts v to v'"

proof(erule subE)
  from type show "is_type P T" .
next
  from wf show "wf_prog wf_md P" .
next
  assume "T' = T" and "\<forall>C. T' \<noteq> Class C"
  thus "\<exists>v'. P \<turnstile> T casts v to v'" by(fastforce intro:casts_prim)
next
  fix C D
  assume T':"T' = Class C" and T:"T = Class D"
    and path_unique:"P \<turnstile> Path C to D unique"
  from T' typeof obtain a Cs where v:"v = Ref(a,Cs)" and last:"last Cs = C"
    by(auto dest!:typeof_Class_Subo)
  from last path_unique obtain Cs' where "P \<turnstile> Path last Cs to D via Cs'"
    by(auto simp:path_unique_def path_via_def)
  hence "P \<turnstile> Class D casts Ref(a,Cs) to Ref(a,Cs@\<^sub>pCs')"
    by -(rule casts_ref,simp_all)
  with T v show "\<exists>v'. P \<turnstile> T casts v to v'" by auto
next
  fix C
  assume "T' = NT" and T:"T = Class C"
  with typeof have "v = Null" by simp
  with T show "\<exists>v'. P \<turnstile> T casts v to v'" by(fastforce intro:casts_null)
qed



text\<open>Derivation of new induction scheme for well typing:\<close>

inductive
  WTrt' :: "[prog,env,heap,expr,     ty     ] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ :' _"   [51,51,51]50)
  and WTrts':: "[prog,env,heap,expr list,ty list] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ [:''] _" [51,51,51]50)
  for P :: prog
where
  "is_class P C \<Longrightarrow>  P,E,h \<turnstile> new C :' Class C"
| "\<lbrakk>is_class P C; P,E,h \<turnstile> e :' T; is_refT T\<rbrakk> 
   \<Longrightarrow> P,E,h \<turnstile> Cast C e :' Class C"
| "\<lbrakk>is_class P C; P,E,h \<turnstile> e :' T; is_refT T\<rbrakk> 
   \<Longrightarrow> P,E,h \<turnstile> \<lparr>C\<rparr>e :' Class C"
| "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> P,E,h \<turnstile> Val v :' T"
| "E V = Some T  \<Longrightarrow>  P,E,h \<turnstile> Var V :' T"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 :' T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2 :' T\<^sub>2;
    case bop of Eq \<Rightarrow> T = Boolean
    | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer \<rbrakk>
   \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :' T"
| "\<lbrakk> P,E,h \<turnstile> Var V :' T; P,E,h \<turnstile> e :' T' \<^cancel>\<open>V \<noteq> This\<close>; P \<turnstile> T' \<le> T \<rbrakk>
   \<Longrightarrow> P,E,h \<turnstile> V:=e :' T"
| "\<lbrakk>P,E,h \<turnstile> e :' Class C; Cs \<noteq> []; P \<turnstile> C has least F:T via Cs\<rbrakk> 
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>F{Cs} :' T"
| "P,E,h \<turnstile> e :' NT \<Longrightarrow> P,E,h \<turnstile> e\<bullet>F{Cs} :' T"
| "\<lbrakk>P,E,h \<turnstile> e\<^sub>1 :' Class C; Cs \<noteq> []; P \<turnstile> C has least F:T via Cs;
    P,E,h \<turnstile> e\<^sub>2 :' T'; P \<turnstile> T' \<le> T \<rbrakk> 
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2 :' T"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1:'NT; P,E,h \<turnstile> e\<^sub>2 :' T'; P \<turnstile> T' \<le> T \<rbrakk> 
   \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2 :' T"
| "\<lbrakk> P,E,h \<turnstile> e :' Class C;  P \<turnstile> C has least M = (Ts,T,m) via Cs;
    P,E,h \<turnstile> es [:'] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
    \<Longrightarrow> P,E,h \<turnstile> e\<bullet>M(es) :' T" 
| "\<lbrakk> P,E,h \<turnstile> e :' Class C'; P \<turnstile> Path C' to C unique;
    P \<turnstile> C has least M = (Ts,T,m) via Cs; 
    P,E,h \<turnstile> es [:'] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
    \<Longrightarrow> P,E,h \<turnstile> e\<bullet>(C::)M(es) :' T"
| "\<lbrakk>P,E,h \<turnstile> e :' NT; P,E,h \<turnstile> es [:'] Ts\<rbrakk> \<Longrightarrow> P,E,h \<turnstile> Call e Copt M es :' T"
| "\<lbrakk> P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T'; P,E(V\<mapsto>T),h \<turnstile> e\<^sub>2 :' T\<^sub>2; P \<turnstile> T' \<le> T; is_type P T \<rbrakk>
   \<Longrightarrow>  P,E,h \<turnstile> {V:T := Val v; e\<^sub>2} :' T\<^sub>2"
| "\<lbrakk> P,E(V\<mapsto>T),h \<turnstile> e :' T'; \<not> assigned V e; is_type P T \<rbrakk>
   \<Longrightarrow>  P,E,h \<turnstile> {V:T; e} :' T'"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 :' T\<^sub>1; P,E,h \<turnstile> e\<^sub>2 :' T\<^sub>2 \<rbrakk>  \<Longrightarrow>  P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 :' T\<^sub>2"
| "\<lbrakk> P,E,h \<turnstile> e :' Boolean;  P,E,h \<turnstile> e\<^sub>1:' T;  P,E,h \<turnstile> e\<^sub>2:' T \<rbrakk>
   \<Longrightarrow> P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :' T"
| "\<lbrakk> P,E,h \<turnstile> e :' Boolean;  P,E,h \<turnstile> c:' T \<rbrakk>
   \<Longrightarrow>  P,E,h \<turnstile> while(e) c :' Void"
| "\<lbrakk> P,E,h \<turnstile> e :' T'; is_refT T'\<rbrakk>  \<Longrightarrow>  P,E,h \<turnstile> throw e :' T"

| "P,E,h \<turnstile> [] [:'] []"
| "\<lbrakk> P,E,h \<turnstile> e :' T;  P,E,h \<turnstile> es [:'] Ts \<rbrakk> \<Longrightarrow>  P,E,h \<turnstile> e#es [:'] T#Ts"



lemmas WTrt'_induct = WTrt'_WTrts'.induct [split_format (complete)]
  and WTrt'_inducts = WTrt'_WTrts'.inducts [split_format (complete)]

inductive_cases WTrt'_elim_cases[elim!]:
  "P,E,h \<turnstile> V :=e :' T"


text\<open>... and some easy consequences:\<close>

lemma [iff]: "P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 :' T\<^sub>2 = (\<exists>T\<^sub>1. P,E,h \<turnstile> e\<^sub>1:' T\<^sub>1 \<and> P,E,h \<turnstile> e\<^sub>2:' T\<^sub>2)"

apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done


lemma [iff]: "P,E,h \<turnstile> Val v :' T = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T)"

apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done


lemma [iff]: "P,E,h \<turnstile> Var V :' T = (E V = Some T)"

apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done



lemma wt_wt': "P,E,h \<turnstile> e : T \<Longrightarrow> P,E,h \<turnstile> e :' T"
and wts_wts': "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> P,E,h \<turnstile> es [:'] Ts"

proof (induct rule:WTrt_inducts)
  case (WTrtBlock E V T h e T')
  thus ?case
    apply(case_tac "assigned V e")
    apply(auto intro:WTrt'_WTrts'.intros 
          simp add:fun_upd_same assigned_def simp del:fun_upd_apply)
    done
qed(auto intro:WTrt'_WTrts'.intros simp del:fun_upd_apply)


lemma wt'_wt: "P,E,h \<turnstile> e :' T \<Longrightarrow> P,E,h \<turnstile> e : T"
and wts'_wts: "P,E,h \<turnstile> es [:'] Ts \<Longrightarrow> P,E,h \<turnstile> es [:] Ts"

apply (induct rule:WTrt'_inducts)
apply (fastforce intro: WTrt_WTrts.intros)+
done



corollary wt'_iff_wt: "(P,E,h \<turnstile> e :' T) = (P,E,h \<turnstile> e : T)"
by(blast intro:wt_wt' wt'_wt)


corollary wts'_iff_wts: "(P,E,h \<turnstile> es [:'] Ts) = (P,E,h \<turnstile> es [:] Ts)"
by(blast intro:wts_wts' wts'_wts)

lemmas WTrt_inducts2 = WTrt'_inducts [unfolded wt'_iff_wt wts'_iff_wts,
  case_names WTrtNew WTrtDynCast WTrtStaticCast WTrtVal WTrtVar WTrtBinOp 
  WTrtLAss WTrtFAcc WTrtFAccNT WTrtFAss WTrtFAssNT WTrtCall WTrtStaticCall WTrtCallNT 
  WTrtInitBlock WTrtBlock WTrtSeq WTrtCond WTrtWhile WTrtThrow 
  WTrtNil WTrtCons, consumes 1]


subsection\<open>The theorem \<open>progress\<close>\<close>


lemma mdc_leq_dyn_type:
"P,E,h \<turnstile> e : T \<Longrightarrow> 
  \<forall>C a Cs D S. T = Class C \<and> e = ref(a,Cs) \<and> h a = Some(D,S) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C"
and "P,E,h \<turnstile> es [:] Ts \<Longrightarrow>
  \<forall>T Ts' e es' C a Cs D S. Ts = T#Ts' \<and> es = e#es' \<and> 
                           T = Class C \<and> e = ref(a,Cs) \<and> h a = Some(D,S)
      \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C"

proof (induct rule:WTrt_inducts2)
  case (WTrtVal h v T E)
  have type:"P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T" by fact
  { fix C a Cs D S
    assume "T = Class C" and "Val v = ref(a,Cs)" and "h a = Some(D,S)"
    with type have "Subobjs P D Cs" and "C = last Cs" by (auto split:if_split_asm)
    hence "P \<turnstile> D \<preceq>\<^sup>* C" by simp (rule Subobjs_subclass) }
  thus ?case by blast
qed auto



lemma appendPath_append_last:
  assumes notempty:"Ds \<noteq> []" 
  shows"(Cs @\<^sub>p Ds) @\<^sub>p [last Ds] = (Cs @\<^sub>p Ds)"

proof -
  have "last Cs = hd Ds \<Longrightarrow> last (Cs @ tl Ds) = last Ds"
  proof(cases "tl Ds = []")
    case True
    assume last:"last Cs = hd Ds"
    with True notempty have "Ds = [last Cs]" by (fastforce dest:hd_Cons_tl)
    hence "last Ds = last Cs" by simp
    with True show ?thesis by simp
  next
    case False
    assume last:"last Cs = hd Ds"
    from notempty False have "last (tl Ds) = last Ds"
      by -(drule hd_Cons_tl,drule_tac x="hd Ds" in last_ConsR,simp)
    with False show ?thesis by simp
  qed
  thus ?thesis by(simp add:appendPath_def)
qed




theorem assumes wf: "wwf_prog P"
shows progress: "P,E,h \<turnstile> e : T \<Longrightarrow>
 (\<And>l. \<lbrakk> P \<turnstile> h \<surd>; P \<turnstile> E \<surd>; \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s'. P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>)"
and "P,E,h \<turnstile> es [:] Ts \<Longrightarrow>
 (\<And>l. \<lbrakk> P \<turnstile> h \<surd>; P \<turnstile> E \<surd>; \<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es \<rbrakk> \<Longrightarrow> \<exists>es' s'. P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>)"
proof (induct rule:WTrt_inducts2)
  case (WTrtNew C E h)
  show ?case
  proof cases
    assume "\<exists>a. h a = None"
    with WTrtNew show ?thesis
      by (fastforce del:exE intro!:RedNew simp:new_Addr_def)
  next
    assume "\<not>(\<exists>a. h a = None)"
    with WTrtNew show ?thesis
      by(fastforce intro:RedNewFail simp add:new_Addr_def)
  qed
next
  case (WTrtDynCast C E h e T)
  have wte: "P,E,h \<turnstile> e : T" and refT: "is_refT T" and "class": "is_class P C"
    and IH: "\<And>l. \<lbrakk>P \<turnstile> h \<surd>; P \<turnstile> E \<surd>; \<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s'. P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
    and D: "\<D> (Cast C e) \<lfloor>dom l\<rfloor>" 
    and hconf: "P \<turnstile> h \<surd>" and envconf:"P \<turnstile> E \<surd>" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof cases
    assume "final e"
    with wte refT show ?thesis
    proof (rule finalRefE)
      assume "e = null" thus ?case by(fastforce intro:RedDynCastNull)
    next
      fix r assume "e = ref r"
      then obtain a Cs where ref:"e = ref(a,Cs)" by (cases r) auto
      with wte obtain D S where h:"h a = Some(D,S)" by auto
      show ?thesis
      proof (cases "P \<turnstile> Path D to C unique")
        case True
        then obtain Cs' where path:"P \<turnstile> Path D to C via Cs'"
          by (fastforce simp:path_via_def path_unique_def)
        then obtain Ds where "Ds = appendPath Cs Cs'" by simp
        with h path True ref show ?thesis by (fastforce intro:RedDynCast)
      next
        case False
        hence path_not_unique:"\<not> P \<turnstile> Path D to C unique" .
        show ?thesis
        proof(cases "P \<turnstile> Path last Cs to C unique")
          case True
          then obtain Cs' where "P \<turnstile> Path last Cs to C via Cs'"
            by(auto simp:path_via_def path_unique_def)
          with True ref show ?thesis by(fastforce intro:RedStaticUpDynCast)
        next
          case False
          hence path_not_unique':"\<not> P \<turnstile> Path last Cs to C unique" .
          thus ?thesis
          proof(cases "C \<notin> set Cs")
            case False
            then obtain Ds Ds' where "Cs = Ds@[C]@Ds'"
              by (auto simp:in_set_conv_decomp)
            with ref show ?thesis by(fastforce intro:RedStaticDownDynCast)
          next
            case True
            with path_not_unique path_not_unique' h ref 
            show ?thesis by (fastforce intro:RedDynCastFail)
          qed
        qed
      qed
    next
      fix r assume "e = Throw r"
      thus ?thesis by(blast intro!:red_reds.DynCastThrow)
    qed
  next
    assume nf: "\<not> final e"
    from IH[OF hconf envconf De nf] show ?thesis by (blast intro:DynCastRed)
  qed
next
  case (WTrtStaticCast C E h e T)
  have wte: "P,E,h \<turnstile> e : T" and refT: "is_refT T" and "class": "is_class P C"
   and IH: "\<And>l. \<lbrakk>P \<turnstile> h \<surd>; P \<turnstile> E \<surd>; \<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s'. P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (\<lparr>C\<rparr>e) \<lfloor>dom l\<rfloor>" 
    and hconf: "P \<turnstile> h \<surd>" and envconf:"P \<turnstile> E \<surd>" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof cases
    assume "final e"
    with wte refT show ?thesis
    proof (rule finalRefE)
      assume "e = null" with "class" show ?case by(fastforce intro:RedStaticCastNull)
    next
      fix r assume "e = ref r"
      then obtain a Cs where ref:"e = ref(a,Cs)" by (cases r) auto
      with wte wf have "class":"is_class P (last Cs)" 
        by (auto intro:Subobj_last_isClass split:if_split_asm)
      show ?thesis
      proof(cases "P \<turnstile> (last Cs) \<preceq>\<^sup>* C")
        case True
        with "class" wf obtain Cs'  where "P \<turnstile> Path last Cs to C via Cs'"
          by(fastforce dest:leq_implies_path)
        with True ref show ?thesis by(fastforce intro:RedStaticUpCast)
      next
        case False
        have notleq:"\<not> P \<turnstile> last Cs \<preceq>\<^sup>* C" by fact
        thus ?thesis
        proof(cases "C \<notin> set Cs")
          case False
          then obtain Ds Ds' where "Cs = Ds@[C]@Ds'"
            by (auto simp:in_set_conv_decomp)
          with ref show ?thesis
            by(fastforce intro:RedStaticDownCast)
        next
          case True
          with ref notleq show ?thesis by (fastforce intro:RedStaticCastFail)
        qed
      qed
    next
      fix r assume "e = Throw r"
      thus ?thesis by(blast intro!:red_reds.StaticCastThrow)
    qed
  next
    assume nf: "\<not> final e"
    from IH[OF hconf envconf De nf] show ?thesis by (blast intro:StaticCastRed)
  qed
next
  case WTrtVal thus ?case by(simp add:final_def)
next
  case WTrtVar thus ?case by(fastforce intro:RedVar simp:hyper_isin_def)
next
  case (WTrtBinOp E h e1 T1 e2 T2 bop T')
  have bop:"case bop of Eq \<Rightarrow> T' = Boolean
                      | Add \<Rightarrow> T1 = Integer \<and> T2 = Integer \<and> T' = Integer"
    and wte1:"P,E,h \<turnstile> e1 : T1" and wte2:"P,E,h \<turnstile> e2 : T2" by fact+
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v1 assume e1 [simp]:"e1 = Val v1"
      show ?thesis
      proof cases
        assume "final e2"
        thus ?thesis
        proof (rule finalE)
          fix v2 assume e2 [simp]:"e2 = Val v2"
          show ?thesis
          proof (cases bop)
            assume "bop = Eq"
            thus ?thesis using WTrtBinOp by(fastforce intro:RedBinOp)
          next
            assume Add:"bop = Add"
            with e1 e2 wte1 wte2 bop obtain i1 i2 
              where "v1 = Intg i1" and "v2 = Intg i2"
              by (auto dest!:typeof_Integer)
            with Add obtain v where "binop(bop,v1,v2) = Some v" by simp
            with e1 e2 show ?thesis by (fastforce intro:RedBinOp)
          qed
        next
          fix a assume "e2 = Throw a"
          thus ?thesis by(auto intro:red_reds.BinOpThrow2)
        qed
      next
        assume "\<not> final e2" with WTrtBinOp show ?thesis
          by simp (fast intro!:BinOpRed2)
      qed
    next
      fix r assume "e1 = Throw r"
      thus ?thesis by simp (fast intro:red_reds.BinOpThrow1)
    qed
  next
    assume "\<not> final e1" with WTrtBinOp show ?thesis
      by simp (fast intro:BinOpRed1)
  qed
next
  case (WTrtLAss E h V T e T')
  have wte:"P,E,h \<turnstile> e : T'"
    and wtvar:"P,E,h \<turnstile> Var V : T"
    and sub:"P \<turnstile> T' \<le> T"
    and envconf:"P \<turnstile> E \<surd>" by fact+
  from envconf wtvar have type:"is_type P T" by(auto simp:envconf_def)
  show ?case
  proof cases
    assume fin:"final e"
    from fin show ?case
    proof (rule finalE)
      fix v assume e:"e = Val v"
      from sub type wf show ?case
      proof(rule subE)
        assume eq:"T' = T" and "\<forall>C. T' \<noteq> Class C"
        hence "P \<turnstile> T casts v to v"
          by simp(rule casts_prim)
        with wte wtvar eq e show ?thesis
          by(auto intro!:RedLAss)
      next
        fix C D
        assume T':"T' = Class C" and T:"T = Class D"
          and path_unique:"P \<turnstile> Path C to D unique"
        from wte e T' obtain a Cs where ref:"e = ref(a,Cs)"
          and last:"last Cs = C" 
          by (auto dest!:typeof_Class_Subo)
        from path_unique obtain Cs' where path_via:"P \<turnstile> Path C to D via Cs'"
          by(auto simp:path_unique_def path_via_def)
        with last have "P \<turnstile> Class D casts Ref(a,Cs) to Ref(a,Cs@\<^sub>pCs')"
          by (fastforce intro:casts_ref simp:path_via_def)
        with wte wtvar T ref show ?thesis
          by(auto intro!:RedLAss)
      next
        fix C
        assume T':"T' = NT" and T:"T = Class C"
        with wte e have null:"e = null" by auto
        have "P \<turnstile> Class C casts Null to Null"
          by -(rule casts_null)
        with wte wtvar T null show ?thesis
          by(auto intro!:RedLAss)
      qed
    next
      fix r assume "e = Throw r"
      thus ?thesis by(fastforce intro:red_reds.LAssThrow)
    qed
  next
    assume "\<not> final e" with WTrtLAss show ?thesis
      by simp (fast intro:LAssRed)
  qed
next
  case (WTrtFAcc E h e C Cs F T)
  have wte: "P,E,h \<turnstile> e : Class C" 
    and field: "P \<turnstile> C has least F:T via Cs"
    and notemptyCs:"Cs \<noteq> []"
    and hconf: "P \<turnstile> h \<surd>" by fact+
  show ?case
  proof cases
    assume "final e"
    with wte show ?thesis
    proof (rule final_refE)
      fix r assume e: "e = ref r"
      then obtain a Cs' where ref:"e = ref(a,Cs')" by (cases r) auto
      with wte obtain D S where h:"h a = Some(D,S)" and suboD:"Subobjs P D Cs'"
        and last:"last Cs' = C"
        by (fastforce split:if_split_asm)
      from field obtain Bs fs ms
        where "class": "class P (last Cs) = Some(Bs,fs,ms)"
        and fs:"map_of fs F = Some T"
        by (fastforce simp:LeastFieldDecl_def FieldDecls_def)
      obtain Ds where Ds:"Ds = Cs'@\<^sub>pCs" by simp
      with notemptyCs "class" have class':"class P (last Ds) = Some(Bs,fs,ms)"
        by (drule_tac Cs'="Cs'" in appendPath_last) simp
      from field suboD last Ds wf have subo:"Subobjs P D Ds"
        by(fastforce intro:Subobjs_appendPath simp:LeastFieldDecl_def FieldDecls_def)
      with hconf h have "P,h \<turnstile> (D,S) \<surd>" by (auto simp:hconf_def)
      with class' subo obtain fs' where S:"(Ds,fs') \<in> S"
        and "P,h \<turnstile> fs' (:\<le>) map_of fs"
        apply (auto simp:oconf_def)
        apply (erule_tac x="Ds" in allE)
        apply auto
        apply (erule_tac x="Ds" in allE)
        apply (erule_tac x="fs'" in allE)
        apply auto
        done
      with fs obtain v where "fs' F = Some v"
        by (fastforce simp:fconf_def)
      with h last Ds S
      have "P,E \<turnstile> \<langle>(ref (a,Cs'))\<bullet>F{Cs}, (h,l)\<rangle> \<rightarrow> \<langle>Val v,(h,l)\<rangle>"
        by (fastforce intro:RedFAcc)
      with ref show ?thesis by blast
    next
      fix r assume "e = Throw r"
      thus ?thesis by(fastforce intro:red_reds.FAccThrow)
    qed
  next
    assume "\<not> final e" with WTrtFAcc show ?thesis
      by(fastforce intro!:FAccRed)
  qed
next
  case (WTrtFAccNT E h e F Cs T)
  show ?case
  proof cases
    assume "final e"  \<comment> \<open>@{term e} is @{term null} or @{term throw}\<close>
    with WTrtFAccNT show ?thesis
      by(fastforce simp:final_def intro: RedFAccNull red_reds.FAccThrow 
                  dest!:typeof_NT)
  next
    assume "\<not> final e" \<comment> \<open>@{term e} reduces by IH\<close>
    with WTrtFAccNT show ?thesis by simp (fast intro:FAccRed)
  qed
next
  case (WTrtFAss E h e\<^sub>1 C Cs F T e\<^sub>2 T')
  have wte1:"P,E,h \<turnstile> e\<^sub>1 : Class C"
    and wte2:"P,E,h \<turnstile> e\<^sub>2 : T'"
    and field:"P \<turnstile> C has least F:T via Cs" 
    and notemptyCs:"Cs \<noteq> []"
    and sub:"P \<turnstile> T' \<le> T"
    and hconf:"P \<turnstile> h \<surd>" by fact+
  from field wf have type:"is_type P T" by(rule least_field_is_type)
  show ?case
  proof cases
    assume "final e\<^sub>1"
    with wte1 show ?thesis
    proof (rule final_refE)
      fix r assume e1: "e\<^sub>1 = ref r"
      show ?thesis
      proof cases
        assume "final e\<^sub>2"
        thus ?thesis
        proof (rule finalE)
          fix v assume e2:"e\<^sub>2 = Val v"
          from e1 obtain a Cs' where ref:"e\<^sub>1 = ref(a,Cs')" by (cases r) auto
          with wte1 obtain D S where h:"h a = Some(D,S)" 
            and suboD:"Subobjs P D Cs'" and last:"last Cs' = C"
            by (fastforce split:if_split_asm)
          from field obtain Bs fs ms
            where "class": "class P (last Cs) = Some(Bs,fs,ms)"
            and fs:"map_of fs F = Some T"
            by (fastforce simp:LeastFieldDecl_def FieldDecls_def)
          obtain Ds where Ds:"Ds = Cs'@\<^sub>pCs" by simp
          with notemptyCs "class" have class':"class P (last Ds) = Some(Bs,fs,ms)"
            by (drule_tac Cs'="Cs'" in appendPath_last) simp
          from field suboD last Ds wf have subo:"Subobjs P D Ds"
            by(fastforce intro:Subobjs_appendPath 
              simp:LeastFieldDecl_def FieldDecls_def)
          with hconf h have "P,h \<turnstile> (D,S) \<surd>" by (auto simp:hconf_def)
          with class' subo obtain fs' where S:"(Ds,fs') \<in> S"
            by (auto simp:oconf_def)
          from sub type wf show ?thesis
          proof(rule subE)
            assume eq:"T' = T" and "\<forall>C. T' \<noteq> Class C"
            hence "P \<turnstile> T casts v to v"
              by simp(rule casts_prim)
            with h last field Ds notemptyCs S eq
            have "P,E \<turnstile> \<langle>(ref (a,Cs'))\<bullet>F{Cs}:=(Val v), (h,l)\<rangle> \<rightarrow> 
              \<langle>Val v, (h(a \<mapsto> (D,insert (Ds,fs'(F\<mapsto>v)) (S -  {(Ds,fs')}))),l)\<rangle>"
              by (fastforce intro:RedFAss)
            with ref e2 show ?thesis by blast
          next
            fix C' D'
            assume T':"T' = Class C'" and T:"T = Class D'"
            and path_unique:"P \<turnstile> Path C' to D' unique"
            from wte2 e2 T' obtain a' Cs'' where ref2:"e\<^sub>2 = ref(a',Cs'')"
              and last':"last Cs'' = C'"
              by (auto dest!:typeof_Class_Subo)
            from path_unique obtain Ds' where "P \<turnstile> Path C' to D' via Ds'"
              by(auto simp:path_via_def path_unique_def)
            with last' 
            have casts:"P \<turnstile> Class D' casts Ref(a',Cs'') to Ref(a',Cs''@\<^sub>pDs')"
              by (fastforce intro:casts_ref simp:path_via_def)
            obtain v' where "v' = Ref(a',Cs''@\<^sub>pDs')" by simp
            with h last field Ds notemptyCs S ref e2 ref2 T casts
            have "P,E \<turnstile> \<langle>(ref (a,Cs'))\<bullet>F{Cs}:=(Val v), (h,l)\<rangle> \<rightarrow> 
                        \<langle>Val v',(h(a \<mapsto> (D,insert (Ds,fs'(F\<mapsto>v'))(S-{(Ds,fs')}))),l)\<rangle>"
              by (fastforce intro:RedFAss)
            with ref e2 show ?thesis by blast
          next
            fix C'
            assume T':"T' = NT" and T:"T = Class C'"
            from e2 wte2 T' have null:"e\<^sub>2 = null" by auto
            have casts:"P \<turnstile> Class C' casts Null to Null"
              by -(rule casts_null)
            obtain v' where "v' = Null" by simp
            with h last field Ds notemptyCs S ref e2 null T casts
            have "P,E \<turnstile> \<langle>(ref (a,Cs'))\<bullet>F{Cs}:=(Val v), (h,l)\<rangle> \<rightarrow> 
                  \<langle>Val v', (h(a \<mapsto> (D,insert (Ds,fs'(F\<mapsto>v')) (S -  {(Ds,fs')}))),l)\<rangle>"
              by (fastforce intro:RedFAss)
            with ref e2 show ?thesis by blast
          qed
        next
          fix r assume "e\<^sub>2 = Throw r"
          thus ?thesis using e1 by(fastforce intro:red_reds.FAssThrow2)
        qed
      next
        assume "\<not> final e\<^sub>2" with WTrtFAss e1 show ?thesis
          by simp (fast intro!:FAssRed2)
      qed
    next
      fix r assume "e\<^sub>1 = Throw r"
      thus ?thesis by(fastforce intro:red_reds.FAssThrow1)
    qed
  next
    assume "\<not> final e\<^sub>1" with WTrtFAss show ?thesis
      by simp (blast intro!:FAssRed1)
  qed
next
  case (WTrtFAssNT E h e\<^sub>1 e\<^sub>2 T' T F Cs)
  show ?case
  proof cases
    assume e1: "final e\<^sub>1"  \<comment> \<open>@{term e\<^sub>1} is @{term null} or @{term throw}\<close>
    show ?thesis
    proof cases
      assume "final e\<^sub>2"  \<comment> \<open>@{term e\<^sub>2} is @{term Val} or @{term throw}\<close>
      with WTrtFAssNT e1 show ?thesis
        by(fastforce simp:final_def intro:RedFAssNull red_reds.FAssThrow1 
                                         red_reds.FAssThrow2 dest!:typeof_NT)
    next
      assume  "\<not> final e\<^sub>2" \<comment> \<open>@{term e\<^sub>2} reduces by IH\<close>
      with WTrtFAssNT e1 show ?thesis
        by (fastforce simp:final_def intro!:red_reds.FAssRed2 red_reds.FAssThrow1)
    qed
  next
    assume "\<not> final e\<^sub>1" \<comment> \<open>@{term e\<^sub>1} reduces by IH\<close>
    with WTrtFAssNT show ?thesis by (fastforce intro:FAssRed1)
  qed
next
  case (WTrtCall E h e C M Ts T pns body Cs es Ts')
  have wte: "P,E,h \<turnstile> e : Class C"
    and "method":"P \<turnstile> C has least M = (Ts, T, pns, body) via Cs"
    and wtes: "P,E,h \<turnstile> es [:] Ts'"and sub: "P \<turnstile> Ts' [\<le>] Ts"
    and IHes: "\<And>l. \<lbrakk>P \<turnstile> h \<surd>; P \<turnstile> E \<surd>; \<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s'. P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
    and hconf: "P \<turnstile> h \<surd>" and envconf:"P \<turnstile> E \<surd>" 
    and D: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume final:"final e"
    with wte show ?thesis
    proof (rule final_refE)
      fix r assume ref: "e = ref r"
      show ?thesis
      proof cases
        assume es: "\<exists>vs. es = map Val vs"
        from ref obtain a Cs' where ref:"e = ref(a,Cs')" by (cases r) auto
        with wte obtain D S where h:"h a = Some(D,S)" and suboD:"Subobjs P D Cs'"
          and last:"last Cs' = C"
          by (fastforce split:if_split_asm)
        from wte ref h have subcls:"P \<turnstile> D \<preceq>\<^sup>* C" by -(drule mdc_leq_dyn_type,auto)
        from "method" have has:"P \<turnstile> C has M = (Ts,T,pns,body) via Cs"
            by(rule has_least_method_has_method)
        from es obtain vs where vs:"es = map Val vs" by auto
        obtain Cs'' Ts'' T' pns' body' where 
          ass:"P \<turnstile> (D,Cs'@\<^sub>pCs) selects M = (Ts'',T',pns',body') via Cs'' \<and>
           length Ts'' = length pns' \<and> length vs = length pns' \<and> P \<turnstile> T' \<le> T"
        proof (cases "\<exists>Ts'' T' pns' body' Ds. P \<turnstile> D has least M = (Ts'',T',pns',body') via Ds")
          case True
          then obtain Ts'' T' pns' body' Cs'' 
            where least:"P \<turnstile> D has least M = (Ts'',T',pns',body') via Cs''"
            by auto
          hence select:"P \<turnstile> (D,Cs'@\<^sub>pCs) selects M = (Ts'',T',pns',body') via Cs''"
            by(rule dyn_unique)
          from subcls least wf has have "Ts = Ts''" and leq:"P \<turnstile> T' \<le> T"
            by -(drule leq_method_subtypes,simp_all,blast)+
          hence "length Ts = length Ts''" by (simp add:list_all2_iff)
          with sub have "length Ts' = length Ts''" by (simp add:list_all2_iff)
          with WTrts_same_length[OF wtes] vs have length:"length vs = length Ts''"
            by simp
          from has_least_wf_mdecl[OF wf least] 
          have lengthParams:"length Ts'' = length pns'" by (simp add:wf_mdecl_def)
          with length have "length vs = length pns'" by simp
          with select lengthParams leq show ?thesis using that by blast
        next
          case False
          hence non_dyn:"\<forall>Ts'' T' pns' body' Ds. 
              \<not> P \<turnstile> D has least M = (Ts'',T',pns',body') via Ds" by auto
          from suboD last have path:"P \<turnstile> Path D to C via Cs'" 
            by(simp add:path_via_def)
          from "method" have notempty:"Cs \<noteq> []" 
            by(fastforce intro!:Subobjs_nonempty 
                        simp:LeastMethodDef_def MethodDefs_def)
          from suboD have "class": "is_class P D" by(rule Subobjs_isClass)
          from suboD last have path:"P \<turnstile> Path D to C via Cs'"
            by(simp add:path_via_def)
          with "method" wf have "P \<turnstile> D has M = (Ts,T,pns,body) via Cs'@\<^sub>pCs"
            by(auto intro:has_path_has has_least_method_has_method)
          with "class" wf obtain Cs'' Ts'' T' pns' body' where overrider:
            "P \<turnstile> (D,Cs'@\<^sub>pCs) has overrider M = (Ts'',T',pns',body') via Cs''"
            by(auto dest!:class_wf simp:is_class_def wf_cdecl_def,blast)
          with non_dyn
          have select:"P \<turnstile> (D,Cs'@\<^sub>pCs) selects M = (Ts'',T',pns',body') via Cs''"
            by-(rule dyn_ambiguous,simp_all)
          from notempty have eq:"(Cs' @\<^sub>p Cs) @\<^sub>p [last Cs] = (Cs' @\<^sub>p Cs)"
            by(rule appendPath_append_last)
          from "method" wf
          have "P \<turnstile> last Cs has least M = (Ts,T,pns,body) via [last Cs]"
            by(auto dest:Subobj_last_isClass intro:Subobjs_Base subobjs_rel
                    simp:LeastMethodDef_def MethodDefs_def)
          with notempty
          have "P \<turnstile> last(Cs'@\<^sub>pCs) has least M = (Ts,T,pns,body) via [last Cs]"
            by -(drule_tac Cs'="Cs'" in appendPath_last,simp)
          with overrider wf eq
          have "(Cs'',(Ts'',T',pns',body')) \<in> MinimalMethodDefs P D M"
            and "P,D \<turnstile> Cs'' \<sqsubseteq> Cs'@\<^sub>pCs"
            by(auto simp:FinalOverriderMethodDef_def OverriderMethodDefs_def)
              (drule wf_sees_method_fun,auto)
          with subcls wf notempty has path have "Ts = Ts''" and leq:"P \<turnstile> T' \<le> T"
            by -(drule leq_methods_subtypes,simp_all,blast)+
          hence "length Ts = length Ts''" by (simp add:list_all2_iff)
          with sub have "length Ts' = length Ts''" by (simp add:list_all2_iff)
          with WTrts_same_length[OF wtes] vs have length:"length vs = length Ts''"
            by simp
          from select_method_wf_mdecl[OF wf select]
          have lengthParams:"length Ts'' = length pns'" by (simp add:wf_mdecl_def)
          with length have "length vs = length pns'" by simp
          with select lengthParams leq show ?thesis using that by blast
        qed
        obtain new_body where "case T of Class D \<Rightarrow> 
           new_body = \<lparr>D\<rparr>blocks(this#pns',Class(last Cs'')#Ts'',Ref(a,Cs'')#vs,body')
    | _ \<Rightarrow> new_body = blocks(this#pns',Class(last Cs'')#Ts'',Ref(a,Cs'')#vs,body')"
          by(cases T) auto
        with h "method" last ass ref vs
          show ?thesis by (auto intro!:exI RedCall)
      next
        assume "\<not>(\<exists>vs. es = map Val vs)"
        hence not_all_Val: "\<not>(\<forall>e \<in> set es. \<exists>v. e = Val v)"
          by(simp add:ex_map_conv)
        let ?ves = "takeWhile (\<lambda>e. \<exists>v. e = Val v) es"
        let ?rest = "dropWhile (\<lambda>e. \<exists>v. e = Val v) es"
        let ?ex = "hd ?rest" let ?rst = "tl ?rest"
        from not_all_Val have nonempty: "?rest \<noteq> []" by auto
        hence es: "es = ?ves @ ?ex # ?rst" by simp
        have "\<forall>e \<in> set ?ves. \<exists>v. e = Val v" by(fastforce dest:set_takeWhileD)
        then obtain vs where ves: "?ves = map Val vs"
          using ex_map_conv by blast
        show ?thesis
        proof cases
          assume "final ?ex"
          moreover from nonempty have "\<not>(\<exists>v. ?ex = Val v)"
            by(auto simp:neq_Nil_conv simp del:dropWhile_eq_Nil_conv)
              (simp add:dropWhile_eq_Cons_conv)
          ultimately obtain r' where ex_Throw: "?ex = Throw r'"
            by(fast elim!:finalE)
          show ?thesis using ref es ex_Throw ves
            by(fastforce intro:red_reds.CallThrowParams)
        next
          assume not_fin: "\<not> final ?ex"
          have "finals es = finals(?ves @ ?ex # ?rst)" using es
            by(rule arg_cong)
          also have "\<dots> = finals(?ex # ?rst)" using ves by simp
          finally have "finals es = finals(?ex # ?rst)" .
          hence "\<not> finals es" using not_finals_ConsI[OF not_fin] by blast
          thus ?thesis using ref D IHes[OF hconf envconf]
            by(fastforce intro!:CallParams)
        qed
      qed
    next
      fix r assume "e = Throw r"
      with WTrtCall.prems show ?thesis by(fast intro!:red_reds.CallThrowObj)
    qed
  next
    assume "\<not> final e"
    with WTrtCall show ?thesis by simp (blast intro!:CallObj)
  qed
next
  case (WTrtStaticCall E h e C' C M Ts T pns body Cs es Ts')
  have wte: "P,E,h \<turnstile> e : Class C'"
    and path_unique:"P \<turnstile> Path C' to C unique"
    and "method":"P \<turnstile> C has least M = (Ts, T, pns, body) via Cs"
    and wtes: "P,E,h \<turnstile> es [:] Ts'"and sub: "P \<turnstile> Ts' [\<le>] Ts"
    and IHes: "\<And>l.
              \<lbrakk>P \<turnstile> h \<surd>; envconf P E; \<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk>
              \<Longrightarrow> \<exists>es' s'. P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
    and hconf: "P \<turnstile> h \<surd>" and envconf:"envconf P E"
    and D: "\<D> (e\<bullet>(C::)M(es)) \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume final:"final e"
    with wte show ?thesis
    proof (rule final_refE)
      fix r assume ref: "e = ref r"
      show ?thesis
      proof cases
        assume es: "\<exists>vs. es = map Val vs"
        from ref obtain a Cs' where ref:"e = ref(a,Cs')" by (cases r) auto
        with wte have last:"last Cs' = C'"
          by (fastforce split:if_split_asm)
        with path_unique obtain Cs''
          where path_via:"P \<turnstile> Path (last Cs') to C via Cs''"
          by (auto simp add:path_via_def path_unique_def)
        obtain Ds where Ds:"Ds = (Cs'@\<^sub>pCs'')@\<^sub>pCs" by simp
        from es obtain vs where vs:"es = map Val vs" by auto
        from sub have "length Ts' = length Ts" by (simp add:list_all2_iff)
        with WTrts_same_length[OF wtes] vs have length:"length vs = length Ts"
          by simp
        from has_least_wf_mdecl[OF wf "method"]
        have lengthParams:"length Ts = length pns" by (simp add:wf_mdecl_def)
        with "method" last path_unique path_via Ds length ref vs show ?thesis
          by (auto intro!:exI RedStaticCall)
      next
        assume "\<not>(\<exists>vs. es = map Val vs)"
        hence not_all_Val: "\<not>(\<forall>e \<in> set es. \<exists>v. e = Val v)"
          by(simp add:ex_map_conv)
        let ?ves = "takeWhile (\<lambda>e. \<exists>v. e = Val v) es"
        let ?rest = "dropWhile (\<lambda>e. \<exists>v. e = Val v) es"
        let ?ex = "hd ?rest" let ?rst = "tl ?rest"
        from not_all_Val have nonempty: "?rest \<noteq> []" by auto
        hence es: "es = ?ves @ ?ex # ?rst" by simp
        have "\<forall>e \<in> set ?ves. \<exists>v. e = Val v" by(fastforce dest:set_takeWhileD)
        then obtain vs where ves: "?ves = map Val vs"
          using ex_map_conv by blast
        show ?thesis
        proof cases
          assume "final ?ex"
          moreover from nonempty have "\<not>(\<exists>v. ?ex = Val v)"
            by(auto simp:neq_Nil_conv simp del:dropWhile_eq_Nil_conv)
              (simp add:dropWhile_eq_Cons_conv)
          ultimately obtain r' where ex_Throw: "?ex = Throw r'"
            by(fast elim!:finalE)
          show ?thesis using ref es ex_Throw ves
            by(fastforce intro:red_reds.CallThrowParams)
        next
          assume not_fin: "\<not> final ?ex"
          have "finals es = finals(?ves @ ?ex # ?rst)" using es
            by(rule arg_cong)
          also have "\<dots> = finals(?ex # ?rst)" using ves by simp
          finally have "finals es = finals(?ex # ?rst)" .
          hence "\<not> finals es" using not_finals_ConsI[OF not_fin] by blast
          thus ?thesis using ref D IHes[OF hconf envconf]
            by(fastforce intro!:CallParams)
        qed
      qed
    next
      fix r assume "e = Throw r"
      with WTrtStaticCall.prems show ?thesis by(fast intro!:red_reds.CallThrowObj)
    qed
  next
    assume "\<not> final e"
    with WTrtStaticCall show ?thesis by simp (blast intro!:CallObj)
  qed
next
  case (WTrtCallNT E h e es Ts Copt M T)
  show ?case
  proof cases
    assume "final e"
    moreover
    { fix v assume e: "e = Val v"
      hence "e = null" using WTrtCallNT by simp
      have ?case
      proof cases
        assume "finals es"
        moreover
        { fix vs assume "es = map Val vs"
          with WTrtCallNT e have ?thesis by(fastforce intro: RedCallNull dest!:typeof_NT) }
        moreover
        { fix vs a es' assume "es = map Val vs @ Throw a # es'"
          with WTrtCallNT e have ?thesis by(fastforce intro: CallThrowParams) }
        ultimately show ?thesis by(fastforce simp:finals_def)
      next
        assume "\<not> finals es" \<comment> \<open>@{term es} reduces by IH\<close>
        with WTrtCallNT e show ?thesis by(fastforce intro: CallParams)
      qed
    }
    moreover
    { fix r assume "e = Throw r"
      with WTrtCallNT have ?case by(fastforce intro: CallThrowObj) }
    ultimately show ?thesis by(fastforce simp:final_def)
  next
    assume "\<not> final e" \<comment> \<open>@{term e} reduces by IH\<close>
    with WTrtCallNT show ?thesis by (fastforce intro:CallObj)
  qed
next
  case (WTrtInitBlock h v T' E V T e\<^sub>2 T\<^sub>2)
  have IH2: "\<And>l. \<lbrakk>P \<turnstile> h \<surd>; P \<turnstile> E(V \<mapsto> T) \<surd>; \<D> e\<^sub>2 \<lfloor>dom l\<rfloor>; \<not> final e\<^sub>2\<rbrakk>
                  \<Longrightarrow> \<exists>e' s'. P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>2,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
    and typeof:"P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T'"
    and type:"is_type P T" and sub:"P \<turnstile> T' \<le> T"
    and hconf: "P \<turnstile> h \<surd>" and envconf:"P \<turnstile> E \<surd>"
    and D: "\<D> {V:T := Val v; e\<^sub>2} \<lfloor>dom l\<rfloor>" by fact+
  from wf typeof type sub obtain v' where casts:"P \<turnstile> T casts v to v'"
    by(auto dest:sub_casts)
  show ?case
  proof cases
    assume fin:"final e\<^sub>2"
    with casts show ?thesis
      by(fastforce elim:finalE intro:RedInitBlock red_reds.InitBlockThrow)
  next
    assume not_fin2: "\<not> final e\<^sub>2"
    from D have D2: "\<D> e\<^sub>2 \<lfloor>dom(l(V\<mapsto>v'))\<rfloor>" by (auto simp:hyperset_defs)
    from envconf type have "P \<turnstile> E(V \<mapsto> T) \<surd>" by(auto simp:envconf_def)
    from IH2[OF hconf this D2 not_fin2]
    obtain h' l' e' where red2: "P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>2,(h, l(V\<mapsto>v'))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
      by auto
    from red_lcl_incr[OF red2] have "V \<in> dom l'" by auto
    with red2 casts show ?thesis by(fastforce intro:InitBlockRed)
  qed
next
  case (WTrtBlock E V T h e T')
  have IH: "\<And>l. \<lbrakk>P \<turnstile> h \<surd>; P \<turnstile> E(V \<mapsto> T) \<surd>; \<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                 \<Longrightarrow> \<exists>e' s'. P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
   and unass: "\<not> assigned V e" and type:"is_type P T"
   and hconf: "P \<turnstile> h \<surd>" and envconf:"P \<turnstile> E \<surd>" 
    and D: "\<D> {V:T; e} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume "e = Val v" with type show ?thesis by(fast intro:RedBlock)
    next
      fix r assume "e = Throw r"
      with type show ?thesis by(fast intro:red_reds.BlockThrow)
    qed
  next
    assume not_fin: "\<not> final e"
    from D have De: "\<D> e \<lfloor>dom(l(V:=None))\<rfloor>" by(simp add:hyperset_defs)
    from envconf type have "P \<turnstile> E(V \<mapsto> T) \<surd>" by(auto simp:envconf_def)
    from IH[OF hconf this De not_fin]
    obtain h' l' e' where red: "P,E(V \<mapsto> T) \<turnstile> \<langle>e,(h,l(V:=None))\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
      by auto
    show ?thesis
    proof (cases "l' V")
      assume "l' V = None"
      with red unass show ?thesis by(blast intro: BlockRedNone)
    next
      fix v assume "l' V = Some v"
      with red unass type show ?thesis by(blast intro: BlockRedSome)
    qed
  qed
next
  case (WTrtSeq E h e\<^sub>1 T\<^sub>1 e\<^sub>2 T\<^sub>2)
  show ?case
  proof cases
    assume "final e\<^sub>1"
    thus ?thesis
      by(fast elim:finalE intro:intro:RedSeq red_reds.SeqThrow)
  next
    assume "\<not> final e\<^sub>1" with WTrtSeq show ?thesis
      by simp (blast intro:SeqRed)
  qed
next
  case (WTrtCond E h e e\<^sub>1 T e\<^sub>2)
  have wt: "P,E,h \<turnstile> e : Boolean" by fact
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume val: "e = Val v"
      then obtain b where v: "v = Bool b" using wt by (fastforce dest:typeof_Boolean)
      show ?thesis
      proof (cases b)
        case True with val v show ?thesis by(auto intro:RedCondT)
      next
        case False with val v show ?thesis by(auto intro:RedCondF)
      qed
    next
      fix r assume "e = Throw r"
      thus ?thesis by(fast intro:red_reds.CondThrow)
    qed
  next
    assume "\<not> final e" with WTrtCond show ?thesis
      by simp (fast intro:CondRed)
  qed
next
  case WTrtWhile show ?case by(fast intro:RedWhile)
next
  case (WTrtThrow E h e T' T)
  show ?case
  proof cases
    assume "final e" \<comment> \<open>Then @{term e} must be @{term throw} or @{term null}\<close>
    with WTrtThrow show ?thesis
      by(fastforce simp:final_def is_refT_def
                  intro:red_reds.ThrowThrow red_reds.RedThrowNull
                  dest!:typeof_NT typeof_Class_Subo)
  next
    assume "\<not> final e" \<comment> \<open>Then @{term e} must reduce\<close>
    with WTrtThrow show ?thesis by simp (blast intro:ThrowRed)
  qed
next
  case WTrtNil thus ?case by simp
next
  case (WTrtCons E h e T es Ts)
  have IHe: "\<And>l. \<lbrakk>P \<turnstile> h \<surd>; P \<turnstile> E \<surd>; \<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s'. P,E \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
   and IHes: "\<And>l. \<lbrakk>P \<turnstile> h \<surd>; P \<turnstile> E \<surd>; \<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s'. P,E \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
   and hconf: "P \<turnstile> h \<surd>" and envconf:"P \<turnstile> E \<surd>"
    and D: "\<D>s (e#es) \<lfloor>dom l\<rfloor>"
   and not_fins: "\<not> finals(e # es)" by fact+
  have De: "\<D> e \<lfloor>dom l\<rfloor>" and Des: "\<D>s es (\<lfloor>dom l\<rfloor> \<squnion> \<A> e)"
    using D by auto
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume e: "e = Val v"
      hence Des': "\<D>s es \<lfloor>dom l\<rfloor>" using De Des by auto
      have not_fins_tl: "\<not> finals es" using not_fins e by simp
      show ?thesis using e IHes[OF hconf envconf Des' not_fins_tl]
        by (blast intro!:ListRed2)
    next
      fix r assume "e = Throw r"
      hence False using not_fins by simp
      thus ?thesis ..
    qed
  next
    assume "\<not> final e"
    from IHe[OF hconf envconf De this] show ?thesis by(fast intro!:ListRed1)
  qed
qed


end
