(*  Title:      Jinja/J/SmallProgress.thy

    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

section \<open>Progress of Small Step Semantics\<close>

theory Progress
imports Equivalence WellTypeRT DefAss "../Common/Conform"
begin

lemma final_addrE:
  "\<lbrakk> P,E,h \<turnstile> e : Class C; final e;
    \<And>a. e = addr a \<Longrightarrow> R;
    \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
(*<*)by(auto simp:final_def)(*>*)


lemma finalRefE:
 "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; final e;
   e = null \<Longrightarrow> R;
   \<And>a C. \<lbrakk> e = addr a; T = Class C \<rbrakk> \<Longrightarrow> R;
   \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
(*<*)by(auto simp:final_def is_refT_def)(*>*)


text\<open>Derivation of new induction scheme for well typing:\<close>

inductive
  WTrt' :: "[J_prog,heap,env,expr,ty] \<Rightarrow> bool"
  and WTrts' :: "[J_prog,heap,env,expr list, ty list] \<Rightarrow> bool"
  and WTrt2' :: "[J_prog,env,heap,expr,ty] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ :' _"   [51,51,51]50)
  and WTrts2' :: "[J_prog,env,heap,expr list, ty list] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ [:''] _" [51,51,51]50)
  for P :: J_prog and h :: heap
where
  "P,E,h \<turnstile> e :' T \<equiv> WTrt' P h E e T"
| "P,E,h \<turnstile> es [:'] Ts \<equiv> WTrts' P h E es Ts"

| "is_class P C  \<Longrightarrow>  P,E,h \<turnstile> new C :' Class C"
| "\<lbrakk> P,E,h \<turnstile> e :' T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> Cast C e :' Class C"
| "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> P,E,h \<turnstile> Val v :' T"
| "E v = Some T  \<Longrightarrow>  P,E,h \<turnstile> Var v :' T"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 :' T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2 :' T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>Eq\<guillemotright> e\<^sub>2 :' Boolean"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 :' Integer;  P,E,h \<turnstile> e\<^sub>2 :' Integer \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>Add\<guillemotright> e\<^sub>2 :' Integer"
| "\<lbrakk> P,E,h \<turnstile> Var V :' T;  P,E,h \<turnstile> e :' T';  P \<turnstile> T' \<le> T \<^cancel>\<open>V \<noteq> This\<close> \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> V:=e :' Void"
| "\<lbrakk> P,E,h \<turnstile> e :' Class C; P \<turnstile> C has F:T in D \<rbrakk> \<Longrightarrow> P,E,h \<turnstile> e\<bullet>F{D} :' T"
| "P,E,h \<turnstile> e :' NT \<Longrightarrow> P,E,h \<turnstile> e\<bullet>F{D} :' T"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 :' Class C;  P \<turnstile> C has F:T in D;
    P,E,h \<turnstile> e\<^sub>2 :' T\<^sub>2;  P \<turnstile> T\<^sub>2 \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 :' Void"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1:'NT; P,E,h \<turnstile> e\<^sub>2 :' T\<^sub>2 \<rbrakk> \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 :' Void"
| "\<lbrakk> P,E,h \<turnstile> e :' Class C; P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
    P,E,h \<turnstile> es [:'] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>M(es) :' T"
| "\<lbrakk> P,E,h \<turnstile> e :' NT; P,E,h \<turnstile> es [:'] Ts \<rbrakk> \<Longrightarrow> P,E,h \<turnstile> e\<bullet>M(es) :' T"
| "P,E,h \<turnstile> [] [:'] []"
| "\<lbrakk> P,E,h \<turnstile> e :' T;  P,E,h \<turnstile> es [:'] Ts \<rbrakk> \<Longrightarrow>  P,E,h \<turnstile> e#es [:'] T#Ts"
| "\<lbrakk> typeof\<^bsub>h\<^esub> v = Some T\<^sub>1; P \<turnstile> T\<^sub>1 \<le> T; P,E(V\<mapsto>T),h \<turnstile> e\<^sub>2 :' T\<^sub>2 \<rbrakk>
  \<Longrightarrow>  P,E,h \<turnstile> {V:T := Val v; e\<^sub>2} :' T\<^sub>2"
| "\<lbrakk> P,E(V\<mapsto>T),h \<turnstile> e :' T'; \<not> assigned V e \<rbrakk> \<Longrightarrow>  P,E,h \<turnstile> {V:T; e} :' T'"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1:' T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2:'T\<^sub>2 \<rbrakk>  \<Longrightarrow>  P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 :' T\<^sub>2"
| "\<lbrakk> P,E,h \<turnstile> e :' Boolean;  P,E,h \<turnstile> e\<^sub>1:' T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2:' T\<^sub>2;
    P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1;
    P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T = T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T = T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :' T"
(*
 "\<lbrakk> P,E,h \<turnstile> e :' Boolean;  P,E,h \<turnstile> e\<^sub>1:' T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2:' T\<^sub>2; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :' T\<^sub>2"
 "\<lbrakk> P,E,h \<turnstile> e :' Boolean;  P,E,h \<turnstile> e\<^sub>1:' T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2:' T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :' T\<^sub>1"
*)
| "\<lbrakk> P,E,h \<turnstile> e :' Boolean;  P,E,h \<turnstile> c:' T \<rbrakk>
  \<Longrightarrow>  P,E,h \<turnstile> while(e) c :' Void"
| "\<lbrakk> P,E,h \<turnstile> e :' T\<^sub>r; is_refT T\<^sub>r \<rbrakk>  \<Longrightarrow>  P,E,h \<turnstile> throw e :' T"
| "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 :' T\<^sub>1;  P,E(V \<mapsto> Class C),h \<turnstile> e\<^sub>2 :' T\<^sub>2; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 :' T\<^sub>2"

(*<*)
lemmas WTrt'_induct = WTrt'_WTrts'.induct [split_format (complete)]
  and WTrt'_inducts = WTrt'_WTrts'.inducts [split_format (complete)]

inductive_cases WTrt'_elim_cases[elim!]:
  "P,E,h \<turnstile> V :=e :' T"
(*>*)

lemma [iff]: "P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 :' T\<^sub>2 = (\<exists>T\<^sub>1. P,E,h \<turnstile> e\<^sub>1:' T\<^sub>1 \<and> P,E,h \<turnstile> e\<^sub>2:' T\<^sub>2)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done
(*>*)

lemma [iff]: "P,E,h \<turnstile> Val v :' T = (typeof\<^bsub>h\<^esub> v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done
(*>*)

lemma [iff]: "P,E,h \<turnstile> Var v :' T = (E v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done
(*>*)


lemma wt_wt': "P,E,h \<turnstile> e : T \<Longrightarrow> P,E,h \<turnstile> e :' T"
and wts_wts': "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> P,E,h \<turnstile> es [:'] Ts"
(*<*)
apply (induct rule:WTrt_inducts)
prefer 14
apply(case_tac "assigned V e")
apply(clarsimp simp add:fun_upd_same assigned_def simp del:fun_upd_apply)
apply(erule (2) WTrt'_WTrts'.intros)
apply(erule (1) WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)+
done
(*>*)


lemma wt'_wt: "P,E,h \<turnstile> e :' T \<Longrightarrow> P,E,h \<turnstile> e : T"
and wts'_wts: "P,E,h \<turnstile> es [:'] Ts \<Longrightarrow> P,E,h \<turnstile> es [:] Ts"
(*<*)
apply (induct rule:WTrt'_inducts)
prefer 16
apply(rule WTrt_WTrts.intros)
apply(rule WTrt_WTrts.intros)
apply(rule WTrt_WTrts.intros)
apply simp
apply(erule (2) WTrt_WTrts.intros)
apply(blast intro:WTrt_WTrts.intros)+
done
(*>*)


corollary wt'_iff_wt: "(P,E,h \<turnstile> e :' T) = (P,E,h \<turnstile> e : T)"
(*<*)by(blast intro:wt_wt' wt'_wt)(*>*)


corollary wts'_iff_wts: "(P,E,h \<turnstile> es [:'] Ts) = (P,E,h \<turnstile> es [:] Ts)"
(*<*)by(blast intro:wts_wts' wts'_wts)(*>*)

(*<*)
lemmas WTrt_inducts2 = WTrt'_inducts [unfolded wt'_iff_wt wts'_iff_wts,
 case_names WTrtNew WTrtCast WTrtVal WTrtVar WTrtBinOpEq WTrtBinOpAdd WTrtLAss WTrtFAcc WTrtFAccNT WTrtFAss
 WTrtFAssNT WTrtCall WTrtCallNT WTrtNil WTrtCons WTrtInitBlock WTrtBlock WTrtSeq WTrtCond
 WTrtWhile WTrtThrow WTrtTry, consumes 1]
(*>*)

theorem assumes wf: "wwf_J_prog P" and hconf: "P \<turnstile> h \<surd>"
shows progress: "P,E,h \<turnstile> e : T \<Longrightarrow>
 (\<And>l. \<lbrakk> \<D> e \<lfloor>dom l\<rfloor>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>)"
and "P,E,h \<turnstile> es [:] Ts \<Longrightarrow>
 (\<And>l. \<lbrakk> \<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es \<rbrakk> \<Longrightarrow> \<exists>es' s'. P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>)"
(*<*)
proof (induct rule:WTrt_inducts2)
  case WTrtNew
  show ?case
  proof cases
    assume "\<exists>a. h a = None"
    with assms WTrtNew show ?thesis
      by (fastforce del:exE intro!:RedNew simp add:new_Addr_def
                   elim!:wf_Fields_Ex[THEN exE])
  next
    assume "\<not>(\<exists>a. h a = None)"
    with assms WTrtNew show ?thesis
      by(fastforce intro:RedNewFail simp add:new_Addr_def)
  qed
next
  case (WTrtCast E e T C)
  have wte: "P,E,h \<turnstile> e : T" and ref: "is_refT T"
   and IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> (Cast C e) \<lfloor>dom l\<rfloor>" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  show ?case
  proof cases
    assume "final e"
    with wte ref show ?thesis
    proof (rule finalRefE)
      assume "e = null" thus ?case by(fastforce intro:RedCastNull)
    next
      fix D a assume A: "T = Class D" "e = addr a"
      show ?thesis
      proof cases
        assume "P \<turnstile> D \<preceq>\<^sup>* C"
        thus ?thesis using A wte by(fastforce intro:RedCast)
      next
        assume "\<not> P \<turnstile> D \<preceq>\<^sup>* C"
        thus ?thesis using A wte by(force intro!:RedCastFail)
      qed
    next
      fix a assume "e = Throw a"
      thus ?thesis by(blast intro!:red_reds.CastThrow)
    qed
  next
    assume nf: "\<not> final e"
    from IH[OF De nf] show ?thesis by (blast intro:CastRed)
  qed
next
  case WTrtVal thus ?case by(simp add:final_def)
next
  case WTrtVar thus ?case by(fastforce intro:RedVar simp:hyper_isin_def)
next
  case (WTrtBinOpEq E e1 T1 e2 T2)
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v1 assume [simp]: "e1 = Val v1"
      show ?thesis
      proof cases
        assume "final e2"
        thus ?thesis
        proof (rule finalE)
          fix v2 assume "e2 = Val v2"
          thus ?thesis using WTrtBinOpEq by(fastforce intro:RedBinOp)
        next
          fix a assume "e2 = Throw a"
          thus ?thesis by(auto intro:red_reds.BinOpThrow2)
        qed
      next
        assume "\<not> final e2" with WTrtBinOpEq show ?thesis
          by simp (fast intro!:BinOpRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by simp (fast intro:red_reds.BinOpThrow1)
    qed
  next
    assume "\<not> final e1" with WTrtBinOpEq show ?thesis
      by simp (fast intro:BinOpRed1)
  qed
next
  case (WTrtBinOpAdd E e1 e2)
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v1 assume [simp]: "e1 = Val v1"
      show ?thesis
      proof cases
        assume "final e2"
        thus ?thesis
        proof (rule finalE)
          fix v2 assume "e2 = Val v2"
          thus ?thesis using WTrtBinOpAdd by(fastforce intro:RedBinOp)
        next
          fix a assume "e2 = Throw a"
          thus ?thesis by(auto intro:red_reds.BinOpThrow2)
        qed
      next
        assume "\<not> final e2" with WTrtBinOpAdd show ?thesis
          by simp (fast intro!:BinOpRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by simp (fast intro:red_reds.BinOpThrow1)
    qed
  next
    assume "\<not> final e1" with WTrtBinOpAdd show ?thesis
      by simp (fast intro:BinOpRed1)
  qed
next
  case (WTrtLAss E V T e T')
  show ?case
  proof cases
    assume "final e" with WTrtLAss show ?thesis
      by(auto simp:final_def intro!:RedLAss red_reds.LAssThrow)
  next
    assume "\<not> final e" with WTrtLAss show ?thesis
      by simp (fast intro:LAssRed)
  qed
next
  case (WTrtFAcc E e C F T D)
  have wte: "P,E,h \<turnstile> e : Class C"
   and field: "P \<turnstile> C has F:T in D" by fact+
  show ?case
  proof cases
    assume "final e"
    with wte show ?thesis
    proof (rule final_addrE)
      fix a assume e: "e = addr a"
      with wte obtain fs where hp: "h a = Some(C,fs)" by auto
      with hconf have "P,h \<turnstile> (C,fs) \<surd>" using hconf_def by fastforce
      then obtain v where "fs(F,D) = Some v" using field
        by(fastforce dest:has_fields_fun simp:oconf_def has_field_def)
      with hp e show ?thesis by(fastforce intro:RedFAcc)
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fastforce intro:red_reds.FAccThrow)
    qed
  next
    assume "\<not> final e" with WTrtFAcc show ?thesis
      by(fastforce intro!:FAccRed)
  qed
next
  case (WTrtFAccNT E e F D T)
  show ?case
  proof cases
    assume "final e"  \<comment> \<open>@{term e} is @{term null} or @{term throw}\<close>
    with WTrtFAccNT show ?thesis
      by(fastforce simp:final_def intro: RedFAccNull red_reds.FAccThrow)
  next
    assume "\<not> final e" \<comment> \<open>@{term e} reduces by IH\<close>
    with WTrtFAccNT show ?thesis by simp (fast intro:FAccRed)
  qed
next
  case (WTrtFAss E e1 C F T D e2 T2)
  have wte1: "P,E,h \<turnstile> e1 : Class C" by fact
  show ?case
  proof cases
    assume "final e1"
    with wte1 show ?thesis
    proof (rule final_addrE)
      fix a assume e1: "e1 = addr a"
      show ?thesis
      proof cases
        assume "final e2"
        thus ?thesis
        proof (rule finalE)
          fix v assume "e2 = Val v"
          thus ?thesis using e1 wte1 by(fastforce intro:RedFAss)
        next
          fix a assume "e2 = Throw a"
          thus ?thesis using e1 by(fastforce intro:red_reds.FAssThrow2)
        qed
      next
        assume "\<not> final e2" with WTrtFAss e1 show ?thesis
          by simp (fast intro!:FAssRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by(fastforce intro:red_reds.FAssThrow1)
    qed
  next
    assume "\<not> final e1" with WTrtFAss show ?thesis
      by simp (blast intro!:FAssRed1)
  qed
next
  case (WTrtFAssNT E e\<^sub>1 e\<^sub>2 T\<^sub>2 F D)
  show ?case
  proof cases
    assume e1: "final e\<^sub>1"  \<comment> \<open>@{term e\<^sub>1} is @{term null} or @{term throw}\<close>
    show ?thesis
    proof cases
      assume "final e\<^sub>2"  \<comment> \<open>@{term e\<^sub>2} is @{term Val} or @{term throw}\<close>
      with WTrtFAssNT e1 show ?thesis
        by(fastforce simp:final_def intro: RedFAssNull red_reds.FAssThrow1 red_reds.FAssThrow2)
    next
      assume "\<not> final e\<^sub>2" \<comment> \<open>@{term e\<^sub>2} reduces by IH\<close>
      with WTrtFAssNT e1 show ?thesis
        by (fastforce  simp:final_def intro!:red_reds.FAssRed2 red_reds.FAssThrow1)
    qed
  next
    assume "\<not> final e\<^sub>1" \<comment> \<open>@{term e\<^sub>1} reduces by IH\<close>
    with WTrtFAssNT show ?thesis by (fastforce intro:FAssRed1)
  qed
next
  case (WTrtCall E e C M Ts T pns body D es Ts')
  have wte: "P,E,h \<turnstile> e : Class C"
   and "method": "P \<turnstile> C sees M:Ts\<rightarrow>T = (pns,body) in D"
   and wtes: "P,E,h \<turnstile> es [:] Ts'"and sub: "P \<turnstile> Ts' [\<le>] Ts"
   and IHes: "\<And>l.
             \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s'. P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
   and D: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e"
    with wte show ?thesis
    proof (rule final_addrE)
      fix a assume e_addr: "e = addr a"
      show ?thesis
      proof cases
        assume es: "\<exists>vs. es = map Val vs"
        from wte e_addr obtain fs where ha: "h a = Some(C,fs)" by auto
        show ?thesis
          using e_addr ha "method" WTrts_same_length[OF wtes] sub es sees_wf_mdecl[OF wf "method"]
          by (fastforce intro!: RedCall simp:list_all2_iff wf_mdecl_def)
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
          ultimately obtain b where ex_Throw: "?ex = Throw b"
            by(fast elim!:finalE)
          show ?thesis using e_addr es ex_Throw ves
            by(fastforce intro:CallThrowParams)
        next
          assume not_fin: "\<not> final ?ex"
          have "finals es = finals(?ves @ ?ex # ?rst)" using es
            by(rule arg_cong)
          also have "\<dots> = finals(?ex # ?rst)" using ves by simp
          finally have "finals es = finals(?ex # ?rst)" .
          hence "\<not> finals es" using not_finals_ConsI[OF not_fin] by blast
          thus ?thesis using e_addr D IHes  by(fastforce intro!:CallParams)
        qed
      qed
    next
      fix a assume "e = Throw a"
      with WTrtCall.prems show ?thesis by(fast intro!:CallThrowObj)
    qed
  next
    assume "\<not> final e"
    with WTrtCall show ?thesis by simp (blast intro!:CallObj)
  qed
next
  case (WTrtCallNT E e es Ts M T)
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
          with WTrtCallNT e have ?thesis by(fastforce intro: RedCallNull) }
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
    { fix a assume "e = Throw a"
      with WTrtCallNT have ?case by(fastforce intro: CallThrowObj) }
    ultimately show ?thesis by(fastforce simp:final_def)
  next
    assume "\<not> final e" \<comment> \<open>@{term e} reduces by IH\<close>
    with WTrtCallNT show ?thesis by (fastforce intro:CallObj)
  qed
next
  case WTrtNil thus ?case by simp
next
  case (WTrtCons E e T es Ts)
  have IHe: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
   and IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s'. P \<turnstile> \<langle>es,(h,l)\<rangle> [\<rightarrow>] \<langle>es',s'\<rangle>"
   and D: "\<D>s (e#es) \<lfloor>dom l\<rfloor>" and not_fins: "\<not> finals(e # es)" by fact+
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
      show ?thesis using e IHes[OF Des' not_fins_tl]
        by (blast intro!:ListRed2)
    next
      fix a assume "e = Throw a"
      hence False using not_fins by simp
      thus ?thesis ..
    qed
  next
    assume "\<not> final e"
    with IHe[OF De] show ?thesis by(fast intro!:ListRed1)
  qed
next
  case (WTrtInitBlock v T\<^sub>1 T E V e\<^sub>2 T\<^sub>2)
  have IH2: "\<And>l. \<lbrakk>\<D> e\<^sub>2 \<lfloor>dom l\<rfloor>; \<not> final e\<^sub>2\<rbrakk>
                  \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e\<^sub>2,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
   and D: "\<D> {V:T := Val v; e\<^sub>2} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e\<^sub>2"
    then show ?thesis
    proof (rule finalE)
      fix v\<^sub>2 assume "e\<^sub>2 = Val v\<^sub>2"
      thus ?thesis by(fast intro:RedInitBlock)
    next
      fix a assume "e\<^sub>2 = Throw a"
      thus ?thesis by(fast intro:red_reds.InitBlockThrow)
    qed
  next
    assume not_fin2: "\<not> final e\<^sub>2"
    from D have D2: "\<D> e\<^sub>2 \<lfloor>dom(l(V\<mapsto>v))\<rfloor>" by (auto simp:hyperset_defs)
    from IH2[OF D2 not_fin2]
    obtain h' l' e' where red2: "P \<turnstile> \<langle>e\<^sub>2,(h, l(V\<mapsto>v))\<rangle> \<rightarrow> \<langle>e',(h', l')\<rangle>"
      by auto
    from red_lcl_incr[OF red2] have "V \<in> dom l'" by auto
    with red2 show ?thesis by(fastforce intro:InitBlockRed)
  qed
next
  case (WTrtBlock E V T e T')
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; \<not> final e\<rbrakk>
                 \<Longrightarrow> \<exists>e' s'. P \<turnstile> \<langle>e,(h,l)\<rangle> \<rightarrow> \<langle>e',s'\<rangle>"
   and unass: "\<not> assigned V e" and D: "\<D> {V:T; e} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume "e = Val v" thus ?thesis by(fast intro:RedBlock)
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro:red_reds.BlockThrow)
    qed
  next
    assume not_fin: "\<not> final e"
    from D have De: "\<D> e \<lfloor>dom(l(V:=None))\<rfloor>" by(simp add:hyperset_defs)
    from IH[OF De not_fin]
    obtain h' l' e' where red: "P \<turnstile> \<langle>e,(h,l(V:=None))\<rangle> \<rightarrow> \<langle>e',(h',l')\<rangle>"
      by auto
    show ?thesis
    proof (cases "l' V")
      assume "l' V = None"
      with red unass show ?thesis by(blast intro: BlockRedNone)
    next
      fix v assume "l' V = Some v"
      with red unass show ?thesis by(blast intro: BlockRedSome)
    qed
  qed
next
  case (WTrtSeq E e1 T1 e2 T2)
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
      by(fast elim:finalE intro:RedSeq red_reds.SeqThrow)
  next
    assume "\<not> final e1" with WTrtSeq show ?thesis
      by simp (blast intro:SeqRed)
  qed
next
  case (WTrtCond E e e\<^sub>1 T\<^sub>1 e\<^sub>2 T\<^sub>2 T)
  have wt: "P,E,h \<turnstile> e : Boolean" by fact
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume val: "e = Val v"
      then obtain b where v: "v = Bool b" using wt by auto
      show ?thesis
      proof (cases b)
        case True with val v show ?thesis by(auto intro:RedCondT)
      next
        case False with val v show ?thesis by(auto intro:RedCondF)
      qed
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro:red_reds.CondThrow)
    qed
  next
    assume "\<not> final e" with WTrtCond show ?thesis
      by simp (fast intro:CondRed)
  qed
next
  case WTrtWhile show ?case by(fast intro:RedWhile)
next
  case (WTrtThrow E e T\<^sub>r T)
  show ?case
  proof cases
    assume "final e" \<comment> \<open>Then @{term e} must be @{term throw} or @{term null}\<close>
    with WTrtThrow show ?thesis
      by(fastforce simp:final_def is_refT_def
                  intro:red_reds.ThrowThrow red_reds.RedThrowNull)
  next
    assume "\<not> final e" \<comment> \<open>Then @{term e} must reduce\<close>
    with WTrtThrow show ?thesis by simp (blast intro:ThrowRed)
  qed
next
  case (WTrtTry E e1 T1 V C e2 T2)
  have wt1: "P,E,h \<turnstile> e1 : T1" by fact
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v assume "e1 = Val v"
      thus ?thesis by(fast intro:RedTry)
    next
      fix a assume e1_Throw: "e1 = Throw a"
      with wt1 obtain D fs where ha: "h a = Some(D,fs)" by fastforce
      show ?thesis
      proof cases
        assume "P \<turnstile> D \<preceq>\<^sup>* C"
        with e1_Throw ha show ?thesis by(fastforce intro!:RedTryCatch)
      next
        assume "\<not> P \<turnstile> D \<preceq>\<^sup>* C"
        with e1_Throw ha show ?thesis by(force intro!:RedTryFail)
      qed
    qed
  next
    assume "\<not> final e1"
    with WTrtTry show ?thesis by simp (fast intro:TryRed)
  qed
qed
(*>*)


end
