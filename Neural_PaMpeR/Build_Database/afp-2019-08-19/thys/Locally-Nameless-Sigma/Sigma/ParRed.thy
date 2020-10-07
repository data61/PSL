(*  Title:      Sigma/ParRed.thy
    Author:     Ludovic Henrio and Florian Kammuller
    Copyright   2006

Confluence of beta for ASP, based on the equally named file in HOL/Proofs/Lambda.
*)

section \<open>Parallel reduction\<close>

theory ParRed imports "HOL-Proofs-Lambda.Commutation" Sigma begin

subsection \<open>Parallel reduction\<close>
inductive par_beta :: "[sterm,sterm] \<Rightarrow> bool"  (infixl "\<Rightarrow>\<^sub>\<beta>" 50)
  where
  pbeta_Fvar[simp,intro!]: "Fvar x \<Rightarrow>\<^sub>\<beta> Fvar x"
| pbeta_Obj[simp,intro!] : 
  "\<lbrakk> dom f' = dom f; finite L;
     \<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>t. (the(f l)\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t 
                        \<and> the(f' l) = \<sigma>[s,p] t);
     \<forall>l\<in>dom f. body (the(f l)) \<rbrakk> \<Longrightarrow> Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T"
| pbeta_Upd[simp,intro!] : 
  "\<lbrakk> t \<Rightarrow>\<^sub>\<beta> t'; lc t; finite L; 
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
      \<longrightarrow> (\<exists>t''. (u\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t'' \<and> u' = \<sigma>[s,p] t'');
     body u \<rbrakk> \<Longrightarrow> Upd t l u \<Rightarrow>\<^sub>\<beta> Upd t' l u'"
| pbeta_Upd'[simp,intro!]: 
  "\<lbrakk> Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T; finite L;
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
       \<longrightarrow> (\<exists>t''. (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t'' \<and> t' = \<sigma>[s,p] t''); l \<in> dom f;
     lc (Obj f T); body t \<rbrakk> \<Longrightarrow> (Upd (Obj f T) l t)  \<Rightarrow>\<^sub>\<beta> (Obj (f'(l \<mapsto> t')) T)"
| pbeta_Call[simp,intro!]: 
  "\<lbrakk> t \<Rightarrow>\<^sub>\<beta> t'; u \<Rightarrow>\<^sub>\<beta> u'; lc t; lc u \<rbrakk>
  \<Longrightarrow> Call t l u \<Rightarrow>\<^sub>\<beta> Call t' l u'"
| pbeta_beta[simp,intro!]: 
  "\<lbrakk> Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T; l \<in> dom f; p \<Rightarrow>\<^sub>\<beta> p'; lc (Obj f T); lc p \<rbrakk>
  \<Longrightarrow> Call (Obj f T) l p \<Rightarrow>\<^sub>\<beta> (the(f' l)\<^bsup>[(Obj f' T), p']\<^esup>)"

(* These are rule formats for inversions rules *)

inductive_cases par_beta_cases [elim!]:
  "Fvar x \<Rightarrow>\<^sub>\<beta> t"
  "Obj f T \<Rightarrow>\<^sub>\<beta> t"
  "Call f l p \<Rightarrow>\<^sub>\<beta> t"
  "Upd f l t \<Rightarrow>\<^sub>\<beta> u"

abbreviation
  par_beta_ascii :: "[sterm, sterm] => bool"  (infixl "=>" 50) where
  "t => u == par_beta t u"

lemma Obj_par_red[consumes 1, case_names obj]: 
  "\<lbrakk> Obj f T \<Rightarrow>\<^sub>\<beta> z; 
     \<And>lz. \<lbrakk> dom lz = dom f; z = Obj lz T\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (rule par_beta_cases(2), assumption, auto)

lemma Upd_par_red[consumes 1, case_names upd obj]: 
  fixes t l u z
  assumes 
  "Upd t l u \<Rightarrow>\<^sub>\<beta> z" and
  "\<And>t' u' L. \<lbrakk> t \<Rightarrow>\<^sub>\<beta> t'; finite L;
                \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>t''. (u\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t'' 
                          \<and> u' = \<sigma>[s,p]t'');
                z = Upd t' l u' \<rbrakk> \<Longrightarrow> Q" and
  "\<And>f f' T u' L. \<lbrakk> l \<in> dom f; Obj f T = t; Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T;
                    finite L;
                    \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                     \<longrightarrow> (\<exists>t''. (u\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t'' 
                              \<and> u' = \<sigma>[s,p]t'');
                z = Obj (f'(l \<mapsto> u')) T \<rbrakk> \<Longrightarrow> Q"
  shows Q
  using assms
proof (cases rule: par_beta.cases)
  case pbeta_Upd thus ?thesis using assms(2) by force
next
  case pbeta_Upd'
  from this(1-2) this(5-6) assms(3)[OF _ _ this(3-4)]
  show ?thesis by force
qed

lemma Call_par_red[consumes 1, case_names call beta]: 
  fixes s l u z
  assumes 
  "Call s l u \<Rightarrow>\<^sub>\<beta> z" and
  "\<And>t u'. \<lbrakk> s \<Rightarrow>\<^sub>\<beta> t; u \<Rightarrow>\<^sub>\<beta> u'; z = Call t l u' \<rbrakk>
  \<Longrightarrow> Q"
  "\<And>f f' T u'. \<lbrakk> Obj f T = s; Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T;
                  l \<in> dom f'; u \<Rightarrow>\<^sub>\<beta> u';
                  z = (the (f' l)\<^bsup>[Obj f' T, u']\<^esup>) \<rbrakk> \<Longrightarrow> Q"
  shows Q
  using assms
proof (cases rule: par_beta.cases)
  case pbeta_Call thus ?thesis using assms(2) by force
next
  case pbeta_beta
  from this(1-5) assms(3)[OF _ this(3)]
  show ?thesis by force
qed

lemma pbeta_induct[consumes 1, case_names Fvar Call Upd Upd' Obj beta Bnd]:
  fixes 
  t :: sterm and t' :: sterm and 
  P1 :: "sterm \<Rightarrow> sterm \<Rightarrow> bool" and P2 :: "sterm \<Rightarrow> sterm \<Rightarrow> bool"
  assumes
  "t \<Rightarrow>\<^sub>\<beta> t'" and
  "\<And>x. P1 (Fvar x) (Fvar x)" and
  "\<And>t t' l u u'. \<lbrakk> t \<Rightarrow>\<^sub>\<beta> t'; P1 t t'; lc t; u \<Rightarrow>\<^sub>\<beta> u'; P1 u u'; lc u \<rbrakk> 
      \<Longrightarrow> P1 (Call t l u) (Call t' l u')" and
  "\<And>t t' l u u'. \<lbrakk> t \<Rightarrow>\<^sub>\<beta> t'; P1 t t'; lc t; P2 u u'; body u \<rbrakk>
      \<Longrightarrow> P1 (Upd t l u) (Upd t' l u')" and
  "\<And>f f' T t t' l. \<lbrakk> Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T; P1 (Obj f T) (Obj f' T);
                      P2 t t'; l \<in> dom f; lc (Obj f T); body t \<rbrakk>
      \<Longrightarrow> P1 (Upd (Obj f T) l t) (Obj (f'(l \<mapsto> t')) T)" and
  "\<And>f f' T. \<lbrakk> dom f' = dom f; \<forall>l\<in>dom f. body (the(f l)); 
               \<forall>l\<in>dom f. P2 (the(f l)) (the(f' l)) \<rbrakk>
      \<Longrightarrow> P1 (Obj f T) (Obj f' T)" and
  "\<And>f f' T l p p'. \<lbrakk> Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T; P1 (Obj f T) (Obj f' T); lc (Obj f T);
                      l \<in> dom f; p \<Rightarrow>\<^sub>\<beta> p'; P1 p p'; lc p \<rbrakk>
      \<Longrightarrow> P1 (Call (Obj f T) l p) (the(f' l)\<^bsup>[Obj f' T, p']\<^esup>)" and
  "\<And>L t t'. 
      \<lbrakk> finite L; 
        \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
        \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' 
                 \<and> P1 (t\<^bsup>[Fvar s,Fvar p]\<^esup>) t'' \<and> t' = \<sigma>[s,p] t'') \<rbrakk>
      \<Longrightarrow> P2 t t'"
  shows "P1 t t'"
  by (induct rule: par_beta.induct[OF assms(1)], auto simp: assms)

subsection \<open>Preservation\<close>
lemma par_beta_lc[simp]:
  fixes t t'
  assumes "t \<Rightarrow>\<^sub>\<beta> t'"
  shows "lc t \<and> lc t'"
using assms
proof 
  (induct
    taking: "\<lambda>t t'. body t'"
    rule: pbeta_induct)
  case Fvar thus ?case by simp
next
  case Call thus ?case by simp
next
  case Upd thus ?case by (simp add: lc_upd)
next
  case Upd' thus ?case by (simp add: lc_upd lc_obj)
next
  case Obj thus ?case by (simp add: lc_obj)
next
  case (beta f f' T l p p') thus ?case 
    by (clarify, simp add: lc_obj body_lc[of "the(f' l)" "Obj f' T" p'])
next
  case (Bnd L t t') note cof = this(2)
  from exFresh_s_p_cof[OF \<open>finite L\<close>]
  obtain s p where sp: "s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p" by auto
  with cof obtain t'' where "lc t''" and "t' = \<sigma>[s,p] t''" by blast
  with lc_body[of t'' s p] sp show "body t'" by force
qed

lemma par_beta_preserves_FV[simp, rule_format]: 
  fixes t t' x
  assumes "t \<Rightarrow>\<^sub>\<beta> t'"
  shows "x \<notin> FV t \<longrightarrow> x \<notin> FV t'"
using assms
proof 
  (induct
    taking: "\<lambda>t t'. x \<notin> FV t \<longrightarrow> x \<notin> FV t'"
    rule: pbeta_induct)
  case Fvar thus ?case by simp
next
  case Call thus ?case by simp
next
  case Upd thus ?case by simp
next
  case Upd' thus ?case by simp
next
  case Obj thus ?case by (simp add: FV_option_lem)
next
  case (beta f f' T l p p') thus ?case
  proof (intro strip)
    assume "x \<notin> FV (Call (Obj f T) l p)"
    with
      \<open>x \<notin> FV (Obj f T) \<longrightarrow> x \<notin> FV (Obj f' T)\<close>
      \<open>x \<notin> FV p \<longrightarrow> x \<notin> FV p'\<close>
    have obj': "x \<notin> FV (Obj f' T)" and p': "x \<notin> FV p'"
      by auto
    from \<open>l \<in> dom f\<close> \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close> have "l \<in> dom f'"
      by auto
    with 
      obj' p' FV_option_lem[of f']
      contra_subsetD[OF sopen_FV[of 0 "Obj f' T" p' "the(f' l)"]]
    show "x \<notin> FV (the (f' l)\<^bsup>[Obj f' T,p']\<^esup>)" by (auto simp: openz_def)
  qed
next
  case (Bnd L t t') note cof = this(2)
  from \<open>finite L\<close> exFresh_s_p_cof[of "L \<union> {x}"]
  obtain s p where 
    "s \<notin> L"and "p \<notin> L" and "s \<noteq> p" and 
    "x \<notin> FV (Fvar s)" and "x \<notin> FV (Fvar p)"
    by auto
  with cof obtain t'' where
    tt'': "x \<notin> FV (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<longrightarrow> x \<notin> FV t''" and
    "t' = \<sigma>[s,p] t''"
    by auto
  show ?case
  proof (intro strip)
    assume "x \<notin> FV t"
    with 
      tt'' \<open>x \<notin> FV (Fvar s)\<close> \<open>x \<notin> FV (Fvar p)\<close>
      contra_subsetD[OF sopen_FV[of 0 "Fvar s" "Fvar p" t]]
      sclose_subset_FV[of 0 s p t''] \<open>t' = \<sigma>[s,p] t''\<close>
    show "x \<notin> FV t'" by (auto simp: openz_def closez_def)
  qed
qed

lemma par_beta_body[simp]:
  "\<lbrakk> finite L; 
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
      \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' \<and> t' = \<sigma>[s,p] t'') \<rbrakk>
  \<Longrightarrow> body t \<and> body t'"
proof (intro conjI)
  fix L :: "fVariable set" and t :: sterm and t' :: sterm
  assume "finite L" hence "finite (L \<union> FV t)" by simp
  from exFresh_s_p_cof[OF this] 
  obtain s p where sp: "s \<notin> L \<union> FV t \<and> p \<notin> L \<union> FV t \<and> s \<noteq> p" by auto
  hence "s \<notin> FV t" and "p \<notin> FV t" and "s \<noteq> p" by auto

  assume 
    "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
      \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> => t'' \<and> t' = \<sigma>[s,p] t'')"
  with sp obtain t'' where "t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t''" and "t' = \<sigma>[s,p] t''"
    by blast

  from par_beta_lc[OF this(1)] have "lc (t\<^bsup>[Fvar s,Fvar p]\<^esup>)" and "lc t''" 
    by auto

  from 
    lc_body[OF this(1) \<open>s \<noteq> p\<close>] 
    sclose_sopen_eq_t[OF \<open>s \<notin> FV t\<close> \<open>p \<notin> FV t\<close> \<open>s \<noteq> p\<close>] 
  show "body t"
    by (simp add: closez_def openz_def)

  from lc_body[OF \<open>lc t''\<close> \<open>s \<noteq> p\<close>] \<open>t' = \<sigma>[s,p] t''\<close> show "body t'" by simp
qed

subsection \<open>Miscellaneous properties of par\_beta\<close>
lemma Fvar_pbeta [simp]: "(Fvar x \<Rightarrow>\<^sub>\<beta> t) = (t = Fvar x)" by auto
lemma Obj_pbeta: "Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T
  \<Longrightarrow> dom f' = dom f 
      \<and> (\<exists>L. finite L 
           \<and> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
               \<longrightarrow> (\<exists>t. (the(f l)\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t 
                      \<and> the(f' l) = \<sigma>[s,p]t)))
      \<and> (\<forall>l\<in>dom f. body (the(f l)))"
  by (rule par_beta_cases(2), assumption, auto)

lemma Obj_pbeta_subst: 
  "\<lbrakk> finite L; 
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
      \<longrightarrow> (\<exists>t''. (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t'' \<and> t' = \<sigma>[s,p] t''); 
     Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T; lc (Obj f T); body t \<rbrakk>
  \<Longrightarrow> Obj (f(l \<mapsto> t)) T \<Rightarrow>\<^sub>\<beta> Obj (f'(l \<mapsto> t')) T"
proof -
  fix L f f' T l t t' 
  assume "Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T" from Obj_pbeta[OF this]
  have 
    dom: "dom (f'(l \<mapsto> t')) = dom (f(l \<mapsto> t))" and 
    exL: "\<exists>L. finite L 
            \<and> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                           \<longrightarrow> (\<exists>t. the (f l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                                  \<and> the (f' l) = \<sigma>[s,p] t))" and
    bodyf: "\<forall>l\<in>dom f. body (the (f l))"
    by auto

  assume "body t" with bodyf 
  have body: "\<forall>l'\<in>dom (f(l \<mapsto> t)). body (the ((f(l \<mapsto> t)) l'))"
    by auto

  assume 
    "finite L" and
    "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
      \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' \<and> t' = \<sigma>[s,p] t'')"
  with exL
  obtain L' where 
    "finite (L' \<union> L)" and
    "\<forall>l'\<in>dom (f(l \<mapsto> t)). \<forall>s p. s \<notin> L' \<union> L \<and> p \<notin> L' \<union> L \<and> s \<noteq> p 
                            \<longrightarrow> (\<exists>t''. the ((f(l \<mapsto> t)) l')\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' 
                                     \<and> the ((f'(l \<mapsto> t')) l') = \<sigma>[s,p] t'')"
    by auto
  from par_beta.pbeta_Obj[OF dom this body]
  show "Obj (f(l \<mapsto> t)) T \<Rightarrow>\<^sub>\<beta> Obj (f'(l \<mapsto> t')) T"
    by assumption
qed

lemma Upd_pbeta: "Upd t l u \<Rightarrow>\<^sub>\<beta> Upd t' l u'
  \<Longrightarrow> t \<Rightarrow>\<^sub>\<beta> t' 
      \<and> (\<exists>L. finite L 
           \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
               \<longrightarrow> (\<exists>t''. (u\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t'' \<and> u' = \<sigma>[s,p]t'')))
      \<and> lc t \<and> body u"
  by (rule par_beta_cases(4), assumption, auto)

lemma par_beta_refl: 
  fixes t
  assumes "lc t"
  shows "t \<Rightarrow>\<^sub>\<beta> t"
  using assms
proof -
  define pred_cof
    where "pred_cof L t \<longleftrightarrow>
      (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> (\<exists>t'. (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t' \<and> t = \<sigma>[s,p] t'))"
    for L t
  from assms show ?thesis
  proof 
    (induct
      taking: "\<lambda>t. body t \<and> (\<exists>L. finite L \<and> pred_cof L t)"
      rule: lc_induct)
    case Fvar thus ?case by simp
  next
    case Call thus ?case by simp
  next
    case Upd thus ?case
      unfolding pred_cof_def
      by auto
  next
    case (Obj f T) note pred = this
    define pred_fl where "pred_fl s p b l \<longleftrightarrow> (\<exists>t'. (the b\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t' \<and> the b = \<sigma>[s,p]t')"
      for s p b and l :: Label

    from fmap_ex_cof[of f pred_fl] pred
    obtain L where
      "finite L" and "\<forall>l\<in>dom f. body (the(f l)) 
                              \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> pred_fl s p (f l) l)"
      unfolding pred_cof_def pred_fl_def
      by auto
    thus "Obj f T \<Rightarrow>\<^sub>\<beta> Obj f T"
      unfolding pred_fl_def
      by auto
  next
    case (Bnd L t) note pred = this(2)
    with \<open>finite L\<close> show ?case
    proof 
      (auto simp: body_def, unfold pred_cof_def,
        rule_tac x = "L \<union> FV t" in exI, simp, clarify)
      fix s p assume 
        "s \<notin> L" and "p \<notin> L" and "s \<noteq> p" and
        "s \<notin> FV t" and "p \<notin> FV t"
      from 
        this(1-3) pred 
        sclose_sopen_eq_t[OF this(4-5) this(3)]
      show "\<exists>t'. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t' \<and> t = \<sigma>[s,p] t'"
        by (rule_tac x = "t\<^bsup>[Fvar s,Fvar p]\<^esup>" in exI, simp add: openz_def closez_def)
    qed
  qed
qed

lemma par_beta_body_refl:
  fixes u
  assumes "body u"
  shows "\<exists>L. finite L \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                          \<longrightarrow> (\<exists>t'. (u\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t' \<and> u = \<sigma>[s,p] t'))"
proof (rule_tac x = "FV u" in exI, simp, clarify)
  fix s p assume "s \<notin> FV u" and "p \<notin> FV u" and "s \<noteq> p"
  from 
    par_beta_refl[OF body_lc[OF assms lc_Fvar[of s] lc_Fvar[of p]]]
    sclose_sopen_eq_t[OF this]
  show "\<exists>t'. (u\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t' \<and> u = \<sigma>[s,p] t'"
    by (rule_tac x = "u\<^bsup>[Fvar s, Fvar p]\<^esup>" in exI, simp add: openz_def closez_def)
qed

lemma par_beta_ssubst[rule_format]:
  fixes t t'
  assumes "t \<Rightarrow>\<^sub>\<beta> t'"
  shows "\<forall>x v v'. v \<Rightarrow>\<^sub>\<beta> v' \<longrightarrow> [x \<rightarrow> v] t \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] t'"
proof -
  define pred_cof
    where "pred_cof L t t' \<longleftrightarrow>
      (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' \<and> t' = \<sigma>[s,p] t''))"
    for L t t'
  {
    fix x v v' t t'
    assume 
      "v \<Rightarrow>\<^sub>\<beta> v'" and
      "\<forall>x v v'. v \<Rightarrow>\<^sub>\<beta> v' \<longrightarrow> (\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v'] t'))"
    hence
      "\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v'] t')"
        by auto
  }note Lex = this

  {
    fix x v l and f :: "Label \<Rightarrow> sterm option"
    assume "l \<in> dom f" hence "l \<in> dom (\<lambda>l. ssubst_option x v (f l))"
      by simp
  }note domssubst = this
  {
    fix x v l T and f :: "Label \<Rightarrow> sterm option"
    assume "lc (Obj f T)" and "lc v" from ssubst_preserves_lc[OF this] 
    have obj: "lc (Obj (\<lambda>l. ssubst_option x v (f l)) T)" by simp
  }note lcobj = this

  from assms show ?thesis
  proof 
    (induct
      taking: "\<lambda>t t'. \<forall>x v v'. v \<Rightarrow>\<^sub>\<beta> v'
                       \<longrightarrow> (\<exists>L. finite L 
                              \<and> pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v'] t'))"
      rule: pbeta_induct)
    case Fvar thus ?case by simp
  next
    case Call thus ?case by simp
  next
    case (Upd t t' l u u') note pred_t = this(2) and pred_u = this(4)
    show ?case
    proof (intro strip)
      fix x v v' assume "v \<Rightarrow>\<^sub>\<beta> v'"
      from Lex[OF this pred_u]
      obtain L where
        "finite L" and "pred_cof L ([x \<rightarrow> v] u) ([x \<rightarrow> v'] u')"
        by auto
      with
        ssubst_preserves_lc[of t v x]
        ssubst_preserves_body[of u v x]
        \<open>lc t\<close> par_beta_lc[OF \<open>v \<Rightarrow>\<^sub>\<beta> v'\<close>] \<open>body u\<close>
        \<open>v \<Rightarrow>\<^sub>\<beta> v'\<close> pred_t
      show "[x \<rightarrow> v] Upd t l u \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] Upd t' l u'"
        unfolding pred_cof_def
        by auto
    qed
  next
    case (Upd' f f' T t t' l) 
    note pred_obj = this(2) and pred_t = this(3)
    show ?case
    proof (intro strip)
      from \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close> \<open>l \<in> dom f\<close> have "l \<in> dom f'" by auto
      fix x v v' assume "v \<Rightarrow>\<^sub>\<beta> v'"
      with
        domssubst[OF \<open>l \<in> dom f\<close>]
        ssubst_preserves_lc[of "Obj f T" v x]
        ssubst_preserves_body[of t v x]
        \<open>lc (Obj f T)\<close> par_beta_lc[OF \<open>v \<Rightarrow>\<^sub>\<beta> v'\<close>] \<open>body t\<close>
        pred_obj
      have 
        "[x \<rightarrow> v] Obj f T \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] Obj f' T" and
        "lc ([x \<rightarrow> v] Obj f T)" and "body ([x \<rightarrow> v] t)"
        by auto
      note lem = 
        pbeta_Upd'[OF this(1)[simplified] _ _ 
                      domssubst[OF \<open>l \<in> dom f\<close>] 
                      this(2)[simplified] this(3)]

      from Lex[OF \<open>v \<Rightarrow>\<^sub>\<beta> v'\<close> pred_t]
      obtain L where
        "finite L" and "pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v'] t')"
        by auto
      with lem[of L "[x \<rightarrow> v'] t'"] ssubstoption_insert[OF \<open>l \<in> dom f'\<close>]
      show "[x \<rightarrow> v] Upd (Obj f T) l t \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] Obj (f'(l \<mapsto> t')) T"
        unfolding pred_cof_def
        by auto
    qed
  next
    case (beta f f' T l p p') 
    note pred_obj = this(2) and pred_p = this(6)
    show ?case
    proof (intro strip)
      fix x v v' assume "v \<Rightarrow>\<^sub>\<beta> v'"
      from 
        par_beta_lc[OF this]
        ssubst_preserves_lc[OF \<open>lc p\<close>]
      have "lc v" and "lc v'" and "lc ([x \<rightarrow> v] p)" by auto
      note lem = 
        pbeta_beta[OF _ domssubst[OF \<open>l \<in> dom f\<close>] _ 
                      lcobj[OF \<open>lc (Obj f T)\<close> this(1)] this(3)]
      from \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close> have "dom f = dom f'" by auto
      with \<open>l \<in> dom f\<close> have "the (ssubst_option x v' (f' l)) = [x \<rightarrow> v'] the (f' l)"
        by auto
      with
        lem[of x "\<lambda>l. ssubst_option x v' (f' l)" "[x \<rightarrow> v'] p'"]
        \<open>v \<Rightarrow>\<^sub>\<beta> v'\<close> pred_obj pred_p
        ssubst_openz_distrib[OF \<open>lc v'\<close>]
      show
        "[x \<rightarrow> v] Call (Obj f T) l p \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] (the (f' l)\<^bsup>[Obj f' T, p']\<^esup>)"
        by simp
    qed
  next
    case (Obj f f' T) note pred = fmap_ball_all3[OF this(1) this(3)]
    show ?case
    proof (intro strip)
      fix x v v'
      define pred_bnd
        where "pred_bnd s p b b' l \<longleftrightarrow>
          (\<exists>t''. [x \<rightarrow> v] the b\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' \<and> [x \<rightarrow> v'] the b' = \<sigma>[s,p] t'')"
        for s p b b' and l::Label
      assume "v \<Rightarrow>\<^sub>\<beta> v'"
      with pred \<open>dom f' = dom f\<close> fmap_ex_cof2[of f' f pred_bnd] 
      obtain L where
        "finite L" and 
        predf: "\<forall>l\<in>dom f. pred_cof L ([x \<rightarrow> v] the (f l)) ([x \<rightarrow> v'] the (f' l))"
        unfolding pred_cof_def pred_bnd_def 
        by auto

      have "\<forall>l\<in>dom (\<lambda>l. ssubst_option x v (f l)). body (the (ssubst_option x v (f l)))"
      proof (intro strip, simp)
        fix l' :: Label assume "l' \<in> dom f"
        with \<open>\<forall>l\<in>dom f. body (the(f l))\<close> have "body (the (f l'))" by blast
        note ssubst_preserves_body[OF this]
        from 
          this[of v x] par_beta_lc[OF \<open>v \<Rightarrow>\<^sub>\<beta> v'\<close>]
          \<open>l' \<in> dom f\<close> ssubst_option_lem[of f x v]
        show "body (the (ssubst_option x v (f l')))" by auto
      qed
      note intro = pbeta_Obj[OF _ \<open>finite L\<close> _ this]
      from
        predf
        ssubst_option_lem[of f x v]
        ssubst_option_lem[of f' x v'] \<open>dom f' = dom f\<close>
        dom_ssubstoption_lem[of x v f]
        dom_ssubstoption_lem[of x v' f']
      show "[x \<rightarrow> v] Obj f T \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] Obj f' T"
        unfolding pred_cof_def
        by (simp, intro intro[of "(\<lambda>l. ssubst_option x v' (f' l))" T], auto)
    qed
  next
    case (Bnd L t t') note pred = this(2)
    show ?case
    proof (intro strip)
      fix x v v' assume "v \<Rightarrow>\<^sub>\<beta> v'"
      from \<open>finite L\<close>
      show "\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v'] t')"
      proof (rule_tac x = "L \<union> {x} \<union> FV v'" in exI, 
          unfold pred_cof_def, auto)
        fix s p assume "s \<notin> L" and "p \<notin> L" and "s \<noteq> p"
        with pred 
        obtain t'' where
          "t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t''" and
          "\<forall>x v v'. v \<Rightarrow>\<^sub>\<beta> v' \<longrightarrow> [x \<rightarrow> v] (t\<^bsup>[Fvar s,Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] t''" and
          "t' = \<sigma>[s,p] t''"
          by blast
        from this(2) \<open>v \<Rightarrow>\<^sub>\<beta> v'\<close> 
        have ssubst_pbeta: "[x \<rightarrow> v] (t\<^bsup>[Fvar s,Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] t''" by blast
        
        assume "s \<noteq> x" and "p \<noteq> x"
        hence "x \<notin> FV (Fvar s)" and "x \<notin> FV (Fvar p)" by auto
        from 
          ssubst_pbeta
          par_beta_lc[OF \<open>v \<Rightarrow>\<^sub>\<beta> v'\<close>] ssubst_sopen_commute[OF _ this]
        have "[x \<rightarrow> v] t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> [x \<rightarrow> v'] t''" by (simp add: openz_def)
        moreover
        assume "s \<notin> FV v'" and "p \<notin> FV v'"
        from 
          ssubst_sclose_commute[OF this not_sym[OF \<open>s \<noteq> x\<close>] 
                                        not_sym[OF \<open>p \<noteq> x\<close>]] 
          \<open>t' = \<sigma>[s,p] t''\<close>
        have "[x \<rightarrow> v'] t' = \<sigma>[s,p] [x \<rightarrow> v'] t''" by (simp add: closez_def)
        ultimately
        show "\<exists>t''. [x \<rightarrow> v] t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' \<and> [x \<rightarrow> v'] t' = \<sigma>[s,p] t''" 
          by (rule_tac x = "[x \<rightarrow> v'] t''" in exI, simp)
      qed
    qed
  qed
qed

lemma renaming_par_beta: "t \<Rightarrow>\<^sub>\<beta> t' \<Longrightarrow> [s \<rightarrow> Fvar sa] t \<Rightarrow>\<^sub>\<beta> [s \<rightarrow> Fvar sa] t'"
  by (erule par_beta_ssubst, simp+)

lemma par_beta_beta:
  fixes l f f' u u'
  assumes 
  "l \<in> dom f" and "Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T" and "u \<Rightarrow>\<^sub>\<beta> u'" and "lc (Obj f T)" and "lc u"
  shows "(the(f l)\<^bsup>[Obj f T, u]\<^esup>) \<Rightarrow>\<^sub>\<beta> (the(f' l)\<^bsup>[Obj f' T, u']\<^esup>)"
proof -
  from Obj_pbeta[OF \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close>] 
  obtain L where 
    "dom f = dom f'" and
    "finite L" and
    pred_sp: "\<forall>l\<in>dom f.\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
                         \<longrightarrow> (\<exists>t''. the (f l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' 
                                  \<and> the (f' l) = \<sigma>[s,p] t'')" and
    "\<forall>l\<in>dom f. body (the (f l))"
    by auto

  from this(2) finite_FV[of "Obj f T"] have fin: "finite (L \<union> FV (Obj f T) \<union> FV u)" by simp
  from exFresh_s_p_cof[OF this]
  obtain s p where 
    sp: "s \<notin> L \<union> FV (Obj f T) \<union> FV u \<and> p \<notin> L \<union> FV (Obj f T) \<union> FV u \<and> s \<noteq> p"
    by auto
  with \<open>l \<in> dom f\<close> obtain t'' where 
    "the (f l)\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t''" and "the (f' l) = \<sigma>[s,p] t''"
    using pred_sp by blast
  from par_beta_lc[OF this(1)] have "lc t''" by simp
  from 
    sopen_sclose_eq_t[OF this] 
    \<open>the (f l)\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t''\<close> \<open>the(f' l) = \<sigma>[s,p] t''\<close>
  have "the (f l)\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> (the (f' l)\<^bsup>[Fvar s, Fvar p]\<^esup>)" 
    by (simp add: openz_def closez_def)
  from par_beta_ssubst[OF this] \<open>u \<Rightarrow>\<^sub>\<beta> u'\<close>
  have "[p \<rightarrow> u] (the (f l)\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> [p \<rightarrow> u'] (the (f' l)\<^bsup>[Fvar s, Fvar p]\<^esup>)"
    by simp
  note par_beta_ssubst[OF this \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close>]
  moreover
  from \<open>l \<in> dom f\<close> sp
  have "s \<notin> FV (the(f l))" and "p \<notin> FV (the(f l))" and "s \<noteq> p" and "s \<notin> FV u"
    by force+
  note ssubst_intro[OF this]
  moreover
  from \<open>l \<in> dom f\<close> \<open>dom f = dom f'\<close> have "l \<in> dom f'" by force
  with 
    par_beta_preserves_FV[OF \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close>]
    par_beta_preserves_FV[OF \<open>u \<Rightarrow>\<^sub>\<beta> u'\<close>] sp FV_option_lem[of f']
  have "s \<notin> FV (the (f' l))" and "p \<notin> FV (the (f' l))" and "s \<noteq> p" and "s \<notin> FV u'"
    by auto
  note ssubst_intro[OF this]
  ultimately
  show "the (f l)\<^bsup>[Obj f T, u]\<^esup> \<Rightarrow>\<^sub>\<beta> (the (f' l)\<^bsup>[Obj f' T, u']\<^esup>)" 
    by (simp add: openz_def closez_def)
qed

subsection \<open>Inclusions\<close>
text \<open>\<open>beta \<subseteq> par_beta \<subseteq> beta^*\<close> \medskip\<close>
lemma beta_subset_par_beta: "beta \<le> par_beta"
proof (clarify)
  define pred_cof
    where "pred_cof L t t' \<longleftrightarrow>
      (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> (\<exists>t''. (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t'' \<and> t' = \<sigma>[s,p] t''))"
    for L t t'

  fix t t' assume "t \<rightarrow>\<^sub>\<beta> t'" thus "t \<Rightarrow>\<^sub>\<beta> t'"
  proof 
    (induct
      taking: "\<lambda>t t'. body t \<and> body t' \<and> (\<exists>L. finite L \<and> pred_cof L t t')"
      rule: beta_induct)
    case CallL thus ?case by (simp add: par_beta_refl)
  next
    case CallR thus ?case by (simp add: par_beta_refl)
  next
    case beta thus ?case by (simp add: par_beta_refl)
  next
    case UpdL
    from 
      par_beta_lc[OF this(2)] this(2) 
      par_beta_body_refl[OF this(3)] this(3)
    show ?case by auto
  next
    case (UpdR t t' u l)
    from this(1) obtain L where
      "finite L" and "pred_cof L t t'" and "body t"
      by auto
    from 
      this(2) pbeta_Upd[OF par_beta_refl[OF \<open>lc u\<close>] \<open>lc u\<close> this(1) _ this(3)]
    show ?case
      unfolding pred_cof_def
      by auto
  next
    case (Upd l f T t)
    from par_beta_body_refl[OF \<open>body t\<close>]
    obtain L where
      "finite L" and 
      "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
        \<longrightarrow> (\<exists>t'. t\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t' \<and> t = \<sigma>[s,p] t')"
      by auto
    from 
      pbeta_Upd'[OF par_beta_refl[OF \<open>lc (Obj f T)\<close>] this
                    \<open>l \<in> dom f\<close> \<open>lc (Obj f T)\<close> \<open>body t\<close>]
    show ?case by assumption
  next
    case (Obj l f t t' T) note cof = this(2) and body = this(3)
    from cof obtain L where 
      "body t" and "finite L" and "pred_cof L t t'"
      by auto
    from body have "lc (Obj f T)" by (simp add: lc_obj)
    from 
      Obj_pbeta_subst[OF \<open>finite L\<close> _ par_beta_refl[OF this] this \<open>body t\<close>]
      \<open>pred_cof L t t'\<close>
    show ?case
      unfolding pred_cof_def
      by auto
  next
    case (Bnd L t t') note pred = this(2)
    from \<open>finite L\<close> exFresh_s_p_cof[of "L \<union> FV t"]
    obtain s p where 
      "s \<notin> L" and "p \<notin> L" and "s \<noteq> p" and
      "s \<notin> FV t" and "p \<notin> FV t"
      by auto
    with pred obtain t'' where 
      "t\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t''" and "t' = \<sigma>[s,p] t''"
      by blast
    from 
      par_beta_lc[OF this(1)] this(2) lc_body[OF _ \<open>s \<noteq> p\<close>]
    have "body \<sigma>[s,p](t\<^bsup>[Fvar s, Fvar p]\<^esup>)" and "body t'" by auto
    from this(1) sclose_sopen_eq_t[OF \<open>s \<notin> FV t\<close> \<open>p \<notin> FV t\<close> \<open>s \<noteq> p\<close>]
    have "body t" by (simp add: openz_def closez_def)
    with \<open>body t'\<close> \<open>finite L\<close> pred show ?case
      unfolding pred_cof_def
      by (simp, rule_tac x = L in exI, auto)
  qed
qed

lemma par_beta_subset_beta: "par_beta \<le> beta^**"
proof (rule predicate2I)
  define pred_cof
    where "pred_cof L t t' \<longleftrightarrow>
      (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> (\<exists>t''. (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<rightarrow>\<^sub>\<beta>\<^sup>* t'' \<and> t' = \<sigma>[s,p] t''))"
    for L t t'

  fix x y assume "x \<Rightarrow>\<^sub>\<beta> y" thus "x \<rightarrow>\<^sub>\<beta>\<^sup>* y"
  proof (induct 
      taking: "\<lambda>t t'. body t' \<and> (\<exists>L. finite L \<and> pred_cof L t t')"
      rule: pbeta_induct)
    case Fvar thus ?case by simp
  next
    case Call thus ?case by auto
  next
    case (Upd t t' l u u')
    from this(4) obtain L where
      "finite L" and "pred_cof L u u'" by auto
    from 
      this(2) 
      rtrancl_beta_Upd[OF \<open>t \<rightarrow>\<^sub>\<beta>\<^sup>* t'\<close> this(1) _ \<open>lc t\<close> \<open>body u\<close>]
    show ?case
      unfolding pred_cof_def
      by simp
  next
    case (Upd' f f' T t t' l)
    from this(3) obtain L where
      "body t'" and "finite L" and "pred_cof L t t'" by auto
    from 
      this(3)
      rtrancl_beta_Upd[OF \<open>Obj f T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj f' T\<close> \<open>finite L\<close> _
                          \<open>lc (Obj f T)\<close> \<open>body t\<close>]
    have rtranclp: "Upd (Obj f T) l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd (Obj f' T) l t'"
      unfolding pred_cof_def
      by simp

    from 
      Obj_pbeta[OF \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close>] \<open>l \<in> dom f\<close> 
      par_beta_lc[OF \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close>]
    have "l \<in> dom f'" and "lc (Obj f' T)" by auto
    from beta_Upd[OF this \<open>body t'\<close>] rtranclp
    show ?case by simp
  next
    case (Obj f f' T) note body = this(2) and pred = this(3)
    define pred_bnd
      where "pred_bnd s p b b' l \<longleftrightarrow> (\<exists>t''. the b\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t'' \<and> the b' = \<sigma>[s,p] t'')"
      for s p b b' and l::Label
    from 
      pred \<open>dom f' = dom f\<close> fmap_ex_cof2[of f' f pred_bnd]
    obtain L where
      "finite L" and 
      "\<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> pred_bnd s p (f l) (f' l) l"
      unfolding pred_cof_def pred_bnd_def
      by auto
    from 
      this(2)
      rtrancl_beta_obj_n[OF \<open>finite L\<close> _ sym[OF \<open>dom f' = dom f\<close>] body]
    show ?case
      unfolding pred_bnd_def
      by simp
  next
    case (beta f f' T l p p')
    note 
      rtrancl_beta_Call[OF \<open>Obj f T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj f' T\<close> \<open>lc (Obj f T)\<close> 
                           \<open>p \<rightarrow>\<^sub>\<beta>\<^sup>* p'\<close> \<open>lc p\<close>]
    moreover
    from 
      Obj_pbeta[OF \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close>] \<open>l \<in> dom f\<close> 
      par_beta_lc[OF \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close>]
      par_beta_lc[OF \<open>p \<Rightarrow>\<^sub>\<beta> p'\<close>]
    have "l \<in> dom f'" and "lc (Obj f' T)" and "lc p'" by auto
    note beta.beta[OF this]
    ultimately
    show ?case 
      by (auto simp: rtranclp.rtrancl_into_rtrancl[of _ _ "Call (Obj f' T) l p'"])
  next
    case (Bnd L t t') note pred = this(2)
    hence "pred_cof L t t'"
      unfolding pred_cof_def
      by blast
    moreover
    from pred \<open>finite L\<close> par_beta_body[of L t t']
    have "body t'" by blast
    ultimately
    show ?case
      using \<open>finite L\<close>
      by auto
  qed
qed

subsection \<open>Confluence (directly)\<close>

(***Main result: Confluence of beta relation for Sigma calculus              ***)
(*** by diamond property of parallel reduction and beta <= par_beta <= beta^* ***)
lemma diamond_binder:
  fixes L1 L2 t ta tb
  assumes 
  "finite L1"  and
  pred_L1: "\<forall>s p. s \<notin> L1 \<and> p \<notin> L1 \<and> s \<noteq> p
              \<longrightarrow> (\<exists>t'. (t\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t' 
                     \<and> (\<forall>z. (t\<^bsup>[Fvar s, Fvar  p]\<^esup> \<Rightarrow>\<^sub>\<beta> z) \<longrightarrow> (\<exists>u. t' \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u))) 
                     \<and> ta = \<sigma>[s,p]t')" and
  "finite L2" and
  pred_L2: "\<forall>s p. s \<notin> L2 \<and> p \<notin> L2 \<and> s \<noteq> p 
              \<longrightarrow> (\<exists>t'. t\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t' \<and> tb = \<sigma>[s,p]t')"
  shows
  "\<exists>L'. finite L' 
      \<and> (\<exists>t''. (\<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                  \<longrightarrow> (\<exists>u. ta\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> t'' = \<sigma>[s,p]u))
             \<and> (\<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                  \<longrightarrow> (\<exists>u. tb\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> t'' = \<sigma>[s,p]u)))"
proof -
  from \<open>finite L1\<close> \<open>finite L2\<close> have "finite (L1 \<union> L2)" by simp
  from exFresh_s_p_cof[OF this]
  obtain s p where sp: "s \<notin> L1 \<union> L2 \<and> p \<notin> L1 \<union> L2 \<and> s \<noteq> p" by auto
  with pred_L1
  obtain t' where 
    "t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'" and 
    "\<forall>z. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> z \<longrightarrow> (\<exists>u. t' \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u)" and
    "ta = \<sigma>[s,p] t'"
    by blast

  from sp pred_L2 obtain t'' where "t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t''" and "tb = \<sigma>[s,p] t''" 
    by blast
  from \<open>\<forall>z. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> z \<longrightarrow> (\<exists>u. t' \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u)\<close> this(1) 
  obtain u where "t' \<Rightarrow>\<^sub>\<beta> u" and "t'' \<Rightarrow>\<^sub>\<beta> u" by blast

  from \<open>finite L1\<close> \<open>finite L2\<close> have "finite (L1 \<union> L2 \<union> FV t \<union> {s} \<union> {p})" by simp
  moreover
  {
    fix x :: sterm and y :: sterm
    assume "t\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> y" and "x = \<sigma>[s,p] y" and "y \<Rightarrow>\<^sub>\<beta> u"
    hence 
      "\<forall>sa pa. sa \<notin> L1 \<union> L2 \<union> FV t \<union> {s} \<union> {p} 
             \<and> pa \<notin> L1 \<union> L2 \<union> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa 
        \<longrightarrow> (\<exists>t. x\<^bsup>[Fvar sa,Fvar pa]\<^esup> \<Rightarrow>\<^sub>\<beta> t \<and>  \<sigma>[s,p] u = \<sigma>[sa,pa] t)"
    proof (intro strip)
      fix sa :: fVariable and pa :: fVariable
      assume 
        sapa: "sa \<notin> L1 \<union> L2 \<union> FV t \<union> {s} \<union> {p} 
               \<and> pa \<notin> L1 \<union> L2 \<union> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa"
      with sp par_beta_lc[OF \<open>y \<Rightarrow>\<^sub>\<beta> u\<close>]
      have "s \<noteq> p" and "s \<notin> FV (Fvar pa)" and "lc y" and "lc u" by auto
      from 
        sopen_sclose_eq_ssubst[OF this(1-3)] 
        sopen_sclose_eq_ssubst[OF this(1-2) this(4)]
        renaming_par_beta \<open>x = \<sigma>[s,p] y\<close> \<open>y \<Rightarrow>\<^sub>\<beta> u\<close>
      have "x\<^bsup>[Fvar sa, Fvar pa]\<^esup> \<Rightarrow>\<^sub>\<beta> (\<sigma>[s,p] u\<^bsup>[Fvar sa, Fvar pa]\<^esup>)"
        by (auto simp: openz_def closez_def)
      
      moreover
      from 
        sapa par_beta_preserves_FV[OF \<open>t \<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> y\<close>]
        sopen_FV[of 0 "Fvar s" "Fvar p" t]
        par_beta_preserves_FV[OF \<open>y \<Rightarrow>\<^sub>\<beta> u\<close>]
        sclose_subset_FV[of 0 s p u]
      have "sa \<notin> FV (\<sigma>[s,p] u)" and "pa \<notin> FV (\<sigma>[s,p] u)" and "sa \<noteq> pa"
        by (auto simp: openz_def closez_def)
      from sym[OF sclose_sopen_eq_t[OF this]] 
      have "\<sigma>[s,p] u = \<sigma>[sa,pa] (\<sigma>[s,p] u\<^bsup>[Fvar sa, Fvar pa]\<^esup>)"
        by (simp add: openz_def closez_def)

      ultimately show "\<exists>t. x\<^bsup>[Fvar sa,Fvar pa]\<^esup> \<Rightarrow>\<^sub>\<beta> t \<and> \<sigma>[s,p] u = \<sigma>[sa,pa] t" 
        by blast
    qed
  }note 
      this[OF \<open>t \<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'\<close> \<open>ta = \<sigma>[s,p] t'\<close> \<open>t' \<Rightarrow>\<^sub>\<beta> u\<close>]
      this[OF \<open>t \<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t''\<close> \<open>tb = \<sigma>[s,p] t''\<close> \<open>t'' \<Rightarrow>\<^sub>\<beta> u\<close>]
  ultimately
  show 
    "\<exists>L'. finite L' 
        \<and> (\<exists>t''. (\<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                   \<longrightarrow> (\<exists>t'. ta\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t' \<and> t'' = \<sigma>[s,p] t'))
               \<and> (\<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                   \<longrightarrow> (\<exists>t'. tb\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t' \<and> t'' = \<sigma>[s,p] t')))"
    by (rule_tac x = "L1 \<union> L2 \<union> FV t \<union> {s} \<union> {p}" in exI, simp, blast)
qed

lemma exL_exMap_lem:
  fixes 
  f :: "Label -~> sterm" and 
  lz :: "Label -~> sterm" and f' :: "Label -~> sterm"
  assumes "dom f = dom lz" and "dom f' = dom f"
  shows 
  "\<forall>L1 L2. finite L1 
    \<longrightarrow> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L1 \<and> p \<notin> L1 \<and> s \<noteq> p 
                     \<longrightarrow> (\<exists>t. (the(f l)\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                            \<and> (\<forall>z. (the(f l)\<^bsup>[Fvar s, Fvar  p]\<^esup> \<Rightarrow>\<^sub>\<beta> z) 
                                \<longrightarrow> (\<exists>u. t \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u)))
                            \<and> the(f' l) = \<sigma>[s,p]t))
    \<longrightarrow> finite L2
    \<longrightarrow> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L2 \<and> p \<notin> L2 \<and> s \<noteq> p 
          \<longrightarrow> (\<exists>t. the(f l)\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t \<and> the(lz l) = \<sigma>[s,p]t))
    \<longrightarrow> (\<exists>L'. finite L' 
            \<and> (\<exists>lu. dom lu = dom f 
            \<and> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                           \<longrightarrow> (\<exists>t. (the(f' l)\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t 
                                  \<and> the(lu l) = \<sigma>[s,p]t))
            \<and> (\<forall>l\<in>dom f. body (the (f' l)))
            \<and> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                           \<longrightarrow> (\<exists>t. (the(lz l)\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t 
                                  \<and> the(lu l) = \<sigma>[s,p]t))
            \<and> (\<forall>l\<in>dom f. body (the (lz l)))))"
  using assms
proof (induct rule: fmap_induct3)
  case empty thus ?case by force
next 
  case (insert x a b c F1 F2 F3) thus ?case
  proof (intro strip)
    fix L1 :: "fVariable set" and L2 :: "fVariable set"
    {
      fix 
        L :: "fVariable set" and
        t :: sterm and F :: "Label -~> sterm" and
        P :: "sterm \<Rightarrow> sterm \<Rightarrow> fVariable \<Rightarrow> fVariable \<Rightarrow> bool"
      assume 
        "dom F1 = dom F" and
        *: "\<forall>l\<in>dom (F1(x \<mapsto> a)). 
           \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
            \<longrightarrow> P (the ((F1(x \<mapsto> a)) l)) (the ((F(x \<mapsto> t)) l)) s p"
      hence 
        F: "\<forall>l\<in>dom F1. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
             \<longrightarrow> P (the(F1 l)) (the(F l)) s p"
      proof (intro strip)
        fix l :: Label and s :: fVariable and p :: fVariable
        assume "l \<in> dom F1" hence "l \<in> dom (F1(x \<mapsto> a))" by simp
        moreover assume "s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p"
        ultimately
        have "P (the((F1(x \<mapsto> a)) l)) (the((F(x \<mapsto> t)) l)) s p"
          using * by blast
        moreover from \<open>x \<notin> dom F1\<close> \<open>l \<in> dom F1\<close> have "l \<noteq> x" by auto
        ultimately show "P (the(F1 l)) (the(F l)) s p" by force
      qed

      from * have "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P a t s p" by auto
      note this F
    }
    note pred = this
    note 
      tmp =
      pred[of _  L1 "(\<lambda>t t' s p. 
                        \<exists>t''. (t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t''
                            \<and> (\<forall>z. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> z \<longrightarrow> (\<exists>u. t'' \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u)))
                            \<and> t' = \<sigma>[s,p] t'')"]
    note predc = tmp(1) note predF3 = tmp(2)
    note tmp = pred[of _ L2 
                       "(\<lambda>t t' s p. \<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'' \<and> t' = \<sigma>[s,p] t'')"]
    note predb = tmp(1) note predF2 = tmp(2)

    assume 
      a: "\<forall>l\<in>dom (F1(x \<mapsto> a)). \<forall>s p. s \<notin> L1 \<and> p \<notin> L1 \<and> s \<noteq> p 
        \<longrightarrow> (\<exists>t. (the ((F1(x \<mapsto> a)) l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
               \<and> (\<forall>z. the ((F1(x \<mapsto> a)) l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> z 
                   \<longrightarrow> (\<exists>u. t \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u))) 
               \<and> the ((F3(x \<mapsto> c)) l) = \<sigma>[s,p] t)" and
      b: "\<forall>l\<in>dom (F1(x \<mapsto> a)). \<forall>s p. s \<notin> L2 \<and> p \<notin> L2 \<and> s \<noteq> p 
        \<longrightarrow> (\<exists>t. the ((F1(x \<mapsto> a)) l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
               \<and> the ((F2(x \<mapsto> b)) l) = \<sigma>[s,p] t)" and
      "finite L1" and "finite L2"
    from 
      diamond_binder[OF this(3) predc[OF sym[OF \<open>dom F3 = dom F1\<close>] this(1)]
                        this(4) predb[OF \<open>dom F1 = dom F2\<close> this(2)]]
    obtain La t where 
      "finite La" and
      pred_c: "\<forall>s p. s \<notin> La \<and> p \<notin> La \<and> s \<noteq> p 
                \<longrightarrow> (\<exists>u. c\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> t = \<sigma>[s,p] u)" and
      pred_b: "\<forall>s p. s \<notin> La \<and> p \<notin> La \<and> s \<noteq> p 
                \<longrightarrow> (\<exists>u. b\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> t = \<sigma>[s,p] u)"
      by blast
    {
      from this(1) have "finite (La \<union> FV c \<union> FV b)" by simp
      from exFresh_s_p_cof[OF this]
      obtain s p where 
        sp: "s \<notin> La \<union> FV c \<union> FV b \<and> p \<notin> La \<union> FV c \<union> FV b \<and> s \<noteq> p" 
        by auto
      with pred_c obtain u where "c\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u" by blast
      from par_beta_lc[OF this] have "lc (c\<^bsup>[Fvar s,Fvar p]\<^esup>)" by simp
      with lc_body[of "c\<^bsup>[Fvar s,Fvar p]\<^esup>" s p] sp sclose_sopen_eq_t[of s c p 0]
      have c: "body c" by (auto simp: closez_def openz_def)
          
      from sp pred_b obtain u where "b\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u" by blast      
      from par_beta_lc[OF this] have "lc (b\<^bsup>[Fvar s,Fvar p]\<^esup>)" by simp
      with lc_body[of "b\<^bsup>[Fvar s,Fvar p]\<^esup>" s p] sp sclose_sopen_eq_t[of s b p 0]
      have "body b" by (auto simp: closez_def openz_def)
      note c this
    }note bodycb = this
    from 
      predF3[OF sym[OF \<open>dom F3 = dom F1\<close>] a]
      predF2[OF \<open>dom F1 = dom F2\<close> b]
      \<open>finite L1\<close> \<open>finite L2\<close>
    have 
      "\<exists>L'. finite L' 
          \<and> (\<exists>lu. dom lu = dom F1 
          \<and> (\<forall>l\<in>dom F1. \<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                          \<longrightarrow> (\<exists>t. the (F3 l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                                 \<and> the (lu l) = \<sigma>[s,p] t)) 
          \<and> (\<forall>l\<in>dom F1. body (the (F3 l))) 
          \<and> (\<forall>l\<in>dom F1. \<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                          \<longrightarrow> (\<exists>t. the (F2 l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                                 \<and> the (lu l) = \<sigma>[s,p] t)) 
          \<and> (\<forall>l\<in>dom F1. body (the (F2 l))))"
      by (rule_tac x = L1 in allE[OF insert(1)], simp)
    then obtain Lb f where 
      "finite Lb" and "dom f = dom F1" and
      pred_F3: "\<forall>l\<in>dom F1. \<forall>s p. s \<notin> La \<union> Lb \<and> p \<notin> La \<union> Lb \<and> s \<noteq> p 
                             \<longrightarrow> (\<exists>t. the (F3 l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                                    \<and> the (f l) = \<sigma>[s,p] t)" and
      body_F3: "\<forall>l\<in>dom F1. body (the (F3 l))" and
      pred_F2: "\<forall>l\<in>dom F1. \<forall>s p. s \<notin> La \<union> Lb \<and> p \<notin> La \<union> Lb \<and> s \<noteq> p 
                             \<longrightarrow> (\<exists>t. the (F2 l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                                    \<and> the (f l) = \<sigma>[s,p] t)" and
      body_F2: "\<forall>l\<in>dom F1. body (the (F2 l))"
      by auto 
    from \<open>finite La\<close> \<open>finite Lb\<close> have "finite (La \<union> Lb)" by simp
    moreover
    from \<open>dom f = dom F1\<close> have "dom (f(x \<mapsto> t)) = dom (F1(x \<mapsto> a))" by simp
    moreover
    from pred_c pred_F3
    have 
      "\<forall>l\<in>dom (F1(x \<mapsto> a)). \<forall>s p. s \<notin> La \<union> Lb \<and> p \<notin> La \<union> Lb \<and> s \<noteq> p 
                              \<longrightarrow> (\<exists>t'. the ((F3(x \<mapsto> c)) l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t' 
                                      \<and> the ((f(x \<mapsto> t)) l) = \<sigma>[s,p] t')"
      by auto
    moreover
    from bodycb(1) body_F3 
    have "\<forall>l\<in>dom (F1(x \<mapsto> a)). body (the ((F3(x \<mapsto> c)) l))"
      by simp
    moreover
    from pred_b pred_F2
    have 
      "\<forall>l\<in>dom (F1(x \<mapsto> a)). \<forall>s p. s \<notin> La \<union> Lb \<and> p \<notin> La \<union> Lb \<and> s \<noteq> p 
                              \<longrightarrow> (\<exists>t'. the ((F2(x \<mapsto> b)) l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t' 
                                      \<and> the ((f(x \<mapsto> t)) l) = \<sigma>[s,p] t')"
      by auto
    moreover
    from bodycb(2) body_F2 
    have "\<forall>l\<in>dom (F1(x \<mapsto> a)). body (the ((F2(x \<mapsto> b)) l))"
      by simp
    ultimately
    show 
      "\<exists>L'. finite L'
          \<and> (\<exists>lu. dom lu = dom (F1(x \<mapsto> a)) 
                \<and> (\<forall>l\<in>dom (F1(x \<mapsto> a)). 
                    \<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                     \<longrightarrow> (\<exists>t'. the ((F3(x \<mapsto> c)) l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'
                             \<and> the (lu l) = \<sigma>[s,p] t'))
                \<and> (\<forall>l\<in>dom (F1(x \<mapsto> a)). body (the ((F3(x \<mapsto> c)) l))) 
                \<and> (\<forall>l\<in>dom (F1(x \<mapsto> a)). 
                    \<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                     \<longrightarrow> (\<exists>t'. the ((F2(x \<mapsto> b)) l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t'
                \<and> the (lu l) = \<sigma>[s,p] t'))
                \<and> (\<forall>l\<in>dom (F1(x \<mapsto> a)). body (the ((F2(x \<mapsto> b)) l))))"
      by (rule_tac x = "La \<union> Lb" in exI, 
        simp (no_asm_simp) only: conjI simp_thms(22),
        rule_tac x = "(f(x \<mapsto> t))" in exI, simp)
  qed
qed

lemma exL_exMap:
  "\<lbrakk> dom (f::Label -~> sterm) = dom (lz::Label -~> sterm); 
     dom (f'::Label -~> sterm) = dom f; 
     finite L1;
     \<forall>l\<in>dom f. \<forall>s p. s \<notin> L1 \<and> p \<notin> L1 \<and> s \<noteq> p 
      \<longrightarrow> (\<exists>t. (the(f l)\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
             \<and> (\<forall>z. (the(f l)\<^bsup>[Fvar s, Fvar  p]\<^esup> \<Rightarrow>\<^sub>\<beta> z) \<longrightarrow> (\<exists>u. t \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u)))
             \<and> the(f' l) = \<sigma>[s,p]t);
     finite L2;
     \<forall>l\<in>dom lz. \<forall>s p. s \<notin> L2 \<and> p \<notin> L2 \<and> s \<noteq> p 
      \<longrightarrow> (\<exists>t. the(f l)\<^bsup>[Fvar s, Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t \<and> the(lz l) = \<sigma>[s,p]t) \<rbrakk>
  \<Longrightarrow> \<exists>L'. finite L' 
         \<and> (\<exists>lu. dom lu = dom f 
               \<and> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                              \<longrightarrow> (\<exists>t. (the(f' l)\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t 
                                     \<and> the(lu l) = \<sigma>[s,p]t))
               \<and> (\<forall>l\<in>dom f. body (the (f' l)))
               \<and> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
                              \<longrightarrow> (\<exists>t. (the(lz l)\<^bsup>[Fvar s, Fvar p]\<^esup>) \<Rightarrow>\<^sub>\<beta> t 
                                     \<and> the(lu l) = \<sigma>[s,p]t))
               \<and> (\<forall>l\<in>dom f. body (the (lz l))))"
  using exL_exMap_lem[of f lz f'] by simp

lemma diamond_par_beta: "diamond par_beta"
  unfolding diamond_def commute_def square_def
proof (rule impI [THEN allI [THEN allI]])
  fix x y assume "x \<Rightarrow>\<^sub>\<beta> y" 
  thus "\<forall>z. x \<Rightarrow>\<^sub>\<beta> z \<longrightarrow> (\<exists>u. y \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u)"
  proof (induct rule: par_beta.induct)
    case pbeta_Fvar thus ?case by simp
  next
    case (pbeta_Upd t t' L u u' l) 
    note pred_t = this(2) and pred_u = this(5)
    show ?case
    proof (intro strip)
      fix z assume "Upd t l u \<Rightarrow>\<^sub>\<beta> z"
      thus "\<exists>u. Upd t' l u' \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u"
      proof (induct rule: Upd_par_red)
          (* Upd: case Upd
             Upd t' l u' \<Rightarrow>\<^sub>\<beta> Upd tb l ub \<and> Upd ta l ua \<Rightarrow>\<^sub>\<beta> Upd tb l ub *)
        case (upd ta ua La)
        from 
          diamond_binder[OF \<open>finite L\<close> pred_u this(2-3)]
          this(1) pred_t
          par_beta_lc[OF this(1)] par_beta_lc[OF \<open>t \<Rightarrow>\<^sub>\<beta> t'\<close>]
        obtain L' ub tb where 
          "t' \<Rightarrow>\<^sub>\<beta> tb" and "lc t'" and "ta \<Rightarrow>\<^sub>\<beta> tb" and 
          "lc ta" and "finite L'" and
          "\<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
            \<longrightarrow> (\<exists>u. u'\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> ub = \<sigma>[s,p] u)" and
          "\<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p 
            \<longrightarrow> (\<exists>u. ua\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> ub = \<sigma>[s,p] u)"
          by auto
        from 
          par_beta.pbeta_Upd[OF this(1-2) this(5-6)]
          par_beta.pbeta_Upd[OF this(3-5) this(7)]
          par_beta_body[OF this(5-6)]
          par_beta_body[OF this(5) this(7)] \<open>z = Upd ta l ua\<close>
        show ?case by (force simp: exI[of _ "Upd tb l ub"])
      next
        case (obj f fa T ua La)
          (* Upd: case Obj
             Upd (Obj f' T) l u' \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> ub)) T 
           \<and> Obj (fa(l \<mapsto> ua)) T \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> ub)) T *)
        from diamond_binder[OF \<open>finite L\<close> pred_u this(4-5)]
        obtain Lb ub where
          "finite Lb" and
          ub1: "\<forall>s p. s \<notin> Lb \<and> p \<notin> Lb \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>u. ua\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> ub = \<sigma>[s,p] u)" and
          ub2: "\<forall>s p. s \<notin> Lb \<and> p \<notin> Lb \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>u. u'\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> ub = \<sigma>[s,p] u)"
          by auto
        from \<open>Obj f T = t\<close> \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T\<close>
        have "t \<Rightarrow>\<^sub>\<beta> Obj fa T" by simp
        with pred_t obtain a where "t' \<Rightarrow>\<^sub>\<beta> a" "Obj fa T \<Rightarrow>\<^sub>\<beta> a"
          by auto
        with 
          par_beta_lc[OF this(2)] 
          par_beta_body[OF \<open>finite Lb\<close> ub1]
        obtain fb where
          "t' \<Rightarrow>\<^sub>\<beta> Obj fb T" and "Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T" and
          "lc (Obj fa T)" and "body ua"
          by auto
        from Obj_pbeta_subst[OF \<open>finite Lb\<close> ub1 this(2-4)] 
        have "Obj (fa(l \<mapsto> ua)) T \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> ub)) T" by assumption
        moreover
        from 
          \<open>t \<Rightarrow>\<^sub>\<beta> t'\<close> \<open>Obj f T = t\<close>
          par_beta_lc[OF \<open>t \<Rightarrow>\<^sub>\<beta> t'\<close>] \<open>t' \<Rightarrow>\<^sub>\<beta> Obj fb T\<close>
          par_beta_body[OF \<open>finite Lb\<close> ub2]
        obtain f' where 
          "t' = Obj f' T" and "Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T" and 
          "lc (Obj f' T)" and "body u'"
          by auto
        note par_beta.pbeta_Upd'[OF this(2) \<open>finite Lb\<close> ub2 _ this(3-4)]
        moreover
        from 
          \<open>t \<Rightarrow>\<^sub>\<beta> t'\<close> \<open>Obj f T = t\<close> \<open>t' = Obj f' T\<close>
          \<open>l \<in> dom f\<close> Obj_pbeta[of f T f']
        have "l \<in> dom f'" by simp
        ultimately
        show ?case
          using \<open>z = Obj (fa(l \<mapsto> ua)) T\<close> \<open>t' = Obj f' T\<close>
          by (rule_tac x = "Obj (fb(l \<mapsto> ub)) T" in exI, simp)
      qed
    qed
  next
    case (pbeta_Obj f' f L T) note pred = this(3)
    show ?case
    proof (clarify)
        (* Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T \<and> Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T *)
      fix fa La
      assume 
        "dom fa = dom f" and "finite La" and
        "\<forall>l\<in>dom f. \<forall>s p. s \<notin> La \<and> p \<notin> La \<and> s \<noteq> p
                     \<longrightarrow> (\<exists>t. the (f l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                            \<and> the (fa l) = \<sigma>[s,p] t)"
      from 
        exL_exMap[OF sym[OF this(1)] \<open>dom f' = dom f\<close> 
                     \<open>finite L\<close> pred this(2)]
        this(1) this(3) \<open>dom f' = dom f\<close>
      obtain Lb fb where 
        "dom fb = dom f'" and "dom fb = dom fa" and "finite Lb" and
        "\<forall>l\<in>dom f'. \<forall>s p. s \<notin> Lb \<and> p \<notin> Lb \<and> s \<noteq> p 
                      \<longrightarrow> (\<exists>t. the (f' l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                             \<and> the (fb l) = \<sigma>[s,p] t)" and
        "\<forall>l\<in>dom f'. body (the (f' l))" and
        "\<forall>l\<in>dom fa. \<forall>s p. s \<notin> Lb \<and> p \<notin> Lb \<and> s \<noteq> p 
                      \<longrightarrow> (\<exists>t. the (fa l)\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> t 
                             \<and> the (fb l) = \<sigma>[s,p] t)" and
        "\<forall>l\<in>dom fa. body (the (fa l))"
        by auto
      from 
        par_beta.pbeta_Obj[OF this(1) this(3-5)]
        par_beta.pbeta_Obj[OF this(2) this(3) this(6-7)]
      show "\<exists>u. Obj f' T \<Rightarrow>\<^sub>\<beta> u \<and> Obj fa T \<Rightarrow>\<^sub>\<beta> u"
        by (rule_tac x = "Obj fb T" in exI, simp)
    qed
  next
    case (pbeta_Upd' f T f' L t t' l) 
    note pred_obj = this(2) and pred_bnd = this(4)
    show ?case
    proof (clarify)
      fix z assume "Upd (Obj f T) l t \<Rightarrow>\<^sub>\<beta> z"
      thus "\<exists>u. Obj (f'(l \<mapsto> t')) T \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u"
      proof (induct rule: Upd_par_red)
          (* Upd': case Upd 
             Obj (f'(l \<mapsto> t')) T \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> tb)) T 
           \<and> Upd (Obj fa T) l ta \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> tb)) T *)
        case (upd a ta La) note pred_ta = this(3)
        from \<open>Obj f T \<Rightarrow>\<^sub>\<beta> a\<close> \<open>z = Upd a l ta\<close>
        obtain fa where 
          "Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T" and "z = Upd (Obj fa T) l ta"
          by auto
        from this(1) pred_obj
        obtain b where "Obj f' T \<Rightarrow>\<^sub>\<beta> b" and "Obj fa T \<Rightarrow>\<^sub>\<beta> b"
          by (elim allE impE exE conjE, simp)
        with 
          par_beta_lc[OF this(1)] par_beta_lc[OF this(2)]
        obtain fb where 
          "Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T" and "lc (Obj f' T)" and
          "Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T" and "lc (Obj fa T)"
          by auto
        from diamond_binder[OF \<open>finite L\<close> pbeta_Upd'(4) \<open>finite La\<close> pred_ta]
        obtain Lb tb where 
          "finite Lb" and
          cb1: "\<forall>s p. s \<notin> Lb \<and> p \<notin> Lb \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>u. t'\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> tb = \<sigma>[s,p] u)" and
          cb2: "\<forall>s p. s \<notin> Lb \<and> p \<notin> Lb \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>u. ta\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> tb = \<sigma>[s,p] u)"
          by auto
        from 
          par_beta_body[OF this(1-2)] 
          Obj_pbeta_subst[OF \<open>finite Lb\<close> cb1 \<open>Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T\<close>
                             \<open>lc (Obj f' T)\<close>]
        have "Obj (f'(l \<mapsto> t')) T \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> tb)) T" 
          by simp
        moreover
        from Obj_pbeta[OF \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T\<close>] \<open>l \<in> dom f\<close>
        have "l \<in> dom fa" by simp
        from 
          par_beta_body[OF \<open>finite Lb\<close> cb2]
          par_beta.pbeta_Upd'[OF \<open>Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T\<close> \<open>finite Lb\<close> 
                                 cb2 this \<open>lc (Obj fa T)\<close>]
        have "Upd (Obj fa T) l ta \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> tb)) T" by simp
        ultimately
        show ?case
          using \<open>z = Upd (Obj fa T) l ta\<close>
          by (rule_tac x = "Obj (fb(l \<mapsto> tb)) T" in exI, simp)
      next
          (* Upd': case Obj 
             Obj (f'(l \<mapsto> t')) T \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> tb)) T 
           \<and> Obj (fa(l \<mapsto> ta)) T \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> tb)) T *)
        case (obj f'' fa T' ta La) 
        note pred_ta = this(5) and this
        hence 
          "l \<in> dom f" and "Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T" and
          "z = Obj (fa(l \<mapsto> ta)) T"
          by auto
        from diamond_binder[OF \<open>finite L\<close> pred_bnd \<open>finite La\<close> pred_ta]
        obtain Lb tb where
          "finite Lb" and
          tb1: "\<forall>s p. s \<notin> Lb \<and> p \<notin> Lb \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>u. t'\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> tb = \<sigma>[s,p] u)" and
          tb2: "\<forall>s p. s \<notin> Lb \<and> p \<notin> Lb \<and> s \<noteq> p 
                 \<longrightarrow> (\<exists>u. ta\<^bsup>[Fvar s,Fvar p]\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> tb = \<sigma>[s,p] u)"
          by auto
        from \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T\<close> pred_obj
        obtain b where "Obj f' T \<Rightarrow>\<^sub>\<beta> b" and "Obj fa T \<Rightarrow>\<^sub>\<beta> b"
          by (elim allE impE exE conjE, simp)
        with par_beta_lc[OF this(1)] par_beta_lc[OF this(2)]
        obtain fb where 
          "Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T" "lc (Obj f' T)" and
          "Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T" "lc (Obj fa T)"
          by auto
        from 
          par_beta_body[OF \<open>finite Lb\<close> tb1] 
          Obj_pbeta_subst[OF \<open>finite Lb\<close> tb1 this(1-2)]
          par_beta_body[OF \<open>finite Lb\<close> tb2] 
          Obj_pbeta_subst[OF \<open>finite Lb\<close> tb2 this(3-4)]
        have 
          "Obj (f'(l \<mapsto> t')) T \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> tb)) T" and
          "Obj (fa(l \<mapsto> ta)) T \<Rightarrow>\<^sub>\<beta> Obj (fb(l \<mapsto> tb)) T" 
          by simp+
        with \<open>z = Obj (fa(l \<mapsto> ta)) T\<close> show ?case
          by (rule_tac x = "Obj (fb(l \<mapsto> tb)) T" in exI, simp)
      qed
    qed
  next
    case (pbeta_Call t t' u u' l) 
    note pred_t = this(2) and pred_u = this(4)
    show ?case
    proof (intro strip)
      fix z assume "Call t l u \<Rightarrow>\<^sub>\<beta> z"
      thus "\<exists>u. Call t' l u' \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u"
      proof (induct rule: Call_par_red)
          (* Call: case Call 
             Call t' l u' \<Rightarrow>\<^sub>\<beta> Call tb l ub \<and> Call t' l u' \<Rightarrow>\<^sub>\<beta> Call tb l ub *)
        case (call ta ua)
        from 
          this(1-2) pred_t pred_u
        obtain tb ub where "t' \<Rightarrow>\<^sub>\<beta> tb" "u' \<Rightarrow>\<^sub>\<beta> ub" "ta \<Rightarrow>\<^sub>\<beta> tb" "ua \<Rightarrow>\<^sub>\<beta> ub"
          by (elim allE impE exE conjE, simp)
        from 
          par_beta_lc[OF this(1)] par_beta_lc[OF this(2)]
          par_beta.pbeta_Call[OF this(1-2)]
          par_beta_lc[OF this(3)] par_beta_lc[OF this(4)] 
          par_beta.pbeta_Call[OF this(3-4)]
          \<open>z = Call ta l ua\<close>
        show ?case
          by (rule_tac x = "Call tb l ub" in exI, simp)
      next
          (* Call: case beta 
             Call (Obj f' T) l u' \<Rightarrow>\<^sub>\<beta> (the (fb l)\<^bsup>[Obj fb T,ub]\<^esup>)
           \<and> the (fa l)\<^bsup>[Obj fa T,ua]\<^esup> \<Rightarrow>\<^sub>\<beta> (the (fb l)\<^bsup>[Obj fb T,ub]\<^esup>) *)
        case (beta f fa T ua) 
        from this(1-2) have "t \<Rightarrow>\<^sub>\<beta> Obj fa T" by simp
        with \<open>u \<Rightarrow>\<^sub>\<beta> ua\<close> pred_t pred_u
        obtain b ub where 
          "t' \<Rightarrow>\<^sub>\<beta> b" and "Obj fa T \<Rightarrow>\<^sub>\<beta> b" and "u' \<Rightarrow>\<^sub>\<beta> ub" and "ua \<Rightarrow>\<^sub>\<beta> ub"
          by (elim allE impE exE conjE, simp)
        from this(1-2) par_beta_lc[OF this(2)]
        obtain fb where 
          "t' \<Rightarrow>\<^sub>\<beta> Obj fb T" and 
          "Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T" and "lc (Obj fa T)"
          by auto
        from 
          par_beta_beta[OF \<open>l \<in> dom fa\<close> this(2) \<open>ua \<Rightarrow>\<^sub>\<beta> ub\<close> this(3)]
          par_beta_lc[OF \<open>ua \<Rightarrow>\<^sub>\<beta> ub\<close>]
        have "the (fa l)\<^bsup>[Obj fa T,ua]\<^esup> \<Rightarrow>\<^sub>\<beta> (the (fb l)\<^bsup>[Obj fb T,ub]\<^esup>)" by simp
        moreover
        from \<open>l \<in> dom fa\<close> Obj_pbeta[OF \<open>Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T\<close>]
        have "l \<in> dom fb" by simp
        from 
          \<open>t \<Rightarrow>\<^sub>\<beta> t'\<close> sym[OF \<open>Obj f T = t\<close>]
          par_beta_lc[OF \<open>t \<Rightarrow>\<^sub>\<beta> t'\<close>] \<open>t' \<Rightarrow>\<^sub>\<beta> Obj fb T\<close>
        obtain f' where 
          "t' = Obj f' T" and "Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T" and
          "lc (Obj f' T)"
          by auto
        from 
          Obj_pbeta[OF this(2)] \<open>l \<in> dom fb\<close>
          par_beta.pbeta_beta[OF this(2) _ \<open>u' \<Rightarrow>\<^sub>\<beta> ub\<close> this(3)]
          par_beta_lc[OF \<open>u' \<Rightarrow>\<^sub>\<beta> ub\<close>]
        have "Call (Obj f' T) l u' \<Rightarrow>\<^sub>\<beta> (the (fb l)\<^bsup>[Obj fb T,ub]\<^esup>)" by auto
        ultimately
        show ?case
          using \<open>t' = Obj f' T\<close> \<open>z = (the (fa l)\<^bsup>[Obj fa T,ua]\<^esup>)\<close>
          by (rule_tac x = "(the (fb l)\<^bsup>[Obj fb T,ub]\<^esup>)" in exI, simp)
      qed
    qed
  next
    case (pbeta_beta f T f' l p p') 
    note pred_obj = this(2) and pred_p = this(5)
    show ?case
    proof (intro strip)
      fix z assume "Call (Obj f T) l p \<Rightarrow>\<^sub>\<beta> z"
      thus "\<exists>u. the (f' l)\<^bsup>[Obj f' T,p']\<^esup> \<Rightarrow>\<^sub>\<beta> u \<and> z \<Rightarrow>\<^sub>\<beta> u"
      proof (induct rule: Call_par_red)
          (* beta: case Call 
             Call (Obj fa T) l pa \<Rightarrow>\<^sub>\<beta> (the (fb l)\<^bsup>[Obj fb T,pb]\<^esup>) 
           \<and> the (f' l)\<^bsup>[Obj f' T,p']\<^esup> \<Rightarrow>\<^sub>\<beta> (the (fb l)\<^bsup>[Obj fb T,pb]\<^esup>) *)
        case (call a pa)
        then obtain fa where 
          "Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T" and "z = Call (Obj fa T) l pa"
          by auto
        from 
          this(1) \<open>p \<Rightarrow>\<^sub>\<beta> pa\<close> pred_obj pred_p
        obtain b pb where 
          "Obj f' T \<Rightarrow>\<^sub>\<beta> b" and "Obj fa T \<Rightarrow>\<^sub>\<beta> b" and 
          "p' \<Rightarrow>\<^sub>\<beta> pb" and "pa \<Rightarrow>\<^sub>\<beta> pb"
          by (elim allE impE exE conjE, simp)
        with par_beta_lc[OF this(1)] par_beta_lc[OF this(2)]
        obtain fb where 
          "Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T" and "lc (Obj f' T)" and
          "Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T" and "lc (Obj fa T)"
          by auto
        from this(1) \<open>l \<in> dom f\<close> \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close> \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T\<close>
        have "l \<in> dom f'" and "l \<in> dom fa" by auto
        from \<open>p' \<Rightarrow>\<^sub>\<beta> pb\<close> \<open>pa \<Rightarrow>\<^sub>\<beta> pb\<close> par_beta_lc
        have "p' \<Rightarrow>\<^sub>\<beta> pb" and "lc p'" and "pa \<Rightarrow>\<^sub>\<beta> pb" and "lc pa" by auto
        from 
          par_beta.pbeta_beta[OF \<open>Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T\<close> \<open>l \<in> dom fa\<close>
                                  this(3) \<open>lc (Obj fa T)\<close> this(4)] 
          par_beta_beta[OF \<open>l \<in> dom f'\<close> \<open>Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T\<close>
                            this(1) \<open>lc (Obj f' T)\<close> this(2)]
          \<open>z = Call (Obj fa T) l pa\<close>
        show ?case
          by (rule_tac x = "(the (fb l)\<^bsup>[Obj fb T,pb]\<^esup>)" in exI, simp)
      next
          (* beta: case beta 
             the (f' l)\<^bsup>[Obj f' T,p']\<^esup> \<Rightarrow>\<^sub>\<beta> (the (fb l)\<^bsup>[Obj fb T,pb]\<^esup>)
          \<and>  the (fa l)\<^bsup>[Obj fa T,pa]\<^esup> \<Rightarrow>\<^sub>\<beta> (the (fb l)\<^bsup>[Obj fb T,pb]\<^esup>) *)
        case (beta f'' fa Ta pa)
        hence "Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T" and "z = (the (fa l)\<^bsup>[Obj fa T,pa]\<^esup>)"
          by auto
        with \<open>p \<Rightarrow>\<^sub>\<beta> pa\<close> pred_obj pred_p
        obtain b pb where 
          "Obj f' T \<Rightarrow>\<^sub>\<beta> b" and "Obj fa T \<Rightarrow>\<^sub>\<beta> b" and
          "p' \<Rightarrow>\<^sub>\<beta> pb" and "pa \<Rightarrow>\<^sub>\<beta> pb"
          by (elim allE impE exE conjE, simp)
        with par_beta_lc
        obtain fb where 
          "Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T" and "lc (Obj f' T)" and "lc p'" and
          "Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T" and "lc (Obj fa T)" and "lc pa"
          by auto
        from \<open>l \<in> dom f\<close> \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj f' T\<close> \<open>Obj f T \<Rightarrow>\<^sub>\<beta> Obj fa T\<close>
        have "l \<in> dom f'" and "l \<in> dom fa" by auto
        from
          par_beta_beta[OF \<open>l \<in> dom f'\<close> \<open>Obj f' T \<Rightarrow>\<^sub>\<beta> Obj fb T\<close> 
                           \<open>p' \<Rightarrow>\<^sub>\<beta> pb\<close> \<open>lc (Obj f' T)\<close> \<open>lc p'\<close>]
          par_beta_beta[OF \<open>l \<in> dom fa\<close> \<open>Obj fa T \<Rightarrow>\<^sub>\<beta> Obj fb T\<close> 
                           \<open>pa \<Rightarrow>\<^sub>\<beta> pb\<close> \<open>lc (Obj fa T)\<close> \<open>lc pa\<close>]
          \<open>z = (the (fa l)\<^bsup>[Obj fa T,pa]\<^esup>)\<close>
        show ?case
          by (rule_tac x = "(the (fb l)\<^bsup>[Obj fb T,pb]\<^esup>)" in exI, simp)
      qed
    qed
  qed
qed

subsection \<open>Confluence (classical not via complete developments)\<close>

theorem beta_confluent: "confluent beta"
  by (rule diamond_par_beta diamond_to_confluence
      par_beta_subset_beta beta_subset_par_beta)+

end
