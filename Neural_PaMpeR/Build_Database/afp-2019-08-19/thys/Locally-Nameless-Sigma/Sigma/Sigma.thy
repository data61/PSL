section \<open>Locally Nameless representation of basic Sigma calculus enriched with formal parameter\<close>

theory Sigma
imports "../preliminary/FMap"
begin

subsection \<open>Infrastructure for the finite maps\<close>

axiomatization max_label :: nat where
  LabelAvail: "max_label > 10"

definition "Label = {n :: nat. n \<le> max_label}"

typedef Label = Label
  unfolding Label_def by auto

lemmas finite_Label_set = Finite_Set.finite_Collect_le_nat[of max_label]

lemma Univ_abs_label: 
  "(UNIV :: (Label set)) = Abs_Label ` {n :: nat. n \<le> max_label}"
proof -
  have "\<forall>x :: Label. x : Abs_Label ` {n :: nat. n \<le> max_label}"
  proof
    fix x :: Label
    have "Rep_Label x \<in> {n. n \<le> max_label}"
      by (fold Label_def, rule Rep_Label)
    hence "Abs_Label (Rep_Label x) \<in> Abs_Label ` {n. n \<le> max_label}"
      by (rule imageI)
    thus "x \<in> Abs_Label ` {n. n \<le> max_label}"
      by (simp add: Rep_Label_inverse)
  qed
  thus ?thesis by force
qed

lemma finite_Label: "finite (UNIV :: (Label set))"
  by (simp add: Univ_abs_label finite_Label_set)

instance Label :: finite
proof
  show "finite (UNIV :: (Label set))" by (rule finite_Label)
qed

consts
Lsuc :: "(Label set) \<Rightarrow> Label \<Rightarrow> Label"
Lmin :: "(Label set) \<Rightarrow> Label"
Lmax :: "(Label set) \<Rightarrow> Label"

definition Llt :: "[Label, Label] \<Rightarrow> bool" (infixl "<" 50) where
  "Llt a b == Rep_Label a < Rep_Label b"
definition Lle :: "[Label, Label] \<Rightarrow> bool" (infixl "\<le>" 50) where
  "Lle a b == Rep_Label a \<le> Rep_Label b"

definition Ltake_eq :: "[Label set, (Label \<rightharpoonup> 'a),  (Label \<rightharpoonup> 'a)] \<Rightarrow> bool"
where  "Ltake_eq L f g  == \<forall>l\<in>L. f l = g l"

lemma Ltake_eq_all:
  fixes f g
  assumes "dom f = dom g" and "Ltake_eq (dom f) f g"
  shows "f = g"
proof
  fix x from assms show "f x = g x" 
    unfolding Ltake_eq_def
    by (cases "x \<in> dom f", auto)
qed

lemma Ltake_eq_dom: 
  fixes L :: "Label set" and f :: "Label -~> 'a"
  assumes "L \<subseteq> dom f" and "card L = card (dom f)"
  shows "L = (dom f)"
proof (auto)
  fix x :: Label assume "x \<in> L"
  with in_mono[OF assms(1)] show "\<exists>y. f x = Some y" by blast
next
  fix x y assume "f x = Some y"
  from card_seteq[OF finite_dom_fmap[of f] \<open>L \<subseteq> dom f\<close>] \<open>card L = card (dom f)\<close>
  have "L = dom f" by simp
  with \<open>f x = Some y\<close> show "x \<in> L" by force
qed

subsection \<open>Object-terms in Locally Nameless representation notation, beta-reduction and substitution\<close>

datatype type = Object "Label -~> (type \<times> type)"

datatype bVariable = Self nat | Param nat
type_synonym fVariable = string
(* each binder introduces 2 variables: self and parameter *)
(* thus to each deBruijn index (nat) correspond 2 variables of the same depth *)

subsubsection \<open>Enriched Sigma datatype of objects\<close>
datatype sterm =
  Bvar bVariable             (* bound variable -- as deBruijn index *)
| Fvar fVariable             (* free variable *)
| Obj "Label -~> sterm" type (* An object maps labels to terms and has a type *)
| Call sterm Label sterm     (* Call a l b calls method l on object a with param b *)
| Upd sterm Label sterm      (* Upd a l b updates method l of object a with body b *)

datatype_compat sterm

primrec applyPropOnOption:: "(sterm \<Rightarrow> bool) \<Rightarrow> sterm option \<Rightarrow> bool" where
f1:  "applyPropOnOption P None  = True" |
f2:  "applyPropOnOption P (Some t) = P t"

lemma sterm_induct[case_names Bvar Fvar Obj Call Upd empty insert]:
  fixes 
  t :: sterm and P1 :: "sterm \<Rightarrow> bool" and 
  f :: "Label -~> sterm" and P3 :: "(Label -~> sterm) \<Rightarrow> bool"
  assumes 
  "\<And>b. P1 (Bvar b)" and
  "\<And>x. P1 (Fvar x)" and
   a_obj: "\<And>f T. P3 f \<Longrightarrow> P1 (Obj f T)" and
  "\<And>t1 l t2. \<lbrakk> P1 t1; P1 t2 \<rbrakk> \<Longrightarrow> P1 (Call t1 l t2)" and
  "\<And>t1 l t2. \<lbrakk> P1 t1; P1 t2 \<rbrakk> \<Longrightarrow> P1 (Upd t1 l t2)" and
  "P3 Map.empty" and
  a_f: "\<And>t1 f l . \<lbrakk> l \<notin> dom f; P1 t1; P3 f \<rbrakk> \<Longrightarrow> (P3 (f(l \<mapsto> t1)))"
  shows "P1 t \<and> P3 f"
proof -
  have "\<forall>t (f::Label -~> sterm) l.  P1 t \<and> (applyPropOnOption P1) (f l)"
  proof (intro strip)
    fix t :: sterm and f' :: "Label -~> sterm" and l :: Label
    define foobar where "foobar = f' l" 
    from assms show "P1 t \<and> applyPropOnOption P1 foobar"
    proof (induct_tac t and foobar rule: compat_sterm.induct compat_sterm_option.induct, auto)
      fix f :: "Label -~> sterm" and T :: type
      assume "\<And>x. applyPropOnOption P1 (f x)"
      with a_f \<open>P3 Map.empty\<close> have "P3 f"
      proof (induct f rule: fmap_induct, simp)
        case (insert F x z)
        note 
          P1F'   = \<open>\<And>xa. applyPropOnOption P1 ((F(x \<mapsto> z)) xa)\<close> and
          predP3 = \<open>\<lbrakk> \<And>l f t1. \<lbrakk>l \<notin> dom f; P1 t1; P3 f\<rbrakk> \<Longrightarrow> P3 (f(l \<mapsto> t1)); 
                      P3 Map.empty; \<And>x. applyPropOnOption P1 (F x)\<rbrakk>
                    \<Longrightarrow> P3 F\<close> and
          P3F'   = \<open>\<And>l f t f. \<lbrakk> l \<notin> dom f; P1 t; P3 f \<rbrakk> \<Longrightarrow> P3 (f(l \<mapsto> t))\<close>
        have "\<And>xa. applyPropOnOption P1 (F xa)"
        proof -
          fix xa :: Label show "applyPropOnOption P1 (F xa)"
          proof (cases "xa = x")
            case True with P1F' \<open>x \<notin> dom F\<close> have "F xa = None" by force
            thus ?thesis by simp
          next
            case False hence eq: "F xa = (F(x \<mapsto> z)) xa" by auto
            from P1F'[of xa] show "applyPropOnOption P1 (F xa)" 
              by (simp only: ssubst[OF eq])
          qed
        qed
        from a_f predP3[OF _ \<open>P3 Map.empty\<close> this] have P3F: "P3 F" by simp
        from P1F'[of x]
        have "applyPropOnOption P1 (Some z)" by auto
        hence "P1 z" by simp
        from a_f[OF \<open>x \<notin> dom F\<close> this P3F] show ?case by assumption
      qed
      with a_obj show "P1 (Obj f T)" by simp
    qed
  qed
  with assms show ?thesis
  proof (auto)
    assume "\<And>l f t1. \<lbrakk>l \<notin> dom f; P3 f\<rbrakk> \<Longrightarrow> P3 (f(l \<mapsto> t1))"
    with \<open>P3 Map.empty\<close> show "P3 f" by (rule fmap_induct)
  qed
qed

lemma ball_tsp_P3:
  fixes 
  P1 :: "sterm \<Rightarrow> bool" and 
  P2 :: "sterm \<Rightarrow> fVariable \<Rightarrow> fVariable \<Rightarrow> bool" and 
  P3 :: "sterm \<Rightarrow> bool" and f :: "Label -~> sterm"
  assumes 
  "\<And>t. \<lbrakk> P1 t; \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P2 t s p \<rbrakk> \<Longrightarrow> P3 t" and
  "\<forall>l\<in>dom f. P1 (the(f l))" and
  "\<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P2 (the(f l)) s p"
  shows "\<forall>l\<in>dom f. P3 (the(f l))"
proof (intro strip)
  fix l assume "l \<in> dom f" with assms(2) have "P1 (the(f l))" by blast
  moreover
  from assms(3) \<open>l \<in> dom f\<close> have "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P2 (the(f l)) s p"
    by blast
  ultimately
  show "P3 (the(f l))" using assms(1) by simp
qed

lemma ball_tt'sp_P3:
  fixes 
  P1 :: "sterm \<Rightarrow> sterm \<Rightarrow> bool" and 
  P2 :: "sterm \<Rightarrow> sterm \<Rightarrow> fVariable \<Rightarrow> fVariable \<Rightarrow> bool" and 
  P3 :: "sterm \<Rightarrow> sterm \<Rightarrow> bool" and 
  f :: "Label -~> sterm" and f' :: "Label -~> sterm"
  assumes 
  "\<And>t t'. \<lbrakk> P1 t t'; \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P2 t t' s p \<rbrakk> \<Longrightarrow> P3 t t'" and
  "dom f = dom f'" and
  "\<forall>l\<in>dom f. P1 (the(f l)) (the(f' l))" and
  "\<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P2 (the(f l)) (the(f' l)) s p"
  shows "\<forall>l\<in>dom f'. P3 (the(f l)) (the(f' l))"
proof (intro strip)
  fix l assume "l \<in> dom f'" with assms(2-3) have "P1 (the(f l)) (the(f' l))" 
    by blast
  moreover 
  from assms(2,4) \<open>l \<in> dom f'\<close>
  have "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P2 (the (f l)) (the(f' l)) s p" by blast
  ultimately
  show "P3 (the(f l)) (the(f' l))" using assms(1)[of "the(f l)" "the(f' l)"] 
    by simp
qed

subsubsection \<open>Free variables\<close>
primrec
 FV       :: "sterm \<Rightarrow> fVariable set"
and
 FVoption :: "sterm option \<Rightarrow> fVariable set"
where
  FV_Bvar : "FV(Bvar b) = {}"
| FV_Fvar : "FV(Fvar x) = {x}"
| FV_Call : "FV(Call t l a) = FV t \<union> FV a"
| FV_Upd  : "FV(Upd t l s) = FV t \<union> FV s"
| FV_Obj  : "FV(Obj f T) = (\<Union> l \<in> dom f. FVoption(f l))"
| FV_None : "FVoption None = {}"
| FV_Some : "FVoption (Some t) = FV t"

definition closed :: "sterm \<Rightarrow> bool" where
 "closed t \<longleftrightarrow> FV t = {}"

(* finiteness of FV *)
lemma finite_FV_FVoption: "finite (FV t) \<and> finite (FVoption s)"
by(induct _ t _ s rule: compat_sterm_sterm_option.induct, simp_all)

(* for infiniteness of string sets see
    List.infinite_UNIV_listI *)

(* NOTE: ex_new_if_finite, infinite_UNIV_listI and finite_FV offer an easy way to proof exists-fresh-statements *)
lemma finite_FV[simp]: "finite (FV t)"
  by (simp add: finite_FV_FVoption)

lemma FV_and_cofinite: "\<lbrakk> \<forall>x. x \<notin> L \<longrightarrow> P x; finite L \<rbrakk> 
  \<Longrightarrow> \<exists>L'. (finite L' \<and> FV t \<subseteq> L' \<and> (\<forall> x. x \<notin> L' \<longrightarrow> P x))"
  by (rule_tac x = "L \<union> FV t" in exI, auto)

lemma exFresh_s_p_cof: 
  fixes L :: "fVariable set"
  assumes "finite L"
  shows "\<exists>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p"
proof -
  from assms have "\<exists>s. s \<notin> L" by (simp only: ex_new_if_finite[OF infinite_UNIV_listI])
  then obtain s where "s \<notin> L" ..
  moreover
  from \<open>finite L\<close> have "finite (L \<union> {s})" by simp
  hence "\<exists>p. p \<notin> L \<union> {s}" by (simp only: ex_new_if_finite[OF infinite_UNIV_listI])
  then obtain p where "p \<notin> L \<union> {s}" ..
  ultimately show ?thesis by blast
qed

lemma FV_option_lem: "\<forall>l\<in>dom f. FV (the(f l)) = FVoption (f l)"
  by auto

subsubsection \<open>Term opening\<close>
primrec
  sopen        :: "[nat, sterm, sterm, sterm] \<Rightarrow> sterm" 
  ("{_ \<rightarrow> [_,_]} _" [0, 0, 0, 300] 300)
and
  sopen_option :: "[nat, sterm, sterm, sterm option] \<Rightarrow> sterm option"
where
  sopen_Bvar: 
    "{k \<rightarrow> [s,p]}(Bvar b) = (case b of (Self i) \<Rightarrow> (if (k = i) then s else (Bvar b)) 
                                    | (Param i) \<Rightarrow> (if (k = i) then p else (Bvar b)))"
| sopen_Fvar: "{k \<rightarrow> [s,p]}(Fvar x) = Fvar x"
| sopen_Call: "{k \<rightarrow> [s,p]}(Call t l a) = Call ({k \<rightarrow> [s,p]}t) l ({k \<rightarrow> [s,p]}a)"
| sopen_Upd : "{k \<rightarrow> [s,p]}(Upd t l u) = Upd ({k \<rightarrow> [s,p]}t) l ({(Suc k) \<rightarrow> [s,p]}u)"
| sopen_Obj : "{k \<rightarrow> [s,p]}(Obj f T) = Obj (\<lambda>l. sopen_option (Suc k) s p (f l)) T"
| sopen_None: "sopen_option k s p None = None"
| sopen_Some: "sopen_option k s p (Some t) = Some ({k \<rightarrow> [s,p]}t)"

definition openz :: "[sterm, sterm, sterm] \<Rightarrow> sterm" ("(_)\<^bsup>[_,_]\<^esup>" [50, 0, 0] 50) where
 "t\<^bsup>[s,p]\<^esup> = {0 \<rightarrow> [s,p]}t"

lemma sopen_eq_Fvar:
  fixes n s p t x
  assumes "{n \<rightarrow> [Fvar s,Fvar p]} t = Fvar x"
  shows 
  "(t = Fvar x) \<or> (x = s \<and> t = (Bvar (Self n))) 
  \<or> (x = p \<and> t = (Bvar (Param n)))"
proof (cases t)
  case Obj with assms show ?thesis by simp
next
  case Call with assms show ?thesis by simp
next
  case Upd with assms show ?thesis by simp
next
  case (Fvar y) with assms show ?thesis
    by (cases "y = x", simp_all)
next
  case (Bvar b) thus ?thesis
  proof (cases b)
    case (Self k) with assms Bvar show ?thesis 
      by (cases "k = n") simp_all
  next
    case (Param k) with assms Bvar show ?thesis 
      by (cases "k = n") simp_all
  qed
qed

lemma sopen_eq_Fvar': 
  assumes "{n \<rightarrow> [Fvar s,Fvar p]} t = Fvar x" and "x \<noteq> s" and "x \<noteq> p"
  shows "t = Fvar x"
proof -
  from sopen_eq_Fvar[OF assms(1)] \<open>x \<noteq> s\<close> \<open>x \<noteq> p\<close> show ?thesis
    by auto
qed

lemma sopen_eq_Bvar: 
  fixes n s p t b
  assumes "{n \<rightarrow> [Fvar s,Fvar p]} t = Bvar b"
  shows "t = Bvar b"
proof (cases t)
  case Fvar with assms show ?thesis by (simp add: openz_def)
next
  case Obj with assms show ?thesis by (simp add: openz_def)
next
  case Call with assms show ?thesis by (simp add: openz_def)
next
  case Upd with assms show ?thesis by (simp add: openz_def)
next
  case (Bvar b') show ?thesis
  proof (cases b')
    case (Self k) with assms Bvar show ?thesis
      by (cases "k = n") (simp_all add: openz_def)
  next
    case (Param k) with assms Bvar show ?thesis
      by (cases "k = n") (simp_all add: openz_def)
  qed
qed

lemma sopen_eq_Obj: 
  fixes n s p t f T
  assumes "{n \<rightarrow> [Fvar s,Fvar p]} t = Obj f T"
  shows 
  "\<exists>f'. {n \<rightarrow> [Fvar s, Fvar p]} Obj f' T = Obj f T  
      \<and>  t = Obj f' T"
proof (cases t)
  case Fvar with assms show ?thesis by simp
next
  case Obj with assms show ?thesis by simp
next
  case Call with assms show ?thesis by simp
next
  case Upd with assms show ?thesis by simp
next
  case (Bvar b) thus ?thesis
  proof (cases b)
    case (Self k) with assms Bvar show ?thesis 
      by (cases "k = n") simp_all
  next
    case (Param k) with assms Bvar show ?thesis 
      by (cases "k = n") simp_all
  qed
qed

lemma sopen_eq_Upd: 
  fixes n s p t t1 l t2
  assumes "{n \<rightarrow> [Fvar s,Fvar p]} t = Upd t1 l t2"
  shows 
  "\<exists>t1' t2'. {n \<rightarrow> [Fvar s,Fvar p]} t1' = t1 
           \<and> {(Suc n) \<rightarrow> [Fvar s,Fvar p]} t2' = t2 \<and> t = Upd t1' l t2'"
proof (cases t)
  case Fvar with assms show ?thesis by simp
next
  case Obj with assms show ?thesis by simp
next
  case Call with assms show ?thesis by simp
next
  case Upd with assms show ?thesis by simp
next
  case (Bvar b) thus ?thesis
  proof (cases b)
    case (Self k) with assms Bvar show ?thesis 
      by (cases "k = n") simp_all
  next
    case (Param k) with assms Bvar show ?thesis 
      by (cases "k = n") simp_all
  qed
qed

lemma sopen_eq_Call: 
  fixes n s p t t1 l t2
  assumes "{n \<rightarrow> [Fvar s,Fvar p]} t = Call t1 l t2"
  shows 
  "\<exists>t1' t2'. {n \<rightarrow> [Fvar s,Fvar p]} t1' = t1 
           \<and> {n \<rightarrow> [Fvar s,Fvar p]} t2' = t2 \<and> t = Call t1' l t2'"
proof (cases t)
  case Fvar with assms show ?thesis by simp
next
  case Obj with assms show ?thesis by simp
next
  case Call with assms show ?thesis by simp
next
  case Upd with assms show ?thesis by simp
next
  case (Bvar b) thus ?thesis
  proof (cases b)
    case (Self k) with assms Bvar show ?thesis 
      by (cases "k = n") simp_all
  next
    case (Param k) with assms Bvar show ?thesis 
      by (cases "k = n") simp_all
  qed
qed

lemma dom_sopenoption_lem[simp]: "dom (\<lambda>l. sopen_option k s t (f l)) = dom f"
  by (auto, case_tac "x \<in> dom f", auto)

lemma sopen_option_lem: 
  "\<forall>l\<in>dom f. {n \<rightarrow> [s,p]} the(f l) = the (sopen_option n s p (f l))" 
  by auto

lemma pred_sopenoption_lem:
  "(\<forall>l\<in>dom (\<lambda>l. sopen_option n s p (f l)).
     (P::sterm \<Rightarrow> bool) (the (sopen_option n s p (f l)))) = 
   (\<forall>l\<in>dom f. (P::sterm \<Rightarrow> bool) ({n \<rightarrow> [s,p]} the (f l)))"
  by (simp, force)

lemma sopen_FV[rule_format]:
  "\<forall>n s p. FV ({n \<rightarrow> [s,p]} t) \<subseteq> FV t \<union> FV s \<union> FV p"
proof -
  fix u
  have
    "(\<forall>n s p. FV ({n \<rightarrow> [s,p]} t) \<subseteq> FV t \<union> FV s \<union> FV p)
    &(\<forall>n s p. FVoption (sopen_option n s p u) \<subseteq> FVoption u \<union> FV s \<union> FV p)"
    apply (induct u rule: compat_sterm_sterm_option.induct)
    apply (auto split: bVariable.split)
    apply (metis (no_types, lifting) FV_Some UnE domI sopen_Some subsetCE)
    apply blast
    apply blast
    done
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma sopen_commute[rule_format]:
  "\<forall>n k s p s' p'. n \<noteq> k
     \<longrightarrow> {n \<rightarrow> [Fvar s', Fvar p']} {k \<rightarrow> [Fvar s, Fvar p]} t 
         = {k \<rightarrow> [Fvar s, Fvar p]} {n \<rightarrow> [Fvar s', Fvar p']} t"
proof -
  fix u
  have
    "(\<forall>n k s p s' p'. n \<noteq> k
      \<longrightarrow> {n \<rightarrow> [Fvar s', Fvar p']} {k \<rightarrow> [Fvar s, Fvar p]} t 
          = {k \<rightarrow> [Fvar s, Fvar p]} {n \<rightarrow> [Fvar s', Fvar p']} t)
    &(\<forall>n k s p s' p'. n \<noteq> k
      \<longrightarrow> sopen_option n (Fvar s') (Fvar p') (sopen_option k (Fvar s) (Fvar p) u) 
          = sopen_option k (Fvar s) (Fvar p)
             (sopen_option n (Fvar s') (Fvar p') u))"
    by (rule compat_sterm_sterm_option.induct, simp_all split: bVariable.split)
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma sopen_fresh_inj[rule_format]:
  "\<forall>n s p t'. {n \<rightarrow> [Fvar s, Fvar p]} t = {n \<rightarrow> [Fvar s, Fvar p]} t'
     \<longrightarrow> s \<notin> FV t \<longrightarrow> s \<notin> FV t' \<longrightarrow> p \<notin> FV t \<longrightarrow> p \<notin> FV t' \<longrightarrow> s \<noteq> p
     \<longrightarrow> t = t'"
proof -
  {
    fix 
      b s p n t
    assume 
      "(case b of Self i \<Rightarrow> if n = i then Fvar s else Bvar b
               | Param i \<Rightarrow> if n = i then Fvar p else Bvar b) = t"
    hence "Fvar s = t \<or> Fvar p = t \<or> Bvar b = t"
      by (cases b, auto, (rename_tac nat, case_tac "n = nat", auto)+)
  }
  note cT = this

(* induction *)
  fix u
  have
    "(\<forall>n s p t'. {n \<rightarrow> [Fvar s, Fvar p]} t = {n \<rightarrow> [Fvar s, Fvar p]} t'
      \<longrightarrow> s \<notin> FV t \<longrightarrow> s \<notin> FV t' \<longrightarrow> p \<notin> FV t \<longrightarrow> p \<notin> FV t' \<longrightarrow> s \<noteq> p
      \<longrightarrow> t = t')
    &(\<forall>n s p u'. sopen_option n (Fvar s) (Fvar p) u 
                  = sopen_option n (Fvar s) (Fvar p) u'
      \<longrightarrow> s \<notin> FVoption u \<longrightarrow> s \<notin> FVoption u' 
      \<longrightarrow> p \<notin> FVoption u \<longrightarrow> p \<notin> FVoption u' \<longrightarrow> s \<noteq> p
      \<longrightarrow> u = u')"
  proof (induct _ t _ u rule: compat_sterm_sterm_option.induct)
    case (Bvar b) thus ?case
    proof (auto)
      fix s p n t
      assume 
        a: "(case b of Self i \<Rightarrow> if n = i then Fvar s else Bvar b
                 | Param i \<Rightarrow> if n = i then Fvar p else Bvar b) 
         = {n \<rightarrow> [Fvar s,Fvar p]} t"
      note cT[OF this]
      moreover assume "s \<notin> FV t" and "p \<notin> FV t" and "s \<noteq> p"
      ultimately show "Bvar b = t"
      proof (auto)
        {
          fix b'
          assume 
            "(case b' of Self i \<Rightarrow> if n = i then Fvar s else Bvar b'
                      | Param i \<Rightarrow> if n = i then Fvar p else Bvar b') = Fvar s"
          with \<open>s \<noteq> p\<close> have "b' = Self n"
            by (cases b', auto, (rename_tac nat, case_tac "n = nat", auto)+)
        }note fvS = this
        assume eq_s: "Fvar s = {n \<rightarrow> [Fvar s,Fvar p]} t"
        with sym[OF this] \<open>s \<notin> FV t\<close> \<open>s \<noteq> p\<close> fvS
        have "t = Bvar (Self n)" by (cases t, auto)
        moreover
        from a sym[OF eq_s] \<open>s \<noteq> p\<close> fvS[of b]
        have "Self n = b" by simp
        ultimately show "Bvar b = t" by simp
      next
        {
          fix b'
          assume 
            "(case b' of Self i \<Rightarrow> if n = i then Fvar s else Bvar b'
                      | Param i \<Rightarrow> if n = i then Fvar p else Bvar b') = Fvar p"
          with \<open>s \<noteq> p\<close> have "b' = Param n"
            by (cases b', auto, (rename_tac nat, case_tac "n = nat", auto)+)
        }note fvP = this
        assume eq_p: "Fvar p = {n \<rightarrow> [Fvar s,Fvar p]} t"
        with sym[OF this] \<open>p \<notin> FV t\<close> \<open>s \<noteq> p\<close> fvP
        have "t = Bvar (Param n)" by (cases t, auto)
        moreover
        from a sym[OF eq_p] \<open>s \<noteq> p\<close> fvP[of b]
        have "Param n = b" by simp
        ultimately show "Bvar b = t" by simp
      next
        assume "Bvar b = {n \<rightarrow> [Fvar s, Fvar p]} t"
        from sym[OF this] show "{n \<rightarrow> [Fvar s,Fvar p]} t = t"
        proof (cases t, auto)
          fix b'
          assume 
            "(case b' of Self i \<Rightarrow> if n = i then Fvar s else Bvar b'
                      | Param i \<Rightarrow> if n = i then Fvar p else Bvar b') = Bvar b"
          from cT[OF this] have "Bvar b = Bvar b'" by simp
          thus "b = b'" by simp
        qed
      qed
    qed
  next
    case (Fvar x) thus ?case
    proof (auto)
      fix n s p t
      assume 
        a: "Fvar x = {n \<rightarrow> [Fvar s,Fvar p]} t" and
        "s \<notin> FV ({n \<rightarrow> [Fvar s,Fvar p]} t)"
      hence "s \<noteq> x" by force
      moreover
      assume "p \<notin> FV ({n \<rightarrow> [Fvar s,Fvar p]} t)"
      with a have "p \<noteq> x" by force
      ultimately
      show "{n \<rightarrow> [Fvar s,Fvar p]} t = t"
        using a
      proof (cases t, auto)
        fix b
        assume 
          "Fvar x = (case b of Self i \<Rightarrow> if n = i then Fvar s else Bvar b
                            | Param i \<Rightarrow> if n = i then Fvar p else Bvar b)"
        from cT[OF sym[OF this]] \<open>s \<noteq> x\<close> \<open>p \<noteq> x\<close>
        have False by simp
        then show 
          "(case b of Self i \<Rightarrow> if n = i then Fvar s else Bvar b
                   | Param i \<Rightarrow> if n = i then Fvar p else Bvar b) = Bvar b" ..
      qed
    qed
  next
    case (Obj f T) thus ?case
    proof (auto)
      fix n s p t
      assume 
        "Obj (\<lambda>l. sopen_option (Suc n) (Fvar s) (Fvar p) (f l)) T 
         = {n \<rightarrow> [Fvar s,Fvar p]} t" and
        "\<forall>l\<in>dom f. s \<notin> FVoption (f l)" and 
        "\<forall>l\<in>dom f. p \<notin> FVoption (f l)" and
        "s \<notin> FV t" and "p \<notin> FV t" and "s \<noteq> p"
      thus "Obj f T = t" using Obj
      proof (cases t, auto)
          (* case Bvar *)
        fix b
        assume 
          "Obj (\<lambda>l. sopen_option (Suc n) (Fvar s) (Fvar p) (f l)) T 
           = (case b of Self i \<Rightarrow> if n = i then Fvar s else Bvar b
                     | Param i \<Rightarrow> if n = i then Fvar p else Bvar b)"
        from cT[OF sym[OF this]] show False by auto
      next
          (* case Obj *)
        fix f'
        assume 
          nin_s: "\<forall>l\<in>dom f'. s \<notin> FVoption (f' l)" and
          nin_p: "\<forall>l\<in>dom f'. p \<notin> FVoption (f' l)" and
          ff':   "(\<lambda>l. sopen_option (Suc n) (Fvar s) (Fvar p) (f l)) 
                  = (\<lambda>l. sopen_option (Suc n) (Fvar s) (Fvar p) (f' l))"
        have "\<And>l. f l = f' l"
        proof -
          fix  l
          from ff'
          have 
            "sopen_option (Suc n) (Fvar s) (Fvar p) (f l) 
             = sopen_option (Suc n) (Fvar s) (Fvar p) (f' l)"
            by (rule cong, simp)
          moreover
          from 
            \<open>\<forall>l\<in>dom f. s \<notin> FVoption (f l)\<close>
            \<open>\<forall>l\<in>dom f. p \<notin> FVoption (f l)\<close> 
          have "s \<notin> FVoption (f l)" and "p \<notin> FVoption (f l)"
            by (case_tac "l \<in> dom f", auto)+
          moreover
          from nin_s nin_p have "s \<notin> FVoption (f' l)" and "p \<notin> FVoption (f' l)"
            by (case_tac "l \<in> dom f'", auto)+
          ultimately show "f l = f' l" using Obj[of l] \<open>s \<noteq> p\<close>
            by simp
        qed
        thus "f = f'" by (rule ext)
      qed
    qed
  next
    case (Call t1 l t2) thus ?case
    proof (auto)
      fix n s p t
      assume 
        "s \<notin> FV t1" and "s \<notin> FV t2" and "p \<notin> FV t1" and "p \<notin> FV t2" and
        "s \<noteq> p" and "s \<notin> FV t" and "p \<notin> FV t" and 
        "Call ({n \<rightarrow> [Fvar s,Fvar p]} t1) l ({n \<rightarrow> [Fvar s,Fvar p]} t2)
         = {n \<rightarrow> [Fvar s,Fvar p]} t"
      thus "Call t1 l t2 = t" using Call
      proof (cases t, auto)
          (* case Bvar *)
        fix b
        assume 
          "Call ({n \<rightarrow> [Fvar s,Fvar p]} t1) l ({n \<rightarrow> [Fvar s,Fvar p]} t2) 
           = (case b of Self i \<Rightarrow> if n = i then Fvar s else Bvar b
                     | Param i \<Rightarrow> if n = i then Fvar p else Bvar b)"
        from cT[OF sym[OF this]] show False by auto
      qed
    qed
  next
    case (Upd t1 l t2) thus ?case
    proof (auto)
      fix n s p t
      assume 
        "s \<notin> FV t1" and "s \<notin> FV t2" and "p \<notin> FV t1" and "p \<notin> FV t2" and
        "s \<noteq> p" and "s \<notin> FV t" and "p \<notin> FV t" and
        "Upd ({n \<rightarrow> [Fvar s,Fvar p]} t1) l ({Suc n \<rightarrow> [Fvar s,Fvar p]} t2)
         = {n \<rightarrow> [Fvar s,Fvar p]} t"
      thus "Upd t1 l t2 = t" using Upd
      proof (cases t, auto)
          (* case Bvar *)
        fix b
        assume 
          "Upd ({n \<rightarrow> [Fvar s,Fvar p]} t1) l ({Suc n \<rightarrow> [Fvar s,Fvar p]} t2) 
           = (case b of Self i \<Rightarrow> if n = i then Fvar s else Bvar b
                     | Param i \<Rightarrow> if n = i then Fvar p else Bvar b)"
        from cT[OF sym[OF this]] show False by auto
      qed
    qed
  next
    case None_sterm thus ?case
    proof (auto)
      fix u s p n
      assume "None = sopen_option n (Fvar s) (Fvar p) u"
      thus "None = u" by (cases u, auto)
    qed
  next
    case (Some_sterm t) thus ?case
    proof (auto)
      fix u s p n
      assume 
        "Some ({n \<rightarrow> [Fvar s,Fvar p]} t) = sopen_option n (Fvar s) (Fvar p) u" and
        "s \<notin> FV t" and "p \<notin> FV t" and "s \<noteq> p" and 
        "s \<notin> FVoption u" and "p \<notin> FVoption u"
      with Some_sterm show "Some t = u" by (cases u) auto
    qed
  qed
  from conjunct1[OF this] show ?thesis by assumption
qed

subsubsection \<open>Variable closing\<close>
primrec
 sclose        :: "[nat, fVariable, fVariable, sterm] \<Rightarrow> sterm" 
 ("{_ \<leftarrow> [_,_]} _" [0, 0, 0, 300] 300)
and
 sclose_option :: "[nat, fVariable, fVariable, sterm option] \<Rightarrow> sterm option"
where
  sclose_Bvar: "{k \<leftarrow> [s,p]}(Bvar b) = Bvar b"
| sclose_Fvar: 
    "{k \<leftarrow> [s,p]}(Fvar x) = (if x = s then (Bvar (Self k)) 
                                      else (if x = p then (Bvar (Param k))
                                                     else (Fvar x)))"
| sclose_Call: "{k \<leftarrow> [s,p]}(Call t l a) = Call ({k \<leftarrow> [s,p]}t) l ({k \<leftarrow> [s,p]}a)"
| sclose_Upd : "{k \<leftarrow> [s,p]}(Upd t l u) = Upd ({k \<leftarrow> [s,p]}t) l ({(Suc k) \<leftarrow> [s,p]}u)"
| sclose_Obj : "{k \<leftarrow> [s,p]}(Obj f T) = Obj (\<lambda>l. sclose_option (Suc k) s p (f l)) T"
| sclose_None: "sclose_option k s p None = None"
| sclose_Some: "sclose_option k s p (Some t) = Some ({k \<leftarrow> [s,p]}t)"

definition closez :: "[fVariable, fVariable, sterm] \<Rightarrow> sterm" ("\<sigma>[_,_] _" [0, 0, 300]) where
 "\<sigma>[s,p] t = {0 \<leftarrow> [s,p]}t"

lemma dom_scloseoption_lem[simp]: "dom (\<lambda>l. sclose_option k s t (f l)) = dom f"
  by (auto, case_tac "x \<in> dom f", auto)

lemma sclose_option_lem: 
  "\<forall>l\<in>dom f. {n \<leftarrow> [s,p]} the(f l) = the (sclose_option n s p (f l))" 
  by auto

lemma pred_scloseoption_lem:
  "(\<forall>l\<in>dom (\<lambda>l. sclose_option n s p (f l)).
     (P::sterm \<Rightarrow> bool) (the (sclose_option n s p (f l)))) = 
   (\<forall>l\<in>dom f. (P::sterm \<Rightarrow> bool) ({n \<leftarrow> [s,p]} the (f l)))"
  by (simp, force)

lemma sclose_fresh[simp, rule_format]:
  "\<forall>n s p. s \<notin> FV t \<longrightarrow> p \<notin> FV t \<longrightarrow> {n \<leftarrow> [s,p]} t = t"
proof -
  have 
    "(\<forall>n s p. s \<notin> FV t \<longrightarrow> p \<notin> FV t \<longrightarrow> {n \<leftarrow> [s,p]} t = t)
    &(\<forall>n s p. s \<notin> FVoption u \<longrightarrow> p \<notin> FVoption u 
       \<longrightarrow> sclose_option n s p u = u)"
  proof (induct _ t _ u rule: compat_sterm_sterm_option.induct, auto simp: bVariable.split)
    (* Obj *)
    fix f n s p
    assume 
      nin_s: "\<forall>l\<in>dom f. s \<notin> FVoption (f l)" and 
      nin_p: "\<forall>l\<in>dom f. p \<notin> FVoption (f l)"
    {
      fix l from nin_s have "s \<notin> FVoption (f l)"
        by (case_tac "l \<in> dom f", auto)
    }
    moreover
    {
      fix l from nin_p have "p \<notin> FVoption (f l)"
        by (case_tac "l \<in> dom f", auto)
    }
    moreover 
    assume 
      "\<And>x. \<forall>n s. s \<notin> FVoption (f x) 
             \<longrightarrow> (\<forall>p. p \<notin> FVoption (f x) 
                   \<longrightarrow> sclose_option n s p (f x) = f x)"
    ultimately
    have "\<And>l. sclose_option (Suc n) s p (f l) = f l" by auto
    with ext show "(\<lambda>l. sclose_option (Suc n) s p (f l)) = f" by auto
  qed
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma sclose_FV[rule_format]:
  "\<forall>n s p. FV ({n \<leftarrow> [s,p]} t) = FV t - {s} - {p}"
proof -
  have
    "(\<forall>n s p. FV ({n \<leftarrow> [s,p]} t) = FV t - {s} - {p})
    &(\<forall>n s p. FVoption (sclose_option n s p u) = FVoption u - {s} - {p})"
    by (rule compat_sterm_sterm_option.induct, simp_all split: bVariable.split, blast+)
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma sclose_subset_FV[rule_format]:
  "FV ({n \<leftarrow> [s,p]} t) \<subseteq> FV t"
  by (simp add: sclose_FV, blast)

lemma Self_not_in_closed[simp]: "sa \<notin> FV ({n \<leftarrow> [sa,pa]} t)"
  by (simp add: sclose_FV)

lemma Param_not_in_closed[simp]: "pa \<notin> FV ({n \<leftarrow> [sa,pa]} t)"
  by (simp add: sclose_FV)

subsubsection \<open>Substitution\<close>
primrec
 ssubst        :: "[fVariable, sterm, sterm] \<Rightarrow> sterm" 
 ("[_ \<rightarrow> _] _" [0, 0, 300] 300)
and
 ssubst_option :: "[fVariable, sterm, sterm option] \<Rightarrow> sterm option"
where
  ssubst_Bvar: "[z \<rightarrow> u](Bvar v) = Bvar v"
| ssubst_Fvar: "[z \<rightarrow> u](Fvar x) = (if (z = x) then u else (Fvar x))"
| ssubst_Call: "[z \<rightarrow> u](Call t l s) = Call ([z \<rightarrow> u]t) l ([z \<rightarrow> u]s)"
| ssubst_Upd : "[z \<rightarrow> u](Upd t l s) = Upd ([z \<rightarrow> u]t) l ([z \<rightarrow> u]s)"
| ssubst_Obj : "[z \<rightarrow> u](Obj f T) = Obj (\<lambda>l. ssubst_option z u (f l)) T"
| ssubst_None: "ssubst_option z u None = None"
| ssubst_Some: "ssubst_option z u (Some t) = Some ([z \<rightarrow> u]t)"

lemma dom_ssubstoption_lem[simp]: "dom (\<lambda>l. ssubst_option z u (f l)) = dom f"
  by (auto, case_tac "x \<in> dom f", auto)

lemma ssubst_option_lem: 
  "\<forall>l\<in>dom f. [z \<rightarrow> u] the(f l) = the (ssubst_option z u (f l))" 
  by auto

lemma pred_ssubstoption_lem:
  "(\<forall>l\<in>dom (\<lambda>l. ssubst_option x t (f l)).
     (P::sterm \<Rightarrow> bool) (the (ssubst_option x t (f l)))) = 
   (\<forall>l\<in>dom f. (P::sterm \<Rightarrow> bool) ([x \<rightarrow> t] the (f l)))"
  by (simp, force)

lemma ssubst_fresh[simp, rule_format]:
  "\<forall>s sa. sa \<notin> FV t \<longrightarrow> [sa \<rightarrow> s] t = t"
proof -
  have 
    "(\<forall>s sa. sa \<notin> FV t \<longrightarrow> [sa \<rightarrow> s] t = t)
    &(\<forall>s sa. sa \<notin> FVoption u \<longrightarrow> ssubst_option sa s u = u)"
  proof (induct _ t _ u rule: compat_sterm_sterm_option.induct, auto)
    fix s sa f
    assume 
      sa:     "\<forall>l\<in>dom f. sa \<notin> FVoption (f l)" and
      ssubst: "\<And>x. \<forall>s sa. sa \<notin> FVoption (f x) \<longrightarrow> ssubst_option sa s (f x) = f x"
    {
      fix l from sa have "sa \<notin> FVoption (f l)" 
        by (case_tac "l \<in> dom f", auto)
      with ssubst have "ssubst_option sa s (f l) = f l" by auto
    }
    with ext show "(\<lambda>l. ssubst_option sa s (f l)) = f" by auto
  qed
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma ssubst_commute[rule_format]:
  "\<forall>s p sa pa. s \<noteq> p \<longrightarrow> s \<notin> FV pa \<longrightarrow> p \<notin> FV sa 
     \<longrightarrow> [s \<rightarrow> sa] [p \<rightarrow> pa] t = [p \<rightarrow> pa] [s \<rightarrow> sa] t"
proof -
  have
    "(\<forall>s p sa pa. s \<noteq> p \<longrightarrow> s \<notin> FV pa \<longrightarrow> p \<notin> FV sa 
       \<longrightarrow> [s \<rightarrow> sa] [p \<rightarrow> pa] t = [p \<rightarrow> pa] [s \<rightarrow> sa] t)
    &(\<forall>s p sa pa. s \<noteq> p \<longrightarrow> s \<notin> FV pa \<longrightarrow> p \<notin> FV sa 
       \<longrightarrow> ssubst_option s sa (ssubst_option p pa u) 
           = ssubst_option p pa (ssubst_option s sa u))"
    by (rule compat_sterm_sterm_option.induct, simp_all split: bVariable.split)
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma ssubst_FV[rule_format]:
  "\<forall>x s. FV ([x \<rightarrow> s] t) \<subseteq> FV s \<union> (FV t - {x})"
proof -
  have
    "(\<forall>x s. FV ([x \<rightarrow> s] t) \<subseteq> FV s \<union> (FV t - {x}))
    &(\<forall>x s. FVoption (ssubst_option x s u) \<subseteq> FV s \<union> (FVoption u - {x}))"
    by (rule compat_sterm_sterm_option.induct, simp_all split: bVariable.split, blast+)
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma ssubstoption_insert: 
  "l \<in> dom f 
  \<Longrightarrow> (\<lambda>(la::Label). ssubst_option x t' (if la = l then Some t else f la))
      = (\<lambda>(la::Label). ssubst_option x t' (f la))(l \<mapsto> [x \<rightarrow> t'] t)"
  by (rule Ltake_eq_all, force, simp add: Ltake_eq_def)

subsubsection \<open>Local closure\<close>
inductive lc :: "sterm \<Rightarrow> bool"
where
  lc_Fvar[simp, intro!]: "lc (Fvar x)"
| lc_Call[simp, intro!]: "\<lbrakk> lc t; lc a \<rbrakk> \<Longrightarrow> lc (Call t l a)"
| lc_Upd[simp, intro!] : 
  "\<lbrakk> lc t; finite L; 
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> lc (u\<^bsup>[Fvar s, Fvar p]\<^esup>) \<rbrakk>
  \<Longrightarrow> lc (Upd t l u)"
| lc_Obj[simp, intro!] : 
  "\<lbrakk> finite L; \<forall>l\<in>dom f. 
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> lc (the(f l)\<^bsup>[Fvar s, Fvar p]\<^esup>) \<rbrakk>
  \<Longrightarrow> lc (Obj f T)"

definition body :: "sterm \<Rightarrow> bool" where
 "body t \<longleftrightarrow> (\<exists>L. finite L \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> lc (t\<^bsup>[Fvar s, Fvar p]\<^esup>)))"

lemma lc_bvar: "lc (Bvar b) = False" 
  by (rule iffI, erule lc.cases, simp_all)

lemma lc_obj:
  "lc (Obj f T) = (\<forall>l\<in>dom f. body (the(f l)))"
proof
  fix f T assume "lc (Obj f T)"
  thus "\<forall>l\<in>dom f. body (the(f l))"
    unfolding body_def
    by (rule lc.cases, auto)
next
  fix f :: "Label -~> sterm" and T :: type
  assume "\<forall>l\<in>dom f. body (the (f l))"
  hence 
    "\<exists>L. finite L \<and> (\<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                                 \<longrightarrow> lc (the (f l)\<^bsup>[Fvar s, Fvar p]\<^esup>))"
  proof (induct f rule: fmap_induct)
    case empty thus ?case by blast
  next
    case (insert F x y) thus ?case
    proof -
      assume "x \<notin> dom F" hence "\<forall>l\<in>dom F. the(F l) = the ((F(x \<mapsto> y)) l)" 
        by auto
      with \<open>\<forall>l\<in>dom (F(x \<mapsto> y)). body (the((F(x \<mapsto> y)) l))\<close>
      have "\<forall>l\<in>dom F. body (the (F l))" by force
      from insert(2)[OF this]
      obtain L where 
        "finite L" and
        "\<forall>l\<in>dom F. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
                     \<longrightarrow> lc (the (F l)\<^bsup>[Fvar s, Fvar p]\<^esup>)" by auto
      moreover
      from \<open>\<forall>l\<in>dom (F(x \<mapsto> y)). body (the((F(x \<mapsto> y)) l))\<close> have "body y" by force
      then obtain L' where 
        "finite L'" and
        "\<forall>s p. s \<notin> L' \<and> p \<notin> L' \<and> s \<noteq> p
          \<longrightarrow> lc (y\<^bsup>[Fvar s, Fvar p]\<^esup>)" by (auto simp: body_def)

      ultimately
      show 
        "\<exists>L. finite L \<and> (\<forall>l\<in>dom (F(x \<mapsto> y)). \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                                               \<longrightarrow> lc (the ((F(x \<mapsto> y)) l)\<^bsup>[Fvar s,Fvar p]\<^esup>))" 
        by (rule_tac x = "L \<union> L'" in exI, auto)
    qed
  qed
  thus "lc (Obj f T)" by auto
qed

lemma lc_upd: "lc (Upd t l s) = (lc t \<and> body s)" 
  by (unfold body_def, rule iffI, erule lc.cases, auto)

lemma lc_call: "lc (Call t l s) = (lc t \<and> lc s)" 
  by (rule iffI, erule lc.cases, simp_all)

lemma lc_induct[consumes 1, case_names Fvar Call Upd Obj Bnd]:
  fixes P1 :: "sterm \<Rightarrow> bool" and P2 :: "sterm \<Rightarrow> bool"
  assumes
  "lc t" and
  "\<And>x. P1 (Fvar x)" and
  "\<And>t l a. \<lbrakk> lc t; P1 t; lc a; P1 a \<rbrakk> \<Longrightarrow> P1 (Call t l a)" and
  "\<And>t l u. \<lbrakk> lc t; P1 t; P2 u \<rbrakk> \<Longrightarrow> P1 (Upd t l u)" and
  "\<And>f T. \<forall>l\<in>dom f. P2 (the(f l)) \<Longrightarrow> P1 (Obj f T)" and
  "\<And>L t. \<lbrakk> finite L; 
            \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
             \<longrightarrow> lc (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<and> P1 (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<rbrakk>
  \<Longrightarrow> P2 t"
  shows "P1 t"
  using assms by (induct rule: lc.induct, auto)
  

subsubsection \<open>Connections between sopen, sclose, ssubst, lc and body and resulting properties\<close>
lemma ssubst_intro[rule_format]:
  "\<forall>n s p sa pa. sa \<notin> FV t \<longrightarrow> pa \<notin> FV t \<longrightarrow> sa \<noteq> pa
     \<longrightarrow> sa \<notin> FV p
     \<longrightarrow> {n \<rightarrow> [s,p]} t = [sa \<rightarrow> s] [pa \<rightarrow> p] {n \<rightarrow> [Fvar sa, Fvar pa]} t"
proof -
  have 
    "(\<forall>n s p sa pa. sa \<notin> FV t \<longrightarrow> pa \<notin> FV t \<longrightarrow> sa \<noteq> pa
       \<longrightarrow> sa \<notin> FV p
       \<longrightarrow> {n \<rightarrow> [s,p]} t = [sa \<rightarrow> s] [pa \<rightarrow> p] {n \<rightarrow> [Fvar sa, Fvar pa]} t)
    &(\<forall>n s p sa pa. sa \<notin> FVoption u \<longrightarrow> pa \<notin> FVoption u \<longrightarrow> sa \<noteq> pa
       \<longrightarrow> sa \<notin> FV p
       \<longrightarrow> sopen_option n s p u 
           = ssubst_option sa s (ssubst_option pa p 
              (sopen_option n (Fvar sa) (Fvar pa) u)))"
  proof (induct _ t _ u rule: compat_sterm_sterm_option.induct)
    case Bvar thus ?case by (simp split: bVariable.split)
  next
    case Fvar thus ?case by simp
  next
    case Upd thus ?case by simp
  next
    case Call thus ?case by simp
  next
    case None_sterm thus ?case by simp
  next
    case (Obj f T) thus ?case
    proof (clarify)
      fix n s p sa pa
      assume "sa \<notin> FV (Obj f T)" and "pa \<notin> FV (Obj f T)"
      {
        fix l 
        from \<open>sa \<notin> FV (Obj f T)\<close> have "sa \<notin> FVoption (f l)"
          by (case_tac "l \<in> dom f", auto)
      }
      moreover
      {
        fix l
        from \<open>pa \<notin> FV (Obj f T)\<close> have pa: "pa \<notin> FVoption (f l)"
          by (case_tac "l \<in> dom f", auto)
      }
      moreover assume "sa \<noteq> pa" and "sa \<notin> FV p"
      ultimately
      have 
        "\<And>l. sopen_option (Suc n) s p (f l) 
              = ssubst_option sa s (ssubst_option pa p
                 (sopen_option (Suc n) (Fvar sa) (Fvar pa) (f l)))"
        using Obj by auto
      with ext 
      show 
        "{n \<rightarrow> [s,p]} Obj f T 
         = [sa \<rightarrow> s] [pa \<rightarrow> p] {n \<rightarrow> [Fvar sa,Fvar pa]} Obj f T"
        by auto
    qed
  next
    case (Some_sterm t) thus ?case
    proof (clarify)
      fix n s p sa pa
      assume "sa \<notin> FVoption (Some t)"
      hence "sa \<notin> FV t" by simp
      moreover assume "pa \<notin> FVoption (Some t)"
      hence "pa \<notin> FV t" by simp
      moreover assume "sa \<noteq> pa" and "sa \<notin> FV p"
      ultimately
      have "{n \<rightarrow> [s,p]} t = [sa \<rightarrow> s] [pa \<rightarrow> p] {n \<rightarrow> [Fvar sa,Fvar pa]} t" 
        using Some_sterm by blast
      thus 
        "sopen_option n s p (Some t) 
         = ssubst_option sa s (ssubst_option pa p 
            (sopen_option n (Fvar sa) (Fvar pa) (Some t)))"
        by simp
    qed
  qed
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma sopen_lc_FV[rule_format]:
  fixes t
  assumes "lc t"
  shows "\<forall>n s p. {n \<rightarrow> [Fvar s, Fvar p]} t = t"
  using assms
proof 
  (induct
    taking: "\<lambda>t. \<forall>n s p. {Suc n \<rightarrow> [Fvar s, Fvar p]} t = t"
    rule: lc_induct)
  case Fvar thus ?case by simp
next
  case Call thus ?case by simp
next
  case Upd thus ?case by simp
next
  case (Obj f T) note pred = this 
  show ?case
  proof (intro strip, simp)
    fix n s p
    {
      fix l
      have "sopen_option (Suc n) (Fvar s) (Fvar p) (f l) = f l"
      proof (cases "l \<in> dom f")
        case False hence "f l = None" by force
        thus ?thesis by force
      next
        case True with pred show ?thesis by force
      qed
    } with ext 
    show "(\<lambda>l. sopen_option (Suc n) (Fvar s) (Fvar p) (f l)) = f"
      by auto
  qed
next
  case (Bnd L t) note cof = this(2)  
  show ?case
  proof (intro strip)
    fix n s p
    from \<open>finite L\<close> exFresh_s_p_cof[of "L \<union> FV t \<union> {s} \<union> {p}"]
    obtain sa pa where
      sapa: "sa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> pa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa"
      by auto
    with cof
    have "{Suc n \<rightarrow> [Fvar s,Fvar p]} (t\<^bsup>[Fvar sa, Fvar pa]\<^esup>) = (t\<^bsup>[Fvar sa, Fvar pa]\<^esup>)"
      by auto
    with sopen_commute[OF Suc_not_Zero[of n]]
    have 
      eq: "{0 \<rightarrow> [Fvar sa,Fvar pa]} {Suc n \<rightarrow> [Fvar s,Fvar p]} t
           = {0 \<rightarrow> [Fvar sa,Fvar pa]} t" 
      by (simp add: openz_def)
    from sapa contra_subsetD[OF sopen_FV[of _ "Fvar s" "Fvar p" t]]
    have 
      "sa \<notin> FV ({Suc n \<rightarrow> [Fvar s,Fvar p]} t)" and "sa \<notin> FV t" and
      "pa \<notin> FV ({Suc n \<rightarrow> [Fvar s,Fvar p]} t)" and "pa \<notin> FV t" and 
      "sa \<noteq> pa" 
      by auto
    from sopen_fresh_inj[OF eq this] 
    show "{Suc n \<rightarrow> [Fvar s,Fvar p]} t = t" by assumption
  qed
qed    

lemma sopen_lc[simp]: 
  fixes t n s p
  assumes "lc t"
  shows "{n \<rightarrow> [s,p]} t = t"
proof -
  from exFresh_s_p_cof[of "FV t \<union> FV p"] 
  obtain sa pa where 
    "sa \<notin> FV t" and "pa \<notin> FV t" and "sa \<noteq> pa" and 
    "sa \<notin> FV p" and "pa \<notin> FV p" 
    by auto
  from ssubst_intro[OF this(1-4)] 
  have "{n \<rightarrow> [s,p]} t = [sa \<rightarrow> s] [pa \<rightarrow> p] {n \<rightarrow> [Fvar sa,Fvar pa]} t" 
    by simp
  with assms have "{n \<rightarrow> [s,p]} t = [sa \<rightarrow> s] [pa \<rightarrow> p] t" 
    using sopen_lc_FV 
    by simp
  with ssubst_fresh[OF \<open>pa \<notin> FV t\<close>] 
  have "{n \<rightarrow> [s,p]} t = [sa \<rightarrow> s] t" by simp
  with ssubst_fresh[OF \<open>sa \<notin> FV t\<close>] 
  show "{n \<rightarrow> [s,p]} t = t" by simp
qed

lemma sopen_twice[rule_format]:
  "\<forall>s p s' p' n. lc s \<longrightarrow> lc p 
     \<longrightarrow> {n \<rightarrow> [s',p']} {n \<rightarrow> [s,p]} t = {n \<rightarrow> [s,p]} t"
proof -
  have
    "(\<forall>s p s' p' n. lc s \<longrightarrow> lc p 
      \<longrightarrow> {n \<rightarrow> [s',p']} {n \<rightarrow> [s,p]} t = {n \<rightarrow> [s,p]} t)
    &(\<forall>s p s' p' n. lc s \<longrightarrow> lc p 
      \<longrightarrow> sopen_option n s' p' (sopen_option n s p u) = sopen_option n s p u)"
    by (rule compat_sterm_sterm_option.induct, auto simp: bVariable.split)
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma sopen_sclose_commute[rule_format]:
  "\<forall>n k s p sa pa. n \<noteq> k \<longrightarrow> sa \<notin> FV s \<longrightarrow> sa \<notin> FV p 
     \<longrightarrow> pa \<notin> FV s \<longrightarrow> pa \<notin> FV p
     \<longrightarrow> {n \<rightarrow> [s, p]} {k \<leftarrow> [sa,pa]} t = {k \<leftarrow> [sa,pa]} {n \<rightarrow> [s, p]} t"
proof -
  have 
    "(\<forall>n k s p sa pa. n \<noteq> k \<longrightarrow> sa \<notin> FV s \<longrightarrow> sa \<notin> FV p 
       \<longrightarrow> pa \<notin> FV s \<longrightarrow> pa \<notin> FV p
       \<longrightarrow> {n \<rightarrow> [s, p]} {k \<leftarrow> [sa,pa]} t = {k \<leftarrow> [sa,pa]} {n \<rightarrow> [s, p]} t)
    &(\<forall>n k s p sa pa. n \<noteq> k \<longrightarrow> sa \<notin> FV s \<longrightarrow> sa \<notin> FV p 
       \<longrightarrow> pa \<notin> FV s \<longrightarrow> pa \<notin> FV p
       \<longrightarrow> sopen_option n s p (sclose_option k sa pa u) 
           = sclose_option k sa pa (sopen_option n s p u))"
    by (rule compat_sterm_sterm_option.induct, simp_all split: bVariable.split)
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma sclose_sopen_eq_t[rule_format]:
  "\<forall>n s p. s \<notin> FV t \<longrightarrow> p \<notin> FV t \<longrightarrow> s \<noteq> p
     \<longrightarrow> {n \<leftarrow> [s,p]} {n \<rightarrow> [Fvar s, Fvar p]} t = t"
proof -
  have 
    "(\<forall>n s p. s \<notin> FV t \<longrightarrow> p \<notin> FV t \<longrightarrow> s \<noteq> p
       \<longrightarrow> {n \<leftarrow> [s,p]} {n \<rightarrow> [Fvar s, Fvar p]} t = t)
    &(\<forall>n s p. s \<notin> FVoption u \<longrightarrow> p \<notin> FVoption u \<longrightarrow> s \<noteq> p
       \<longrightarrow> sclose_option n s p (sopen_option n (Fvar s) (Fvar p) u) = u)"
  proof (induct _ t _ u rule: compat_sterm_sterm_option.induct, simp_all split: bVariable.split, auto)
    (* Obj *)
    fix f n s p
    assume 
      nin_s: "\<forall>l\<in>dom f. s \<notin> FVoption (f l)" and
      nin_p: "\<forall>l\<in>dom f. p \<notin> FVoption (f l)"
    {
      fix l from nin_s have "s \<notin> FVoption (f l)"
        by (case_tac "l \<in> dom f", auto)
    }
    moreover
    {
      fix l from nin_p have "p \<notin> FVoption (f l)"
        by (case_tac "l \<in> dom f", auto)
    }
    moreover 
    assume 
      "s \<noteq> p" and
      "\<And>x. \<forall>n s. s \<notin> FVoption (f x) 
             \<longrightarrow> (\<forall>p. p \<notin> FVoption (f x) \<longrightarrow> s \<noteq> p 
                   \<longrightarrow> sclose_option n s p (sopen_option n (Fvar s) (Fvar p) (f x)) 
                       = f x)"
    ultimately
    have "\<And>l. sclose_option n s p (sopen_option n (Fvar s) (Fvar p) (f l)) = f l"
      by auto
    with ext 
    show "(\<lambda>l. sclose_option n s p (sopen_option n (Fvar s) (Fvar p) (f l))) = f "
      by auto
  qed
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma sopen_sclose_eq_t[simp, rule_format]:
  fixes t
  assumes "lc t"
  shows "\<forall>n s p. {n \<rightarrow> [Fvar s, Fvar p]} {n \<leftarrow> [s,p]} t = t"
  using assms
proof 
  (induct
    taking: "\<lambda>t. \<forall>n s p. {Suc n \<rightarrow> [Fvar s, Fvar p]} {Suc n \<leftarrow> [s,p]} t = t"
    rule: lc_induct)
  case Fvar thus ?case by simp
next
  case Call thus ?case by simp
next
  case Upd thus ?case by simp
next
  case (Obj f T) note pred = this
  show ?case
  proof (intro strip, simp)
    fix n s p
    {
      fix l
      have 
        "sopen_option (Suc n) (Fvar s) (Fvar p) (sclose_option (Suc n) s p (f l)) 
         = f l"
      proof (cases "l \<in> dom f")
        case False hence "f l = None" by force
        thus ?thesis by simp
      next
        case True with pred
        show ?thesis by force
      qed
    }
    with ext 
    show "(\<lambda>l. sopen_option (Suc n) (Fvar s) (Fvar p) 
                 (sclose_option (Suc n) s p (f l))) = f" 
      by simp
  qed
next
  case (Bnd L t) note cof = this(2)
  show ?case
  proof (intro strip)
    fix n s p
    from \<open>finite L\<close> exFresh_s_p_cof[of "L \<union> FV t \<union> {s} \<union> {p}"]
    obtain sa pa where
      sapa: "sa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> pa \<notin> L \<union> FV t \<union> {s} \<union> {p} 
             \<and> sa \<noteq> pa"
      by auto
    with cof
    have 
      eq: "{Suc n \<rightarrow> [Fvar s,Fvar p]} {Suc n \<leftarrow> [s,p]} (t\<^bsup>[Fvar sa, Fvar pa]\<^esup>) 
           = (t\<^bsup>[Fvar sa, Fvar pa]\<^esup>)" by blast

    {
      fix x assume "x \<notin> FV t"
      from contra_subsetD[OF sclose_subset_FV this]
      have "x \<notin> FV ({Suc n \<leftarrow> [s,p]} t)" by simp
      moreover assume "x \<noteq> p" and "x \<noteq> s"
      ultimately
      have "x \<notin> FV ({Suc n \<leftarrow> [s,p]} t) \<union> FV (Fvar s) \<union> FV (Fvar p)"
        by simp
      from contra_subsetD[OF sopen_FV this]
      have "x \<notin> FV ({Suc n \<rightarrow> [Fvar s,Fvar p]} {Suc n \<leftarrow> [s,p]} t)"
        by simp
    } with sapa
    have 
      "s \<notin> FV (Fvar sa)" and "s \<notin> FV (Fvar pa)" and
      "p \<notin> FV (Fvar sa)" and "p \<notin> FV (Fvar pa)" and
      "sa \<notin> FV ({Suc n \<rightarrow> [Fvar s,Fvar p]} {Suc n \<leftarrow> [s,p]} t)" and
      "sa \<notin> FV t" and
      "pa \<notin> FV ({Suc n \<rightarrow> [Fvar s,Fvar p]} {Suc n \<leftarrow> [s,p]} t)" and
      "pa \<notin> FV t" and "sa \<noteq> pa"
      by auto
(* proof:

{Suc n \<rightarrow> [Fvar s,Fvar p]} {Suc n \<leftarrow> [s,p]} (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>) 
= {Suc n \<rightarrow> [Fvar s,Fvar p]} {Suc n \<leftarrow> [s,p]} {0 \<rightarrow> [Fvar sa,Fvar pa]} t
= {Suc n \<rightarrow> [Fvar s,Fvar p]} {0 \<rightarrow> [Fvar sa,Fvar pa]} {Suc n \<leftarrow> [s,p]} t
= {0 \<rightarrow> [Fvar sa,Fvar pa]} {Suc n \<rightarrow> [Fvar s,Fvar p]} {Suc n \<leftarrow> [s,p]} t
= {0 \<rightarrow> [Fvar sa,Fvar pa]} t
= (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)
*)
    from
      eq
      sym[OF sopen_sclose_commute[OF not_sym[OF Suc_not_Zero[of n]] 
                                                this(1-4)]]
      sopen_commute[OF Suc_not_Zero[of n]]
      sopen_fresh_inj[OF _ this(5-9)]
    show "{Suc n \<rightarrow> [Fvar s,Fvar p]} {Suc n \<leftarrow> [s,p]} t = t"
      by (auto simp: openz_def)
  qed
qed

lemma ssubst_sopen_distrib[rule_format]:
  "\<forall>n s p t'. lc t' \<longrightarrow> [x \<rightarrow> t'] {n \<rightarrow> [s,p]} t 
   = {n \<rightarrow> [[x \<rightarrow> t']s, [x \<rightarrow> t']p]} [x \<rightarrow> t'] t"
proof -
  have
    "(\<forall>n s p t'. lc t' 
       \<longrightarrow> [x \<rightarrow> t'] {n \<rightarrow> [s,p]} t = {n \<rightarrow> [[x \<rightarrow> t']s, [x \<rightarrow> t']p]} [x \<rightarrow> t'] t)
    &(\<forall>n s p t'. lc t' 
       \<longrightarrow> ssubst_option x t' (sopen_option n s p u) 
           = sopen_option n ([x \<rightarrow> t']s) ([x \<rightarrow> t']p) (ssubst_option x t' u))"
    by (rule compat_sterm_sterm_option.induct, simp_all split: bVariable.split)
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma ssubst_openz_distrib:
  "lc t' \<Longrightarrow> [x \<rightarrow> t'] (t\<^bsup>[s,p]\<^esup>) = (([x \<rightarrow> t'] t)\<^bsup>[[x \<rightarrow> t'] s, [x \<rightarrow> t'] p]\<^esup>)"
  by (simp add: openz_def ssubst_sopen_distrib)

lemma ssubst_sopen_commute: "\<lbrakk> lc t'; x \<notin> FV s; x \<notin> FV p \<rbrakk> 
  \<Longrightarrow> [x \<rightarrow> t'] {n \<rightarrow> [s,p]} t = {n \<rightarrow> [s,p]} [x \<rightarrow> t'] t"
  by (frule ssubst_sopen_distrib[of t' x n s p t], simp)

lemma sopen_commute_gen:
  fixes s p s' p' n k t
  assumes "lc s" and "lc p" and "lc s'" and "lc p'" and "n \<noteq> k"
  shows "{n \<rightarrow> [s,p]} {k \<rightarrow> [s',p']} t = {k \<rightarrow> [s',p']} {n \<rightarrow> [s,p]} t"
proof -
  have "finite (FV s \<union> FV p \<union> FV s' \<union> FV p' \<union> FV t)" by auto
  from exFresh_s_p_cof[OF this]
  obtain sa pa where 
    "sa \<notin> FV s \<union> FV p \<union> FV s' \<union> FV p' \<union> FV t 
    \<and> pa \<notin> FV s \<union> FV p \<union> FV s' \<union> FV p' \<union> FV t \<and> sa \<noteq> pa" by auto
  moreover 
  hence "finite (FV s \<union> FV p \<union> FV s' \<union> FV p' \<union> FV t \<union> {sa} \<union> {pa})" by auto
  from exFresh_s_p_cof[OF this]
  obtain sb pb where 
    "sb \<notin> FV s \<union> FV p \<union> FV s' \<union> FV p' \<union> FV t \<union> {sa} \<union> {pa} 
    \<and> pb \<notin> FV s \<union> FV p \<union> FV s' \<union> FV p' \<union> FV t \<union> {sa} \<union> {pa} 
    \<and> sb \<noteq> pb" by auto
  ultimately
  have
    "sa \<notin> FV t" and "pa \<notin> FV t" and "sb \<notin> FV t" and "pb \<notin> FV t" and
    "sa \<notin> FV ({n \<rightarrow> [s,p]} t)" and "pa \<notin> FV ({n \<rightarrow> [s,p]} t)" and
    "sb \<notin> FV ({k \<rightarrow> [s',p']} t)" and "pb \<notin> FV ({k \<rightarrow> [s',p']} t)" and

    "sa \<noteq> pa" and "sb \<noteq> pb" and "sb \<noteq> sa" and "sb \<noteq> pa" and 
    "pb \<noteq> sa" and "pb \<noteq> pa" and

    "sa \<notin> FV s" and "sa \<notin> FV p" and "pa \<notin> FV s" and "pa \<notin> FV p" and
    "sb \<notin> FV s'" and "sb \<notin> FV p'" and "pb \<notin> FV s'" and "pb \<notin> FV p'" and
    "sa \<notin> FV p'" and "sb \<notin> FV p" and

    "sa \<notin> FV (Fvar sb)" and "sa \<notin> FV (Fvar pb)" and
    "pa \<notin> FV (Fvar sb)" and "pa \<notin> FV (Fvar pb)" and
    "pb \<notin> FV (Fvar sa)" and "pb \<notin> FV (Fvar pa)" and
    "sb \<notin> FV (Fvar sa)" and "sb \<notin> FV (Fvar pa)" and

    "lc s" and "lc p" and "lc s'" and "lc p'"

    using contra_subsetD[OF sopen_FV] assms(1-4)
    by auto

(* proof:

{n \<rightarrow> [s,p]} {k \<rightarrow> [s',p']} t 
= {n \<rightarrow> [s,p]} [sa \<rightarrow> s'] [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} t
= [sa \<rightarrow> s'] [pa \<rightarrow> p'] [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} t
= [sb \<rightarrow> s] [pb \<rightarrow> p] {n \<rightarrow> [Fvar sb,Fvar pb]} [sa \<rightarrow> s'] [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} t
= [sb \<rightarrow> s] [pb \<rightarrow> p] [sa \<rightarrow> s'] {n \<rightarrow> [Fvar sb,Fvar pb]} [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} t
= [sb \<rightarrow> s] [pb \<rightarrow> p] [sa \<rightarrow> s'] [pa \<rightarrow> p'] {n \<rightarrow> [Fvar sb,Fvar pb]} {k \<rightarrow> [Fvar sa,Fvar pa]} t
= [sb \<rightarrow> s] [pb \<rightarrow> p] [sa \<rightarrow> s'] [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} {n \<rightarrow> [Fvar sb,Fvar pb]} t
= [sb \<rightarrow> s] [sa \<rightarrow> s'] [pb \<rightarrow> p] [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} {n \<rightarrow> [Fvar sb,Fvar pb]} t
= [sa \<rightarrow> s'] [sb \<rightarrow> s] [pb \<rightarrow> p] [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} {n \<rightarrow> [Fvar sb,Fvar pb]} t
= [sa \<rightarrow> s'] [sb \<rightarrow> s] [pa \<rightarrow> p'] [pb \<rightarrow> p] {k \<rightarrow> [Fvar sa,Fvar pa]} {n \<rightarrow> [Fvar sb,Fvar pb]} t
= [sa \<rightarrow> s'] [pa \<rightarrow> p'] [sb \<rightarrow> s] [pb \<rightarrow> p] {k \<rightarrow> [Fvar sa,Fvar pa]} {n \<rightarrow> [Fvar sb,Fvar pb]} t
= [sa \<rightarrow> s'] [pa \<rightarrow> p'] [sb \<rightarrow> s] {k \<rightarrow> [Fvar sa,Fvar pa]} [pb \<rightarrow> p] {n \<rightarrow> [Fvar sb,Fvar pb]} t
= [sa \<rightarrow> s'] [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} [sb \<rightarrow> s] [pb \<rightarrow> p] {n \<rightarrow> [Fvar sb,Fvar pb]} t
= [sa \<rightarrow> s'] [pa \<rightarrow> p'] {k \<rightarrow> [Fvar sa,Fvar pa]} {n \<rightarrow> [s,p]} t
= {k \<rightarrow> [s',p']} {n \<rightarrow> [s,p]} t 
*)
  from 
    ssubst_intro[OF \<open>sa \<notin> FV t\<close> \<open>pa \<notin> FV t\<close> \<open>sa \<noteq> pa\<close> \<open>sa \<notin> FV p'\<close>] 
    ssubst_intro[OF \<open>sb \<notin> FV ({k \<rightarrow> [s',p']} t)\<close> \<open>pb \<notin> FV ({k \<rightarrow> [s',p']} t)\<close> 
                    \<open>sb \<noteq> pb\<close> \<open>sb \<notin> FV p\<close>]
    sym[OF ssubst_sopen_commute[OF \<open>lc s'\<close> 
                                   \<open>sa \<notin> FV (Fvar sb)\<close> \<open>sa \<notin> FV (Fvar pb)\<close>]]
    sym[OF ssubst_sopen_commute[OF \<open>lc p'\<close> 
                                   \<open>pa \<notin> FV (Fvar sb)\<close> \<open>pa \<notin> FV (Fvar pb)\<close>]]
    sopen_commute[OF \<open>n \<noteq> k\<close>]
    ssubst_commute[OF \<open>pb \<noteq> sa\<close> \<open>pb \<notin> FV s'\<close> \<open>sa \<notin> FV p\<close>]
    ssubst_commute[OF \<open>sb \<noteq> sa\<close> \<open>sb \<notin> FV s'\<close> \<open>sa \<notin> FV s\<close>]
    ssubst_commute[OF \<open>pb \<noteq> pa\<close> \<open>pb \<notin> FV p'\<close> \<open>pa \<notin> FV p\<close>]
    ssubst_commute[OF \<open>sb \<noteq> pa\<close> \<open>sb \<notin> FV p'\<close> \<open>pa \<notin> FV s\<close>]
    ssubst_sopen_commute[OF \<open>lc s\<close> \<open>sb \<notin> FV (Fvar sa)\<close> \<open>sb \<notin> FV (Fvar pa)\<close>] 
    ssubst_sopen_commute[OF \<open>lc p\<close> \<open>pb \<notin> FV (Fvar sa)\<close> \<open>pb \<notin> FV (Fvar pa)\<close>] 
    sym[OF ssubst_intro[OF \<open>sb \<notin> FV t\<close> \<open>pb \<notin> FV t\<close> \<open>sb \<noteq> pb\<close> \<open>sb \<notin> FV p\<close>]] 
    sym[OF ssubst_intro[OF \<open>sa \<notin> FV ({n \<rightarrow> [s,p]} t)\<close> \<open>pa \<notin> FV ({n \<rightarrow> [s,p]} t)\<close>
                           \<open>sa \<noteq> pa\<close> \<open>sa \<notin> FV p'\<close>]]
  show "{n \<rightarrow> [s,p]} {k \<rightarrow> [s',p']} t = {k \<rightarrow> [s',p']} {n \<rightarrow> [s,p]} t"
    by force
qed

lemma ssubst_preserves_lc[simp, rule_format]:
  fixes t
  assumes "lc t"
  shows "\<forall>x t'. lc t' \<longrightarrow> lc ([x \<rightarrow> t'] t)"
proof -
  define pred_cof
    where "pred_cof L t \<longleftrightarrow> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> lc (t\<^bsup>[Fvar s, Fvar p]\<^esup>))" for L t

  {
    fix x v t
    assume 
      "lc v" and
      "\<forall>x v. lc v \<longrightarrow> (\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> v] t))"
    hence
      "\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> v] t)"
        by auto
  }note Lex = this

  from assms show ?thesis
  proof 
    (induct
      taking: "\<lambda>t. \<forall>x t'. lc t' \<longrightarrow> (\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> t'] t))"
      rule: lc_induct)
    case Fvar thus ?case by simp
  next
    case Call thus ?case by simp
  next
    case (Upd t l u) note pred_t = this(2) and pred_bnd = this(3)
    show ?case
    proof (intro strip)
      fix x t' assume "lc t'"
      note Lex[OF this pred_bnd] 
      from this[of x] 
      obtain L where "finite L" and "pred_cof L ([x \<rightarrow> t'] u)"
        by auto
      with \<open>lc t'\<close> pred_t show "lc ([x \<rightarrow> t'] Upd t l u)" 
        unfolding pred_cof_def
        by simp
    qed
  next
    case (Obj f T) note pred = this
    show ?case
    proof (intro strip)
      fix x t' assume "lc t'"
      define pred_fl where "pred_fl s p b l = lc ([x \<rightarrow> t'] the b\<^bsup>[Fvar s, Fvar p]\<^esup>)"
        for s p b and l::Label

      from \<open>lc t'\<close> fmap_ball_all2[OF pred]
      have "\<forall>l\<in>dom f. \<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> t'] the(f l))"
        unfolding pred_cof_def
        by simp
      with fmap_ex_cof[of f pred_fl]
      obtain L where 
        "finite L" and "\<forall>l\<in>dom f. pred_cof L ([x \<rightarrow> t'] the(f l))"
        unfolding pred_cof_def pred_fl_def
        by auto
      with pred_ssubstoption_lem[of x t' f "pred_cof L"]
      show "lc ([x \<rightarrow> t'] Obj f T)"
        unfolding pred_cof_def
        by simp
    qed
  next
    case (Bnd L t) note pred = this(2)
    show ?case
    proof (intro strip)
      fix x t' assume "lc t'"
      with \<open>finite L\<close> show "\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> t'] t)"
        unfolding pred_cof_def
      proof (
          rule_tac x = "L \<union> {x}" in exI, 
          intro conjI, simp, intro strip)
        fix s p assume sp: "s \<notin> L \<union> {x} \<and> p \<notin> L \<union> {x} \<and> s \<noteq> p"
        hence "x \<notin> FV (Fvar s)" and "x \<notin> FV (Fvar p)"
          by auto
        from sp pred \<open>lc t'\<close>
        have "lc ([x \<rightarrow> t'] (t\<^bsup>[Fvar s,Fvar p]\<^esup>))"
          by blast
        with ssubst_sopen_commute[OF \<open>lc t'\<close> \<open>x \<notin> FV (Fvar s)\<close> 
                                     \<open>x \<notin> FV (Fvar p)\<close>]
        show "lc ([x \<rightarrow> t'] t\<^bsup>[Fvar s,Fvar p]\<^esup>)"
          by (auto simp: openz_def)
      qed
    qed
  qed
qed

lemma sopen_sclose_eq_ssubst: "\<lbrakk> sa \<noteq> pa; sa \<notin> FV p; lc t \<rbrakk> 
  \<Longrightarrow> {n \<rightarrow> [s,p]} {n \<leftarrow> [sa,pa]} t = [sa \<rightarrow> s] [pa \<rightarrow> p] t"
  by (rule_tac sa1 = sa and pa1 = pa and t1 = "{n \<leftarrow> [sa,pa]} t" 
    in ssubst[OF ssubst_intro], simp+)

lemma ssubst_sclose_commute[rule_format]:
  "\<forall>x n s p t'. s \<notin> FV t' \<longrightarrow> p \<notin> FV t' \<longrightarrow> x \<noteq> s \<longrightarrow> x \<noteq> p 
     \<longrightarrow> [x \<rightarrow> t'] {n \<leftarrow> [s,p]} t = {n \<leftarrow> [s,p]} [x \<rightarrow> t'] t"
proof -
  have
    "(\<forall>x n s p t'. s \<notin> FV t' \<longrightarrow> p \<notin> FV t' \<longrightarrow> x \<noteq> s \<longrightarrow> x \<noteq> p 
       \<longrightarrow> [x \<rightarrow> t'] {n \<leftarrow> [s,p]} t = {n \<leftarrow> [s,p]} [x \<rightarrow> t'] t)
    &(\<forall>x n s p t'. s \<notin> FV t' \<longrightarrow> p \<notin> FV t' \<longrightarrow> x \<noteq> s \<longrightarrow> x \<noteq> p 
       \<longrightarrow> ssubst_option x t' (sclose_option n s p u) 
           = sclose_option n s p (ssubst_option x t' u))"
    by (rule compat_sterm_sterm_option.induct, simp_all split: bVariable.split)
  from conjunct1[OF this] show ?thesis by assumption
qed

lemma body_lc_FV: 
  fixes t s p
  assumes "body t"
  shows "lc (t\<^bsup>[Fvar s, Fvar p]\<^esup>)"
proof -
  from assms 
  obtain L where 
    "finite L" and pred_sp: "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> lc (t\<^bsup>[Fvar s,Fvar p]\<^esup>)"
    unfolding body_def by auto

  hence "finite (L \<union> FV t \<union> {s} \<union> {p})" by simp
  from exFresh_s_p_cof[OF this] obtain sa pa where sapa: 
    "sa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> pa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa"
    by auto
  hence "sa \<notin> FV t" and "pa \<notin> FV t" and "sa \<noteq> pa" and "sa \<notin> FV (Fvar p)" by auto
  from pred_sp sapa have "lc (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)" by blast

  with 
    ssubst_intro[OF \<open>sa \<notin> FV t\<close> \<open>pa \<notin> FV t\<close> \<open>sa \<noteq> pa\<close> \<open>sa \<notin> FV (Fvar p)\<close>] 
    ssubst_preserves_lc
  show "lc (t\<^bsup>[Fvar s,Fvar p]\<^esup>)" by (auto simp: openz_def)
qed

lemma body_lc: 
  fixes t s p
  assumes "body t" and "lc s" and "lc p"
  shows "lc (t\<^bsup>[s, p]\<^esup>)"
proof -
  have "finite (FV t \<union> FV p)" by simp
  from exFresh_s_p_cof[OF this] obtain sa pa where
    "sa \<notin> FV t \<union> FV p \<and> pa \<notin> FV t \<union> FV p \<and> sa \<noteq> pa" by auto
  hence "sa \<notin> FV t" and "pa \<notin> FV t" and "sa \<noteq> pa" and "sa \<notin> FV p" 
    by auto

  from body_lc_FV[OF \<open>body t\<close>] have lc: "lc (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)"
    by assumption

  from
    ssubst_intro[OF \<open>sa \<notin> FV t\<close> \<open>pa \<notin> FV t\<close> \<open>sa \<noteq> pa\<close> \<open>sa \<notin> FV p\<close>] 
    ssubst_preserves_lc[OF lc] \<open>lc s\<close> \<open>lc p\<close>
  show "lc (t\<^bsup>[s,p]\<^esup>)" by (auto simp: openz_def)
qed

lemma lc_body: 
  fixes t s p
  assumes "lc t" and "s \<noteq> p"
  shows "body (\<sigma>[s,p] t)"
  unfolding body_def
proof 
  have 
    "\<forall>sa pa. sa \<notin> FV t \<union> {s} \<union> {p} \<and> pa \<notin> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa
      \<longrightarrow> lc (\<sigma>[s,p] t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)"
  proof (intro strip)
    fix sa :: fVariable and pa :: fVariable
    assume "sa \<notin> FV t \<union> {s} \<union> {p} \<and> pa \<notin> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa"
    hence "s \<notin> FV (Fvar pa)" by auto
    from 
      sopen_sclose_eq_ssubst[OF \<open>s \<noteq> p\<close> this \<open>lc t\<close>] 
      ssubst_preserves_lc[OF \<open>lc t\<close>]
    show "lc (\<sigma>[s,p] t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)" by (simp add: openz_def closez_def)
  qed
  thus 
    "finite (FV t \<union> {s} \<union> {p}) 
     \<and> (\<forall>sa pa. sa \<notin> FV t \<union> {s} \<union> {p} \<and> pa \<notin> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa
         \<longrightarrow> lc (\<sigma>[s,p] t\<^bsup>[Fvar sa,Fvar pa]\<^esup>))" by simp
qed

lemma ssubst_preserves_lcE_lem[rule_format]:
  fixes t
  assumes "lc t"
  shows "\<forall>x u t'. t = [x \<rightarrow> u] t' \<longrightarrow> lc u \<longrightarrow> lc t'"
  using assms
proof 
  (induct
    taking: 
    "\<lambda>t. \<forall>x u t'. t = [x \<rightarrow> u] t' \<longrightarrow> lc u \<longrightarrow> body t'" 
    rule: lc_induct)
  case Fvar thus ?case by (intro strip, case_tac t', simp_all)
next
  case Call thus ?case by (intro strip, case_tac t', simp_all)
next
  case (Upd t l u) note pred_t = this(2) and pred_u = this(3) 
  show ?case
  proof (intro strip)
    fix x v t'' assume "Upd t l u = [x \<rightarrow> v] t''" and "lc v"
    from this(1) have t'': "(\<exists>t' u'. t'' = Upd t' l u') \<or> (t'' = Fvar x)"
    proof (cases t'', auto)
      fix y
      assume "Upd t l u = (if x = y then v else Fvar y)"
      thus "y = x" by (case_tac "y = x", auto)
    qed
    show "lc t''"
    proof (cases "t'' = Fvar x")
      case True thus ?thesis by simp
    next
      case False with \<open>Upd t l u = [x \<rightarrow> v] t''\<close> t'' 
      show ?thesis
      proof (clarify)
        fix t' u' assume "Upd t l u = [x \<rightarrow> v] Upd t' l u'"
        hence "t = [x \<rightarrow> v] t'" and "u = [x \<rightarrow> v] u'" 
          by auto
        with \<open>lc v\<close> pred_t pred_u lc_upd[of t' l u']
        show "lc (Upd t' l u')" by auto
      qed
    qed
  qed
next
  case (Obj f T) note pred = this
  show ?case
  proof (intro strip)
    fix x v t' assume "Obj f T = [x \<rightarrow> v] t'" and "lc v"
    from this(1) have t': "(\<exists>f'. t' = Obj f' T) \<or> (t' = Fvar x)"
    proof (cases t', auto)
      fix y :: fVariable
      assume "Obj f T = (if x = y then v else Fvar y)"
      thus "y = x" by (case_tac "y = x", auto)
    qed
    show "lc t'"
    proof (cases "t' = Fvar x")
      case True thus ?thesis by simp
    next
      case False with \<open>Obj f T = [x \<rightarrow> v] t'\<close> t'
      show ?thesis
      proof (clarify)
        fix f' assume "Obj f T = [x \<rightarrow> v] Obj f' T"
        hence
          ssubst: "\<forall>l\<in>dom f. the(f l) = [x \<rightarrow> v] the(f' l)" and
          "dom f = dom f'"
          by auto
        with pred \<open>lc v\<close> lc_obj[of f' T]
        show "lc (Obj f' T)"
          by auto
      qed
    qed
  qed
next
  case (Bnd L t) note pred = this(2)
  show ?case
  proof (intro strip)
    fix x v t' assume "t = [x \<rightarrow> v] t'" and "lc v"
    from \<open>finite L\<close> exFresh_s_p_cof[of "L \<union> {x} \<union> FV t'"]
    obtain s p where 
      "s \<notin> L" and "p \<notin> L" and "s \<noteq> p" and
      "x \<notin> FV (Fvar s)" and "x \<notin> FV (Fvar p)" and
      "s \<notin> FV t'" and "p \<notin> FV t'"
      by auto
    from 
      \<open>t = [x \<rightarrow> v] t'\<close>
      ssubst_sopen_commute[OF \<open>lc v\<close> \<open>x \<notin> FV (Fvar s)\<close> \<open>x \<notin> FV (Fvar p)\<close>]
    have "(t\<^bsup>[Fvar s, Fvar p]\<^esup>) = [x \<rightarrow> v] (t'\<^bsup>[Fvar s, Fvar p]\<^esup>)"
      by (auto simp: openz_def)
    with 
      \<open>s \<notin> L\<close> \<open>p \<notin> L\<close> \<open>s \<noteq> p\<close> \<open>lc v\<close> pred
    have "lc (t'\<^bsup>[Fvar s, Fvar p]\<^esup>)" by blast
    from 
      lc_body[OF this \<open>s \<noteq> p\<close>]
      sclose_sopen_eq_t[OF \<open>s \<notin> FV t'\<close> \<open>p \<notin> FV t'\<close> \<open>s \<noteq> p\<close>]
    show "body t'" by (auto simp: openz_def closez_def)
  qed
qed

lemma ssubst_preserves_lcE: "\<lbrakk> lc ([x \<rightarrow> t'] t); lc t' \<rbrakk> \<Longrightarrow> lc t"
  by (drule_tac t = "[x \<rightarrow> t'] t" and x = x and u = t' and t' = t 
    in ssubst_preserves_lcE_lem, simp+)

lemma obj_openz_lc: "\<lbrakk> lc (Obj f T); lc p; l \<in> dom f \<rbrakk> \<Longrightarrow> lc (the(f l)\<^bsup>[Obj f T, p]\<^esup>)"
  by (rule_tac s = "Obj f T" and p = p in body_lc, (simp add: lc_obj)+)

lemma obj_insert_lc: 
  fixes f T t l
  assumes "lc (Obj f T)" and "body t"
  shows "lc (Obj (f(l \<mapsto> t)) T)"
proof (rule ssubst[OF lc_obj], rule ballI)
  fix l' :: Label assume "l' \<in> dom (f(l \<mapsto> t))"
  with assms show "body (the ((f(l \<mapsto> t)) l'))"
    by (cases "l' = l", (auto simp: lc_obj))
qed

lemma ssubst_preserves_body[simp]:
  fixes t t' x
  assumes "body t" and "lc t'"
  shows "body ([x \<rightarrow> t'] t)"
  unfolding body_def
proof -
  have 
    "\<forall>s p. s \<notin> FV t' \<union> {x} \<and> p \<notin> FV t' \<union> {x} \<and> s \<noteq> p
      \<longrightarrow> lc ([x \<rightarrow> t'] t\<^bsup>[Fvar s,Fvar p]\<^esup>)"
  proof (intro strip)
    fix s :: fVariable and p :: fVariable
    from body_lc_FV[OF \<open>body t\<close>]
    have "lc ({0 \<rightarrow> [Fvar s,Fvar p]} t)" by (simp add: openz_def)
    from ssubst_preserves_lc[OF this \<open>lc t'\<close>] 
    have "lc ([x \<rightarrow> t'] (t\<^bsup>[Fvar s,Fvar p]\<^esup>))" by (simp add: openz_def)

    moreover assume "s \<notin> FV t' \<union> {x} \<and> p \<notin> FV t' \<union> {x} \<and> s \<noteq> p"
    hence "x \<notin> FV (Fvar s)" and "x \<notin> FV (Fvar p)" by auto
    note ssubst_sopen_commute[OF \<open>lc t'\<close> this]
    ultimately
    show "lc ([x \<rightarrow> t'] t\<^bsup>[Fvar s,Fvar p]\<^esup>)" by (simp add: openz_def)
  qed
  thus 
    "\<exists>L. finite L \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                      \<longrightarrow> lc ([x \<rightarrow> t'] t\<^bsup>[Fvar s,Fvar p]\<^esup>))"
    by (rule_tac x = "FV t' \<union> {x}" in exI, simp)
qed

lemma sopen_preserves_body[simp]:
  fixes t s p
  assumes "body t" and "lc s" and "lc p"
  shows "body ({n \<rightarrow> [s,p]} t)"
  unfolding body_def
proof -
  have 
    "\<forall>sa pa. sa \<notin> FV t \<union> FV s \<and> pa \<notin> FV p \<and> sa \<noteq> pa
      \<longrightarrow> lc ({n \<rightarrow> [s,p]} t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)"
  proof (cases "n = 0")
    case True thus ?thesis
      using body_lc[OF \<open>body t\<close> \<open>lc s\<close> \<open>lc p\<close>] sopen_twice[OF \<open>lc s\<close> \<open>lc p\<close>] 
      by (simp add: openz_def)
  next
    case False thus ?thesis
    proof (intro strip)
      fix sa :: fVariable and pa :: fVariable
      from body_lc_FV[OF \<open>body t\<close>] have "lc (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)" by assumption
      moreover
      from sopen_commute_gen[OF _ _ \<open>lc s\<close> \<open>lc p\<close> not_sym[OF \<open>n \<noteq> 0\<close>]]
      have "{n \<rightarrow> [s,p]} t\<^bsup>[Fvar sa,Fvar pa]\<^esup> = {n \<rightarrow> [s,p]} (t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)"
        by (simp add: openz_def)
      ultimately show "lc ({n \<rightarrow> [s,p]} t\<^bsup>[Fvar sa,Fvar pa]\<^esup>)" by simp
    qed
  qed
  thus "\<exists>L. finite L 
          \<and> (\<forall>sa pa. sa \<notin> L \<and> pa \<notin> L \<and> sa \<noteq> pa 
              \<longrightarrow> lc ({n \<rightarrow> [s,p]} t\<^bsup>[Fvar sa,Fvar pa]\<^esup>))"
    by (rule_tac x = "FV t \<union> FV s \<union> FV p" in exI, simp)
qed

subsection \<open>Beta-reduction\<close>
inductive beta :: "[sterm, sterm] \<Rightarrow> bool" (infixl "\<rightarrow>\<^sub>\<beta>" 50)
where
  beta[simp, intro!]      : 
  "\<lbrakk> l \<in> dom f; lc (Obj f T); lc a \<rbrakk> \<Longrightarrow> Call (Obj f T) l a \<rightarrow>\<^sub>\<beta> (the (f l)\<^bsup>[(Obj f T), a]\<^esup>)"
| beta_Upd[simp, intro!]  : 
  "\<lbrakk> l \<in> dom f; lc (Obj f T); body t \<rbrakk> \<Longrightarrow> Upd (Obj f T) l t \<rightarrow>\<^sub>\<beta> Obj (f(l \<mapsto> t)) T" 
| beta_CallL[simp, intro!]: "\<lbrakk> t \<rightarrow>\<^sub>\<beta> t'; lc u \<rbrakk> \<Longrightarrow> Call t l u \<rightarrow>\<^sub>\<beta> Call t' l u"
| beta_CallR[simp, intro!]: "\<lbrakk> t \<rightarrow>\<^sub>\<beta> t'; lc u \<rbrakk> \<Longrightarrow> Call u l t \<rightarrow>\<^sub>\<beta> Call u l t'"
| beta_UpdL[simp, intro!] : "\<lbrakk> t \<rightarrow>\<^sub>\<beta> t'; body u \<rbrakk> \<Longrightarrow> Upd t l u \<rightarrow>\<^sub>\<beta> Upd t' l u"
| beta_UpdR[simp, intro!] : 
  "\<lbrakk> finite L; 
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t''\<and> t'= \<sigma>[s,p]t'');
     lc u \<rbrakk> \<Longrightarrow> Upd u l t \<rightarrow>\<^sub>\<beta> Upd u l t'"
| beta_Obj[simp, intro!]  : 
  "\<lbrakk> l \<in> dom f; finite L; 
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> t'= \<sigma>[s,p]t'');
     \<forall>l\<in>dom f. body (the (f l)) \<rbrakk> 
  \<Longrightarrow> Obj (f(l \<mapsto> t)) T \<rightarrow>\<^sub>\<beta> Obj (f(l \<mapsto> t')) T"

inductive_cases beta_cases [elim!]:
  "Call s l t \<rightarrow>\<^sub>\<beta> u"
  "Upd s l t \<rightarrow>\<^sub>\<beta> u"
  "Obj s T  \<rightarrow>\<^sub>\<beta> t"

abbreviation
  beta_reds :: "[sterm, sterm] => bool"  (infixl "->>" 50) where
  "s ->> t == beta^** s t"
abbreviation
  beta_ascii :: "[sterm, sterm] => bool"  (infixl "->" 50) where
  "s -> t == beta s t"

notation (latex)
  beta_reds (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50)

lemma beta_induct[consumes 1, 
  case_names CallL CallR UpdL UpdR Upd Obj beta Bnd]:
  fixes 
  t :: sterm and t' :: sterm and 
  P1 :: "sterm \<Rightarrow> sterm \<Rightarrow> bool" and P2 :: "sterm \<Rightarrow> sterm \<Rightarrow> bool"
  assumes
  "t \<rightarrow>\<^sub>\<beta> t'" and
  "\<And>t t' u l. \<lbrakk> t \<rightarrow>\<^sub>\<beta> t'; P1 t t'; lc u \<rbrakk> \<Longrightarrow> P1 (Call t l u) (Call t' l u)" and
  "\<And>t t' u l. \<lbrakk> t \<rightarrow>\<^sub>\<beta> t'; P1 t t'; lc u \<rbrakk> \<Longrightarrow> P1 (Call u l t) (Call u l t')" and
  "\<And>t t' u l. \<lbrakk> t \<rightarrow>\<^sub>\<beta> t'; P1 t t'; body u\<rbrakk> \<Longrightarrow> P1 (Upd t l u) (Upd t' l u)" and
  "\<And>t t' u l. \<lbrakk> P2 t t'; lc u \<rbrakk> \<Longrightarrow> P1 (Upd u l t) (Upd u l t')" and
  "\<And>l f T t. \<lbrakk> l \<in> dom f; lc (Obj f T); body t \<rbrakk> 
      \<Longrightarrow> P1 (Upd (Obj f T) l t) (Obj (f(l \<mapsto> t)) T)" and
  "\<And>l f t t' T. \<lbrakk> l \<in> dom f; P2 t t'; \<forall>l\<in>dom f. body (the (f l)) \<rbrakk>
      \<Longrightarrow> P1 (Obj (f(l \<mapsto> t)) T) (Obj (f(l \<mapsto> t')) T)" and
  "\<And>l f T a. \<lbrakk> l \<in> dom f; lc (Obj f T); lc a \<rbrakk> 
      \<Longrightarrow> P1 (Call (Obj f T) l a) (the (f l)\<^bsup>[Obj f T,a]\<^esup>)" and
  "\<And>L t t'. 
      \<lbrakk> finite L; 
        \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
        \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t'' 
                 \<and> P1 (t\<^bsup>[Fvar s,Fvar p]\<^esup>) t'' \<and> t' = \<sigma>[s,p] t'') \<rbrakk>
      \<Longrightarrow> P2 t t'"
  shows "P1 t t'"
  using assms by (induct rule: beta.induct, auto)

lemma Fvar_beta: "Fvar x \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> False"
  by (erule beta.cases, auto)

lemma Obj_beta: 
  assumes "Obj f T \<rightarrow>\<^sub>\<beta> z"
  shows
  "\<exists>l f' t t'. dom f = dom f' \<and> f = (f'(l \<mapsto> t)) \<and> l \<in> dom f' 
             \<and> (\<exists>L. finite L 
                  \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
                      \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> t'= \<sigma>[s,p]t'')))
             \<and> z = Obj (f'(l \<mapsto> t')) T"
proof (cases rule: beta_cases(3)[OF assms])
  case (1 l fa L t t') thus ?thesis
    by (rule_tac x = l in exI, 
        rule_tac x = fa in exI,
        rule_tac x = t in exI,
        rule_tac x = t' in exI, auto)
qed

lemma Upd_beta: "Upd t l u \<rightarrow>\<^sub>\<beta> z \<Longrightarrow>
  (\<exists>t'. t \<rightarrow>\<^sub>\<beta> t' \<and> z = Upd t' l u) 
  \<or>(\<exists>u' L. finite L 
         \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
             \<longrightarrow> (\<exists>t''. (u\<^bsup>[Fvar s, Fvar p]\<^esup>) \<rightarrow>\<^sub>\<beta> t'' \<and> u' = \<sigma>[s,p]t'')) 
         \<and> z = Upd t l u')
  \<or>(\<exists>f T. l \<in> dom f \<and> Obj f T = t \<and> z = Obj (f(l \<mapsto> u)) T)"
  by (erule beta_cases, auto)

lemma Call_beta: "Call t l u \<rightarrow>\<^sub>\<beta> z \<Longrightarrow>
  (\<exists>t'. t \<rightarrow>\<^sub>\<beta> t' \<and> z = Call t' l u) \<or> (\<exists>u'. u \<rightarrow>\<^sub>\<beta> u' \<and> z = Call t l u')
  \<or>(\<exists>f T. Obj f T = t \<and> l \<in> dom f \<and> z = (the (f l)\<^bsup>[Obj f T, u]\<^esup>))"
  by (erule beta_cases, auto)

subsubsection \<open>Properties\<close>
lemma beta_lc[simp]:
  fixes t t'
  assumes "t \<rightarrow>\<^sub>\<beta> t'"
  shows "lc t \<and> lc t'"
using assms
proof 
  (induct
    taking: "\<lambda>t t'. body t \<and> body t'"
    rule: beta_induct)
  case CallL thus ?case by simp
next
  case CallR thus ?case by simp
next
  case UpdR thus ?case by (simp add: lc_upd)
next
  case UpdL thus ?case by (simp add: lc_upd)
next
  case beta thus ?case by (simp add: obj_openz_lc)
next
  case Upd thus ?case by (simp add: lc_obj lc_upd)
next
  case Obj thus ?case by (simp add: lc_obj)
next
  case (Bnd L t t') note cof = this(2)
  from \<open>finite L\<close> exFresh_s_p_cof[of "L \<union> FV t"]
  obtain s p where 
    "s \<notin> L" and "s \<notin> FV t" and "p \<notin> L" and "p \<notin> FV t" and "s \<noteq> p" 
    by auto  
  with cof obtain t'' where
    "lc (t\<^bsup>[Fvar s, Fvar p]\<^esup>)" and "lc t''" and
    "t' = \<sigma>[s,p] t''" by auto
  from 
    lc_body[OF this(1) \<open>s \<noteq> p\<close>] 
    sclose_sopen_eq_t[OF \<open>s \<notin> FV t\<close> \<open>p \<notin> FV t\<close> \<open>s \<noteq> p\<close>]
    this(3) lc_body[OF this(2) \<open>s \<noteq> p\<close>]
  show ?case by (simp add: openz_def closez_def)
qed

lemma beta_ssubst[rule_format]:
  fixes t t'
  assumes "t \<rightarrow>\<^sub>\<beta> t'"
  shows "\<forall>x v. lc v \<longrightarrow> [x \<rightarrow> v] t \<rightarrow>\<^sub>\<beta> [x \<rightarrow> v] t'"
proof -
  define pred_cof
    where "pred_cof L t t' \<longleftrightarrow>
      (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s, Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> t' = \<sigma>[s,p] t''))"
    for L t t'
  {
    fix x v t t'
    assume 
      "lc v" and
      "\<forall>x v. lc v \<longrightarrow> (\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v] t'))"
    hence
      "\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v] t')"
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
      taking: "\<lambda>t t'. \<forall>x v. lc v 
                       \<longrightarrow> (\<exists>L. finite L 
                              \<and> pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v] t'))"
      rule: beta_induct)
    case CallL thus ?case by simp
  next
    case CallR thus ?case by simp
  next
    case UpdL thus ?case by simp
  next
    case (UpdR t t' u l) note pred = this(1)
    show ?case
    proof (intro strip)
      fix x v assume "lc v"
      from Lex[OF this pred]
      obtain L where
        "finite L" and "pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v] t')"
        by auto
      with ssubst_preserves_lc[OF \<open>lc u\<close> \<open>lc v\<close>] 
      show "[x \<rightarrow> v] Upd u l t \<rightarrow>\<^sub>\<beta> [x \<rightarrow> v] Upd u l t'"
        unfolding pred_cof_def
        by auto
    qed
  next
    case (beta l f T t) thus ?case
    proof (intro strip, simp)
      fix x v assume "lc v"
      from ssubst_preserves_lc[OF \<open>lc t\<close> this] have "lc ([x \<rightarrow> v] t)" 
        by simp
      note lem =
        beta.beta[OF domssubst[OF \<open>l \<in> dom f\<close>] 
        lcobj[OF \<open>lc (Obj f T)\<close> \<open>lc v\<close>] this]

      from \<open>l \<in> dom f\<close> have "the (ssubst_option x v (f l)) = [x \<rightarrow> v] the (f l)"
        by auto
      with lem[of x] ssubst_openz_distrib[OF \<open>lc v\<close>]
      show
        "Call (Obj (\<lambda>l. ssubst_option x v (f l)) T) l ([x \<rightarrow> v] t)
         \<rightarrow>\<^sub>\<beta> [x \<rightarrow> v] (the (f l)\<^bsup>[Obj f T, t]\<^esup>)"
        by simp
    qed
  next
    case (Upd l f T t) thus ?case
    proof (intro strip, simp)
      fix x v assume "lc v"
      from ssubst_preserves_body[OF \<open>body t\<close> \<open>lc v\<close>] have "body ([x \<rightarrow> v] t)" 
        by simp
      from
        beta.beta_Upd[OF domssubst[OF \<open>l \<in> dom f\<close>] 
                         lcobj[OF \<open>lc (Obj f T)\<close> \<open>lc v\<close>] this]
        ssubstoption_insert[OF \<open>l \<in> dom f\<close>] 
      show
        "Upd (Obj (\<lambda>l. ssubst_option x v (f l)) T) l ([x \<rightarrow> v] t)
         \<rightarrow>\<^sub>\<beta> Obj (\<lambda>la. ssubst_option x v (if la = l then Some t else f la)) T"
        by simp
    qed
  next
    case (Obj l f t t' T) note pred = this(2)
    show ?case
    proof (intro strip, simp)
      fix x v assume "lc v"
      note Lex[OF this pred]
      from this[of x] obtain L where
        "finite L" and "pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v] t')"
        by auto
      have "\<forall>l\<in>dom (\<lambda>l. ssubst_option x v (f l)). body (the (ssubst_option x v (f l)))"
      proof (intro strip, simp)
        fix l' :: Label assume "l' \<in> dom f"
        with \<open>\<forall>l\<in>dom f. body (the(f l))\<close> have "body (the (f l'))" by blast
        note ssubst_preserves_body[OF this \<open>lc v\<close>]
        with \<open>l' \<in> dom f\<close> ssubst_option_lem
        show "body (the (ssubst_option x v (f l')))" by auto
      qed
      from
        beta.beta_Obj[OF domssubst[OF \<open>l \<in> dom f\<close>] \<open>finite L\<close> _ this] 
        ssubstoption_insert[OF \<open>l \<in> dom f\<close>] \<open>pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v] t')\<close>
      show 
        "Obj (\<lambda>la. ssubst_option x v (if la = l then Some t else f la)) T
         \<rightarrow>\<^sub>\<beta> Obj (\<lambda>la. ssubst_option x v (if la = l then Some t' else f la)) T"
        unfolding pred_cof_def
        by simp
    qed
  next
    case (Bnd L t t') note pred = this(2)
    show ?case
    proof (intro strip)
      fix x v assume "lc v"
      from \<open>finite L\<close>
      show "\<exists>L. finite L \<and> pred_cof L ([x \<rightarrow> v] t) ([x \<rightarrow> v] t')"
      proof (rule_tac x = "L \<union> {x} \<union> FV v" in exI, 
          unfold pred_cof_def, auto)
        fix s p assume "s \<notin> L" and "p \<notin> L" and "s \<noteq> p"
        with pred \<open>lc v\<close> obtain t'' where
          "t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t''" and
          ssubst_beta: "[x \<rightarrow> v] (t\<^bsup>[Fvar s,Fvar p]\<^esup>) \<rightarrow>\<^sub>\<beta> [x \<rightarrow> v] t''" and
          "t' = \<sigma>[s,p] t''"
          by blast
        assume "s \<noteq> x" and "p \<noteq> x"
        hence "x \<notin> FV (Fvar s)" and "x \<notin> FV (Fvar p)" by auto
        from ssubst_sopen_commute[OF \<open>lc v\<close> this] ssubst_beta
        have "[x \<rightarrow> v] t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> [x \<rightarrow> v] t''" 
          by (simp add: openz_def)
        moreover
        assume "s \<notin> FV v" and "p \<notin> FV v"
        from 
          ssubst_sclose_commute[OF this not_sym[OF \<open>s \<noteq> x\<close>] 
                                        not_sym[OF \<open>p \<noteq> x\<close>]] 
          \<open>t' = \<sigma>[s,p] t''\<close>
        have "[x \<rightarrow> v] t' = \<sigma>[s,p] [x \<rightarrow> v] t''" 
          by (simp add: closez_def)
        ultimately
        show "\<exists>t''. [x \<rightarrow> v] t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> [x \<rightarrow> v] t' = \<sigma>[s,p] t''" 
          by (rule_tac x = "[x \<rightarrow> v] t''" in exI, simp)
      qed
    qed
  qed
qed

declare if_not_P [simp] not_less_eq [simp]
  \<comment> \<open>don't add @{text "r_into_rtrancl[intro!]"}\<close>

lemma beta_preserves_FV[simp, rule_format]:
  fixes t t' x
  assumes "t \<rightarrow>\<^sub>\<beta> t'"
  shows "x \<notin> FV t \<longrightarrow> x \<notin> FV t'"
using assms
proof 
  (induct
    taking: "\<lambda>t t'. x \<notin> FV t \<longrightarrow> x \<notin> FV t'"
    rule: beta_induct)
  case CallL thus ?case by simp
next
  case CallR thus ?case by simp
next
  case UpdL thus ?case by simp
next
  case UpdR thus ?case by simp
next
  case Upd thus ?case by simp
next
  case Obj thus ?case by simp
next
  case (beta l f T t) thus ?case
  proof (intro strip)
    assume "x \<notin> FV (Call (Obj f T) l t)"
    with \<open>l \<in> dom f\<close> have "x \<notin> FV (the (f l)) \<union> FV (Obj f T) \<union> FV t"
    proof (auto)
      fix y :: sterm
      assume "x \<in> FV y" and "f l = Some y"
      hence "x \<in> FVoption (f l)"
        by auto
      moreover assume "\<forall>l\<in>dom f. x \<notin> FVoption (f l)"
      ultimately show False using \<open>l \<in> dom f\<close>
        by blast
    qed
    from contra_subsetD[OF sopen_FV this]
    show "x \<notin> FV (the (f l)\<^bsup>[Obj f T,t]\<^esup>)" by (simp add: openz_def)
  qed
next
  case (Bnd L t t') thus ?case
  proof (intro strip)
    assume "x \<notin> FV t"
    from \<open>finite L\<close> exFresh_s_p_cof[of "L \<union> {x}"]
    obtain s p where sp: "s \<notin> L \<union> {x} \<and> p \<notin> L \<union> {x} \<and> s \<noteq> p" by auto
    with \<open>x \<notin> FV t\<close> sopen_FV[of 0 "Fvar s" "Fvar p" t]
    have "x \<notin> FV (t\<^bsup>[Fvar s, Fvar p]\<^esup>)" by (auto simp: openz_def)
    with sp Bnd(2) obtain t'' where
      "x \<notin> FV t''" and "t' = \<sigma>[s,p] t''" 
      by auto
    with sclose_subset_FV[of 0 s p t''] show "x \<notin> FV t'" 
      by (auto simp: closez_def)
  qed
qed

lemma rtrancl_beta_lc[simp, rule_format]: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> t \<noteq> t' \<longrightarrow> lc t \<and> lc t'"
  by (erule rtranclp.induct, simp, 
      drule beta_lc, blast)

lemma rtrancl_beta_lc2[simp]: "\<lbrakk> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'; lc t \<rbrakk> \<Longrightarrow> lc t'"
  by (case_tac "t = t'", simp+)

lemma rtrancl_beta_body:
  fixes L t t'
  assumes 
  "finite L" and
  "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
    \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t'' \<and> t' = \<sigma>[s,p] t'')" and
  "body t"
  shows "body t'"
proof (cases "t = t'")
  case True with assms(3) show ?thesis by simp
next
  from exFresh_s_p_cof[OF \<open>finite L\<close>] 
  obtain s p where sp: "s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p" by auto
  hence "s \<noteq> p" by simp

  from assms(2) sp
  obtain t'' where "t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t''" and "t' = \<sigma>[s,p] t''" 
    by auto
  with \<open>body t\<close> have "lc t''"
  proof (cases "(t\<^bsup>[Fvar s,Fvar p]\<^esup>) = t''")
    case True with body_lc[OF \<open>body t\<close>] show "lc t''" by auto
  next
    case False with rtrancl_beta_lc[OF \<open>t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t''\<close>] 
    show "lc t''" by auto
  qed
  from lc_body[OF this \<open>s \<noteq> p\<close>] \<open>t' = \<sigma>[s,p] t''\<close> show "body t'" by simp
qed

lemma rtrancl_beta_preserves_FV[simp, rule_format]: 
  "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> x \<notin> FV t \<longrightarrow> x \<notin> FV t'"
proof (induct t t' rule: rtranclp.induct, simp)
  case (rtrancl_into_rtrancl a b c) thus ?case
  proof (clarify)
    assume "x \<notin> FV b" and "x \<in> FV c"
    from beta_preserves_FV[OF \<open>b \<rightarrow>\<^sub>\<beta> c\<close> this(1)] this(2)
    show False by simp
  qed
qed

subsubsection \<open>Congruence rules\<close>
lemma rtrancl_beta_CallL [intro!, rule_format]:
  "\<lbrakk> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'; lc u \<rbrakk> \<Longrightarrow> Call t l u \<rightarrow>\<^sub>\<beta>\<^sup>* Call t' l u"
proof (induct t t' rule: rtranclp.induct, simp)
  case (rtrancl_into_rtrancl a b c) thus ?case
  proof (auto)
    from \<open>b \<rightarrow>\<^sub>\<beta> c\<close> \<open>lc u\<close> have "Call b l u \<rightarrow>\<^sub>\<beta> Call c l u" by simp
    with rtrancl_into_rtrancl(2)[OF \<open>lc u\<close>]
    show "Call a l u \<rightarrow>\<^sub>\<beta>\<^sup>* Call c l u" by auto
  qed
qed

lemma rtrancl_beta_CallR [intro!, rule_format]:
  "\<lbrakk> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'; lc u \<rbrakk> \<Longrightarrow> Call u l t \<rightarrow>\<^sub>\<beta>\<^sup>* Call u l t'"
proof (induct t t' rule: rtranclp.induct, simp)
  case (rtrancl_into_rtrancl a b c) thus ?case
  proof (auto)
    from \<open>b \<rightarrow>\<^sub>\<beta> c\<close> \<open>lc u\<close> have "Call u l b \<rightarrow>\<^sub>\<beta> Call u l c" by simp
    with rtrancl_into_rtrancl(2)[OF \<open>lc u\<close>]
    show "Call u l a \<rightarrow>\<^sub>\<beta>\<^sup>* Call u l c" by auto
  qed
qed

lemma rtrancl_beta_Call [intro!, rule_format]:
  "\<lbrakk> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'; lc t; u \<rightarrow>\<^sub>\<beta>\<^sup>* u'; lc u \<rbrakk> 
  \<Longrightarrow> Call t l u \<rightarrow>\<^sub>\<beta>\<^sup>* Call t' l u'"
proof (induct t t' rule: rtranclp.induct, blast)
  case (rtrancl_into_rtrancl a b c) thus ?case
  proof (auto)
    from \<open>u \<rightarrow>\<^sub>\<beta>\<^sup>* u'\<close> \<open>lc u\<close> have "lc u'" by auto
    with \<open>b \<rightarrow>\<^sub>\<beta> c\<close> have "Call b l u' \<rightarrow>\<^sub>\<beta> Call c l u'" by simp
    with rtrancl_into_rtrancl(2)[OF \<open>lc a\<close> \<open>u \<rightarrow>\<^sub>\<beta>\<^sup>* u'\<close> \<open>lc u\<close>]
    show "Call a l u \<rightarrow>\<^sub>\<beta>\<^sup>* Call c l u'" by auto
  qed
qed

lemma rtrancl_beta_UpdL:
  "\<lbrakk> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'; body u \<rbrakk> \<Longrightarrow> Upd t l u \<rightarrow>\<^sub>\<beta>\<^sup>* Upd t' l u"
proof (induct t t' rule: rtranclp.induct, simp)
  case (rtrancl_into_rtrancl a b c) thus ?case
  proof (auto)
    from \<open>b \<rightarrow>\<^sub>\<beta> c\<close> \<open>body u\<close> have "Upd b l u \<rightarrow>\<^sub>\<beta> Upd c l u" by simp
    with rtrancl_into_rtrancl(2)[OF \<open>body u\<close>]
    show "Upd a l u \<rightarrow>\<^sub>\<beta>\<^sup>* Upd c l u" by auto
  qed
qed

lemma beta_binder[rule_format]:
  fixes t t'
  assumes "t \<rightarrow>\<^sub>\<beta> t'"
  shows 
  "\<forall>L s p. finite L \<longrightarrow> s \<notin> L \<longrightarrow> p \<notin> L \<longrightarrow> s \<noteq> p 
    \<longrightarrow> (\<exists>L'. finite L' \<and> (\<forall>sa pa. sa \<notin> L' \<and> pa \<notin> L' \<and> sa \<noteq> pa
                            \<longrightarrow> (\<exists>t''. (\<sigma>[s,p] t)\<^bsup>[Fvar sa,Fvar pa]\<^esup> \<rightarrow>\<^sub>\<beta> t'' 
                                     \<and> \<sigma>[s,p] t' = \<sigma>[sa,pa] t'')))"
proof (intro strip)
  fix L :: "fVariable set" and s :: fVariable and p :: fVariable
  assume "s \<noteq> p"
  have 
    "\<forall>sa pa. sa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> pa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa
      \<longrightarrow> (\<exists>t''. (\<sigma>[s,p] t)\<^bsup>[Fvar sa,Fvar pa]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> \<sigma>[s,p] t' = \<sigma>[sa,pa] t'')"
  proof (intro strip)
    fix sa :: fVariable and pa :: fVariable
    from beta_ssubst[OF \<open>t \<rightarrow>\<^sub>\<beta> t'\<close>] 
    have "[p \<rightarrow> Fvar pa] t \<rightarrow>\<^sub>\<beta> [p \<rightarrow> Fvar pa] t'" by simp
    from beta_ssubst[OF this] 
    have 
      betasubst: "[s \<rightarrow> Fvar sa] [p \<rightarrow> Fvar pa] t \<rightarrow>\<^sub>\<beta> [s \<rightarrow> Fvar sa] [p \<rightarrow> Fvar pa] t'" 
      by simp

    from beta_lc[OF \<open>t \<rightarrow>\<^sub>\<beta> t'\<close>] have "lc t" and "lc t'" by auto

    assume 
      sapa: "sa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> pa \<notin> L \<union> FV t \<union> {s} \<union> {p} \<and> sa \<noteq> pa"
    hence "s \<notin> FV (Fvar pa)" by auto
    from 
      sopen_sclose_eq_ssubst[OF \<open>s \<noteq> p\<close> this \<open>lc t\<close>] 
      sopen_sclose_eq_ssubst[OF \<open>s \<noteq> p\<close> this \<open>lc t'\<close>]
      betasubst
    have "\<sigma>[s,p] t\<^bsup>[Fvar sa, Fvar pa]\<^esup> \<rightarrow>\<^sub>\<beta> (\<sigma>[s,p] t'\<^bsup>[Fvar sa, Fvar pa]\<^esup>)"
      by (simp add: openz_def closez_def)

    moreover
    {
      from sapa have "sa \<notin> FV t" by simp
      from 
        contra_subsetD[OF sclose_subset_FV 
                          beta_preserves_FV[OF \<open>t \<rightarrow>\<^sub>\<beta> t'\<close> this]] 
      have "sa \<notin> FV (\<sigma>[s,p] t')" by (simp add: closez_def)
      moreover
      from sapa have "pa \<notin> FV t" by simp
      from 
        contra_subsetD[OF sclose_subset_FV 
                          beta_preserves_FV[OF \<open>t \<rightarrow>\<^sub>\<beta> t'\<close> this]]
      have "pa \<notin> FV (\<sigma>[s,p] t')" by (simp add: closez_def)
      ultimately
      have "sa \<notin> FV (\<sigma>[s,p] t')" and "pa \<notin> FV (\<sigma>[s,p] t')" and "sa \<noteq> pa" 
        using sapa
        by auto
      note sym[OF sclose_sopen_eq_t[OF this]]
    }
    ultimately
    show 
      "\<exists>t''. \<sigma>[s,p] t\<^bsup>[Fvar sa,Fvar pa]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> \<sigma>[s,p] t' = \<sigma>[sa,pa] t''" 
      by (auto simp: openz_def closez_def)
  qed
  moreover assume "finite L"
  ultimately
  show 
    "\<exists>L'. finite L' \<and> (\<forall>sa pa. sa \<notin> L' \<and> pa \<notin> L' \<and> sa \<noteq> pa 
                        \<longrightarrow> (\<exists>t''. \<sigma>[s,p] t\<^bsup>[Fvar sa,Fvar pa]\<^esup> \<rightarrow>\<^sub>\<beta> t'' 
                                 \<and> \<sigma>[s,p] t' = \<sigma>[sa,pa] t''))"
    by (rule_tac x = "L \<union> FV t \<union> {s} \<union> {p}" in exI, simp)
qed

lemma rtrancl_beta_UpdR:
  fixes L t t' u l
  assumes 
  "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
    \<longrightarrow> (\<exists>t''. (t\<^bsup>[Fvar s, Fvar p]\<^esup>) \<rightarrow>\<^sub>\<beta>\<^sup>* t'' \<and> t' = \<sigma>[s,p]t'')" and
  "finite L" and "lc u"
  shows "Upd u l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd u l t'"
proof -
  from \<open>finite L\<close> have "finite (L \<union> FV t)" by simp
  from exFresh_s_p_cof[OF this]
  obtain s p where sp: "s \<notin> L \<union> FV t \<and> p \<notin> L \<union> FV t \<and> s \<noteq> p" by auto
  with assms(1) obtain t'' where "t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t''" and t': "t' = \<sigma>[s,p] t''" 
    by auto
  with \<open>lc u\<close> have "Upd u l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd u l \<sigma>[s,p] t''"
  proof (erule_tac rtranclp_induct)
    from sp have "s \<notin> FV t" and "p \<notin> FV t" and "s \<noteq> p" by auto
    from sclose_sopen_eq_t[OF this] 
    show "Upd u l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd u l (\<sigma>[s,p](t\<^bsup>[Fvar s,Fvar p]\<^esup>))" 
      by (simp add: openz_def closez_def)
  next
    fix y :: sterm and z :: sterm
    assume "y \<rightarrow>\<^sub>\<beta> z"
    from sp have "s \<notin> L" and "p \<notin> L" and "s \<noteq> p" by auto
    from beta_binder[OF \<open>y \<rightarrow>\<^sub>\<beta> z\<close> \<open>finite L\<close> this]
    obtain L' where 
      "finite L'" and
      "\<forall>sa pa. sa \<notin> L' \<and> pa \<notin> L' \<and> sa \<noteq> pa
        \<longrightarrow> (\<exists>t''. \<sigma>[s,p] y\<^bsup>[Fvar sa,Fvar pa]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> \<sigma>[s,p] z = \<sigma>[sa,pa] t'')"
      by auto
    from beta.beta_UpdR[OF this \<open>lc u\<close>]
    have "Upd u l (\<sigma>[s,p] y) \<rightarrow>\<^sub>\<beta> Upd u l (\<sigma>[s,p] z)" by assumption
    moreover assume "Upd u l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd u l (\<sigma>[s,p] y)"
    ultimately show "Upd u l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd u l (\<sigma>[s,p] z)" by simp
  qed
  with t' show "Upd u l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd u l t'" by simp
qed

lemma rtrancl_beta_Upd: 
  "\<lbrakk> u \<rightarrow>\<^sub>\<beta>\<^sup>* u'; finite L; 
     \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
      \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t'' \<and> t' = \<sigma>[s,p]t'');
     lc u; body t \<rbrakk>
  \<Longrightarrow> Upd u l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd u' l t'"
proof (induct u u' rule: rtranclp.induct)
  case rtrancl_refl thus ?case by (simp add: rtrancl_beta_UpdR)
next
  case (rtrancl_into_rtrancl a b c) thus ?case
  proof (auto)
    from rtrancl_beta_body[OF \<open>finite L\<close> rtrancl_into_rtrancl(5) \<open>body t\<close>] \<open>b \<rightarrow>\<^sub>\<beta> c\<close>
    have "Upd b l t' \<rightarrow>\<^sub>\<beta> Upd c l t'" by simp
    with rtrancl_into_rtrancl(2)[OF \<open>finite L\<close> rtrancl_into_rtrancl(5) \<open>lc a\<close> \<open>body t\<close>]
    show "Upd a l t \<rightarrow>\<^sub>\<beta>\<^sup>* Upd c l t'" by simp
  qed
qed

lemma rtrancl_beta_obj: 
  fixes l f L T t t'
  assumes 
  "l \<in> dom f" and "finite L" and
  "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
    \<longrightarrow> (\<exists>t''. t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t'' \<and> t' = \<sigma>[s,p]t'')" and
  "\<forall>l\<in>dom f. body (the(f l))" and "body t"
  shows "Obj (f (l \<mapsto> t)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f (l \<mapsto> t')) T"
proof -
  from \<open>finite L\<close> have "finite (L \<union> FV t)" by simp
  from exFresh_s_p_cof[OF this]
  obtain s p where sp: "s \<notin> L \<union> FV t \<and> p \<notin> L \<union> FV t \<and> s \<noteq> p" by auto
  with assms(3) obtain t'' where "t\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t''" and "t' = \<sigma>[s,p] t''" 
    by auto
  with \<open>l \<in> dom f\<close> \<open>\<forall>l\<in>dom f. body (the(f l))\<close> 
  have "Obj (f(l \<mapsto> t)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f(l \<mapsto> \<sigma>[s,p] t'')) T"
  proof (erule_tac rtranclp_induct)
    from sp have "s \<notin> FV t" and "p \<notin> FV t" and "s \<noteq> p" by auto
    from sclose_sopen_eq_t[OF this] 
    show "Obj (f(l \<mapsto> t)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f(l \<mapsto> \<sigma>[s,p] (t\<^bsup>[Fvar s,Fvar p]\<^esup>))) T" 
      by (simp add: openz_def closez_def)
  next
    fix y :: sterm and z :: sterm assume "y \<rightarrow>\<^sub>\<beta> z"
    from sp have "s \<notin> L" and "p \<notin> L" and "s \<noteq> p" by auto
    from beta_binder[OF \<open>y \<rightarrow>\<^sub>\<beta> z\<close> \<open>finite L\<close> this]
    obtain L' where 
      "finite L'" and
      "\<forall>sa pa. sa \<notin> L' \<and> pa \<notin> L' \<and> sa \<noteq> pa
        \<longrightarrow> (\<exists>t''. \<sigma>[s,p] y\<^bsup>[Fvar sa,Fvar pa]\<^esup> \<rightarrow>\<^sub>\<beta> t'' \<and> \<sigma>[s,p] z = \<sigma>[sa,pa] t'')"
      by auto
    from beta.beta_Obj[OF \<open>l \<in> dom f\<close> this \<open>\<forall>l\<in>dom f. body (the(f l))\<close>]
    have "Obj (f(l \<mapsto> \<sigma>[s,p] y)) T \<rightarrow>\<^sub>\<beta> Obj (f(l \<mapsto> \<sigma>[s,p] z)) T"
      by assumption
    moreover assume "Obj (f(l \<mapsto> t)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f(l \<mapsto> \<sigma>[s,p] y)) T"
    ultimately
    show "Obj (f(l \<mapsto> t)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f(l \<mapsto> \<sigma>[s,p] z)) T" by simp
  qed
  with \<open>t' = \<sigma>[s,p] t''\<close> show "Obj (f(l \<mapsto> t)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f(l \<mapsto> t')) T" 
    by simp
qed

lemma obj_lem: 
  fixes l f T L t'
  assumes 
  "l \<in> dom f" and "finite L" and
  "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
    \<longrightarrow> (\<exists>t''. ((the(f l))\<^bsup>[Fvar s,Fvar p]\<^esup>) \<rightarrow>\<^sub>\<beta>\<^sup>* t'' \<and> t' = \<sigma>[s,p]t'')" and
  "\<forall>l\<in>dom f. body (the(f l))"
  shows "Obj f T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f(l \<mapsto> t')) T"
proof 
  (rule_tac P = "\<lambda>y. Obj y T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f(l \<mapsto> t')) T" and s = "(f(l \<mapsto> the(f l)))" 
    in subst)
  from \<open>l \<in> dom f\<close> fun_upd_idem show "f(l \<mapsto> the (f l)) = f" by force
next
  from \<open>l \<in> dom f\<close> \<open>\<forall>l\<in>dom f. body (the(f l))\<close> have "body (the (f l))" 
    by blast
  with 
    rtrancl_beta_obj[OF \<open>l \<in> dom f\<close> \<open>finite L\<close> assms(3) \<open>\<forall>l\<in>dom f. body (the(f l))\<close>]
  show "Obj (f(l \<mapsto> the (f l))) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (f(l \<mapsto> t')) T" by simp
qed

lemma rtrancl_beta_obj_lem00: 
  fixes L f g
  assumes 
  "finite L" and
  "\<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
               \<longrightarrow> (\<exists>t''. ((the(f l))\<^bsup>[Fvar s, Fvar p]\<^esup>) \<rightarrow>\<^sub>\<beta>\<^sup>* t'' 
                        \<and> the(g l) = \<sigma>[s,p]t'')" and
  "dom f = dom g" and "\<forall>l\<in>dom f. body (the (f l))"
  shows 
  "\<forall>k \<le> (card (dom f)). 
    (\<exists>ob. length ob = (k + 1)
        \<and> (\<forall>obi. obi \<in> set ob \<longrightarrow> dom (fst(obi)) = dom f \<and> ((snd obi) \<subseteq> dom f)) 
        \<and> (fst (ob!0) = f)
        \<and> (card (snd (ob!k)) = k)
        \<and> (\<forall>i < k. snd (ob!i) \<subset> snd (ob!k))
        \<and> (Obj (fst (ob!0)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst (ob!k)) T)
        \<and> (card (snd (ob!k)) = k 
           \<longrightarrow> (Ltake_eq (snd (ob!k)) (fst (ob!k)) g)
                \<and> (Ltake_eq ((dom f) - (snd (ob!k))) (fst (ob!k)) f)))"
proof
  fix k :: nat
  show 
    "k \<le> card (dom f) 
    \<longrightarrow> (\<exists>ob. length ob = k + 1 
            \<and> (\<forall>obi. obi \<in> set ob \<longrightarrow> dom (fst obi) = dom f \<and> snd obi \<subseteq> dom f) 
            \<and> fst (ob ! 0) = f 
            \<and> card (snd (ob ! k)) = k 
            \<and> (\<forall>i<k. snd (ob ! i) \<subset> snd (ob ! k)) 
            \<and> Obj (fst (ob ! 0)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst (ob ! k)) T 
            \<and> (card (snd (ob ! k)) = k 
               \<longrightarrow> Ltake_eq (snd (ob ! k)) (fst (ob ! k)) g 
                   \<and> Ltake_eq (dom f - snd (ob ! k)) (fst (ob ! k)) f))"
  proof (induct k)
    case 0 thus ?case
    by (simp, rule_tac x = "[(f,{})]" in exI, simp add: Ltake_eq_def)
  next
    case (Suc k) thus ?case
    proof (clarify)
      assume "Suc k \<le> card (dom f)" hence "k < card (dom f)" by arith
      with Suc.hyps
      obtain ob where 
        "length ob = k + 1" and
        mem_ob: "\<forall>obi. obi \<in> set ob 
                  \<longrightarrow> dom (fst obi) = dom f \<and> snd obi \<subseteq> dom f" and
        "fst (ob ! 0) = f" and
        "card (snd (ob ! k)) = k" and
        "\<forall>i<k. snd (ob ! i) \<subset> snd (ob ! k)" and
        "Obj (fst (ob ! 0)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst (ob ! k)) T" and
        card_k: "card (snd (ob ! k)) = k 
                 \<longrightarrow> Ltake_eq (snd (ob ! k)) (fst (ob ! k)) g 
                     \<and> Ltake_eq (dom f - snd (ob ! k)) (fst (ob ! k)) f"
        by auto
      from \<open>length ob = k + 1\<close> have obkmem: "(ob!k) \<in> set ob" by auto

      with mem_ob have obksnd: "snd(ob!k) \<subseteq> dom f" by blast
      from 
        card_psubset[OF finite_dom_fmap this] \<open>card (snd(ob!k)) = k\<close> 
        \<open>k < card (dom f)\<close>
      have "snd (ob!k) \<subset> dom f" by simp
      then obtain l' where "l' \<in> dom f" and "l' \<notin> snd (ob!k)" by auto

      from obkmem mem_ob have obkfst: "dom (fst(ob!k)) = dom f" by blast 

        (* get witness *)
      define ob' where "ob' = ob @ [(fst(ob!k)(l' \<mapsto> the (g l')), insert l' (snd(ob!k)))]"

      from nth_fst[OF \<open>length ob = k + 1\<close>] have first: "ob'!0 = ob!0" 
        by (simp add: ob'_def)

      from \<open>length ob = k + 1\<close> nth_last[of ob "Suc k"]
      have last: "ob'!Suc k = (fst(ob!k)(l' \<mapsto> the (g l')), insert l' (snd(ob!k)))"
        by (simp add: ob'_def)

      from \<open>length ob = k + 1\<close> nth_append[of ob _ k] have kth: "ob'!k = ob!k"
        by (auto simp: ob'_def)

      from \<open>card (snd(ob!k)) = k\<close> card_k
      have ass:
        "\<forall>l\<in>(snd(ob!k)). fst(ob!k) l = g l"
        "\<forall>l\<in>(dom f - snd(ob!k)). fst(ob!k) l = f l"
        by (auto simp: Ltake_eq_def)


        (* prop#1 *)
      from \<open>length ob = k + 1\<close> have "length ob' = Suc k + 1" 
        by (auto simp: ob'_def)

        (* prop#2 *)
      moreover
      have "\<forall>obi. obi \<in> set ob' \<longrightarrow> dom (fst obi) = dom f \<and> snd obi \<subseteq> dom f"
        unfolding ob'_def
      proof (intro strip)
        fix obi :: "(Label -~> sterm) \<times> (Label set)"
        assume "obi \<in> set (ob @ [(fst(ob!k)(l' \<mapsto> the (g l')), insert l' (snd (ob!k)))])"
        note mem_append_lem'[OF this]
        thus "dom (fst obi) = dom f \<and> snd obi \<subseteq> dom f"
        proof (rule disjE, simp_all)
          assume "obi \<in> set ob" 
          with mem_ob show "dom (fst obi) = dom f \<and> snd obi \<subseteq> dom f"
            by blast
        next
          from obkfst obksnd \<open>l' \<in> dom f\<close>
          show 
            "insert l' (dom (fst (ob!k))) = dom f 
             \<and> l' \<in> dom f \<and> snd(ob!k) \<subseteq> dom f" 
            by blast
        qed
      qed

        (* prop#3 *)
      moreover 
      from first \<open>fst(ob!0) = f\<close> have "fst(ob'!0) = f" by simp

        (* prop#4 *)
      moreover
      from obksnd finite_dom_fmap finite_subset 
      have "finite (snd (ob!k))" by auto
      from card_insert[OF this]
      have "card (insert l' (snd (ob!k))) = Suc (card (snd(ob!k) - {l'}))" 
        by simp
      with \<open>l' \<notin> snd (ob!k)\<close> \<open>card (snd(ob!k)) = k\<close> last
      have "card(snd(ob'!Suc k)) = Suc k" by auto

        (* prop#5 *)
      moreover
      have "\<forall>i<Suc k. snd (ob'!i) \<subset> snd (ob'!Suc k)"
      proof (intro strip)
        fix i :: nat
        from last have "snd(ob'!Suc k) = insert l' (snd (ob!k))" by simp
        with \<open>l' \<notin> snd (ob!k)\<close> have "snd(ob!k) \<subset> snd(ob'!Suc k)" by auto
        moreover
        assume "i < Suc k"
        with \<open>length ob = k + 1\<close> have "i < length ob" by simp
        with nth_append[of ob _ i] have "ob'!i = ob!i" by (simp add: ob'_def)
        ultimately show "snd(ob'!i) \<subset> snd(ob'!Suc k)"
        proof (cases "i < k")
          case True 
          with 
            \<open>\<forall>i<k. snd(ob!i) \<subset> snd(ob!k)\<close> \<open>ob'!i = ob!i\<close> 
            \<open>snd(ob!k) \<subset> snd(ob'!Suc k)\<close>
          show "snd (ob'!i) \<subset> snd (ob'!Suc k)" by auto
        next
          case False with \<open>i < Suc k\<close> have "i = k" by arith
          with \<open>ob'!i = ob!i\<close> \<open>snd(ob!k) \<subset> snd(ob'!Suc k)\<close>
          show "snd (ob'!i) \<subset> snd (ob'!Suc k)" by auto
        qed
      qed

        (* prop#6 -- the main statement *)
      moreover
      {
        from \<open>l' \<in> dom f\<close> \<open>l' \<notin> snd(ob!k)\<close> have "l' \<in> (dom f - snd(ob!k))" 
          by auto
        with ass have "the(fst(ob!k) l') = the(f l')" by auto 
        with \<open>l' \<in> dom f\<close> assms(2)
        have 
          sp: "\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                \<longrightarrow> (\<exists>t''. the(fst(ob!k) l')\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t'' 
                         \<and> the (g l') = \<sigma>[s,p] t'')"
          by simp

        moreover
        have "\<forall>l\<in>dom (fst(ob!k)). body (the(fst(ob!k) l))"
        proof (intro strip)
          fix la :: Label
          assume "la \<in> dom (fst(ob!k))"
          with obkfst have inf: "la \<in> dom f" by auto
          with assms(4) have bodyf: "body (the(f la))" by auto
          show "body (the(fst(ob!k) la))"
          proof (cases "la \<in> snd(ob!k)")
            case False with inf have "la \<in> (dom f - snd(ob!k))" by auto
            with ass have "fst(ob!k) la = f la" by blast
            with bodyf show "body (the (fst(ob!k) la))" by auto
          next
            from exFresh_s_p_cof[OF \<open>finite L\<close>]
            obtain s p where "s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p" by auto
            with assms(2) inf
            obtain t' where 
              "the (f la)\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and
              "the (g la) = \<sigma>[s,p] t'" by blast
            from body_lc[OF bodyf] have lcf: "lc (the (f la)\<^bsup>[Fvar s,Fvar p]\<^esup>)" by auto
            hence bodyg: "body (the(g la))"
            proof (cases "(the (f la)\<^bsup>[Fvar s,Fvar p]\<^esup>) = t'")
              case True 
              with 
                lcf lc_body \<open>s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p\<close> 
                \<open>the(g la) = \<sigma>[s,p] t'\<close>
              show "body (the(g la))" by auto
            next
              case False 
              with 
                rtrancl_beta_lc[OF \<open>the (f la)\<^bsup>[Fvar s,Fvar p]\<^esup> \<rightarrow>\<^sub>\<beta>\<^sup>* t'\<close>] 
                lc_body \<open>s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p\<close> \<open>the(g la) = \<sigma>[s,p] t'\<close>
              show "body (the(g la))" by auto
            qed
            case True with ass bodyg show "body (the(fst(ob!k) la))" by simp
          qed
        qed

        moreover
        from \<open>l' \<in> dom f\<close> obkfst have "l' \<in> dom(fst(ob!k))" by auto
        note obj_lem[OF this \<open>finite L\<close>]

        ultimately
        have "Obj (fst(ob!k)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst(ob!k)(l' \<mapsto> the (g l'))) T"
          by blast

        moreover
        from last have "fst(ob'!Suc k) = fst(ob!k)(l' \<mapsto> the (g l'))"
          by auto

        ultimately
        have "Obj (fst(ob'!0)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst(ob'!Suc k)) T"
          using 
            rtranclp_trans[OF \<open>Obj (fst (ob!0)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst (ob!k)) T\<close>] first kth
          by auto
      }

        (* prop#7 *)
      moreover
      from \<open>l' \<in> dom f\<close> \<open>dom f = dom g\<close>
      have 
        "card (snd(ob'!Suc k)) = Suc k 
         \<longrightarrow> Ltake_eq (snd (ob'!Suc k)) (fst (ob'!Suc k)) g 
             \<and> Ltake_eq (dom f - snd(ob'!Suc k)) (fst(ob'!Suc k)) f"
        by (auto simp: Ltake_eq_def last ass)
      
      ultimately
      show 
        "\<exists>ob. length ob = Suc k + 1 
            \<and> (\<forall>obi. obi \<in> set ob \<longrightarrow> dom (fst obi) = dom f \<and> snd obi \<subseteq> dom f) 
            \<and> fst (ob ! 0) = f 
            \<and> card (snd (ob ! Suc k)) = Suc k 
            \<and> (\<forall>i<Suc k. snd (ob ! i) \<subset> snd (ob ! Suc k)) 
            \<and> Obj (fst (ob ! 0)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst (ob ! Suc k)) T 
            \<and> (card (snd (ob ! Suc k)) = Suc k 
               \<longrightarrow> Ltake_eq (snd (ob ! Suc k)) (fst (ob ! Suc k)) g 
                   \<and> Ltake_eq (dom f - snd (ob ! Suc k)) (fst (ob ! Suc k)) f)"
        by (rule_tac x = ob' in exI, simp)
    qed
  qed
qed

lemma rtrancl_beta_obj_n: 
  fixes f g L T
  assumes 
  "finite L" and
  "\<forall>l\<in>dom f. \<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
               \<longrightarrow> (\<exists>t''. ((the(f l))\<^bsup>[Fvar s, Fvar p]\<^esup>) \<rightarrow>\<^sub>\<beta>\<^sup>* t'' 
                        \<and> the(g l) = \<sigma>[s,p]t'')" and
  "dom f = dom g" and "\<forall>l\<in>dom f. body (the(f l))"
  shows "Obj f T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj g T"
proof (cases "f = Map.empty")
  case True with \<open>dom f = dom g\<close> have "{} = dom g" by simp
  from \<open>f = Map.empty\<close> empty_dom[OF this] show ?thesis by simp
next
  from rtrancl_beta_obj_lem00[OF assms]
  obtain ob :: "((Label -~> sterm) \<times> (Label set)) list" 
    where 
    "length ob = card(dom f) + 1" and
    "\<forall>obi. obi \<in> set ob \<longrightarrow> dom (fst obi) = dom f \<and> snd obi \<subseteq> dom f" and
    "fst(ob!0) = f" and
    "card (snd(ob!card(dom f))) = card(dom f)" and
    "Obj (fst(ob!0)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst(ob!card(dom f))) T" and
    "Ltake_eq (snd(ob!card(dom f))) (fst(ob!card(dom f))) g"
    by blast
  from \<open>length ob = card (dom f) + 1\<close> have "(ob!card(dom f)) \<in> set ob" by auto
  with \<open>\<forall>obi. obi \<in> set ob \<longrightarrow> dom (fst obi) = dom f \<and> snd obi \<subseteq> dom f\<close>
  have "dom (fst(ob!card(dom f))) = dom f" and "snd(ob!card(dom f)) \<subseteq> dom f"
    by blast+

  {
    fix l :: Label
    from 
      \<open>snd(ob!card(dom f)) \<subseteq> dom f\<close> \<open>card (snd(ob!card(dom f))) = card(dom f)\<close>
      Ltake_eq_dom
    have "snd(ob!card(dom f)) = dom f" by blast
    with \<open>Ltake_eq (snd(ob!card (dom f))) (fst(ob!card (dom f))) g\<close> 
    have "fst(ob!card(dom f)) l = g l"
    proof (cases "l \<in> dom f", simp_all add: Ltake_eq_def)
      assume "l \<notin> dom f" 
      with \<open>dom f = dom g\<close> \<open>dom (fst(ob!card(dom f))) = dom f\<close> 
      show "fst(ob!card(dom f)) l = g l" by auto
    qed
  }
  with ext have "fst(ob!card(dom f)) = g" by auto
  with \<open>fst(ob!0) = f\<close> \<open>Obj (fst(ob!0)) T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj (fst(ob!card (dom f))) T\<close> 
  show "Obj f T \<rightarrow>\<^sub>\<beta>\<^sup>* Obj g T" by simp
qed

subsection \<open>Size of sterms\<close>

(* this section defines the size of sterms 
compared to size, the size of an object is the sum of the size of its fields +1 *)

definition fsize0 :: "(Label -~> sterm) \<Rightarrow> (sterm \<Rightarrow> nat) \<Rightarrow> nat" where
  "fsize0 f sts =
    foldl (+) 0 (map sts (Finite_Set.fold (\<lambda>x z. z@[THE y. Some y = f x]) [] (dom f)))"

primrec
 ssize        :: "sterm \<Rightarrow> nat" 
and
 ssize_option :: "sterm option \<Rightarrow> nat"
where
  ssize_Bvar : "ssize (Bvar b) = 0"
| ssize_Fvar : "ssize (Fvar x) = 0"
| ssize_Call : "ssize (Call a l b) = (ssize a) + (ssize b) + Suc 0"
| ssize_Upd  : "ssize (Upd a l b) = (ssize a) + (ssize b) + Suc 0" 
| ssize_Obj  : "ssize (Obj f T) = Finite_Set.fold (\<lambda>x y. y + ssize_option (f x)) (Suc 0) (dom f)"
| ssize_None : "ssize_option (None) = 0"
| ssize_Some : "ssize_option (Some y) = ssize y + Suc 0"

(* We need this locale, as all the handy functions are there now *)
interpretation comp_fun_commute "(\<lambda>x y::nat. y + (f x))"
  by (unfold comp_fun_commute_def, force)

lemma SizeOfObjectPos: "ssize (Obj (f::Label -~> sterm) T) > 0"
proof (simp)
  from finite_dom_fmap have "finite (dom f)" by auto
  thus "0 < Finite_Set.fold (\<lambda>x y. y + ssize_option (f x)) (Suc 0) (dom f)"
  proof (induct)
    case empty thus ?case by simp
  next
    case (insert A a) thus ?case by auto
  qed
qed

end
