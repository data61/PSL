(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Agent
  imports "HOL-Nominal.Nominal"
begin

lemma pt_id:
  fixes x :: 'a
    and a :: 'x

  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"
  shows "[(a, a)] \<bullet> x = x"
proof -
  have "x = ([]::'x prm) \<bullet> x"
    by(simp add: pt1[OF pt])
  also have "[(a, a)] \<bullet> x = ([]::'x prm) \<bullet> x"
    by(simp add: pt3[OF pt] at_ds1[OF at])
  finally show ?thesis by simp
qed

lemma pt_swap:
  fixes x :: 'a
  and a :: 'x
  and b :: 'x

  assumes pt: "pt TYPE('a) TYPE('x)"
  and     at: "at TYPE('x)"

  shows "[(a, b)] \<bullet> x = [(b, a)] \<bullet> x"
proof -
  show ?thesis by(simp add: pt3[OF pt] at_ds5[OF at])
qed

atom_decl name

lemmas name_fresh_abs = fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fs_name1]
lemmas name_bij = at_bij[OF at_name_inst]
lemmas name_supp_abs = abs_fun_supp[OF pt_name_inst, OF at_name_inst, OF fs_name1]
lemmas name_abs_eq = abs_fun_eq[OF pt_name_inst, OF at_name_inst]
lemmas name_supp = at_supp[OF at_name_inst]
lemmas name_calc = at_calc[OF at_name_inst]
lemmas name_fresh_fresh = pt_fresh_fresh[OF pt_name_inst, OF at_name_inst]
lemmas name_fresh_left = pt_fresh_left[OF pt_name_inst, OF at_name_inst]
lemmas name_fresh_right = pt_fresh_right[OF pt_name_inst, OF at_name_inst]
lemmas name_id[simp] = pt_id[OF pt_name_inst, OF at_name_inst]
lemmas name_swap_bij[simp] = pt_swap_bij[OF pt_name_inst, OF at_name_inst]
lemmas name_swap = pt_swap[OF pt_name_inst, OF at_name_inst]
lemmas name_rev_per = pt_rev_pi[OF pt_name_inst, OF at_name_inst]
lemmas name_per_rev = pt_pi_rev[OF pt_name_inst, OF at_name_inst]
lemmas name_exists_fresh = at_exists_fresh[OF at_name_inst, OF fs_name1]
lemmas name_perm_compose = pt_perm_compose[OF pt_name_inst, OF at_name_inst]

nominal_datatype pi = PiNil                  ("\<zero>")
                    | Output name name pi    ("_{_}._" [120, 120, 110] 110)
                    | Tau pi                 ("\<tau>._" [120] 110)
                    | Input name "\<guillemotleft>name\<guillemotright> pi" ("_<_>._" [120, 120, 110] 110)
                    | Match name name pi     ("[_\<frown>_]_" [120, 120, 110] 110)
                    | Mismatch name name pi  ("[_\<noteq>_]_" [120, 120, 110] 110)
                    | Sum pi pi              (infixr "\<oplus>" 90)
                    | Par pi pi              (infixr "\<parallel>" 85)
                    | Res "\<guillemotleft>name\<guillemotright> pi"        ("<\<nu>_>_" [100, 100] 100)
                    | Bang pi                ("!_" [110] 110)

lemmas name_fresh[simp] = at_fresh[OF at_name_inst]

lemma alphaInput:
  fixes a :: name
  and   x :: name
  and   P :: pi
  and   c :: name

  assumes A1: "c \<sharp> P"

  shows "a<x>.P = a<c>.([(x, c)] \<bullet> P)"
proof(cases "x = c")
  assume "x=c"
  thus ?thesis by(simp)
next
  assume "x \<noteq> c"
  with A1 show ?thesis
    by(simp add: pi.inject alpha name_fresh_left name_calc)
qed

lemma alphaRes:
  fixes a :: name
  and   P :: pi
  and   c :: name
  
  assumes A1: "c \<sharp> P"

  shows "<\<nu>a>P = <\<nu>c>([(a, c)] \<bullet> P)"
proof(cases "a=c")
  assume "a=c"
  thus ?thesis by simp
next
  assume "a \<noteq> c"
  with A1 show ?thesis
    by(simp add: pi.inject alpha fresh_left name_calc)
qed

(*Substitution*)

definition subst_name :: "name \<Rightarrow> name \<Rightarrow> name \<Rightarrow> name"   ("_[_::=_]" [110, 110, 110] 110)
where
  "a[b::=c] \<equiv> if (a = b) then c else a"

declare subst_name_def[simp]

lemma subst_name_eqvt[eqvt]:
  fixes p :: "name prm"
  and   a :: name
  and   b :: name
  and   c :: name

  shows "p \<bullet> (a[b::=c]) = (p\<bullet> a)[(p \<bullet> b)::=(p \<bullet> c)]"
by(auto simp add: at_bij[OF at_name_inst])


nominal_primrec (freshness_context: "(c::name, d::name)")
  subs :: "pi \<Rightarrow> name \<Rightarrow> name \<Rightarrow> pi" ("_[_::=_]" [100,100,100] 100)
where
  "\<zero>[c::=d] = \<zero>"
| "\<tau>.(P)[c::=d] = \<tau>.(P[c::=d])"
| "a{b}.P[c::=d] = (a[c::=d]){(b[c::=d])}.(P[c::=d])"
| "\<lbrakk>x \<noteq> a; x \<noteq> c; x \<noteq> d\<rbrakk> \<Longrightarrow> (a<x>.P)[c::=d] = (a[c::=d])<x>.(P[c::=d])"
| "[a\<frown>b]P[c::=d] = [(a[c::=d])\<frown>(b[c::=d])](P[c::=d])"
| "[a\<noteq>b]P[c::=d] = [(a[c::=d])\<noteq>(b[c::=d])](P[c::=d])"
| "(P \<oplus> Q)[c::=d] = (P[c::=d]) \<oplus> (Q[c::=d])"
| "(P \<parallel> Q)[c::=d] = (P[c::=d]) \<parallel> (Q[c::=d])"
| "\<lbrakk>x \<noteq> c; x \<noteq> d\<rbrakk> \<Longrightarrow> (<\<nu>x>P)[c::=d] = <\<nu>x>(P[c::=d])"
| "!P[c::=d] = !(P[c::=d])"
apply(simp_all add: abs_fresh)
apply(finite_guess)+
by(fresh_guess)+

lemma forget:
  fixes a :: name
  and   P :: pi
  and   b :: name

  assumes "a \<sharp> P"

  shows "P[a::=b] = P"
using assms
by(nominal_induct P avoiding: a b rule: pi.strong_induct)
  (auto simp add: name_fresh_abs)

lemma fresh_fact2[rule_format]:
  fixes P :: pi
  and   a :: name
  and   b :: name

  assumes "a \<noteq> b"

  shows "a \<sharp> P[a::=b]"
using assms
by(nominal_induct P avoiding: a b rule: pi.strong_induct)
  (auto simp add: name_fresh_abs)

lemma subst_identity[simp]:
  fixes P :: pi
  and   a :: name

  shows "P[a::=a] = P"
by(nominal_induct P avoiding: a rule: pi.strong_induct) auto

lemma renaming:
  fixes P :: pi
  and   a :: name
  and   b :: name
  and   c :: name

  assumes "c \<sharp> P"

  shows "P[a::=b] = ([(c, a)] \<bullet> P)[c::=b]"
using assms
by(nominal_induct P avoiding: a b c rule: pi.strong_induct)
  (auto simp add: name_calc name_fresh_abs)


lemma fresh_fact1:
  fixes P :: pi
  and   a :: name
  and   b :: name
  and   c :: name

  assumes "a \<sharp> P"
  and     "a \<noteq> c"

  shows "a \<sharp> P[b::=c]"
using assms
by(nominal_induct P avoiding: a b c rule: pi.strong_induct)
  (auto simp add: name_fresh_abs)


lemma eqvt_subs[eqvt]:
  fixes p :: "name prm"
  and   P :: pi
  and   a :: name
  and   b :: name

  shows "p \<bullet> (P[a::=b]) = (p \<bullet> P)[(p \<bullet> a)::=(p \<bullet> b)]"
by(nominal_induct P avoiding: a b rule: pi.strong_induct)
  (auto simp add: name_bij)


lemma substInput[simp]:
  fixes x :: name
  and   b :: name
  and   c :: name
  and   a :: name
  and   P :: pi

  assumes "x \<noteq> b"
  and     "x \<noteq> c"

  shows "(a<x>.P)[b::=c] = (a[b::=c])<x>.(P[b::=c])"
proof -
  obtain y::name where"y \<noteq> a" and "y \<sharp> P" and "y \<noteq> b" and "y \<noteq> c"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  from \<open>y \<sharp> P\<close> have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" by(simp add: alphaInput)
  moreover have "(a[b::=c])<x>.(P[b::=c]) = (a[b::=c])<y>.(([(x, y)] \<bullet> P)[b::=c])" (is "?LHS = ?RHS")
  proof -
    from \<open>y \<sharp> P\<close> \<open>y \<noteq> c\<close> have "y \<sharp> P[b::=c]" by(rule fresh_fact1)
    hence "?LHS = (a[b::=c])<y>.([(x, y)] \<bullet> (P[b::=c]))" by(simp add: alphaInput)
    moreover with \<open>x \<noteq> b\<close> \<open>x \<noteq> c\<close> \<open>y \<noteq> b\<close> \<open>y \<noteq> c\<close> have "\<dots> = ?RHS"
      by(auto simp add: eqvt_subs name_calc)
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis using \<open>y \<noteq> a\<close> \<open>y \<noteq> b\<close> \<open>y \<noteq> c\<close> by simp
qed

lemma injPermSubst:
  fixes P :: pi
  and   a :: name
  and   b :: name

  assumes "b \<sharp> P"

  shows "[(a, b)] \<bullet> P = P[a::=b]"
using assms
by(nominal_induct P avoiding: a b rule: pi.strong_induct)
  (auto simp add: name_calc name_fresh_abs)

lemma substRes2:
  fixes P :: pi
  and   a :: name
  and   b :: name

  assumes "b \<sharp> P"

  shows "<\<nu>a>P = <\<nu>b>(P[a::=b])"
proof(case_tac "a = b")
  assume "a = b"
  thus ?thesis by auto
next
  assume "a \<noteq> b"
  moreover with \<open>b \<sharp> P\<close> show ?thesis
    apply(simp add: pi.inject abs_fun_eq[OF pt_name_inst, OF at_name_inst])
    apply auto
    apply(simp add: renaming)
    apply(simp add: pt_swap[OF pt_name_inst, OF at_name_inst])
    apply(simp add: renaming)
    apply(simp add: pt_fresh_left[OF pt_name_inst, OF at_name_inst])
    by(force simp add: at_calc[OF at_name_inst])
qed

lemma freshRes:
  fixes P :: pi
  and   a :: name
  
  shows "a \<sharp> <\<nu>a>P"
by(simp add: name_fresh_abs)

lemma substRes3: 
  fixes P :: pi
  and   a :: name
  and   b :: name

  assumes "b \<sharp> P"

  shows "(<\<nu>a>P)[a::=b] = <\<nu>b>(P[a::=b])"
proof -
  have "(<\<nu>a>P)[a::=b] = <\<nu>a>P"
    using freshRes by(simp add: forget)
  thus ?thesis using \<open>b \<sharp> P\<close> by(simp add: substRes2)
qed

lemma suppSubst:
  fixes P :: pi
  and   a :: name
  and   b :: name

  shows "supp(P[a::=b]) \<subseteq> insert b ((supp P) - {a})"
apply(nominal_induct P avoiding: a b rule: pi.strong_induct,
      simp_all add: pi.supp name_supp_abs name_supp supp_prod)
by(blast)+
  
(******** Sequential substitution *******)

primrec seqSubs :: "pi \<Rightarrow> (name \<times> name) list \<Rightarrow> pi" ("_[<_>]" [100,100] 100) where
  "P[<[]>] = P"
| "P[<(x#\<sigma>)>] = (P[(fst x)::=(snd x)])[<\<sigma>>]"

primrec seq_subst_name :: "name \<Rightarrow> (name \<times> name) list \<Rightarrow> name" where
  "seq_subst_name a [] = a"
| "seq_subst_name a (x#\<sigma>) = seq_subst_name (a[(fst x)::=(snd x)]) \<sigma>"

lemma freshSeqSubstName:
  fixes x :: name
  and   a :: name
  and   s :: "(name \<times> name) list"

  assumes "x \<noteq> a"
  and     "x \<sharp> s"

  shows "x \<noteq> seq_subst_name a s"
using assms
apply(induct s arbitrary: a)
apply simp
apply(case_tac "aa = fst(a)")
by (force simp add: fresh_list_cons fresh_prod)+


lemma seqSubstZero[simp]:
  fixes \<sigma> :: "(name \<times> name) list"

  shows "\<zero>[<\<sigma>>] = \<zero>"
by(induct \<sigma>, auto)

lemma seqSubstTau[simp]:
  fixes P :: pi
  and   \<sigma> :: "(name \<times> name) list"

  shows "(\<tau>.(P))[<\<sigma>>] = \<tau>.(P[<\<sigma>>])"
by(induct \<sigma> arbitrary: P, auto)

lemma seqSubstOutput[simp]:
  fixes a :: name
  and   b :: name
  and   P :: pi
  and   \<sigma> :: "(name \<times> name) list"
  
  shows "(a{b}.P)[<\<sigma>>] = (seq_subst_name a \<sigma>){(seq_subst_name b \<sigma>)}.(P[<\<sigma>>])"
by(induct \<sigma> arbitrary: a b P, auto)

lemma seqSubstInput[simp]:
  fixes a :: name
  and   x :: name
  and   P :: pi
  and   \<sigma> :: "(name \<times> name) list"

  assumes "x \<sharp> \<sigma>"
 
  shows "(a<x>.P)[<\<sigma>>] = (seq_subst_name a \<sigma>)<x>.(P[<\<sigma>>])"
using assms
by(induct \<sigma> arbitrary: a x P) (auto simp add: fresh_list_cons fresh_prod)

lemma seqSubstMatch[simp]:
  fixes a :: name
  and   b :: name
  and   P :: pi
  and   \<sigma> :: "(name \<times> name) list"

  shows "([a\<frown>b]P)[<\<sigma>>] = [(seq_subst_name a \<sigma>)\<frown>(seq_subst_name b \<sigma>)](P[<\<sigma>>])"
by(induct \<sigma> arbitrary: a b P, auto)

lemma seqSubstMismatch[simp]:
  fixes a :: name
  and   b :: name
  and   P :: pi
  and   \<sigma> :: "(name \<times> name) list"

  shows "([a\<noteq>b]P)[<\<sigma>>] = [(seq_subst_name a \<sigma>)\<noteq>(seq_subst_name b \<sigma>)](P[<\<sigma>>])"
by(induct \<sigma> arbitrary: a b P, auto)

lemma seqSubstSum[simp]:
  fixes P :: pi
  and   Q :: pi
  and   \<sigma> :: "(name \<times> name) list"

  shows "(P \<oplus> Q)[<\<sigma>>] = (P[<\<sigma>>]) \<oplus> (Q[<\<sigma>>])"
by(induct \<sigma> arbitrary: P Q , auto)

lemma seqSubstPar[simp]:
  fixes P :: pi
  and   Q :: pi
  and   \<sigma> :: "(name \<times> name) list"

  shows "(P \<parallel> Q)[<\<sigma>>] = (P[<\<sigma>>]) \<parallel> (Q[<\<sigma>>])"
by(induct \<sigma> arbitrary: P Q, auto)

lemma seqSubstRes[simp]:
  fixes x :: name
  and   P :: pi
  and   \<sigma> :: "(name \<times> name) list"

  assumes "x \<sharp> \<sigma>"

  shows "(<\<nu>x>P)[<\<sigma>>] = <\<nu>x>(P[<\<sigma>>])"
using assms
by(induct \<sigma> arbitrary: x P) (auto simp add: fresh_list_cons fresh_prod)

lemma seqSubstBang[simp]:
  fixes P :: pi
  and   s :: "(name \<times> name) list"

  shows "(!P)[<\<sigma>>] = !(P[<\<sigma>>])"
by(induct \<sigma> arbitrary: P, auto)

lemma seqSubstEqvt[eqvt, simp]:
  fixes P :: pi
  and   \<sigma> :: "(name \<times> name) list"
  and   p :: "name prm"

  shows "p \<bullet> (P[<\<sigma>>]) = (p \<bullet> P)[<(p \<bullet> \<sigma>)>]"
by(induct \<sigma> arbitrary: P, auto simp add: eqvt_subs)

lemma seqSubstAppend[simp]:
  fixes P  :: pi
  and   \<sigma>  :: "(name \<times> name) list"
  and   \<sigma>' :: "(name \<times> name) list"

  shows "P[<(\<sigma>@\<sigma>')>] = (P[<\<sigma>>])[<\<sigma>'>]"
by(induct \<sigma> arbitrary: P, auto)

lemma freshSubstChain[intro]:
  fixes P :: pi
  and   \<sigma> :: "(name \<times> name) list"
  and   a :: name

  assumes "a \<sharp> P"
  and     "a \<sharp> \<sigma>"

  shows "a \<sharp> P[<\<sigma>>]"
using assms
by(induct \<sigma> arbitrary: a P, auto simp add: fresh_list_cons fresh_prod fresh_fact1)

end
