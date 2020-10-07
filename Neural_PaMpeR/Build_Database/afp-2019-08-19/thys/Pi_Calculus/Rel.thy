(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Rel
  imports Agent
begin

definition eqvt :: "(('a::pt_name) \<times> ('a::pt_name)) set \<Rightarrow> bool"
  where "eqvt Rel \<equiv> (\<forall>x (perm::name prm). x \<in> Rel \<longrightarrow> perm \<bullet> x \<in> Rel)"

lemma eqvtRelI:
  fixes Rel  :: "('a::pt_name \<times> 'a) set"
  and   P    :: 'a
  and   Q    :: 'a
  and   perm :: "name prm"

  assumes "eqvt Rel"
  and     "(P, Q) \<in> Rel"

  shows "(perm \<bullet> P, perm \<bullet> Q) \<in> Rel"
using assms
by(auto simp add: eqvt_def)

lemma eqvtRelE:
  fixes Rel  :: "('a::pt_name \<times> 'a) set"
  and   P    :: 'a
  and   Q    :: 'a
  and   perm :: "name prm"

  assumes "eqvt Rel"
  and     "(perm \<bullet> P, perm \<bullet> Q) \<in> Rel"

  shows "(P, Q) \<in> Rel"
proof -
  have "rev perm \<bullet> (perm \<bullet> P) = P" and "rev perm \<bullet> (perm \<bullet> Q) = Q"
    by(simp add: pt_rev_pi[OF pt_name_inst, OF at_name_inst])+
  with assms show ?thesis
    by(force dest: eqvtRelI[of _ _ _ "rev perm"])
qed

lemma eqvtTrans[intro]:
  fixes Rel  :: "('a::pt_name \<times> 'a) set"
  and   Rel' :: "('a \<times> 'a) set"

  assumes EqvtRel:  "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "eqvt (Rel O Rel')"
using assms
by(force simp add: eqvt_def)

lemma eqvtUnion[intro]:
  fixes Rel  :: "('a::pt_name \<times> 'a) set"
  and   Rel' :: "('a \<times> 'a) set"

  assumes EqvtRel:  "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "eqvt (Rel \<union> Rel')"
using assms
by(force simp add: eqvt_def)

definition substClosed :: "(pi \<times> pi) set \<Rightarrow> (pi \<times> pi) set" where
  "substClosed Rel \<equiv> {(P, Q) | P Q. \<forall>\<sigma>. (P[<\<sigma>>], Q[<\<sigma>>]) \<in> Rel}"

lemma eqvtSubstClosed:
  fixes Rel :: "(pi \<times> pi) set"

  assumes eqvtRel: "eqvt Rel"

  shows "eqvt (substClosed Rel)"
proof(simp add: eqvt_def substClosed_def, auto)
  fix P Q perm s

  assume "\<forall>s. (P[<s>], Q[<s>]) \<in> Rel"
  hence "(P[<(rev (perm::name prm) \<bullet> s)>], Q[<(rev perm \<bullet> s)>]) \<in> Rel" by simp
  with eqvtRel have "(perm \<bullet> (P[<(rev perm \<bullet> s)>]), perm \<bullet> (Q[<(rev perm \<bullet> s)>])) \<in> Rel"
    by(rule eqvtRelI)
  thus "((perm \<bullet> P)[<s>], (perm \<bullet> Q)[<s>]) \<in> Rel"
    by(simp add: name_per_rev)
qed

lemma substClosedSubset:
  fixes Rel  :: "(pi \<times> pi) set"

  shows "substClosed Rel \<subseteq> Rel"
proof(auto simp add: substClosed_def)
  fix P Q
  assume "\<forall>s. (P[<s>], Q[<s>]) \<in> Rel"
  hence "(P[<[]>], Q[<[]>]) \<in> Rel" by blast
  thus "(P, Q) \<in> Rel" by simp
qed

lemma partUnfold:
  fixes P   :: pi
  and   Q   :: pi
  and   \<sigma>   :: "(name \<times> name) list"
  and   Rel :: "(pi \<times> pi) set"

  assumes "(P, Q) \<in> substClosed Rel"

  shows "(P[<\<sigma>>], Q[<\<sigma>>]) \<in> substClosed Rel"
using assms
proof(auto simp add: substClosed_def)
  fix \<sigma>'
  assume "\<forall>\<sigma>. (P[<\<sigma>>], Q[<\<sigma>>]) \<in> Rel"
  hence "(P[<(\<sigma>@\<sigma>')>], Q[<(\<sigma>@\<sigma>')>]) \<in> Rel" by blast
  thus "((P[<\<sigma>>])[<\<sigma>'>], (Q[<\<sigma>>])[<\<sigma>'>]) \<in> Rel"
    by simp
qed

inductive_set bangRel :: "(pi \<times> pi) set \<Rightarrow> (pi \<times> pi) set"
for Rel :: "(pi \<times> pi) set"
where
  BRBang: "(P, Q) \<in> Rel \<Longrightarrow> (!P, !Q) \<in> bangRel Rel"
| BRPar: "(R, T) \<in> Rel \<Longrightarrow> (P, Q) \<in> (bangRel Rel) \<Longrightarrow> (R \<parallel> P, T \<parallel> Q) \<in> (bangRel Rel)"
| BRRes: "(P, Q) \<in> bangRel Rel \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> bangRel Rel"

inductive_cases BRBangCases': "(P, !Q) \<in> bangRel Rel"
inductive_cases BRParCases': "(P, Q \<parallel> !Q) \<in> bangRel Rel"
inductive_cases BRResCases': "(P, <\<nu>x>Q) \<in> bangRel Rel"

lemma eqvtBangRel:
  fixes Rel :: "(pi \<times> pi) set"

  assumes eqvtRel: "eqvt Rel"

  shows "eqvt(bangRel Rel)"
proof(simp add: eqvt_def, auto)
  fix P Q perm
  assume "(P, Q) \<in> bangRel Rel"
  thus "((perm::name prm) \<bullet> P, perm \<bullet> Q) \<in> bangRel Rel"
  proof(induct)
    fix P Q
    assume "(P, Q) \<in> Rel"
    with eqvtRel have "(perm \<bullet> P, perm \<bullet> Q) \<in> Rel"
      by(rule eqvtRelI)
    thus "(perm \<bullet> !P, perm \<bullet> !Q) \<in> bangRel Rel"
      by(force intro: BRBang)
  next
    fix P Q R T
    assume R: "(R, T) \<in> Rel"
    assume BR: "(perm \<bullet> P, perm \<bullet> Q) \<in> bangRel Rel"

    from eqvtRel R have "(perm \<bullet> R, perm \<bullet> T) \<in> Rel"
      by(rule eqvtRelI)

    with BR show "(perm \<bullet> (R \<parallel> P), perm \<bullet> (T \<parallel> Q)) \<in> bangRel Rel"
      by(force intro: BRPar)
  next
    fix P Q a
    assume "(perm \<bullet> P, perm \<bullet> Q) \<in> bangRel Rel"
    thus "(perm \<bullet> <\<nu>a>P, perm \<bullet> <\<nu>a>Q) \<in> bangRel Rel"
      by(force intro: BRRes)
  qed
qed

lemma BRBangCases[consumes 1, case_names BRBang]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   F   :: "pi \<Rightarrow> bool"

  assumes "(P, !Q) \<in> bangRel Rel"
  and     "\<And>P. (P, Q) \<in> Rel \<Longrightarrow> F (!P)"
  
  shows "F P"
using assms
by(induct rule: BRBangCases', auto simp add: pi.inject)

lemma BRParCases[consumes 1, case_names BRPar]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   F   :: "pi \<Rightarrow> bool"

  assumes "(P, Q \<parallel> !Q) \<in> bangRel Rel"
  and     "\<And>P R. \<lbrakk>(P, Q) \<in> Rel; (R, !Q) \<in> bangRel Rel\<rbrakk> \<Longrightarrow> F (P \<parallel> R)"

  shows "F P"
using assms
by(induct rule: BRParCases', auto simp add: pi.inject)

lemma bangRelSubset:
  fixes Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes "(P, Q) \<in> bangRel Rel"
  and     "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> (P, Q) \<in> Rel'"

  shows "(P, Q) \<in> bangRel Rel'"
using assms
by(induct rule:  bangRel.induct) (auto intro: BRBang BRPar BRRes)

lemma bangRelSymetric: 
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes A:   "(P, Q) \<in> bangRel Rel"
  and     Sym: "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> (Q, P) \<in> Rel"

  shows "(Q, P) \<in> bangRel Rel"
proof -
  from A show ?thesis
  proof(induct)
    fix P Q
    assume "(P, Q) \<in> Rel"
    hence "(Q, P) \<in> Rel" by(rule Sym)
    thus "(!Q, !P) \<in> bangRel Rel" by(rule BRBang)
  next
    fix P Q R T
    assume RRelT: "(R, T) \<in> Rel"
    assume IH: "(Q, P) \<in> bangRel Rel"
    from RRelT have "(T, R) \<in> Rel" by(rule Sym)
    thus "(T \<parallel> Q, R \<parallel> P) \<in> bangRel Rel" using IH by(rule BRPar)
  next
    fix P Q a
    assume "(Q, P) \<in> bangRel Rel"
    thus "(<\<nu>a>Q, <\<nu>a>P) \<in> bangRel Rel" by(rule BRRes)
  qed
qed

primrec resChain :: "name list \<Rightarrow> pi \<Rightarrow> pi" where
   base: "resChain [] P = P"
 | step: "resChain (x#xs) P = <\<nu>x>(resChain xs P)"

lemma resChainPerm[simp]:
  fixes perm :: "name prm"
  and   lst  :: "name list"
  and   P    :: pi
  
  shows "perm \<bullet> (resChain lst P) = resChain (perm \<bullet> lst) (perm \<bullet> P)"
by(induct_tac lst, auto)

lemma resChainFresh:
  fixes a   :: name
  and   lst :: "name list"
  and   P   :: pi

  assumes "a \<sharp> (lst, P)"

  shows "a \<sharp> (resChain lst P)"
using assms apply(induct_tac lst)
apply(simp add: fresh_prod)
by(simp add: fresh_prod name_fresh_abs)

end
