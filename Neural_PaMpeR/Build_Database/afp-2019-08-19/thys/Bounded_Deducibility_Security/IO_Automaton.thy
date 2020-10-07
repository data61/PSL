section \<open>IO Automaton\<close>

(*<*)
theory IO_Automaton
imports Trivia
begin
(*>*)


subsection\<open>Preliminaries\<close>

text \<open>Transitions\<close>

datatype ('state,'act,'out) trans =
Trans (srcOf: 'state) (actOf: 'act) (outOf: 'out) (tgtOf: 'state)


type_synonym ('state,'act,'out) trace = "('state,'act,'out) trans list"


locale IO_Automaton =
fixes istate :: "'state" (* initial step *)
  and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'out * 'state"  (* transition function *)
begin


subsection\<open>Reachability and invariance\<close>

(* Reachable states: *)
inductive reach :: "'state \<Rightarrow> bool" where
Istate: "reach istate"
|
Step: "reach s \<Longrightarrow> reach (snd (step s a))"

lemma reach_PairI:
assumes "reach s" and "step s a = (ou, s')"
shows "reach s'"
by (metis Step assms assms snd_eqD)

(* holds at the initial state: *)
definition holdsIstate :: "('state \<Rightarrow> bool) \<Rightarrow> bool" where
"holdsIstate \<phi> \<equiv> \<phi> istate"

(* is invariant: *)
definition invar :: "('state \<Rightarrow> bool) \<Rightarrow> bool" where
"invar \<phi> \<equiv> \<forall> s a. reach s \<and> \<phi> s \<longrightarrow> \<phi> (snd (step s a))"

lemma holdsIstate_invar:
assumes h: "holdsIstate \<phi>" and i: "invar \<phi>" and a: "reach s"
shows "\<phi> s"
using a apply (induct rule: reach.induct)
using h i unfolding holdsIstate_def invar_def by auto


subsection\<open>System traces\<close>

(* The output and effect of an action on a state: *)
definition out :: "'state \<Rightarrow> 'act \<Rightarrow> 'out" where "out s a \<equiv> fst (step s a)"
definition eff :: "'state \<Rightarrow> 'act \<Rightarrow> 'state" where "eff s a \<equiv> snd (step s a)"

primrec validTrans :: "('state,'act,'out) trans \<Rightarrow> bool" where
"validTrans (Trans s a ou s') = (step s a = (ou, s'))"

lemma validTrans:
"validTrans trn =
 (step (srcOf trn) (actOf trn) = (outOf trn, tgtOf trn))"
by (cases trn) auto

(* Traces allowed by the system (starting in any given state) *)
(* Two alternative definitions: growing from the left and growing from the right: *)
inductive valid :: "('state,'act,'out) trace \<Rightarrow> bool" where
Singl[simp,intro!]:
"validTrans trn
 \<Longrightarrow>
 valid [trn]"
|
Cons[intro]:
"\<lbrakk>validTrans trn; tgtOf trn = srcOf (hd tr); valid tr\<rbrakk>
 \<Longrightarrow>
 valid (trn # tr)"

inductive_cases valid_SinglE[elim!]: "valid [trn]"
inductive_cases valid_ConsE[elim]: "valid (trn # tr)"

inductive valid2 :: "('state,'act,'out) trace \<Rightarrow> bool" where
Singl[simp,intro!]:
"validTrans trn
 \<Longrightarrow>
 valid2 [trn]"
|
Rcons[intro]:
"\<lbrakk>valid2 tr; tgtOf (last tr) = srcOf trn; validTrans trn\<rbrakk>
 \<Longrightarrow>
 valid2 (tr ## trn)"

inductive_cases valid2_SinglE[elim!]: "valid2 [trn]"
inductive_cases valid2_RconsE[elim]: "valid2 (tr ## trn)"

lemma Nil_not_valid[simp]: "\<not> valid []"
by (metis valid.simps neq_Nil_conv)

lemma Nil_not_valid2[simp]: "\<not> valid2 []"
by (metis valid2.cases append_Nil butlast.simps butlast_snoc not_Cons_self2)

lemma valid_Rcons:
assumes "valid tr" and "tgtOf (last tr) = srcOf trn" and "validTrans trn"
shows "valid (tr ## trn)"
using assms proof(induct arbitrary: trn)
  case (Cons trn tr trna)
  thus ?case by (cases tr) (auto intro: valid.Cons)
qed(auto intro: valid.intros)

lemma valid_hd_Rcons[simp]:
assumes "valid tr"
shows "hd (tr ## tran) = hd tr"
by (metis Nil_not_valid assms hd_append)

lemma valid2_hd_Rcons[simp]:
assumes "valid2 tr"
shows "hd (tr ## tran) = hd tr"
by (metis Nil_not_valid2 assms hd_append)

lemma valid2_last_Cons[simp]:
assumes "valid2 tr"
shows "last (tran # tr) = last tr"
by (metis Nil_not_valid2 assms last.simps)

lemma valid2_Cons:
assumes "valid2 tr" and "tgtOf trn = srcOf (hd tr)" and "validTrans trn"
shows "valid2 (trn # tr)"
using assms proof(induct arbitrary: trn)
  case Singl  show ?case
  unfolding two_singl_Rcons using Singl
  by (intro valid2.Rcons) (auto intro: valid2.Singl)
next
  case Rcons show ?case
  unfolding append.append_Cons[symmetric] using Rcons by (intro valid2.Rcons) auto
qed

lemma valid_valid2: "valid = valid2"
proof(rule ext, safe)
  fix tr assume "valid tr"  thus "valid2 tr"
  by (induct) (auto intro: valid2.Singl valid2_Cons)
next
  fix tr assume "valid2 tr"  thus "valid tr"
  by (induct) (auto intro: valid.Singl valid_Rcons)
qed

lemmas valid2_valid = valid_valid2[symmetric]

definition validFrom :: "'state \<Rightarrow> ('state,'act,'out) trace \<Rightarrow> bool" where
"validFrom s tr \<equiv> tr = [] \<or> (valid tr \<and> srcOf (hd tr) = s)"

lemma validFrom_Nil[simp,intro!]: "validFrom s []"
unfolding validFrom_def by auto

lemma validFrom_valid[simp,intro]: "valid tr \<and> srcOf (hd tr) = s \<Longrightarrow> validFrom s tr"
unfolding validFrom_def by auto

lemma validFrom_validTrans[intro]:
assumes "validTrans (Trans s a ou s')" and "validFrom s' tr"
shows "validFrom s (Trans s a ou s' # tr)"
using assms unfolding validFrom_def by auto


subsection \<open>Traces versus reachability\<close>

lemma valid_reach_src_tgt:
assumes "valid tr" and "reach (srcOf (hd tr))"
shows "reach (tgtOf (last tr))"
using assms by induct (auto intro: reach_PairI simp: validTrans)

lemma valid_init_reach:
assumes "valid tr" and "srcOf (hd tr) = istate"
shows "reach (tgtOf (last tr))"
using valid_reach_src_tgt assms reach.Istate by metis

lemma Trans_fst_sndI:
"valid [Trans s a (fst (step s a)) (snd (step s a))]"
by (metis valid.Singl surjective_pairing validTrans.simps)

lemma reach_init_valid:
assumes "reach s"
shows
"s = istate
 \<or>
 (\<exists> tr. valid tr \<and> srcOf (hd tr) = istate \<and> tgtOf (last tr) = s)"
using assms proof induction
  case (Step s a)
  thus ?case proof(elim disjE exE conjE)
    assume s: "s = istate"
    let ?ou = "fst (step s a)"  let ?s' = "snd (step s a)"
    show ?thesis using s
    by (intro disjI2 exI[of _ "[Trans s a ?ou ?s']"]) auto
  next
    fix tr assume v: "valid tr" and s: "srcOf (hd tr) = istate" and t: "tgtOf (last tr) = s"
    let ?ou = "fst (step s a)"  let ?s' = "snd (step s a)"
    show ?thesis using v t s
    by (intro disjI2 exI[of _ "tr ## Trans s a ?ou ?s'"]) (auto intro: valid_Rcons)
  qed
qed auto

lemma reach_validFrom:
assumes "reach s'"
shows "\<exists> s tr. s = istate \<and> (s = s' \<or> (validFrom s tr \<and> tgtOf (last tr) = s'))"
using reach_init_valid[OF assms] unfolding validFrom_def by auto


(*<*)

end (* locale IO_Automaton *)

end

(*>*)
