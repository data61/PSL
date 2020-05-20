(*  Title:      Jinja/J/execute_WellType.thy
    Author:     Christoph Petzinger
    Copyright   2004 Technische Universitaet Muenchen
*)

section \<open>Code Generation For WellType\<close>

theory execute_WellType
imports
  WellType Examples
begin

(* Replace WT_WTs.WTCond with new intros WT_WTs.WTCond1 and WT_WTs.WTCond2 *)

lemma WTCond1:
  "\<lbrakk>P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^sub>1::T\<^sub>1;  P,E \<turnstile> e\<^sub>2::T\<^sub>2; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2;
    P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T\<^sub>2 = T\<^sub>1 \<rbrakk> \<Longrightarrow> P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T\<^sub>2"
by (fastforce)

lemma WTCond2:
  "\<lbrakk>P,E \<turnstile> e :: Boolean;  P,E \<turnstile> e\<^sub>1::T\<^sub>1;  P,E \<turnstile> e\<^sub>2::T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1;
    P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T\<^sub>1 = T\<^sub>2 \<rbrakk> \<Longrightarrow> P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T\<^sub>1"
by (fastforce)

lemmas [code_pred_intro] =
  WT_WTs.WTNew
  WT_WTs.WTCast
  WT_WTs.WTVal
  WT_WTs.WTVar
  WT_WTs.WTBinOpEq
  WT_WTs.WTBinOpAdd
  WT_WTs.WTLAss
  WT_WTs.WTFAcc
  WT_WTs.WTFAss
  WT_WTs.WTCall
  WT_WTs.WTBlock
  WT_WTs.WTSeq

declare
  WTCond1 [code_pred_intro WTCond1]
  WTCond2 [code_pred_intro WTCond2]

lemmas [code_pred_intro] =
  WT_WTs.WTWhile
  WT_WTs.WTThrow
  WT_WTs.WTTry
  WT_WTs.WTNil
  WT_WTs.WTCons

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as type_check, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as infer_type)
  WT
proof -
  case WT
  from WT.prems show thesis
  proof(cases (no_simp))
    case (WTCond E e e1 T1 e2 T2 T)
    from \<open>x \<turnstile> T1 \<le> T2 \<or> x \<turnstile> T2 \<le> T1\<close> show thesis
    proof
      assume "x \<turnstile> T1 \<le> T2"
      with \<open>x \<turnstile> T1 \<le> T2 \<longrightarrow> T = T2\<close> have "T = T2" ..
      from \<open>xa = E\<close> \<open>xb = if (e) e1 else e2\<close> \<open>xc = T\<close> \<open>x,E \<turnstile> e :: Boolean\<close> 
        \<open>x,E \<turnstile> e1 :: T1\<close> \<open>x,E \<turnstile> e2 :: T2\<close> \<open>x \<turnstile> T1 \<le> T2\<close> \<open>x \<turnstile> T2 \<le> T1 \<longrightarrow> T = T1\<close>
      show ?thesis unfolding \<open>T = T2\<close> by(rule WT.WTCond1[OF refl])
    next
      assume "x \<turnstile> T2 \<le> T1"
      with \<open>x \<turnstile> T2 \<le> T1 \<longrightarrow> T = T1\<close> have "T = T1" ..
      from \<open>xa = E\<close> \<open>xb = if (e) e1 else e2\<close> \<open>xc = T\<close> \<open>x,E \<turnstile> e :: Boolean\<close> 
        \<open>x,E \<turnstile> e1 :: T1\<close> \<open>x,E \<turnstile> e2 :: T2\<close> \<open>x \<turnstile> T2 \<le> T1\<close> \<open>x \<turnstile> T1 \<le> T2 \<longrightarrow> T = T2\<close>
      show ?thesis unfolding \<open>T = T1\<close> by(rule WT.WTCond2[OF refl])
    qed
  qed(assumption|erule (2) WT.that[OF refl])+
next
  case WTs
  from WTs.prems show thesis
    by(cases (no_simp))(assumption|erule (2) WTs.that[OF refl])+
qed

notation infer_type ("_,_ \<turnstile> _ :: '_" [51,51,51]100)

definition test1 where "test1 = [],Map.empty \<turnstile> testExpr1 :: _"
definition test2 where "test2 = [], Map.empty  \<turnstile> testExpr2 :: _"
definition test3 where "test3 = [], Map.empty(''V'' \<mapsto> Integer)  \<turnstile> testExpr3 :: _"
definition test4 where "test4 = [], Map.empty(''V'' \<mapsto> Integer)  \<turnstile> testExpr4 :: _"
definition test5 where "test5 = [classObject, (''C'',(''Object'',[(''F'',Integer)],[]))], Map.empty  \<turnstile> testExpr5 :: _"
definition test6 where "test6 = [classObject, classI], Map.empty  \<turnstile> testExpr6 :: _"

ML_val \<open>
  val SOME(@{code Integer}, _) = Predicate.yield @{code test1};
  val SOME(@{code Integer}, _) = Predicate.yield @{code test2};
  val SOME(@{code Integer}, _) = Predicate.yield @{code test3};
  val SOME(@{code Void}, _) = Predicate.yield @{code test4};
  val SOME(@{code Void}, _) = Predicate.yield @{code test5};
  val SOME(@{code Integer}, _) = Predicate.yield @{code test6};
\<close>

definition testmb_isNull where "testmb_isNull = [classObject, classA], Map.empty([this] [\<mapsto>] [Class ''A'']) \<turnstile> mb_isNull :: _"
definition testmb_add where "testmb_add = [classObject, classA], Map.empty([this,''i''] [\<mapsto>] [Class ''A'',Integer]) \<turnstile> mb_add :: _"
definition testmb_mult_cond where "testmb_mult_cond = [classObject, classA], Map.empty([this,''j''] [\<mapsto>] [Class ''A'',Integer]) \<turnstile> mb_mult_cond :: _"
definition testmb_mult_block where "testmb_mult_block = [classObject, classA], Map.empty([this,''i'',''j'',''temp''] [\<mapsto>] [Class ''A'',Integer,Integer,Integer]) \<turnstile> mb_mult_block :: _"
definition testmb_mult where "testmb_mult = [classObject, classA], Map.empty([this,''i'',''j''] [\<mapsto>] [Class ''A'',Integer,Integer]) \<turnstile> mb_mult :: _"

ML_val \<open>
  val SOME(@{code Boolean}, _) = Predicate.yield @{code testmb_isNull};
  val SOME(@{code Integer}, _) = Predicate.yield @{code testmb_add};
  val SOME(@{code Boolean}, _) = Predicate.yield @{code testmb_mult_cond};
  val SOME(@{code Void}, _) = Predicate.yield @{code testmb_mult_block};
  val SOME(@{code Integer}, _) = Predicate.yield @{code testmb_mult};
\<close>

definition test where "test = [classObject, classA], Map.empty \<turnstile> testExpr_ClassA :: _"

ML_val \<open>
  val SOME(@{code Integer}, _) = Predicate.yield @{code test};
\<close>

end
