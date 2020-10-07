(*  Title:      IL_Operator.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Temporal logic operators on natural intervals\<close>

theory IL_TemporalOperators
imports IL_IntervalOperators
begin

text \<open>Bool : some additional properties\<close>

instantiation bool :: "{ord, zero, one, plus, times, order}"
begin

definition Zero_bool_def [simp]: "0 \<equiv> False"
definition One_bool_def [simp]: "1 \<equiv> True"
definition add_bool_def: "a + b \<equiv> a \<or> b"
definition mult_bool_def: "a * b \<equiv> a \<and> b"

instance ..

end

value "False < True"
value "True < True"
value "True \<le> True"

lemmas bool_op_rel_defs =
  add_bool_def 
  mult_bool_def
  less_bool_def
  le_bool_def

instance bool :: wellorder
apply (rule wf_wellorderI)
 apply (rule_tac t="{(x, y). x < y}" and s="{(False, True)}" in subst)
  apply fastforce
 apply (unfold wf_def, blast)
apply intro_classes
done

instance bool :: comm_semiring_1
apply intro_classes
apply (unfold bool_op_rel_defs Zero_bool_def One_bool_def)
apply blast+
done


subsection \<open>Basic definitions\<close>

lemma UNIV_nat: "\<nat> = (UNIV::nat set)"
by (simp add: Nats_def)

text \<open>Universal temporal operator: Always/Globally\<close>
definition iAll :: "iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Always\<close>
  where "iAll I P \<equiv> \<forall>t\<in>I. P t"

text \<open>Existential temporal operator: Eventually/Finally\<close>
definition iEx :: "iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Eventually\<close>
  where "iEx I P \<equiv> \<exists>t\<in>I. P t"


syntax
  "_iAll" :: "Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<box> _ _./ _)" [0, 0, 10] 10)
  "_iEx" ::  "Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<diamond> _ _./ _)" [0, 0, 10] 10)
translations
  "\<box> t I. P" \<rightleftharpoons> "CONST iAll I (\<lambda>t. P)"
  "\<diamond> t I. P" \<rightleftharpoons> "CONST iEx I (\<lambda>t. P)"

text \<open>Future temporal operator: Next\<close>
definition iNext :: "Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Next\<close>
  where "iNext t0 I P \<equiv> P (inext t0 I)"

text \<open>Past temporal operator: Last/Previous\<close>
definition iLast :: "Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Last\<close>
  where "iLast t0 I P \<equiv> P (iprev t0 I)"

syntax
  "_iNext" :: "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<circle> _ _ _./ _)" [0, 0, 10] 10)
  "_iLast" :: "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<ominus> _ _ _./ _)" [0, 0, 10] 10)
translations
  "\<circle> t t0 I. P" \<rightleftharpoons> "CONST iNext t0 I (\<lambda>t. P)"
  "\<ominus> t t0 I. P" \<rightleftharpoons> "CONST iLast t0 I (\<lambda>t. P)"

lemma "\<circle> t 10 [0\<dots>]. (t + 10 > 10)"
by (simp add: iNext_def iT_inext_if)

text \<open>The following versions of Next and Last operator differ in the cases
  where no next/previous element exists or specified time point is not in interval:
  the weak versions return @{term True} and the strong versions return @{term False}.\<close>

definition iNextWeak :: "Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Weak Next\<close>
  where "iNextWeak t0 I P  \<equiv> (\<box> t {inext t0 I} \<down>> t0. P t)"

definition iNextStrong :: "Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Strong Next\<close>
  where "iNextStrong t0 I P \<equiv> (\<diamond> t {inext t0 I} \<down>> t0. P t)"

definition iLastWeak :: "Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Weak Last\<close>
  where "iLastWeak t0 I P   \<equiv> (\<box> t {iprev t0 I} \<down>< t0. P t)"

definition iLastStrong :: "Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Strong Last\<close>
  where "iLastStrong t0 I P \<equiv> (\<diamond> t {iprev t0 I} \<down>< t0. P t)"

syntax
  "_iNextWeak"   :: "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<circle>\<^sub>W _ _ _./ _)" [0, 0, 10] 10)
  "_iNextStrong" :: "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<circle>\<^sub>S _ _ _./ _)" [0, 0, 10] 10)
  "_iLastWeak"   :: "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<ominus>\<^sub>W _ _ _./ _)" [0, 0, 10] 10)
  "_iLastStrong" :: "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" ("(3\<ominus>\<^sub>S _ _ _./ _)" [0, 0, 10] 10)
translations
  "\<circle>\<^sub>W t t0 I. P" \<rightleftharpoons> "CONST iNextWeak t0 I (\<lambda>t. P)"
  "\<circle>\<^sub>S t t0 I. P" \<rightleftharpoons> "CONST iNextStrong t0 I (\<lambda>t. P)"
  "\<ominus>\<^sub>W t t0 I. P" \<rightleftharpoons> "CONST iLastWeak t0 I (\<lambda>t. P)"
  "\<ominus>\<^sub>S t t0 I. P" \<rightleftharpoons> "CONST iLastStrong t0 I (\<lambda>t. P)"


text \<open>Some examples for Next and Last operator\<close>

lemma "\<circle> t 5 [0\<dots>,10]. ([0::int,10,20,30,40,50,60,70,80,90] ! t < 80)"
by (simp add: iNext_def iIN_inext)

lemma "\<ominus> t 5 [0\<dots>,10]. ([0::int,10,20,30,40,50,60,70,80,90] ! t < 80)"
by (simp add: iLast_def iIN_iprev)


text \<open>Temporal Until operator\<close>
definition iUntil :: "iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Until\<close>
  where "iUntil I P Q \<equiv> \<diamond> t I. Q t \<and> (\<box> t' (I \<down>< t). P t')"

text \<open>Temporal Since operator (past operator corresponding to Until)\<close>
definition iSince :: "iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Since\<close>
  where "iSince I P Q \<equiv> \<diamond> t I. Q t \<and> (\<box> t' (I \<down>> t). P t')"

syntax
  "_iUntil" ::  "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" 
    ("(_./ _ (3\<U> _ _)./ _)" [10, 0, 0, 0, 10] 10)
  "_iSince" ::  "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" 
    ("(_./ _ (3\<S> _ _)./ _)" [10, 0, 0, 0, 10] 10)
translations
  "P. t \<U> t' I. Q" \<rightleftharpoons> "CONST iUntil I (\<lambda>t. P) (\<lambda>t'. Q)"
  "P. t \<S> t' I. Q" \<rightleftharpoons> "CONST iSince I (\<lambda>t. P) (\<lambda>t'. Q)"

definition iWeakUntil :: "iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Weak Until/Wating-for/Unless\<close>
  where "iWeakUntil I P Q \<equiv> (\<box> t I. P t) \<or> (\<diamond> t I. Q t \<and> (\<box> t' (I \<down>< t). P t'))"

definition iWeakSince :: "iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Weak Since/Back-to\<close>
  where "iWeakSince I P Q \<equiv> (\<box> t I. P t) \<or> (\<diamond> t I. Q t \<and> (\<box> t' (I \<down>> t). P t'))"

syntax
  "_iWeakUntil" ::  "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" 
    ("(_./ _ (3\<W> _ _)./ _)" [10, 0, 0, 0, 10] 10)
  "_iWeakSince" ::  "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" 
    ("(_./ _ (3\<B> _ _)./ _)" [10, 0, 0, 0, 10] 10)
translations
  "P. t \<W> t' I. Q" \<rightleftharpoons> "CONST iWeakUntil I (\<lambda>t. P) (\<lambda>t'. Q)"
  "P. t \<B> t' I. Q" \<rightleftharpoons> "CONST iWeakSince I (\<lambda>t. P) (\<lambda>t'. Q)"


definition iRelease :: "iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Release\<close>
  where "iRelease I P Q \<equiv> (\<box> t I. Q t) \<or> (\<diamond> t I. P t \<and> (\<box> t' (I \<down>\<le> t). Q t'))"

definition iTrigger :: "iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool"      \<comment> \<open>Trigger\<close>
  where "iTrigger I P Q \<equiv> (\<box> t I. Q t) \<or> (\<diamond> t I. P t \<and> (\<box> t' (I \<down>\<ge> t). Q t'))"

syntax
  "_iRelease" ::  "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" 
    ("(_./ _ (3\<R> _ _)./ _)" [10, 0, 0, 0, 10] 10)
  "_iTrigger" ::  "Time \<Rightarrow> Time \<Rightarrow> iT \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> (Time \<Rightarrow> bool) \<Rightarrow> bool" 
    ("(_./ _ (3\<T> _ _)./ _)" [10, 0, 0, 0, 10] 10)
translations
  "P. t \<R> t' I. Q" \<rightleftharpoons> "CONST iRelease I (\<lambda>t. P) (\<lambda>t'. Q)"
  "P. t \<T> t' I. Q" \<rightleftharpoons> "CONST iTrigger I (\<lambda>t. P) (\<lambda>t'. Q)"


lemmas iTL_Next_defs =
  iNext_def iLast_def
  iNextWeak_def iLastWeak_def
  iNextStrong_def iLastStrong_def
lemmas iTL_defs = 
  iAll_def iEx_def
  iUntil_def iSince_def
  iWeakUntil_def iWeakSince_def
  iRelease_def iTrigger_def
  iTL_Next_defs
(* Like in Set.thy *)
(* To avoid eta-contraction of body: *)
print_translation \<open>
 [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax iAll} @{syntax_const "_iAll"},
  Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax iEx} @{syntax_const "_iEx"}]
\<close>

print_translation \<open>
let
  fun btr' syn [i,Abs abs,Abs abs'] =
    let
      val (t,P) = Syntax_Trans.atomic_abs_tr' abs;
      val (t',Q) = Syntax_Trans.atomic_abs_tr' abs'
    in Syntax.const syn $ P $ t $ t' $ i $ Q end
in
 [(@{const_syntax "iUntil"}, K (btr' "_iUntil")),
  (@{const_syntax "iSince"}, K (btr' "_iSince"))]
end
\<close>

print_translation \<open>
let
  fun btr' syn [i,Abs abs,Abs abs'] =
    let
      val (t,P) = Syntax_Trans.atomic_abs_tr' abs;
      val (t',Q) = Syntax_Trans.atomic_abs_tr' abs'
    in Syntax.const syn $ P $ t $ t' $ i $ Q end
in
 [(@{const_syntax "iWeakUntil"}, K (btr' "_iWeakUntil")),
  (@{const_syntax "iWeakSince"}, K (btr' "_iWeakSince"))]
end
\<close>

print_translation \<open>
let
  fun btr' syn [i,Abs abs,Abs abs'] =
    let
      val (t,P) = Syntax_Trans.atomic_abs_tr' abs;
      val (t',Q) = Syntax_Trans.atomic_abs_tr' abs'
    in Syntax.const syn $ P $ t $ t' $ i $ Q end
in
 [(@{const_syntax "iRelease"}, K (btr' "_iRelease")),
  (@{const_syntax "iTrigger"}, K (btr' "_iTrigger"))]
end
\<close>


subsection \<open>Basic lemmata for temporal operators\<close>

subsubsection \<open>Intro/elim rules\<close>

lemma 
  iexI[intro]:      "\<lbrakk> P t; t \<in> I \<rbrakk> \<Longrightarrow> \<diamond> t I. P t" and
  rev_iexI[intro?]: "\<lbrakk> t \<in> I; P t \<rbrakk> \<Longrightarrow> \<diamond> t I. P t" and
  iexE[elim!]:      "\<lbrakk> \<diamond> t I. P t; \<And>t. \<lbrakk> t \<in> I; P t \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (unfold iEx_def, blast+)

lemma
  iallI[intro!]: "(\<And>t. t \<in> I \<Longrightarrow> P t) \<Longrightarrow> \<box> t I. P t" and
  ispec[dest?]: "\<lbrakk> \<box> t I. P t; t \<in> I \<rbrakk> \<Longrightarrow> P t" and
  iallE[elim]: "\<lbrakk> \<box> t I. P t; P t \<Longrightarrow> Q; t \<notin> I \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (unfold iAll_def, blast+)

lemma
  iuntilI[intro]: "
    \<lbrakk> Q t; (\<And>t'. t' \<in> I \<down>< t\<Longrightarrow> P t'); t \<in> I \<rbrakk> \<Longrightarrow> P t'. t' \<U> t I. Q t" and
  rev_iuntilI[intro?]: "
    \<lbrakk> t \<in> I; Q t; (\<And>t'. t' \<in> I \<down>< t\<Longrightarrow> P t') \<rbrakk> \<Longrightarrow> P t'. t' \<U> t I. Q t"
by (unfold iUntil_def, blast+)

lemma
  iuntilE[elim]: "
    \<lbrakk> P' t'. t' \<U> t I. P t; \<And>t. \<lbrakk> t \<in> I; P t \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (unfold iUntil_def, blast)

lemma
  isinceI[intro]: "
    \<lbrakk> Q t; (\<And>t'. t' \<in> I \<down>> t\<Longrightarrow> P t'); t \<in> I \<rbrakk> \<Longrightarrow> P t'. t' \<S> t I. Q t" and
  rev_isinceI[intro?]: "
    \<lbrakk> t \<in> I; Q t; (\<And>t'. t' \<in> I \<down>> t\<Longrightarrow> P t') \<rbrakk> \<Longrightarrow> P t'. t' \<S> t I. Q t"
by (unfold iSince_def, blast+)
lemma
  isinceE[elim]: "
    \<lbrakk> P' t'. t' \<S> t I. P t; \<And>t. \<lbrakk> t \<in> I; P t \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (unfold iSince_def, blast)


subsubsection \<open>Rewrite rules for trivial simplification\<close>

lemma iall_triv[simp]: "(\<box> t I. P) = ((\<exists>t. t \<in> I) \<longrightarrow> P)"
by (simp add: iAll_def)

lemma iex_triv[simp]: "(\<diamond> t I. P) = ((\<exists>t. t \<in> I) \<and> P)"
by (simp add: iEx_def)

lemma iex_conjL1: "
  (\<diamond> t1 I1. (P1 t1 \<and> (\<diamond> t2 I2. P2 t1 t2))) = 
  (\<diamond> t1 I1. \<diamond> t2 I2. P1 t1 \<and> P2 t1 t2)"
by blast

lemma iex_conjR1: "
  (\<diamond> t1 I1. ((\<diamond> t2 I2. P2 t1 t2) \<and> P1 t1)) =
  (\<diamond> t1 I1. \<diamond> t2 I2. P2 t1 t2 \<and> P1 t1)"
by blast

lemma iex_conjL2: "
  (\<diamond> t1 I1. (P1 t1 \<and> (\<diamond> t2 (I2 t1). P2 t1 t2))) = 
  (\<diamond> t1 I1. \<diamond> t2 (I2 t1). P1 t1 \<and> P2 t1 t2)"
by blast

lemma iex_conjR2: "
  (\<diamond> t1 I1. ((\<diamond> t2 (I2 t1). P2 t1 t2) \<and> P1 t1)) = 
  (\<diamond> t1 I1. \<diamond> t2 (I2 t1). P2 t1 t2 \<and> P1 t1)"
by blast

lemma iex_commute: "
  (\<diamond> t1 I1. \<diamond> t2 I2. P t1 t2) = 
  (\<diamond> t2 I2. \<diamond> t1 I1. P t1 t2)"
by blast

lemma iall_conjL1: "
  I2 \<noteq> {} \<Longrightarrow>
  (\<box> t1 I1. (P1 t1 \<and> (\<box> t2 I2. P2 t1 t2))) = 
  (\<box> t1 I1. \<box> t2 I2. P1 t1 \<and> P2 t1 t2)"
by blast

lemma iall_conjR1: "
  I2 \<noteq> {} \<Longrightarrow>
  (\<box> t1 I1. ((\<box> t2 I2. P2 t1 t2) \<and> P1 t1)) =
  (\<box> t1 I1. \<box> t2 I2. P2 t1 t2 \<and> P1 t1)"
by blast

lemma iall_conjL2: "
  \<box> t1 I1. I2 t1 \<noteq> {} \<Longrightarrow>
  (\<box> t1 I1. (P1 t1 \<and> (\<box> t2 (I2 t1). P2 t1 t2))) = 
  (\<box> t1 I1. \<box> t2 (I2 t1). P1 t1 \<and> P2 t1 t2)"
by blast

lemma iall_conjR2: "
  \<box> t1 I1. I2 t1 \<noteq> {} \<Longrightarrow>
  (\<box> t1 I1. ((\<box> t2 (I2 t1). P2 t1 t2) \<and> P1 t1)) = 
  (\<box> t1 I1. \<box> t2 (I2 t1). P2 t1 t2 \<and> P1 t1)"
by blast

lemma iall_commute: "
  (\<box> t1 I1. \<box> t2 I2. P t1 t2) = 
  (\<box> t2 I2. \<box> t1 I1. P t1 t2)"
by blast

lemma iall_conj_distrib: "
  (\<box> t I. P t \<and> Q t) = ((\<box> t I. P t) \<and> (\<box> t I. Q t))"
by blast

lemma iex_disj_distrib: "
  (\<diamond> t I. P t \<or> Q t) = ((\<diamond> t I. P t) \<or> (\<diamond> t I. Q t))"
by blast

lemma iall_conj_distrib2: "
  (\<box> t1 I1. \<box> t2 (I2 t1). P t1 t2 \<and> Q t1 t2) = 
  ((\<box> t1 I1. \<box> t2 (I2 t1). P t1 t2) \<and> (\<box> t1 I1. \<box> t2 (I2 t1). Q t1 t2))"
by blast

lemma iex_disj_distrib2: "
  (\<diamond> t1 I1. \<diamond> t2 (I2 t1). P t1 t2 \<or> Q t1 t2) = 
  ((\<diamond> t1 I1. \<diamond> t2 (I2 t1). P t1 t2) \<or> (\<diamond> t1 I1. \<diamond> t2 (I2 t1). Q t1 t2))"
by blast

lemma iUntil_disj_distrib: "
  (P t1. t1 \<U> t2 I. (Q1 t2 \<or> Q2 t2)) = ((P t1. t1 \<U> t2 I. Q1 t2) \<or> (P t1. t1 \<U> t2 I. Q2 t2))"
unfolding iUntil_def by blast

lemma iSince_disj_distrib: "
  (P t1. t1 \<S> t2 I. (Q1 t2 \<or> Q2 t2)) = ((P t1. t1 \<S> t2 I. Q1 t2) \<or> (P t1. t1 \<S> t2 I. Q2 t2))"
unfolding iSince_def by blast

lemma 
  iNext_iff: "(\<circle> t t0 I. P t) = (\<box> t [\<dots>0] \<oplus> (inext t0 I). P t)" and
  iLast_iff: "(\<ominus> t t0 I. P t) = (\<box> t [\<dots>0] \<oplus> (iprev t0 I). P t)"
by (fastforce simp: iTL_Next_defs iT_add iIN_0)+

lemma 
  iNext_iEx_iff: "(\<circle> t t0 I. P t) = (\<diamond> t [\<dots>0] \<oplus> (inext t0 I). P t)" and
  iLast_iEx_iff: "(\<ominus> t t0 I. P t) = (\<diamond> t [\<dots>0] \<oplus> (iprev t0 I). P t)"
by (fastforce simp: iTL_Next_defs iT_add iIN_0)+


lemma inext_singleton_cut_greater_not_empty_iff: "
  ({inext t0 I} \<down>> t0 \<noteq> {}) = (I \<down>> t0 \<noteq> {} \<and> t0 \<in> I)"
apply (simp add: cut_greater_singleton)
apply (case_tac "t0 \<in> I")
 prefer 2
 apply (simp add: not_in_inext_fix)
apply simp
apply (case_tac "I \<down>> t0 = {}")
 apply (simp add: cut_greater_empty_iff inext_all_le_fix)
apply (simp add: cut_greater_not_empty_iff inext_mono2)
done

lemma iprev_singleton_cut_less_not_empty_iff: "
  ({iprev t0 I} \<down>< t0 \<noteq> {}) = (I \<down>< t0 \<noteq> {} \<and> t0 \<in> I)"
apply (simp add: cut_less_singleton)
apply (case_tac "t0 \<in> I")
 prefer 2
 apply (simp add: not_in_iprev_fix)
apply simp
apply (case_tac "I \<down>< t0 = {}")
 apply (simp add: cut_less_empty_iff iprev_all_ge_fix)
apply (simp add: cut_less_not_empty_iff iprev_mono2)
done

lemma inext_singleton_cut_greater_empty_iff: "
  ({inext t0 I} \<down>> t0 = {}) = (I \<down>> t0 = {} \<or> t0 \<notin> I)"
apply (subst Not_eq_iff[symmetric])
apply (simp add: inext_singleton_cut_greater_not_empty_iff)
done

lemma iprev_singleton_cut_less_empty_iff: "
  ({iprev t0 I} \<down>< t0 = {}) = (I \<down>< t0 = {} \<or> t0 \<notin> I)"
apply (subst Not_eq_iff[symmetric])
apply (simp add: iprev_singleton_cut_less_not_empty_iff)
done

lemma iNextWeak_iff : "(\<circle>\<^sub>W t t0 I. P t) = ((\<circle> t t0 I. P t) \<or> (I \<down>> t0 = {}) \<or> t0 \<notin> I)"
apply (unfold iTL_defs)
apply (simp add: inext_singleton_cut_greater_empty_iff[symmetric] cut_greater_singleton)
done

lemma iNextStrong_iff : "(\<circle>\<^sub>S t t0 I. P t) = ((\<circle> t t0 I. P t) \<and> (I \<down>> t0 \<noteq> {}) \<and> t0 \<in> I)"
apply (unfold iTL_defs)
apply (simp add: inext_singleton_cut_greater_not_empty_iff[symmetric] cut_greater_singleton)
done

lemma iLastWeak_iff : "(\<ominus>\<^sub>W t t0 I. P t) = ((\<ominus> t t0 I. P t) \<or> (I \<down>< t0 = {}) \<or> t0 \<notin> I)"
apply (unfold iTL_defs)
apply (simp add: iprev_singleton_cut_less_empty_iff[symmetric] cut_less_singleton)
done

lemma iLastStrong_iff : "(\<ominus>\<^sub>S t t0 I. P t) = ((\<ominus> t t0 I. P t) \<and> (I \<down>< t0 \<noteq> {}) \<and> t0 \<in> I)"
apply (unfold iTL_defs)
apply (simp add: iprev_singleton_cut_less_not_empty_iff[symmetric] cut_less_singleton)
done

lemmas iTL_Next_iff =
  iNext_iff iLast_iff
  iNextWeak_iff iNextStrong_iff
  iLastWeak_iff iLastStrong_iff


lemma 
  iNext_iff_singleton       : "(\<circle> t t0 I. P t) = (\<box> t {inext t0 I}. P t)" and
  iLast_iff_singleton       : "(\<ominus> t t0 I. P t) = (\<box> t {iprev t0 I}. P t)"
by (fastforce simp: iTL_Next_defs iT_add iIN_0)+
lemmas iNextLast_iff_singleton = iNext_iff_singleton iLast_iff_singleton

lemma 
  iNext_iEx_iff_singleton   : "(\<circle> t t0 I. P t) = (\<diamond> t {inext t0 I}. P t)" and
  iLast_iEx_iff_singleton   : "(\<ominus> t t0 I. P t) = (\<diamond> t {iprev t0 I}. P t)"
by (fastforce simp: iTL_Next_defs iT_add iIN_0)+


lemma 
  iNextWeak_iAll_conv:  "(\<circle>\<^sub>W t t0 I. P t) = (\<box> t ({inext t0 I} \<down>> t0). P t)" and
  iNextStrong_iEx_conv: "(\<circle>\<^sub>S t t0 I. P t) = (\<diamond> t ({inext t0 I} \<down>> t0). P t)" and
  iLastWeak_iAll_conv:  "(\<ominus>\<^sub>W t t0 I. P t) = (\<box> t ({iprev t0 I} \<down>< t0). P t)" and
  iLastStrong_iEx_conv: "(\<ominus>\<^sub>S t t0 I. P t) = (\<diamond> t ({iprev t0 I} \<down>< t0). P t)"
by (simp_all add: iTL_Next_defs)


lemma 
  iAll_True[simp]: "\<box> t I. True" and
  iAll_False[simp]: "(\<box> t I. False) = (I = {})" and
  iEx_True[simp]: "(\<diamond> t I. True) = (I \<noteq> {})" and
  iEx_False[simp]: "\<not> (\<diamond> t I. False)" 
by blast+

lemma empty_iff_iAll_False:   "(I = {}) = (\<box> t I. False)" by blast
lemma not_empty_iff_iEx_True: "(I \<noteq> {}) = (\<diamond> t I. True)" by blast

lemma 
  iNext_True: "\<circle> t t0 I. True" and
  iNextWeak_True: "(\<circle>\<^sub>W t t0 I. True)" and
  iNext_False: "\<not> (\<circle> t t0 I. False)" and
  iNextStrong_False: "\<not> (\<circle>\<^sub>S t t0 I. False)"
by (simp_all add: iTL_defs)

lemma
  iNextStrong_True: "(\<circle>\<^sub>S t t0 I. True) = (I \<down>> t0 \<noteq> {} \<and> t0 \<in> I)" and
  iNextWeak_False: "(\<not> (\<circle>\<^sub>W t t0 I. False)) = (I \<down>> t0 \<noteq> {} \<and> t0 \<in> I)"
by (simp_all add: iTL_defs ex_in_conv inext_singleton_cut_greater_not_empty_iff)


lemma 
  iLast_True:        "\<ominus> t t0 I. True" and
  iLastWeak_True:    "(\<ominus>\<^sub>W t t0 I. True)" and
  iLast_False:       "\<not> (\<ominus> t t0 I. False)" and
  iLastStrong_False: "\<not> (\<ominus>\<^sub>S t t0 I. False)"
by (simp_all add: iTL_defs)

lemma
  iLastStrong_True:  "(\<ominus>\<^sub>S t t0 I. True) = (I \<down>< t0 \<noteq> {} \<and> t0 \<in> I)" and
  iLastWeak_False:   "(\<not> (\<ominus>\<^sub>W t t0 I. False)) = (I \<down>< t0 \<noteq> {} \<and> t0 \<in> I)"
by (simp_all add: iTL_defs ex_in_conv iprev_singleton_cut_less_not_empty_iff)

lemma iUntil_True_left[simp]: "(True. t' \<U> t I. Q t) = (\<diamond> t I. Q t)" 
by blast

lemma iUntil_True[simp]: "(P t'. t' \<U> t I. True) = (I \<noteq> {})"
apply (unfold iTL_defs)
apply (rule iffI)
 apply blast
apply (rule_tac x="iMin I" in bexI)
apply (simp add: cut_less_Min_empty iMinI_ex2)+
done

lemma iUntil_False_left[simp]: "(False. t' \<U> t I. Q t) = (I \<noteq> {} \<and> Q (iMin I))"
apply (case_tac "I = {}", blast)
apply (simp add: iTL_defs)
apply (rule iffI)
 apply clarsimp
 apply (drule iMin_equality)
  apply (simp add: cut_less_empty_iff)
 apply simp
apply (rule_tac x="iMin I" in bexI)
 apply (simp add: cut_less_Min_empty)
apply (simp add: iMinI_ex2)
done

lemma iUntil_False[simp]: "\<not> (P t'. t' \<U> t I. False)" 
by blast

lemma iSince_True_left[simp]: "(True. t' \<S> t I. Q t) = (\<diamond> t I. Q t)" 
by blast

lemma iSince_True_if: "
  (P t'. t' \<S> t I. True) = 
  (if finite I then I \<noteq> {} else \<diamond> t1 I. \<box> t2 (I \<down>> t1). P t2)"
apply (clarsimp simp: iTL_defs)
apply (rule iffI)
 apply clarsimp
apply (rule_tac x="Max I" in bexI)
 apply (simp add: cut_greater_Max_empty)
apply simp
done

corollary iSince_True_finite[simp]: "finite I \<Longrightarrow> (P t'. t' \<S> t I. True) = (I \<noteq> {})"
by (simp add: iSince_True_if)

lemma iSince_False_left[simp]: "(False. t' \<S> t I. Q t) = (finite I \<and> I \<noteq> {} \<and> Q (Max I))"
apply (simp add: iTL_defs)
apply (case_tac "I = {}", simp)
apply (case_tac "infinite I")
 apply (simp add: nat_cut_greater_infinite_not_empty)
apply (rule iffI)
 apply clarsimp
 apply (drule Max_equality)
   apply simp
  apply (simp add: cut_greater_empty_iff)
 apply simp
apply (rule_tac x="Max I" in bexI)
 apply (simp add: cut_greater_Max_empty)
apply simp
done

lemma iSince_False[simp]: "\<not> (P t'. t' \<S> t I. False)"
by blast

lemma iWeakUntil_True_left[simp]: "True. t' \<W> t I. Q t"
by (simp add: iWeakUntil_def)

lemma iWeakUntil_True[simp]: "P t'. t' \<W> t I. True"
apply (simp add: iTL_defs)
apply (case_tac "I = {}", simp)
apply (rule disjI2)
apply (rule_tac x="iMin I" in bexI)
 apply (simp add: cut_less_Min_empty)
apply (simp add: iMinI_ex2)
done

lemma iWeakUntil_False_left[simp]: "(False. t' \<W> t I. Q t) = (I = {} \<or> Q (iMin I))"
apply (simp add: iTL_defs)
apply (case_tac "I = {}", simp)
apply (rule iffI)
 apply (clarsimp simp: cut_less_empty_iff)
 apply (frule iMin_equality)
 apply simp+
apply (rule_tac x="iMin I" in bexI)
 apply (simp add: cut_less_Min_empty)
apply (simp add: iMinI_ex2)
done

lemma iWeakUntil_False[simp]: "(P t'. t' \<W> t I. False) = (\<box> t I. P t)"
by (simp add: iWeakUntil_def)

lemma iWeakSince_True_left[simp]: "True. t' \<B> t I. Q t"
by (simp add: iTL_defs)

lemma iWeakSince_True_disj: "
  (P t'. t' \<B> t I. True) = 
  (I = {} \<or> (\<diamond> t1 I. \<box> t2 (I \<down>> t1). P t2))"
unfolding iTL_defs by blast

lemma iWeakSince_True_finite[simp]: "finite I \<Longrightarrow> (P t'. t' \<B> t I. True)"
apply (simp add: iTL_defs)
apply (case_tac "I = {}", simp)
apply (rule disjI2)
apply (rule_tac x="Max I" in bexI)
 apply (simp add: cut_greater_Max_empty)
apply simp
done

lemma iWeakSince_False_left[simp]: "(False. t' \<B> t I. Q t) = (I = {} \<or> (finite I \<and> Q (Max I)))"
apply (simp add: iTL_defs)
apply (case_tac "I = {}", simp)
apply (case_tac "infinite I")
 apply (simp add: nat_cut_greater_infinite_not_empty)
apply (rule iffI)
 apply clarsimp
 apply (drule Max_equality)
   apply simp
  apply (simp add: cut_greater_empty_iff)
 apply simp
apply simp
apply (rule_tac x="Max I" in bexI)
 apply (simp add: cut_greater_Max_empty)
apply simp
done

lemma iWeakSince_False[simp]: "(P t'. t' \<B> t I. False) = (\<box> t I. P t)"
by (simp add: iWeakSince_def)

lemma iRelease_True_left[simp]: "(True. t' \<R> t I. Q t) = (I = {} \<or> Q (iMin I))"
apply (simp add: iTL_defs)
apply (case_tac "I = {}", simp)
apply (rule iffI)
 apply (erule disjE)
  apply (blast intro: iMinI2_ex2)
 apply clarsimp
 apply (drule_tac x="iMin I" in bspec)
  apply (blast intro: iMinI_ex2)
 apply simp
apply (rule disjI2)
apply (rule_tac x="iMin I" in bexI)
 apply fastforce
apply (simp add: iMinI_ex2)
done

lemma iRelease_True[simp]: "P t'. t' \<R> t I. True"
by (simp add: iTL_defs)

lemma iRelease_False_left[simp]: "(False. t' \<R> t I. Q t) = (\<box> t I. Q t)"
by (simp add: iTL_defs)

lemma iRelease_False[simp]: "(P t'. t' \<R> t I. False) = (I = {})"
unfolding iTL_defs by blast

lemma iTrigger_True_left[simp]: "(True. t' \<T> t I. Q t) = (I = {} \<or> (\<diamond> t1 I. \<box> t2 (I \<down>\<ge> t1). Q t2))"
unfolding iTL_defs by blast

lemma iTrigger_True[simp]: "P t'. t' \<T> t I. True"
by (simp add: iTL_defs)

lemma iTrigger_False_left[simp]: "(False. t' \<T> t I. Q t) = (\<box> t I. Q t)"
by (simp add: iTL_defs)

lemma iTrigger_False[simp]: "(P t'. t' \<T> t I. False) = (I = {})"
unfolding iTL_defs by blast

lemma 
  iUntil_TrueTrue[simp]: "(True. t' \<U> t I. True) = (I \<noteq> {})" and
  iSince_TrueTrue[simp]: "(True. t' \<S> t I. True) = (I \<noteq> {})" and
  iWeakUntil_TrueTrue[simp]: "True. t' \<W> t I. True" and
  iWeakSince_TrueTrue[simp]: "True. t' \<B> t I. True" and
  iRelease_TrueTrue[simp]: "True. t' \<R> t I. True" and
  iTrigger_TrueTrue[simp]: "True. t' \<T> t I. True"
by (simp_all add: iTL_defs ex_in_conv)


subsubsection \<open>Empty sets and singletons\<close>

lemma iAll_empty[simp]: "\<box> t {}. P t" by blast
lemma iEx_empty[simp]: "\<not> (\<diamond> t {}. P t)" by blast

lemma iUntil_empty[simp]: "\<not> (P t0. t0 \<U> t1 {}. Q t1)" by blast
lemma iSince_empty[simp]: "\<not> (P t0. t0 \<S> t1 {}. Q t1)" by blast
lemma iWeakUntil_empty[simp]: "P t0. t0 \<W> t1 {}. Q t1" by (simp add: iWeakUntil_def)
lemma iWeakSince_empty[simp]: "P t0. t0 \<B> t1 {}. Q t1" by (simp add: iWeakSince_def)

lemma iRelease_empty[simp]: "P t0. t0 \<R> t1 {}. Q t1" by (simp add: iRelease_def)
lemma iTrigger_empty[simp]: "P t0. t0 \<T> t1 {}. Q t1" by (simp add: iTrigger_def)

lemmas iTL_empty =
  iAll_empty iEx_empty
  iUntil_empty iSince_empty
  iWeakUntil_empty iWeakSince_empty
  iRelease_empty iTrigger_empty

lemma iAll_singleton[simp]: "(\<box> t' {t}. P t') = P t" by blast
lemma iEx_singleton[simp]: "(\<diamond> t' {t}. P t') = P t" by blast

lemma iUntil_singleton[simp]: "(P t0. t0 \<U> t1 {t}. Q t1) = Q t"
by (simp add: iUntil_def cut_less_singleton)

lemma iSince_singleton[simp]: "(P t0. t0 \<S> t1 {t}. Q t1) = Q t"
by (simp add: iSince_def cut_greater_singleton)

lemma iWeakUntil_singleton[simp]: "(P t0. t0 \<W> t1 {t}. Q t1) = (P t \<or> Q t)"
by (simp add: iWeakUntil_def cut_less_singleton)

lemma iWeakSince_singleton[simp]: "(P t0. t0 \<B> t1 {t}. Q t1) = (P t \<or> Q t)"
by (simp add: iWeakSince_def cut_greater_singleton)

lemma iRelease_singleton[simp]: "(P t0. t0 \<R> t1 {t}. Q t1) = Q t"
unfolding iRelease_def by blast

lemma iTrigger_singleton[simp]: "(P t0. t0 \<T> t1 {t}. Q t1) = Q t"
unfolding iTrigger_def by blast

lemmas iTL_singleton =
  iAll_singleton iEx_singleton
  iUntil_singleton iSince_singleton
  iWeakUntil_singleton iWeakSince_singleton
  iRelease_singleton iTrigger_singleton


subsubsection \<open>Conversions between temporal operators\<close>

lemma iAll_iEx_conv: "(\<box> t I. P t) = (\<not> (\<diamond> t I. \<not> P t))" by blast
lemma iEx_iAll_conv: "(\<diamond> t I. P t) = (\<not> (\<box> t I. \<not> P t))" by blast

lemma not_iAll[simp]: "(\<not> (\<box> t I. P t)) = (\<diamond> t I. \<not> P t)" by blast
lemma not_iEx[simp]: "(\<not> (\<diamond> t I. P t)) = (\<box> t I. \<not> P t)" by blast

lemma iUntil_iEx_conv: "(True. t' \<U> t I. P t) = (\<diamond> t I. P t)" by blast
lemma iSince_iEx_conv: "(True. t' \<S> t I. P t) = (\<diamond> t I. P t)" by blast

lemma iRelease_iAll_conv: "(False. t' \<R> t I. P t) = (\<box> t I. P t)"
by (simp add: iRelease_def)

lemma iTrigger_iAll_conv: "(False. t' \<T> t I. P t) = (\<box> t I. P t)"
by (simp add: iTrigger_def)

lemma iWeakUntil_iUntil_conv: "(P t'. t' \<W> t I. Q t) = ((P t'. t' \<U> t I. Q t) \<or> (\<box> t I. P t))"
unfolding iWeakUntil_def iUntil_def by blast

lemma iWeakSince_iSince_conv: "(P t'. t' \<B> t I. Q t) = ((P t'. t' \<S> t I. Q t) \<or> (\<box> t I. P t))"
unfolding iWeakSince_def iSince_def by blast

lemma iUntil_iWeakUntil_conv: "(P t'. t' \<U> t I. Q t) = ((P t'. t' \<W> t I. Q t) \<and> (\<diamond> t I. Q t))"
by (subst iWeakUntil_iUntil_conv, blast)

lemma iSince_iWeakSince_conv: "(P t'. t' \<S> t I. Q t) = ((P t'. t' \<B> t I. Q t) \<and> (\<diamond> t I. Q t))"
by (subst iWeakSince_iSince_conv, blast)


lemma iRelease_iWeakUntil_conv: "(P t'. t' \<R> t I. Q t) = (Q t'. t' \<W> t I. (Q t \<and> P t))"
apply (unfold iRelease_def iWeakUntil_def)
apply (simp add: cut_le_less_conv_if)
apply blast
done

lemma iRelease_iUntil_conv: "(P t'. t' \<R> t I. Q t) = ((\<box> t I. Q t) \<or> (Q t'. t' \<U> t I. (Q t \<and> P t)))"
by (fastforce simp: iRelease_iWeakUntil_conv iWeakUntil_iUntil_conv)

lemma iTrigger_iWeakSince_conv: "(P t'. t' \<T> t I. Q t) = (Q t'. t' \<B> t I. (Q t \<and> P t))"
apply (unfold iTrigger_def iWeakSince_def)
apply (simp add: cut_ge_greater_conv_if)
apply blast
done

lemma iTrigger_iSince_conv: "(P t'. t' \<T> t I. Q t) = ((\<box> t I. Q t) \<or> (Q t'. t' \<S> t I. (Q t \<and> P t)))"
by (fastforce simp: iTrigger_iWeakSince_conv iWeakSince_iSince_conv)

lemma iRelease_not_iUntil_conv: "(P t'. t' \<R> t I. Q t) = (\<not> (\<not> P t'. t' \<U> t I. \<not> Q t))"
apply (simp only: iUntil_def iRelease_def not_iAll not_iEx de_Morgan_conj not_not)
apply (case_tac "\<box> t I. Q t", blast)
apply (simp (no_asm_simp))
apply clarsimp
apply (rule iffI)
 apply (elim iexE, intro iallI, rename_tac t1 t2)
 apply (case_tac "t2 \<le> t1", blast)
 apply (simp add: linorder_not_le, blast)
apply (frule_tac t=t in ispec, assumption)
apply clarsimp
apply (rule_tac t="iMin {t \<in> I. P t}" in iexI)
 prefer 2
 apply (blast intro: subsetD[OF _ iMinI_ex])
apply (rule conjI)
 apply (blast intro: iMinI2)
apply (clarsimp simp: cut_le_mem_iff, rename_tac t1 t2)
apply (drule_tac t=t2 in ispec, assumption)
apply (clarsimp simp: cut_less_mem_iff)
apply (frule_tac x=t' in order_less_le_trans, assumption)
apply (drule not_less_iMin)
apply simp
done
lemma iUntil_not_iRelease_conv: "(P t'. t' \<U> t I. Q t) = (\<not> (\<not> P t'. t' \<R> t I. \<not> Q t))"
by (simp add: iRelease_not_iUntil_conv)

text \<open>The Trigger operator \isasymT is a past operator,
  so that it is used for time intervals,
  that are bounded by a current time point, and thus are finite.
  For an infinite interval
  the stated relation to the Since operator \isasymS would not be fulfilled.\<close>
lemma iTrigger_not_iSince_conv: "finite I \<Longrightarrow> (P t'. t' \<T> t I. Q t) = (\<not> (\<not> P t'. t' \<S> t I. \<not> Q t))"
apply (unfold iTrigger_def iSince_def)
apply (case_tac "\<box> t I. Q t", blast)
apply (simp (no_asm_simp))
apply clarsimp
apply (rule iffI)
 apply (elim iexE conjE, rule iallI, rename_tac t1 t2)
 apply (case_tac "t2 \<ge> t1", blast)
 apply (simp add: linorder_not_le, blast)
apply (frule_tac t=t in ispec, assumption)
 apply (erule disjE, blast)
apply (erule iexE)
apply (subgoal_tac "finite {t \<in> I. P t}")
 prefer 2
 apply (blast intro: subset_finite_imp_finite)
apply (rule_tac t="Max {t \<in> I. P t}" in iexI)
 prefer 2
 apply (blast intro: subsetD[OF _ MaxI])
apply (rule conjI)
 apply (blast intro: MaxI2)
apply (clarsimp simp: cut_ge_mem_iff, rename_tac t1 t2)
apply (drule_tac t=t2 in ispec, assumption)
apply (clarsimp simp: cut_greater_mem_iff, rename_tac t')
apply (frule_tac z=t' in order_le_less_trans, assumption)
apply (drule_tac A="{t \<in> I. P t}" in not_greater_Max[rotated 1])
apply simp+
done

lemma iSince_not_iTrigger_conv: "finite I \<Longrightarrow> (P t'. t' \<S> t I. Q t) = (\<not> (\<not> P t'. t' \<T> t I. \<not> Q t))"
by (simp add: iTrigger_not_iSince_conv)


lemma not_iUntil: "
  (\<not> (P t1. t1 \<U> t2 I. Q t2)) =
  (\<box> t I. (Q t \<longrightarrow> (\<diamond> t' (I \<down>< t). \<not> P t')))"
unfolding iTL_defs by blast

lemma not_iSince: "
  (\<not> (P t1. t1 \<S> t2 I. Q t2)) =
  (\<box> t I. (Q t \<longrightarrow> (\<diamond> t' (I \<down>> t). \<not> P t')))"
unfolding iTL_defs by blast


lemma iWeakUntil_conj_iUntil_conv: "
  (P t1. t1 \<W> t2 I. (P t2 \<and> Q t2)) = (\<not> (\<not> Q t1. t1 \<U> t2 I. \<not> P t2))"
by (simp add: iRelease_not_iUntil_conv[symmetric] iRelease_iWeakUntil_conv)

lemma iUntil_disj_iUntil_conv: "
  (P t1 \<or> Q t1. t1 \<U> t2 I. Q t2) = 
  (P t1. t1 \<U> t2 I. Q t2)"
apply (unfold iUntil_def)
apply (rule iffI)
 prefer 2
 apply blast
apply (clarsimp, rename_tac t1)
apply (rule_tac t="iMin {t \<in> I. Q t}" in iexI)
 apply (subgoal_tac "Q (iMin {t \<in> I. Q t})")
  prefer 2
  apply (blast intro: iMinI2)
 apply (clarsimp, rename_tac t2)
 apply (frule Collect_not_less_iMin, simp)
 apply (subgoal_tac "t2 < t1")
  prefer 2
  apply (rule order_less_le_trans, assumption)
  apply (simp add: Collect_iMin_le)
 apply blast
apply (rule subsetD[OF _ iMinI])
apply blast+
done

lemma iWeakUntil_disj_iWeakUntil_conv: "
  (P t1 \<or> Q t1. t1 \<W> t2 I. Q t2) = 
  (P t1. t1 \<W> t2 I. Q t2)"
apply (simp only: iWeakUntil_iUntil_conv iUntil_disj_iUntil_conv)
apply (case_tac "P t1. t1 \<U> t2 I. Q t2", simp+)
apply (case_tac "\<box> t I. P t", blast)
apply (simp add: not_iUntil)
apply (clarsimp, rename_tac t1)
apply (case_tac "\<not> Q t1", blast)
apply (subgoal_tac "iMin {t \<in> I. Q t} \<in> I")
 prefer 2
 apply (blast intro: subsetD[OF _ iMinI])
apply (frule_tac t="iMin {t \<in> I. Q t}" in ispec, assumption)
apply (drule mp)
 apply (blast intro: iMinI2)
apply (clarsimp, rename_tac t2)
apply (subgoal_tac "\<not> Q t2")
 prefer 2
 apply (drule Collect_not_less_iMin)
 apply (simp add: cut_less_mem_iff)
apply blast
done

lemma iWeakUntil_iUntil_conj_conv: "
  (P t1. t1 \<W> t2 I. Q t2) = 
  (\<not> (\<not> Q t1. t1 \<U> t2 I. (\<not> P t2 \<and> \<not> Q t2)))"
apply (subst iWeakUntil_disj_iWeakUntil_conv[symmetric])
apply (subst de_Morgan_disj[symmetric])
apply (subst iWeakUntil_conj_iUntil_conv[symmetric])
apply (simp add: conj_disj_distribR conj_disj_absorb)
done


text \<open>Negation and temporal operators\<close>
 
lemma 
  not_iNext[simp]: "(\<not> (\<circle> t t0 I. P t)) = (\<circle> t t0 I. \<not> P t)" and
  not_iNextWeak[simp]: "(\<not> (\<circle>\<^sub>W t t0 I. P t)) = (\<circle>\<^sub>S t t0 I. \<not> P t)" and
  not_iNextStrong[simp]: "(\<not> (\<circle>\<^sub>S t t0 I. P t)) = (\<circle>\<^sub>W t t0 I. \<not> P t)" and
  not_iLast[simp]: "(\<not> (\<ominus> t t0 I. P t)) = (\<ominus> t t0 I. \<not> P t)" and
  not_iLastWeak[simp]: "(\<not> (\<ominus>\<^sub>W t t0 I. P t)) = (\<ominus>\<^sub>S t t0 I. \<not> P t)" and
  not_iLastStrong[simp]: "(\<not> (\<ominus>\<^sub>S t t0 I. P t)) = (\<ominus>\<^sub>W t t0 I. \<not> P t)"
by (simp_all add: iTL_Next_defs)

lemma not_iWeakUntil: "
  (\<not> (P t1. t1 \<W> t2 I. Q t2)) =
  ((\<box> t I. (Q t \<longrightarrow> (\<diamond> t' (I \<down>< t). \<not> P t'))) \<and> (\<diamond> t I. \<not> P t))"
by (simp add: iWeakUntil_iUntil_conv not_iUntil)
lemma not_iWeakSince: "
  (\<not> (P t1. t1 \<B> t2 I. Q t2)) =
  ((\<box> t I. (Q t \<longrightarrow> (\<diamond> t' (I \<down>> t). \<not> P t'))) \<and> (\<diamond> t I. \<not> P t))"
by (simp add: iWeakSince_iSince_conv not_iSince)

lemma not_iRelease: "
  (\<not> (P t'. t' \<R> t I. Q t)) = 
  ((\<diamond> t I. \<not> Q t) \<and> (\<box> t I. P t \<longrightarrow> (\<diamond> t I \<down>\<le> t. \<not> Q t)))"
by (simp add: iRelease_def)

lemma not_iRelease_iUntil_conv: "
  (\<not> (P t'. t' \<R> t I. Q t)) = (\<not> P t'. t' \<U> t I. \<not> Q t)"
by (simp add: iUntil_not_iRelease_conv)

lemma not_iTrigger: "
  (\<not> (P t'. t' \<T> t I. Q t)) = 
  ((\<diamond> t I. \<not> Q t) \<and> (\<box> t I. \<not> P t \<or> (\<diamond> t I \<down>\<ge> t. \<not> Q t)))"
by (simp add: iTrigger_def)

lemma not_iTrigger_iSince_conv: "
  finite I \<Longrightarrow> (\<not> (P t'. t' \<T> t I. Q t)) = (\<not> P t'. t' \<S> t I. \<not> Q t)"
by (simp add: iSince_not_iTrigger_conv)


subsubsection \<open>Some implication results\<close>

lemma all_imp_iall: "\<forall>x. P x \<Longrightarrow> \<box> t I. P t" by blast
lemma bex_imp_lex:  "\<diamond> t I. P t \<Longrightarrow> \<exists>x. P x" by blast

lemma iAll_imp_iEx: "I \<noteq> {} \<Longrightarrow> \<box> t I. P t \<Longrightarrow> \<diamond> t I. P t" by blast
lemma i_set_iAll_imp_iEx: "I \<in> i_set \<Longrightarrow> \<box> t I. P t \<Longrightarrow> \<diamond> t I. P t"
by (rule iAll_imp_iEx, rule i_set_imp_not_empty)

lemmas iT_iAll_imp_iEx = iT_not_empty[THEN iAll_imp_iEx]

lemma iUntil_imp_iEx: "P t1. t1 \<U> t2 I. Q t2 \<Longrightarrow> \<diamond> t I. Q t"
unfolding iTL_defs  by blast

lemma iSince_imp_iEx: "P t1. t1 \<S> t2 I. Q t2 \<Longrightarrow> \<diamond> t I. Q t"
unfolding iTL_defs  by blast

lemma iall_subset_imp_iall: "\<lbrakk> \<box> t B. P t; A \<subseteq> B \<rbrakk> \<Longrightarrow> \<box> t A. P t"
by blast

lemma iex_subset_imp_iex: "\<lbrakk> \<diamond> t A. P t; A \<subseteq> B \<rbrakk> \<Longrightarrow> \<diamond> t B. P t"
by blast

lemma iall_mp: "\<lbrakk> \<box> t I. P t \<longrightarrow> Q t; \<box> t I. P t \<rbrakk> \<Longrightarrow> \<box> t I. Q t" by blast
lemma iex_mp: "\<lbrakk> \<box> t I. P t \<longrightarrow> Q t; \<diamond> t I. P t \<rbrakk> \<Longrightarrow> \<diamond> t I. Q t" by blast


lemma iUntil_imp: "
  \<lbrakk> P1 t1. t1 \<U> t2 I. Q t2; \<box> t I. P1 t \<longrightarrow> P2 t \<rbrakk> \<Longrightarrow> P2 t1. t1 \<U> t2 I. Q t2"
unfolding iTL_defs  by blast

lemma iSince_imp: "
  \<lbrakk> P1 t1. t1 \<S> t2 I. Q t2; \<box> t I. P1 t \<longrightarrow> P2 t \<rbrakk> \<Longrightarrow> P2 t1. t1 \<S> t2 I. Q t2"
unfolding iTL_defs  by blast

lemma iWeakUntil_imp: "
  \<lbrakk> P1 t1. t1 \<W> t2 I. Q t2; \<box> t I. P1 t \<longrightarrow> P2 t \<rbrakk> \<Longrightarrow> P2 t1. t1 \<W> t2 I. Q t2"
unfolding iTL_defs  by blast

lemma iWeakSince_imp: "
  \<lbrakk> P1 t1. t1 \<B> t2 I. Q t2; \<box> t I. P1 t \<longrightarrow> P2 t \<rbrakk> \<Longrightarrow> P2 t1. t1 \<B> t2 I. Q t2"
unfolding iTL_defs  by blast

lemma iRelease_imp: "
  \<lbrakk> P1 t1. t1 \<R> t2 I. Q t2; \<box> t I. P1 t \<longrightarrow> P2 t \<rbrakk> \<Longrightarrow> P2 t1. t1 \<R> t2 I. Q t2"
unfolding iTL_defs  by blast

lemma iTrigger_imp: "
  \<lbrakk> P1 t1. t1 \<T> t2 I. Q t2; \<box> t I. P1 t \<longrightarrow> P2 t \<rbrakk> \<Longrightarrow> P2 t1. t1 \<T> t2 I. Q t2"
unfolding iTL_defs  by blast


lemma iMin_imp_iUntil: "
  \<lbrakk> I \<noteq> {}; Q (iMin I) \<rbrakk> \<Longrightarrow> P t'. t' \<U> t I. Q t"
apply (unfold iUntil_def)
apply (rule_tac t="iMin I" in iexI)
 apply (simp add: cut_less_Min_empty)
apply (blast intro: iMinI_ex2)
done

lemma Max_imp_iSince: "
  \<lbrakk> finite I; I \<noteq> {}; Q (Max I) \<rbrakk> \<Longrightarrow> P t'. t' \<S> t I. Q t"
apply (unfold iSince_def)
apply (rule_tac t="Max I" in iexI)
 apply (simp add: cut_greater_Max_empty)
apply (blast intro: Max_in)
done


subsubsection \<open>Congruence rules for temporal operators' predicates\<close>

lemma iAll_cong: "\<box> t I. f t = g t \<Longrightarrow> (\<box> t I. P (f t) t) = (\<box> t I. P (g t) t)"
unfolding iTL_defs by simp

lemma iEx_cong: "\<box> t I. f t = g t \<Longrightarrow> (\<diamond> t I. P (f t) t) = (\<diamond> t I. P (g t) t)"
unfolding iTL_defs by simp

lemma iUntil_cong1: "
  \<box> t I. f t = g t \<Longrightarrow> 
  (P (f t1) t1. t1 \<U> t2 I. Q t2) = (P (g t1) t1. t1 \<U> t2 I. Q t2)"
apply (unfold iUntil_def)
apply (rule iEx_cong)
apply (rule iallI)
apply (rule_tac f="\<lambda>x. (Q t \<and> x)" in arg_cong, rename_tac t)
apply (rule iAll_cong[OF iall_subset_imp_iall[OF _ cut_less_subset]])
apply (rule iallI, rename_tac t')
apply (drule_tac t=t' in ispec)
apply simp+
done

lemma iUntil_cong2: "
  \<box> t I. f t = g t \<Longrightarrow> 
  (P t1. t1 \<U> t2 I. Q (f t2) t2) = (P t1. t1 \<U> t2 I. Q (g t2) t2)"
apply (unfold iUntil_def)
apply (rule iEx_cong)
apply (rule iallI, rename_tac t)
apply (drule_tac t=t in ispec)
apply simp+
done

lemma iSince_cong1: "
  \<box> t I. f t = g t \<Longrightarrow> 
  (P (f t1) t1. t1 \<S> t2 I. Q t2) = (P (g t1) t1. t1 \<S> t2 I. Q t2)"
apply (unfold iSince_def)
apply (rule iEx_cong)
apply (rule iallI, rename_tac t)
apply (rule_tac f="\<lambda>x. (Q t \<and> x)" in arg_cong)
apply (rule iAll_cong[OF iall_subset_imp_iall[OF _ cut_greater_subset]])
apply (rule iallI, rename_tac t')
apply (drule_tac t=t' in ispec)
apply simp+
done

lemma iSince_cong2: "
  \<box> t I. f t = g t \<Longrightarrow> 
  (P t1. t1 \<S> t2 I. Q (f t2) t2) = (P t1. t1 \<S> t2 I. Q (g t2) t2)"
apply (unfold iSince_def)
apply (rule iEx_cong)
apply (rule iallI, rename_tac t)
apply (drule_tac t=t in ispec)
apply simp+
done


lemma bex_subst: "
  \<forall>x\<in>A. P x \<longrightarrow> (Q x = Q' x) \<Longrightarrow>
  (\<exists>x\<in>A. P x \<and> Q x) = (\<exists>x\<in>A. P x \<and> Q' x)" 
by blast

lemma iEx_subst: "
  \<box> t I. P t \<longrightarrow> (Q t = Q' t) \<Longrightarrow>
  (\<diamond> t I. P t \<and> Q t) = (\<diamond> t I. P t \<and> Q' t)"
by blast


subsubsection \<open>Temporal operators with set unions/intersections and subsets\<close>

lemma iAll_subset: "\<lbrakk> A \<subseteq> B; \<box> t B. P t \<rbrakk> \<Longrightarrow> \<box> t A. P t"
by (rule iall_subset_imp_iall)

lemma iEx_subset: "\<lbrakk> A \<subseteq> B; \<diamond> t A. P t \<rbrakk> \<Longrightarrow> \<diamond> t B. P t"
by (rule iex_subset_imp_iex)

lemma iUntil_append: "
  \<lbrakk> finite A; Max A \<le> iMin B \<rbrakk> \<Longrightarrow>
  P t1. t1 \<U> t2 A. Q t2 \<Longrightarrow> P t1. t1 \<U> t2 (A \<union> B). Q t2"
apply (case_tac "A = {}", simp)
apply (unfold iUntil_def)
apply (rule iEx_subset[OF Un_upper1])
apply (rule_tac f="\<lambda>t. A \<down>< t" and g="\<lambda>t. (A \<union> B) \<down>< t" in subst[OF iEx_cong, rule_format])
 apply (clarsimp simp: cut_less_Un, rename_tac t t')
 apply (cut_tac t=t and I=B in cut_less_Min_empty)
 apply simp+
done

lemma iSince_prepend: "
  \<lbrakk> finite A; Max A \<le> iMin B \<rbrakk> \<Longrightarrow>
  P t1. t1 \<S> t2 B. Q t2 \<Longrightarrow> P t1. t1 \<S> t2 (A \<union> B). Q t2"
apply (case_tac "B = {}", simp)
apply (unfold iSince_def)
apply (rule iEx_subset[OF Un_upper2])
apply (rule_tac f="\<lambda>t. B \<down>> t" and g="\<lambda>t. (A \<union> B) \<down>> t" in subst[OF iEx_cong, rule_format])
 apply (clarsimp simp: cut_greater_Un, rename_tac t t')
 apply (cut_tac t=t and I=A in cut_greater_Max_empty)
 apply (simp add: iMin_ge_iff)+
done

lemma 
  iAll_union: "\<lbrakk> \<box> t A. P t; \<box> t B. P t \<rbrakk> \<Longrightarrow> \<box> t (A \<union> B). P t" and
  iAll_union_conv: "(\<box> t A \<union> B. P t) = ((\<box> t A. P t) \<and> (\<box> t B. P t))"
by blast+

lemma 
  iEx_union: "(\<diamond> t A. P t) \<or> (\<diamond> t B. P t) \<Longrightarrow> \<diamond> t (A \<union> B). P t" and
  iEx_union_conv: "(\<diamond> t (A \<union> B). P t) = ((\<diamond> t A. P t) \<or> (\<diamond> t B. P t))" 
by blast+

lemma iAll_inter: "(\<box> t A. P t) \<or> (\<box> t B. P t) \<Longrightarrow> \<box> t (A \<inter> B). P t" by blast

lemma not_iEx_inter: "
  \<exists>A B P. (\<diamond> t A. P t) \<and> (\<diamond> t B. P t) \<and> \<not> (\<diamond> t (A \<inter> B). P t)"
by (rule_tac x="{0}" in exI, rule_tac x="{Suc 0}" in exI, blast)

lemma 
  iAll_insert: "\<lbrakk> P t; \<box> t I. P t \<rbrakk> \<Longrightarrow> \<box> t' (insert t I). P t'" and
  iAll_insert_conv: "(\<box> t' (insert t I). P t') = (P t \<and> (\<box> t' I. P t'))"
by blast+

lemma 
  iEx_insert: "\<lbrakk> P t \<or> (\<diamond> t I. P t) \<rbrakk> \<Longrightarrow> \<diamond> t' (insert t I). P t'" and
  iEx_insert_conv: "(\<diamond> t' (insert t I). P t') = (P t \<or> (\<diamond> t' I. P t'))"
by blast+


subsection \<open>Further results for temporal operators\<close>

lemma Collect_minI_iEx: "\<diamond> t I. P t \<Longrightarrow> \<diamond> t I. P t \<and> (\<box> t' (I \<down>< t). \<not> P t')"
by (unfold iAll_def iEx_def, rule Collect_minI_ex_cut)

lemma iUntil_disj_conv1: "
  I \<noteq> {} \<Longrightarrow>
  (P t'. t' \<U> t I. Q t) = (Q (iMin I) \<or> (P t'. t' \<U> t I. Q t \<and> iMin I < t))"
apply (case_tac "Q (iMin I)")
 apply (simp add: iMin_imp_iUntil)
apply (unfold iUntil_def, blast)
done

lemma iSince_disj_conv1: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow>
  (P t'. t' \<S> t I. Q t) = (Q (Max I) \<or> (P t'. t' \<S> t I. Q t \<and> t < Max I))"
apply (case_tac "Q (Max I)")
 apply (simp add: Max_imp_iSince)
apply (unfold iSince_def, blast)
done

lemma iUntil_next: "
  I \<noteq> {} \<Longrightarrow>
  (P t'. t' \<U> t I. Q t) = 
  (Q (iMin I) \<or> (P (iMin I) \<and> (P t'. t' \<U> t (I \<down>> (iMin I)). Q t)))"
apply (case_tac "Q (iMin I)")
 apply (simp add: iMin_imp_iUntil)
apply (simp add: iUntil_def)
apply (frule iMinI_ex2)
apply blast
done

lemma iSince_prev: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow>
  (P t'. t' \<S> t I. Q t) = 
  (Q (Max I) \<or> (P (Max I) \<and> (P t'. t' \<S> t (I \<down>< Max I). Q t)))"
apply (case_tac "Q (Max I)")
 apply (simp add: Max_imp_iSince)
apply (simp add: iSince_def)
apply (frule Max_in, assumption)
apply blast
done

lemma iNext_induct_rule: "
  \<lbrakk> P (iMin I); \<box> t I. (P t \<longrightarrow> (\<circle> t' t I. P t')); t \<in> I \<rbrakk> \<Longrightarrow> P t"
apply (rule inext_induct[of _ I])
  apply simp
 apply (drule_tac t=n in ispec, assumption)
 apply (simp add: iNext_def)
apply assumption
done

lemma iNext_induct: "
  \<lbrakk> P (iMin I); \<box> t I. (P t \<longrightarrow> (\<circle> t' t I. P t')) \<rbrakk> \<Longrightarrow> \<box> t I. P t"
by (rule iallI, rule iNext_induct_rule)

lemma iLast_induct_rule: "
  \<lbrakk> P (Max I); \<box> t I. (P t \<longrightarrow> (\<ominus> t' t I. P t')); finite I; t \<in> I \<rbrakk> \<Longrightarrow> P t"
apply (rule iprev_induct[of _ I])
  apply assumption
 apply (drule_tac t=n in ispec, assumption)
 apply (simp add: iLast_def)
apply assumption+
done

lemma iLast_induct: "
  \<lbrakk> P (Max I); \<box> t I. (P t \<longrightarrow> (\<ominus> t' t I. P t')); finite I \<rbrakk> \<Longrightarrow> \<box> t I. P t"
by (rule iallI, rule iLast_induct_rule)


lemma iUntil_conj_not: "((P t1 \<and> \<not> Q t1). t1 \<U> t2 I. Q t2) = (P t1. t1 \<U> t2 I. Q t2)"
apply (unfold iUntil_def)
apply (rule iffI)
 apply blast
apply (clarsimp, rename_tac t)
apply (rule_tac t="iMin {x \<in> I. Q x}" in iexI)
 apply (rule conjI)
  apply (blast intro: iMinI2)
 apply (clarsimp simp: cut_less_mem_iff, rename_tac t1)
 apply (subgoal_tac "iMin {x \<in> I. Q x} \<le> t")
  prefer 2
  apply (simp add: iMin_le)
 apply (frule order_less_le_trans, assumption)
 apply (drule_tac t=t1 in ispec, simp add: cut_less_mem_iff)
 apply (rule ccontr, simp)
 apply (subgoal_tac "t1 \<in> {x \<in> I. Q x}")
  prefer 2
  apply blast
 apply (drule_tac k=t1 and I="{x \<in> I. Q x}" in iMin_le)
 apply simp
apply (blast intro: subsetD[OF _ iMinI])
done

lemma iWeakUntil_conj_not: "((P t1 \<and> \<not> Q t1). t1 \<W> t2 I. Q t2) = (P t1. t1 \<W> t2 I. Q t2)"
by (simp only: iWeakUntil_iUntil_conv iUntil_conj_not, blast)

lemma iSince_conj_not: "finite I \<Longrightarrow>
  ((P t1 \<and> \<not> Q t1). t1 \<S> t2 I. Q t2) = (P t1. t1 \<S> t2 I. Q t2)"
apply (simp only: iSince_def)
apply (case_tac "I = {}", simp)
apply (rule iffI)  
 apply blast
apply (clarsimp, rename_tac t)
apply (subgoal_tac "finite {x \<in> I. Q x}")
 prefer 2
 apply fastforce
apply (rule_tac t="Max {x \<in> I. Q x}" in iexI)
 apply (rule conjI)
  apply (blast intro: MaxI2)
 apply (clarsimp simp: cut_greater_mem_iff, rename_tac t1)
 apply (subgoal_tac "t \<le> Max {x \<in> I. Q x}")
  prefer 2
  apply simp
 apply (frule order_le_less_trans, assumption)
 apply (drule_tac t=t1 in ispec, simp add: cut_greater_mem_iff)
 apply (rule ccontr, simp)
 apply (subgoal_tac "t1 \<in> {x \<in> I. Q x}")
  prefer 2
  apply blast
 apply (drule  not_greater_Max[rotated 1], simp+)
apply (rule subsetD[OF _ MaxI], fastforce+)
done

lemma iWeakSince_conj_not: "finite I \<Longrightarrow>
  ((P t1 \<and> \<not> Q t1). t1 \<B> t2 I. Q t2) = (P t1. t1 \<B> t2 I. Q t2)"
by (simp only: iWeakSince_iSince_conv iSince_conj_not, blast)


lemma iNextStrong_imp_iNextWeak: "(\<circle>\<^sub>S t t0 I. P t) \<longrightarrow> (\<circle>\<^sub>W t t0 I. P t)"
unfolding iTL_Next_defs by blast
lemma iLastStrong_imp_iLastWeak: "(\<ominus>\<^sub>S t t0 I. P t) \<longrightarrow> (\<ominus>\<^sub>W t t0 I. P t)"
unfolding iTL_Next_defs by blast

lemma infin_imp_iNextWeak_iNextStrong_eq_iNext: "
  \<lbrakk> infinite I; t0 \<in> I \<rbrakk> \<Longrightarrow> 
  ((\<circle>\<^sub>W t t0 I. P t) = (\<circle> t t0 I. P t)) \<and> ((\<circle>\<^sub>S t t0 I. P t) = (\<circle> t t0 I. P t))"
by (simp add: iTL_Next_iff nat_cut_greater_infinite_not_empty)

lemma infin_imp_iNextWeak_eq_iNext: "\<lbrakk> infinite I; t0 \<in> I \<rbrakk> \<Longrightarrow> (\<circle>\<^sub>W t t0 I. P t) = (\<circle> t t0 I. P t)"
by (simp add: infin_imp_iNextWeak_iNextStrong_eq_iNext)
lemma infin_imp_iNextStrong_eq_iNext: "\<lbrakk> infinite I; t0 \<in> I \<rbrakk> \<Longrightarrow> (\<circle>\<^sub>S t t0 I. P t) = (\<circle> t t0 I. P t)"
by (simp add: infin_imp_iNextWeak_iNextStrong_eq_iNext)
lemma infin_imp_iNextStrong_eq_iNextWeak: "\<lbrakk> infinite I; t0 \<in> I \<rbrakk> \<Longrightarrow> (\<circle>\<^sub>S t t0 I. P t) = (\<circle>\<^sub>W t t0 I. P t)"
by (simp add: infin_imp_iNextWeak_eq_iNext infin_imp_iNextStrong_eq_iNext)

lemma 
  not_in_iNext_eq: "t0 \<notin> I \<Longrightarrow> (\<circle> t t0 I. P t) = (P t0)" and
  not_in_iLast_eq: "t0 \<notin> I \<Longrightarrow> (\<ominus> t t0 I. P t) = (P t0)"
by (simp_all add: iTL_defs not_in_inext_fix not_in_iprev_fix)

lemma 
  not_in_iNextWeak_eq: "t0 \<notin> I \<Longrightarrow> (\<circle>\<^sub>W t t0 I. P t)" and
  not_in_iLastWeak_eq: "t0 \<notin> I \<Longrightarrow> (\<ominus>\<^sub>W t t0 I. P t)"
by (simp_all add: iNextWeak_iff iLastWeak_iff)

lemma 
  not_in_iNextStrong_eq: "t0 \<notin> I \<Longrightarrow> \<not> (\<circle>\<^sub>S t t0 I. P t)" and
  not_in_iLastStrong_eq: "t0 \<notin> I \<Longrightarrow> \<not> (\<ominus>\<^sub>S t t0 I. P t)"
by (simp_all add: iNextStrong_iff iLastStrong_iff)

lemma 
  iNext_UNIV: "(\<circle> t t0 UNIV. P t) = P (Suc t0)" and
  iNextWeak_UNIV: "(\<circle>\<^sub>W t t0 UNIV. P t) = P (Suc t0)" and
  iNextStrong_UNIV: "(\<circle>\<^sub>S t t0 UNIV. P t) = P (Suc t0)"
by (simp_all add: iTL_Next_defs inext_UNIV cut_greater_singleton)

lemma 
  iLast_UNIV: "(\<ominus> t t0 UNIV. P t) = P (t0 - Suc 0)" and
  iLastWeak_UNIV: "(\<ominus>\<^sub>W t t0 UNIV. P t) = (if 0 < t0 then P (t0 - Suc 0) else True)" and
  iLastStrong_UNIV: "(\<ominus>\<^sub>S t t0 UNIV. P t) = (if 0 < t0 then P (t0 - Suc 0) else False)"
by (simp_all add: iTL_Next_defs iprev_UNIV cut_less_singleton)

lemmas iTL_Next_UNIV = 
  iNext_UNIV iNextWeak_UNIV iNextStrong_UNIV
  iLast_UNIV iLastWeak_UNIV iLastStrong_UNIV

lemma inext_nth_iNext_Suc: "(\<circle> t (I \<rightarrow> n) I. P t) = P (I \<rightarrow> Suc n)"
by (simp add: iNext_def)

lemma iprev_nth_iLast_Suc: "(\<ominus> t (I \<leftarrow> n) I. P t) = P (I \<leftarrow> Suc n)"
by (simp add: iLast_def)


subsection \<open>Temporal operators and arithmetic interval operators\<close>

text \<open>
  Shifting intervals through addition and subtraction of constants. 
  Mirroring intervals through subtraction of intervals from constants. 
  Expanding and compressing intervals through multiplication and division by constants.\<close>

text \<open>Always operator\<close>
lemma iT_Plus_iAll_conv: "(\<box> t I \<oplus> k. P t) = (\<box> t I. P (t + k))"
apply (unfold iAll_def Ball_def)
apply (rule iffI)
 apply (clarify, rename_tac x)
 apply (drule_tac x="x + k" in spec)
 apply (simp add: iT_Plus_mem_iff2)
apply (clarify, rename_tac x)
apply (drule_tac x="x - k" in spec)
apply (simp add: iT_Plus_mem_iff)
done

lemma iT_Mult_iAll_conv: "(\<box> t I \<otimes> k. P t) = (\<box> t I. P (t * k))"
apply (unfold iAll_def Ball_def)
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty)
apply (case_tac "k = 0")
 apply (force simp: iT_Mult_0 iTILL_0)
apply (rule iffI)
 apply (clarify, rename_tac x)
 apply (drule_tac x="x * k" in spec)
 apply (simp add: iT_Mult_mem_iff2)
apply (clarify, rename_tac x)
apply (drule_tac x="x div k" in spec)
apply (simp add: iT_Mult_mem_iff mod_0_div_mult_cancel)
done

lemma iT_Plus_neg_iAll_conv: "(\<box> t I \<oplus>- k. P t) = (\<box> t (I \<down>\<ge> k). P (t - k))"
apply (unfold iAll_def Ball_def)
apply (rule iffI)
 apply (clarify, rename_tac x)
 apply (drule_tac x="x - k" in spec)
 apply (simp add: iT_Plus_neg_mem_iff2)
apply (clarify, rename_tac x)
apply (drule_tac x="x + k" in spec)
apply (simp add: iT_Plus_neg_mem_iff cut_ge_mem_iff)
done

lemma iT_Minus_iAll_conv: "(\<box> t k \<ominus> I. P t) = (\<box> t (I \<down>\<le> k). P (k - t))"
apply (unfold iAll_def Ball_def)
apply (rule iffI)
 apply (clarify, rename_tac x)
 apply (drule_tac x="k - x" in spec)
 apply (simp add: iT_Minus_mem_iff)
apply (clarify, rename_tac x)
apply (drule_tac x="k - x" in spec)
apply (simp add: iT_Minus_mem_iff cut_le_mem_iff)
done

lemma iT_Div_iAll_conv: "(\<box> t I \<oslash> k. P t) = (\<box> t I. P (t div k))"
apply (case_tac "I = {}")
 apply (simp add: iT_Div_empty)
apply (case_tac "k = 0")
 apply (force simp: iT_Div_0 iTILL_0)
apply (unfold iAll_def Ball_def)
apply (rule iffI)
 apply (clarify, rename_tac x)
 apply (drule_tac x="x div k" in spec)
 apply (simp add: iT_Div_imp_mem)
apply (blast dest: iT_Div_mem_iff[THEN iffD1])
done

lemmas iT_arith_iAll_conv = 
  iT_Plus_iAll_conv
  iT_Mult_iAll_conv
  iT_Plus_neg_iAll_conv
  iT_Minus_iAll_conv
  iT_Div_iAll_conv

text \<open>Eventually operator\<close>
lemma 
  iT_Plus_iEx_conv: "(\<diamond> t I \<oplus> k. P t) = (\<diamond> t I. P (t + k))" and
  iT_Mult_iEx_conv: "(\<diamond> t I \<otimes> k. P t) = (\<diamond> t I. P (t * k))" and
  iT_Plus_neg_iEx_conv: "(\<diamond> t I \<oplus>- k. P t) = (\<diamond> t (I \<down>\<ge> k). P (t - k))" and
  iT_Minus_iEx_conv: "(\<diamond> t k \<ominus> I. P t) = (\<diamond> t (I \<down>\<le> k). P (k - t))" and
  iT_Div_iEx_conv: "(\<diamond> t I \<oslash> k. P t) = (\<diamond> t I. P (t div k))"
by (simp_all only: iEx_iAll_conv iT_arith_iAll_conv)


text \<open>Until and Since operators\<close>

lemma iT_Plus_iUntil_conv: "(P t1. t1 \<U> t2 (I \<oplus> k). Q t2) = (P (t1 + k). t1 \<U> t2 I. Q (t2 + k))"
by (simp add: iUntil_def iT_Plus_iAll_conv iT_Plus_iEx_conv iT_Plus_cut_less2)

lemma iT_Mult_iUntil_conv: "(P t1. t1 \<U> t2 (I \<otimes> k). Q t2) = (P (t1 * k). t1 \<U> t2 I. Q (t2 * k))"
apply (case_tac "I = {}")
 apply (simp add: iT_Mult_empty)
apply (case_tac "k = 0")
 apply (force simp add: iT_Mult_0 iTILL_0)
apply (simp add: iUntil_def iT_Mult_iAll_conv iT_Mult_iEx_conv iT_Mult_cut_less2)
done

lemma iT_Plus_neg_iUntil_conv: "(P t1. t1 \<U> t2 (I \<oplus>- k). Q t2) = (P (t1 - k). t1 \<U> t2 (I \<down>\<ge> k). Q (t2 - k))"
apply (simp add: iUntil_def iT_Plus_neg_iAll_conv iT_Plus_neg_iEx_conv iT_Plus_neg_cut_less2)
apply (simp add: i_cut_commute_disj)
done

lemma iT_Minus_iUntil_conv: "(P t1. t1 \<U> t2 (k \<ominus> I). Q t2) = (P (k - t1). t1 \<S> t2 (I \<down>\<le> k). Q (k - t2))"
apply (simp add: iUntil_def iSince_def iT_Minus_iAll_conv iT_Minus_iEx_conv iT_Minus_cut_less2)
apply (simp add: i_cut_commute_disj)
done

lemma iT_Div_iUntil_conv: "(P t1. t1 \<U> t2 (I \<oslash> k). Q t2) = (P (t1 div k). t1 \<U> t2 I. Q (t2 div k))"
apply (case_tac "I = {}")
 apply (simp add: iT_Div_empty)
apply (case_tac "k = 0")
 apply (force simp add: iT_Div_0 iTILL_0)
apply (simp add: iUntil_def iT_Div_iAll_conv iT_Div_iEx_conv iT_Div_cut_less2)
apply (rule iffI)
 apply (clarsimp, rename_tac t)
 apply (subgoal_tac "I \<down>\<ge> (t - t mod k) \<noteq> {}")
  prefer 2
  apply (simp add: cut_ge_not_empty_iff)
  apply (rule_tac x=t in bexI)
  apply simp+
 apply (case_tac "t mod k = 0")
  apply (rule_tac t=t in iexI)
  apply simp+
 apply (rule_tac t="iMin (I \<down>\<ge> (t - t mod k))" in iexI)
  apply (subgoal_tac "
    t - t mod k \<le> iMin (I \<down>\<ge> (t - t mod k)) \<and>
    iMin (I \<down>\<ge> (t - t mod k)) \<le> t")
   prefer 2
   apply (rule conjI)
    apply (blast intro: cut_ge_Min_greater)
   apply (simp add: iMin_le cut_ge_mem_iff)
  apply clarify
  apply (rule_tac t="iMin (I \<down>\<ge> (t - t mod k)) div k" and s="t div k" in subst)
   apply (rule order_antisym)
    apply (drule_tac m="t - t mod k" and k=k in div_le_mono)
    apply (simp add: sub_mod_div_eq_div)
   apply (rule div_le_mono, assumption)
  apply (clarsimp, rename_tac t1)
  apply (subgoal_tac "t1 \<in> I \<down>< (t - t mod k) \<union> I \<down>\<ge> (t - t mod k)")
   prefer 2
   apply (simp add: cut_less_cut_ge_ident)
  apply (subgoal_tac "t1 \<notin> I \<down>\<ge> (t - t mod k)")
   prefer 2
   apply (blast dest: not_less_iMin)
  apply blast
 apply (blast intro: subsetD[OF _ iMinI_ex2])
apply (clarsimp, rename_tac t)
apply (rule_tac t=t in iexI)
 apply simp
 apply (rule_tac B="I \<down>< t" in iAll_subset)
 apply (simp add: cut_less_mono)
apply simp+
done


text \<open>Until and Since operators can be converted into each other through substraction of intervals from constants\<close>

lemma iUntil_iSince_conv: "
  \<lbrakk> finite I; Max I \<le> k \<rbrakk> \<Longrightarrow> 
  (P t1. t1 \<U> t2 I. Q t2) = (P (k - t1). t1 \<S> t2 (k \<ominus> I). Q (k - t2))"
apply (case_tac "I = {}")
 apply (simp add: iT_Minus_empty)
apply (frule le_trans[OF iMin_le_Max], assumption+)
apply (subgoal_tac "Max (k \<ominus> I) \<le> k")
 prefer 2
 apply (simp add: iT_Minus_Max)
apply (subgoal_tac "iMin (k \<ominus> I) \<le> k")
 prefer 2
 apply (rule order_trans[OF iMin_le_Max])
 apply (simp add: iT_Minus_finite iT_Minus_empty_iff del: Max_le_iff)+
apply (rule_tac t="P t1. t1 \<U> t2 I. Q t2" and s="P t1. t1 \<U> t2 (k \<ominus> (k \<ominus> I)). Q t2" in subst)
 apply (simp add: iT_Minus_Minus_eq)
apply (simp add: iT_Minus_iUntil_conv cut_le_Max_all iT_Minus_finite)
done

lemma iSince_iUntil_conv: "
  \<lbrakk> finite I; Max I \<le> k \<rbrakk> \<Longrightarrow> 
  (P t1. t1 \<S> t2 I. Q t2) = (P (k - t1). t1 \<U> t2 (k \<ominus> I). Q (k - t2))"
apply (case_tac "I = {}")
 apply (simp add: iT_Minus_empty)
apply (simp (no_asm_simp) add: iT_Minus_iUntil_conv)
apply (simp (no_asm_simp) add: cut_le_Max_all)
apply (unfold iSince_def)
apply (rule iffI)
 apply (clarsimp, rename_tac t)
 apply (rule_tac t=t in iexI)
  apply (frule_tac x=t in bspec, assumption)
  apply (clarsimp, rename_tac t1)
  apply (drule_tac t=t1 in ispec)
   apply (simp add: cut_greater_mem_iff)
  apply simp+
apply (clarsimp, rename_tac t)
apply (rule_tac t=t in iexI)
 apply (clarsimp, rename_tac t')
 apply (drule_tac t=t' in ispec)
  apply (simp add: cut_greater_mem_iff)
 apply simp+
done


lemma iT_Plus_iSince_conv: "(P t1. t1 \<S> t2 (I \<oplus> k). Q t2) = (P (t1 + k). t1 \<S> t2 I. Q (t2 + k))"
by (simp add: iSince_def iT_Plus_iAll_conv iT_Plus_iEx_conv iT_Plus_cut_greater2)

lemma iT_Mult_iSince_conv: "0 < k \<Longrightarrow> (P t1. t1 \<S> t2 (I \<otimes> k). Q t2) = (P (t1 * k). t1 \<S> t2 I. Q (t2 * k))"
by (simp add: iSince_def iT_Mult_iAll_conv iT_Mult_iEx_conv iT_Mult_cut_greater2)

lemma iT_Plus_neg_iSince_conv: "(P t1. t1 \<S> t2 (I \<oplus>- k). Q t2) = (P (t1 - k). t1 \<S> t2 (I \<down>\<ge> k). Q (t2 - k))"
apply (simp add: iSince_def iT_Plus_neg_iAll_conv iT_Plus_neg_iEx_conv)
apply (rule iffI)
 apply (clarsimp, rename_tac t)
 apply (simp add: iT_Plus_neg_cut_greater2)
 apply (rule_tac t=t in iexI)
  apply (clarsimp, rename_tac t')
  apply (drule_tac t="t' - k" in ispec)
   apply (simp add: iT_Plus_neg_mem_iff2 cut_greater_mem_iff)
  apply simp
 apply blast
apply (clarsimp, rename_tac t)
apply (rule_tac t=t in iexI)
 apply (clarsimp, rename_tac t')
 apply (drule_tac t="t' + k" in ispec)
  apply (simp add: iT_Plus_neg_mem_iff i_cut_mem_iff)
 apply simp
apply blast
done
lemma iT_Minus_iSince_conv: "
  (P t1. t1 \<S> t2 (k \<ominus> I). Q t2) = (P (k - t1). t1 \<U> t2 (I \<down>\<le> k). Q (k - t2))"
apply (case_tac "I = {}")
 apply (simp add: iT_Minus_empty cut_le_empty)
apply (case_tac "I \<down>\<le> k = {}")
 apply (simp add: iT_Minus_image_conv)
apply (subst iT_Minus_cut_eq[OF order_refl, symmetric])
apply (subst iSince_iUntil_conv[where k=k])
  apply (rule iT_Minus_finite)
 apply (subst iT_Minus_Max)
   apply simp
  apply (rule cut_le_bound, rule iMinI_ex2, simp)
 apply simp
apply (simp add: iT_Minus_Minus_cut_eq)
done

lemma iT_Div_iSince_conv: "
  0 < k \<Longrightarrow> (P t1. t1 \<S> t2 (I \<oslash> k). Q t2) = (P (t1 div k). t1 \<S> t2 I. Q (t2 div k))"
apply (case_tac "I = {}")
 apply (simp add: iT_Div_empty)
apply (simp add: iSince_def iT_Div_iAll_conv iT_Div_iEx_conv)
apply (simp add: iT_Div_cut_greater)
apply (subgoal_tac "\<forall>t. t \<le> t div k * k + (k - Suc 0)")
 prefer 2
 apply clarsimp
 apply (simp add: div_mult_cancel add.commute[of _ k])
 apply (simp add: le_add_diff Suc_mod_le_divisor)
apply (rule iffI)
 apply (clarsimp, rename_tac t)
 apply (drule_tac x=t in spec)
 apply (subgoal_tac "I \<down>\<le> (t div k * k + (k - Suc 0)) \<noteq> {}")
  prefer 2
  apply (simp add: cut_le_not_empty_iff)
  apply (rule_tac x=t in bexI, assumption+)
 apply (subgoal_tac "t \<le> Max (I \<down>\<le> (t div k * k + (k - Suc 0)))")
  prefer 2
  apply (simp add: nat_cut_le_finite cut_le_mem_iff)
 apply (subgoal_tac "Max (I \<down>\<le> (t div k * k + (k - Suc 0))) \<le> t div k * k + (k - Suc 0)")
  prefer 2
  apply (simp add: nat_cut_le_finite cut_le_mem_iff)
 apply (subgoal_tac "Max (I \<down>\<le> (t div k * k + (k - Suc 0))) div k = t div k")
  prefer 2
  apply (rule order_antisym)
   apply (rule_tac t="t div k" and s="(t div k * k + (k - Suc 0)) div k" in subst)
    apply (simp only: div_add1_eq1_mod_0_left[OF mod_mult_self2_is_0])
    apply simp
   apply (rule div_le_mono)
   apply (simp only: div_add1_eq1_mod_0_left[OF mod_mult_self2_is_0])
   apply simp
  apply (rule div_le_mono, assumption)
 apply (rule_tac t="Max (I \<down>\<le> (t div k * k + (k - Suc 0)))" in iexI)
  apply (clarsimp, rename_tac t1)
  apply (subgoal_tac "t1 \<in> I")
   prefer 2
   apply assumption
  apply (subgoal_tac "t div k * k + (k - Suc 0) < t1")
   prefer 2
   apply (rule ccontr)
   apply (drule not_greater_Max[OF nat_cut_le_finite])
   apply (simp add: i_cut_mem_iff)
  apply (drule_tac t="t1 div k" in ispec)
   apply (simp add: iT_Div_imp_mem cut_greater_mem_iff)
  apply assumption
 apply (blast intro: subsetD[OF _ Max_in[OF nat_cut_le_finite]])
apply (clarsimp, rename_tac t)
apply (drule_tac x=t in spec)
apply (rule_tac t=t in iexI)
 apply (clarsimp simp: iT_Div_mem_iff, rename_tac t1 t2)
 apply (drule_tac t=t2 in ispec)
  apply (simp add: cut_greater_mem_iff)
 apply simp+
done


text \<open>Weak Until and Weak Since operators\<close>

lemma iT_Plus_iWeakUntil_conv: "(P t1. t1 \<W> t2 (I \<oplus> k). Q t2) = (P (t1 + k). t1 \<W> t2 I. Q (t2 + k))"
by (simp add: iWeakUntil_iUntil_conv iT_Plus_iUntil_conv iT_Plus_iAll_conv)

lemma iT_Mult_iWeakUntil_conv: "(P t1. t1 \<W> t2 (I \<otimes> k). Q t2) = (P (t1 * k). t1 \<W> t2 I. Q (t2 * k))"
by (simp add: iWeakUntil_iUntil_conv iT_Mult_iUntil_conv iT_Mult_iAll_conv)

lemma iT_Plus_neg_iWeakUntil_conv: "(P t1. t1 \<W> t2 (I \<oplus>- k). Q t2) = (P (t1 - k). t1 \<W> t2 (I \<down>\<ge> k). Q (t2 - k))"
by (simp add: iWeakUntil_iUntil_conv iT_Plus_neg_iUntil_conv iT_Plus_neg_iAll_conv)

lemma iT_Minus_iWeakUntil_conv: "(P t1. t1 \<W> t2 (k \<ominus> I). Q t2) = (P (k - t1). t1 \<B> t2 (I \<down>\<le> k). Q (k - t2))"
by (simp add: iWeakUntil_iUntil_conv iWeakSince_iSince_conv iT_Minus_iUntil_conv iT_Minus_iAll_conv)

lemma iT_Div_iWeakUntil_conv: "(P t1. t1 \<W> t2 (I \<oslash> k). Q t2) = (P (t1 div k). t1 \<W> t2 I. Q (t2 div k))"
by (simp add: iWeakUntil_iUntil_conv iT_Div_iUntil_conv iT_Div_iAll_conv)


lemma iT_Plus_iWeakSince_conv: "(P t1. t1 \<B> t2 (I \<oplus> k). Q t2) = (P (t1 + k). t1 \<B> t2 I. Q (t2 + k))"
by (simp add: iWeakSince_iSince_conv iT_Plus_iSince_conv iT_Plus_iAll_conv)

lemma iT_Mult_iWeakSince_conv: "0 < k \<Longrightarrow> (P t1. t1 \<B> t2 (I \<otimes> k). Q t2) = (P (t1 * k). t1 \<B> t2 I. Q (t2 * k))"
by (simp add: iWeakSince_iSince_conv iT_Mult_iSince_conv iT_Mult_iAll_conv)

lemma iT_Plus_neg_iWeakSince_conv: "(P t1. t1 \<B> t2 (I \<oplus>- k). Q t2) = (P (t1 - k). t1 \<B> t2 (I \<down>\<ge> k). Q (t2 - k))"
by (simp add: iWeakSince_iSince_conv iT_Plus_neg_iSince_conv iT_Plus_neg_iAll_conv)

lemma iT_Minus_iWeakSince_conv: "
  (P t1. t1 \<B> t2 (k \<ominus> I). Q t2) = (P (k - t1). t1 \<W> t2 (I \<down>\<le> k). Q (k - t2))"
by (simp add: iWeakSince_iSince_conv iT_Minus_iSince_conv iT_Minus_iAll_conv iWeakUntil_iUntil_conv)

lemma iT_Div_iWeakSince_conv: "
  0 < k \<Longrightarrow> (P t1. t1 \<B> t2 (I \<oslash> k). Q t2) = (P (t1 div k). t1 \<B> t2 I. Q (t2 div k))"
by (simp add: iWeakSince_iSince_conv iT_Div_iSince_conv iT_Div_iAll_conv)


text \<open>Release and Trigger operators\<close>

lemma iT_Plus_iRelease_conv: "(P t1. t1 \<R> t2 (I \<oplus> k). Q t2) = (P (t1 + k). t1 \<R> t2 I. Q (t2 + k))"
by (simp add: iRelease_iWeakUntil_conv iT_Plus_iWeakUntil_conv)

lemma iT_Mult_iRelease_conv: "(P t1. t1 \<R> t2 (I \<otimes> k). Q t2) = (P (t1 * k). t1 \<R> t2 I. Q (t2 * k))"
by (simp add: iRelease_iWeakUntil_conv iT_Mult_iWeakUntil_conv)

lemma iT_Plus_neg_iRelease_conv: "(P t1. t1 \<R> t2 (I \<oplus>- k). Q t2) = (P (t1 - k). t1 \<R> t2 (I \<down>\<ge> k). Q (t2 - k))"
by (simp add: iRelease_iWeakUntil_conv iT_Plus_neg_iWeakUntil_conv)

lemma iT_Minus_iRelease_conv: "(P t1. t1 \<R> t2 (k \<ominus> I). Q t2) = (P (k - t1). t1 \<T> t2 (I \<down>\<le> k). Q (k - t2))"
by (simp add: iRelease_iWeakUntil_conv iT_Minus_iWeakUntil_conv 
  iTrigger_iSince_conv iWeakSince_iSince_conv disj_commute)

lemma iT_Div_iRelease_conv: "(P t1. t1 \<R> t2 (I \<oslash> k). Q t2) = (P (t1 div k). t1 \<R> t2 I. Q (t2 div k))"
by (simp add: iRelease_iWeakUntil_conv iT_Div_iWeakUntil_conv)


lemma iT_Plus_iTrigger_conv: "(P t1. t1 \<T> t2 (I \<oplus> k). Q t2) = (P (t1 + k). t1 \<T> t2 I. Q (t2 + k))"
by (simp add: iTrigger_iWeakSince_conv iT_Plus_iWeakSince_conv)

lemma iT_Mult_iTrigger_conv: "0 < k \<Longrightarrow> (P t1. t1 \<T> t2 (I \<otimes> k). Q t2) = (P (t1 * k). t1 \<T> t2 I. Q (t2 * k))"
by (simp add: iTrigger_iWeakSince_conv iT_Mult_iWeakSince_conv)

lemma iT_Plus_neg_iTrigger_conv: "(P t1. t1 \<T> t2 (I \<oplus>- k). Q t2) = (P (t1 - k). t1 \<T> t2 (I \<down>\<ge> k). Q (t2 - k))"
by (simp add: iTrigger_iWeakSince_conv iT_Plus_neg_iWeakSince_conv)

lemma iT_Minus_iTrigger_conv: "
  (P t1. t1 \<T> t2 (k \<ominus> I). Q t2) = (P (k - t1). t1 \<R> t2 (I \<down>\<le> k). Q (k - t2))"
by (fastforce simp add: iTrigger_iWeakSince_conv iT_Minus_iWeakSince_conv iRelease_iUntil_conv iWeakUntil_iUntil_conv)

lemma iT_Div_iTrigger_conv: "
  0 < k \<Longrightarrow> (P t1. t1 \<T> t2 (I \<oslash> k). Q t2) = (P (t1 div k). t1 \<T> t2 I. Q (t2 div k))"
by (simp add: iTrigger_iWeakSince_conv iT_Div_iWeakSince_conv)

end
