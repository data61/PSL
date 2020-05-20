(* Author:     Brandon Bohrer *)
theory Interval_Word32
imports
  Complex_Main
  Word_Lib.Word_Lemmas
  Word_Lib.Word_Lib
  Word_Lib.Word_Syntax
begin

text\<open>Interval-Word32.thy implements conservative interval arithmetic operators on 32-bit word 
   values, with explicit infinities for values outside the representable bounds. It is suitable 
   for use in interpreters for languages which  must have a well-understood low-level behavior
   (see Interpreter.thy). This work was originally part of the paper by Bohrer \emph{et al.}~\cite{BohrerTMMP18}.

   It is worth noting that this is not the first formalization of interval arithmetic in 
   Isabelle/HOL. This article is presented regardless because it has unique goals in mind
   which have led to unique design decisions. Our goal is generate code which can be used to 
   perform conservative arithmetic in implementations extracted from a proof.

   The Isabelle standard library now features interval arithmetic, for example in Approximation.thy.
   Ours differs in two ways:
   1) We use intervals with explicit positive and negative infinities, and with overflow checking.
      Such checking is often relevant in implementation-level code with unknown inputs.
      To promote memory-efficient implementations, we moreover use sentinel values for infinities,
      rather than datatype constructors. This is especially important in real-time settings where
      the garbarge collection required for datatypes can be a concern.
   2) Our goal is not to use interval arithmetic to discharge Isabelle goals, but to generate useful
      proven-correct implementation code, see Interpreter.thy. On the other hand,  we are not 
      concerned with producing interval-based automation for arithmetic goals in HOL.

   In practice, much of the work in this theory comes down to sheer case-analysis.
   Bounds-checking requires many edge cases in arithmetic functions, which come with many cases in
   proofs. Where possible, we attempt to offload interesting facts about word representations of 
   numbers into reusable lemmas, but even then main results require many subcases, each with 
   a certain amount of arithmetic grunt work.
\<close>

section \<open>Interval arithmetic definitions\<close>
subsection \<open>Syntax\<close>
text\<open>Words are 32-bit\<close>
type_synonym word = "32 Word.word"

text\<open>Sentinel values for infinities. Note that we leave the maximum value ($2^31$) 
  completed unused, so that negation of $(2^{31})-1$ is not an edge case\<close>
definition NEG_INF::"word"
where NEG_INF_def[simp]:"NEG_INF = -((2 ^ 31) -1)"

definition NegInf::"real"
where NegInf[simp]:"NegInf = real_of_int (sint NEG_INF)"

definition POS_INF::"word"
where POS_INF_def[simp]:"POS_INF = (2^31) - 1"

definition PosInf::"real"
where PosInf[simp]:"PosInf = real_of_int (sint POS_INF)"

text\<open>Subtype of words who represent a finite value. \<close>
typedef bword = "{n::word. sint n \<ge> sint NEG_INF \<and> sint n \<le> sint POS_INF}"
  apply(rule exI[where x=NEG_INF])
  by (auto)

text\<open>Numeric literals\<close>
type_synonym lit = bword
      
setup_lifting type_definition_bword

lift_definition bword_zero::"bword" is "0::32 Word.word"
  by auto

lift_definition bword_one::"bword" is "1::32 Word.word"
  by(auto simp add: sint_uint)

lift_definition bword_neg_one::"bword" is "-1::32 Word.word"
  by(auto)


definition word::"word \<Rightarrow> bool"
where word_def[simp]:"word w \<equiv> w \<in> {NEG_INF..POS_INF}"


named_theorems rep_simps "Simplifications for representation functions"

text\<open>Definitions of interval containment and word representation
repe w r iff word w encodes real number r\<close>
inductive repe ::"word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>E" 10)
where 
  repPOS_INF:"r \<ge> real_of_int (sint POS_INF) \<Longrightarrow> repe POS_INF r" 
| repNEG_INF:"r \<le> real_of_int (sint NEG_INF) \<Longrightarrow> repe NEG_INF r"
| repINT:"(sint w) < real_of_int(sint POS_INF) \<Longrightarrow> (sint w) > real_of_int(sint NEG_INF) 
    \<Longrightarrow> repe w (sint w)"

inductive_simps 
    repePos_simps[rep_simps]:"repe POS_INF r"
and repeNeg_simps[rep_simps]:"repe NEG_INF r"
and repeInt_simps[rep_simps]:"repe w (sint w)"

text\<open>repU w r if w represents an upper bound of r\<close>
definition repU ::"word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>U" 10)
where "repU w r \<equiv> \<exists> r'. r' \<ge> r \<and> repe w r'"

lemma repU_leq:"repU w r \<Longrightarrow> r' \<le> r \<Longrightarrow> repU w r'"
  unfolding repU_def
  using order_trans by auto

text\<open>repU w r if w represents a lower bound of r\<close>
definition repL ::"word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>L" 10)
where "repL w r \<equiv> \<exists> r'. r' \<le> r \<and> repe w r'"

lemma repL_geq:"repL w r \<Longrightarrow> r' \<ge> r \<Longrightarrow> repL w r'"
  unfolding repL_def
  using order_trans by auto

text\<open>repP (l,u) r  iff l and u encode lower and upper bounds of r\<close>
definition repP ::"word * word \<Rightarrow> real \<Rightarrow> bool" (infix "\<equiv>\<^sub>P" 10)
where "repP w r \<equiv> let (w1, w2) = w in repL w1 r \<and> repU w2 r" 


lemma int_not_posinf:
  assumes b1:"real_of_int (sint ra) <  real_of_int (sint POS_INF)"
  assumes b2:"real_of_int (sint NEG_INF) <  real_of_int (sint ra)"
  shows "ra \<noteq> POS_INF"
  using b1 b2 by auto
        
lemma int_not_neginf:
  assumes b1:" real_of_int (sint ra) <  real_of_int (sint POS_INF)"
  assumes b2:" real_of_int (sint NEG_INF) <  real_of_int (sint ra)"
  shows "ra \<noteq> NEG_INF"
  using b1 b2 by auto

lemma int_not_undef:
  assumes b1:"real_of_int (sint ra) <  real_of_int (sint POS_INF)"
  assumes b2:"real_of_int (sint NEG_INF) < real_of_int (sint ra)"
  shows "ra \<noteq> NEG_INF-1"
  using b1 b2  by auto

lemma sint_range:
  assumes b1:"real_of_int (sint ra) < real_of_int (sint POS_INF)"
  assumes b2:"real_of_int (sint NEG_INF) < real_of_int (sint ra)"
  shows "sint ra  \<in> {i. i > -((2^31)-1)  \<and> i < (2^31)-1}"
  using b1 b2 by auto

lemma word_size_neg:
  fixes w :: "32 Word.word"
  shows "size (-w) = size w"
  using Word.word_size[of w] Word.word_size[of "-w"] by auto

lemma uint_distinct:
  fixes w1 w2
  shows "w1 \<noteq> w2 \<Longrightarrow> uint w1 \<noteq> uint w2"
  by auto

section \<open>Preliminary lemmas\<close>
subsection \<open>Case analysis lemmas\<close>
text\<open>Case analysis principle for pairs of intervals, used in proofs of arithmetic operations\<close>
lemma ivl_zero_case:
  fixes l1 u1 l2 u2 :: real
  assumes ivl1:"l1 \<le> u1"
  assumes ivl2:"l2 \<le> u2"
  shows 
"(l1 \<le> 0 \<and> 0 \<le> u1 \<and> l2 \<le> 0 \<and> 0 \<le> u2)
\<or>(l1 \<le> 0 \<and> 0 \<le> u1 \<and> 0 \<le> l2)
\<or>(l1 \<le> 0 \<and> 0 \<le> u1 \<and> u2 \<le> 0)
\<or>(0 \<le> l1 \<and> l2 \<le> 0 \<and> 0 \<le> u2)
\<or>(u1 \<le> 0 \<and> l2 \<le> 0 \<and> 0 \<le> u2)
\<or>(u1 \<le> 0 \<and> u2 \<le> 0)
\<or>(u1 \<le> 0 \<and> 0 \<le> l2)
\<or>(0 \<le> l1 \<and> u2 \<le> 0)
\<or>(0 \<le> l1 \<and> 0 \<le> l2)"
using ivl1 ivl2 
by (metis le_cases)

lemma case_ivl_zero
[consumes 2, case_names ZeroZero ZeroPos ZeroNeg PosZero NegZero NegNeg NegPos PosNeg PosPos]:
  fixes l1 u1 l2 u2 :: real
  shows
  "l1 \<le> u1 \<Longrightarrow>
   l2 \<le> u2 \<Longrightarrow> 
((l1 \<le> 0 \<and> 0 \<le> u1 \<and> l2 \<le> 0 \<and> 0 \<le> u2) \<Longrightarrow> P) \<Longrightarrow>
((l1 \<le> 0 \<and> 0 \<le> u1 \<and> 0 \<le> l2) \<Longrightarrow> P) \<Longrightarrow>
((l1 \<le> 0 \<and> 0 \<le> u1 \<and> u2 \<le> 0) \<Longrightarrow> P) \<Longrightarrow>
 ((0 \<le> l1 \<and> l2 \<le> 0 \<and> 0 \<le> u2) \<Longrightarrow> P) \<Longrightarrow>
((u1 \<le> 0 \<and> l2 \<le> 0 \<and> 0 \<le> u2) \<Longrightarrow> P) \<Longrightarrow>
((u1 \<le> 0 \<and> u2 \<le> 0) \<Longrightarrow> P) \<Longrightarrow>
((u1 \<le> 0 \<and> 0 \<le> l2) \<Longrightarrow> P) \<Longrightarrow>
((0 \<le> l1 \<and> u2 \<le> 0) \<Longrightarrow> P) \<Longrightarrow>
((0 \<le> l1 \<and> 0 \<le> l2) \<Longrightarrow> P) \<Longrightarrow> P"
  using ivl_zero_case[of l1 u1 l2 u2]
  by auto

lemma case_inf2[case_names PosPos PosNeg PosNum NegPos NegNeg NegNum NumPos NumNeg NumNum]:
  shows 
  "\<And>w1 w2 P.
      (w1 = POS_INF \<Longrightarrow> w2 = POS_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = POS_INF \<Longrightarrow> w2 = NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = POS_INF \<Longrightarrow> w2 \<noteq> POS_INF \<Longrightarrow> w2 \<noteq> NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = NEG_INF \<Longrightarrow> w2 = POS_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = NEG_INF \<Longrightarrow> w2 = NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = NEG_INF \<Longrightarrow> w2 \<noteq> POS_INF \<Longrightarrow> w2 \<noteq> NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 \<noteq> POS_INF \<Longrightarrow> w1 \<noteq> NEG_INF \<Longrightarrow> w2 = POS_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 \<noteq> POS_INF \<Longrightarrow> w1 \<noteq> NEG_INF \<Longrightarrow> w2 = NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 \<noteq> POS_INF \<Longrightarrow> w1 \<noteq> NEG_INF \<Longrightarrow> w2 \<noteq> POS_INF \<Longrightarrow> w2 \<noteq> NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> P w1 w2"
  by(auto)

lemma case_pu_inf[case_names PosAny AnyPos NegNeg NegNum NumNeg NumNum]:
  shows 
  "\<And>w1 w2 P.
      (w1 = POS_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w2 = POS_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = NEG_INF \<Longrightarrow> w2 = NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = NEG_INF \<Longrightarrow> w2 \<noteq> POS_INF \<Longrightarrow> w2 \<noteq> NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 \<noteq> POS_INF \<Longrightarrow> w1 \<noteq> NEG_INF \<Longrightarrow> w2 = NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 \<noteq> POS_INF \<Longrightarrow> w1 \<noteq> NEG_INF \<Longrightarrow> w2 \<noteq> POS_INF \<Longrightarrow> w2 \<noteq> NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> P w1 w2"
  by(auto)

lemma case_pl_inf[case_names NegAny AnyNeg PosPos PosNum NumPos NumNum]:
  shows 
  "\<And>w1 w2 P.
      (w1 = NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w2 = NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = POS_INF \<Longrightarrow> w2 = POS_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 = POS_INF \<Longrightarrow> w2 \<noteq> POS_INF \<Longrightarrow> w2 \<noteq> NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 \<noteq> POS_INF \<Longrightarrow> w1 \<noteq> NEG_INF \<Longrightarrow> w2 = POS_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> (w1 \<noteq> POS_INF \<Longrightarrow> w1 \<noteq> NEG_INF \<Longrightarrow> w2 \<noteq> POS_INF \<Longrightarrow> w2 \<noteq> NEG_INF \<Longrightarrow> P w1 w2)
  \<Longrightarrow> P w1 w2"
  by(auto)

lemma word_trichotomy[case_names Less Equal Greater]:
  fixes w1 w2 :: word
  shows 
  "(w1 <s w2 \<Longrightarrow> P w1 w2) \<Longrightarrow>
   (w1 = w2  \<Longrightarrow> P w1 w2) \<Longrightarrow>
   (w2 <s w1 \<Longrightarrow> P w1 w2) \<Longrightarrow> P w1 w2"
  using signed.linorder_cases by auto

lemma case_times_inf
 [case_names 
  PosPos NegPos PosNeg NegNeg 
  PosLo PosHi PosZero NegLo NegHi NegZero
  LoPos HiPos ZeroPos LoNeg HiNeg ZeroNeg
  AllFinite]:
  fixes w1 w2 P
  assumes pp:"(w1 = POS_INF \<and> w2 = POS_INF \<Longrightarrow> P w1 w2)"
  and np:"(w1 = NEG_INF \<and> w2 = POS_INF \<Longrightarrow> P w1 w2)"
  and pn:"(w1 = POS_INF \<and> w2 = NEG_INF \<Longrightarrow> P w1 w2)"
  and nn:"(w1 = NEG_INF \<and> w2 = NEG_INF \<Longrightarrow> P w1 w2)"
  and pl:"(w1 = POS_INF \<and> w2 \<noteq> NEG_INF \<and> w2 <s 0 \<Longrightarrow> P w1 w2)"
  and ph:"(w1 = POS_INF \<and> w2 \<noteq> POS_INF \<and> 0 <s w2   \<Longrightarrow> P w1 w2)"
  and pz:"(w1 = POS_INF \<and> w2 = 0 \<Longrightarrow> P w1 w2)"
  and nl:"(w1 = NEG_INF \<and> w2 \<noteq> NEG_INF \<and> w2 <s 0 \<Longrightarrow> P w1 w2)"
  and nh:"(w1 = NEG_INF \<and> w2 \<noteq> POS_INF \<and> 0 <s w2 \<Longrightarrow> P w1 w2)"
  and nz:"(w1 = NEG_INF \<and> 0 = w2 \<Longrightarrow> P w1 w2)"
  and lp:"(w1 \<noteq> NEG_INF \<and> w1 <s 0 \<and> w2 = POS_INF \<Longrightarrow> P w1 w2)"
  and hp:"(w1 \<noteq> POS_INF \<and> 0 <s w1 \<and> w2 = POS_INF \<Longrightarrow> P w1 w2)"
  and zp:"(0 = w1 \<and> w2 = POS_INF \<Longrightarrow> P w1 w2)"
  and ln:"(w1 \<noteq> NEG_INF \<and> w1 <s 0 \<and> w2 = NEG_INF \<Longrightarrow> P w1 w2)"
  and hn:"(w1 \<noteq> POS_INF \<and> 0 <s w1 \<and> w2 = NEG_INF \<Longrightarrow> P w1 w2)"
  and zn:"(0 = w1 \<and> w2 = NEG_INF \<Longrightarrow> P w1 w2)"
  and allFinite:"w1 \<noteq> NEG_INF \<and> w1 \<noteq> POS_INF \<and> w2 \<noteq> NEG_INF \<and> w2 \<noteq> POS_INF \<Longrightarrow> P w1 w2"
  shows " P w1 w2"
  proof (cases rule: word_trichotomy[of w1 0])
    case Less then have w1l:"w1 <s 0" by auto
    then show ?thesis
    proof (cases rule: word_trichotomy[of w2 0])
      case Less
      then show ?thesis 
        using nn nl ln nz zn allFinite w1l lp pl by blast
    next
      case Equal 
      then show ?thesis
        using nn nl ln nz zn  w1l allFinite lp pz
        by (auto)
    next
      case Greater
      then show ?thesis
        using  nh np zp lp w1l allFinite ln ph
        by (auto)
    qed
  next
    case Equal then have w1z:"w1 = 0" by auto
    then show ?thesis
    proof (cases rule: word_trichotomy[of w2 0])
      case Less
      then show ?thesis
        using zn allFinite w1z nl pl zp by auto
    next
      case Equal
      then show ?thesis
        using w1z allFinite
        by (auto)
    next
      case Greater
      then show ?thesis
        using allFinite zp w1z nh ph zn by auto
    qed
  next
    case Greater then have w1h:"0 <s w1" by auto
    then show ?thesis
    proof (cases rule: word_trichotomy[of w2 0])
      case Less
      then show ?thesis
        using pn pl hn  w1h allFinite hp nl by blast
    next
      case Equal
      then show ?thesis
        using pz pz allFinite w1h hn hp nz by blast
    next
      case Greater
      then show ?thesis
        using pp ph hp w1h allFinite hn nh by blast
    qed
  qed


subsection \<open>Trivial arithmetic lemmas\<close>

lemma max_diff_pos:"0 \<le> 9223372034707292161 + ((-(2 ^ 31))::real)" by auto

lemma max_less:"2 ^ 31 < (9223372039002259455::int)" by auto

lemma sints64:"sints 64 = {i. - (2 ^ 63) \<le> i \<and> i < 2 ^ 63}"
  using sints_def[of 64] range_sbintrunc[of 63] by auto 

lemma sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
  using sints_def[of 32] range_sbintrunc[of 31] by auto 

lemma upcast_max:"sint((scast(0x80000001::word))::64 Word.word)=sint((0x80000001::32 Word.word))"
  by auto

lemma upcast_min:"(0xFFFFFFFF80000001::64 Word.word) = ((scast (-0x7FFFFFFF::word))::64 Word.word)"
  by auto

lemma min_extend_neg:"sint ((0xFFFFFFFF80000001)::64 Word.word) < 0"
  by auto

lemma min_extend_val':"sint ((-0x7FFFFFFF)::64 Word.word) = (-0x7FFFFFFF)" by auto

lemma min_extend_val:"(-0x7FFFFFFF::64 Word.word) = 0xFFFFFFFF80000001" by auto

lemma range2s:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
  by auto


section \<open>Arithmetic operations\<close>
text\<open>This section defines operations which conservatively compute upper and lower bounds of 
 arithmetic functions given upper and lower bounds on their arguments. Each function comes with a 
 proof that it rounds in the advertised direction.
\<close>
subsection \<open>Addition upper bound\<close>
text\<open>Upper bound of w1 + w2\<close>
fun pu :: "word \<Rightarrow> word \<Rightarrow> word"
where "pu w1 w2 = 
(if w1 = POS_INF then POS_INF
 else if w2 = POS_INF then POS_INF
 else if w1 = NEG_INF then 
  (if w2 = NEG_INF then NEG_INF 
   else
     (let sum::64 Word.word = ((scast w2)::64 Word.word) + ((scast NEG_INF)::64 Word.word) in
     if (sum::64 Word.word) <=s ((scast NEG_INF)::64 Word.word) then NEG_INF
     else scast sum))
 else if w2 = NEG_INF then 
  (let sum::64 Word.word = ((scast w1)::64 Word.word) + ((scast NEG_INF)::64 Word.word) in
   if (sum::64 Word.word) <=s ((scast NEG_INF)::64 Word.word) then NEG_INF
   else scast sum)
 else 
  (let sum::64 Word.word = ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word) in
   if ((scast POS_INF)::64 Word.word) <=s (sum::64 Word.word) then POS_INF
   else if (sum::64 Word.word) <=s ((scast NEG_INF)::64 Word.word) then NEG_INF
   else scast sum))"

lemma scast_down_range:
fixes w::"'a::len Word.word"
assumes "sint w \<in> sints (len_of (TYPE('b::len)))"
shows "sint w = sint ((scast w)::'b Word.word)"
unfolding scast_def
by (simp add: assms word_sint.Abs_inverse)

lemma pu_lemma:
  fixes w1 w2
  fixes r1 r2 :: real
  assumes up1:"w1 \<equiv>\<^sub>U (r1::real)"
  assumes up2:"w2 \<equiv>\<^sub>U (r2::real)"
  shows   "pu w1 w2 \<equiv>\<^sub>U (r1 + r2)"
proof -
  have scast_eq1:"sint((scast w1)::64 Word.word) = sint w1" 
    apply(rule Word.sint_up_scast)
    unfolding Word.is_up by auto
  have scast_eq2:"sint((scast (0x80000001::word))::64 Word.word) 
  = sint ((0x80000001::32 Word.word))"
     by auto
  have scast_eq3:"sint((scast w2)::64 Word.word) = sint w2"
    apply(rule Word.sint_up_scast)
    unfolding Word.is_up by auto
  have w2Geq:"sint ((scast w2)::64 Word.word) \<ge> - (2 ^ 31) " 
    using Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 Word.word_size 
      scast_eq1 upcast_max scast_eq3 len32 mem_Collect_eq 
    by auto
  have "sint ((scast w2)::64 Word.word) \<le> 2 ^ 31"
    apply (auto simp add: Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 
        scast_eq3 len32)
    using Word.word_sint.Rep[of "(w2)::32 Word.word"] len32[of "TYPE(32)"] sints32 by auto
  then have w2Less:"sint ((scast w2)::64 Word.word) < 9223372039002259455" by auto
  have w2Range:
    "-(2 ^ (size ((scast w2)::64 Word.word) - 1)) 
     \<le> sint ((scast w2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) 
   \<and> sint ((scast w2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) 
     \<le> 2 ^ (size ((scast w2)::64 Word.word) - 1) - 1"
    apply(auto simp add: Word.word_size scast_eq1 upcast_max sints64 max_less)
    using max_diff_pos max_less w2Less w2Geq by auto
  have w2case1a:"sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) 
            =  sint ((scast w2)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
    by(rule signed_arith_sint(1)[OF w2Range])
  have w1Lower:"sint ((scast w1)::64 Word.word) \<ge> - (2 ^ 31) " 
    using Word.word_sint.Rep[of "(w1)::32 Word.word"] sints32 Word.word_size scast_eq1 scast_eq2 
      scast_eq3 len32 mem_Collect_eq 
    by auto
  have w1Leq:"sint ((scast w1)::64 Word.word) \<le> 2 ^ 31"
    apply (auto simp add: Word.word_sint.Rep[of "(w1)::32 Word.word"] sints32 scast_eq1 len32)
    using Word.word_sint.Rep[of "(w1)::32 Word.word"] len32[of "TYPE(32)"] sints32 by auto
  then have w1Less:"sint ((scast w1)::64 Word.word) < 9223372039002259455"
    using max_less by auto
  have w1MinusBound:" - (2 ^ (size ((scast w1)::64 Word.word) - 1)) 
    \<le> sint ((scast w1)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) 
  \<and> sint ((scast w1)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) 
    \<le> 2 ^ (size ((scast w1)::64 Word.word) - 1) - 1"
    apply(auto simp add:
    Word.word_size[of "(scast w1)::64 Word.word"] 
    Word.word_size[of "(scast (-0x7FFFFFFF))::64 Word.word"]
    scast_eq3 scast_eq2 
    Word.word_sint.Rep[of "(w1)::32 Word.word"]
    Word.word_sint.Rep[of "0x80000001::32 Word.word"]
    Word.word_sint.Rep[of "(scast w1)::64 Word.word"]
    Word.word_sint.Rep[of "-0x7FFFFFFF::64 Word.word"]
    sints64 sints32)
    using w1Lower w1Less by auto
  have w1case1a:"sint (((scast w1)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) 
             = sint ((scast w1)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
    by (rule signed_arith_sint(1)[of "(scast w1)::64 Word.word" "(- 0x7FFFFFFF)", OF w1MinusBound])
  have w1case1a':"sint (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001) 
        = sint ((scast w1)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word)"
    using min_extend_val w1case1a by auto
  have w1Leq':"sint w1 \<le> 2^31 - 1"
    using Word.word_sint.Rep[of "(w1)::32 Word.word"] 
    by (auto simp add:  sints32 len32[of "TYPE(32)"])
  have neg64:"(((scast w2)::64 Word.word) + 0xFFFFFFFF80000001) 
            = ((scast w2)::64 Word.word) + (-0x7FFFFFFF)" by auto
  have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
    by auto
  obtain r'\<^sub>1 and r'\<^sub>2 where   
            geq1:"r'\<^sub>1\<ge>r1" and equiv1:"w1 \<equiv>\<^sub>E r'\<^sub>1"
        and geq2:"r'\<^sub>2\<ge>r2" and equiv2:"w2 \<equiv>\<^sub>E r'\<^sub>2"
          using up1 up2 unfolding repU_def by auto
  show ?thesis
proof (cases rule: case_pu_inf[where ?w1.0=w1, where ?w2.0=w2])
  case PosAny then show ?thesis
    apply (auto simp add: repU_def repe.simps)
    using linear by blast 
next
  case AnyPos
  then show ?thesis
  apply (auto simp add: repU_def repe.simps)
  using linear by blast
next
  case NegNeg
  then show ?thesis 
  using up1 up2 
  by (auto simp add: repU_def repe.simps)
next
  case NegNum
  assume neq1:"w2 \<noteq> POS_INF"
  assume eq2:"w1 = NEG_INF"
  assume neq3:"w2 \<noteq> NEG_INF"
  let ?sum = "(scast w2 + scast NEG_INF)::64 Word.word"
  have leq1:"r'\<^sub>1 \<le>  (real_of_int (sint NEG_INF))" 
    using equiv1 neq1 eq2 neq3 by (auto simp add: repe.simps)
  have leq2:"r'\<^sub>2 =  (real_of_int (sint w2))"
    using equiv2 neq1 eq2 neq3 by (auto simp add: repe.simps)
  have case1:"?sum <=s ((scast NEG_INF)::64 Word.word) \<Longrightarrow> NEG_INF \<equiv>\<^sub>U r1 + r2"
    using up1 up2 apply (simp add: repU_def repe.simps word_sle_def)
    apply(rule exI[where x= "r1 + r2"])
    apply(auto)
        using w2case1a min_extend_neg
        apply (auto simp add: neq1 eq2 neq3 repINT repU_def repe.simps repeInt_simps
        up2 word_sless_alt) 
    using repINT repU_def repe.simps repeInt_simps up2 word_sless_alt 
      add.right_neutral add_mono dual_order.trans of_int_le_0_iff scast_eq3 by fastforce+
  have case2:"\<not>(?sum <=s scast NEG_INF) \<Longrightarrow> scast ?sum \<equiv>\<^sub>U r1 + r2"
    apply(simp add: repU_def repe.simps word_sle_def up1 up2)
    apply(rule exI[where x= "r'\<^sub>2 - 0x7FFFFFFF"])
    apply(rule conjI)
    subgoal 
      proof -
        assume " \<not> sint (scast w2 + 0xFFFFFFFF80000001) \<le> - 2147483647"
        have bound1:"r1 \<le> - 2147483647"
          using leq1 geq1 by (auto)
        have bound2:"r2 \<le> r'\<^sub>2"
          using leq2 geq2 by auto        
        show "r1 + r2 \<le> r'\<^sub>2 - 2147483647"
          using bound1 bound2
          by(linarith)
      qed
    apply(rule disjI2)
    apply(rule disjI2)
    apply(auto)
    subgoal
      proof -
        assume a:"\<not> sint (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
        then have sintw2_bound:"sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
          unfolding min_extend_val by auto 
        have case1a:" sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) 
                 =  sint ((scast w2)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
          by(rule signed_arith_sint(1)[OF w2Range])
        have "- 0x7FFFFFFF < sint w2 + (- 0x7FFFFFFF)"
          using sintw2_bound case1a min_extend_val' scast_eq3 by linarith
        then have w2bound:"0 < sint w2" 
          using less_add_same_cancel2 by blast
        have rightSize:"sint (((scast w2)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          using case1a scast_eq3 min_extend_val' Word.word_sint.Rep[of "(w2)::32 Word.word"] w2bound
          by (auto simp add: sints32 len32[of "TYPE(32)"])
        have downcast:"sint ((scast (((scast w2)::64 Word.word) + ((- 0x7FFFFFFF))))::word) 
                   = sint (((scast w2)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word)) "
          using scast_down_range[OF rightSize]
          by auto
        then have b:"sint ((scast (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001))::word)
                 = sint (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001)" 
          using min_extend_val by auto
        have c:"sint (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001) 
            = sint ((scast w2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word)"
          using min_extend_val case1a by auto
        show "r'\<^sub>2 - 2147483647 
        = (real_of_int (sint ((scast (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001))::word)))"
          using a b min_extend_val' scast_eq3 leq2 case1a
          by auto
      qed
    subgoal  
    proof -
      have range2a:" - (2 ^ (size ((scast w2)::64 Word.word) - 1)) 
        \<le> sint ((scast w2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) 
      \<and> sint ((scast w2)::64 Word.word) + sint ((-0x7FFFFFFF)::64 Word.word) 
        \<le> 2 ^ (size ((scast w2)::64 Word.word) - 1) - 1"
        apply(auto simp add: Word.word_size scast_eq1 upcast_max sints64 sints32 max_less)
        using max_diff_pos max_less w2Geq w2Less by auto
      have case2a:"sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) 
                =  sint ((scast w2)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
        by(rule signed_arith_sint(1)[OF range2a])
      have neg64:"(((scast w2)::64 Word.word) + 0xFFFFFFFF80000001) 
                = ((scast w2)::64 Word.word) + (-0x7FFFFFFF)" by auto
      assume "\<not> sint (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
      then have sintw2_bound:"sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
        unfolding neg64 by auto 
      have a:"sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF)) 
            = sint((scast w2)::64 Word.word) + sint((-0x7FFFFFFF)::64 Word.word)" 
        using case2a by auto
      have b:"sint ((scast w2)::64 Word.word) = sint w2" 
        apply(rule Word.sint_up_scast)
        unfolding Word.is_up by auto
      have d:"sint w2 \<le> 2^31 - 1"
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] 
        by (auto simp add:  sints32 len32[of "TYPE(32)"])
      have "- 0x7FFFFFFF < sint w2 + (- 0x7FFFFFFF)"
        using sintw2_bound case2a min_extend_val' scast_eq3 by linarith
      then have w2bound:"0 < sint w2" 
        using less_add_same_cancel2 by blast
      have rightSize:"sint (((scast w2)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
        unfolding case2a b min_extend_val'
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] w2bound
        by (auto simp add: sints32 len32[of "TYPE(32)"])
      have downcast:"sint ((scast (((scast w2)::64 Word.word) + ((- 0x7FFFFFFF))))::word) 
                  = sint (((scast w2)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word))"
        using scast_down_range[OF rightSize]
        by auto
      have "sint (scast (((scast w2)::64 Word.word) + (-0x7FFFFFFF))::word) < 2147483647"
        unfolding downcast a b min_extend_val'
        using range2s[of "sint w2", OF d]
        by auto
      then show "sint (scast (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001)::word) < 2147483647"
        by auto
    qed
    subgoal proof -
      assume notLeq:"\<not> sint (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
      then have gr:"sint (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001) > - 2147483647" 
        by auto
      have case2a:"sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) 
                 = sint ((scast w2)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
        by(rule signed_arith_sint(1)[OF w2Range])
      from neg64
      have sintw2_bound:"sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
        unfolding neg64 using notLeq by auto 
      have a:"sint (((scast w2)::64 Word.word) + (-0x7FFFFFFF)) 
            = sint((scast w2)::64 Word.word) + sint((-0x7FFFFFFF)::64 Word.word)" 
        using case2a by auto
      have c:"sint((-0x7FFFFFFF)::64 Word.word) = -0x7FFFFFFF" 
        by auto
      have d:"sint w2 \<le> 2^31 - 1"
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] 
        by (auto simp add:  sints32 len32[of "TYPE(32)"])
      have "- 0x7FFFFFFF < sint w2 + (- 0x7FFFFFFF)"
        using sintw2_bound case2a c scast_eq3 by linarith
      then have w2bound:"0 < sint w2" 
        using less_add_same_cancel2 by blast
      have rightSize:"sint (((scast w2)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
        unfolding case2a scast_eq3
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] w2bound
        by (auto simp add: sints32 len32[of "TYPE(32)"])
      have downcast:"sint ((scast (((scast w2)::64 Word.word) + ((- 0x7FFFFFFF))))::word) 
                   = sint (((scast w2)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word))"
        using scast_down_range[OF rightSize]
        by auto
      have sintEq:" sint ((scast (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001))::word) 
          = sint (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001) "
          using downcast by auto
      show "-2147483647 
          < real_of_int (sint ((scast (((scast w2)::64 Word.word) + 0xFFFFFFFF80000001))::word))"
        unfolding sintEq  
        using gr of_int_less_iff of_int_minus of_int_numeral by linarith
      qed
    done
  have castEquiv:"\<not>(?sum <=s scast NEG_INF) \<Longrightarrow> (scast ?sum) \<equiv>\<^sub>U r1 + r2"
    using up1 up2 case1 case2  by fastforce
  have letRep:"(let sum = ?sum in if sum <=s scast NEG_INF then NEG_INF else scast sum) \<equiv>\<^sub>U r1 + r2"
    using case1 case2
    by(cases "?sum <=s scast NEG_INF"; auto) 
  show "pu w1 w2 \<equiv>\<^sub>U r1 + r2"
    using letRep eq2 neq1 
    by(auto)
next
  case NumNeg
  assume neq3:"w1 \<noteq> NEG_INF"
  assume neq1:"w1 \<noteq> POS_INF"
  assume eq2:"w2 = NEG_INF"
  let ?sum = "(scast w1 + scast NEG_INF)::64 Word.word"
  have case1:"?sum <=s ((scast NEG_INF)::64 Word.word) \<Longrightarrow> NEG_INF \<equiv>\<^sub>U r1 + r2"
    using up1 up2 apply (simp add: repU_def repe.simps word_sle_def)
    apply(rule exI[where x= "r1 + r2"])
    apply(auto)
        using w1case1a min_extend_neg 
        apply (auto simp add: neq1 eq2 neq3 repINT repU_def repe.simps repeInt_simps 
        up2 word_sless_alt) 
    using repINT repU_def repe.simps repeInt_simps up2 word_sless_alt
    proof -
      fix r'
      assume a1:"sint ((scast w1)::64 Word.word) \<le> 0"
      then have h3:"sint w1 \<le> 0" using scast_eq1 by auto 
      assume a2:"r2 \<le> r'"
      assume a3:"r1 \<le>  (real_of_int (sint w1))"
      assume a4:"r' \<le>  (- 2147483647)"
      from a2 a4 have h1:"r2 \<le> - 2147483647" by auto
      from a1 a3 h3 have h2:"r1 \<le> 0" 
      using dual_order.trans of_int_le_0_iff by blast
      show "r1 + r2 \<le>  (- 2147483647)"
        using h1 h2 add.right_neutral add_mono by fastforce
    qed
  have leq1:"r'\<^sub>2 \<le>  (real_of_int (sint NEG_INF))" and leq2:"r'\<^sub>1 =  (real_of_int (sint w1))" 
    using equiv1 equiv2 neq1 eq2 neq3 unfolding repe.simps by auto
  have case1a:"sint (((scast w1)::64 Word.word) + (-0x7FFFFFFF::64 Word.word)) 
             = sint ((scast w1)::64 Word.word) + sint (-0x7FFFFFFF::64 Word.word)"
    by(rule signed_arith_sint(1)[OF w1MinusBound])
  have case2:"\<not>(?sum <=s scast NEG_INF) \<Longrightarrow> scast ?sum \<equiv>\<^sub>U r1 + r2"
    apply (simp add: repU_def repe.simps word_sle_def up1 up2)
    apply(rule exI[where x= "r'\<^sub>1 - 0x7FFFFFFF"]) (*r1 + r2*)
    apply(rule conjI)
    subgoal using leq1 leq2 geq1 geq2 by auto
    apply(rule disjI2)
    apply(rule disjI2)
    apply(auto)
    subgoal
      proof -
      have f:"r'\<^sub>1 =  (real_of_int (sint w1))"
        by (simp add: leq1 leq2 )
       assume a:"\<not> sint (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
       then have sintw2_bound:"sint (((scast w1)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
         unfolding min_extend_val by auto 
       have "- 0x7FFFFFFF < sint w1 + (- 0x7FFFFFFF)"
         using sintw2_bound case1a min_extend_val' scast_eq1 by linarith
       then have w2bound:"0 < sint w1" 
         using less_add_same_cancel2 by blast
       have rightSize:"sint (((scast w1)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
         unfolding w1case1a 
         using w2bound Word.word_sint.Rep[of "(w1)::32 Word.word"]
         by (auto simp add: sints32 len32[of "TYPE(32)"] scast_eq1)
      have downcast:"sint ((scast (((scast w1)::64 Word.word) + ((- 0x7FFFFFFF))))::word)
                   = sint (((scast w1)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word))"
        using scast_down_range[OF rightSize]
        by auto
      then have b:"sint ((scast (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001))::word) 
                 = sint (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001)" 
        using min_extend_val by auto
      have "(real_of_int (sint ((scast w1)::64 Word.word ) - 2147483647)) 
          = r'\<^sub>1 -  (real_of_int 2147483647)"
          by (simp add: scast_eq1 leq2)
      then show "r'\<^sub>1 -  2147483647 
        = (real_of_int (sint ((scast (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001))::word)))"
        by (metis b w1case1a' min_extend_val' diff_minus_eq_add minus_minus of_int_numeral)
      qed
    subgoal  
    proof -
      assume "\<not> sint (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
      then have sintw2_bound:"sint (((scast w1)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
        unfolding neg64 by auto 
      have "- 0x7FFFFFFF < sint w1 + (- 0x7FFFFFFF)"
        using sintw2_bound case1a min_extend_val' scast_eq1 by linarith
      then have w2bound:"0 < sint w1" 
        using less_add_same_cancel2 by blast
      have rightSize:"sint (((scast w1)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
        unfolding case1a scast_eq1 w1case1a'
        using Word.word_sint.Rep[of "(w1)::32 Word.word"] w2bound
        by(auto simp add: sints32 len32[of "TYPE(32)"])
      have downcast:"sint ((scast (((scast w1)::64 Word.word) + ((- 0x7FFFFFFF))))::word) 
                   = sint (((scast w1)::64 Word.word) + ((- 0x7FFFFFFF)::64 Word.word)) "
        using scast_down_range[OF rightSize]
        by auto
      show "sint (scast (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001)::word) < 2147483647"
        using downcast min_extend_val' w1case1a' scast_eq1 arith[of "sint w1", OF w1Leq']
        by auto
    qed
    subgoal proof -
      assume notLeq:"\<not> sint (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001) \<le> - 2147483647"
      then have gr:"sint (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001) > - 2147483647" 
        by auto
      then have sintw2_bound:"sint (((scast w1)::64 Word.word) + (-0x7FFFFFFF)) > - 2147483647"
        unfolding neg64 using notLeq by auto 
      have "- 0x7FFFFFFF < sint w1 + (- 0x7FFFFFFF)"
        using sintw2_bound case1a min_extend_val' scast_eq1 by linarith
      then have w2bound:"0 < sint w1" 
        using less_add_same_cancel2 by blast
      have rightSize:"sint (((scast w1)::64 Word.word) + - 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
        unfolding case1a scast_eq1 w1case1a'
        using Word.word_sint.Rep[of "(w1)::32 Word.word"] w2bound
        by (auto simp add: sints32 len32[of "TYPE(32)"])
      show "- 2147483647 
        < real_of_int (sint ((scast (((scast w1)::64 Word.word) + 0xFFFFFFFF80000001))::word))"
        using scast_down_range[OF rightSize] gr of_int_less_iff of_int_minus of_int_numeral
        by auto
      qed
      done
    have letUp:"(let sum=?sum in if sum <=s scast NEG_INF then NEG_INF else scast sum) \<equiv>\<^sub>U r1+r2"
      using case1 case2
      by (auto simp add: Let_def)
    have puSimp:"pu w1 w2=(let sum = ?sum in if sum <=s scast NEG_INF then NEG_INF else scast sum)"
      using neq3 neq1 eq2 equiv1 leq2 repeInt_simps by force
    then show "pu w1 w2 \<equiv>\<^sub>U r1 + r2"      
      using letUp puSimp by auto
next
  case NumNum
  assume notinf1:"w1 \<noteq> POS_INF"
  assume notinf2:"w2 \<noteq> POS_INF"
  assume notneginf1:"w1 \<noteq> NEG_INF"
  assume notneginf2:"w2 \<noteq> NEG_INF"
  let ?sum = "((scast w1)::64 Word.word) + ((scast w2):: 64 Word.word)"
  have inf_case:"scast POS_INF <=s ?sum \<Longrightarrow> POS_INF \<equiv>\<^sub>U r1 + r2"
    using repU_def repePos_simps 
    by (meson dual_order.strict_trans not_less order_refl)
  have truth:" - (2 ^ (size ((scast w1)::64 Word.word) - 1)) 
     \<le> sint ((scast w1)::64 Word.word) + sint ((scast w2)::64 Word.word) 
   \<and> sint ((scast w1)::64 Word.word) + sint ((scast w2)::64 Word.word) 
     \<le> 2 ^ (size ((scast w1)::64 Word.word) - 1) - 1"
    using Word.word_size[of "(scast w2)::64 Word.word"]
      Word.word_size[of "(scast w1)::64 Word.word"]
    scast_eq1 scast_eq3
    Word.word_sint.Rep[of "(w1)::32 Word.word"]
    Word.word_sint.Rep[of "(w2)::32 Word.word"]
    Word.word_sint.Rep[of "(scast w1)::64 Word.word"]
    Word.word_sint.Rep[of "(scast w2)::64 Word.word"]
    sints64 sints32 by auto 
  have sint_eq:"sint((scast w1 + scast w2)::64 Word.word) = sint w1 + sint w2"
    using signed_arith_sint(1)[of "(scast w1)::64 Word.word" "(scast w2)::64 Word.word", OF truth]
      scast_eq1 scast_eq3
    by auto
  have bigOne:"scast w1 + scast w2 <=s ((- 0x7FFFFFFF)::64 Word.word) 
    \<Longrightarrow> \<exists>r'\<ge>r1 + r2. r' \<le>  (- 0x7FFFFFFF)"
   proof -
     assume "scast w1 + scast w2 <=s ((- 0x7FFFFFFF)::64 Word.word)"
     then have sum_leq:"sint w1 + sint w2 \<le> - 0x7FFFFFFF"
           and sum_leq':" (sint w1 + sint w2) \<le>  (- 2147483647)"
       using sint_eq unfolding Word.word_sle_def by auto 
     obtain r'\<^sub>1 r'\<^sub>2 ::real where 
       bound1:"r'\<^sub>1 \<ge> r1 \<and> (w1 \<equiv>\<^sub>E r'\<^sub>1)" and
       bound2:"r'\<^sub>2 \<ge> r2 \<and> (w2 \<equiv>\<^sub>E r'\<^sub>2)"
       using up1 up2 unfolding repU_def by auto
     have somethingA:"r'\<^sub>1  \<le>  sint w1" and somethingB:"r'\<^sub>2  \<le>  sint w2" 
       using \<open>scast w1 + scast w2 <=s - 0x7FFFFFFF\<close>  word_sle_def notinf1 notinf2 
         bound1 bound2 unfolding repe.simps by auto
     have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w1 + sint w2"
       using somethingA somethingB add_mono by fastforce  
     show "\<exists>r'\<ge>r1 + r2. r' \<le> (- 0x7FFFFFFF)"
       apply(rule exI[where x = "r'\<^sub>1 + r'\<^sub>2"])
       using bound1 bound2 add_mono something sum_leq' order.trans 
       by auto
   qed
   have anImp:"\<And>r'.  (r'\<ge>r1 + r2 \<and> r' \<le>  (- 2147483647)) \<Longrightarrow> 
    (\<exists>r. - (2 ^ 31 - 1) = - (2 ^ 31 - 1) 
     \<and> r' = r \<and> r \<le> (real_of_int (sint ((- (2 ^ 31 - 1))::32 Word.word))))"
      by auto
   have anEq:"((scast ((- (2 ^ 31 - 1))::32 Word.word))::64 Word.word) =  (- 0x7FFFFFFF)"
     by auto
   have bigTwo:
   "\<not>(((scast POS_INF)::64 Word.word) <=s ?sum) \<Longrightarrow> 
    \<not>(?sum <=s ((scast NEG_INF)::64 Word.word)) \<Longrightarrow> 
    \<exists>r'\<ge>r1 + r2. r' = 
      (real_of_int (sint (scast (((scast w1)::64 Word.word) + ((scast w2)::64 Word.word))::word)))
    \<and> (r' <  0x7FFFFFFF \<and>  (-0x7FFFFFFF) < r')"
   proof -
     assume "\<not>(((scast POS_INF)::64 Word.word) <=s ?sum)"
     then have sum_leq:"sint w1 + sint w2 < 0x7FFFFFFF"
       unfolding Word.word_sle_def POS_INF_def using sint_eq by auto
     then have sum_leq':" (sint w1 + sint w2) <  (2147483647)"
       by auto
     assume "\<not>(?sum <=s ((scast NEG_INF)::64 Word.word))"
     then have sum_geq:"(- 0x7FFFFFFF) < sint w1 + sint w2"
       unfolding Word.word_sle_def NEG_INF_def using sint_eq by auto 
     then have sum_geq':" (- 2147483647) <  (sint w1 + sint w2)"
       by auto
     obtain r'\<^sub>1 r'\<^sub>2 ::real where 
       bound1:"r'\<^sub>1 \<ge> r1 \<and> (w1 \<equiv>\<^sub>E r'\<^sub>1)" and
       bound2:"r'\<^sub>2 \<ge> r2 \<and> (w2 \<equiv>\<^sub>E r'\<^sub>2)"
       using up1 up2 unfolding repU_def by auto
     have somethingA:"r'\<^sub>1  \<le>  sint w1" and somethingB:"r'\<^sub>2  \<le>  sint w2" 
       using word_sle_def notinf1 notinf2 bound1 bound2 unfolding repe.simps by auto
     have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w1 + sint w2"
       using somethingA somethingB add_mono by fastforce  
     have "(w1 \<equiv>\<^sub>E r'\<^sub>1)" using bound1 by auto
     then have
           r1w1:"r'\<^sub>1 =  (real_of_int (sint w1))"
       and w1U:" (real_of_int (sint w1)) <  (real_of_int (sint POS_INF))"
       and w1L:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w1))"
       unfolding repe.simps
       using notinf1 notinf2 notneginf1 notneginf2 by (auto)
     have "(w2 \<equiv>\<^sub>E r'\<^sub>2)" using bound2 by auto
     then have
           r2w1:"r'\<^sub>2 =  (real_of_int (sint w2))"
       and w2U:" (real_of_int (sint w2)) <  (real_of_int (sint POS_INF))"
       and w2L:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w2))"
       unfolding repe.simps
       using notinf1 notinf2 notneginf1 notneginf2 by (auto)
     have "sint (((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)) 
         = sint ((scast (((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)))::word)"
       apply(rule scast_down_range)
       unfolding sint_eq using sints32 sum_geq sum_leq by auto
     then have cast_eq:"(sint ((scast (((scast w1)::64 Word.word) 
                      + ((scast w2)::64 Word.word)))::word)) 
                    = sint w1 + sint w2"
       using scast_down_range sints32 sum_geq sum_leq sint_eq by auto
     from something and cast_eq 
     have r12_sint_scast:"r'\<^sub>1 + r'\<^sub>2 
       = (sint ((scast (((scast w1)::64 Word.word) 
         + ((scast w2)::64 Word.word)))::word))"
       using r1w1 w1U w1L r2w1 w2U w2L by (simp)
     show ?thesis 
       using bound1 bound2 add_mono r12_sint_scast cast_eq sum_leq sum_leq' sum_geq' 
       \<open>r'\<^sub>1 + r'\<^sub>2 =  (real_of_int (sint (scast (scast w1 + scast w2))))\<close>
       by auto
   qed
   have neg_inf_case:"?sum <=s ((scast ((NEG_INF)::word))::64 Word.word) \<Longrightarrow> NEG_INF \<equiv>\<^sub>U r1 + r2"
   proof (unfold repU_def NEG_INF_def repe.simps)
     assume "scast w1 + scast w2 <=s ((scast ((- (2 ^ 31 - 1))::word))::64 Word.word)"
     then have "scast w1 + scast w2 <=s ((- 0x7FFFFFFF)::64 Word.word)" 
       by (metis anEq)
     then obtain r' where geq:"(r' \<ge> r1 + r2)" and leq:"(r' \<le>  (- 0x7FFFFFFF))"
      using bigOne by auto
     show "(\<exists>r'\<ge>plus r1 r2.
       (\<exists>r. uminus (minus(2 ^ 31) 1) = POS_INF \<and> r' = r \<and>  (real_of_int (sint POS_INF)) \<le> r) 
     \<or> (\<exists>r. uminus (minus(2 ^ 31) 1) = uminus (minus(2 ^ 31)  1) 
        \<and> r' = r \<and> r \<le> real_of_int (sint ((uminus (minus(2 ^ 31) 1))::word)))
     \<or> (\<exists>w. uminus (minus(2 ^ 31) 1) = w 
        \<and> r' = real_of_int (sint w)
        \<and> (real_of_int (sint w)) <  (real_of_int (sint POS_INF)) 
        \<and> less (real_of_int (sint (uminus (minus(2 ^ 31) 1))))  (real_of_int (sint w))))"
       using  leq anImp geq by auto
   qed
   have int_case:"\<not>(((scast POS_INF)::64 Word.word) <=s ?sum) 
              \<Longrightarrow> \<not> (?sum <=s ((scast NEG_INF)::64 Word.word)) 
              \<Longrightarrow> ((scast ?sum)::word) \<equiv>\<^sub>U r1 + r2"
   proof -
     assume bound1:"\<not> ((scast POS_INF)::64 Word.word) <=s scast w1 + scast w2"
     assume bound2:"\<not> scast w1 + scast w2 <=s ((scast NEG_INF)::64 Word.word)"
     obtain r'::real  
       where rDef:"r' = (real_of_int (sint ((scast (((scast w1)::64 Word.word) 
                        + ((scast w2)::64 Word.word)))::word)))"
       and r12:"r'\<ge>r1 + r2" 
       and boundU:"r' <  0x7FFFFFFF" 
       and boundL:"(-0x7FFFFFFF) < r'"
       using bigTwo[OF bound1 bound2] by auto
     obtain w::word 
     where wdef:"w = (scast (((scast w1)::64 Word.word) + ((scast w2)::64 Word.word))::word)"
       by auto
     then have wr:"r' = (real_of_int (sint w))"
       using r12 bound1 bound2 rDef by blast
     show ?thesis
       unfolding repU_def repe.simps 
       using r12 wdef rDef boundU boundL wr  
       by auto 
   qed
   have almost:"(let sum::64 Word.word = scast w1 + scast w2 in 
     if scast POS_INF <=s sum then POS_INF 
     else if sum <=s scast NEG_INF then NEG_INF 
    else scast sum) \<equiv>\<^sub>U r1 + r2"
   apply(cases "((scast POS_INF)::64 Word.word) <=s ((?sum)::64 Word.word)")
   subgoal using inf_case Let_def int_case neg_inf_case by auto
   apply(cases "?sum <=s scast NEG_INF")
   subgoal 
     using inf_case Let_def int_case neg_inf_case 
     proof -
       assume "\<not> (scast POS_INF::64 Word.word) <=s scast w1 + scast w2"
       then have "\<not> (scast w1::64 Word.word) + scast w2 <=s scast NEG_INF 
                \<and> \<not> (scast POS_INF::64 Word.word) <=s scast w1 + scast w2 
                \<and> \<not> (scast w1::64 Word.word) + scast w2 <=s scast NEG_INF 
             \<or> ((let w = scast w1 + scast w2 in 
                if scast POS_INF <=s (w::64 Word.word)  then POS_INF 
                else if w <=s scast NEG_INF then NEG_INF 
                else scast w) \<equiv>\<^sub>U r1 + r2)"
         using neg_inf_case by presburger
       then show ?thesis
         using int_case by force
     qed
   subgoal using inf_case Let_def int_case neg_inf_case 
   proof -
     assume a1: "\<not> (scast POS_INF::64 Word.word) <=s scast w1 + scast w2"
     assume "\<not> (scast w1::64 Word.word) + scast w2 <=s scast NEG_INF"
     have "\<not> (scast w1::64 Word.word) + scast w2 <=s scast NEG_INF 
         \<and> \<not> (scast POS_INF::64 Word.word) <=s scast w1 + scast w2 
      \<or> ((let w = scast w1 + scast w2 in 
         if scast POS_INF <=s (w::64 Word.word) then POS_INF 
         else if w <=s scast NEG_INF then NEG_INF 
         else scast w) \<equiv>\<^sub>U r1 + r2)"
       using a1 neg_inf_case by presburger
     then show ?thesis
       using int_case by force
   qed
   done
  then show ?thesis 
    using notinf1 notinf2 notneginf1 notneginf2 by auto
qed
qed

text\<open>Lower bound of w1 + w2\<close>
fun pl :: "word \<Rightarrow> word \<Rightarrow> word"
where "pl w1 w2 = 
(if w1 = NEG_INF then NEG_INF
 else if w2 = NEG_INF then NEG_INF
 else if w1 = POS_INF then 
  (if w2 = POS_INF then POS_INF 
   else
     (let sum::64 Word.word = ((scast w2)::64 Word.word) + ((scast POS_INF)::64 Word.word) in
     if ((scast POS_INF)::64 Word.word) <=s(sum::64 Word.word) then POS_INF
     else scast sum))
 else if w2 = POS_INF then 
  (let sum::64 Word.word = ((scast w1)::64 Word.word) + ((scast POS_INF)::64 Word.word) in
   if ((scast POS_INF)::64 Word.word) <=s(sum::64 Word.word)  then POS_INF
   else scast sum)
 else 
  (let sum::64 Word.word = ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word) in
   if ((scast POS_INF)::64 Word.word) <=s (sum::64 Word.word) then POS_INF
   else if (sum::64 Word.word) <=s ((scast NEG_INF)::64 Word.word) then NEG_INF
   else scast sum))"


subsection \<open>Addition lower bound\<close>

text\<open>Correctness of lower bound of w1 + w2\<close>
lemma pl_lemma:
assumes lo1:"w1 \<equiv>\<^sub>L (r1::real)"
assumes lo2:"w2 \<equiv>\<^sub>L (r2::real)"
shows "pl w1 w2 \<equiv>\<^sub>L (r1 + r2)"
proof -
  have scast_eq1:"sint((scast w1)::64 Word.word) = sint w1" 
    apply(rule Word.sint_up_scast)
    unfolding Word.is_up by auto
  have scast_eq2:"sint((scast (0x80000001::word))::64 Word.word)=sint((0x80000001::32 Word.word))"
    by auto
  have scast_eq3:"sint((scast w2)::64 Word.word) = sint w2"
    apply(rule Word.sint_up_scast)
    unfolding Word.is_up by auto
  have sints64:"sints 64 = {i. - (2 ^ 63) \<le> i \<and> i < 2 ^ 63}"
    using sints_def[of 64] range_sbintrunc[of 63] by auto 
  have sints32:"sints 32 = {i. - (2 ^ 31) \<le> i \<and> i < 2 ^ 31}"
    using sints_def[of 32] range_sbintrunc[of 31] by auto 
  have thing1:"0 \<le> 9223372034707292161 + ((-(2 ^ 31))::real)" by auto
  have "sint (( w2)) \<ge> (-(2 ^ 31))"
    using Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 mem_Collect_eq
    Word.word_size[of "(scast w2)::64 Word.word"] scast_eq1 scast_eq2 scast_eq3 len32 
    by auto
  then have thing4:"sint ((scast w2)::64 Word.word) \<ge> (-(2 ^ 31))" 
    using scast_down_range sint_ge sints_num
    using scast_eq3 by linarith
  have aLeq2:"(-(2 ^ 31)::int) \<ge> -9223372039002259455" by auto 
  then have thing2:" (0::int) \<le> 9223372039002259455 + sint ((scast w2)::64 Word.word)"
    using thing4 aLeq2 
    by (metis ab_group_add_class.ab_left_minus add.commute add_mono neg_le_iff_le)
  have aLeq:"2 ^ 31 \<le> (9223372039002259455::int)" by auto
  have bLeq:"sint ((scast w2)::64 Word.word) \<le> 2 ^ 31"
    apply ( auto simp add: Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 
        scast_eq3 len32)
    using Word.word_sint.Rep[of "(w2)::32 Word.word"] len32[of "TYPE(32)"] sints32 by auto
  have thing3:" sint ((scast w2)::64 Word.word) \<le> 9223372034707292160 "
    using aLeq bLeq by auto
  have truth:" - (2 ^ (size ((scast w2)::64 Word.word) - 1)) 
      \<le> sint ((scast w2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) 
    \<and> sint ((scast w2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) 
      \<le> 2 ^ (size ((scast w2)::64 Word.word) - 1) - 1"
    by(auto simp add:
    Word.word_size[of "(scast w2)::64 Word.word"] 
    Word.word_size[of "(scast (0x7FFFFFFF))::64 Word.word"]
    scast_eq1 scast_eq2 
    sints64 sints32 thing2 thing1 thing3)
  have case1a:" sint (((scast w2)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) 
             =  sint ((scast w2)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
    by(rule signed_arith_sint(1)[OF truth])
  have case1b:"sint ((0xFFFFFFFF80000001)::64 Word.word) < 0"
    by auto
  have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
    by auto
  have neg64:"(((scast w2)::64 Word.word) + 0x7FFFFFFF) 
            = ((scast w2)::64 Word.word) + (0x7FFFFFFF)"
    by auto
  obtain r'\<^sub>1 and r'\<^sub>2 where   
            geq1:"r'\<^sub>1\<le>r1" and equiv1:"w1 \<equiv>\<^sub>E r'\<^sub>1"
        and geq2:"r'\<^sub>2\<le>r2" and equiv2:"w2 \<equiv>\<^sub>E r'\<^sub>2"
          using lo1 lo2 unfolding repL_def by auto
  show ?thesis
proof (cases rule: case_pl_inf[where ?w1.0=w1, where ?w2.0=w2])
  case NegAny
  then show ?thesis
  apply (auto simp add: repL_def repe.simps)
  using lo1 lo2 linear by auto
next
  case AnyNeg
  then show ?thesis 
  apply (auto simp add: repL_def repe.simps)
  using linear by auto
next
  case PosPos
  then show ?thesis 
  using lo1 lo2 
  by (auto simp add: repL_def repe.simps)
next
  case PosNum
  assume neq1:"w2 \<noteq> POS_INF"
  assume eq2:"w1 = POS_INF"
  assume neq3:"w2 \<noteq> NEG_INF"
  let ?sum = "(scast w2 + scast POS_INF)::64 Word.word"
  have case1:"(((scast POS_INF)::64 Word.word) <=s ?sum) \<Longrightarrow> POS_INF \<equiv>\<^sub>L r1 + r2"
    using lo1 lo2 apply (simp add: repL_def repe.simps word_sle_def)
    apply(rule exI[where x= "r1 + r2"])
    using case1a case1b 
    apply (auto simp add: neq1 eq2 neq3 repINT repL_def repe.simps 
      repeInt_simps lo2 word_sless_alt)
   proof -
      fix r'
      assume a1:"0 \<le> sint (((scast w2)::64 Word.word))"
      from a1 have h3:"2147483647 \<le> sint w2 + 0x7FFFFFFF " using scast_eq3
        by auto
      assume a2:"r' \<le> r1"
      assume a3:"(real_of_int (sint w2)) \<le> r2"
      assume a4:"(2147483647) \<le> r'"
      from a2 a4 have h1:"2147483647 \<le> r1" by auto
      from a1 a3 h3 have h2:"0 \<le> r2" 
        using dual_order.trans of_int_le_0_iff le_add_same_cancel2 by fastforce
      show "(2147483647) \<le> r1 + r2 "
        using h1 h2 h3 add.right_neutral add_mono  
        by fastforce
      qed
  have leq1:"r'\<^sub>1 \<ge>  (real_of_int (sint POS_INF))" 
    using equiv1 neq1 eq2 neq3 
    unfolding repe.simps by auto
  have leq2:"r'\<^sub>2 = (real_of_int (sint w2))"
    using equiv2 neq1 eq2 neq3
    unfolding repe.simps by auto      
  have case2:"\<not>(scast POS_INF <=s ?sum) \<Longrightarrow> scast ?sum \<equiv>\<^sub>L r1 + r2"
    apply (simp add: repL_def repe.simps word_sle_def lo1 lo2)
    apply(rule exI[where x= "r'\<^sub>2 + 0x7FFFFFFF"]) (*r1 + r2*)
    apply(rule conjI)
    subgoal 
      proof -
        assume "\<not> 2147483647 \<le> sint (scast w2 + 0x7FFFFFFF)"
        have bound1:"2147483647 \<le> r1"
          using leq1 geq1 by (auto)
        have bound2:"r'\<^sub>2 \<le> r2 "
          using leq2 geq2 by auto        
        show "r'\<^sub>2 + 2147483647 \<le> r1 + r2"
          using bound1 bound2
          by linarith
      qed
    apply(rule disjI2)
    apply(rule disjI2)
    apply(auto)
    subgoal
      proof -
       assume a:"\<not> 2147483647 \<le> sint (((scast w2)::64 Word.word) + 0x7FFFFFFF)"
       then have sintw2_bound:"2147483647 > sint (((scast w2)::64 Word.word) + (0x7FFFFFFF))"
         by auto 
       have case1a:"sint (((scast w2)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) 
                 =  sint ((scast w2)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
         by(rule signed_arith_sint(1)[OF truth])
       have a1:"sint (((scast w2)::64 Word.word) + (0x7FFFFFFF)) 
              = sint((scast w2)::64 Word.word) + sint((0x7FFFFFFF)::64 Word.word)" 
         using case1a by auto
       have c1:"sint((0x7FFFFFFF)::64 Word.word) = 0x7FFFFFFF" 
         by auto
       have "sint w2 + ( 0x7FFFFFFF) <  0x7FFFFFFF"
         using sintw2_bound case1a c1 scast_eq3 by linarith
       then have w2bound:"sint w2 < 0" 
         using add_less_same_cancel2 by blast
       have rightSize:"sint (((scast w2)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
         unfolding case1a scast_eq3 c1 
         using Word.word_sint.Rep[of "(w2)::32 Word.word"] w2bound 
         by (auto simp add: sints32 len32[of "TYPE(32)"])
      have downcast:"sint ((scast (((scast w2)::64 Word.word) + (( 0x7FFFFFFF))))::word)
        = sint (((scast w2)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word))"
        using scast_down_range[OF rightSize]
        by auto
      then have b:"sint ((scast (((scast w2)::64 Word.word) + 0x7FFFFFFF))::word)
                 = sint (((scast w2)::64 Word.word) + 0x7FFFFFFF)" 
        by auto
      have c:"sint (((scast w2)::64 Word.word) + 0x7FFFFFFF)
            = sint ((scast w2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word)"
        using case1a by auto
      have d:"sint ((0x7FFFFFFF)::64 Word.word) = (0x7FFFFFFF)" by auto 
      have f:"r'\<^sub>2 =  (real_of_int (sint w2))"
        by (simp add: leq2)
      show "r'\<^sub>2 +  2147483647 
        = (real_of_int (sint ((scast (((scast w2)::64 Word.word) + 0x7FFFFFFF))::word)))"
        using a b c d scast_eq3 f leq2 of_int_numeral by fastforce
      qed
    subgoal  
    proof -
      have truth2a:"-(2^(size ((scast w2)::64 Word.word)-1)) 
          \<le> sint ((scast w2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) 
        \<and> sint ((scast w2)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) 
          \<le> 2 ^ (size ((scast w2)::64 Word.word) - 1) - 1"
        apply(auto simp add:
            Word.word_size[of "(scast w2)::64 Word.word"]
            Word.word_size[of "(scast (0x7FFFFFFF))::64 Word.word"]
            scast_eq1 scast_eq2 sints64 sints32 thing2)
        using thing1 thing2 thing3 by auto
      have case2a:" sint (((scast w2)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) 
                  = sint ((scast w2)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
        by(rule signed_arith_sint(1)[OF truth2a])
      have min_cast:"(0x7FFFFFFF::64 Word.word) =((scast (0x7FFFFFFF::word))::64 Word.word)"
        by auto
      assume "\<not> 2147483647 \<le> sint (((scast w2)::64 Word.word) + 0x7FFFFFFF)"
      then have sintw2_bound:"2147483647 > sint (((scast w2)::64 Word.word) + (0x7FFFFFFF))"
        using neg64 by auto
      have a:"sint (((scast w2)::64 Word.word) + (0x7FFFFFFF)) 
            = sint((scast w2)::64 Word.word) + sint((0x7FFFFFFF)::64 Word.word)" 
        using case2a by auto
      have c:"sint((0x7FFFFFFF)::64 Word.word) = 0x7FFFFFFF" 
        by auto
      have " 0x7FFFFFFF > sint w2 + ( 0x7FFFFFFF)"
        using sintw2_bound case2a c scast_eq3 by linarith
      then have w2bound:" sint w2 < 0" 
        by simp
      have rightSize:"sint (((scast w2)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
        unfolding case2a scast_eq3 c
        apply (auto simp add: sints32 len32[of "TYPE(32)"])
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 len32[of "TYPE(32)"] w2bound 
        by auto
      have downcast:"sint ((scast (((scast w2)::64 Word.word) + (( 0x7FFFFFFF))))::word) 
        = sint (((scast w2)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word))"
        using scast_down_range[OF rightSize]
        by auto
      then show "sint (scast (((scast w2)::64 Word.word) + 0x7FFFFFFF)::word) < 2147483647"
        unfolding downcast a scast_eq3 c
        using w2bound by auto
    qed
    subgoal proof -
      assume notLeq:"\<not> 2147483647 \<le> sint (((scast w2)::64 Word.word) + 0x7FFFFFFF)"
      then have gr:"sint (((scast w2)::64 Word.word) + 0x7FFFFFFF) <  2147483647" 
        by auto
      have case2a:" sint (((scast w2)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) 
                  = sint ((scast w2)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
        by(rule signed_arith_sint(1)[OF truth])
      have min_cast:"(0x7FFFFFFF::64 Word.word) =((scast (0x7FFFFFFF::word))::64 Word.word)"
        by auto
      have neg64:"(((scast w2)::64 Word.word) + 0x7FFFFFFF) 
                = ((scast w2)::64 Word.word) + (0x7FFFFFFF)"
        by auto
      then have sintw2_bound:"sint (((scast w2)::64 Word.word) + (0x7FFFFFFF)) < 2147483647"
        using neg64 using notLeq by auto 
      have a:"sint (((scast w2)::64 Word.word) + (0x7FFFFFFF)) 
            = sint((scast w2)::64 Word.word) + sint((0x7FFFFFFF)::64 Word.word)"
        using case2a by auto
      have c:"sint((0x7FFFFFFF)::64 Word.word) = 0x7FFFFFFF" 
        by auto
      have "- 2147483647 \<noteq> w2" using neq3 unfolding NEG_INF_def by auto
      then have "sint((- 2147483647)::word) \<noteq> sint w2"
        using word_sint.Rep_inject by blast
      then have n1:"- 2147483647 \<noteq> sint w2"
        by auto
      have "- 2147483648 \<noteq> w2"
        apply(rule repe.cases[OF equiv2])
        by auto
      then have "sint(- 2147483648::word) \<noteq> sint w2"
      using word_sint.Rep_inject by blast
      then have n2:"- 2147483648 \<noteq> sint w2" 
        by auto
      then have d:"sint w2 > - 2147483647"
        using Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 len32[of "TYPE(32)"] neq3 n1 n2
        by auto
      have w2bound:"- 2147483647 < sint w2 + 0x7FFFFFFF"
        using sintw2_bound case2a c scast_eq3 d by linarith
      have rightSize:"sint (((scast w2)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
        using sints32 len32[of "TYPE(32)"] w2bound Word.word_sint.Rep[of "(w2)::32 Word.word"] 
          c case2a scast_eq3 sintw2_bound
        by (auto simp add: sints32 len32[of "TYPE(32)"])
      have downcast:"sint ((scast (((scast w2)::64 Word.word) + (( 0x7FFFFFFF))))::word)
                   = sint (((scast w2)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word))"
        using scast_down_range[OF rightSize]
        by auto
      have sintEq:" sint ((scast (((scast w2)::64 Word.word) + 0x7FFFFFFF))::word) =
          sint (((scast w2)::64 Word.word) + 0x7FFFFFFF) "
          using downcast by auto
      show "- 2147483647 
          < real_of_int (sint ((scast (((scast w2)::64 Word.word) + 0x7FFFFFFF))::word))"
        unfolding sintEq  
        using gr of_int_less_iff of_int_minus of_int_numeral c case2a scast_eq3 w2bound by linarith
      qed
      done
  have "(let sum = ?sum in if scast POS_INF <=s sum then POS_INF else scast sum) \<equiv>\<^sub>L r1 + r2"
    using case1 case2
    by (auto simp add: Let_def)
  then show ?thesis 
    using lo1 lo2 neq1 eq2 neq3 
    by (auto)
next
  case NumPos
    assume neq3:"w1 \<noteq> NEG_INF"
    assume neq1:"w1 \<noteq> POS_INF"
    assume eq2:"w2 = POS_INF"
    let ?sum = "(scast w1 + scast POS_INF)::64 Word.word"
    have thing1:"0 \<le> 9223372034707292161 + ((-(2 ^ 31))::real)" by auto
    have "sint (( w1)) \<ge> (-(2 ^ 31))"
      using Word.word_sint.Rep[of "(w1)::32 Word.word"] scast_eq1 scast_eq2 scast_eq3
        Word.word_size[of "(scast w1)::64 Word.word"] sints32 len32 mem_Collect_eq
      by auto
    then have thing4:"sint ((scast w1)::64 Word.word) \<ge> (-(2 ^ 31))" 
      using scast_down_range sint_ge sints_num scast_eq3 scast_eq1 by linarith
    have aLeq2:"(-(2 ^ 31)::int) \<ge> -9223372039002259455" by auto 
    then have thing2:" (0::int) \<le> 9223372039002259455 + sint ((scast w1)::64 Word.word)"
      using thing4 aLeq2 
      by (metis ab_group_add_class.ab_left_minus add.commute add_mono neg_le_iff_le)
    have aLeq:"2 ^ 31 \<le> (9223372039002259455::int)" by auto
    have bLeq:"sint ((scast w1)::64 Word.word) \<le> 2 ^ 31"
      apply (auto simp add: Word.word_sint.Rep[of "(w1)::32 Word.word"] sints32 
          scast_eq1 len32)
      using Word.word_sint.Rep[of "(w1)::32 Word.word"] len32[of "TYPE(32)"] sints32
      by clarsimp
    have thing3:" sint ((scast w1)::64 Word.word) \<le> 9223372034707292160 "
      using aLeq bLeq by auto
    have truth:" - (2 ^ (size ((scast w1)::64 Word.word) - 1)) 
                   \<le> sint ((scast w1)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word)
                 \<and> sint ((scast w1)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word) 
                   \<le> 2 ^ (size ((scast w1)::64 Word.word) - 1) - 1"
      by(auto simp add:
      Word.word_size[of "(scast w1)::64 Word.word"]
      Word.word_size[of "(scast (0x7FFFFFFF))::64 Word.word"]
      scast_eq3 scast_eq2 sints64 sints32 thing2 thing1 thing3)
    have case1a:"sint (((scast w1)::64 Word.word) + (0x7FFFFFFF::64 Word.word)) 
               = sint ((scast w1)::64 Word.word) + sint (0x7FFFFFFF::64 Word.word)"
      by(rule signed_arith_sint(1)[OF truth])
    have case1b:"sint ((0xFFFFFFFF80000001)::64 Word.word) < 0"
      by auto
    have g:"(0x7FFFFFFF::64 Word.word) = 0x7FFFFFFF" by auto
    have c:"sint (((scast w1)::64 Word.word) + 0x7FFFFFFF) 
          = sint ((scast w1)::64 Word.word) + sint ((0x7FFFFFFF)::64 Word.word)"
      using g case1a 
      by blast
    have d:"sint ((0x7FFFFFFF)::64 Word.word) = (0x7FFFFFFF)" by auto 
    have e:"sint ((scast w1)::64 Word.word) = sint w1" 
      using scast_eq1 by blast
    have d2:"sint w1 \<le> 2^31 - 1"
      using Word.word_sint.Rep[of "(w1)::32 Word.word"] 
      by (auto simp add: sints32 len32[of "TYPE(32)"])
    have case1:"scast POS_INF <=s ?sum \<Longrightarrow> POS_INF \<equiv>\<^sub>L r1 + r2"
      using lo1 lo2 apply (simp add: repL_def repe.simps word_sle_def)
      apply(rule exI[where x= "r1 + r2"])
      apply(auto)
          using case1a case1b 
          apply (auto simp add: neq1 eq2 neq3 repINT repL_def 
            repe.simps repeInt_simps lo2 word_sless_alt) (* close 4 goals *)
     proof -
        fix r'
        have h3:"sint (((scast w1)::64 Word.word) + 0x7FFFFFFF) 
          = sint (((scast w1)::64 Word.word)) + sint(0x7FFFFFFF::64 Word.word)" 
          using case1a by auto 
        have h4:"sint(0x7FFFFFFF::64 Word.word) = 2147483647" by auto
        assume a1:"0 \<le> sint ((scast w1)::64 Word.word)"
        then have h3:"sint w1 \<ge> 0" using scast_eq1 h3 h4 by auto 
        assume a2:"r' \<le> r2"
        assume a3:"(real_of_int (sint w1)) \<le> r1"
        assume a4:"(2147483647) \<le> r'"
        from a2 a4 have h1:"r2 \<ge>  2147483647" by auto
        from a1 a3 h3 have h2:"r1 \<ge> 0" 
          using dual_order.trans of_int_0_le_iff by fastforce
        show " 2147483647 \<le> r1 + r2"
          using h1 h2 add.right_neutral add_mono by fastforce
        qed
    have leq1:"r'\<^sub>2 \<ge>  (real_of_int (sint POS_INF))" and leq2:"r'\<^sub>1 =  (real_of_int (sint w1))" 
      using equiv1 equiv2 neq1 eq2 neq3 unfolding repe.simps by auto
    have neg64:"(((scast w1)::64 Word.word) + 0xFFFFFFFF80000001) 
              = ((scast w1)::64 Word.word) + (-0x7FFFFFFF)" 
      by auto
    have case2:"\<not>(scast POS_INF <=s ?sum) \<Longrightarrow> scast ?sum \<equiv>\<^sub>L r1 + r2"
      apply (simp add: repL_def repe.simps word_sle_def lo1 lo2)
      apply(rule exI[where x= "r'\<^sub>1 + 0x7FFFFFFF"]) 
      apply(rule conjI)
      subgoal 
        proof -
          assume "\<not> 2147483647 \<le> sint (scast w1 + 0x7FFFFFFF)"
          have bound1:"r2 \<ge>  2147483647"
            using leq1 geq2 by (auto)
          have bound2:"r1 \<ge> r'\<^sub>1"
            using leq2 geq1 by auto        
          show "r'\<^sub>1 + 2147483647 \<le> r1 + r2"
            using bound1 bound2
            by linarith
          qed
      apply(rule disjI2)
      apply(rule disjI2)
      apply(auto)
      subgoal
        proof -
        have f:"r'\<^sub>1 =  (real_of_int (sint w1))"
          by (simp add: leq1 leq2 )
         assume a:"\<not> 2147483647 \<le> sint (((scast w1)::64 Word.word) + 0x7FFFFFFF)"
         then have sintw2_bound:"2147483647 > sint (((scast w1)::64 Word.word) + (0x7FFFFFFF))"
           by auto 
         have "0x7FFFFFFF > sint w1 + (0x7FFFFFFF)"
           using sintw2_bound case1a d scast_eq1 by linarith
         then have w2bound:"0 > sint w1" 
           using add_less_same_cancel2 by blast
         have rightSize:"sint (((scast w1)::64 Word.word) + 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
           unfolding case1a e 
           using w2bound Word.word_sint.Rep[of "(w1)::32 Word.word"]
           by (auto simp add: sints32 len32[of "TYPE(32)"] )
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w1)::64 Word.word) + (( 0x7FFFFFFF))))::word) 
                     = sint (((scast w1)::64 Word.word) + (( 0x7FFFFFFF)::64 Word.word))"
          using scast_down_range[OF rightSize]
          by auto
        then have b:"sint((scast (((scast w1)::64 Word.word) + 0x7FFFFFFF))::word)
                   = sint(((scast w1)::64 Word.word) + 0x7FFFFFFF)" 
          using g by auto
        show "r'\<^sub>1 + 2147483647
          = (real_of_int (sint ((scast (((scast w1)::64 Word.word) + 0x7FFFFFFF))::word)))"
          using a b c d e f 
          proof -
            have "(real_of_int (sint ((scast w1)::64 Word.word ) + 2147483647)) 
                = r'\<^sub>1 +  (real_of_int 2147483647)"
              using e leq2 by auto
            then show ?thesis
              using b c d of_int_numeral by metis
          qed
        qed
      subgoal  
      proof -
        assume "\<not> 2147483647 \<le> sint (((scast w1)::64 Word.word) + 0x7FFFFFFF)"
        then have sintw2_bound:"sint (((scast w1)::64 Word.word) + (0x7FFFFFFF)) < 2147483647"
          unfolding neg64 by auto 
        have "0x7FFFFFFF > sint w1 + (0x7FFFFFFF)"
          using sintw2_bound case1a d scast_eq1 by linarith
        then have w2bound:"0 > sint w1" 
          using add_less_same_cancel2 by blast
        have rightSize:"sint (((scast w1)::64 Word.word) + 0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case1a e c 
          using Word.word_sint.Rep[of "(w1)::32 Word.word"] w2bound
          by (auto simp add: sints32 len32[of "TYPE(32)"])
        have arith:"\<And>x::int. x \<le> 2 ^ 31 - 1 \<Longrightarrow> x + (- 2147483647) < 2147483647"
          by auto
        have downcast:"sint ((scast (((scast w1)::64 Word.word) + 0x7FFFFFFF))::word) 
          = sint (((scast w1)::64 Word.word) + ((0x7FFFFFFF)::64 Word.word))"
          using scast_down_range[OF rightSize]
          by auto
        show "sint (scast (((scast w1)::64 Word.word) + 0x7FFFFFFF)::word) < 2147483647"
          using downcast d e c arith[of "sint w1", OF d2] sintw2_bound by linarith
      qed
      subgoal proof -
        assume notLeq:"\<not> 2147483647 \<le> sint (((scast w1)::64 Word.word) + 0x7FFFFFFF)"
        then have gr:"2147483647 > sint (((scast w1)::64 Word.word) + 0x7FFFFFFF)" 
          by auto
        then have sintw2_bound:"sint (((scast w1)::64 Word.word) + (0x7FFFFFFF)) < 2147483647"
          unfolding neg64 using notLeq by auto 
        have "0x7FFFFFFF > sint w1 + ( 0x7FFFFFFF)"
          using sintw2_bound case1a d scast_eq1 by linarith
        then have useful:"0 > sint w1"
          using add_less_same_cancel2 by blast
        have rightSize:"sint (((scast w1)::64 Word.word) +  0x7FFFFFFF) \<in> sints (len_of TYPE(32))"
          unfolding case1a e
          using Word.word_sint.Rep[of "(w1)::32 Word.word"]
            sints32 len32[of "TYPE(32)"] useful
          by auto
        have "- 2147483647 \<noteq> w1" using neq3 unfolding NEG_INF_def by auto
        then have "sint((- 2147483647)::word) \<noteq> sint w1"
          using word_sint.Rep_inject by blast
        then have n1:"- 2147483647 \<noteq> sint w1"
          by auto
        have "- 2147483648 \<noteq> w1"
          apply(rule repe.cases[OF equiv1]) using int_not_undef[of w1] by auto
        then have "sint(- 2147483648::word) \<noteq> sint w1"
          using word_sint.Rep_inject by blast
        then have n2:"- 2147483648 \<noteq> sint w1" 
          by auto
        then have d:"sint w1 > - 2147483647"
          using Word.word_sint.Rep[of "(w1)::32 Word.word"] 
            sints32 len32[of "TYPE(32)"] n1 n2 neq3 
          by (simp)
        have d2:"sint (0x7FFFFFFF::64 Word.word) > 0"
          by auto
        from d d2 have d3:"- 2147483647 < sint w1 + sint (0x7FFFFFFF::64 Word.word)"
          by auto
        have d4:"sint ((scast (((scast w1)::64 Word.word) + 0x7FFFFFFF))::word) 
          = sint w1 + sint (0x7FFFFFFF::64 Word.word)"
          using case1a rightSize scast_down_range scast_eq1 by fastforce  
        then show "-2147483647 
          < real_of_int (sint ((scast (((scast w1)::64 Word.word) + 0x7FFFFFFF))::word))"
          using d3 d4 by auto
        qed done
      have "(let sum = ?sum in if scast POS_INF <=s sum then POS_INF else scast sum) \<equiv>\<^sub>L r1 + r2"
        using case1 case2
        by (auto simp add: Let_def)
      then show ?thesis 
        using neq1 eq2 neq3 by (auto)
next
  case NumNum
  assume notinf1:"w1 \<noteq> POS_INF"
  assume notinf2:"w2 \<noteq> POS_INF"
  assume notneginf1:"w1 \<noteq> NEG_INF"
  assume notneginf2:"w2 \<noteq> NEG_INF"
  let ?sum = "((scast w1)::64 Word.word) + ((scast w2):: 64 Word.word)"
  have truth:" - (2 ^ (size ((scast w1)::64 Word.word) - 1)) 
      \<le> sint ((scast w1)::64 Word.word) + sint ((scast w2)::64 Word.word) 
    \<and> sint ((scast w1)::64 Word.word) + sint ((scast w2)::64 Word.word) 
      \<le> 2 ^ (size ((scast w1)::64 Word.word) - 1) - 1"
    using Word.word_size[of "(scast w2)::64 Word.word"] 
      Word.word_size[of "(scast w1)::64 Word.word"]
      scast_eq1 scast_eq3 sints64 sints32
      Word.word_sint.Rep[of "(w1)::32 Word.word"]
      Word.word_sint.Rep[of "(w2)::32 Word.word"]
    by auto 
  have sint_eq:"sint((scast w1 + scast w2)::64 Word.word) = sint w1 + sint w2"
    using signed_arith_sint(1)[of "(scast w1)::64 Word.word" "(scast w2)::64 Word.word", OF truth]
      scast_eq1 scast_eq3
    by auto
  have bigOne:"scast w1 + scast w2 <=s ((- 0x7FFFFFFF)::64 Word.word) 
    \<Longrightarrow> \<exists>r'\<le>r1 + r2. r' \<le>  -0x7FFFFFFF"
  proof -
    assume "scast w1 + scast w2 <=s ((- 0x7FFFFFFF)::64 Word.word)"
    then have sum_leq:"sint w1 + sint w2 \<le> - 0x7FFFFFFF"
          and sum_leq':" (sint w1 + sint w2) \<le>  (- 2147483647)"
      using sint_eq unfolding Word.word_sle_def by auto 
    obtain r'\<^sub>1 r'\<^sub>2 ::real where 
      bound1:"r'\<^sub>1 \<le> r1 \<and> (w1 \<equiv>\<^sub>E r'\<^sub>1)" and
      bound2:"r'\<^sub>2 \<le> r2 \<and> (w2 \<equiv>\<^sub>E r'\<^sub>2)"
      using lo1 lo2 unfolding repL_def by auto
    have somethingA:"r'\<^sub>1 \<le> sint w1" and somethingB:"r'\<^sub>2 \<le> sint w2" 
      using bound1 bound2 \<open>scast w1 + scast w2 <=s -0x7FFFFFFF\<close> word_sle_def notinf1 notinf2 
      unfolding repe.simps by auto
    have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w1 + sint w2"
      using somethingA somethingB add_mono 
      by fastforce  
    show "\<exists>r'\<le>r1 + r2. r' \<le> (-0x7FFFFFFF)"
      apply(rule exI[where x = "r'\<^sub>1 + r'\<^sub>2"])
      using bound1 bound2 add_mono something sum_leq' order.trans by auto
  qed
  have anImp:"\<And>r'.  (r'\<ge>r1 + r2 \<and> r' \<le>  (- 2147483647)) \<Longrightarrow>
   (\<exists>r. - (2 ^ 31 - 1) = - (2 ^ 31 - 1) \<and> r' = r \<and> r 
        \<le> (real_of_int (sint ((- (2 ^ 31 - 1))::32 Word.word))))"
    by auto
  have anEq:"((scast ((- (2 ^ 31 - 1))::32 Word.word))::64 Word.word) = (- 0x7FFFFFFF)"
    by auto
  have bigTwo:
   "\<not>(((scast POS_INF)::64 Word.word) <=s ?sum) \<Longrightarrow>
    \<not>(?sum <=s ((scast NEG_INF)::64 Word.word)) \<Longrightarrow>
    \<exists>r'\<le>r1 + r2. r' = (real_of_int (sint (scast (((scast w1)::64 Word.word)
                      + ((scast w2)::64 Word.word))::word)))
               \<and> (r' <  0x7FFFFFFF \<and>  (-0x7FFFFFFF) < r')"
  proof -
    assume "\<not>(((scast POS_INF)::64 Word.word) <=s ?sum)"
    then have sum_leq:"sint w1 + sint w2 < 0x7FFFFFFF"
      unfolding Word.word_sle_def using sint_eq by auto
    then have sum_leq':" (sint w1 + sint w2) < (2147483647)"
      by auto
    assume "\<not>(?sum <=s ((scast NEG_INF)::64 Word.word))"
    then have sum_geq:"(- 0x7FFFFFFF) < sint w1 + sint w2"
      unfolding Word.word_sle_def using sint_eq by auto
    then have sum_geq':" (- 2147483647) <  (sint w1 + sint w2)"
      by auto
    obtain r'\<^sub>1 r'\<^sub>2 ::real where 
      bound1:"r'\<^sub>1 \<le> r1 \<and> (w1 \<equiv>\<^sub>E r'\<^sub>1)" and
      bound2:"r'\<^sub>2 \<le> r2 \<and> (w2 \<equiv>\<^sub>E r'\<^sub>2)"
       using lo1 lo2 unfolding repL_def by auto
    have somethingA:"r'\<^sub>1  \<le>  sint w1" and somethingB:"r'\<^sub>2 \<le> sint w2" 
      using word_sle_def notinf1 notinf2 bound1 bound2 unfolding repe.simps by auto
    have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w1 + sint w2"
      using somethingA somethingB add_mono 
      by fastforce  
    have "(w1 \<equiv>\<^sub>E r'\<^sub>1)" using bound1 by auto
    then have
          r1w1:"r'\<^sub>1 = (real_of_int (sint w1))"
      and w1U:"(real_of_int (sint w1)) < (real_of_int (sint POS_INF))"
      and w1L:"(real_of_int (sint NEG_INF)) < (real_of_int (sint w1))"
      unfolding repe.simps
      using notinf1 notinf2 notneginf1 notneginf2 by (auto)
    have "(w2 \<equiv>\<^sub>E r'\<^sub>2)" using bound2 by auto
    then have
          r2w1:"r'\<^sub>2 =  (real_of_int (sint w2))"
      and w2U:"(real_of_int (sint w2)) < (real_of_int (sint POS_INF))"
      and w2L:"(real_of_int (sint NEG_INF)) < (real_of_int (sint w2))"
      unfolding repe.simps
      using notinf1 notinf2 notneginf1 notneginf2 by (auto)
    have "sint (((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)) 
        = sint ((scast (((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)))::word)"
      apply(rule scast_down_range)
      unfolding sint_eq using sints32 sum_geq sum_leq by auto
    then have cast_eq:"(sint ((scast (((scast w1)::64 Word.word) 
        + ((scast w2)::64 Word.word)))::word)) 
      = sint w1 + sint w2"
      using scast_down_range sints32 sum_geq sum_leq sint_eq by auto
    from something and cast_eq 
    have r12_sint_scast:"r'\<^sub>1 + r'\<^sub>2 
      = (sint ((scast (((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)))::word))"
      using r1w1 w1U w1L r2w1 w2U w2L 
      by (simp)
    have leq_ref:"\<And>x y ::real. x = y ==> x \<le> y" by auto
    show ?thesis
      apply(rule exI[where x="r'\<^sub>1 + r'\<^sub>2"])
      apply(rule conjI)
      subgoal 
        using r12_sint_scast cast_eq leq_ref r2w1 r1w1 add_mono[of r'\<^sub>1 r1 r'\<^sub>2 r2] bound1 bound2
        by auto
      using bound1 bound2 add_mono r12_sint_scast cast_eq sum_leq sum_leq' sum_geq' sum_geq
      \<open>r'\<^sub>1 + r'\<^sub>2 =  (real_of_int (sint (scast (scast w1 + scast w2))))\<close> 
      by auto
    qed
  have neg_inf_case:"?sum <=s ((scast ((NEG_INF)::word))::64 Word.word)  \<Longrightarrow> NEG_INF \<equiv>\<^sub>L r1 + r2"
  proof (unfold repL_def NEG_INF_def repe.simps)
    assume "scast w1 + scast w2 <=s ((scast ((- (2 ^ 31 - 1))::word))::64 Word.word)"
    then have "scast w1 + scast w2 <=s ((- 0x7FFFFFFF)::64 Word.word)" 
      by (metis anEq)
    then obtain r' where geq:"(r' \<le> r1 + r2)" and leq:"(r' \<le> (-0x7FFFFFFF))"
      using bigOne by auto
    show "(\<exists>r'\<le>plus r1  r2.
      (\<exists>r. uminus (minus(2 ^ 31) 1) = POS_INF \<and> r' = r \<and>  (real_of_int (sint POS_INF)) \<le> r)
    \<or> (\<exists>r. uminus (minus(2 ^ 31) 1) = uminus (minus(2 ^ 31)  1) 
        \<and> r' = r \<and> r \<le>  (real_of_int (sint ((uminus (minus(2 ^ 31) 1))::word))))
    \<or> (\<exists>w. uminus (minus(2 ^ 31) 1) = w \<and>
           r' =  (real_of_int (sint w)) \<and>
            (real_of_int (sint w)) <  (real_of_int (sint POS_INF)) 
        \<and> less ( (real_of_int (sint (uminus (minus(2 ^ 31) 1))))) ((real_of_int (sint w)))))"
    using  leq geq by auto
  qed
  have bigThree:"0x7FFFFFFF <=s ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word) 
    \<Longrightarrow> \<exists>r'\<le>r1 + r2. 2147483647 \<le> r'"
  proof -
    assume "0x7FFFFFFF <=s ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)"
    then have sum_leq:"0x7FFFFFFF \<le> sint w1 + sint w2 "
          and sum_leq':" 2147483647 \<le>  (sint w1 + sint w2)"
      using sint_eq unfolding Word.word_sle_def by auto 
    obtain r'\<^sub>1 r'\<^sub>2 ::real where 
      bound1:"r'\<^sub>1 \<le> r1 \<and> (w1 \<equiv>\<^sub>E r'\<^sub>1)" and
      bound2:"r'\<^sub>2 \<le> r2 \<and> (w2 \<equiv>\<^sub>E r'\<^sub>2)"
      using lo1 lo2 unfolding repL_def by auto
    have somethingA:"r'\<^sub>1  \<le>  sint w1" and somethingB:"r'\<^sub>2  \<le>  sint w2" 
      using \<open> 0x7FFFFFFF <=s scast w1 + scast w2 \<close> word_sle_def notinf1 notinf2
        bound1 bound2 repe.simps
      by auto
    have something:"r'\<^sub>1 + r'\<^sub>2 \<le>  sint w1 + sint w2"
      using somethingA somethingB add_mono of_int_add  
      by fastforce  
    show "\<exists>r'\<le> r1 + r2.  (2147483647) \<le> r'"
      apply(rule exI[where x = "r'\<^sub>1 + r'\<^sub>2"])
      using bound1 bound2 add_mono something sum_leq' order.trans
    proof -
      have f1: " (real_of_int (sint w2)) = r'\<^sub>2"
        by (metis bound2 notinf2 notneginf2 repe.cases)
      have " (real_of_int (sint w1)) = r'\<^sub>1"
        by (metis bound1 notinf1 notneginf1 repe.cases)
      then have f2: " (real_of_int 2147483647) \<le> r'\<^sub>2 + r'\<^sub>1"
        using f1 sum_leq' by force
      have "r'\<^sub>2 + r'\<^sub>1 \<le> r2 + r1"
        by (meson add_left_mono add_right_mono bound1 bound2 order.trans)
      then show "r'\<^sub>1 + r'\<^sub>2 \<le> r1 + r2 \<and>  2147483647 \<le> r'\<^sub>1 + r'\<^sub>2"
        using f2 by (simp add: add.commute)
    qed
  qed
  have inf_case:"((scast POS_INF)::64 Word.word) <=s ?sum \<Longrightarrow> POS_INF \<equiv>\<^sub>L r1 + r2"
    proof -
      assume "((scast POS_INF)::64 Word.word) 
          <=s ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)"
      then have "((scast ((2 ^ 31 - 1)::word))::64 Word.word) 
             <=s ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)"
        unfolding  repL_def repe.simps by auto
      then have "(0x7FFFFFFF::64 Word.word) 
             <=s ((scast w1)::64 Word.word) + ((scast w2)::64 Word.word)"
        by auto
      then obtain r' where geq:"(r' \<le> r1 + r2)" and leq:"(0x7FFFFFFF \<le> r')"
        using bigThree by auto
      show "?thesis"
        unfolding repL_def repe.simps using leq geq by auto
    qed
  have int_case:"\<not>(((scast POS_INF)::64 Word.word) <=s ?sum) 
    \<Longrightarrow> \<not> (?sum <=s ((scast NEG_INF)::64 Word.word)) 
    \<Longrightarrow> ((scast ?sum)::word) \<equiv>\<^sub>L r1 + r2"
  proof -
    assume bound1:"\<not> ((scast POS_INF)::64 Word.word) <=s scast w1 + scast w2"
    assume bound2:"\<not> scast w1 + scast w2 <=s ((scast NEG_INF)::64 Word.word)"
    obtain r'::real  
      where rDef:"r' = (real_of_int (sint ((scast (((scast w1)::64 Word.word) 
                     + ((scast w2)::64 Word.word)))::word)))"
      and r12:"r'\<le>r1 + r2" 
      and boundU:"r' <  0x7FFFFFFF" 
      and boundL:" (-0x7FFFFFFF) < r'"
      using bigTwo[OF bound1 bound2] by auto
    obtain w::word 
    where wdef:"w = (scast (((scast w1)::64 Word.word) + ((scast w2)::64 Word.word))::word)"
      by auto
    then have wr:"r' =  (real_of_int (sint w))"
      using r12 bound1 bound2 rDef by blast
    show ?thesis
      unfolding repL_def repe.simps 
      using r12 wdef rDef boundU boundL wr  
      by auto 
  qed
  have "(let sum = ?sum in
    if scast POS_INF <=s sum then POS_INF 
    else if sum <=s scast NEG_INF then NEG_INF 
    else scast sum) \<equiv>\<^sub>L r1 + r2"
    apply(cases "((scast POS_INF)::64 Word.word) <=s ?sum")
     apply(cases "?sum <=s scast NEG_INF")
      using inf_case neg_inf_case int_case by (auto simp add: Let_def)
  then show ?thesis 
    using notinf1 notinf2 notneginf1 notneginf2
    by(auto)
qed
qed

subsection \<open>Max function\<close>

text\<open>Maximum of w1 + w2 in 2s-complement\<close>
fun wmax :: "word \<Rightarrow> word \<Rightarrow> word"
where "wmax w1 w2 = (if w1 <s w2 then w2 else w1)"

text\<open>Correctness of wmax\<close>
lemma wmax_lemma:
  assumes eq1:"w1 \<equiv>\<^sub>E (r1::real)"
  assumes eq2:"w2 \<equiv>\<^sub>E (r2::real)"
  shows "wmax w1 w2 \<equiv>\<^sub>E (max r1 r2)"
proof(cases rule: case_inf2[where ?w1.0=w1, where ?w2.0=w2])
  case PosPos
  from PosPos eq1 eq2
  have bound1:"(real_of_int (sint POS_INF)) \<le> r1"
  and bound2:"(real_of_int (sint POS_INF)) \<le> r2"
    by (auto simp add: repe.simps)
  have eqInf:"wmax w1 w2 = POS_INF"
    using PosPos unfolding wmax.simps by auto
  have pos_eq:"POS_INF \<equiv>\<^sub>E max r1 r2"
    apply(rule repPOS_INF)
    using bound1 bound2
    by linarith
  show ?thesis
    using pos_eq eqInf by auto
next
  case PosNeg
  from PosNeg 
  have bound1:"(real_of_int (sint POS_INF)) \<le> r1"
   and bound2:"r2 \<le> (real_of_int (sint NEG_INF))"
    using eq1 eq2 by (auto simp add: repe.simps)
  have eqNeg:"wmax w1 w2 = POS_INF"
    unfolding eq1 eq2 wmax.simps PosNeg word_sless_def word_sle_def
    by(auto) 
  have neg_eq:"POS_INF \<equiv>\<^sub>E max r1 r2"
    apply(rule repPOS_INF)
    using bound1 bound2 eq1 eq2 by auto
  show "?thesis"
    using eqNeg neg_eq by auto
next
  case PosNum
  from PosNum eq1 eq2
  have bound1:" (real_of_int (sint POS_INF)) \<le> r1"
  and bound2a:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w2))"
  and bound2b:" (real_of_int (sint w2)) <  (real_of_int (sint POS_INF))"
    by (auto simp add: repe.simps)
  have eqNeg:"wmax w1 w2 = POS_INF"
    using PosNum bound2b 
    unfolding wmax.simps word_sless_def word_sle_def
    by auto 
  have neg_eq:"POS_INF \<equiv>\<^sub>E max r1 r2"
    apply (rule repPOS_INF)
    using bound1 bound2a bound2b word_sless_alt le_max_iff_disj 
    unfolding eq1 eq2 by blast
  show "?thesis"
    using eqNeg neg_eq by auto
next
  case NegPos
  from NegPos eq1 eq2
  have bound1:"r1 \<le>  (real_of_int (sint NEG_INF))"
   and bound2:" (real_of_int (sint POS_INF)) \<le> r2"
    by (auto simp add: repe.simps)
  have eqNeg:"wmax w1 w2 = POS_INF"
    unfolding NegPos word_sless_def word_sle_def
    by(auto)
  have neg_eq:"POS_INF \<equiv>\<^sub>E max r1 r2"
    apply(rule repPOS_INF)
    using bound1 bound2 by auto
  show "wmax w1 w2 \<equiv>\<^sub>E max r1 r2"
    using eqNeg neg_eq by auto
next
  case NegNeg
  from NegNeg eq1 eq2
  have bound1:"r1 \<le>  (real_of_int (sint NEG_INF))"
   and bound2:"r2 \<le>  (real_of_int (sint NEG_INF))"
    by (auto simp add: repe.simps)
  have eqNeg:"NEG_INF \<equiv>\<^sub>E max r1 r2"
    apply(rule repNEG_INF)
    using eq1 eq2 bound1 bound2
    by(auto)
  have neg_eq:"wmax w1 w2 = NEG_INF"
    using NegNeg by auto 
  show "wmax w1 w2 \<equiv>\<^sub>E max r1 r2"
    using eqNeg neg_eq by auto
next
  case NegNum
  from NegNum eq1 eq2
  have eq3:"r2 = (real_of_int (sint w2))"
   and bound2a:"(real_of_int (sint w2)) < (real_of_int (sint POS_INF))"
   and bound2b:"(real_of_int (sint NEG_INF)) < (real_of_int (sint w2))"
   and bound1:"r1 \<le> (real_of_int (sint NEG_INF))"
    by (auto simp add: repe.simps)
  have eqNeg:"max r1 r2 = (real_of_int (sint w2))"
    using NegNum assms(2) bound2a eq3 repeInt_simps bound1 bound2a bound2b
    by (metis less_irrefl max.bounded_iff max_def not_less)
  then have extra_eq:"(wmax w1 w2) = w2"
    using assms(2) bound2a eq3 NegNum repeInt_simps 
    by (simp add: word_sless_alt)
  have neg_eq:"wmax w1 w2 \<equiv>\<^sub>E (real_of_int (sint (wmax w1 w2)))"
    apply(rule repINT)
    using extra_eq eq3 bound2a bound2b by(auto)
  show "wmax w1 w2 \<equiv>\<^sub>E max r1 r2"
    using eqNeg neg_eq extra_eq by auto
next
  case NumPos
  from NumPos eq1 eq2
  have p2:"w2 = POS_INF"
   and eq1:"r1 = (real_of_int (sint w1))"
   and eq2:"r2 = r2"
   and bound1a:"(real_of_int (sint w1)) < (real_of_int (sint POS_INF))"
   and bound1b:"(real_of_int (sint NEG_INF)) < (real_of_int (sint w1))"
   and bound2:"(real_of_int (sint POS_INF)) \<le> r2"
    by (auto simp add: repe.simps)    
  have res1:"wmax w1 w2 = POS_INF"
    using NumPos p2 eq1 eq2 assms(1) bound1b p2 repeInt_simps 
    by (simp add: word_sless_alt)
  have res3:"POS_INF \<equiv>\<^sub>E max r1 r2"
    using repPOS_INF NumPos bound2 le_max_iff_disj by blast
  show "wmax w1 w2 \<equiv>\<^sub>E max r1 r2" 
    using res1 res3 by auto
next
  case NumNeg
  from NumNeg eq1 eq2
  have n2:"w2 = NEG_INF"
   and rw1:"r1 = (real_of_int (sint w1))"
   and bound1a:"(real_of_int (sint w1)) < (real_of_int (sint POS_INF))"
   and bound1b:"(real_of_int (sint NEG_INF)) < (real_of_int (sint w1))"
   and bound2:"r2 \<le> (real_of_int (sint NEG_INF))"
    by (auto simp add: repe.simps)    
  have res1:"max r1 r2 = (real_of_int (sint (wmax w1 w2)))"
    using bound1b bound2 NumNeg less_trans wmax.simps of_int_less_iff 
      word_sless_alt rw1 antisym_conv2 less_imp_le max_def
    by metis
  have res2:"wmax w1 w2 \<equiv>\<^sub>E (real_of_int (sint (wmax w1 w2)))"
    apply(rule repINT)
    using bound1a bound1b bound2 NumNeg leD leI less_trans n2 wmax.simps 
    by (auto simp add: word_sless_alt)
  show "wmax w1 w2 \<equiv>\<^sub>E max r1 r2"
    using res1 res2 by auto
next
  case NumNum
  from NumNum eq1 eq2
  have eq1:"r1 = (real_of_int (sint w1))"
   and eq2:"r2 = (real_of_int (sint w2))"
   and bound1a:"(real_of_int (sint w1)) < (real_of_int (sint POS_INF))"
   and bound1b:"(real_of_int (sint NEG_INF)) < (real_of_int (sint w1))"
   and bound2a:"(real_of_int (sint w2)) < (real_of_int (sint POS_INF))"
   and bound2b:"(real_of_int (sint NEG_INF)) < (real_of_int (sint w2))"
    by (auto simp add: repe.simps)    
  have res1:"max r1 r2 = (real_of_int (sint (wmax w1 w2)))"
    using eq1 eq2 bound1a bound1b bound2a bound2b
    by (simp add: max_def word_sless_alt)
  have res2:"wmax w1 w2 \<equiv>\<^sub>E (real_of_int (sint (wmax w1 w2)))"
    apply (rule repINT)
    using bound1a bound1b bound2a bound2b
    by (simp add: \<open>max r1 r2 =  (real_of_int (sint (wmax w1 w2)))\<close> eq2 min_less_iff_disj)+
  show "wmax w1 w2 \<equiv>\<^sub>E max r1 r2"
    using res1 res2 by auto
qed

lemma max_repU1:
  assumes "w1 \<equiv>\<^sub>U x"
  assumes "w2 \<equiv>\<^sub>U y"
  shows "wmax w1 w2 \<equiv>\<^sub>U x "
  using wmax_lemma assms repU_def
  by (meson le_max_iff_disj)
  
lemma max_repU2:
  assumes "w1 \<equiv>\<^sub>U y"
  assumes "w2 \<equiv>\<^sub>U x"
  shows "wmax w1 w2 \<equiv>\<^sub>U x"
  using wmax_lemma assms repU_def
  by (meson le_max_iff_disj)

text\<open>Product of w1 * w2 with bounds checking\<close>
fun wtimes :: "word \<Rightarrow> word \<Rightarrow> word"
where "wtimes w1 w2 =
 (if w1 = POS_INF \<and> w2 = POS_INF then POS_INF
  else if w1 = NEG_INF \<and> w2 = POS_INF then NEG_INF
  else if w1 = POS_INF \<and> w2 = NEG_INF then NEG_INF
  else if w1 = NEG_INF \<and> w2 = NEG_INF then POS_INF
  
  else if w1 = POS_INF \<and> w2 <s 0 then NEG_INF 
  else if w1 = POS_INF \<and> 0 <s w2 then POS_INF 
  else if w1 = POS_INF \<and> 0 = w2 then 0 
  else if w1 = NEG_INF \<and> w2 <s 0 then POS_INF 
  else if w1 = NEG_INF \<and> 0 <s w2 then NEG_INF 
  else if w1 = NEG_INF \<and> 0 = w2 then 0 
  
  else if w1 <s 0 \<and> w2 = POS_INF then NEG_INF 
  else if 0 <s w1 \<and> w2 = POS_INF then POS_INF 
  else if 0 = w1 \<and> w2 = POS_INF then 0
  else if w1 <s 0 \<and> w2 = NEG_INF then POS_INF 
  else if 0 <s w1 \<and> w2 = NEG_INF then NEG_INF 
  else if 0 = w1 \<and> w2 = NEG_INF then 0 
  
  else 
  (let prod::64 Word.word = (scast w1) * (scast w2) in
   if prod <=s (scast NEG_INF) then NEG_INF
   else if (scast POS_INF) <=s prod then POS_INF
   else (scast prod)))"


subsection \<open>Multiplication upper bound\<close>
text\<open>Product of 32-bit numbers fits in 64 bits\<close>
lemma times_upcast_lower:
  fixes x y::int
  assumes a1:"x \<ge> -2147483648"
  assumes a2:"y \<ge> -2147483648"
  assumes a3:"x \<le> 2147483648"
  assumes a4:"y \<le> 2147483648"
  shows "- 4611686018427387904 \<le>  x * y"
proof -
  let ?thesis = "- 4611686018427387904 \<le> x * y"
  have is_neg:"- 4611686018427387904 < (0::int)" by auto
  have case1:"x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<ge> 0" and a6:"y \<ge> 0"
      have h1:"x * y \<ge> 0"
        using a5 a6 by (simp add: zero_le_mult_iff)
      then show ?thesis using is_neg by auto
    qed
  have case2:"x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis" 
    proof -
      assume a5:"x \<le> 0" and a6:"y \<ge> 0"
      have h1:"-2147483648 * (2147483648) \<le> x * 2147483648"
        using a1 a2 a3 a4 a5 a6 by linarith
      have h2:"-2147483648 \<le> y" using a6 by auto
      have h3:"x * 2147483648 \<le> x * y" 
        using a1 a2 a3 a4 a5 a6 h2 
        using mult_left_mono_neg by blast
      show ?thesis using h1 h2 h3 by auto
    qed
  have case3:"x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<ge> 0" and a6:"y \<le> 0"
      have h1:"2147483648 * (-2147483648) \<le> 2147483648 * y"
        using a1 a2 a3 a4 a5 a6 by linarith
      have h2:"-2147483648 \<le> x" using a5 by auto
      have h3:"2147483648 * y \<le> x * y" 
        using a1 a2 a3 a4 a5 a6 h2 
        using mult_left_mono_neg mult_right_mono_neg by blast
      show ?thesis using h1 h2 h3 by auto
    qed
  have case4:"x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> ?thesis"
  proof -
      assume a5:"x \<le> 0" and a6:"y \<le> 0"
      have h1:"x * y \<ge> 0"
        using a5 a6 by (simp add: zero_le_mult_iff)
      then show ?thesis using is_neg by auto
    qed
  show ?thesis
    using case1 case2 case3 case4 by linarith
qed

text\<open>Product of 32-bit numbers fits in 64 bits\<close>
lemma times_upcast_upper:
  fixes x y ::int
  assumes a1:"x \<ge> -2147483648"
  assumes a2:"y \<ge> -2147483648"
  assumes a3:"x \<le> 2147483648"
  assumes a4:"y \<le> 2147483648"
  shows "x * y \<le> 4611686018427387904" 
proof -
  let ?thesis = "x * y \<le> 4611686018427387904"
  have case1:"x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<ge> 0" and a6:"y \<ge> 0"
      have h1:"2147483648 * 2147483648 \<ge> x * 2147483648"
        using a1 a2 a3 a4 a5 a6 by linarith
      have h2:"x * 2147483648 \<ge> x * y" 
        using a1 a2 a3 a4 a5 a6 by (simp add: mult_mono)
      show ?thesis using h1 h2 by auto
    qed
  have case2:"x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<le> 0" and a6:"y \<ge> 0"
      have h1:"2147483648 * 2147483648 \<ge> (0::int)" by auto
      have h2:"0 \<ge> x * y"
        using a5 a6 mult_nonneg_nonpos2 by blast
      show ?thesis using h1 h2 by auto
    qed
  have case3:"x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<ge> 0" and a6:"y \<le> 0"
      have h1:"2147483648 * 2147483648 \<ge> (0::int)" by auto
      have h2:"0 \<ge> x * y"
        using a5 a6 mult_nonneg_nonpos by blast
      show ?thesis using h1 h2 by auto
    qed
  have case4:"x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> ?thesis"
    proof -
      assume a5:"x \<le> 0" and a6:"y \<le> 0"
      have h1:"-2147483648 * -2147483648 \<ge> x * -2147483648"
        using a1 a2 a3 a4 a5 a6 by linarith
      have h2:"x * -2147483648 \<ge> x * y" 
        using a1 a2 a3 a4 a5 a6 mult_left_mono_neg by blast
      show ?thesis using h1 h2 by auto
    qed
show "x * y \<le> 4611686018427387904"
  using case1 case2 case3 case4
  by linarith
qed
   
text\<open>Correctness of 32x32 bit multiplication\<close>

subsection \<open>Exact multiplication\<close>
lemma wtimes_exact:
assumes eq1:"w1 \<equiv>\<^sub>E r1"
assumes eq2:"w2 \<equiv>\<^sub>E r2"
shows "wtimes w1 w2 \<equiv>\<^sub>E r1 * r2"
proof -
  have POS_cast:"sint ((scast POS_INF)::64 Word.word) = sint POS_INF"
    apply(rule Word.sint_up_scast)
    unfolding Word.is_up by auto
  have POS_sint:"sint POS_INF = (2^31)-1"  by auto
  have w1_cast:"sint ((scast w1)::64 Word.word) = sint w1"
    apply(rule Word.sint_up_scast)
    unfolding Word.is_up by auto
  have w2_cast:"sint ((scast w2)::64 Word.word) = sint w2"
    apply(rule Word.sint_up_scast)
    unfolding Word.is_up by auto
  have NEG_cast:"sint ((scast NEG_INF)::64 Word.word) = sint NEG_INF"
    apply(rule Word.sint_up_scast)
    unfolding Word.is_up by auto
  have rangew1:"sint ((scast w1)::64 Word.word) \<in> {- (2 ^ 31).. (2^31)} " 
    using Word.word_sint.Rep[of "(w1)::32 Word.word"] sints32 len32 mem_Collect_eq POS_cast w1_cast 
    by auto
  have rangew2:"sint ((scast w2)::64 Word.word) \<in> {- (2 ^ 31).. (2^31)} " 
    using Word.word_sint.Rep[of "(w2)::32 Word.word"] sints32 len32 mem_Collect_eq POS_cast w2_cast 
    by auto
  show ?thesis
proof (cases rule: case_times_inf[of w1 w2])
  case PosPos then
  have a1: "PosInf \<le> r1"
  and  a2: "PosInf \<le> r2" 
    using "PosPos" eq1 eq2 repe.simps by (auto)
  have f3: "\<And>n e::real.  1 \<le> max ( (numeral n)) e"
    by (simp add: le_max_iff_disj)
  have "\<And>n e::real. 0 \<le> max ( (numeral n)) e"
    by (simp add: le_max_iff_disj)
  then have "r1 \<le> r1 * r2"
    using f3 "PosPos" eq1 eq2 repe.simps
    using eq1 eq2 by (auto simp add: repe.simps)
  then have "PosInf \<le> r1 * r2"
    using a1 by linarith
  then show ?thesis
    using "PosPos"  by(auto simp add: repe.simps)
next
  case NegPos
  from "NegPos" have notPos:"w1 \<noteq> POS_INF" unfolding POS_INF_def NEG_INF_def by auto
  have a1: "NegInf \<ge> r1"
    using eq1 "NegPos" by (auto simp add: repe.simps)
  have a2: "PosInf \<le> r2"
    using eq2 "NegPos" by (auto simp add: repe.simps)
  have f1: "real_of_int Numeral1 = 1"
    by simp
  have f3: "(real_of_int 3) \<le> - r1"
    using a1 by (auto)
  have f4:"0 \<le> r2"
    using f1 a2 by(auto)
  have f5: "r1 \<le>  - 1"
    using f3 by auto
  have fact:"r1 * r2 \<le> - r2"
    using f5 f4 mult_right_mono by fastforce
  show ?thesis
    using a1 a2 fact by (auto simp add: repe.simps "NegPos")
next
  case PosNeg
  have a1: "PosInf \<le> r1"
    using eq1 "PosNeg" by (auto simp add: repe.simps)
  then have h1:"r1 \<ge> 1"
    by (auto)
  have a2: " NegInf \<ge> r2"
    using eq2 "PosNeg" by (auto simp add: repe.simps)
  have f1: "\<not>  NegInf *  (- 1) \<le> 1"
    by (auto)
  have f2: "\<forall>e ea::real. (e *  (- 1) \<le> ea) = (ea *  (- 1) \<le> e)" by force
  then have f3: "\<not> 1 *  (- 1::real) \<le>  NegInf"
    using f1 by blast
  have f4: "r1 *  (- 1) \<le>  NegInf"
    using f2 a1 
    by(auto)
  have f5: "\<forall>e ea eb. (if (ea::real) \<le> eb then e \<le> eb else e \<le> ea) = (e \<le> ea \<or> e \<le> eb)"
    by force
  have " 0 *  (- 1::real) \<le> 1"
    by simp
  then have "r1 *  (- 1) \<le>  0"
    using f5 f4 f3 f2 by meson
  then have f6: "0 \<le> r1" by fastforce
  have "1 *  (- 1) \<le>  (- 1::real)"
    using f2 by force
  then have fact:"r2 \<le>  (- 1)"
    using f3 a2 by fastforce
  have rule:"\<And>c. c > 0 \<Longrightarrow> r1 \<ge> c \<and> r2 \<le> -1 \<Longrightarrow> r1 * r2 \<le> -c"
    apply auto
    by (metis (no_types, hide_lams) f5 mult_less_cancel_left_pos 
        mult_minus1_right neg_le_iff_le not_less)
  have "r1 * r2 \<le> NegInf"
    using "PosNeg" f6 fact rule[of PosInf] a1
    by(auto)
  then show ?thesis
    using "PosNeg" by (auto simp add: repe.simps)
next
  case NegNeg
  have a1: "(-2147483647) \<ge> r1"
    using eq1 "NegNeg" by (auto simp add: repe.simps)
  then have h1:"r1 \<le> -1"
    using max.bounded_iff max_def one_le_numeral
    by auto
  have a2: " (-2147483647) \<ge> r2"
    using eq2 "NegNeg" by (auto simp add: repe.simps)
  have f1: "\<forall>e ea eb. \<not> (e::real) \<le> ea \<or> \<not> 0 \<le> eb \<or> eb * e \<le> eb * ea"
    using mult_left_mono by metis
  have f2: "-  1 =  (- 1::real)"
    by force
  have f3: " 0 \<le>  (1::real)"
    by simp
  have f4: "\<forall>e ea eb. (ea::real) \<le> e \<or> \<not> ea \<le> eb \<or> \<not> eb \<le> e"
    by (meson less_le_trans not_le)
  have f5: " 0 \<le>  (2147483647::real)"
    by simp
  have f6: "-  (- 2147483647) =  (2147483647::real)"
    by force
  then have f7: "- ( (- 2147483647) * r1) =  (2147483647 * r1)"
    by (metis mult_minus_left)
  have f8: "- ( (- 2147483647) *  (- 1)) =  2147483647 *  (- 1::real)"
    by simp
  have " 2147483647 = -  1 *  (- 2147483647::real)"
    by simp
  then have f9: "r1 \<le>  (- 1) \<longrightarrow>  2147483647 \<le> r1 *  (- 2147483647)"
    using f8 f7 f5 f2 f1 by linarith
  have f10: "-  2147483647 =  (- 2147483647::real)"
    by fastforce
  have f11: "- (r2 *  1 * (r1 *  (- 1))) = r1 * r2"
    by (simp add: mult.commute)
  have f12: "r1 *  (- 1) = - (r1 *  1)"
    by simp
  have "r1 *  1 * ( (- 2147483647) *  1) =  (- 2147483647) * r1"
    by (simp add: mult.commute)
  then have f13: "r1 *  (- 1) * ( (- 2147483647) *  1) =  2147483647 * r1"
    using f12 f6 by (metis (no_types) mult_minus_left)
  have " 1 * r1 \<le>  1 *  (- 2147483647)"
    using a1 
    by (auto simp add: a1)
  then have " 2147483647 \<le> r1 *  (- 1)" by fastforce
  then have "0 \<le> r1 *  (- 1)"
    using f5 f4 by (metis)
  then have "r1 \<le>  (- 1) \<and> - (r1 *  2147483647) \<le> - (r2 *  1 * (r1 *  (- 1)))"
    by (metis a2 f11 h1 mult_left_mono_neg minus_mult_right mult_minus1_right neg_0_le_iff_le)
  then have "r1 \<le>  (- 1) \<and> r1 *  (- 2147483647) \<le> r2 * r1"
    using f11 f10 by (metis mult_minus_left mult.commute)
  then have fact:" 2147483647 \<le> r2 * r1"
    using f9 f4 by blast
  show ?thesis
    using a1 a2 h1 fact
    by (auto simp add: repe.simps "NegNeg" mult.commute)
next
  case PosLo
  from "PosLo"
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" by (auto)
  from eq1 "PosLo" 
  have upper:" (real_of_int (sint POS_INF)) \<le> r1 " 
    by (auto simp add: repe.simps)
  have lower1:"sint w2 < 0" using "PosLo" 
    apply (auto simp add: word_sless_def word_sle_def)   
    by (simp add: dual_order.order_iff_strict)
  then have lower2:"sint w2 \<le> -1" by auto
  from eq2 have rw2:"r2 =  (real_of_int (sint w2))" 
    using repe.simps "PosLo"  
    by (auto simp add: repe.simps)
  have f4: "r1 *  (- 1) \<le>  (- 2147483647)"
    using upper by (auto)
  have f5: "r2 \<le>  (- 1)"
    using lower2 rw2 by simp
  have "0 < r1"
    using upper by (auto) 
  have "\<forall>r. r < - 2147483647 \<or> \<not> r < r1 * - 1"
    using f4 less_le_trans by blast
  then have "r1 *  (real_of_int (sint w2)) \<le>  (- 2147483647)"
    using f5 f4 upper lower2 rw2 mult_left_mono
    by (metis \<open>0 < r1\<close> dual_order.order_iff_strict f5 mult_left_mono rw2)
  then have "r1 * r2 \<le> real_of_int (sint NEG_INF)" 
    using upper lower2  rw2 
    by (auto)
  then show ?thesis
    using "PosLo" by (auto simp add: repe.simps)
next
  case PosHi
  from "PosHi"
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" 
    by (auto)
  from eq1 "PosHi" 
  have upper:"(real_of_int (sint POS_INF)) \<le> r1 " 
    by (auto simp add: repe.simps)
  have lower1:"sint w2 > 0" using "PosHi" 
    apply (auto simp add: word_sless_def word_sle_def)   
    by (simp add: dual_order.order_iff_strict)
  then have lower2:"sint w2 \<ge> 1" by auto
  from eq2 have rw2:"r2 =  (real_of_int (sint w2))" 
    using repe.simps "PosHi"
    by (auto) 
  have "0 \<le> r1" using upper by (auto)
  then have "r1 \<le> r1 * r2"
    using rw2 lower2 by (metis (no_types)  mult_left_mono mult.right_neutral of_int_1_le_iff)
  have "PosInf \<le> r1 * r2"
      using upper lower2 rw2 
      apply (auto)
      using \<open>0 \<le> r1\<close> mult_mono mult_numeral_1_right numeral_One of_int_1_le_iff zero_le_one
      by metis
  then show ?thesis
  using "PosHi" by (auto simp add: repe.simps)
next
  case PosZero
  from "PosZero"
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF"
    by (auto)
  from eq1 "PosZero"
  have upper:" (real_of_int (sint POS_INF)) \<le> r1 " 
    by (auto simp add: repe.simps)
  have lower1:"sint w2 = 0" using "PosZero" 
    by (auto simp add: word_sless_def word_sle_def)   
  from eq2 have rw2:"r2 =  (real_of_int (sint w2))" 
    using repe.simps "PosZero" 
    by auto 
  have "0 = r1 * r2"
    using "PosZero" rw2 by auto
  then show ?thesis
    using "PosZero" by (auto simp add: repe.simps)
next
  case NegHi
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" 
    using "NegHi" by (auto)
  from eq1 "NegHi" 
  have upper:"(real_of_int (sint NEG_INF)) \<ge> r1 " 
    by (auto simp add: repe.simps)
  have low:"sint w2 > 0" using "NegHi"
    apply (auto simp add: word_sless_def word_sle_def)
    by (simp add: dual_order.order_iff_strict)
  then have lower1:"(real_of_int (sint w2)) > 0" by auto
  then have lower2:"(real_of_int (sint w2)) \<ge> 1"  
    using low
    by (simp add: int_le_real_less) 
  from eq1 have rw1:"r1 \<le> (real_of_int (sint w1))" 
    using repe.simps "NegHi" 
    by (simp add: upper)
  from eq2 have rw2:"r2 = (real_of_int (sint w2))" 
    using repe.simps "NegHi"
    by (auto)
  have mylem:"\<And>x y z::real. x \<le> -1 \<Longrightarrow> y \<ge> 1 \<Longrightarrow> z \<le> -1 \<Longrightarrow> x \<le> z \<Longrightarrow>  x * y \<le> z"
    proof -
    fix x y z::real
    assume a1:"x \<le> -1"
    assume a2:"y \<ge> 1"
    then have h1:"-1 \<ge> -y" by auto
    assume a3:"z \<le> -1"
    then have a4:"z < 0"  by auto
    from a4 have h2:"-z > 0"  using leD leI by auto
    from a3 have h5:"-z \<ge> 1"  by (simp add: leD leI)
    assume a5:"x \<le> z"
    then have h6:"-x \<ge> -z" by auto
    have h3:"-x * -z = x * z" by auto
    show "x * y \<le> z"
      using a1 a2 a3 a5 a4 h1 h2 h3 h6 h5 a5 dual_order.trans leD mult.right_neutral
      by (metis dual_order.order_iff_strict mult_less_cancel_left2)
    qed
  have prereqs:"r1 \<le> - 1" "1 
      \<le> (real_of_int (sint w2))" " (- 2147483647::real) \<le> - 1 " "r1 \<le> (-2147483647)"
    using rw1 rw2 "NegHi" lower2 by (auto simp add: word_sless_def word_sle_def)
  have "r1 * r2 \<le> real_of_int (sint NEG_INF)"
    using upper lower1 lower2 rw1 rw2 
    apply (auto simp add: word_sless_def word_sle_def)
    using mylem[of  "r1" " (real_of_int (sint w2))" " (- 2147483647)"] prereqs
    by auto
  then show ?thesis
    using "NegHi" by (auto simp add: repe.simps)
next
  case NegLo
  from "NegLo"
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" 
    by (auto)
  from eq1 "NegLo" 
  have upper:"(real_of_int (sint NEG_INF)) \<ge> r1" 
  by (auto simp add: repe.simps)
  have low:"sint w2 < 0" using "NegLo"
    by (auto simp add: word_sless_def word_sle_def dual_order.order_iff_strict)
  then have lower1:"(real_of_int (sint w2)) < 0" by auto
  then have lower2:"(real_of_int (sint w2)) \<le> -1"  using low
  by (simp add: int_le_real_less) 
  from eq1 have rw1:"r1 \<le>  (real_of_int (sint w1))" 
    using repe.simps "NegLo"
    by (simp add: upper)
  from eq2 have rw2:"r2 =  (real_of_int (sint w2))" 
    using repe.simps "NegLo"
    by (auto)
  have hom:"(- 2147483647) = -(2147483647::real)" by auto
  have mylem:"\<And>x y z::real. y < 0 \<Longrightarrow>   x \<le> y \<Longrightarrow> z \<le> -1 \<Longrightarrow> -y \<le> x * z"
    proof -
    fix x y z::real
    assume a1:"y < 0"
    assume a2:"x \<le> y"
    then have h1:"-x \<ge> -y" by auto
    assume a3:"z \<le> -1"
    then have a4:"z < 0" 
      by auto
    from a4 have h2:"-z > 0" using leD leI by auto
    from a3 have h5:"-z \<ge> 1" by (simp add: leD leI)
    have h4:"-x * -z \<ge> -y"
      using  a1 a2 a3 a4 h1 h2 h5 dual_order.trans mult.right_neutral
      by (metis mult.commute neg_0_less_iff_less real_mult_le_cancel_iff1)
    have h3:"-x * -z = x * z" by auto
    show "- y \<le> x * z "
      using a1 a2 a3 a4 h1 h2 h3 h4 h5 
      by simp
    qed
  have prereqs:"- 2147483647 < (0::real)" " r1 \<le> - 2147483647" " (real_of_int (sint w2)) \<le> - 1"
    using rw1 rw2 "NegLo" by (auto simp add: word_sless_def word_sle_def lower2)
  have "2147483647 \<le> r1 * r2" 
    using upper lower1 lower2 rw1 rw2 prereqs
      mylem[of "-2147483647" "r1" "(real_of_int (sint w2))"] 
    by (auto simp add: word_sless_def word_sle_def)
  then show ?thesis
    using "NegLo" by (auto simp add: repe.simps)
next
  case NegZero
  from "NegZero"
  have w2NotPinf:"w2 \<noteq> POS_INF" and w2NotNinf:"w2 \<noteq> NEG_INF" by (auto)
  from eq2 "NegZero" 
  have "r2 = 0" 
    using repe.simps "NegZero"
    by (auto)
  then show ?thesis
    using "NegZero" by (auto simp add: repe.simps)
next
  case LoPos
  from "LoPos"
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" 
    by (auto)
  from eq2 "LoPos" 
  have upper:"(real_of_int (sint POS_INF)) \<le> r2 " 
    by (auto simp add: repe.simps)
  have lower1:"sint w1 < 0" using "LoPos"
    apply (auto simp add: word_sless_def word_sle_def)   
    by (simp add: dual_order.order_iff_strict)
  then have lower2:"sint w1 \<le> -1" by auto
  from eq1 have rw1:"r1 = (real_of_int (sint w1))" 
    using repe.simps "LoPos" by (auto simp add: repe.simps)
  have f4: "r2 * (- 1) \<le> (- 2147483647)"
    using upper by(auto)
  have f5: "r1 \<le> (- 1)"
    using lower2 rw1 by simp
  have "0 < r2"
    using upper by(auto)
  then have "r2 * r1 \<le> r2 * (- 1)"
    by (metis dual_order.order_iff_strict mult_right_mono f5  mult.commute)
  then have "r2 * r1 \<le> (- 2147483647)"
    by (meson f4 less_le_trans not_le)
  then have "(real_of_int (sint w1)) * r2 \<le> (- 2147483647)"
    using f5 f4 rw1 less_le_trans not_le mult.commute rw1 
    by (auto simp add: mult.commute)
  then have "r1 * r2 \<le> NegInf"
    using rw1
    by (auto)
  then show ?thesis
    using "LoPos" by (auto simp: repe.simps)
next
  case HiPos
  from "HiPos"
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" 
    by (auto)
  from eq2 "HiPos"
  have upper:"(real_of_int (sint POS_INF)) \<le> r2 " 
    by (auto simp add: repe.simps)
  have lower1:"sint w1 > 0" using "HiPos"
    by (auto simp add: word_sless_def word_sle_def dual_order.order_iff_strict)
  then have lower2:"sint w1 \<ge> 1" by auto
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" 
    using "HiPos" 
    by (auto simp add: repe.simps)
  have "0 \<le> r2"
    using upper by(auto)
  then have "r2 \<le> r2 * r1"
    using lower2 rw2 by (metis (no_types) mult_left_mono mult.right_neutral of_int_1_le_iff)
  have "2147483647 \<le> r1 * r2"
    using upper lower2  rw2 
    by (auto simp add: word_sless_def word_sle_def order_trans)
  then show ?thesis
    using "HiPos" by (auto simp add: repe.simps)
next
  case ZeroPos
  from "ZeroPos"
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF"
    by (auto)
  from eq2 "ZeroPos" 
  have upper:" (real_of_int (sint POS_INF)) \<le> r2 " 
    by (auto simp add: repe.simps)
  have lower1:"sint w1 = 0" using "ZeroPos" 
    by (auto simp add: word_sless_def word_sle_def)   
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" 
    using repe.simps "ZeroPos" 
    by (auto)
  have "r1 = 0" using lower1 rw2 by auto
  then show ?thesis
    using "ZeroPos" by (auto simp add: repe.simps)
next 
  case ZeroNeg
  from "ZeroNeg" 
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF" 
    by (auto)
  from eq2 "ZeroNeg" 
  have upper:"(real_of_int (sint NEG_INF)) \<ge> r2 " 
    by (auto simp add: repe.simps)
  have lower1:"sint w1 = 0" using "ZeroNeg" 
    by (auto simp add: word_sless_def word_sle_def)   
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" 
    using repe.simps "ZeroNeg" 
    by (auto)
  have "r1 = 0" using lower1 rw2 by auto
  then show ?thesis
    using "ZeroNeg" by (auto simp add: repe.simps)
next
  case LoNeg
  from "LoNeg"
  have w2NotPinf:"w1 \<noteq> POS_INF" and w2NotNinf:"w1 \<noteq> NEG_INF"
    by (auto)
  from eq2 "LoNeg" 
  have upper:" (real_of_int (sint NEG_INF)) \<ge> r2 " 
    by (auto simp add: repe.simps)
  have low:"sint w1 < 0" using "LoNeg" 
    apply (auto simp add: word_sless_def word_sle_def)
    by (simp add: dual_order.order_iff_strict)
  then have lower1:"(real_of_int (sint w1)) < 0" by auto
  then have lower2:"(real_of_int (sint w1)) \<le> -1"  using low
    by (simp add:  int_le_real_less) 
  from eq1 have rw1:"r2 \<le>  (real_of_int (sint w2))" 
    using "LoNeg" upper by auto
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" 
    using "LoNeg" by (auto simp add: upper repe.simps)
  have hom:"(- 2147483647::real) = -(2147483647)" by auto
  have mylem:"\<And>x y z::real. y < 0 \<Longrightarrow>   x \<le> y \<Longrightarrow> z \<le> -1 \<Longrightarrow> -y \<le> x * z"
    proof -
    fix x y z::real
    assume a1:"y < 0"
    assume a2:"x \<le> y"
    then have h1:"-x \<ge> -y" by auto
    assume a3:"z \<le> -1"
    then have a4:"z < 0" by auto
    from a4 have h2:"-z > 0" 
      using leD leI by auto
    from a3 have h5:"-z \<ge> 1" 
      by (simp add:  leD leI)
    have h4:"-x * -z \<ge> -y"
      using  a1 a2 a3 a4 h1 h2 h5 dual_order.trans mult_left_mono mult.right_neutral mult.commute
      by (metis dual_order.order_iff_strict mult_minus_right mult_zero_right neg_le_iff_le)
    have h3:"-x * -z = x * z" by auto
    show "- y \<le> x * z "
      using a1 a2 a3 a4 h1 h2 h3 h4 h5 
      by simp
    qed
  have prereqs:"- 2147483647 < (0::real)" " r2 \<le> - 2147483647" " (real_of_int (sint w1)) \<le> - 1"
    using rw1 rw2 "LoNeg" lower2 by (auto simp add: word_sless_def word_sle_def lower2)
  have "2147483647 \<le> r1 * r2"
    using upper lower1 lower2 rw1 rw2 mylem[of "-2147483647" "r2" 
        "(real_of_int (sint w1))"] prereqs
    by (auto simp add:word_sless_def word_sle_def mult.commute)
  then show ?thesis
    using "LoNeg" by (auto simp add: repe.simps)
next
  case HiNeg
  from HiNeg
  have w1NotPinf:"w1 \<noteq> POS_INF" and w1NotNinf:"w1 \<noteq> NEG_INF"
    by (auto)
  have upper:" (real_of_int (sint NEG_INF)) \<ge> r2 " 
    using HiNeg eq2
    by (auto simp add: repe.simps )
  have low:"sint w1 > 0" using HiNeg 
    apply (auto simp add: word_sless_def word_sle_def)
    by (simp add: dual_order.order_iff_strict)
  then have lower1:"(real_of_int (sint w1)) > 0" by auto
  then have lower2:"(real_of_int (sint w1)) \<ge> 1"  using low
  by (simp add: int_le_real_less) 
  from eq2 have rw1:"r2 \<le>  (real_of_int (sint w2))" 
    using repe.simps HiNeg by (simp add: upper)
  from eq1 have rw2:"r1 =  (real_of_int (sint w1))" 
    using repe.simps HiNeg  
    by (auto)
  have mylem:"\<And>x y z::real. x \<le> -1 \<Longrightarrow> y \<ge> 1 \<Longrightarrow> z \<le> -1 \<Longrightarrow> x \<le> z \<Longrightarrow>  x * y \<le> z"
    proof -
      fix x y z::real
      assume a1:"x \<le> -1"
      assume a2:"y \<ge> 1"
      then have h1:"-1 \<ge> -y" by auto
      assume a3:"z \<le> -1"
      then have a4:"z < 0" by auto
      from a4 have h2:"-z > 0" 
        using  leD leI by auto
      from a3 have h5:"-z \<ge> 1" 
        by (simp add:  leD leI)
      assume a5:"x \<le> z"
      then have h6:"-x \<ge> -z" by auto
      have h3:"-x * -z = x * z" by auto
      show "x * y \<le> z"
        using a1 a2 a3 a4 h1 h2 h3 h6 h5 a5 dual_order.trans less_eq_real_def
        by (metis mult_less_cancel_left1 not_le)
    qed
  have prereqs:"r2 \<le> - 1" "1 \<le> (real_of_int (sint w1))" 
               " (- 2147483647) \<le> - (1::real )" "r2 \<le>  (- 2147483647)"
    using rw1 rw2 HiNeg lower2 by (auto simp add: word_sless_def word_sle_def)
  have "r1 * r2 \<le> - 2147483647"
    using upper lower1 lower2 rw1 rw2 
    apply (auto simp add: word_sless_def word_sle_def)
    using mylem[of "r2" "(real_of_int (sint w1))" " (- 2147483647)"] prereqs
    by (auto simp add: mult.commute)
  then show ?thesis
    using HiNeg by(auto simp add: repe.simps)
next
  case AllFinite
  let ?prod = "(((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))"
  consider 
      (ProdNeg) "?prod <=s ((scast NEG_INF)::64 Word.word)" 
    | (ProdPos) "(((scast POS_INF)::64 Word.word) <=s ?prod)"
    | (ProdFin) "\<not>(?prod <=s ((scast NEG_INF)::64 Word.word)) 
              \<and>  \<not>((scast POS_INF)::64 Word.word) <=s ?prod"
    by (auto)
  then show ?thesis
  proof (cases)
    case ProdNeg
    have bigLeq:"(4611686018427387904::real) \<le> 9223372036854775807" by auto
    have set_cast:"\<And>x::int. (x \<in> {-(2^31)..2^31}) = ( (real_of_int x) \<in> {-(2^31)..2^31})"
      by auto
    have eq3:"sint(((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)) = 
     sint ((scast w1)::64 Word.word) * sint ((scast w2)::64 Word.word)"
     apply(rule Word_Lemmas.signed_arith_sint(4))
     using rangew1 rangew2 w1_cast w2_cast 
     using Word.word_size[of "((scast w1)::64 Word.word)"] 
     using Word.word_size[of "((scast w2)::64 Word.word)"]
     using times_upcast_upper[of "sint w1" "sint w2"]
     using times_upcast_lower[of "sint w1" "sint w2"] 
     by auto
    assume "?prod <=s ((scast NEG_INF)::64 Word.word)"
    then have sint_leq:"sint ?prod \<le> sint ((scast NEG_INF)::64 Word.word)"
      using word_sle_def by blast
    have neqs:"w1 \<noteq> POS_INF" " w1 \<noteq> NEG_INF" "w2 \<noteq> POS_INF" "w2 \<noteq> NEG_INF"
      using AllFinite word_sless_def signed.not_less_iff_gr_or_eq by force+
    from eq1 have rw1:"r1 = (real_of_int (sint w1))" using neqs by (auto simp add: repe.simps)
    from eq2 have rw2:"r2 = (real_of_int (sint w2))" using neqs by (auto simp add: repe.simps)
    show ?thesis
      using AllFinite ProdNeg  w1_cast w2_cast rw1 rw2 sint_leq  
      apply (auto simp add: repe.simps)
      by (metis (no_types, hide_lams) eq3 of_int_le_iff of_int_minus of_int_mult of_int_numeral) 
  next
    case ProdPos
    have bigLeq:"(4611686018427387904::real) \<le> 9223372036854775807" by auto
    have set_cast:"\<And>x::int. (x \<in> {-(2^31)..2^31}) = ( (real_of_int x) \<in> {-(2^31)..2^31})"
      by auto
    have eq3:"sint(((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)) = 
      sint ((scast w1)::64 Word.word) * sint ((scast w2)::64 Word.word)"
      apply(rule Word_Lemmas.signed_arith_sint(4))
      using rangew1 rangew2 POS_cast POS_sint w1_cast w2_cast
      using Word.word_size[of "((scast w1)::64 Word.word)"] 
      using Word.word_size[of "((scast w2)::64 Word.word)"]
      using times_upcast_upper[of "sint w1" "sint w2"]
      using times_upcast_lower[of "sint w1" "sint w2"] 
      by auto
    assume cast:"((scast POS_INF)::64 Word.word) <=s ?prod"
    then have sint_leq:"sint ((scast POS_INF)::64 Word.word) \<le> sint ?prod"
      using word_sle_def by blast
    have neqs:"w1 \<noteq> POS_INF" " w1 \<noteq> NEG_INF" "w2 \<noteq> POS_INF" "w2 \<noteq> NEG_INF"
      using AllFinite word_sless_def signed.not_less_iff_gr_or_eq by force+
    from eq1 have rw1:"r1 =  (real_of_int (sint w1))" 
      using repe.simps AllFinite neqs by auto
    from eq2 have rw2:"r2 = (real_of_int (sint w2))" 
      using repe.simps AllFinite neqs by auto
    have prodHi:"r1 * r2 \<ge> PosInf"
      using w1_cast w2_cast rw1 rw2 sint_leq apply(auto)
      by (metis (no_types, hide_lams) eq3 of_int_le_iff of_int_mult of_int_numeral)
    have infs:"SCAST(32 \<rightarrow> 64) NEG_INF <s SCAST(32 \<rightarrow> 64) POS_INF"
      by (auto)
    have casted:"SCAST(32 \<rightarrow> 64) POS_INF <=s SCAST(32 \<rightarrow> 64) w1 * SCAST(32 \<rightarrow> 64) w2"
      using cast by auto
    have almostContra:"SCAST(32 \<rightarrow> 64) NEG_INF <s SCAST(32 \<rightarrow> 64) w1 * SCAST(32 \<rightarrow> 64) w2"
      using infs cast  signed.order.strict_trans2 by blast
    have contra:"\<not>(SCAST(32 \<rightarrow> 64) w1 * SCAST(32 \<rightarrow> 64) w2 <=s SCAST(32 \<rightarrow> 64) NEG_INF)"
      using eq3 almostContra by auto
    have wtimesCase:"wtimes w1 w2 = POS_INF"
      using neqs ProdPos almostContra wtimes.simps AllFinite ProdPos
      by (auto simp add: repe.simps Let_def)
    show ?thesis
      using prodHi
      apply(simp only: repe.simps)      
      apply(rule disjI1)
      apply(rule exI[where x= "r1*r2"])
      apply(rule conjI)
       apply(rule wtimesCase)
      using prodHi by auto
  next
    case ProdFin
    have bigLeq:"(4611686018427387904::real) \<le> 9223372036854775807" by auto
    have set_cast:"\<And>x::int. (x \<in> {-(2^31)..2^31}) = ( (real_of_int x) \<in> {-(2^31)..2^31})"
      by auto
    have eq3:"sint(((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)) = 
      sint ((scast w1)::64 Word.word) * sint ((scast w2)::64 Word.word)"
      apply(rule Word_Lemmas.signed_arith_sint(4))
      using rangew1 rangew2 POS_cast POS_sint w1_cast w2_cast 
      using Word.word_size[of "((scast w1)::64 Word.word)"] 
      using Word.word_size[of "((scast w2)::64 Word.word)"]
      using times_upcast_upper[of "sint w1" "sint w2"]
      using times_upcast_lower[of "sint w1" "sint w2"] 
      by auto
    from ProdFin have a1:"\<not>(?prod <=s ((scast NEG_INF)::64 Word.word))"
      by auto
    then have sintGe:"sint (?prod) > sint (((scast NEG_INF)::64 Word.word))"
      using word_sle_def dual_order.order_iff_strict signed.linear 
      by fastforce
    from ProdFin have a2:"\<not>((scast POS_INF)::64 Word.word) <=s ?prod"
      by auto
    then have sintLe:"sint (((scast POS_INF)::64 Word.word)) > sint (?prod)"
      using word_sle_def dual_order.order_iff_strict signed.linear 
      by fastforce
    have neqs:"w1 \<noteq> POS_INF" " w1 \<noteq> NEG_INF" "w2 \<noteq> POS_INF" "w2 \<noteq> NEG_INF"
      using AllFinite word_sless_def signed.not_less_iff_gr_or_eq by force+
    from eq1 have rw1:"r1 =  (real_of_int (sint w1))" using neqs by(auto simp add: repe.simps)
    from eq2 have rw2:"r2 =  (real_of_int (sint w2))" using neqs by(auto simp add: repe.simps)
    from rw1 rw2 have "r1 * r2 =  (real_of_int ((sint w1) * (sint w2)))"
      by simp
    have rightSize:"sint (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))
      \<in> sints (len_of TYPE(32))"
      using sintLe sintGe sints32 by (simp) 
    have downcast:"sint ((scast (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word)))::word)
                 = sint (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))"
      using scast_down_range[OF rightSize]
      by auto
    then have res_eq:"r1 * r2 
      = real_of_int(sint((scast (((scast w1)::64 Word.word)*((scast w2)::64 Word.word)))::word))"
      using rw1 rw2 eq3 POS_cast POS_sint w1_cast w2_cast downcast 
        \<open>r1 * r2 =  (real_of_int (sint w1 * sint w2))\<close> 
      by (auto)
    have res_up:"sint (scast (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))::word) 
               < sint POS_INF"
      using rw1 rw2 eq3 POS_cast POS_sint w1_cast w2_cast downcast
        \<open>r1 * r2 = (real_of_int (sint w1 * sint w2))\<close> 
        \<open>sint (scast w1 * scast w2) < sint (scast POS_INF)\<close> 
          of_int_eq_iff res_eq 
      by presburger
    have res_lo:"sint NEG_INF 
               < sint (scast (((scast w1)::64 Word.word) * ((scast w2)::64 Word.word))::word)"
      using rw1 rw2 eq3 POS_cast POS_sint w1_cast w2_cast NEG_cast downcast
        \<open>r1 * r2 =  (real_of_int (sint w1 * sint w2))\<close> 
        \<open>sint (scast NEG_INF) < sint (scast w1 * scast w2)\<close> 
        of_int_eq_iff res_eq 
      by presburger
    have "scast ?prod \<equiv>\<^sub>E (r1 * r2)"
      using res_eq res_up res_lo 
      by (auto simp add: rep_simps)
    then show ?thesis 
      using AllFinite ProdFin by(auto)
  qed
qed
qed

subsection \<open>Multiplication upper bound\<close>
text\<open>Upper bound of multiplication from upper and lower bounds\<close>
fun tu :: "word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word"
where "tu w1l w1u w2l w2u = 
 wmax (wmax (wtimes w1l w2l) (wtimes w1u w2l))
      (wmax (wtimes w1l w2u) (wtimes w1u w2u))"

lemma tu_lemma:
  assumes u1:"u\<^sub>1 \<equiv>\<^sub>U (r1::real)"
  assumes u2:"u\<^sub>2 \<equiv>\<^sub>U (r2::real)"
  assumes l1:"l\<^sub>1 \<equiv>\<^sub>L (r1::real)"
  assumes l2:"l\<^sub>2 \<equiv>\<^sub>L (r2::real)"
  shows "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U (r1 * r2)"
proof -
  obtain rl1 rl2 ru1 ru2 :: real 
  where gru1:"ru1 \<ge> r1" and gru2:"ru2 \<ge> r2" and grl1:"rl1 \<le> r1" and grl2:"rl2 \<le> r2" 
  and eru1:"u\<^sub>1 \<equiv>\<^sub>E ru1" and eru2:"u\<^sub>2 \<equiv>\<^sub>E ru2" and erl1:"l\<^sub>1 \<equiv>\<^sub>E rl1" and erl2:"l\<^sub>2 \<equiv>\<^sub>E rl2"
  using u1 u2 l1 l2 unfolding repU_def repL_def by auto
  have timesuu:"wtimes u\<^sub>1 u\<^sub>2 \<equiv>\<^sub>E ru1 * ru2"
    using wtimes_exact[OF eru1 eru2] by auto
  have timesul:"wtimes u\<^sub>1 l\<^sub>2 \<equiv>\<^sub>E ru1 * rl2"
    using wtimes_exact[OF eru1 erl2] by auto
  have timeslu:"wtimes l\<^sub>1 u\<^sub>2 \<equiv>\<^sub>E rl1 * ru2"
    using wtimes_exact[OF erl1 eru2] by auto
  have timesll:"wtimes l\<^sub>1 l\<^sub>2 \<equiv>\<^sub>E rl1 * rl2"
    using wtimes_exact[OF erl1 erl2] by auto
  have maxt12:"wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>E max (rl1 * rl2) (ru1 * rl2)"
    by (rule  wmax_lemma[OF timesll timesul])
  have maxt34:"wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>E max (rl1 * ru2) (ru1 * ru2)"
    by (rule  wmax_lemma[OF timeslu timesuu])
  have bigMax:"wmax (wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>E max (max (rl1 * rl2) (ru1 * rl2)) (max (rl1 * ru2) (ru1 * ru2))"
    by (rule wmax_lemma[OF maxt12 maxt34])
  obtain maxt12val :: real 
    where maxU12:"wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>U max (rl1 * rl2) (ru1 * rl2)"
  using maxt12 unfolding repU_def by blast
  obtain maxt34val :: real 
    where maxU34:"wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>U max (rl1 * ru2) (ru1 * ru2)"
  using maxt34 unfolding repU_def by blast
  obtain bigMaxU:"wmax (wmax (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmax (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>U max (max (rl1 * rl2) (ru1 * rl2)) (max (rl1 * ru2) (ru1 * ru2))"
  using bigMax unfolding repU_def by blast
  have ivl1:"rl1 \<le> ru1" using grl1 gru1 by auto
  have ivl2:"rl2 \<le> ru2" using grl2 gru2 by auto
  let ?thesis = "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r1 * r2"
  show ?thesis
  using ivl1 ivl2
  proof(cases rule: case_ivl_zero)
    case ZeroZero
    assume "rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    then have geq1:"ru1 \<ge> 0" and geq2:"ru2 \<ge> 0" by auto
    consider "r1 \<ge> 0 \<and> r2 \<ge> 0" | "r1 \<ge> 0 \<and> r2 \<le> 0" | "r1 \<le> 0 \<and> r2 \<ge> 0" | "r1 \<le> 0 \<and> r2 \<le> 0"
    using le_cases by auto
    then show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r1 * r2" 
    proof (cases)
      case 1
      have g1:"ru1 * ru2 \<ge> ru1 * r2" 
        using "1" geq1 geq2 grl2 gru2
        by (simp add: mult_left_mono)
      have g2:"ru1 * r2 \<ge> r1 * r2"
        using "1" geq1 geq2 grl1 grl2 gru1 gru2
        by (simp add: mult_right_mono)
      from g1 and g2
      have up:"ru1 * ru2 \<ge> r1 * r2"
        by auto
      show ?thesis
        using up eru1 eru2 erl1 erl2 repU_def timesuu tu.simps
          max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU]
        by (metis wmax.elims)
    next
      case 2
      have g1:"ru1 * ru2 \<ge> 0" 
        using "2" geq1 geq2 grl2 gru2 by (simp)
      have g2:"0 \<ge> r1 * r2"
        using "2" by (simp add: mult_le_0_iff)
        from g1 and g2
      have up:"ru1 * ru2 \<ge> r1 * r2" by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12]
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis  repU_def  tu.simps)
    next
      case 3
      have g1:"ru1 * ru2 \<ge> 0" 
        using "3" geq1 geq2  by simp
      have g2:"0 \<ge> r1 * r2"
        using "3" by (simp add: mult_le_0_iff)
      from g1 and g2
      have up:"ru1 * ru2 \<ge> r1 * r2" by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] repU_def tu.simps timesuu
        by (metis max.coboundedI1 max.commute maxt34)
    next
      case 4
      have g1:"rl1 * rl2 \<ge> rl1 * r2" 
        using "4" geq1 geq2 grl1 grl2 gru1 gru2
        using  \<open>rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2\<close> less_eq_real_def
          by (metis mult_left_mono_neg)
      have g2:"rl1 * r2 \<ge> r1 * r2"
        using "4" geq1 geq2 grl1 grl2 gru1 gru2 \<open>rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2\<close>  
          by (metis mult_left_mono_neg mult.commute)
      from g1 and g2
      have up:"rl1 * rl2 \<ge> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34
        by (metis max_repU1 repU_def timesll tu.simps)
      qed
  next
    case ZeroPos
    assume bounds:"rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> 0 \<le> rl2"
    have r2:"r2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    consider "r1 \<ge> 0" | "r1 \<le> 0" using le_cases by (auto)
    then show ?thesis
    proof (cases)
      case 1
      assume r1:"r1 \<ge> 0"
      have g1:"ru1 * ru2 \<ge> ru1 * r2" 
        using r1 r2 bounds grl1 grl2 gru1 gru2
        using mult_left_mono by blast
      have g2:"ru1 * r2 \<ge> r1 * r2"
        using r1 r2 bounds grl1 grl2 gru1 gru2
        using mult_right_mono by blast
      from g1 and g2
      have up:"ru1 * ru2 \<ge> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis repU_def tu.simps) 
    next
      case 2
      assume r1:"r1 \<le> 0"
      have g1:"ru1 * ru2 \<ge> 0" 
        using r1 r2 bounds grl1 grl2 gru1 gru2
        using mult_left_mono 
        by (simp add: mult_less_0_iff less_le_trans not_less)
      have g2:"0 \<ge> r1 * r2"
        using r1 r2 bounds grl1 grl2 gru1 gru2
        using mult_right_mono 
        by (simp add: mult_le_0_iff)
      from g1 and g2
      have up:"ru1 * ru2 \<ge> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis repU_def tu.simps) 
      qed 
  next
    case ZeroNeg
    assume bounds:"rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> ru2 \<le> 0"
    have r2:"r2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have case1:"r1 \<ge> 0 \<Longrightarrow> ?thesis" 
    proof -
      assume r1:"r1 \<ge> 0"
      have g1:"rl1 * rl2 \<ge> 0" 
        using r1 r2 bounds grl1 grl2 gru1 gru2 mult_less_0_iff less_le_trans not_less
        by metis
      have g2:"0 \<ge> r1 * r2"
        using r1 r2 bounds grl1 grl2 gru1 gru2
        using mult_right_mono 
        by (simp add: mult_le_0_iff)
      from g1 and g2
      have up:"rl1 * rl2 \<ge> r1 * r2"
        by auto
      show ?thesis 
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34
        by (metis max_repU2 max_repU1 repU_def timesll tu.simps)
    qed
    have case2:"r1 \<le> 0 \<Longrightarrow> ?thesis"
    proof -
      assume r1:"r1 \<le> 0"
      have g1:"rl1 * rl2 \<ge> rl1 * r2" 
        using r1 r2 bounds  grl1 grl2 gru1 gru2
        by (metis mult_left_mono_neg)
      have g2:"rl1 * r2 \<ge> r1 * r2"
        using r1 r2 bounds grl1 grl2 gru1 gru2 mult.commute
        by (metis mult_left_mono_neg)
      from g1 and g2
      have up:"rl1 * rl2 \<ge> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34 
        by (metis max_repU1 repU_def timesll tu.simps) 
    qed
    show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r1 * r2"
      using case1 case2 le_cases by blast
  next
    case PosZero
    assume bounds:"0 \<le> rl1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    have r1:"r1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    consider "r2 \<ge> 0" | "r2 \<le> 0" using le_cases by auto
    then show ?thesis
    proof (cases)
      case 1
      have g1:"ru1 * ru2 \<ge> ru1 * r2" 
        using "1" bounds grl1 grl2 gru1 gru2
        using mult_left_mono 
        using leD leI less_le_trans by metis
      have g2:"ru1 * r2 \<ge> r1 * r2"
        using "1" bounds grl1 grl2 gru1 gru2
        using mult_right_mono by blast
      from g1 and g2
      have up:"ru1 * ru2 \<ge> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
        by (metis repU_def tu.simps) 
    next
      case 2
        have g1:"ru1 * ru2 \<ge> 0" 
          using r1 bounds grl2 gru2 gru1 leD leI less_le_trans by auto
        have g2:"0 \<ge> r1 * r2"
          using r1 "2" 
          by (simp add: mult_le_0_iff)
        from g1 and g2
        have up:"ru1 * ru2 \<ge> r1 * r2"
          by auto
        show ?thesis
          using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
            max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.coboundedI1 max.commute maxt34
          by (metis repU_def  tu.simps)
      qed
  next
    case NegZero
    assume bounds:"ru1 \<le> 0 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    have r1:"r1 \<le> 0"  using bounds dual_order.trans gru1 by blast
    consider "r2 \<ge> 0" | "r2 \<le> 0" using le_cases by auto
    then show ?thesis
    proof (cases)
      case 1
      have g1:"ru1 * rl2 \<ge> 0" 
        using r1 "1" bounds grl1 grl2 gru1 gru2 mult_less_0_iff not_less
        by metis
      have g2:"0 \<ge> r1 * r2"
        using r1 "1" bounds grl1 grl2 gru1 gru2
        by (simp add: mult_le_0_iff)
      from g1 and g2
      have up:"ru1 * rl2 \<ge> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34
        by (metis max_repU1 repU_def timesul tu.simps) 
    next
      case 2
      have lower:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
      have g1:"rl1 * rl2 \<ge> rl1 * r2" 
        using r1 "2" bounds grl1 grl2 gru1 gru2 less_eq(1) less_le_trans not_less 
          mult_le_cancel_left
        by metis
      have g2:"rl1 * r2 \<ge> r1 * r2"
        using r1 "2" bounds grl1 grl2 gru1 gru2 mult.commute not_le lower mult_le_cancel_left
        by metis
      from g1 and g2
      have up:"rl1 * rl2 \<ge> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
          max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34
        by (metis max_repU1 repU_def timesll tu.simps)
    qed
  next
    case NegNeg
    assume bounds:"ru1 \<le> 0 \<and> ru2 \<le> 0"
    have r1:"r1 \<le> 0" using bounds dual_order.trans gru1 by blast
    have r2:"r2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have lower1:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
    have lower2:"rl2 \<le> 0" using bounds dual_order.trans grl2 r2 by blast
    have g1:"rl1 * rl2 \<ge> rl1 * r2" 
      using r1 r2 bounds  grl1 grl2 gru1 gru2 less_eq(1)  mult_le_cancel_left less_le_trans not_less
      by metis
    have g2:"rl1 * r2 \<ge> r1 * r2"
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult.commute not_le lower1 lower2 mult_le_cancel_left
      by metis
    from g1 and g2
    have up:"rl1 * rl2 \<ge> r1 * r2"
      by auto
    show ?thesis
      using up maxU12 maxU34 bigMaxU wmax.elims max_repU2 max_repU2[OF maxU12] 
        max_repU2[OF maxU34] max_repU2[OF bigMaxU] max.commute maxt34 
      by (metis max_repU1 repU_def timesll tu.simps)
  next
    case NegPos
    assume bounds:"ru1 \<le> 0 \<and> 0 \<le> rl2"
    have r1:"r1 \<le> 0" using bounds dual_order.trans gru1 by blast
    have r2:"r2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have lower1:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
    have lower2:"rl2 \<ge> 0" using bounds by auto
    have upper1:"ru1 \<le> 0" using bounds by auto 
    have upper2:"ru2 \<ge> 0" using bounds dual_order.trans gru2 r2 by blast
    have g1:"ru1 * rl2 \<ge> ru1 * r2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 not_less upper1 lower2 mult_le_cancel_left
      by metis
    have g2:"ru1 * r2 \<ge> r1 * r2"
      using r1 upper1 r2 mult_right_mono gru1 by metis
    from g1 and g2
    have up:"ru1 * rl2 \<ge> r1 * r2"
      by auto
    show ?thesis
      using up maxU12 maxU34 bigMaxU wmax.elims maxt34
        max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU]
      by (metis max_repU1 repU_def timesul tu.simps)
  next
    case PosNeg
    assume bounds:"0 \<le> rl1 \<and> ru2 \<le> 0"
    have r1:"r1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have r2:"r2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have lower1:"rl1 \<ge> 0" using bounds by auto
    have lower2:"rl2 \<le> 0" using dual_order.trans grl2 r2 by blast
    have upper1:"ru1 \<ge> 0" using dual_order.trans gru1 u1 r1 by blast  
    have upper2:"ru2 \<le> 0" using bounds by auto
    have g1:"rl1 * ru2 \<ge> rl1 * r2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 not_less upper2 lower1 mult_le_cancel_left 
      by metis
    have g2:"rl1 * r2 \<ge> r1 * r2"
      using r1 lower1 r2 not_less gru2 gru1 grl1 grl2
      by (metis mult_le_cancel_left mult.commute)
    from g1 and g2
    have up:"rl1 * ru2 \<ge> r1 * r2"
      by auto
    show "tu l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>U r1 * r2"
      using up maxU12 maxU34 bigMaxU wmax.elims max.coboundedI1 max.commute maxt34
        max_repU2[OF maxU12] max_repU2[OF maxU34] max_repU2[OF bigMaxU] 
      by (metis repU_def tu.simps)
  next
    case PosPos
    assume bounds:"0 \<le> rl1 \<and> 0 \<le> rl2"
    have r1:"r1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have r2:"r2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have lower1:"rl1 \<ge> 0" using bounds by auto
    have lower2:"rl2 \<ge> 0" using bounds by auto
    have upper1:"ru1 \<ge> 0" using dual_order.trans gru1 u1 r1 by blast  
    have upper2:"ru2 \<ge> 0" using dual_order.trans gru2 u2 r2 bounds by blast
    have g1:"ru1 * ru2 \<ge> ru1 * r2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult_left_mono leD leI less_le_trans by metis
    have g2:"ru1 * r2 \<ge> r1 * r2"
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult_right_mono by metis
    from g1 and g2
    have up:"ru1 * ru2 \<ge> r1 * r2"
      by auto
    show ?thesis
      using up maxU12 maxU34 bigMaxU wmax.elims max.coboundedI1 max.commute maxt34
        max_repU2[OF bigMaxU] max_repU2[OF maxU12] max_repU2[OF maxU34]
      by (metis repU_def tu.simps)
  qed
qed

subsection \<open>Minimum function\<close>
text\<open>Minimum of 2s-complement words\<close>
fun wmin :: "word \<Rightarrow> word \<Rightarrow> word"
where "wmin w1 w2 = 
  (if w1 <s w2 then w1 else w2)"
                                            
text\<open>Correctness of wmin\<close>
lemma wmin_lemma:
  assumes eq1:"w1 \<equiv>\<^sub>E (r1::real)"
  assumes eq2:"w2 \<equiv>\<^sub>E (r2::real)"
  shows "wmin w1 w2 \<equiv>\<^sub>E (min r1 r2)"
proof(cases rule: case_inf2[where ?w1.0=w1, where ?w2.0=w2])
  case PosPos
  assume p1:"w1 = POS_INF"   
     and p2:"w2 = POS_INF"
  then have bound1:"(real_of_int (sint POS_INF)) \<le> r1"
        and bound2:"(real_of_int (sint POS_INF)) \<le> r2"
    using eq1 eq2 by (auto simp add: rep_simps repe.simps)
  have eqInf:"wmin w1 w2 = POS_INF"
    using p1 p2 unfolding wmin.simps by auto
  have pos_eq:"POS_INF \<equiv>\<^sub>E min r1 r2"
    apply(rule repPOS_INF)
    using bound1 bound2 unfolding eq1 eq2 by auto
  show ?thesis
    using pos_eq eqInf by auto
next
  case PosNeg
  assume p1:"w1 = POS_INF"
  assume n2:"w2 = NEG_INF"
  obtain r ra :: real 
  where bound1:" (real_of_int (sint POS_INF)) \<le> r"
    and bound2:"ra \<le>  (real_of_int (sint NEG_INF))"
    and eq1:"r1 = r"
    and eq2:"r2 = ra"
    using p1 n2 eq1 eq2 by(auto simp add: rep_simps repe.simps)
  have eqNeg:"wmin w1 w2 = NEG_INF"
    unfolding eq1 eq2 wmin.simps p1 n2 word_sless_def word_sle_def
    by(auto) 
  have neg_eq:"NEG_INF \<equiv>\<^sub>E min r1 r2"
    apply(rule repNEG_INF)
    using bound1 bound2 eq1 eq2 by auto
  show "?thesis"
    using eqNeg neg_eq by auto
next
  case PosNum
  assume p1:"w1 = POS_INF"
  assume np2:"w2 \<noteq> POS_INF"
  assume nn2:"w2 \<noteq> NEG_INF"
  have eq2:"r2 = (real_of_int (sint w2))"
    and bound1:"(real_of_int (sint POS_INF)) \<le> r1"
    and bound2a:"(real_of_int (sint NEG_INF)) < (real_of_int (sint w2))"
    and bound2b:"(real_of_int (sint w2)) < (real_of_int (sint POS_INF))"
    using p1 np2 nn2 eq1 eq2 by(auto simp add: rep_simps repe.simps)
  have eqNeg:"min r1 r2 = sint w2"
    using p1
    by (metis bound1 bound2b dual_order.trans eq2 min_def not_less) 
  have neg_eq:"wmin w1 w2 \<equiv>\<^sub>E  (real_of_int (sint (wmin w1 w2)))"
    apply (rule repINT)
    using bound1 bound2a bound2b bound2b p1 unfolding eq1 eq2
    by (auto simp add: word_sless_alt)
  show "?thesis"
    using eqNeg neg_eq
    by (metis bound2b less_eq_real_def not_less of_int_less_iff p1 wmin.simps word_sless_alt)
next
  case NegPos
  assume n1:"w1 = NEG_INF"   
  assume p2:"w2 = POS_INF"
  have  bound1:"r1 \<le> (real_of_int (sint NEG_INF))"
    and bound2:"(real_of_int (sint POS_INF)) \<le> r2"
    using n1 p2 eq1 eq2 by(auto simp add: rep_simps repe.simps)    
  have eqNeg:"wmin w1 w2 = NEG_INF"
    unfolding eq1 eq2 wmin.simps n1 p2 word_sless_def word_sle_def
    by(auto)
  have neg_eq:"NEG_INF \<equiv>\<^sub>E min r1 r2"
    apply(rule repNEG_INF)
    using bound1 bound2 unfolding eq1 eq2 by auto
  show "wmin w1 w2 \<equiv>\<^sub>E min r1 r2"
    using eqNeg neg_eq by auto                      
next
  case NegNeg
  assume n1:"w1 = NEG_INF"                 
  assume n2:"w2 = NEG_INF" 
  have bound1:"r1 \<le>  (real_of_int (sint NEG_INF))"
   and bound2:"r2 \<le>  (real_of_int (sint NEG_INF))"
    using n1 n2 eq1 eq2 by(auto simp add: rep_simps repe.simps)    
  have eqNeg:"NEG_INF \<equiv>\<^sub>E min r1 r2"
    apply(rule repNEG_INF)
    using eq1 eq2 bound1 bound2 unfolding NEG_INF_def
    by (auto)
  have neg_eq:"wmin w1 w2 = NEG_INF"
    using n1 n2 unfolding NEG_INF_def wmin.simps by auto 
  show "wmin w1 w2 \<equiv>\<^sub>E min r1 r2"
    using eqNeg neg_eq by auto
next
  case NegNum
  assume n1:"w1 = NEG_INF" 
    and  nn2:"w2 \<noteq> NEG_INF"
    and  np2:"w2 \<noteq> POS_INF"
  have eq2:"r2 =  (real_of_int (sint w2))"
    and bound2a:"(real_of_int (sint w2)) <  (real_of_int (sint POS_INF))"
    and bound2b:"(real_of_int (sint NEG_INF)) <  (real_of_int (sint w2))"
    and bound1:"r1 \<le>  (real_of_int (sint NEG_INF))"
    using n1 nn2 np2 eq2 eq1 eq2 by (auto simp add: rep_simps repe.simps)  
  have eqNeg:"wmin w1 w2 = NEG_INF"
    using n1 assms(2) bound2a eq2 n1 repeInt_simps  
    by (auto simp add: word_sless_alt)
  have neg_eq:"NEG_INF \<equiv>\<^sub>E min r1 r2"
    apply(rule repNEG_INF)
    using bound1 bound2a bound2b eq1 min_le_iff_disj by blast
  show "wmin w1 w2 \<equiv>\<^sub>E min r1 r2"
    using eqNeg neg_eq by auto
next
  case NumPos
  assume p2:"w2 = POS_INF"
   and  nn1:"w1 \<noteq> NEG_INF"
   and  np1:"w1 \<noteq> POS_INF"
  have eq1:"r1 =  (real_of_int (sint w1))"
    and bound1a:" (real_of_int (sint w1)) <  (real_of_int (sint POS_INF))"
    and bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w1))"
    and bound2:" (real_of_int (sint POS_INF)) \<le> r2"
    using nn1 np1 p2 eq2 eq1 eq2 by (auto simp add: rep_simps repe.simps)  
  have res1:"wmin w1 w2 = w1"
    using p2 eq1 eq2  assms(1) bound1b p2 repeInt_simps  
    by (auto simp add: word_sless_alt)
  have res2:"min r1 r2 =  (real_of_int (sint w1))"
    using eq1 eq2 bound1a bound1b bound2 
    by (auto simp add: less_imp_le less_le_trans min_def)
  have res3:"wmin w1 w2 \<equiv>\<^sub>E  (real_of_int (sint (wmin w1 w2)))"
    apply(rule repINT)
    using p2 bound1a res1 bound1a bound1b bound2 
    by auto
  show "wmin w1 w2 \<equiv>\<^sub>E min r1 r2" 
    using res1 res2 res3 by auto
next
  case NumNeg
  assume nn1:"w1 \<noteq> NEG_INF"
  assume np1:"w1 \<noteq> POS_INF"
  assume n2:"w2 = NEG_INF"
  have eq1:"r1 =  (real_of_int (sint w1))"
    and bound1a:" (real_of_int (sint w1)) <  (real_of_int (sint POS_INF))"
    and bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w1))"
    and bound2:"r2 \<le>  (real_of_int (sint NEG_INF))"
    using nn1 np1 n2 eq2 eq1 eq2 by (auto simp add: rep_simps repe.simps)
  have res1:"wmin w1 w2 = NEG_INF"
    using n2 bound1b
    by (metis min.absorb_iff2 min_def n2 not_less of_int_less_iff wmin.simps word_sless_alt)
  have res2:"NEG_INF \<equiv>\<^sub>E min r1 r2"
    apply(rule repNEG_INF)
    using eq1 eq2 bound1a bound1b bound2 min_le_iff_disj by blast
  show "wmin w1 w2 \<equiv>\<^sub>E min r1 r2"
    using res1 res2 by auto
next
  case NumNum
  assume np1:"w1 \<noteq> POS_INF"
  assume nn1:"w1 \<noteq> NEG_INF"
  assume np2:"w2 \<noteq> POS_INF"
  assume nn2:"w2 \<noteq> NEG_INF"
  have eq1:"r1 =  (real_of_int (sint w1))"
  and  eq2:"r2 =  (real_of_int (sint w2))"
  and  bound1a:" (real_of_int (sint w1)) <  (real_of_int (sint POS_INF))"
  and  bound1b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w1))"
  and  bound2a:" (real_of_int (sint w2)) <  (real_of_int (sint POS_INF))"
  and  bound2b:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint w2))"
    using nn1 np1 nn2 np2 eq2 eq1 eq2 
    by (auto simp add: rep_simps repe.simps)
  have res1:"min r1 r2 =  (real_of_int (sint (wmin w1 w2)))"
    using eq1 eq2 bound1a bound1b bound2a bound2b 
    by (simp add: min_def word_sless_alt)
  have res2:"wmin w1 w2 \<equiv>\<^sub>E (real_of_int (sint (wmin w1 w2)))"
    apply (rule repINT)
    using bound1a bound1b bound2a bound2b
    by (simp add: \<open>min r1 r2 = (real_of_int (sint (wmin w1 w2)))\<close> eq2 min_less_iff_disj)+
  show "wmin w1 w2 \<equiv>\<^sub>E min r1 r2"
    using res1 res2 by auto
qed    
    
lemma min_repU1:
  assumes "w1 \<equiv>\<^sub>L x"
  assumes "w2 \<equiv>\<^sub>L y"
  shows "wmin w1 w2 \<equiv>\<^sub>L x "
  using wmin_lemma assms repL_def
  by (meson min_le_iff_disj)

lemma min_repU2:
  assumes "w1 \<equiv>\<^sub>L y"
  assumes "w2 \<equiv>\<^sub>L x"
  shows "wmin w1 w2 \<equiv>\<^sub>L x"
  using wmin_lemma assms repL_def
by (meson min_le_iff_disj)


subsection \<open>Multiplication lower bound\<close>
text\<open>Multiplication lower bound\<close>
fun tl :: "word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word \<Rightarrow> word"
where "tl w1l w1u w2l w2u =
  wmin (wmin (wtimes w1l w2l) (wtimes w1u w2l))
       (wmin (wtimes w1l w2u) (wtimes w1u w2u))"

text\<open>Correctness of multiplication lower bound\<close>
lemma tl_lemma:
  assumes u1:"u\<^sub>1 \<equiv>\<^sub>U (r1::real)"
  assumes u2:"u\<^sub>2 \<equiv>\<^sub>U (r2::real)"
  assumes l1:"l\<^sub>1 \<equiv>\<^sub>L (r1::real)"
  assumes l2:"l\<^sub>2 \<equiv>\<^sub>L (r2::real)"
  shows "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L (r1 * r2)"
proof -
  obtain rl1 rl2 ru1 ru2 :: real 
  where gru1:"ru1 \<ge> r1" and gru2:"ru2 \<ge> r2" and grl1:"rl1 \<le> r1" and grl2:"rl2 \<le> r2" 
  and eru1:"u\<^sub>1 \<equiv>\<^sub>E ru1" and eru2:"u\<^sub>2 \<equiv>\<^sub>E ru2" and erl1:"l\<^sub>1 \<equiv>\<^sub>E rl1" and erl2:"l\<^sub>2 \<equiv>\<^sub>E rl2"
  using u1 u2 l1 l2 unfolding repU_def repL_def by auto
  have timesuu:"wtimes u\<^sub>1 u\<^sub>2 \<equiv>\<^sub>E ru1 * ru2"
    using wtimes_exact[OF eru1 eru2] by auto
  have timesul:"wtimes u\<^sub>1 l\<^sub>2 \<equiv>\<^sub>E ru1 * rl2"
    using wtimes_exact[OF eru1 erl2] by auto
  have timeslu:"wtimes l\<^sub>1 u\<^sub>2 \<equiv>\<^sub>E rl1 * ru2"
    using wtimes_exact[OF erl1 eru2] by auto
  have timesll:"wtimes l\<^sub>1 l\<^sub>2 \<equiv>\<^sub>E rl1 * rl2"
    using wtimes_exact[OF erl1 erl2] by auto
  have maxt12:"wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>E min (rl1 * rl2) (ru1 * rl2)"
    by (rule  wmin_lemma[OF timesll timesul])
  have maxt34:"wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>E min (rl1 * ru2) (ru1 * ru2)"
    by (rule  wmin_lemma[OF timeslu timesuu])
  have bigMax:"wmin (wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>E min (min(rl1 * rl2) (ru1 * rl2)) (min (rl1 * ru2) (ru1 * ru2))"
    by (rule wmin_lemma[OF maxt12 maxt34])
  obtain maxt12val :: real 
    where maxU12:"wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2) \<equiv>\<^sub>L min (rl1 * rl2) (ru1 * rl2)"
  using maxt12 unfolding repL_def by blast
  obtain maxt34val :: real 
    where maxU34:"wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2) \<equiv>\<^sub>L min (rl1 * ru2) (ru1 * ru2)"
  using maxt34 unfolding repL_def by blast
  obtain bigMaxU:"wmin (wmin (wtimes l\<^sub>1 l\<^sub>2) (wtimes u\<^sub>1 l\<^sub>2)) (wmin (wtimes l\<^sub>1 u\<^sub>2) (wtimes u\<^sub>1 u\<^sub>2))
    \<equiv>\<^sub>L min (min (rl1 * rl2) (ru1 * rl2)) (min (rl1 * ru2) (ru1 * ru2))"
  using bigMax unfolding repL_def by blast
  have ivl1:"rl1 \<le> ru1" using grl1 gru1 by auto
  have ivl2:"rl2 \<le> ru2" using grl2 gru2 by auto
  let ?thesis = "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r1 * r2"
  show ?thesis
  using ivl1 ivl2
  proof(cases rule: case_ivl_zero)
    case ZeroZero        
    assume "rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    then have geq1:"ru1 \<ge> 0" and geq2:"ru2 \<ge> 0" 
    and geq3:"rl1 \<le> 0" and geq4:"rl2 \<le> 0" by auto
    consider "r1 \<ge> 0 \<and> r2 \<ge> 0" | "r1 \<le> 0 \<and> r2 \<ge> 0" | "r1 \<ge> 0 \<and> r2 \<le> 0" | "r1 \<le> 0 \<and> r2 \<le> 0"
      using le_cases by auto
    then show ?thesis
    proof (cases)
      case 1
      have g1:"rl1 * ru2 \<le> 0" 
        using "1" geq1 geq2 geq3 geq4 grl2 gru2 mult_le_0_iff by blast
      have g2:"0 \<le>  r1 * r2"
        using "1"  geq1 geq2 grl1 grl2 gru1 gru2
        by (simp)
      from g1 and g2
      have up:"rl1 * ru2 \<le> r1 * r2"
        by auto
      show ?thesis
        using up eru1 eru2 erl1 erl2 min_repU1 min_repU2 
          repL_def repU_def timeslu tl.simps wmin.elims
        by (metis bigMax min_le_iff_disj)
    next
      case 2
      have g1:"rl1 * ru2 \<le> rl1 * r2" 
        using "2" geq1 geq2 grl2 gru2
        by (metis mult_le_cancel_left  geq3 leD)
      have g2:"rl1 * r2 \<le> r1 * r2"
        using "2" geq1 geq2 grl2 gru2
        by (simp add: mult_right_mono grl1)
      from g1 and g2
      have up:"rl1 * ru2 \<le> r1 * r2"
        by auto
      show ?thesis
        by (metis up maxU12 min_repU2 repL_def tl.simps min.coboundedI1 maxt34)
    next
      case 3
      have g1:"ru1 * rl2 \<le> ru1 * r2" 
        using "3" geq1 geq2 grl2 gru2
        by (simp add: mult_left_mono)
      have g2:"ru1 * r2 \<le> r1 * r2"
        using "3" geq1 geq2 grl1 grl2 gru1 gru2 mult_minus_right mult_right_mono
        by (simp add: mult_right_mono_neg)
      from g1 and g2
      have up:"ru1 * rl2 \<le> r1 * r2" by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 maxt34 timesul
        by (metis repL_def tl.simps)
    next
      case 4
      have g1:"ru1 * rl2 \<le> 0" 
        using "4" geq1 geq2 grl1 grl2 gru1 gru2 \<open>rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2\<close> 
          mult_less_0_iff  less_eq_real_def not_less
        by auto
      have g2:"0 \<le> r1 * r2"
        using "4" geq1 geq2 grl1 grl2 gru1 gru2
        by (metis mult_less_0_iff  not_less)
      from g1 and g2
      have up:"ru1 * rl2 \<le> r1 * r2"
        by auto
      show ?thesis
      by (metis up maxU12 maxU34 wmin.elims min_repU1 min_repU2 repL_def timesul tl.simps) 
    qed
  next
    case ZeroPos
    assume bounds:"rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> 0 \<le> rl2"
    have r2:"r2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    consider "r1 \<ge> 0" | "r1 \<le> 0" using le_cases by auto
    then show ?thesis
    proof (cases)
      case 1
      have g1:"rl1 * rl2 \<le> 0" 
        using "1" r2 bounds grl1 grl2 gru1 gru2
        by (simp add: mult_le_0_iff)
      have g2:"0 \<le> r1 * r2"
        using "1" r2 bounds grl1 grl2 gru1 gru2
        by (simp)
      from g1 and g2
      have up:"rl1 * rl2 \<le> r1 * r2"
        by auto
      show ?thesis
        by (metis repL_def timesll tl.simps up maxU12 maxU34 wmin.elims min_repU2 min_repU1) 
    next
      case 2
      have bound:"ru2 \<ge> 0"
        using "2" r2 bounds grl1 grl2 gru1 gru2 dual_order.trans by auto
      then have g1:"rl1 * ru2 \<le> rl1 * r2" 
        using "2" r2 bounds grl1 grl2 gru1 gru2 mult_le_cancel_left
        by fastforce
      have g2:"rl1 * r2 \<le> r1 * r2"
        using "2" r2 bounds grl1 grl2 gru1 gru2 mult_le_0_iff mult_le_cancel_right by fastforce
      from g1 and g2
      have up:"rl1 * ru2 \<le> r1 * r2" by auto
      show ?thesis
        by (metis up maxU12 wmin.elims min_repU2 min.coboundedI1 maxt34 repL_def tl.simps) 
      qed
  next
    case ZeroNeg
    assume bounds:"rl1 \<le> 0 \<and> 0 \<le> ru1 \<and> ru2 \<le> 0"
    have r2:"r2 \<le> 0" using bounds dual_order.trans gru2 by blast
    consider (Pos) "r1 \<ge> 0" | (Neg) "r1 \<le> 0" using le_cases by auto
    then show ?thesis
    proof (cases)
      case Pos
      have bound:"rl2 \<le> 0"
        using Pos r2 bounds grl1 grl2 gru1 gru2 dual_order.trans by auto
      then have g1:"ru1 * rl2 \<le> ru1 * r2" 
        using Pos bounds grl1 grl2 gru1 gru2 mult_le_cancel_left
        by fastforce
      have p1:"\<And>a::real. (0 \<le> - a) = (a \<le> 0)"
        by(auto)
      have p2:"\<And>a b::real.  (- a \<le> - b) = (b \<le> a)" by auto
      have g2:"ru1 * r2 \<le> r1 * r2"
        using Pos r2 bounds grl1 grl2 gru1 gru2 p1 p2
        by (simp add: mult_right_mono_neg)
      from g1 and g2
      have up:"ru1 * rl2 \<le> r1 * r2"
        by auto
      show ?thesis 
        by (metis up maxU12 maxU34 wmin.elims min_repU2 min_repU1 repL_def timesul tl.simps)
    next
      case Neg
      have g1:"ru1 * ru2 \<le> 0" 
        using Neg r2 bounds  grl1 grl2 gru1 gru2 mult_le_0_iff by blast
      have g2:"0 \<le> r1 * r2"
        using Neg r2 zero_le_mult_iff by blast  
      from g1 and g2
      have up:"ru1 * ru2 \<le> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 
        min.coboundedI1 min.commute maxt34 
        by (metis repL_def tl.simps) 
      qed
  next
    case PosZero
    assume bounds:"0 \<le> rl1 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    have r1:"r1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have bound:"0 \<le> ru1" using r1 bounds grl1 grl2 gru1 gru2 dual_order.trans by auto
    consider "r2 \<ge> 0" | "r2 \<le> 0" using le_cases by auto
    then show ?thesis
    proof (cases)
      case 1
      have g1:"rl1 * rl2 \<le> 0" 
        using r1 "1" bounds grl1 grl2 gru1 gru2 mult_le_0_iff by blast
      have g2:"0 \<le> r1 * r2"
        using r1 "1" bounds grl1 grl2 gru1 gru2 zero_le_mult_iff by blast
      from g1 and g2
      have up:"rl1 * rl2 \<le> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmax.elims min_repU2 min_repU1 
        min.coboundedI1 min.commute maxt12 maxt34 repL_def timesll tl.simps
        by metis          
    next
      case 2
      have g1:"ru1 * rl2 \<le> ru1 * r2" 
        using r1 "2" bounds bound grl1 grl2 gru1 gru2
        using mult_left_mono by blast
      have g2:"ru1 * r2 \<le> r1 * r2"
        using r1 "2" bounds bound grl2 gru2
        by (metis mult_left_mono_neg gru1 mult.commute)
      from g1 and g2
      have up:"ru1 * rl2 \<le> r1 * r2"
        by auto
      show ?thesis
        using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 maxt34
        by (metis repL_def timesul tl.simps)
      qed
  next
    case NegZero
    assume bounds:"ru1 \<le> 0 \<and> rl2 \<le> 0 \<and> 0 \<le> ru2"
    have r1:"r1 \<le> 0"  using bounds dual_order.trans gru1 by blast
    have bound:"rl1 \<le> 0" using r1  bounds grl1 grl2 gru1 gru2 dual_order.trans by auto
    consider "r2 \<ge> 0" | "r2 \<le> 0" using le_cases by auto
    then show ?thesis
    proof (cases)
      case 1
      assume r2:"r2 \<ge> 0"
      have g1:"rl1 * ru2 \<le> rl1 * r2" 
        using r1 r2 bounds bound grl1 grl2 gru1 gru2
        by (metis mult_le_cancel_left leD)  
      have g2:"rl1 * r2 \<le> r1 * r2"
        using r1 r2 bounds grl1 grl2 gru1 gru2 mult_right_mono 
        by (simp add: mult_le_0_iff)
      from g1 and g2
      have up:"rl1 * ru2 \<le> r1 * r2"
        by auto
      show ?thesis
      using up maxU12 maxU34 bigMaxU min_repU2 min_repU1 min.coboundedI1 maxt34
      by (metis min_repU2 repL_def tl.simps) 
    next
      case 2
      assume r2:"r2 \<le> 0"
      have lower:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
      have g1:"ru1 * ru2 \<le> 0" 
        using r1 r2 bounds  grl1 grl2 gru1 gru2 mult_le_0_iff by blast
      have g2:"0 \<le> r1 * r2"
        using r1 r2 
        by (simp add: zero_le_mult_iff)
      from g1 and g2
      have up:"ru1 * ru2 \<le> r1 * r2"
        by auto
      show ?thesis
      using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 
        min.coboundedI1 min.commute maxt34
      by (metis repL_def tl.simps)
      qed
  next
    case NegNeg
    assume bounds:"ru1 \<le> 0 \<and> ru2 \<le> 0"
    have r1:"r1 \<le> 0" using bounds dual_order.trans gru1 by blast
    have r2:"r2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have lower1:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
    have lower2:"rl2 \<le> 0" using bounds dual_order.trans grl2 r2 by blast
    have g1:"ru1 * ru2 \<le> ru1 * r2" 
      using r1 r2 bounds  grl1 grl2 gru1 gru2
      using    not_less mult_le_cancel_left
      by metis
    have g2:"ru1 * r2 \<le> r1 * r2"
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult_le_cancel_left mult.commute not_le lower1 lower2
      by metis
    from g1 and g2
    have up:"ru1 * ru2 \<le> r1 * r2"
      by auto
    show ?thesis
      using up maxU12 maxU34 bigMaxU 
      wmin.elims min_repU2 min_repU1 
      min.coboundedI1 min.commute maxt34 
      by (metis repL_def tl.simps)
  next
    case NegPos
    assume bounds:"ru1 \<le> 0 \<and> 0 \<le> rl2"
    have r1:"r1 \<le> 0" using bounds dual_order.trans gru1 by blast
    have r2:"r2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have lower1:"rl1 \<le> 0" using bounds dual_order.trans grl1 r1 by blast
    have lower2:"rl2 \<ge> 0" using bounds by auto
    have upper1:"ru1 \<le> 0" using bounds by auto 
    have upper2:"ru2 \<ge> 0" using bounds dual_order.trans gru2 r2 by blast
    have g1:"rl1 * ru2 \<le> rl1 * r2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 less_le_trans upper1 lower2 
      by (metis mult_le_cancel_left not_less)
    have g2:"rl1 * r2 \<le> r1 * r2"
      using r1 upper1 r2 mult_right_mono mult_le_0_iff grl1 by blast
    from g1 and g2
    have up:"rl1 * ru2 \<le> r1 * r2"
      by auto
    show ?thesis
    using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1 maxt12 maxt34 
    by (metis repL_def timeslu tl.simps)
  next
    case PosNeg
    assume bounds:"0 \<le> rl1 \<and> ru2 \<le> 0"
    have r1:"r1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have r2:"r2 \<le> 0" using bounds dual_order.trans gru2 by blast
    have lower1:"rl1 \<ge> 0" using bounds by auto
    have lower2:"rl2 \<le> 0" using dual_order.trans grl2 r2 by blast
    have upper1:"ru1 \<ge> 0" using dual_order.trans gru1 u1 r1 by blast  
    have upper2:"ru2 \<le> 0" using bounds by auto
    have g1:"ru1 * rl2 \<le> ru1 * r2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2 mult_left_mono less_le_trans not_less
      by metis
    have g2:"ru1 * r2 \<le> r1 * r2"
      using r1 lower1 r2 not_less gru2 gru1 grl1 grl2
      by (metis mult_le_cancel_left  mult.commute)
    from g1 and g2
    have up:"ru1 * rl2 \<le> r1 * r2"
      by auto
    show "tl l\<^sub>1 u\<^sub>1 l\<^sub>2 u\<^sub>2 \<equiv>\<^sub>L r1 * r2"
      using up maxU12 maxU34 bigMaxU wmin.elims min_repU2 min_repU1
      by (metis repL_def timesul tl.simps)
  next
    case PosPos
    assume bounds:"0 \<le> rl1 \<and> 0 \<le> rl2"
    have r1:"r1 \<ge> 0" using bounds dual_order.trans grl1 by blast
    have r2:"r2 \<ge> 0" using bounds dual_order.trans grl2 by blast
    have lower1:"rl1 \<ge> 0" using bounds by auto
    have lower2:"rl2 \<ge> 0" using bounds by auto
    have upper1:"ru1 \<ge> 0" using dual_order.trans gru1 u1 r1 by blast  
    have upper2:"ru2 \<ge> 0" using dual_order.trans gru2 u2 r2 bounds by blast
    have g1:"rl1 * rl2 \<le> rl1 * r2" 
      using r1 r2 bounds grl1 grl2 gru1 gru2
      using mult_left_mono 
      using leD leI less_le_trans by auto
    have g2:"rl1 * r2 \<le> r1 * r2"
      using r1 r2 bounds grl1 grl2 gru1 gru2
      using mult_right_mono by blast
    from g1 and g2
    have up:"rl1 * rl2 \<le> r1 * r2"
      by auto
    show ?thesis
    using up maxU12 maxU34 bigMaxU min_repU2 min_repU1 min.coboundedI1 maxt12 maxt34
      by (metis repL_def tl.simps)
  qed
qed

text\<open>Most significant bit only changes under successor when all other bits are 1\<close>
lemma msb_succ:
  fixes w :: "32 Word.word"
  assumes neq1:"uint w \<noteq> 0xFFFFFFFF"
  assumes neq2:"uint w \<noteq> 0x7FFFFFFF"
  shows "msb (w + 1) = msb w"
  proof -
    have "w \<noteq> 0xFFFFFFFF"
      using neq1 by auto
    then have neqneg1:"w \<noteq> -1" by auto
    have "w \<noteq> 0x7FFFFFFF"
      using neq2 by auto
    then have neqneg2:"w \<noteq> (2^31)-1" by auto
    show ?thesis using neq1 neq2  unfolding msb_big
    using Word_Lemmas.word_le_make_less[of "w + 1" "0x80000000"] 
          Word_Lemmas.word_le_make_less[of "w " "0x80000000"]
          neqneg1 neqneg2
      by auto
  qed

text\<open>Negation commutes with msb except at edge cases\<close>
lemma msb_non_min:
  fixes w :: "32 Word.word"
  assumes neq1:"uint w \<noteq> 0"
  assumes neq2:"uint w \<noteq> ((2^(len_of (TYPE(31)))))"
  shows "msb (uminus w) = HOL.Not(msb(w))"
  proof -
    have fact1:"uminus w = word_succ (~~ w)"
      by (rule twos_complement)
    have fact2:"msb (~~w) = HOL.Not(msb w)"
      using Word.word_ops_msb[of w] 
      by auto
    have neqneg1:"w \<noteq> 0" using neq1 by auto
    have not_undef:"w \<noteq> 0x80000000"
      using neq2 by auto
    then have neqneg2:"w \<noteq> (2^31)" by auto
    have "~~ 0xFFFFFFFF = (0::word)" by auto
    then have "(~~ w) \<noteq> 0xFFFFFFFF"
      using neqneg1 neqneg2 Word.word_bool_alg.double_compl[of w] 
      by metis
    then have uintNeq1:"uint (~~ w) \<noteq> 0xFFFFFFFF"
      using uint_distinct[of "~~w" "0xFFFFFFFF"] 
      by auto
    have "~~ (0x7FFFFFFF::word) = (2 ^ 31::word)" by (auto simp add: max_word_def)
    then have "(~~ w) \<noteq> 0x7FFFFFFF"
      using neqneg1 neqneg2 Word.word_bool_alg.double_compl[of w] 
      by metis
    then have uintNeq2:" uint (~~ w) \<noteq> 0x7FFFFFFF"
      using uint_distinct[of "~~w" "0x7FFFFFFF"]
      by auto
    have fact3:"msb ((~~w) + 1) = msb (~~w)"
      apply(rule msb_succ[of "~~w"])
      using neq1 neq2 uintNeq1 uintNeq2 by auto 
    show "msb (uminus w) = HOL.Not(msb(w))"
      using fact1 fact2 fact3 by (simp add: word_succ_p1)
    qed

text\<open>Only 0x80000000 preserves msb=1 under negation\<close>
lemma msb_min_neg:
  fixes w::"word"
  assumes msb1:"msb (- w)"
  assumes msb2:"msb w"
  shows "uint w = ((2^(len_of (TYPE(31)))))"
  proof -
    have neq1:"uint w \<noteq> 0" using msb2 word_msb_0 uint_0_iff by force
    show ?thesis using msb1 msb2 msb_non_min[OF neq1] 
    by auto
  qed


text\<open>Only 0x00000000 preserves msb=0 under negation\<close>
lemma msb_zero:
  fixes w::"word"
  assumes msb1:"\<not> msb (- w)"
  assumes msb2:"\<not> msb w"
  shows "uint w = 0"
  proof -
    have neq:"w \<noteq> ((2 ^ len_of TYPE(31))::word)" using msb1 msb2 by auto
    have eq:"uint ((2 ^ len_of TYPE(31))::word) = 2 ^ len_of TYPE(31)" 
      by auto
    then have neq:"uint w \<noteq> uint ((2 ^ len_of TYPE(31))::word)" 
      using uint_distinct[of w "2^len_of TYPE(31)"] neq eq by auto
    show ?thesis
      using msb1 msb2 minus_zero msb_non_min[of w] neq by force
  qed
    
text\<open>Finite numbers alternate msb under negation\<close>
lemma msb_pos:
  fixes w::"word"
  assumes msb1:"msb (- w)"
  assumes msb2:"\<not> msb w"
  shows "uint w \<in> {1 .. (2^((len_of TYPE(32)) - 1))-1}" 
  proof -
    have main: "w \<in> {1 .. (2^((len_of TYPE(32)) - 1))-1}"
      using msb1 msb2 apply(clarsimp) 
      unfolding word_msb_sint
      apply(rule conjI)
      apply (metis neg_equal_0_iff_equal not_le word_less_1)
      proof -
        have imp:"w \<ge> 0x80000000 \<Longrightarrow> False"
          proof -
            assume geq:"w \<ge> 0x80000000"
            then have "msb w"
              using Word_Lemmas.msb_big[of w] by auto
            then show False using msb2 by auto
          qed
        have mylem:"\<And>w1 w2::word. uint w1 \<ge> uint w2 \<Longrightarrow> w1 \<ge> w2" 
          subgoal for w1 w2 
            by (simp add: word_le_def)
          done
        have mylem2:"\<And>w1 w2::word.  w1 >  w2 \<Longrightarrow> uint w1 > uint w2" 
          subgoal for w1 w2 
            by (simp add: word_less_def)
          done
        have gr_to_geq:"w > 0x7FFFFFFF \<Longrightarrow> w \<ge> 0x80000000"
          apply(rule mylem)
          using mylem2[of "0x7FFFFFFF" "w"] by auto
        have taut:"w \<le> 0x7FFFFFFF \<or> w > 0x7FFFFFFF" by auto        
        then show "w \<le> 0x7FFFFFFF"
        using imp taut gr_to_geq by auto
      qed
    have set_eq:"(uint ` (({1..(minus(2 ^ (minus(len_of TYPE(32))  1)) 1)})::word set)) 
               = ({1..minus(2 ^ (minus (len_of TYPE(32)) 1)) 1}::int set)"
      apply(auto simp add: word_le_def)
      subgoal for xa 
      proof -
        assume lower:"1 \<le> xa" and upper:"xa \<le> 2147483647"
        then have in_range:"xa \<in> {0 .. 2^32-1}" by auto
        then have "xa \<in> range (uint::word \<Rightarrow> int)" 
          unfolding Word.word_uint.Rep_range Word.uints_num by auto
        then obtain w::word  where xaw:"xa = uint w" by auto
        then have "w \<in> {1..0x7FFFFFFF} " 
        using lower upper apply(clarsimp, auto)
        by (auto simp add: word_le_def)
        then show ?thesis
          using uint_distinct uint_distinct main image_eqI word_le_def xaw by blast
      qed
      done
    then show  "uint w \<in> {1..2 ^ (len_of TYPE(32) - 1) - 1}" 
      using uint_distinct uint_distinct main image_eqI
      by blast
    qed
    
lemma msb_neg:
  fixes w::"word"
  assumes msb1:"\<not> msb (- w)"
  assumes msb2:"msb w"
  shows "uint w \<in> {2^((len_of TYPE(32) - 1))+1 .. 2^((len_of TYPE(32)))-1}" 
  proof -
    have mylem:"\<And>w1 w2::word. uint w1 \<ge> uint w2 \<Longrightarrow> w1 \<ge> w2" 
      by (simp add: word_le_def)
    have mylem2:"\<And>w1 w2::word.  w1 >  w2 \<Longrightarrow> uint w1 > uint w2" 
      by (simp add: word_less_def)
    have gr_to_geq:"w > 0x80000000 \<Longrightarrow> w \<ge> 0x80000001"
      apply(rule mylem)
      using mylem2[of "0x80000000" "w"] by auto
    have taut:"w \<le> 0x80000000 \<or> 0x80000000 < w" by auto
    have imp:"w \<le> 0x80000000 \<Longrightarrow> False"
      proof -
        assume geq:"w \<le> 0x80000000"
        then have "(msb (-w))"
          using Word_Lemmas.msb_big[of "-w"] Word_Lemmas.msb_big[of "w"] 
          by (simp add: msb2) 
        then show False using msb1 by auto
      qed
    have main: "w \<in> {2^((len_of TYPE(32)) - 1)+1 .. 2^((len_of TYPE(32)))-1}"  
      using msb1 msb2 apply(clarsimp)
      unfolding word_msb_sint
      proof -
        show "0x80000001 \<le> w"
        using imp taut gr_to_geq by auto
      qed
    have set_eq:"(uint ` (({2^((len_of TYPE(32) - 1))+1 .. 2^((len_of TYPE(32)))-1})::word set)) 
                       = {2^((len_of TYPE(32) - 1))+1 .. 2^((len_of TYPE(32)))-1}"
      apply(auto)
      subgoal for xa by (simp add: word_le_def)
      subgoal for w using Word.word.uint[of w] by auto
      subgoal for xa
      proof -
        assume lower:"2147483649 \<le> xa" and upper:"xa \<le> 4294967295"
        then have in_range:"xa \<in> {0x80000000 .. 0xFFFFFFFF}" by auto
        then have "xa \<in> range (uint::word \<Rightarrow> int)" 
          unfolding Word.word_uint.Rep_range Word.uints_num by auto
        then obtain w::word  where xaw:"xa = uint w" by auto
        then have the_in:"w \<in> {0x80000001 .. 0xFFFFFFFF} " 
          using lower upper
          by (auto simp add: word_le_def)
        have the_eq:"(0xFFFFFFFF::word) = -1" by auto
        from the_in the_eq have "w \<in> {0x80000001 .. -1}" by auto
        then show ?thesis
      using uint_distinct uint_distinct main image_eqI word_le_def xaw by blast
      qed
      done
    then show  "uint w \<in> {2^((len_of TYPE(32)) - 1)+1 .. 2^((len_of TYPE(32)))-1}" 
      using uint_distinct uint_distinct main image_eqI
      by blast
    qed

text\<open>2s-complement commutes with negation except edge cases\<close>
lemma sint_neg_hom:
  fixes w :: "32 Word.word"
  shows "uint w \<noteq> ((2^(len_of (TYPE(31))))) \<Longrightarrow> (sint(-w) = -(sint w))"
  unfolding Word_Bitwise.word_sint_msb_eq apply auto
    subgoal using msb_min_neg by auto 
   prefer 3 subgoal using msb_zero[of w] by (simp add: msb_zero)
  proof -
    assume msb1:"msb (- w)"
    assume msb2:"\<not> msb w"
    have "uint w \<in> {1 .. (2^((len_of TYPE(32)) - 1))-1}" using msb_pos[OF msb1 msb2] by auto
    then have bound:"uint w \<in> {1 .. 0x7FFFFFFF}" by auto
    have size:"size (w::32 Word.word) = 32" using Word.word_size[of w] by auto 
    have lem:"\<And>x::int. \<And>n::nat.   x \<in> {1..(2^n)-1} \<Longrightarrow> ((- x) mod (2^n)) - (2^n) = - x"
      subgoal for x n
        apply(cases "x mod 2^n = 0")
        by(auto simp add: Divides.zmod_zminus1_eq_if[of x  "2^n"])
      done
    have lem_rule:"uint w \<in> {1..2 ^ 32 - 1} 
      \<Longrightarrow> (- uint w mod  4294967296) - 4294967296 = - uint w"
      using lem[of "uint w" 32] by auto
    have almost:"- uint w mod 4294967296 - 4294967296 = - uint w"
      apply(rule lem_rule)  
      using bound by auto
    show "uint (- w) - 2 ^ size (- w) = - uint w"
    using bound
    unfolding Word.uint_word_ariths word_size_neg by (auto simp add: size almost)
next
  assume neq:"uint w \<noteq> 0x80000000"
  assume msb1:"\<not> msb (- w)"
  assume msb2:"msb w"
  have bound:"uint w \<in> {0x80000001.. 0xFFFFFFFF}" using msb1 msb2 msb_neg by auto
  have size:"size (w::32 Word.word) = 32" using Word.word_size[of w] by auto
  have lem:"\<And>x::int. \<And>n::nat.   x \<in> {1..(2^n)-1} \<Longrightarrow> (-x mod (2^n)) = (2^n) - x"
      subgoal for x n
        apply(auto)
        apply(cases "x mod 2^n = 0")
        by (simp add: Divides.zmod_zminus1_eq_if[of x  "2^n"])+
      done
  from bound 
  have  wLeq: "uint w \<le> 4294967295"
    and wGeq: "2147483649 \<le> uint w"
    by auto
  from wLeq have wLeq':"uint w \<le> 4294967296" by fastforce
  have f3: "(0 \<le> 4294967296 + - 1 * uint w + - 1 * ((4294967296 + - 1 * uint w) mod 4294967296))
            = (uint w + (4294967296 + - 1 * uint w) mod 4294967296 \<le> 4294967296)"
    by auto
  have f4: "(0 \<le> 4294967296 + - 1 * uint w) = (uint w \<le> 4294967296)"
    by auto
  have f5: "\<forall>i ia. \<not> (0::int) \<le> i \<or> 0 \<le> i + - 1 * (i mod ia)"
    by (simp add: zmod_le_nonneg_dividend)
  then have f6: "uint w + (4294967296 + - 1 * uint w) mod 4294967296 \<le> 4294967296"
    using f4 f3 wLeq' by blast
  have f7: "4294967296 + - 1 * uint w + - 4294967296 = - 1 * uint w"
    by auto
  have f8: "- (1::int) * 4294967296 = - 4294967296"
    by auto
  have f9: "(0 \<le> - 1 * uint w) = (uint w \<le> 0)"
    by auto
  have f10: "(4294967296 + -1 * uint w + -1 * ((4294967296 + -1 * uint w) mod 4294967296) \<le> 0) 
           = (4294967296 \<le> uint w + (4294967296 + - 1 * uint w) mod 4294967296)"
    by auto
  have f11: "\<not> 4294967296 \<le> (0::int)"
    by auto
  have f12: "\<forall>x0. ((0::int) < x0) = (\<not> x0 \<le> 0)"
    by auto
  have f13: "\<forall>x0 x1. ((x1::int) < x0) = (\<not> 0 \<le> x1 + - 1 * x0)"
    by auto
  have f14: "\<forall>x0 x1. ((x1::int) \<le> x1 mod x0) = (x1 + - 1 * (x1 mod x0) \<le> 0)"
    by auto
  have "\<not> uint w \<le> 0"
    using wGeq by fastforce
  then have "4294967296 \<le> uint w + (4294967296 + - 1 * uint w) mod 4294967296"
    using f14 f13 f12 f11 f10 f9 f8 f7 by (metis (no_types) int_mod_ge)
  then 
  show "uint (- w) = 2 ^ size w - uint w"
    using f6
    unfolding Word.uint_word_ariths  
    by (auto simp add: size f4)
  qed

text\<open>2s-complement encoding is injective\<close>
lemma sint_dist:
  fixes x y ::word
  assumes "x \<noteq> y"
  shows "sint x \<noteq> sint y"
  by (simp add: assms)

subsection\<open>Negation\<close>
fun wneg :: "word \<Rightarrow> word"
where "wneg w = 
  (if w = NEG_INF then POS_INF else if w = POS_INF then NEG_INF else -w)"

text\<open>word negation is correct\<close>
lemma wneg_lemma:
  assumes eq:"w \<equiv>\<^sub>E (r::real)"
  shows "wneg w \<equiv>\<^sub>E -r"
  apply(rule repe.cases[OF eq])
    apply(auto intro!: repNEG_INF repPOS_INF simp add: repe.simps)[2]
  subgoal for ra
  proof -
    assume eq:"w = ra"
    assume i:"r =  (real_of_int (sint ra))"
    assume bounda:" (real_of_int (sint ra)) <  (real_of_int (sint POS_INF))"
    assume boundb:" (real_of_int (sint NEG_INF)) <  (real_of_int (sint ra))"
    have raNeq:"ra \<noteq> 2147483647"
      using sint_range[OF bounda boundb]
      by (auto)
    have raNeqUndef:"ra \<noteq> 2147483648"
      using int_not_undef[OF bounda boundb]
      by (auto)
    have "uint ra \<noteq> uint ((2 ^ len_of TYPE(31))::word)"
      apply (rule uint_distinct)
      using raNeqUndef by auto
    then have raNeqUndefUint:"uint ra \<noteq> ((2 ^ len_of TYPE(31)))"
      by auto
    have res1:"wneg w \<equiv>\<^sub>E  (real_of_int (sint (wneg w)))"
      apply (rule repINT)
      using sint_range[OF bounda boundb] sint_neg_hom[of ra, OF raNeqUndefUint]
      raNeq raNeqUndefUint raNeqUndef eq 
      by(auto)
    have res2:"- r =  (real_of_int (sint (wneg w)))"
      using eq bounda boundb i sint_neg_hom[of ra, OF raNeqUndefUint] raNeq raNeqUndef eq
      by (auto)
    show ?thesis
      using res1 res2 by auto
    qed
  done

subsection\<open>Comparison\<close>
fun wgreater :: "word \<Rightarrow> word \<Rightarrow> bool"
where "wgreater w1 w2 = (sint w1 > sint w2)"

lemma neg_less_contra:"\<And>x. Suc x < - (Suc x) \<Longrightarrow> False"
  by auto

text\<open>Comparison < is correct\<close>
lemma wgreater_lemma:"w1 \<equiv>\<^sub>L (r1::real) \<Longrightarrow> w2 \<equiv>\<^sub>U r2 \<Longrightarrow> wgreater w1 w2 \<Longrightarrow> r1 > r2"
  proof (auto simp add: repU_def repL_def)
    fix r'\<^sub>1 r'\<^sub>2
    assume sint_le:"sint w1 > sint w2"
    then have sless:"(w2 <s w1)" using word_sless_alt by auto
    assume r1_leq:"r'\<^sub>1 \<le> r1"
    assume r2_leq:"r2 \<le> r'\<^sub>2"
    assume wr1:"w1 \<equiv>\<^sub>E r'\<^sub>1"
    assume wr2:"w2 \<equiv>\<^sub>E r'\<^sub>2"
    have greater:"r'\<^sub>1 > r'\<^sub>2" 
      using wr1 wr2 apply(auto simp add: repe.simps)
      prefer 4 using sless sint_le  by (auto simp add: less_le_trans not_le)
    show "r1 > r2"
      using r1_leq r2_leq greater by auto
  qed

text\<open>Comparison $\geq$ of words\<close>
fun wgeq :: "word \<Rightarrow> word \<Rightarrow> bool"
where "wgeq w1 w2 =
((\<not> ((w2 = NEG_INF \<and> w1 = NEG_INF)
  \<or>(w2 = POS_INF \<and> w1 = POS_INF))) \<and>
(sint w2 \<le> sint w1))"

text\<open>Comparison $\geq$ of words is correct\<close>
lemma wgeq_lemma:"w1 \<equiv>\<^sub>L r1 \<Longrightarrow> w2 \<equiv>\<^sub>U (r2::real) \<Longrightarrow> wgeq w1 w2 \<Longrightarrow> r1 \<ge> r2"
  proof (unfold wgeq.simps)
    assume assms:"\<not> (w2 = NEG_INF \<and> w1 = NEG_INF \<or> w2 = POS_INF \<and> w1 = POS_INF) \<and> sint w2 \<le> sint w1"
    assume a1:"w1 \<equiv>\<^sub>L r1" and a2:"w2 \<equiv>\<^sub>U (r2::real)"
    from assms have sint_le:"sint w2 \<le> sint w1" by auto
    then have sless:"(w2 <=s w1)" using word_sless_alt word_sle_def by auto
    obtain r'\<^sub>1 r'\<^sub>2 where  r1_leq:"r'\<^sub>1 \<le> r1" and r2_leq:"r2 \<le> r'\<^sub>2"
    and wr1:"w1 \<equiv>\<^sub>E r'\<^sub>1" and wr2:"w2 \<equiv>\<^sub>E r'\<^sub>2"
    using a1 a2 unfolding repU_def repL_def by auto
    from assms have check1:"\<not> (w1 = NEG_INF \<and> w2 = NEG_INF)" by auto
    from assms have check2:"\<not> (w1 = POS_INF \<and> w2 = POS_INF)" by auto
    have less:"r'\<^sub>2 \<le> r'\<^sub>1" 
      using sless sint_le check1 check2 repe.simps wr2 wr1
      by(auto simp add: repe.simps)
    show "r1 \<ge> r2"
      using r1_leq r2_leq less by auto
  qed

subsection\<open>Absolute value\<close>

text\<open>Absolute value of word\<close>
fun wabs :: "word \<Rightarrow> word"
  where "wabs l1 = (wmax l1 (wneg l1))"

text\<open>Correctness of wmax\<close>
lemma wabs_lemma:
  assumes eq:"w \<equiv>\<^sub>E (r::real)"
  shows "wabs w \<equiv>\<^sub>E (abs r)"
proof -
  have w:"wmax w (wneg w) \<equiv>\<^sub>E max r (-r)" by (rule wmax_lemma[OF eq wneg_lemma[OF eq]])
  have r:"max r (-r) = abs r" by auto
  from w r show ?thesis by auto
qed
end