text\<open>
Interpreter.thy defines a simple programming language over interval-valued variables and executable
semantics (interpreter) for that language. We then prove that the interpretation of interval terms
is a sound over-approximation of a real-valued semantics of the same language.

Our language is a version of first order dynamic logic-style regular programs.
We use a finite identifier space for compatibility with Differential-Dynamic-Logic, where identifier
finiteness is required to treat program states as Banach spaces to enable differentiation.
\<close>
(* Author:     Brandon Bohrer *)
theory Interpreter
imports
  Complex_Main
  "./Finite_String"
  Interval_Word32
  Word_Lib.Word_Lemmas
  Word_Lib.Word_Lib
  Word_Lib.Word_Syntax
begin

section\<open>Syntax\<close>
text\<open>Our term language supports variables, polynomial arithmetic, and extrema. This choice was made
   based on the needs of the original paper and could be extended if necessary.\<close>
datatype  trm =
  Var fin_string
| Const lit
| Plus trm trm
| Times trm trm
| Neg trm
| Max trm trm
| Min trm trm
| Abs trm

text\<open>Our statement language is nondeterministic first-order regular programs.
 This coincides with the discrete subset of hybrid programs from the dL entry.

Our assertion language are the formulas of first-order dynamic logic\<close>
datatype prog =
  Assign fin_string "trm"     (infixr ":=" 10)
| AssignAny fin_string                
| Test "formula"              ("?")
| Choice "prog" "prog"        (infixl "\<union>\<union>" 10)
| Sequence "prog"  "prog"     (infixr ";;" 8)
| Loop "prog"                 ("_**")

and formula =
  Geq "trm" "trm"
| Not "formula"                        ("!")
| And "formula" "formula"              (infixl "&&" 8)
| Exists fin_string "formula"
| Diamond "prog" "formula"               ("(\<langle> _ \<rangle> _)" 10)
    
text\<open>Derived forms\<close>
definition Or :: "formula \<Rightarrow> formula \<Rightarrow> formula" (infixl "||" 7)
where or_simp[simp]:"Or P Q = Not (And (Not P) (Not Q))"

definition Equals :: "trm \<Rightarrow> trm \<Rightarrow> formula"
where equals_simp[simp]:"Equals \<theta> \<theta>' = (And (Geq \<theta> \<theta>') (Geq \<theta>' \<theta>))"

definition Greater :: "trm \<Rightarrow> trm \<Rightarrow> formula"
where greater_simp[simp]:"Greater \<theta> \<theta>' = Not (Geq \<theta>' \<theta>)"

definition Leq :: "trm \<Rightarrow> trm \<Rightarrow> formula"
where leq_simp[simp]:"Leq \<theta> \<theta>' = (Geq \<theta>' \<theta>)"

definition Less :: "trm \<Rightarrow> trm \<Rightarrow> formula"
where less_simp[simp]:"Less \<theta> \<theta>' = (Not (Geq \<theta> \<theta>'))"

section \<open>Semantics\<close>
text\<open> States over reals vs. word intervals which contain them\<close>
type_synonym rstate = "fin_string \<Rightarrow> real"
type_synonym wstate = "(fin_string + fin_string) \<Rightarrow> word"

definition wstate::"wstate \<Rightarrow> prop"
where wstate_def[simp]:"wstate \<nu> \<equiv> (\<And>i. word (\<nu> (Inl i)) \<and> word (\<nu> (Inr i)))"

text\<open>Interpretation of a term in a state\<close>
inductive rtsem :: "trm \<Rightarrow> rstate \<Rightarrow> real  \<Rightarrow> bool"  ("([_]_ \<down> _)" 10)
  where 
  rtsem_Const:"Rep_bword w \<equiv>\<^sub>E r \<Longrightarrow> ([Const w]\<nu> \<down> r)"
| rtsem_Var:"([Var x]\<nu> \<down> \<nu> x)"
| rtsem_Plus:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> ([Plus \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (r1 + r2))"
| rtsem_Times:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> ([Times \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (r1 * r2))"
| rtsem_Max:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> ([Max \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (max r1 r2))"
| rtsem_Min:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> ([Min \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> (min r1 r2))"
| rtsem_Abs:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1)\<rbrakk> \<Longrightarrow> ([Abs \<theta>\<^sub>1]\<nu> \<down> (abs r1))"
| rtsem_Neg:"([\<theta>]\<nu> \<down> r) \<Longrightarrow> ([Neg \<theta>]\<nu> \<down> -r)"

inductive_simps 
    rtsem_Const_simps[simp] : "([(Const w)]\<nu> \<down> r)"
and rtsem_Var_simps[simp] : "([Var x]\<nu> \<down> r)"
and rtsem_PlusU_simps[simp] : "([Plus \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> r)"
and rtsem_TimesU_simps[simp] : "([Times \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<down> r)"
and rtsem_Max_simps[simp] : "([Max \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> r)"
and rtsem_Min_simps[simp] : "([Min \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<down> r)"
and rtsem_Abs_simps[simp] : "([Abs \<theta>] \<nu> \<down> r)"
and rtsem_Neg_simps[simp] : "([Neg \<theta>] \<nu> \<down> r)"

definition set_less :: "real set \<Rightarrow> real set \<Rightarrow> bool" (infix "<\<^sub>S" 10)
where "set_less A B \<equiv> (\<forall> x y. x \<in> A \<and> y \<in> B \<longrightarrow> x < y)"

definition set_geq :: "real set \<Rightarrow> real set \<Rightarrow> bool" (infix "\<ge>\<^sub>S" 10)
where "set_geq A B \<equiv> (\<forall> x y. x \<in> A \<and> y \<in> B \<longrightarrow> x \<ge> y)"

text\<open>Interpretation of an assertion in a state\<close>
inductive rfsem :: "formula \<Rightarrow> rstate \<Rightarrow> bool \<Rightarrow> bool" ("([_]_) \<downharpoonright> _" 20)
where 
  rGreaterT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> r1 > r2 \<Longrightarrow> ([Greater \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> True)"
| rGreaterF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> r2 \<ge> r1 \<Longrightarrow> ([Greater \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> False)"
| rGeqT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> r1 \<ge> r2 \<Longrightarrow> ([Geq \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> True)"
| rGeqF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> r2 > r1 \<Longrightarrow> ([Geq \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> False)"
| rEqualsT:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> r1 = r2 \<Longrightarrow> ([Equals \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> True)"
| rEqualsF:"\<lbrakk>([\<theta>\<^sub>1]\<nu> \<down> r1); ([\<theta>\<^sub>2]\<nu> \<down> r2)\<rbrakk> \<Longrightarrow> r1 \<noteq> r2 \<Longrightarrow> ([Equals \<theta>\<^sub>1 \<theta>\<^sub>2] \<nu> \<downharpoonright> False)"
| rAndT:"\<lbrakk>([\<phi>]\<nu> \<downharpoonright> True); ([\<psi>]\<nu> \<downharpoonright> True)\<rbrakk> \<Longrightarrow> ([And \<phi> \<psi>]\<nu> \<downharpoonright> True)"
| rAndF1:"([\<phi>]\<nu> \<downharpoonright> False) \<Longrightarrow> ([And \<phi> \<psi>]\<nu> \<downharpoonright> False)"
| rAndF2:"([\<psi>]\<nu> \<downharpoonright> False) \<Longrightarrow> ([And \<phi> \<psi>]\<nu> \<downharpoonright> False)"
| rOrT1:"([\<phi>]\<nu> \<downharpoonright> True) \<Longrightarrow> ([Or \<phi> \<psi>]\<nu> \<downharpoonright> True)"
| rOrT2:"([\<psi>]\<nu> \<downharpoonright> True) \<Longrightarrow> ([Or \<phi> \<psi>]\<nu> \<downharpoonright> True)"
| rOrF:"\<lbrakk>([\<phi>]\<nu> \<downharpoonright> False) ;([\<psi>]\<nu> \<downharpoonright> False)\<rbrakk> \<Longrightarrow> ([And \<phi> \<psi>]\<nu> \<downharpoonright> False)"
| rNotT:"([\<phi>]\<nu> \<downharpoonright> False) \<Longrightarrow> ([(Not \<phi>)]\<nu> \<downharpoonright> True)"
| rNotF:"([\<phi>]\<nu> \<downharpoonright> True) \<Longrightarrow> ([(Not \<phi>)]\<nu> \<downharpoonright> False)"

inductive_simps
    rfsem_Greater_simps[simp]: "([Greater \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<downharpoonright> b)"
and rfsem_Geq_simps[simp]: "([Geq \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<downharpoonright> b)"
and rfsem_Equals_simps[simp]: "([Equals \<theta>\<^sub>1 \<theta>\<^sub>2]\<nu> \<downharpoonright> b)"
and rfsem_And_simps[simp]: "([And \<phi>  \<psi>]\<nu> \<downharpoonright> b)"
and rfsem_Or_simps[simp]: "([(Or \<phi> \<psi>)]\<nu> \<downharpoonright> b)"
and rfsem_Not_simps[simp]: "([Not \<phi>]\<nu> \<downharpoonright> b)"

text\<open>Interpretation of a program is a transition relation on states\<close>
inductive rpsem :: "prog \<Rightarrow> rstate \<Rightarrow>  rstate \<Rightarrow> bool" ("([_]_) \<downharpoonleft> _" 20)
where
  rTest[simp]:"\<lbrakk>([\<phi>]\<nu> \<downharpoonright> True); \<nu> = \<omega>\<rbrakk> \<Longrightarrow> ([? \<phi>]\<nu> \<downharpoonleft> \<omega>)"
| rSeq[simp]:"\<lbrakk>([\<alpha>]\<nu> \<downharpoonleft> \<mu>); ([\<beta>]\<mu> \<downharpoonleft> \<omega>)\<rbrakk> \<Longrightarrow> ([\<alpha>;; \<beta>]\<nu> \<downharpoonleft> \<omega>)"
| rAssign[simp]:"\<lbrakk>([\<theta>]\<nu> \<down> r); \<omega> = (\<nu> (x := r))\<rbrakk> \<Longrightarrow> ([Assign x \<theta>]\<nu> \<downharpoonleft> \<omega>)"
| rChoice1[simp]:"([\<alpha>]\<nu> \<downharpoonleft> \<omega>) \<Longrightarrow> ([Choice \<alpha> \<beta>]\<nu> \<downharpoonleft> \<omega>)"
| rChoice2[simp]:"([\<beta>]\<nu> \<downharpoonleft> \<omega>) \<Longrightarrow> ([Choice \<alpha> \<beta>]\<nu> \<downharpoonleft> \<omega>)"

inductive_simps
    rpsem_Test_simps[simp]: "([? \<phi>]\<nu> \<downharpoonleft> b)"
and rpsem_Seq_simps[simp]: "([\<alpha>;; \<beta>]\<nu> \<downharpoonleft> b)"
and rpsem_Assign_simps[simp]: "([Assign x \<theta>]\<nu> \<downharpoonleft> b)"
and rpsem_Choice_simps[simp]: "([Choice \<alpha> \<beta>]\<nu> \<downharpoonleft> b)"

text\<open>Upper bound of arbitrary term\<close>
fun wtsemU :: "trm \<Rightarrow> wstate \<Rightarrow>  word * word " ("([_]<>_)" 20)
where "([Const r]<>\<nu>) = (Rep_bword r::word, Rep_bword r)"
| wVarU:"([Var x]<>\<nu>) = (\<nu> (Inl x), \<nu> (Inr x))"
| wPlusU:"([Plus \<theta>\<^sub>1 \<theta>\<^sub>2]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
   (pl l1 l2, pu u1 u2))"
| wTimesU:"([(Times \<theta>\<^sub>1 \<theta>\<^sub>2)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
   (tl l1 u1 l2 u2, tu l1 u1 l2 u2))"
| wMaxU:"([(Max \<theta>\<^sub>1 \<theta>\<^sub>2)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
  (wmax l1 l2, wmax u1 u2))"
| wMinU:"([(Min \<theta>\<^sub>1 \<theta>\<^sub>2)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
   let (l2, u2) = [\<theta>\<^sub>2]<> \<nu> in
  (wmin l1 l2, wmin u1 u2))"
| wNegU:"([(Neg \<theta>)]<> \<nu>) =
  (let (l, u) = [\<theta>]<> \<nu> in
   (wneg u, wneg l))"
| wAbsU:"([(Abs \<theta>\<^sub>1)]<> \<nu>) = 
  (let (l1, u1) = [\<theta>\<^sub>1]<> \<nu> in 
  (wmax l1 (wneg u1), wmax u1 (wneg l1)))"

inductive wfsem :: "formula \<Rightarrow> wstate \<Rightarrow> bool \<Rightarrow> bool" ("([[_]]_ \<down> _)" 20)
where 
  wGreaterT:"wgreater (fst ([\<theta>\<^sub>1]<>\<nu>)) (snd ([\<theta>\<^sub>2]<>\<nu>)) \<Longrightarrow>  ([[(Greater \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> True)"
| wGreaterF:"wgeq (fst ([\<theta>\<^sub>2]<>\<nu>)) (snd ([\<theta>\<^sub>1]<>\<nu>)) \<Longrightarrow>  ([[(Greater \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> False)"
| wGeqT:"wgeq (fst ([\<theta>\<^sub>1]<> \<nu>)) (snd ([\<theta>\<^sub>2]<>\<nu>)) \<Longrightarrow>  ([[(Geq \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> True)"
| wGeqF:"wgreater (fst ([\<theta>\<^sub>2]<>\<nu>)) (snd ([\<theta>\<^sub>1]<>\<nu>)) \<Longrightarrow>  ([[(Geq \<theta>\<^sub>1 \<theta>\<^sub>2)]]\<nu> \<down> False)"
| wEqualsT:"\<lbrakk>(fst ([\<theta>\<^sub>2]<>\<nu>) = snd ([\<theta>\<^sub>2]<>\<nu>)); (snd ([\<theta>\<^sub>2]<>\<nu>) = snd ([\<theta>\<^sub>1]<>\<nu>)); 
             (snd ([\<theta>\<^sub>1]<>\<nu>) = fst ([\<theta>\<^sub>1]<>\<nu>)); (fst ([\<theta>\<^sub>2]<>\<nu>) \<noteq> NEG_INF); 
             (fst ([\<theta>\<^sub>2]<>\<nu>) \<noteq> POS_INF)\<rbrakk> 
         \<Longrightarrow> ([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]] \<nu> \<down> True)"
| wEqualsF1:"wgreater (fst ([\<theta>\<^sub>1]<> \<nu>)) (snd ([\<theta>\<^sub>2]<>\<nu>)) \<Longrightarrow>  ([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]] \<nu> \<down> False)"
| wEqualsF2:"wgreater (fst ([\<theta>\<^sub>2]<> \<nu>)) (snd ([\<theta>\<^sub>1]<>\<nu>)) \<Longrightarrow>  ([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]] \<nu> \<down> False)"
| wAndT:"\<lbrakk>[[\<phi>]]\<nu> \<down> True; [[\<psi>]]\<nu> \<down> True\<rbrakk> \<Longrightarrow> ([[And \<phi> \<psi>]]\<nu> \<down> True)"
| wAndF1:"[[\<phi>]]\<nu> \<down> False \<Longrightarrow> ([[And \<phi> \<psi>]]\<nu> \<down> False)"
| wAndF2:"[[\<psi>]]\<nu> \<down> False \<Longrightarrow> ([[And \<phi> \<psi>]]\<nu> \<down> False)"
| wOrT1:"([[\<phi>]]\<nu> \<down> True) \<Longrightarrow> ([[Or \<phi> \<psi>]]\<nu> \<down> True)"
| wOrT2:"([[\<psi>]]\<nu> \<down> True) \<Longrightarrow> ([[Or \<phi> \<psi>]]\<nu> \<down> True)"
| wOrF:"\<lbrakk>[[\<phi>]]\<nu> \<down> False; [[\<psi>]]\<nu> \<down> False\<rbrakk> \<Longrightarrow> ([[And \<phi> \<psi>]]\<nu> \<down> False)"
| wNotT:"([[\<phi>]]\<nu> \<down> False) \<Longrightarrow> ([[Not \<phi>]]\<nu> \<down> True)"
| wNotF:"([[\<phi>]]\<nu> \<down> True) \<Longrightarrow> ([[Not \<phi>]]\<nu> \<down> False)"

inductive_simps
    wfsem_Gr_simps[simp]: "([[Le \<theta>\<^sub>1 \<theta>\<^sub>2]]\<nu> \<down> b)"
and wfsem_And_simps[simp]: "([[And \<phi> \<psi>]]\<nu> \<down> b)"
and wfsem_Or_simps[simp]: "([[Or \<phi> \<psi>]]\<nu> \<down> b)"
and wfsem_Not_simps[simp]: "([[Not \<phi>]]\<nu> \<down> b)"
and wfsem_Equals_simps[simp]: "([[Equals \<theta>\<^sub>1 \<theta>\<^sub>2]]\<nu> \<down> b)"

text\<open>Program semantics\<close>
inductive wpsem :: "prog \<Rightarrow>  wstate \<Rightarrow> wstate \<Rightarrow> bool" ("([[_]]_ \<down> _)" 20)
where
  wTest:"([[\<phi>]]\<nu> \<down> True) \<Longrightarrow> \<nu> = \<omega> \<Longrightarrow> ([[? \<phi>]] \<nu> \<down> \<omega>)"
| wSeq:"([[\<alpha>]]\<nu> \<down> \<mu>) \<Longrightarrow> ([[\<beta>]] \<mu> \<down> \<omega>) \<Longrightarrow> ([[\<alpha>;; \<beta>]] \<nu> \<down> \<omega>)"
| wAssign:"\<omega> = ((\<nu> ((Inr x) := snd([\<theta>]<>\<nu>))) ((Inl x) := fst([\<theta>]<>\<nu>))) \<Longrightarrow> ([[Assign x \<theta>]] \<nu> \<down> \<omega>)"
| wChoice1[simp]:"([[\<alpha>]]\<nu> \<down> \<omega>) \<Longrightarrow> ([[Choice \<alpha> \<beta>]]\<nu> \<down> \<omega>)"
| wChoice2[simp]:"([[\<beta>]]\<nu> \<down> \<omega>) \<Longrightarrow> ([[Choice \<alpha> \<beta>]]\<nu> \<down> \<omega>)"

inductive_simps
    wpsem_Test_simps[simp]: "([[Test \<phi>]]\<nu> \<down> b)"
and wpsem_Seq_simps[simp]: "([[\<alpha>;; \<beta>]]\<nu> \<down> b)"
and wpsem_Assign_simps[simp]: "([[Assign x \<theta>]]\<nu> \<down> b)"
and wpsem_Choice_simps[simp]: "([[Choice \<alpha> \<beta>]]\<nu> \<down> b)"

lemmas real_max_mono =  Lattices.linorder_class.max.mono  
lemmas real_minus_le_minus = Groups.ordered_ab_group_add_class.neg_le_iff_le

text\<open>Interval state consists of upper and lower bounds for each real variable\<close>
inductive represents_state::"wstate \<Rightarrow> rstate \<Rightarrow> bool" (infix "REP" 10)
where REPI:"(\<And>x. (\<nu> (Inl x) \<equiv>\<^sub>L \<nu>' x) \<and> (\<nu> (Inr x) \<equiv>\<^sub>U \<nu>' x)) \<Longrightarrow> (\<nu> REP \<nu>')"

inductive_simps repstate_simps:"\<nu> REP \<nu>'"

section\<open>Soundness proofs\<close>
text\<open>Interval term valuation soundly contains real valuation\<close>
lemma trm_sound:
  fixes \<theta>::"trm"
  shows "([\<theta>]\<nu>' \<down> r) \<Longrightarrow> (\<nu> REP \<nu>') \<Longrightarrow>   ([\<theta>]<>\<nu>) \<equiv>\<^sub>P r"
proof (induction rule: rtsem.induct)
 case rtsem_Const 
   fix w r \<nu>'
   show "Rep_bword w \<equiv>\<^sub>E r \<Longrightarrow> \<nu> REP \<nu>' \<Longrightarrow> [Const w]<>\<nu> \<equiv>\<^sub>P r"
     using repU_def repL_def repP_def repe.simps rep_simps repstate_simps 
     by auto
next
 case rtsem_Var
   fix x \<nu>'
   show "\<nu> REP \<nu>' \<Longrightarrow> [Var x]<>\<nu> \<equiv>\<^sub>P \<nu>' x"
   by(auto simp add: repU_def repL_def repP_def repe.simps rep_simps repstate_simps)
next
 case rtsem_Plus
   fix \<theta>\<^sub>1 :: "trm" and \<nu>':: "rstate" and r1 and \<theta>\<^sub>2 :: "trm" and  r2
   assume rep:"\<nu> REP \<nu>'"
   assume eval1:"[\<theta>\<^sub>1]\<nu>' \<down> r1"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r1)"
   then have IH1:"[\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r1" using rep by auto
   assume eval2:"[\<theta>\<^sub>2]\<nu>' \<down> r2"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r2)"
   then have IH2:"[\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r2" using rep by auto
   obtain l1 u1 l2 u2 where 
        lu1:"(l1, u1) = ([\<theta>\<^sub>1]<> \<nu>)" 
    and lu2:"(l2, u2) = ([\<theta>\<^sub>2]<> \<nu>)"
    using IH1 IH2 repP_def by auto
   from lu1 and lu2 have
        lu1':"([\<theta>\<^sub>1]<> \<nu>) = (l1, u1)" 
    and lu2':"([\<theta>\<^sub>2]<> \<nu>) = (l2, u2)"
    by auto
  have l1:"l1 \<equiv>\<^sub>L r1" using IH1 lu1 unfolding repP_def by auto
  have u1:"u1 \<equiv>\<^sub>U r1" using IH1 lu1 unfolding repP_def by auto
  have l2:"l2 \<equiv>\<^sub>L r2" using IH2 lu2 unfolding repP_def by auto
  have u2:"u2 \<equiv>\<^sub>U r2" using IH2 lu2 unfolding repP_def by auto
  then have "([(Plus \<theta>\<^sub>1 \<theta>\<^sub>2)]<>\<nu>) = (pl l1 l2, pu u1 u2)"  
   using lu1' lu2' by auto
  have lBound:"(pl l1 l2 \<equiv>\<^sub>L r1 + r2)"
    using l1 l2 pl_lemma by auto
  have uBound:"(pu u1 u2 \<equiv>\<^sub>U r1 + r2)"
    using pu_lemma[OF u1 u2] by auto
  have "(pl l1 l2, pu u1 u2) \<equiv>\<^sub>P (r1 + r2)"
    unfolding repP_def Let_def using lBound uBound by auto
  then show"[Plus \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r1 + r2"
    using lu1' lu2' by auto
next
 case rtsem_Times
   fix \<theta>\<^sub>1 :: "trm" and \<nu>' r1 and \<theta>\<^sub>2 :: "trm" and r2
   assume eval1:"[\<theta>\<^sub>1]\<nu>' \<down> r1"
   assume eval2:"[\<theta>\<^sub>2]\<nu>' \<down> r2"
   assume rep:"\<nu> REP \<nu>'"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> ([\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r1))"
   then have IH1:"[\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r1" using rep by auto 
   assume "(\<nu> REP \<nu>' \<Longrightarrow> ([\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r2))"
   then have IH2:"[\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r2" using rep by auto
    obtain l1 u1 l2 u2 where 
        lu1:"([\<theta>\<^sub>1]<> \<nu>) = (l1, u1) " 
    and lu2:"([\<theta>\<^sub>2]<> \<nu>) = (l2, u2)"
    using IH1 IH2 repP_def by auto
  have l1:"l1 \<equiv>\<^sub>L r1" using IH1 lu1 unfolding repP_def by auto
  have u1:"u1 \<equiv>\<^sub>U r1" using IH1 lu1 unfolding repP_def by auto
  have l2:"l2 \<equiv>\<^sub>L r2" using IH2 lu2 unfolding repP_def by auto
  have u2:"u2 \<equiv>\<^sub>U r2" using IH2 lu2 unfolding repP_def by auto
  then have "([(Times \<theta>\<^sub>1  \<theta>\<^sub>2)]<>\<nu>) = (tl l1 u1 l2 u2, tu l1 u1 l2 u2)"  
   using lu1 lu2 unfolding wTimesU Let_def by auto 
  have lBound:"(tl l1 u1 l2 u2 \<equiv>\<^sub>L r1 * r2)"
    using l1 u1 l2 u2 tl_lemma by auto
  have uBound:"(tu l1 u1 l2 u2 \<equiv>\<^sub>U r1 * r2)"
    using l1 u1 l2 u2 tu_lemma by auto
  have "(tl l1 u1 l2 u2, tu l1 u1 l2 u2) \<equiv>\<^sub>P (r1 * r2)"
    unfolding repP_def Let_def using lBound uBound by auto
  then show "[Times \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r1 * r2"
    using lu1 lu2 by auto
next
 case rtsem_Max
   fix \<theta>\<^sub>1 :: "trm" and \<nu>' r1 and \<theta>\<^sub>2 :: "trm" and  r2
   assume eval1:"([\<theta>\<^sub>1]\<nu>' \<down> r1)"
   assume eval2:"([\<theta>\<^sub>2]\<nu>' \<down> r2)"
   assume rep:"\<nu> REP \<nu>'"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r1)"
   then have IH1:"[\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r1" using rep by auto
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r2)"
   then have IH2:"[\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r2" using rep by auto
   obtain l1 u1 l2 u2 where 
        lu1:"([\<theta>\<^sub>1]<> \<nu>) = (l1, u1)" 
    and lu2:"([\<theta>\<^sub>2]<> \<nu>) = (l2, u2)"
    using IH1 IH2 repP_def by auto
   from IH1 IH2 
   obtain ub1 ub2 lb1 lb2:: real 
   where urep1:"(ub1 \<ge> r1) \<and> (snd ([\<theta>\<^sub>1]<>\<nu>) \<equiv>\<^sub>E ub1)" 
   and   urep2:"(ub2 \<ge> r2) \<and> (snd ([\<theta>\<^sub>2]<>\<nu>) \<equiv>\<^sub>E ub2)"
   and   lrep1:"(lb1 \<le> r1) \<and> (fst ([\<theta>\<^sub>1]<>\<nu>) \<equiv>\<^sub>E lb1)" 
   and   lrep2:"(lb2 \<le> r2) \<and> (fst ([\<theta>\<^sub>2]<>\<nu>) \<equiv>\<^sub>E lb2)"
     using repP_def repU_def repL_def by auto
   have lbound:"wmax l1 l2 \<equiv>\<^sub>L max r1 r2"
     by (metis dual_order.trans fst_conv le_cases lrep1 lrep2 lu1 lu2 max_def repL_def wmax.elims)
   have ubound:"wmax u1 u2 \<equiv>\<^sub>U max r1 r2"     
     by (metis real_max_mono lu1 lu2 repU_def snd_conv urep1 urep2 wmax_lemma)
   have "([trm.Max \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu>) = (wmax l1 l2, wmax u1 u2)"
     using lu1 lu2 unfolding wMaxU Let_def 
     by (simp)
   then show "[trm.Max \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P max r1 r2"
    unfolding repP_def
    using lbound ubound lu1 lu2 by auto
next
  case rtsem_Min
    fix \<theta>\<^sub>1 :: "trm" and \<nu>' r1 and \<theta>\<^sub>2 :: "trm" and  r2
   assume eval1:"([\<theta>\<^sub>1]\<nu>' \<down> r1)"
   assume eval2:"([\<theta>\<^sub>2]\<nu>' \<down> r2)"
   assume rep:"\<nu> REP \<nu>'"
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r1)"
   then have IH1:"[\<theta>\<^sub>1]<>\<nu> \<equiv>\<^sub>P r1" using rep by auto
   assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r2)"
   then have IH2:"[\<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P r2" using rep by auto
   obtain l1 u1 l2 u2 where 
        lu1:"([\<theta>\<^sub>1]<> \<nu>) = (l1, u1)" 
    and lu2:"([\<theta>\<^sub>2]<> \<nu>) = (l2, u2)"
    using IH1 IH2 repP_def by auto
   from IH1 IH2 
   obtain ub1 ub2 lb1 lb2:: real 
   where urep1:"(ub1 \<ge> r1) \<and> (snd ([\<theta>\<^sub>1]<>\<nu>) \<equiv>\<^sub>E ub1)" 
   and   urep2:"(ub2 \<ge> r2) \<and> (snd ([\<theta>\<^sub>2]<>\<nu>) \<equiv>\<^sub>E ub2)"
   and   lrep1:"(lb1 \<le> r1) \<and> (fst ([\<theta>\<^sub>1]<>\<nu>) \<equiv>\<^sub>E lb1)" 
   and   lrep2:"(lb2 \<le> r2) \<and> (fst ([\<theta>\<^sub>2]<>\<nu>) \<equiv>\<^sub>E lb2)"
     using prod.case_eq_if repP_def  repU_def repL_def by auto
   have lbound:"wmin l1 l2 \<equiv>\<^sub>L min r1 r2"
     by (metis fst_conv lrep1 lrep2 lu1 lu2 min.mono repL_def wmin_lemma)
   have ubound:"wmin u1 u2 \<equiv>\<^sub>U min r1 r2"     
     using lu1 lu2 min_le_iff_disj repU_def urep1 urep2 by auto
   have "([Min \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu>) = (wmin l1 l2, wmin u1 u2)"
     using lu1 lu2 unfolding wMinU Let_def by auto
  then show "[Min \<theta>\<^sub>1 \<theta>\<^sub>2]<>\<nu> \<equiv>\<^sub>P min r1 r2"
    unfolding repP_def
    using lbound ubound lu1 lu2 by auto
next
  case rtsem_Neg
  fix \<theta> :: "trm" and \<nu>' r
  assume eval:"[\<theta>]\<nu>' \<down> r"
  assume rep:"\<nu> REP \<nu>'"
  assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>]<>\<nu> \<equiv>\<^sub>P r)"
  then have IH:"[\<theta>]<>\<nu> \<equiv>\<^sub>P r" using rep by auto
  obtain l1 u1  where 
        lu:"([\<theta>]<> \<nu>) = (l1, u1)" 
    using IH repP_def by auto
  from IH 
  obtain ub lb:: real 
   where urep:"(ub \<ge> r) \<and> (snd ([\<theta>]<>\<nu>) \<equiv>\<^sub>E ub)" 
   and   lrep:"(lb \<le> r) \<and> (fst ([\<theta>]<>\<nu>) \<equiv>\<^sub>E lb)" 
    using  repP_def repU_def repL_def by auto
  have ubound:"((wneg u1) \<equiv>\<^sub>L (uminus r))"
    by (metis real_minus_le_minus lu repL_def snd_conv urep wneg_lemma)
  have lbound:"((wneg l1) \<equiv>\<^sub>U (uminus r))"
    using real_minus_le_minus lu repU_def lrep wneg_lemma
    by (metis fst_conv)
  show "[Neg \<theta>]<>\<nu> \<equiv>\<^sub>P - r"
    unfolding repP_def Let_def using ubound lbound lu 
    by (auto)
next
  case rtsem_Abs
  fix \<theta> :: "trm" and \<nu>' r
  assume eval:"[\<theta>]\<nu>' \<down> r"
  assume rep:"\<nu> REP \<nu>'"
  assume "(\<nu> REP \<nu>' \<Longrightarrow> [\<theta>]<>\<nu> \<equiv>\<^sub>P r)"
  then have IH:"[\<theta>]<>\<nu> \<equiv>\<^sub>P r" using rep by auto
  obtain l1 u1  where 
        lu:"([\<theta>]<> \<nu>) = (l1, u1)" 
    using IH repP_def by auto
  from IH 
  obtain ub lb:: real 
   where urep:"(ub \<ge> r) \<and> (snd ([\<theta>]<>\<nu>) \<equiv>\<^sub>E ub)" 
   and   lrep:"(lb \<le> r) \<and> (fst ([\<theta>]<>\<nu>) \<equiv>\<^sub>E lb)" 
    using prod.case_eq_if repP_def  repU_def repL_def by auto
  have lbound:"wmax l1 (wneg u1) \<equiv>\<^sub>L (abs r)"
    apply(simp only: repL_def)
    apply(rule exI[where x="max lb (- ub)"])
    apply(rule conjI)  
    using lrep wmax_lemma lu urep wneg_lemma by auto
  have ubound:"(wmax u1 (wneg l1) \<equiv>\<^sub>U (abs r))"
    apply(simp only: repU_def)
    apply(rule exI[where x="max ub (- lb)"])
    using lrep wmax_lemma lu urep wneg_lemma by auto 
  show "[Abs \<theta>]<>\<nu> \<equiv>\<^sub>P abs r"
    using repP_def Let_def ubound lbound lu lu wAbsU by auto
qed

text\<open>Every word represents some real\<close>
lemma word_rep:"\<And>bw::bword. \<exists>r::real. Rep_bword bw \<equiv>\<^sub>E r"
proof -
  fix bw
  obtain w where weq:"w = Rep_bword bw" by auto
  have negInfCase:"w = NEG_INF \<Longrightarrow> ?thesis bw"
   apply(rule exI[where x="-((2 ^ 31) -1)"])
    using weq by (auto simp add: repe.simps)
  have posInfCase:"w = POS_INF \<Longrightarrow> ?thesis bw"
    apply(rule exI[where x="((2 ^ 31) -1)"])
    using weq by (auto simp add: repe.simps)
  have boundU:"w \<noteq> NEG_INF \<Longrightarrow> w \<noteq> POS_INF \<Longrightarrow> sint (Rep_bword bw) < sint POS_INF"
    using Rep_bword weq
    by (metis (no_types, lifting) mem_Collect_eq min.absorb_iff2 min_def not_le 
        Word.word_sint.Rep_eqD)
  have boundL:"w \<noteq> NEG_INF \<Longrightarrow> w \<noteq> POS_INF \<Longrightarrow> sint NEG_INF < sint (Rep_bword bw)"
    using Rep_bword weq
    by (metis (no_types, lifting) mem_Collect_eq min.absorb_iff2 min_def not_le 
        Word.word_sint.Rep_eqD)
  have intCase:"w \<noteq> NEG_INF \<Longrightarrow> w \<noteq> POS_INF \<Longrightarrow> ?thesis bw"
    apply(rule exI[where x=" (real_of_int (sint (Rep_bword bw)))"])
    apply(rule repINT)
    using boundU boundL by(auto)
  then show "?thesis bw"
    apply(cases "w = POS_INF")
     apply(cases "w = NEG_INF")
      using posInfCase intCase negInfCase by auto
  qed

text\<open>Every term has a value\<close>
lemma eval_tot:"(\<exists>r. ([\<theta>::trm]\<nu>' \<down> r))"
proof (induction "\<theta>")
qed (auto simp add: Min_def word_rep bword_neg_one_def, blast?)

text\<open>Interval formula semantics soundly implies real semantics\<close>
lemma fml_sound:
  fixes \<phi>::"formula" and \<nu>::"wstate"
  shows "(wfsem \<phi> \<nu> b) \<Longrightarrow>  (\<nu> REP \<nu>') \<Longrightarrow> (rfsem \<phi> \<nu>'  b)"
proof (induction arbitrary: \<nu>' rule: wfsem.induct)
case (wGreaterT t1 v t2 w)
  assume wle:"wgreater (fst ([t1]<>v)) (snd ([t2]<>v))"
  assume rep:"v REP w" 
  obtain r1 and r2 where eval1:"[t1]w \<down> r1" and  eval2:"[t2]w \<down> r2"
    using eval_tot[of t1 w] eval_tot[of t2 w] by (auto)
  note rep1 = trm_sound[of t1 w r1, where \<nu>=v, OF eval1 rep]
  note rep2 = trm_sound[of t2 w r2, where \<nu>=v, OF eval2 rep]
  show "[Greater t1 t2]w \<downharpoonright> True"
    apply(rule rGreaterT[where ?r1.0 = r1, where ?r2.0 = r2]) 
    prefer 3
    apply(rule wgreater_lemma[where ?w1.0="fst([t1]<> v)", where ?w2.0="snd([t2]<> v)"])
    using rep1 rep2 wle repP_def repL_def repU_def  eval1 eval2 
    by ((simp add: prod.case_eq_if | blast)+)
next
  case (wGreaterF t2 v t1 v')
  assume wl:"wgeq (fst ([t2]<>v)) (snd ([t1]<>v))"
  assume rep:"v REP v'"
  obtain r1 r2:: real
  where eval1:"(rtsem t1 v' r1)" and  
    eval2:"rtsem t2 v' r2"
    using eval_tot[of t1 v'] eval_tot[of t2 v']  by (auto)
  note rep1 = trm_sound[of t1 v' r1, where \<nu>=v, OF eval1 rep]
  note rep2 = trm_sound[of t2 v' r2, where \<nu>=v, OF eval2 rep]
  show "[Greater t1 t2]v' \<downharpoonright> False"
    apply(rule rGreaterF [of t1 v' r1 t2 r2])
    apply(rule eval1)
     apply(rule eval2)
    apply(rule wgeq_lemma[where ?w1.0="fst([t2]<> v)", where ?w2.0="snd([t1]<> v)"])
    using rep1 rep2 repP_def wgeq_lemma wl rep
    by auto
next
  case (wGeqT t1 v t2 v')
  assume a1:"wgeq (fst ([t1]<>v)) (snd ([t2]<>v))"
  assume rep:"v REP v'"
  obtain r1 r2:: real
  where eval1:"(rtsem t1 v' r1)" and  
    eval2:"rtsem t2 v' r2"
    using eval_tot[of t1 v'] eval_tot[of t2 v']  by (auto)
  note rep1 = trm_sound[of t1 v' r1, where \<nu>=v, OF eval1 rep]
  note rep2 = trm_sound[of t2 v' r2, where \<nu>=v, OF eval2 rep]
  show "[Geq t1 t2]v' \<downharpoonright> True"
    apply(rule rGeqT)
      apply(rule eval1)
    apply(rule eval2)
  using wgeq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using wgreater_lemma prod.case_eq_if a1
  by auto
next
  case (wGeqF t2 v t1 v')
  assume a1:"wgreater (fst ([t2]<>v)) (snd ([t1]<>v))"
  assume rep:"v REP v'"
  obtain r1 r2:: real
  where eval1:"(rtsem t1 v' r1)" and  
    eval2:"rtsem t2 v'  r2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by (auto)
  note rep1 = trm_sound[of t1 v' r1, where \<nu>=v, OF eval1 rep]
  note rep2 = trm_sound[of t2 v' r2, where \<nu>=v, OF eval2 rep]
  show "[Geq t1 t2]v' \<downharpoonright> False"
    apply(rule rGeqF, rule eval1, rule eval2)
  using wgeq_lemma eval1 eval2 rep1 rep2 unfolding repP_def Let_def
  using wgreater_lemma rGreaterF prod.case_eq_if a1 rGreaterF by auto
next
  case (wEqualsT t2 v t1 v')
  assume eq1:"fst ([t2]<>v) = snd ([t2]<>v)"
  assume eq2:"snd ([t2]<>v) = snd ([t1]<>v)"
  assume eq3:"snd ([t1]<>v) = fst ([t1]<>v)"
  assume rep:"v REP v'"  
  assume neq1:"fst ([t2]<>v) \<noteq> NEG_INF"
  assume neq2:"fst ([t2]<>v) \<noteq> POS_INF"
  obtain r1 r2:: real
  where eval1:"(rtsem t1 v' r1)" and  
        eval2:"rtsem t2 v'  r2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by (auto)
  note rep1 = trm_sound[of t1 v' r1, where \<nu>=v, OF eval1 rep]
  note rep2 = trm_sound[of t2 v' r2, where \<nu>=v, OF eval2 rep]
  show "[Equals t1 t2]v' \<downharpoonright> True"
    apply(rule rEqualsT, rule eval1, rule eval2)
    using eq1 eq2 eq3 eval1 eval2 rep1 rep2
    unfolding repP_def Let_def repL_def repU_def repe.simps using neq1 neq2 by auto
next
  case (wEqualsF1 t1 v t2 v')
  assume wle:"wgreater (fst ([t1]<>v)) (snd ([t2]<>v))"
  assume rep:"v REP v'"
  obtain r1 r2:: real
  where eval1:"(rtsem t1 v' r1)" and  
    eval2:"rtsem t2 v'  r2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by (auto)
  note rep1 = trm_sound[of t1 v' r1, where \<nu>=v, OF eval1 rep]
  note rep2 = trm_sound[of t2 v' r2, where \<nu>=v, OF eval2 rep]
  show "[Equals t1 t2]v' \<downharpoonright> False"
  apply(rule rEqualsF, rule eval1, rule eval2)
    using wgeq_lemma eval1 eval2 rep1 rep2 wgreater_lemma rGreaterF  prod.case_eq_if wle
    unfolding repP_def
    by (metis (no_types, lifting) less_irrefl) 
next
  case (wEqualsF2 t2 v t1 v')
  assume wle:"wgreater (fst ([t2]<>v)) (snd ([t1]<>v))"
  assume rep:"v REP v'"
  obtain r1 r2:: real
  where eval1:"(rtsem t1 v' r1)" and  
    eval2:"rtsem t2 v'  r2"
    using eval_tot[of t1 v'] eval_tot[of t2 v'] by (auto)
  note rep1 = trm_sound[of t1 v' r1, where \<nu>=v, OF eval1 rep]
  note rep2 = trm_sound[of t2 v' r2, where \<nu>=v, OF eval2 rep]
  show "[Equals t1 t2]v' \<downharpoonright> False"
    apply(rule rEqualsF, rule eval1, rule eval2)
    using wgeq_lemma eval1 eval2 rep1 rep2  wgreater_lemma rGreaterF prod.case_eq_if wle
    unfolding repP_def
    by (metis (no_types, lifting) less_irrefl)
qed (auto)
  
lemma rep_upd:"\<omega> = (\<nu>(Inr x := snd([\<theta>]<>\<nu>)))(Inl x := fst([\<theta>]<>\<nu>))
\<Longrightarrow> \<nu> REP \<nu>' \<Longrightarrow> ([\<theta>::trm]\<nu>' \<down> r) \<Longrightarrow> \<omega> REP \<nu>'(x := r)"
  apply(rule REPI)
  apply(rule conjI)
   apply(unfold repL_def)
   using trm_sound prod.case_eq_if repP_def repstate_simps repL_def 
   apply(metis (no_types, lifting) Inl_Inr_False fun_upd_apply sum.inject(1))
  using repP_def repstate_simps repU_def
  apply(auto simp add: repU_def)
  by (metis (full_types) surjective_pairing trm_sound)

text\<open>Interval program semantics soundly contains real semantics existentially\<close>
theorem interval_program_sound:
  fixes \<alpha>::"prog"
  shows "([[\<alpha>]] \<nu> \<down> \<omega>)  \<Longrightarrow> \<nu> REP \<nu>' \<Longrightarrow> (\<exists>\<omega>'. (\<omega> REP \<omega>') \<and> ([\<alpha>] \<nu>' \<downharpoonleft> \<omega>'))"
proof (induction arbitrary: \<nu>' rule: wpsem.induct)
  case (wTest \<phi> \<nu> \<omega> \<nu>') 
  assume sem:"[[\<phi>]]\<nu> \<down> True"
  and eq:"\<nu> = \<omega>"
  and rep:"\<nu> REP \<nu>'"
  show ?case 
    apply(rule exI[where x=\<nu>'])
    using sem rep by (auto simp add: eq fml_sound rep)
next
  case (wAssign \<omega> \<nu> x \<theta> \<nu>') 
  assume eq:"\<omega> = \<nu>(Inr x := snd ([\<theta>]<>\<nu>), Inl x := fst ([\<theta>]<>\<nu>))"
  and rep:"\<nu> REP \<nu>'"
  obtain r::real where eval:"([\<theta>::trm]\<nu>' \<down> r)" using eval_tot  by auto
  show ?case 
    apply(rule exI[where x="\<nu>'(x := r)"])
    apply(rule conjI)
    apply(rule rep_upd[OF eq rep eval])
    apply auto
    apply(rule exI[where x=r])
    by (auto simp add: eval)
next case (wSeq \<alpha> \<nu> \<mu> \<beta> \<omega> \<nu>') then show ?case by (simp, blast)
next case (wChoice1 a v w b v') then show ?case by auto
next case (wChoice2 a v w b v') then show ?case by auto
qed

end