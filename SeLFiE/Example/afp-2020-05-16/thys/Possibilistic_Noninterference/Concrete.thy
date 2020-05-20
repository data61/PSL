section \<open>Concrete setting\<close>

theory Concrete 
imports Syntactic_Criteria After_Execution
begin

lemma (in PL_Indis) WbisT_If_cross:
  assumes "c1 \<approx>wT c2" "c1 \<approx>wT c1" "c2 \<approx>wT c2"
  shows "(If tst c1 c2) \<approx>wT (If tst c1 c2)"
proof -
  define \<phi>
    where "\<phi> c d \<longleftrightarrow> (\<exists>c1' c2'. c = If tst c1' c2' \<and> d = If tst c1' c2' \<and> c1' \<approx>wT c2' \<and> c1' \<approx>wT c1' \<and> c2' \<approx>wT c2')"
    for c d
  with assms have "\<phi> (If tst c1 c2) (If tst c1 c2)" by auto
  then show ?thesis
  proof (induct rule: WbisT_coinduct[where \<phi>=\<phi>])
    case (cont c s d t c' s')
    note cont(2,3)
    moreover from cont obtain c1 c2
      where \<phi>: "c = If tst c1 c2" "d = If tst c1 c2" "c1 \<approx>wT c2" "c1 \<approx>wT c1" "c2 \<approx>wT c2"
      by (auto simp: \<phi>_def)
    moreover then have "c2 \<approx>wT c1"
      using WbisT_sym unfolding sym_def by blast
    ultimately have "(d, t) \<rightarrow>*c (if tval tst t then c1 else c2, t) \<and> s' \<approx> t \<and>
      (\<phi> c' (if tval tst t then c1 else c2) \<or> c' \<approx>wT (if tval tst t then c1 else c2))"
      by (auto simp: \<phi>_def)
    then show ?case by auto
  qed (auto simp: \<phi>_def)
qed

text\<open>

We instatiate the following notions, kept generic so far:

\begin{itemize}
  \item On the language syntax: 
  \begin{itemize}
    \item atoms, tests and states just like at the possibilistic case; 
    \item choices, to either if-choices (based on tests) or binary fixed-probability choices; 
    \item the schedulers, to the uniform one
  \end{itemize}
  \item On the security semantics, the lattice of levels and the indis relation, again, just like at the possibilistic case. 
\end{itemize}
\<close>

datatype level = Lo | Hi

lemma [simp]: "\<And> l. l \<noteq> Hi \<longleftrightarrow> l = Lo" and 
      [simp]: "\<And> l. Hi \<noteq> l \<longleftrightarrow> Lo = l" and 
      [simp]: "\<And> l. l \<noteq> Lo \<longleftrightarrow> l = Hi" and 
      [simp]: "\<And> l. Lo \<noteq> l \<longleftrightarrow> Hi = l"
by (metis level.exhaust level.simps(2))+

lemma [dest]: "\<And> l A. \<lbrakk>l \<in> A; Lo \<notin> A\<rbrakk> \<Longrightarrow> l = Hi" and 
      [dest]: "\<And> l A. \<lbrakk>l \<in> A; Hi \<notin> A\<rbrakk> \<Longrightarrow> l = Lo"
by (metis level.exhaust)+

declare level.split[split]

instantiation level :: complete_lattice
begin
  definition top_level: "top \<equiv> Hi"
  definition bot_level: "bot \<equiv> Lo"
  definition inf_level: "inf l1 l2 \<equiv> if Lo \<in> {l1,l2} then Lo else Hi"
  definition sup_level: "sup l1 l2 \<equiv> if Hi \<in> {l1,l2} then Hi else Lo"
  definition less_eq_level: "less_eq l1 l2 \<equiv> (l1 = Lo \<or> l2 = Hi)"
  definition less_level: "less l1 l2 \<equiv> l1 = Lo \<and> l2 = Hi"
  definition Inf_level: "Inf L \<equiv> if Lo \<in> L then Lo else Hi"
  definition Sup_level: "Sup L \<equiv> if Hi \<in> L then Hi else Lo"
instance
  proof qed (auto simp: top_level bot_level inf_level sup_level
                        less_eq_level less_level Inf_level Sup_level)
end

lemma sup_eq_Lo[simp]: "sup a b = Lo \<longleftrightarrow> a = Lo \<and> b = Lo"
  by (auto simp: sup_level)

datatype var = h | h' | l | l'
datatype exp = Ct nat | Var var | Plus exp exp | Minus exp exp
datatype test = Tr | Eq exp exp | Gt exp exp | Non test
datatype atom = Assign var exp
type_synonym state = "var \<Rightarrow> nat"
 
syntax
 "_assign" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("_ ::= _" [1000, 61] 61)

translations
  "x ::= expr" == "CONST Atm (CONST Assign x expr)"
 
primrec sec where
  "sec h  = Hi"
| "sec h' = Hi"
| "sec l  = Lo"
| "sec l' = Lo"

fun eval where 
 "eval (Ct n) s = n"
|"eval (Var x) s = s x"
|"eval (Plus e1 e2) s = eval e1 s + eval e2 s"
|"eval (Minus e1 e2) s = eval e1 s - eval e2 s"

fun tval where 
 "tval Tr s = True"
|"tval (Eq e1 e2) s = (eval e1 s = eval e2 s)"
|"tval (Gt e1 e2) s = (eval e1 s > eval e2 s)"
|"tval (Non e) s = (\<not> tval e s)"

fun aval where 
"aval (Assign x e) s = (s (x := eval e s))"

definition indis :: "(state * state) set"where 
"indis \<equiv> {(s,t). ALL x. sec x = Lo \<longrightarrow> s x = t x}"

interpretation Example_PL: PL_Indis tval aval indis
proof
  show "equiv UNIV indis"
    unfolding refl_on_def sym_def trans_def equiv_def indis_def by auto
qed

fun exprSec where 
 "exprSec (Ct n) = bot"
|"exprSec (Var x) = sec x"
|"exprSec (Plus e1 e2) = sup (exprSec e1) (exprSec e2)"
|"exprSec (Minus e1 e2) = sup (exprSec e1) (exprSec e2)"

fun tstSec where 
 "tstSec Tr = bot"
|"tstSec (Eq e1 e2) = sup (exprSec e1) (exprSec e2)"
|"tstSec (Gt e1 e2) = sup (exprSec e1) (exprSec e2)"
|"tstSec (Non e) = tstSec e"

lemma exprSec_Lo_eval_eq: "exprSec expr = Lo \<Longrightarrow> (s, t) \<in> indis \<Longrightarrow> eval expr s = eval expr t"
  by (induct expr) (auto simp: indis_def)

lemma compatAtmSyntactic[simp]: "exprSec expr = Lo \<or> sec v = Hi \<Longrightarrow> Example_PL.compatAtm (Assign v expr)"
  unfolding Example_PL.compatAtm_def
  by (induct expr)
     (auto simp: indis_def intro!: arg_cong2[where f="(+)"] arg_cong2[where f="(-)"] exprSec_Lo_eval_eq)

lemma presAtmSyntactic[simp]: "sec v = Hi \<Longrightarrow> Example_PL.presAtm (Assign v expr)"
  unfolding Example_PL.presAtm_def by (simp add: indis_def)

lemma compatTstSyntactic[simp]: "tstSec tst = Lo \<Longrightarrow> Example_PL.compatTst tst"
  unfolding Example_PL.compatTst_def
  by (induct tst)
     (simp_all, safe del: iffI
              intro!: arg_cong2[where f="(=)"] arg_cong2[where f="(<) :: nat \<Rightarrow> nat \<Rightarrow> bool"] exprSec_Lo_eval_eq)

lemma "Example_PL.SC_discr (h ::= Ct 0)"
  by (simp add: Example_PL.SC_discr.simps)

abbreviation "siso c \<equiv> Example_PL.siso c"
abbreviation "siso0 c \<equiv> Example_PL.siso0 c"
abbreviation "discr c \<equiv> Example_PL.discr c"
abbreviation "discr0 c \<equiv> Example_PL.discr0 c"
abbreviation Sbis_abbrev (infix "\<approx>s" 55) where "c1 \<approx>s c2 \<equiv> (c1,c2) \<in> Example_PL.Sbis"
abbreviation ZObis_abbrev (infix "\<approx>01" 55) where "c1 \<approx>01 c2 \<equiv> (c1,c2) \<in> Example_PL.ZObis"
abbreviation ZObisT_abbrev (infix "\<approx>01T" 55) where "c1 \<approx>01T c2 \<equiv> (c1,c2) \<in> Example_PL.ZObisT"
abbreviation Wbis_abbrev (infix "\<approx>w" 55) where "c1 \<approx>w c2 \<equiv> (c1,c2) \<in> Example_PL.Wbis"
abbreviation WbisT_abbrev (infix "\<approx>wT" 55) where "c1 \<approx>wT c2 \<equiv> (c1,c2) \<in> Example_PL.WbisT"
abbreviation BisT_abbrev (infix "\<approx>T" 55) where "c1 \<approx>T c2 \<equiv> (c1,c2) \<in> Example_PL.BisT"

subsection \<open>Programs from EXAMPLE 1\<close>

definition [simp]: "c0 = (h ::= Ct 0)"

definition [simp]: "c1 = (if Eq (Var l) (Ct 0) then h ::= Ct 1 else l ::= Ct 2)"

definition [simp]: "c2 = (if Eq (Var h) (Ct 0) then h ::= Ct 1 else h ::= Ct 2)"

definition [simp]: "c3 = (if Eq (Var h) (Ct 0) then h ::= Ct 1 ;; h ::= Ct 2
                                         else h ::= Ct 3)"

definition [simp]: "c4 = l ::= Ct 4 ;; c3"

definition [simp]: "c5 = c3 ;; l ::= Ct 4"

definition [simp]: "c6 = l ::= Var h"

definition [simp]: "c7 = l ::= Var h ;; l ::= Ct 0"

definition [simp]: "c8 = h' ::= Var h ;;
  while Gt (Var h) (Ct 0) do (h ::= Minus (Var h) (Ct 1) ;; h' ::= Plus (Var h') (Ct 1)) ;;
  l ::= Ct 4"

definition [simp]: "c9 = c7 | l' ::= Var l"

definition [simp]: "c10 = c5 | l ::= Ct 5"

definition [simp]: "c11 = c8 | l ::= Ct 5"

declare bot_level[iff]

theorem c0: "siso c0" "discr c0"
  by auto

theorem c1: "siso c1" "c1 \<approx>s c1"
  by auto

theorem c2: "discr c2"
  by auto

theorem Sbis_c2: "c2 \<approx>s c2"
  oops

theorem c3: "discr c3"
  by auto

theorem c4: "c4 \<approx>01 c4"
  by auto

theorem c5: "c5 \<approx>w c5"
  by auto

text\<open>Example 4 from the paper\<close>

theorem "c3 \<approx>wT c3" by auto

theorem "c5 \<approx>wT c5" by auto

corollary "discr (while Eq (Var h) (Ct 0)  do h ::= Ct 0)"
  by auto

text\<open>Example 5 from the paper\<close>

definition [simp]: "c12 \<equiv> h ::= Ct 4 ;;
  while Gt (Var h) (Ct 0)
    do (h ::= Minus (Var h) (Ct 1) ;; h' ::= Plus (Var h') (Ct 1)) ;;
  l ::= Ct 1"

corollary "(c12 | l ::= Ct 2) \<approx>T (c12 | l ::= Ct 2)"
  by auto

definition [simp]: "c13 =
  (if Eq (Var h) (Ct 0) then h ::= Ct 1 ;; l ::= Ct 2 else l ::= Ct 2) ;; l' ::= Ct 4"

lemma c13_inner:
  "(h ::= Ct 1 ;; l ::= Ct 2) \<approx>wT (l ::= Ct 2)"
proof -
  define \<phi> where "\<phi> =
    (\<lambda>(c :: (test, atom) com) (d :: (test, atom) com).
      c = h ::= Ct 1 ;; l ::= Ct 2 \<and> d = l ::= Ct 2 \<or>
      d = h ::= Ct 1 ;; l ::= Ct 2 \<and> c = l ::= Ct 2)"
  then have "\<phi> (h ::= Ct 1 ;; l ::= Ct 2) (l ::= Ct 2)"
    by auto
  then show ?thesis
  proof (induct rule: Example_PL.WbisT_coinduct[where \<phi>=\<phi>])
    case sym then show ?case by (auto simp add: \<phi>_def)
  next
    case (cont c s d t c' s') then show ?case
      by (auto simp add: \<phi>_def intro!: exI[of _ "l ::= Ct 2"] exI[of _ t])
         (auto simp: indis_def)
  next
    have exec:
        "\<And>t. Example_PL.MtransT (h ::= Ct 1 ;; l ::= Ct 2, t) (aval (Assign l (Ct 2)) (aval (Assign h (Ct 1)) t))"
        by (simp del: aval.simps)
           (blast intro: Example_PL.transC_MtransT Example_PL.transC_MtransC.SeqT Example_PL.transT.Atm Example_PL.transT_MtransT)
    case (termi c s d t s') with exec show ?case
      by (auto simp add: \<phi>_def intro!: exI[of _ "t (h := 1, l := 2)"])
         (auto simp: indis_def)
  qed
qed

theorem "c13 \<approx>wT c13"
   using c13_inner
   by (auto intro!: Example_PL.Seq_WbisT Example_PL.WbisT_If_cross)

end
