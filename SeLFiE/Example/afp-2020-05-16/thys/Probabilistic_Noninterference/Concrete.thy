section \<open>Concrete setting\<close>

theory Concrete
imports Syntactic_Criteria
begin

(* We instatiate the parameters according to Examples 1 and 2 from the paper. *)

(* Security levels: *)
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
type_synonym choice = "real + test"
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

fun cval where
 "cval (Inl p) s = min 1 (max 0 p)"
|"cval (Inr tst) s = (if tval tst s then 1 else 0)"

definition indis :: "(state * state) set"where
"indis \<equiv> {(s,t). ALL x. sec x = Lo \<longrightarrow> s x = t x}"

interpretation Example_PL: PL_Indis aval tval cval indis
proof
  fix ch :: choice and  s show "0 \<le> cval ch s \<and> cval ch s \<le> 1"
    by (cases ch) auto
next
  show "equiv UNIV indis"
    unfolding refl_on_def sym_def trans_def equiv_def indis_def by auto
qed

(* The security level of expressions: *)
fun exprSec where
 "exprSec (Ct n) = Lo"
|"exprSec (Var x) = sec x"
|"exprSec (Plus e1 e2) = sup (exprSec e1) (exprSec e2)"
|"exprSec (Minus e1 e2) = sup (exprSec e1) (exprSec e2)"

(* The security level of tests: *)
fun tstSec where
 "tstSec Tr = Lo"
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

(* Stateless choices are always compatible: *)
lemma compatPrchSyntactic[simp]: "Example_PL.compatCh (Inl p)"
  unfolding Example_PL.compatCh_def by auto

(* A test-choice is compatible iff its test is compatible: *)
lemma compatIfchSyntactic[simp]: "Example_PL.compatCh (Inr tst) \<longleftrightarrow> Example_PL.compatTst tst"
  unfolding Example_PL.compatCh_def Example_PL.compatTst_def by auto

abbreviation Ch_half ("Ch\<^sub>\<onehalf>") where "Ch\<^sub>\<onehalf> \<equiv> Ch (Inl (1/2))"
abbreviation If where "If tst \<equiv> Ch (Inr tst)"

abbreviation "siso c \<equiv> Example_PL.siso c"
abbreviation "discr c \<equiv> Example_PL.discr c"
abbreviation Sbis_abbrev (infix "\<approx>s" 55) where "c1 \<approx>s c2 \<equiv> (c1,c2) \<in> Example_PL.Sbis"
abbreviation ZObis_abbrev (infix "\<approx>01" 55) where "c1 \<approx>01 c2 \<equiv> (c1,c2) \<in> Example_PL.ZObis"

abbreviation "SC_siso c \<equiv> Example_PL.SC_siso c"
abbreviation "SC_discr c \<equiv> Example_PL.SC_discr c"
abbreviation "SC_Sbis c \<equiv> Example_PL.SC_Sbis c"
abbreviation "SC_ZObis c \<equiv> Example_PL.SC_ZObis c"

lemma "SC_discr (h ::= Ct 0)"
  by (simp add: Example_PL.SC_discr.simps)


subsection \<open>The secure programs from the paper's Example 3\<close>

definition [simp]: "d0 =
  h' ::= Ct 0 ;;
  While (Gt (Var h) (Ct 0))
    (Ch\<^sub>\<onehalf> (h ::= Ct 0)
         (h' ::= Plus (Var h') (Ct 1)))"

definition [simp]: "d1 =
  While (Gt (Var h) (Ct 0))
    (Ch\<^sub>\<onehalf> (h ::= Minus (Var h) (Ct 1))
         (h ::= Plus (Var h) (Ct 1)))"

definition [simp]: "d2 =
  If (Eq (Var l) (Ct 0))
    (l' ::= Ct 1)
    d0"

definition [simp]: "d3 =
  h ::= Ct 5 ;;
  ParT [d0, (l ::= Ct 1)]"

(* The syntactic criteria are checked automatically: *)
theorem "SC_discr d0"
        "SC_discr d1"
        "SC_Sbis d2"
        "SC_ZObis d2"
  by (auto simp: Example_PL.SC_discr.simps Example_PL.SC_Sbis.simps Example_PL.SC_ZObis.simps)

(* Alternatively, the semantic notions follow directly from the compositionality facts
used as intro rules: *)
theorem "discr d0"
        "discr d1"
        "d2 \<approx>s d2"
        "d3 \<approx>01 d3"
  by (auto intro!: compatAtmSyntactic
                   Example_PL.ZObis Example_PL.proper_intros
                   Example_PL.Atm_Sbis)


end
