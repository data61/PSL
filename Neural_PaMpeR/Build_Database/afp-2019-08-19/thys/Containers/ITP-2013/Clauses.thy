theory Clauses imports
  Main
  Containers.Containers
begin

type_synonym literal = "nat \<times> bool"
type_synonym clause = "literal set"
type_synonym cnf = "clause set"

datatype bexp
  = Var nat
  | not bexp
  | Or bexp bexp (infixl "or" 110)
  | And bexp bexp (infixl "and" 120)

declare [[coercion Var]] [[coercion_enabled]]

declare SUP_cong_simp[fundef_cong del]
function cnf :: "bexp \<Rightarrow> cnf"
where
  "cnf v = {{(v, True)}}"
| "cnf (b and b') = cnf b \<union> cnf b'"
| "cnf (b or b') = (\<Union>c \<in> cnf b. (\<lambda>c'. c \<union> c') ` cnf b')"
| "cnf (not v) = {{(v, False)}}"
| "cnf (not (not b)) = cnf b"
| "cnf (not (b and b')) = cnf (not b or not b')"
| "cnf (not (b or b')) = cnf (not b and not b')"
by pat_completeness simp_all
termination by(relation "measure (rec_bexp (\<lambda>_. 1) (\<lambda>_ n. 3 * n + 1) (\<lambda>_ _ n m. n + m + 1) (\<lambda>_ _ n m. n + m + 1))") simp_all
declare SUP_cong_simp[fundef_cong]

definition test 
where 
  "test = 
  (1 and 2) or (not 1 and not 2) or
  (3 and 4) or (not 3 and not 4) or
  (5 and 6) or (not 5 and not 6) or
  (7 and 8) or (not 7 and not 8) or
  (9 and 10) or (not 9 and not 10) or
  (11 and 12) or (not 11 and not 12) or
  (1 and 2) or (3 and 4) or
  (1 and 3) or (2 and 4)"

value "cnf test = {}"

text \<open>Sanity check for correctness\<close>

type_synonym env = "nat \<Rightarrow> bool"

primrec eval_bexp :: "env \<Rightarrow> bexp \<Rightarrow> bool" ("_ \<Turnstile> _" [100, 100] 70)
where
  "\<Phi> \<Turnstile> v \<longleftrightarrow> \<Phi> v"
| "\<Phi> \<Turnstile> not b \<longleftrightarrow> \<not> \<Phi> \<Turnstile> b"
| "\<Phi> \<Turnstile> b and b' \<longleftrightarrow> \<Phi> \<Turnstile> b \<and> \<Phi> \<Turnstile> b'"
| "\<Phi> \<Turnstile> b or b' \<longleftrightarrow> \<Phi> \<Turnstile> b \<or> \<Phi> \<Turnstile> b'"

definition eval_cnf :: "env \<Rightarrow> cnf \<Rightarrow> bool" ("_ \<turnstile> _" [100, 100] 70)
where "\<Phi> \<turnstile> F \<longleftrightarrow> (\<forall>C \<in> F. \<exists>(n, b) \<in> C. \<Phi> n = b)"

lemma cnf_correct: "\<Phi> \<turnstile> cnf b \<longleftrightarrow> \<Phi> \<Turnstile> b"
proof(rule sym, induction b rule: cnf.induct)
  case 2 show ?case by(simp add: "2.IH")(auto simp add: eval_cnf_def)
next
  case 3 then show ?case
    by (auto simp add: "3.IH" eval_cnf_def split_beta) blast+
qed(auto simp add: eval_cnf_def)

end
