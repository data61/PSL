text\<open>CNFs alone are nice, but now we want to relate between CNFs and formulas.\<close>
theory CNF_Formulas
imports Formulas CNF
begin
  
context begin

(* attempts to eliminate \<bottom> from formulas while converting to nnf have been made.
But that just gives you additional cases. So nnfs and cnfs will contain \<bottom> *) 

function (sequential) nnf where
"nnf (Atom k) = (Atom k)" |
"nnf \<bottom> = \<bottom>" |
"nnf (Not (And F G)) = Or (nnf (Not F)) (nnf (Not G))" |
"nnf (Not (Or F G)) = And (nnf (Not F)) (nnf (Not G))" |
"nnf (Not (Not F)) = nnf F" |
"nnf (Not (Imp F G)) = And (nnf F) (nnf (Not G))" |
"nnf (Not F) = (Not F)" |
"nnf (And F G) = And (nnf F) (nnf G)" |
"nnf (Or F G) = Or (nnf F) (nnf G)" |
"nnf (Imp F G) = Or (nnf (Not F)) (nnf G)"
  by(pat_completeness) auto

private fun nnf_cost where
"nnf_cost (Atom _) = 42" | 
"nnf_cost \<bottom> = 42" |
"nnf_cost (Not F) = Suc (nnf_cost F)" |
"nnf_cost (And F G) = Suc (nnf_cost F + nnf_cost G)" |
"nnf_cost (Or F G) = Suc (nnf_cost F + nnf_cost G)" |
"nnf_cost (Imp F G) = Suc (Suc (nnf_cost F + nnf_cost G))" (* this is why *)

termination nnf by(relation "measure (\<lambda>F. nnf_cost F)"; simp)

lemma "nnf ((Atom (k::nat)) \<^bold>\<rightarrow> (Not ((Atom l) \<^bold>\<or> (Not (Atom m))))) = \<^bold>\<not> (Atom k) \<^bold>\<or> (\<^bold>\<not> (Atom l) \<^bold>\<and> Atom m)"
  by code_simp

fun is_lit_plus where
"is_lit_plus \<bottom> = True" |
"is_lit_plus (Not \<bottom>) = True" |
"is_lit_plus (Atom _) = True" |
"is_lit_plus (Not (Atom _)) = True" |
"is_lit_plus _ = False"
case_of_simps is_lit_plus_cases: is_lit_plus.simps
fun is_disj where
(* It is crucial for this to be a (right) deep tree for the proof of LSC \<Longrightarrow> Res
  At some point, we obtain a subset A where A is in a disjunction from (A \<or> B). 
  Now, resolution is at a loss because you can't say anything about the subset.
  If, however, that subset is sandwiched between a literal and the empty clause,
  you can just cover all the cases. *)
"is_disj (Or F G) = (is_lit_plus F \<and> is_disj G)" |
"is_disj F = is_lit_plus F"
fun is_cnf where
(* here, we do want to allow arbitrary trees of \<and>.
  If we do not do that, the proofs in LSC_Resolution won't work,
  since it relies on the \<and> case being just
  a simple split in LSC and union in Resolution.
  It is possible that that is fixable, but at what cost? *)
"is_cnf (And F G) = (is_cnf F \<and> is_cnf G)" |
"is_cnf H = is_disj H"
fun is_nnf where
"is_nnf (Imp F G) = False" |
"is_nnf (And F G) = (is_nnf F \<and> is_nnf G)" |
"is_nnf (Or F G) = (is_nnf F \<and> is_nnf G)" |
"is_nnf F = is_lit_plus F"

lemma is_nnf_nnf: "is_nnf (nnf F)"
  by(induction F rule: nnf.induct; simp)
lemma nnf_no_imp: "A \<^bold>\<rightarrow> B \<notin> set (subformulae (nnf F))"
  by(induction F rule: nnf.induct; simp)
lemma subformulae_nnf: "is_nnf F \<Longrightarrow> G \<in> set (subformulae F) \<Longrightarrow> is_nnf G" (* fun fact *)
  by(induction F rule: is_nnf.induct; simp add: is_lit_plus_cases split: formula.splits; elim disjE conjE; simp)
lemma is_nnf_NotD: "is_nnf (\<^bold>\<not> F) \<Longrightarrow> (\<exists>k. F = Atom k) \<or> F = \<bottom>"
  by(cases F; simp)

fun cnf :: "'a formula \<Rightarrow> 'a clause set" where
"cnf (Atom k) = {{ k\<^sup>+ }}" |
"cnf (Not (Atom k)) = {{ k\<inverse> }}" |
"cnf \<bottom> = {\<box>}" |
"cnf (Not \<bottom>) = {}"  |
"cnf (And F G) = cnf F \<union> cnf G"  |
"cnf (Or F G) = {C \<union> D| C D. C \<in> (cnf F) \<and> D \<in> (cnf G)}"

lemma cnf_fin:
assumes "is_nnf F"
shows "finite (cnf F)" "C \<in> cnf F \<Longrightarrow> finite C"
proof -
  have "finite (cnf F) \<and> (C \<in> cnf F \<longrightarrow> finite C)" using assms
    by(induction F arbitrary: C rule: cnf.induct;  clarsimp simp add: finite_image_set2)
  thus "finite (cnf F)" "C \<in> cnf F \<Longrightarrow> finite C" by simp+
qed

(* Sets, as produced by @{const cnf} can be hard to handle.
   Less because of their infinity, more because of their lack of explicit order. *)
fun cnf_lists :: "'a formula \<Rightarrow> 'a literal list list" where
"cnf_lists (Atom k) = [[ k\<^sup>+ ]]" |
"cnf_lists (Not (Atom k)) = [[ k\<inverse> ]]" |
"cnf_lists \<bottom> = [[]]" |
"cnf_lists (Not \<bottom>) = []"  |
"cnf_lists (And F G) = cnf_lists F @ cnf_lists G"  |
"cnf_lists (Or F G) = [f @ g. f \<leftarrow> (cnf_lists F), g \<leftarrow> (cnf_lists G)]"

primrec form_of_lit where
"form_of_lit (Pos k) = Atom k" |
"form_of_lit (Neg k) = \<^bold>\<not>(Atom k)"
case_of_simps form_of_lit_cases: form_of_lit.simps

definition "disj_of_clause c \<equiv> \<^bold>\<Or>[form_of_lit l. l \<leftarrow> c]"
definition "form_of_cnf F \<equiv> \<^bold>\<And>[disj_of_clause c. c \<leftarrow> F]"
definition "cnf_form_of \<equiv> form_of_cnf \<circ> cnf_lists"
lemmas cnf_form_of_defs = cnf_form_of_def form_of_cnf_def disj_of_clause_def

lemma disj_of_clause_simps[simp]:
  "disj_of_clause [] = \<bottom>"
  "disj_of_clause (F#FF) = form_of_lit F \<^bold>\<or> disj_of_clause FF"
by(simp_all add: disj_of_clause_def)

lemma is_cnf_BigAnd: "is_cnf (\<^bold>\<And>ls) \<longleftrightarrow> (\<forall>l \<in> set ls. is_cnf l)"
  by(induction ls; simp)

private lemma BigOr_is_not_cnf'': "is_cnf (\<^bold>\<Or>ls) \<Longrightarrow> (\<forall>l \<in> set ls. is_lit_plus l)" 
proof(induction ls)
  case (Cons l ls)
  from Cons.prems have "is_cnf (\<^bold>\<Or> ls)" 
    by (metis BigOr.simps is_cnf.simps(3,5) is_disj.simps(1) list.exhaust)
  thus ?case using Cons by simp
qed simp
private lemma BigOr_is_not_cnf': "(\<forall>l \<in> set ls. is_lit_plus l) \<Longrightarrow> is_cnf (\<^bold>\<Or>ls)" 
  by(induction ls; simp) (metis BigOr.simps(1, 2) formula.distinct(25) is_cnf.elims(2) is_cnf.simps(3) list.exhaust)
  (* ugh *)
lemma BigOr_is_not_cnf: "is_cnf (\<^bold>\<Or>ls) \<longleftrightarrow> (\<forall>l \<in> set ls. is_lit_plus l)"
  using BigOr_is_not_cnf' BigOr_is_not_cnf'' by blast

lemma is_nnf_BigAnd[simp]: "is_nnf (\<^bold>\<And>ls) \<longleftrightarrow> (\<forall>l \<in> set ls. is_nnf l)"
  by(induction ls; simp)
lemma is_nnf_BigOr[simp]: "is_nnf (\<^bold>\<Or>ls) \<longleftrightarrow> (\<forall>l \<in> set ls. is_nnf l)"
  by(induction ls; simp)
lemma form_of_lit_is_nnf[simp,intro!]: "is_nnf (form_of_lit x)"
  by(cases x; simp)
lemma form_of_lit_is_lit[simp,intro!]: "is_lit_plus (form_of_lit x)"
  by(cases x; simp)
lemma disj_of_clause_is_nnf[simp,intro!]: "is_nnf (disj_of_clause F)"
  unfolding disj_of_clause_def by simp

lemma cnf_form_of_is: "is_nnf F \<Longrightarrow> is_cnf (cnf_form_of F)"
  by(cases F) (auto simp: cnf_form_of_defs is_cnf_BigAnd BigOr_is_not_cnf)

lemma nnf_cnf_form: "is_nnf F \<Longrightarrow> is_nnf (cnf_form_of F)"
  by(cases F) (auto simp add: cnf_form_of_defs)

lemma cnf_BigAnd: "cnf (\<^bold>\<And>ls) = (\<Union>x \<in> set ls. cnf x)"
  by(induction ls; simp)

lemma cnf_BigOr: "cnf (\<^bold>\<Or> (x @ y)) =  {f \<union> g |f g. f \<in> cnf (\<^bold>\<Or>x) \<and> g \<in> cnf (\<^bold>\<Or>y)}"
  by(induction x arbitrary: y; simp) (metis (no_types, hide_lams) sup.assoc)

lemma cnf_cnf: "is_nnf F \<Longrightarrow> cnf (cnf_form_of F) = cnf F"
  by(induction F rule: cnf.induct; 
     fastforce simp add: cnf_form_of_defs cnf_BigAnd cnf_BigOr)
(* this is not an idempotency (is that a word?) lemma, since cnf_form_of is not idempotent. *)

lemma is_nnf_nnf_id: "is_nnf F \<Longrightarrow> nnf F = F"
proof(induction rule: is_nnf.induct)
  fix v assume "is_nnf (\<^bold>\<not> v)"
  thus "nnf (\<^bold>\<not> v) = \<^bold>\<not> v" by(cases v rule: is_lit_plus.cases; simp)
qed simp_all
  
lemma disj_of_clause_is: "is_disj (disj_of_clause R)"
  by(induction R; simp)
    
lemma form_of_cnf_is_nnf: "is_nnf (form_of_cnf R)"
  unfolding form_of_cnf_def by simp
    
lemma cnf_disj: "cnf (disj_of_clause R) = {set R}"
  by(induction R; simp add: form_of_lit_cases split: literal.splits)
lemma cnf_disj_ex: "is_disj F \<Longrightarrow> \<exists>R. cnf F = {R} \<or> cnf F = {}"
  by(induction F rule: is_disj.induct; clarsimp simp: is_lit_plus_cases split: formula.splits)
    
    
lemma cnf_form_of_cnf: "cnf (form_of_cnf S) = set (map set S)"
  unfolding form_of_cnf_def by (simp add: cnf_BigAnd cnf_disj) blast
    
lemma disj_is_nnf: "is_disj F \<Longrightarrow> is_nnf F"
  by(induction F rule: is_disj.induct; simp add: is_lit_plus_cases split: formula.splits)
    
lemma nnf_BigAnd: "nnf (\<^bold>\<And>F) = \<^bold>\<And>(map nnf F)"
  by(induction F; simp)

end

end
