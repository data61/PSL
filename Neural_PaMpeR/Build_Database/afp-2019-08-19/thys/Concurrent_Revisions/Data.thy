section \<open>Data\<close>

text \<open>This theory defines the data types and notations, and some preliminary results about them.\<close>

theory Data
  imports Main
begin

subsection \<open>Function notations\<close>

abbreviation \<epsilon> :: "'a \<rightharpoonup> 'b" where
  "\<epsilon> \<equiv> \<lambda>x. None"

fun combine :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a  \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" ("_;;_" 20) where
  "(f ;; g) x = (if g x = None then f x else g x)"

lemma dom_combination_dom_union: "dom (\<tau>;;\<tau>') = dom \<tau> \<union> dom \<tau>'"
  by auto

subsection \<open>Values, expressions and execution contexts\<close>

datatype const = Unit | F | T

datatype (RID\<^sub>V: 'r, LID\<^sub>V: 'l,'v) val = 
  CV const
| Var 'v
| Loc 'l
| Rid 'r
| Lambda 'v "('r,'l,'v) expr"
and (RID\<^sub>E: 'r, LID\<^sub>E: 'l,'v) expr =
  VE "('r,'l,'v) val"
| Apply "('r,'l,'v) expr" "('r,'l,'v) expr"
| Ite "('r,'l,'v) expr" "('r,'l,'v) expr" "('r,'l,'v) expr"
| Ref "('r,'l,'v) expr"
| Read "('r,'l,'v) expr"
| Assign "('r,'l,'v) expr" "('r,'l,'v) expr"
| Rfork "('r,'l,'v) expr"
| Rjoin "('r,'l,'v) expr"

datatype (RID\<^sub>C: 'r, LID\<^sub>C: 'l,'v) cntxt = 
  Hole ("\<box>")
| ApplyL\<^sub>\<E> "('r,'l,'v) cntxt" "('r,'l,'v) expr" 
| ApplyR\<^sub>\<E> "('r,'l,'v) val" "('r,'l,'v) cntxt"
| Ite\<^sub>\<E> "('r,'l,'v) cntxt" "('r,'l,'v) expr" "('r,'l,'v) expr"
| Ref\<^sub>\<E> "('r,'l,'v) cntxt"
| Read\<^sub>\<E> "('r,'l,'v) cntxt"
| AssignL\<^sub>\<E> "('r,'l,'v) cntxt" "('r,'l,'v) expr"
| AssignR\<^sub>\<E> 'l "('r,'l,'v) cntxt"
| Rjoin\<^sub>\<E> "('r,'l,'v) cntxt"

subsection \<open>Plugging and decomposing\<close>

fun plug :: "('r,'l,'v) cntxt \<Rightarrow> ('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) expr" (infix "\<lhd>" 60) where
  "\<box> \<lhd> e = e"
| "ApplyL\<^sub>\<E> \<E> e1 \<lhd> e = Apply (\<E> \<lhd> e) e1"
| "ApplyR\<^sub>\<E> val \<E> \<lhd> e = Apply (VE val) (\<E> \<lhd> e)"
| "Ite\<^sub>\<E> \<E> e1 e2 \<lhd> e = Ite (\<E> \<lhd> e) e1 e2"
| "Ref\<^sub>\<E> \<E> \<lhd> e = Ref (\<E> \<lhd> e)"
| "Read\<^sub>\<E> \<E> \<lhd> e = Read (\<E> \<lhd> e)"
| "AssignL\<^sub>\<E> \<E> e1 \<lhd> e = Assign (\<E> \<lhd> e) e1"
| "AssignR\<^sub>\<E> l \<E> \<lhd> e = Assign (VE (Loc l)) (\<E> \<lhd> e)"
| "Rjoin\<^sub>\<E> \<E> \<lhd> e = Rjoin (\<E> \<lhd> e)"

translations
  "\<E>[x]" \<rightleftharpoons> "\<E> \<lhd> x"

lemma injective_cntxt [simp]: "(\<E>[e1] = \<E>[e2]) = (e1 = e2)" by (induction \<E>) auto

lemma VE_empty_cntxt [simp]: "(VE v = \<E>[e]) = (\<E> = \<box> \<and> VE v = e)" by (cases \<E>, auto) 

inductive redex :: "('r,'l,'v) expr \<Rightarrow> bool" where
  app: "redex (Apply (VE (Lambda x e)) (VE v))"
| iteTrue: "redex (Ite (VE (CV T)) e1 e2)"
| iteFalse: "redex (Ite (VE (CV F)) e1 e2)"
| ref: "redex (Ref (VE v))"
| read: "redex (Read (VE (Loc l)))"
| assign: "redex (Assign (VE (Loc l)) (VE v))"
| rfork: "redex (Rfork e)"
| rjoin: "redex (Rjoin (VE (Rid r)))"

inductive_simps redex_simps [simp]: "redex e"
inductive_cases redexE [elim]: "redex e"

lemma plugged_redex_not_val [simp]: "redex r \<Longrightarrow> (\<E> \<lhd> r) \<noteq> (VE t)" by (cases \<E>) auto

inductive decompose :: "('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) cntxt \<Rightarrow> ('r,'l,'v) expr \<Rightarrow> bool" where
  top_redex: "redex e \<Longrightarrow> decompose e \<box> e"
| lapply: "\<lbrakk> \<not>redex (Apply e\<^sub>1 e\<^sub>2); decompose e\<^sub>1 \<E> r \<rbrakk> \<Longrightarrow> decompose (Apply e\<^sub>1 e\<^sub>2) (ApplyL\<^sub>\<E> \<E> e\<^sub>2) r"
| rapply: "\<lbrakk> \<not>redex (Apply (VE v) e); decompose e \<E> r \<rbrakk> \<Longrightarrow> decompose (Apply (VE v) e) (ApplyR\<^sub>\<E> v \<E>) r"
| ite: "\<lbrakk> \<not>redex (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3); decompose e\<^sub>1 \<E> r \<rbrakk> \<Longrightarrow> decompose (Ite e\<^sub>1 e\<^sub>2 e\<^sub>3) (Ite\<^sub>\<E> \<E> e\<^sub>2 e\<^sub>3) r"
| ref: "\<lbrakk> \<not>redex (Ref e); decompose e \<E> r \<rbrakk> \<Longrightarrow> decompose (Ref e) (Ref\<^sub>\<E> \<E>) r"
| read: "\<lbrakk> \<not>redex (Read e); decompose e \<E> r \<rbrakk> \<Longrightarrow> decompose (Read e) (Read\<^sub>\<E> \<E>) r"
| lassign: "\<lbrakk> \<not>redex (Assign e\<^sub>1 e\<^sub>2); decompose e\<^sub>1 \<E> r \<rbrakk> \<Longrightarrow> decompose (Assign e\<^sub>1 e\<^sub>2) (AssignL\<^sub>\<E> \<E> e\<^sub>2) r"
| rassign: "\<lbrakk> \<not>redex (Assign (VE (Loc l)) e\<^sub>2); decompose e\<^sub>2 \<E> r \<rbrakk> \<Longrightarrow> decompose (Assign (VE (Loc l)) e\<^sub>2) (AssignR\<^sub>\<E> l \<E>) r"
| rjoin:  "\<lbrakk> \<not>redex (Rjoin e); decompose e \<E> r \<rbrakk> \<Longrightarrow> decompose (Rjoin e) (Rjoin\<^sub>\<E> \<E>) r"

inductive_cases decomposeE [elim]: "decompose e \<E> r"

lemma plug_decomposition_equivalence: "redex r \<Longrightarrow> decompose e \<E> r = (\<E>[r] = e)"
proof (rule iffI)
  assume x: "decompose e \<E> r"
  show "\<E>[r] = e" 
  proof (use x in \<open>induct rule: decompose.induct\<close>)
    case (top_redex e)
    thus "\<box>[e] = e" by simp
  next
    case (lapply e\<^sub>1 e\<^sub>2 \<E> r)
    have "(ApplyL\<^sub>\<E> \<E> e\<^sub>2) [r] = Apply (\<E>[r]) e\<^sub>2" by simp
    also have "... = Apply e\<^sub>1 e\<^sub>2" using \<open>\<E>[r] = e\<^sub>1\<close> by simp
    then show ?case by simp
  qed simp+
next
  assume red: "redex r" and  eq: "\<E>[r] = e"
  have "decompose (\<E>[r]) \<E> r" by (induct \<E>) (use red in \<open>auto intro: decompose.intros\<close>)
  thus "decompose e \<E> r" by (simp add: eq)
qed

lemma unique_decomposition: "decompose e \<E>\<^sub>1 r\<^sub>1 \<Longrightarrow> decompose e \<E>\<^sub>2 r\<^sub>2 \<Longrightarrow> \<E>\<^sub>1 = \<E>\<^sub>2 \<and> r\<^sub>1 = r\<^sub>2"
  by (induct arbitrary: \<E>\<^sub>2 rule: decompose.induct) auto

lemma completion_eq [simp]:
  assumes
    red_e: "redex r" and
    red_e': "redex r'"
  shows "(\<E>[r] = \<E>'[r']) = (\<E> = \<E>' \<and> r = r')"
proof (rule iffI)
  show "\<E>[r] = \<E>'[r'] \<Longrightarrow> \<E> = \<E>' \<and> r = r'"
  proof (rule conjI)
    assume eq: "\<E>[r] = \<E>'[r']"
    have "decompose (\<E>[r]) \<E> r" using plug_decomposition_equivalence red_e by blast
    hence fst_decomp:"decompose (\<E>'[r']) \<E> r" by (simp add: eq)
    have snd_decomp: "decompose (\<E>'[r']) \<E>' r'" using plug_decomposition_equivalence red_e' by blast
    show cntxts_eq: "\<E> = \<E>'" using fst_decomp snd_decomp unique_decomposition by blast
    show "r = r'" using cntxts_eq eq by simp
  qed
qed simp

subsection \<open>Stores and states\<close>

type_synonym ('r,'l,'v) store = "'l \<rightharpoonup> ('r,'l,'v) val"
type_synonym ('r,'l,'v) local_state = "('r,'l,'v) store \<times> ('r,'l,'v) store \<times> ('r,'l,'v) expr"
type_synonym ('r,'l,'v) global_state = "'r \<rightharpoonup> ('r,'l,'v) local_state"

fun doms :: "('r,'l,'v) local_state \<Rightarrow> 'l set" where
  "doms (\<sigma>,\<tau>,e) = dom \<sigma> \<union> dom \<tau>"

fun LID_snapshot :: "('r,'l,'v) local_state \<Rightarrow> ('r,'l,'v) store" ("_\<^sub>\<sigma>" 200) where
  "LID_snapshot (\<sigma>,\<tau>,e) = \<sigma>"

fun LID_local_store :: "('r,'l,'v) local_state \<Rightarrow> ('r,'l,'v) store" ("_\<^sub>\<tau>" 200) where
  "LID_local_store (\<sigma>,\<tau>,e) = \<tau>"

fun LID_expression :: "('r,'l,'v) local_state \<Rightarrow> ('r,'l,'v) expr" ("_\<^sub>e" 200) where
  "LID_expression (\<sigma>,\<tau>,e) = e"

end