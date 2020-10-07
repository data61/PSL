chapter\<open>De Bruijn Syntax, Quotations, Codes, V-Codes\<close>

theory Coding
imports SyntaxN
begin

declare fresh_Nil [iff]

section \<open>de Bruijn Indices (locally-nameless version)\<close>

nominal_datatype dbtm = DBZero | DBVar name | DBInd nat | DBEats dbtm dbtm

nominal_datatype dbfm =
    DBMem dbtm dbtm
  | DBEq dbtm dbtm
  | DBDisj dbfm dbfm
  | DBNeg dbfm
  | DBEx dbfm

declare dbtm.supp [simp]
declare dbfm.supp [simp]

fun lookup :: "name list \<Rightarrow> nat \<Rightarrow> name \<Rightarrow> dbtm"
  where
    "lookup [] n x = DBVar x"
  | "lookup (y # ys) n x = (if x = y then DBInd n else (lookup ys (Suc n) x))"

lemma fresh_imp_notin_env: "atom name \<sharp> e \<Longrightarrow> name \<notin> set e"
  by (metis List.finite_set fresh_finite_set_at_base fresh_set)

lemma lookup_notin: "x \<notin> set e \<Longrightarrow> lookup e n x = DBVar x"
  by (induct e arbitrary: n) auto

lemma lookup_in:
  "x \<in> set e \<Longrightarrow> \<exists>k. lookup e n x = DBInd k \<and> n \<le> k \<and> k < n + length e"
apply (induct e arbitrary: n) 
apply (auto intro: Suc_leD)
apply (metis Suc_leD add_Suc_right add_Suc_shift)
done

lemma lookup_fresh: "x \<sharp> lookup e n y \<longleftrightarrow> y \<in> set e \<or> x \<noteq> atom y"
  by (induct arbitrary: n rule: lookup.induct) (auto simp: pure_fresh fresh_at_base)

lemma lookup_eqvt[eqvt]: "(p \<bullet> lookup xs n x) = lookup (p \<bullet> xs) (p \<bullet> n) (p \<bullet> x)"
  by (induct xs arbitrary: n) (simp_all add: permute_pure)

lemma lookup_inject [iff]: "(lookup e n x = lookup e n y) \<longleftrightarrow> x = y"
apply (induct e n x arbitrary: y rule: lookup.induct, force, simp)
by (metis Suc_n_not_le_n dbtm.distinct(7) dbtm.eq_iff(3) lookup_in lookup_notin)

nominal_function trans_tm :: "name list \<Rightarrow> tm \<Rightarrow> dbtm"
  where
   "trans_tm e Zero = DBZero"
 | "trans_tm e (Var k) = lookup e 0 k"
 | "trans_tm e (Eats t u) = DBEats (trans_tm e t) (trans_tm e u)"
by (auto simp: eqvt_def trans_tm_graph_aux_def) (metis tm.strong_exhaust)

nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_trans_tm_iff [simp]: "i \<sharp> trans_tm e t \<longleftrightarrow> i \<sharp> t \<or> i \<in> atom ` set e"
  by (induct t rule: tm.induct, auto simp: lookup_fresh fresh_at_base)

lemma trans_tm_forget: "atom i \<sharp> t \<Longrightarrow> trans_tm [i] t = trans_tm [] t"
  by (induct t rule: tm.induct, auto simp: fresh_Pair)

nominal_function (invariant "\<lambda>(xs, _) y. atom ` set xs \<sharp>* y")
  trans_fm :: "name list \<Rightarrow> fm \<Rightarrow> dbfm"
  where
   "trans_fm e (Mem t u) = DBMem (trans_tm e t) (trans_tm e u)"
 | "trans_fm e (Eq t u)  = DBEq (trans_tm e t) (trans_tm e u)"
 | "trans_fm e (Disj A B) = DBDisj (trans_fm e A) (trans_fm e B)"
 | "trans_fm e (Neg A)   = DBNeg (trans_fm e A)"
 | "atom k \<sharp> e \<Longrightarrow> trans_fm e (Ex k A) = DBEx (trans_fm (k#e) A)"
apply(simp add: eqvt_def trans_fm_graph_aux_def)
apply(erule trans_fm_graph.induct)
using [[simproc del: alpha_lst]]
apply(auto simp: fresh_star_def)
apply(rule_tac y=b and c=a in fm.strong_exhaust)
apply(auto simp: fresh_star_def)
apply(erule_tac c=ea in Abs_lst1_fcb2')
apply (simp_all add: eqvt_at_def)
apply (simp_all add: fresh_star_Pair perm_supp_eq)
apply (simp add: fresh_star_def)
done

nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_trans_fm [simp]: "i \<sharp> trans_fm e A \<longleftrightarrow> i \<sharp> A \<or> i \<in> atom ` set e"
  by (nominal_induct A avoiding: e rule: fm.strong_induct, auto simp: fresh_at_base)

abbreviation DBConj :: "dbfm \<Rightarrow> dbfm \<Rightarrow> dbfm"
  where "DBConj t u \<equiv> DBNeg (DBDisj (DBNeg t) (DBNeg u))"

lemma trans_fm_Conj [simp]: "trans_fm e (Conj A B) = DBConj (trans_fm e A) (trans_fm e B)"
  by (simp add: Conj_def)

lemma trans_tm_inject [iff]: "(trans_tm e t = trans_tm e u) \<longleftrightarrow> t = u"
proof (induct t arbitrary: e u rule: tm.induct)
  case Zero show ?case
    apply (cases u rule: tm.exhaust, auto)
    apply (metis dbtm.distinct(1) dbtm.distinct(3) lookup_in lookup_notin)
    done
next
  case (Var i) show ?case
    apply (cases u rule: tm.exhaust, auto)
    apply (metis dbtm.distinct(1) dbtm.distinct(3) lookup_in lookup_notin)
    apply (metis dbtm.distinct(10) dbtm.distinct(11) lookup_in lookup_notin)
    done
next
  case (Eats tm1 tm2) thus ?case
    apply (cases u rule: tm.exhaust, auto)
    apply (metis dbtm.distinct(12) dbtm.distinct(9) lookup_in lookup_notin)
    done
qed

lemma trans_fm_inject [iff]: "(trans_fm e A = trans_fm e B) \<longleftrightarrow> A = B"
proof (nominal_induct A avoiding: e B rule: fm.strong_induct)
  case (Mem tm1 tm2) thus ?case
    by (rule fm.strong_exhaust [where y=B and c=e]) (auto simp: fresh_star_def)
next
  case (Eq tm1 tm2) thus ?case
    by (rule fm.strong_exhaust [where y=B and c=e]) (auto simp: fresh_star_def)
next
  case (Disj fm1 fm2) show ?case
    by (rule fm.strong_exhaust [where y=B and c=e]) (auto simp: Disj fresh_star_def)
next
  case (Neg fm) show ?case
    by (rule fm.strong_exhaust [where y=B and c=e]) (auto simp: Neg fresh_star_def)
next
  case (Ex name fm)
  thus ?case  using [[simproc del: alpha_lst]]
  proof (cases rule: fm.strong_exhaust [where y=B and c="(e, name)"], simp_all add: fresh_star_def)
    fix name'::name and fm'::fm
    assume name': "atom name' \<sharp> (e, name)"
    assume "atom name \<sharp> fm' \<or> name = name'"
    thus "(trans_fm (name # e) fm = trans_fm (name' # e) fm') = ([[atom name]]lst. fm = [[atom name']]lst. fm')"
         (is "?lhs = ?rhs")
    proof (rule disjE)
      assume "name = name'"
      thus "?lhs = ?rhs"
        by (metis fresh_Pair fresh_at_base(2) name')
    next
      assume name: "atom name \<sharp> fm'"
      have eq1: "(name \<leftrightarrow> name') \<bullet> trans_fm (name' # e) fm' = trans_fm (name' # e) fm'"
        by (simp add: flip_fresh_fresh name)
      have eq2: "(name \<leftrightarrow> name') \<bullet> ([[atom name']]lst. fm') = [[atom name']]lst. fm'"
        by (rule flip_fresh_fresh) (auto simp: Abs_fresh_iff name)
      show "?lhs = ?rhs" using name' eq1 eq2 Ex(1) Ex(3) [of "name#e" "(name \<leftrightarrow> name') \<bullet> fm'"]
        by (simp add: flip_fresh_fresh) (metis Abs1_eq(3))
    qed
  qed
qed

lemma trans_fm_perm:
  assumes c: "atom c \<sharp> (i,j,A,B)"
  and     t: "trans_fm [i] A = trans_fm [j] B"
  shows "(i \<leftrightarrow> c) \<bullet> A = (j \<leftrightarrow> c) \<bullet> B"
proof -
  have c_fresh1: "atom c \<sharp> trans_fm [i] A"
    using c by (auto simp: supp_Pair)
  moreover
  have i_fresh: "atom i \<sharp> trans_fm [i] A"
    by auto
  moreover
  have c_fresh2: "atom c \<sharp> trans_fm [j] B"
    using c by (auto simp: supp_Pair)
  moreover
  have j_fresh: "atom j \<sharp> trans_fm [j] B"
    by auto
  ultimately have "((i \<leftrightarrow> c) \<bullet> (trans_fm [i] A)) = ((j \<leftrightarrow> c) \<bullet> trans_fm [j] B)"
    by (simp only: flip_fresh_fresh t)
  then have "trans_fm [c] ((i \<leftrightarrow> c) \<bullet> A) = trans_fm [c] ((j \<leftrightarrow> c) \<bullet> B)"
    by simp
  then show "(i \<leftrightarrow> c) \<bullet> A = (j \<leftrightarrow> c) \<bullet> B" by simp
qed

section\<open>Characterising the Well-Formed de Bruijn Formulas\<close>

subsection\<open>Well-Formed Terms\<close>

inductive wf_dbtm :: "dbtm \<Rightarrow> bool"
  where
    Zero:  "wf_dbtm DBZero"
  | Var:   "wf_dbtm (DBVar name)"
  | Eats:  "wf_dbtm t1 \<Longrightarrow> wf_dbtm t2 \<Longrightarrow> wf_dbtm (DBEats t1 t2)"

equivariance wf_dbtm

inductive_cases Zero_wf_dbtm [elim!]: "wf_dbtm DBZero"
inductive_cases Var_wf_dbtm [elim!]:  "wf_dbtm (DBVar name)"
inductive_cases Ind_wf_dbtm [elim!]:  "wf_dbtm (DBInd i)"
inductive_cases Eats_wf_dbtm [elim!]: "wf_dbtm (DBEats t1 t2)"

declare wf_dbtm.intros [intro]

lemma wf_dbtm_imp_is_tm:
  assumes "wf_dbtm x"
  shows "\<exists>t::tm. x = trans_tm [] t"
using assms
proof (induct rule: wf_dbtm.induct)
  case Zero thus ?case
    by (metis trans_tm.simps(1))
next
  case (Var i) thus ?case
    by (metis lookup.simps(1) trans_tm.simps(2))
next
  case (Eats dt1 dt2) thus ?case
    by (metis trans_tm.simps(3))
qed

lemma wf_dbtm_trans_tm: "wf_dbtm (trans_tm [] t)"
  by (induct t rule: tm.induct) auto

theorem wf_dbtm_iff_is_tm: "wf_dbtm x \<longleftrightarrow> (\<exists>t::tm. x = trans_tm [] t)"
  by (metis wf_dbtm_imp_is_tm wf_dbtm_trans_tm)

nominal_function abst_dbtm :: "name \<Rightarrow> nat \<Rightarrow> dbtm \<Rightarrow> dbtm"
  where
   "abst_dbtm name i DBZero = DBZero"
 | "abst_dbtm name i (DBVar name') = (if name = name' then DBInd i else DBVar name')"
 | "abst_dbtm name i (DBInd j) = DBInd j"
 | "abst_dbtm name i (DBEats t1 t2) = DBEats (abst_dbtm name i t1) (abst_dbtm name i t2)"
apply (simp add: eqvt_def abst_dbtm_graph_aux_def, auto)
apply (metis dbtm.exhaust)
done

nominal_termination (eqvt)
  by lexicographic_order

nominal_function subst_dbtm :: "dbtm \<Rightarrow> name \<Rightarrow> dbtm \<Rightarrow> dbtm"
  where
   "subst_dbtm u i DBZero = DBZero"
 | "subst_dbtm u i (DBVar name) = (if i = name then u else DBVar name)"
 | "subst_dbtm u i (DBInd j) = DBInd j"
 | "subst_dbtm u i (DBEats t1 t2) = DBEats (subst_dbtm u i t1) (subst_dbtm u i t2)"
by (auto simp: eqvt_def subst_dbtm_graph_aux_def) (metis dbtm.exhaust)

nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_iff_non_subst_dbtm: "subst_dbtm DBZero i t = t \<longleftrightarrow> atom i \<sharp> t"
  by (induct t rule: dbtm.induct) (auto simp: pure_fresh fresh_at_base(2))

lemma lookup_append: "lookup (e @ [i]) n j = abst_dbtm i (length e + n) (lookup e n j)"
  by (induct e arbitrary: n) (auto simp: fresh_Cons)

lemma trans_tm_abs: "trans_tm (e@[name]) t = abst_dbtm name (length e) (trans_tm e t)"
  by (induct t rule: tm.induct) (auto simp: lookup_notin lookup_append)

subsection\<open>Well-Formed Formulas\<close>

nominal_function abst_dbfm :: "name \<Rightarrow> nat \<Rightarrow> dbfm \<Rightarrow> dbfm"
  where
   "abst_dbfm name i (DBMem t1 t2) = DBMem (abst_dbtm name i t1) (abst_dbtm name i t2)"
 | "abst_dbfm name i (DBEq t1 t2) =  DBEq (abst_dbtm name i t1) (abst_dbtm name i t2)"
 | "abst_dbfm name i (DBDisj A1 A2) = DBDisj (abst_dbfm name i A1) (abst_dbfm name i A2)"
 | "abst_dbfm name i (DBNeg A) = DBNeg (abst_dbfm name i A)"
 | "abst_dbfm name i (DBEx A) = DBEx (abst_dbfm name (i+1) A)"
apply (simp add: eqvt_def abst_dbfm_graph_aux_def, auto)
apply (metis dbfm.exhaust)
done

nominal_termination (eqvt)
  by lexicographic_order

nominal_function subst_dbfm :: "dbtm \<Rightarrow> name \<Rightarrow> dbfm \<Rightarrow> dbfm"
  where
   "subst_dbfm u i (DBMem t1 t2) = DBMem (subst_dbtm u i t1) (subst_dbtm u i t2)"
 | "subst_dbfm u i (DBEq t1 t2) =  DBEq (subst_dbtm u i t1) (subst_dbtm u i t2)"
 | "subst_dbfm u i (DBDisj A1 A2) = DBDisj (subst_dbfm u i A1) (subst_dbfm u i A2)"
 | "subst_dbfm u i (DBNeg A) = DBNeg (subst_dbfm u i A)"
 | "subst_dbfm u i (DBEx A) = DBEx (subst_dbfm u i A)"
by (auto simp: eqvt_def subst_dbfm_graph_aux_def) (metis dbfm.exhaust)

nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_iff_non_subst_dbfm: "subst_dbfm DBZero i t = t \<longleftrightarrow> atom i \<sharp> t"
  by (induct t rule: dbfm.induct) (auto simp: fresh_iff_non_subst_dbtm)


section\<open>Well formed terms and formulas (de Bruijn representation)\<close>

inductive wf_dbfm :: "dbfm \<Rightarrow> bool"
  where
    Mem:   "wf_dbtm t1 \<Longrightarrow> wf_dbtm t2 \<Longrightarrow> wf_dbfm (DBMem t1 t2)"
  | Eq:    "wf_dbtm t1 \<Longrightarrow> wf_dbtm t2 \<Longrightarrow> wf_dbfm (DBEq t1 t2)"
  | Disj:  "wf_dbfm A1 \<Longrightarrow> wf_dbfm A2 \<Longrightarrow> wf_dbfm (DBDisj A1 A2)"
  | Neg:   "wf_dbfm A \<Longrightarrow> wf_dbfm (DBNeg A)"
  | Ex:    "wf_dbfm A \<Longrightarrow> wf_dbfm (DBEx (abst_dbfm name 0 A))"

equivariance wf_dbfm

lemma atom_fresh_abst_dbtm [simp]: "atom i \<sharp> abst_dbtm i n t"
  by (induct t rule: dbtm.induct) (auto simp: pure_fresh)

lemma atom_fresh_abst_dbfm [simp]: "atom i \<sharp> abst_dbfm i n A"
  by (nominal_induct A arbitrary: n rule: dbfm.strong_induct) auto

text\<open>Setting up strong induction: "avoiding" for name. Necessary to allow some proofs to go through\<close>
nominal_inductive wf_dbfm
  avoids Ex: name
  by (auto simp: fresh_star_def)

inductive_cases Mem_wf_dbfm [elim!]:  "wf_dbfm (DBMem t1 t2)"
inductive_cases Eq_wf_dbfm [elim!]:   "wf_dbfm (DBEq t1 t2)"
inductive_cases Disj_wf_dbfm [elim!]: "wf_dbfm (DBDisj A1 A2)"
inductive_cases Neg_wf_dbfm [elim!]:  "wf_dbfm (DBNeg A)"
inductive_cases Ex_wf_dbfm [elim!]:   "wf_dbfm (DBEx z)"

declare wf_dbfm.intros [intro]

lemma trans_fm_abs: "trans_fm (e@[name]) A = abst_dbfm name (length e) (trans_fm e A)"
  apply (nominal_induct A avoiding: name e rule: fm.strong_induct)
  apply (auto simp: trans_tm_abs fresh_Cons fresh_append)
  apply (metis One_nat_def Suc_eq_plus1 append_Cons list.size(4))
  done

lemma abst_trans_fm: "abst_dbfm name 0 (trans_fm [] A) = trans_fm [name] A"
  by (metis append_Nil list.size(3) trans_fm_abs)

lemma abst_trans_fm2: "i \<noteq> j \<Longrightarrow> abst_dbfm i (Suc 0) (trans_fm [j] A) = trans_fm [j,i] A"
  using trans_fm_abs [where e="[j]" and name=i]
  by auto

lemma wf_dbfm_imp_is_fm:
  assumes "wf_dbfm x" shows "\<exists>A::fm. x = trans_fm [] A"
using assms
proof (induct rule: wf_dbfm.induct)
  case (Mem t1 t2) thus ?case
    by (metis trans_fm.simps(1) wf_dbtm_imp_is_tm)
next
  case (Eq t1 t2) thus ?case
    by (metis trans_fm.simps(2) wf_dbtm_imp_is_tm)
next
  case (Disj fm1 fm2) thus ?case
    by (metis trans_fm.simps(3))
next
  case (Neg fm) thus ?case
    by (metis trans_fm.simps(4))
next
  case (Ex fm name) thus ?case
    apply auto
    apply (rule_tac x="Ex name A" in exI)
    apply (auto simp: abst_trans_fm)
    done
qed

lemma wf_dbfm_trans_fm: "wf_dbfm (trans_fm [] A)"
  apply (nominal_induct A rule: fm.strong_induct)
  apply (auto simp: wf_dbtm_trans_tm abst_trans_fm)
  apply (metis abst_trans_fm wf_dbfm.Ex)
  done

lemma wf_dbfm_iff_is_fm: "wf_dbfm x \<longleftrightarrow> (\<exists>A::fm. x = trans_fm [] A)"
  by (metis wf_dbfm_imp_is_fm wf_dbfm_trans_fm)

lemma dbtm_abst_ignore [simp]:
  "abst_dbtm name i (abst_dbtm name j t) = abst_dbtm name j t"
  by (induct t rule: dbtm.induct) auto

lemma abst_dbtm_fresh_ignore [simp]: "atom name \<sharp> u \<Longrightarrow> abst_dbtm name j u = u"
  by (induct u rule: dbtm.induct) auto

lemma dbtm_subst_ignore [simp]:
  "subst_dbtm u name (abst_dbtm name j t) = abst_dbtm name j t"
  by (induct t rule: dbtm.induct) auto

lemma dbtm_abst_swap_subst:
  "name \<noteq> name' \<Longrightarrow> atom name' \<sharp> u \<Longrightarrow>
   subst_dbtm u name (abst_dbtm name' j t) = abst_dbtm name' j (subst_dbtm u name t)"
  by (induct t rule: dbtm.induct) auto

lemma dbfm_abst_swap_subst:
  "name \<noteq> name' \<Longrightarrow> atom name' \<sharp> u \<Longrightarrow>
   subst_dbfm u name (abst_dbfm name' j A) = abst_dbfm name' j (subst_dbfm u name A)"
  by (induct A arbitrary: j rule: dbfm.induct) (auto simp: dbtm_abst_swap_subst)

lemma subst_trans_commute [simp]:
  "atom i \<sharp> e \<Longrightarrow> subst_dbtm (trans_tm e u) i (trans_tm e t) = trans_tm e (subst i u t)"
  apply (induct t rule: tm.induct)
  apply (auto simp: lookup_notin fresh_imp_notin_env)
  apply (metis abst_dbtm_fresh_ignore dbtm_subst_ignore lookup_fresh lookup_notin subst_dbtm.simps(2))
  done

lemma subst_fm_trans_commute [simp]:
  "subst_dbfm (trans_tm [] u) name (trans_fm [] A) = trans_fm [] (A (name::= u))"
  apply (nominal_induct A avoiding: name u rule: fm.strong_induct)
  apply (auto simp: lookup_notin abst_trans_fm [symmetric])
  apply (metis dbfm_abst_swap_subst fresh_at_base(2) fresh_trans_tm_iff)
  done

lemma subst_fm_trans_commute_eq:
  "du = trans_tm [] u \<Longrightarrow> subst_dbfm du i (trans_fm [] A) = trans_fm [] (A(i::=u))"
  by (metis subst_fm_trans_commute)


section\<open>Quotations\<close>

fun htuple :: "nat \<Rightarrow> hf"  where
   "htuple 0 = \<langle>0,0\<rangle>"
 | "htuple (Suc k) = \<langle>0, htuple k\<rangle>"

fun HTuple :: "nat \<Rightarrow> tm"  where
   "HTuple 0 = HPair Zero Zero"
 | "HTuple (Suc k) = HPair Zero (HTuple k)"

lemma eval_tm_HTuple [simp]:  "\<lbrakk>HTuple n\<rbrakk>e = htuple n"
  by (induct n) auto

lemma fresh_HTuple [simp]: "x \<sharp> HTuple n"
  by (induct n) auto

lemma HTuple_eqvt[eqvt]: "(p \<bullet> HTuple n) = HTuple (p \<bullet> n)"
  by (induct n, auto simp: HPair_eqvt permute_pure)

lemma htuple_nonzero [simp]: "htuple k \<noteq> 0"
  by (induct k) auto

lemma htuple_inject [iff]: "htuple i = htuple j \<longleftrightarrow> i=j"
proof (induct i arbitrary: j)
  case 0 show ?case
    by (cases j) auto
next
  case (Suc i) show ?case
    by (cases j) (auto simp: Suc)
qed

subsection \<open>Quotations of de Bruijn terms\<close>

definition nat_of_name :: "name \<Rightarrow> nat"
  where "nat_of_name x = nat_of (atom x)"

lemma nat_of_name_inject [simp]: "nat_of_name n1 = nat_of_name n2 \<longleftrightarrow> n1 = n2"
  by (metis nat_of_name_def atom_components_eq_iff atom_eq_iff sort_of_atom_eq)

definition name_of_nat :: "nat \<Rightarrow> name"
  where "name_of_nat n \<equiv> Abs_name (Atom (Sort ''SyntaxN.name'' []) n)"

lemma nat_of_name_Abs_eq [simp]: "nat_of_name (Abs_name (Atom (Sort ''SyntaxN.name'' []) n)) = n"
  by (auto simp: nat_of_name_def atom_name_def Abs_name_inverse)

lemma nat_of_name_name_eq [simp]: "nat_of_name (name_of_nat n) = n"
  by (simp add: name_of_nat_def)

lemma name_of_nat_nat_of_name [simp]: "name_of_nat (nat_of_name i) = i"
  by (metis nat_of_name_inject nat_of_name_name_eq)

lemma HPair_neq_ORD_OF [simp]: "HPair x y \<noteq> ORD_OF i"
  by (metis Not_Ord_hpair Ord_ord_of eval_tm_HPair eval_tm_ORD_OF)

text\<open>Infinite support, so we cannot use nominal primrec.\<close>
function quot_dbtm :: "dbtm \<Rightarrow> tm"
  where
   "quot_dbtm DBZero = Zero"
 | "quot_dbtm (DBVar name) = ORD_OF (Suc (nat_of_name name))"
 | "quot_dbtm (DBInd k) = HPair (HTuple 6) (ORD_OF k)"
 | "quot_dbtm (DBEats t u) = HPair (HTuple 1) (HPair (quot_dbtm t) (quot_dbtm u))"
by (rule dbtm.exhaust) auto

termination
  by lexicographic_order

lemma quot_dbtm_inject_lemma [simp]: "\<lbrakk>quot_dbtm t\<rbrakk>e = \<lbrakk>quot_dbtm u\<rbrakk>e \<longleftrightarrow> t=u"
proof (induct t arbitrary: u rule: dbtm.induct)
  case DBZero show ?case
    by (induct u rule: dbtm.induct) auto
next
  case (DBVar name) show ?case
    by (induct u rule: dbtm.induct) (auto simp: hpair_neq_Ord')
next
  case (DBInd k) show ?case
    by (induct u rule: dbtm.induct) (auto simp: hpair_neq_Ord hpair_neq_Ord')
next
  case (DBEats t1 t2) thus ?case
    by (induct u rule: dbtm.induct) (simp_all add: hpair_neq_Ord)
qed

lemma quot_dbtm_inject [iff]: "quot_dbtm t = quot_dbtm u \<longleftrightarrow> t=u"
  by (metis quot_dbtm_inject_lemma)

subsection \<open>Quotations of de Bruijn formulas\<close>

text\<open>Infinite support, so we cannot use nominal primrec.\<close>
function quot_dbfm :: "dbfm \<Rightarrow> tm"
  where
   "quot_dbfm (DBMem t u) = HPair (HTuple 0) (HPair (quot_dbtm t) (quot_dbtm u))"
 | "quot_dbfm (DBEq t u) = HPair (HTuple 2) (HPair (quot_dbtm t) (quot_dbtm u))"
 | "quot_dbfm (DBDisj A B) = HPair (HTuple 3) (HPair (quot_dbfm A) (quot_dbfm B))"
 | "quot_dbfm (DBNeg A) = HPair (HTuple 4) (quot_dbfm A)"
 | "quot_dbfm (DBEx A) = HPair (HTuple 5) (quot_dbfm A)"
by (rule_tac y=x in dbfm.exhaust, auto)

termination
  by lexicographic_order

lemma htuple_minus_1: "n > 0 \<Longrightarrow> htuple n = \<langle>0, htuple (n - 1)\<rangle>"
  by (metis Suc_diff_1 htuple.simps(2))

lemma HTuple_minus_1: "n > 0 \<Longrightarrow> HTuple n = HPair Zero (HTuple (n - 1))"
  by (metis Suc_diff_1 HTuple.simps(2))

lemmas HTS = HTuple_minus_1 HTuple.simps \<comment> \<open>for freeness reasoning on codes\<close>

lemma quot_dbfm_inject_lemma [simp]: "\<lbrakk>quot_dbfm A\<rbrakk>e = \<lbrakk>quot_dbfm B\<rbrakk>e \<longleftrightarrow> A=B"
proof (induct A arbitrary: B rule: dbfm.induct)
  case (DBMem t u) show ?case
    by (induct B rule: dbfm.induct) (simp_all add: htuple_minus_1)
next
  case (DBEq t u) show ?case
    by (induct B rule: dbfm.induct) (auto simp: htuple_minus_1)
next
  case (DBDisj A B') thus ?case
    by (induct B rule: dbfm.induct) (simp_all add: htuple_minus_1)
next
  case (DBNeg A) thus ?case
    by (induct B rule: dbfm.induct) (simp_all add: htuple_minus_1)
next
  case (DBEx A) thus ?case
    by (induct B rule: dbfm.induct) (simp_all add: htuple_minus_1)
qed


class quot =
  fixes quot :: "'a \<Rightarrow> tm"  ("\<lceil>_\<rceil>")

instantiation tm :: quot
begin
  definition quot_tm :: "tm \<Rightarrow> tm"
    where "quot_tm t = quot_dbtm (trans_tm [] t)"
  
  instance ..
end

lemma quot_dbtm_fresh [simp]: "s \<sharp> (quot_dbtm t)"
  by (induct t rule: dbtm.induct) auto

lemma quot_tm_fresh [simp]: fixes t::tm shows "s \<sharp> \<lceil>t\<rceil>"
  by (simp add: quot_tm_def)

lemma quot_Zero [simp]: "\<lceil>Zero\<rceil> = Zero"
  by (simp add: quot_tm_def)

lemma quot_Var: "\<lceil>Var x\<rceil> = SUCC (ORD_OF (nat_of_name x))"
  by (simp add: quot_tm_def)

lemma quot_Eats: "\<lceil>Eats x y\<rceil> = HPair (HTuple 1) (HPair \<lceil>x\<rceil> \<lceil>y\<rceil>)"
  by (simp add: quot_tm_def)

text\<open>irrelevance of the environment for quotations, because they are ground terms\<close>
lemma eval_quot_dbtm_ignore:
    "\<lbrakk>quot_dbtm t\<rbrakk>e = \<lbrakk>quot_dbtm t\<rbrakk>e'"
  by (induct t rule: dbtm.induct) auto

lemma eval_quot_dbfm_ignore:
    "\<lbrakk>quot_dbfm A\<rbrakk>e = \<lbrakk>quot_dbfm A\<rbrakk>e'"
  by (induct A rule: dbfm.induct) (auto intro: eval_quot_dbtm_ignore)


instantiation fm :: quot
begin
  definition quot_fm :: "fm \<Rightarrow> tm"
    where "quot_fm A = quot_dbfm (trans_fm [] A)"
  
  instance ..
end

lemma quot_dbfm_fresh [simp]: "s \<sharp> (quot_dbfm A)"
  by (induct A rule: dbfm.induct) auto

lemma quot_fm_fresh [simp]: fixes A::fm shows "s \<sharp> \<lceil>A\<rceil>"
  by (simp add: quot_fm_def)

lemma quot_fm_permute [simp]: fixes A:: fm shows "p \<bullet> \<lceil>A\<rceil> = \<lceil>A\<rceil>"
  by (metis fresh_star_def perm_supp_eq quot_fm_fresh)

lemma quot_Mem: "\<lceil>x IN y\<rceil> = HPair (HTuple 0) (HPair (\<lceil>x\<rceil>) (\<lceil>y\<rceil>))"
  by (simp add: quot_fm_def quot_tm_def)

lemma quot_Eq: "\<lceil>x EQ y\<rceil> = HPair (HTuple 2) (HPair (\<lceil>x\<rceil>) (\<lceil>y\<rceil>))"
  by (simp add: quot_fm_def quot_tm_def)

lemma quot_Disj: "\<lceil>A OR B\<rceil> = HPair (HTuple 3) (HPair (\<lceil>A\<rceil>) (\<lceil>B\<rceil>))"
  by (simp add: quot_fm_def)

lemma quot_Neg: "\<lceil>Neg A\<rceil> = HPair (HTuple 4) (\<lceil>A\<rceil>)"
  by (simp add: quot_fm_def)

lemma quot_Ex: "\<lceil>Ex i A\<rceil> = HPair (HTuple 5) (quot_dbfm (trans_fm [i] A))"
  by (simp add: quot_fm_def)

lemma eval_quot_fm_ignore: fixes A:: fm shows "\<lbrakk>\<lceil>A\<rceil>\<rbrakk>e = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e'"
  by (metis eval_quot_dbfm_ignore quot_fm_def)

lemmas quot_simps = quot_Var quot_Eats quot_Eq quot_Mem quot_Disj quot_Neg quot_Ex

section\<open>Definitions Involving Coding\<close>

definition q_Var :: "name \<Rightarrow> hf"
  where "q_Var i \<equiv> succ (ord_of (nat_of_name i))"

definition q_Ind :: "hf \<Rightarrow> hf"
  where "q_Ind k \<equiv>  \<langle>htuple 6, k\<rangle>"

abbreviation Q_Eats :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "Q_Eats t u \<equiv> HPair (HTuple (Suc 0)) (HPair t u)"

definition q_Eats :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "q_Eats x y \<equiv> \<langle>htuple 1, x, y\<rangle>"

abbreviation Q_Succ :: "tm \<Rightarrow> tm"
  where "Q_Succ t \<equiv> Q_Eats t t"

definition q_Succ :: "hf \<Rightarrow> hf"
  where "q_Succ x \<equiv> q_Eats x x"

lemma quot_Succ: "\<lceil>SUCC x\<rceil> = Q_Succ \<lceil>x\<rceil>"
  by (auto simp: SUCC_def quot_Eats)

abbreviation Q_HPair :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "Q_HPair t u \<equiv>
           Q_Eats (Q_Eats Zero (Q_Eats (Q_Eats Zero u) t))
                  (Q_Eats (Q_Eats Zero t) t)"

definition q_HPair :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "q_HPair x y \<equiv>
           q_Eats (q_Eats 0 (q_Eats (q_Eats 0 y) x))
                  (q_Eats (q_Eats 0 x) x)"

abbreviation Q_Mem :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "Q_Mem t u \<equiv> HPair (HTuple 0) (HPair t u)"

definition q_Mem :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "q_Mem x y \<equiv> \<langle>htuple 0, x, y\<rangle>"

abbreviation Q_Eq :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "Q_Eq t u \<equiv> HPair (HTuple 2) (HPair t u)"

definition q_Eq :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "q_Eq x y \<equiv> \<langle>htuple 2, x, y\<rangle>"

abbreviation Q_Disj :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "Q_Disj t u \<equiv> HPair (HTuple 3) (HPair t u)"

definition q_Disj :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "q_Disj x y \<equiv> \<langle>htuple 3, x, y\<rangle>"

abbreviation Q_Neg :: "tm \<Rightarrow> tm"
  where "Q_Neg t \<equiv> HPair (HTuple 4) t"

definition q_Neg :: "hf \<Rightarrow> hf"
  where "q_Neg x \<equiv> \<langle>htuple 4, x\<rangle>"

abbreviation Q_Conj :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "Q_Conj t u \<equiv> Q_Neg (Q_Disj (Q_Neg t) (Q_Neg u))"

definition q_Conj :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "q_Conj t u \<equiv> q_Neg (q_Disj (q_Neg t) (q_Neg u))"

abbreviation Q_Imp :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "Q_Imp t u \<equiv> Q_Disj (Q_Neg t) u"

definition q_Imp :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "q_Imp t u \<equiv> q_Disj (q_Neg t) u"

abbreviation Q_Ex :: "tm \<Rightarrow> tm"
  where "Q_Ex t \<equiv> HPair (HTuple 5) t"

definition q_Ex :: "hf \<Rightarrow> hf"
  where "q_Ex x \<equiv> \<langle>htuple 5, x\<rangle>"

abbreviation Q_All :: "tm \<Rightarrow> tm"
  where "Q_All t \<equiv> Q_Neg (Q_Ex (Q_Neg t))"

definition q_All :: "hf \<Rightarrow> hf"
  where "q_All x \<equiv> q_Neg (q_Ex (q_Neg x))"

lemmas q_defs = q_Var_def q_Ind_def q_Eats_def q_HPair_def q_Eq_def q_Mem_def
                q_Disj_def q_Neg_def q_Conj_def q_Imp_def q_Ex_def q_All_def

lemma q_Eats_iff [iff]: "q_Eats x y = q_Eats x' y' \<longleftrightarrow> x=x' \<and> y=y'"
  by (metis hpair_iff q_Eats_def)

lemma quot_subst_eq: "\<lceil>A(i::=t)\<rceil> = quot_dbfm (subst_dbfm (trans_tm [] t) i (trans_fm [] A))"
  by (metis quot_fm_def subst_fm_trans_commute)

lemma Q_Succ_cong: "H \<turnstile> x EQ x' \<Longrightarrow> H \<turnstile> Q_Succ x EQ Q_Succ x'"
  by (metis HPair_cong Refl)

  
section\<open>Quotations are Injective\<close>

subsection\<open>Terms\<close>

lemma eval_tm_inject [simp]: fixes t::tm shows "\<lbrakk>\<lceil>t\<rceil>\<rbrakk> e = \<lbrakk>\<lceil>u\<rceil>\<rbrakk> e \<longleftrightarrow> t=u"
proof (induct t arbitrary: u rule: tm.induct)
  case Zero thus ?case
    by (cases u rule: tm.exhaust) (auto simp: quot_Var quot_Eats)
next
  case (Var i) thus ?case
    apply (cases u rule: tm.exhaust, auto)
    apply (auto simp: quot_Var quot_Eats)
    done
next
  case (Eats t1 t2) thus ?case
    apply (cases u rule: tm.exhaust, auto)
    apply (auto simp: quot_Eats quot_Var)
    done
qed

subsection\<open>Formulas\<close>

lemma eval_fm_inject [simp]: fixes A::fm shows "\<lbrakk>\<lceil>A\<rceil>\<rbrakk> e = \<lbrakk>\<lceil>B\<rceil>\<rbrakk> e \<longleftrightarrow> A=B"
proof (nominal_induct B arbitrary: A rule: fm.strong_induct)
  case (Mem tm1 tm2) thus ?case
    by (cases A rule: fm.exhaust, auto simp: quot_simps htuple_minus_1)
next
  case (Eq tm1 tm2) thus ?case
    by (cases A rule: fm.exhaust, auto simp: quot_simps htuple_minus_1)
next
  case (Neg \<alpha>) thus ?case
    by (cases A rule: fm.exhaust, auto simp: quot_simps htuple_minus_1)
next
  case (Disj fm1 fm2)
  thus ?case
    by (cases A rule: fm.exhaust, auto simp: quot_simps htuple_minus_1)
next
  case (Ex i \<alpha>)
  thus ?case
    apply (induct A arbitrary: i rule: fm.induct)
    apply (auto simp: trans_fm_perm quot_simps htuple_minus_1 Abs1_eq_iff_all)
    by (metis (no_types) Abs1_eq_iff_all(3) dbfm.eq_iff(5) fm.eq_iff(5) fresh_Nil trans_fm.simps(5))
qed

subsection\<open>The set \<open>\<Gamma>\<close> of Definition 1.1, constant terms used for coding\<close>

inductive coding_tm :: "tm \<Rightarrow> bool"
  where
    Ord:    "\<exists>i. x = ORD_OF i \<Longrightarrow> coding_tm x"
  | HPair:  "coding_tm x \<Longrightarrow> coding_tm y \<Longrightarrow> coding_tm (HPair x y)"

declare coding_tm.intros [intro]

lemma coding_tm_Zero [intro]: "coding_tm Zero"
  by (metis ORD_OF.simps(1) Ord)

lemma coding_tm_HTuple [intro]: "coding_tm (HTuple k)"
  by (induct k, auto)

inductive_simps coding_tm_HPair [simp]: "coding_tm (HPair x y)"

lemma quot_dbtm_coding [simp]: "coding_tm (quot_dbtm t)"
  apply (induct t rule: dbtm.induct, auto)
  apply (metis ORD_OF.simps(2) Ord)
  done

lemma quot_dbfm_coding [simp]: "coding_tm (quot_dbfm fm)"
  by (induct fm rule: dbfm.induct, auto)

lemma quot_fm_coding: fixes A::fm shows "coding_tm \<lceil>A\<rceil>"
  by (metis quot_dbfm_coding quot_fm_def)

inductive coding_hf :: "hf \<Rightarrow> bool"
  where
    Ord:    "\<exists>i. x = ord_of i \<Longrightarrow> coding_hf x"
  | HPair:  "coding_hf x \<Longrightarrow> coding_hf y \<Longrightarrow> coding_hf (\<langle>x,y\<rangle>)"

declare coding_hf.intros [intro]

lemma coding_hf_0 [intro]: "coding_hf 0"
  by (metis coding_hf.Ord ord_of.simps(1))

inductive_simps coding_hf_hpair [simp]: "coding_hf (\<langle>x,y\<rangle>)"

lemma coding_tm_hf [simp]: "coding_tm t \<Longrightarrow> coding_hf \<lbrakk>t\<rbrakk>e"
  by (induct t rule: coding_tm.induct) auto

  
section \<open>V-Coding for terms and formulas, for the Second Theorem\<close>

text\<open>Infinite support, so we cannot use nominal primrec.\<close>
function vquot_dbtm :: "name set \<Rightarrow> dbtm \<Rightarrow> tm"
  where
   "vquot_dbtm V DBZero = Zero"
 | "vquot_dbtm V (DBVar name) = (if name \<in> V then Var name
                                 else ORD_OF (Suc (nat_of_name name)))"
 | "vquot_dbtm V (DBInd k) = HPair (HTuple 6) (ORD_OF k)"
 | "vquot_dbtm V (DBEats t u) = HPair (HTuple 1) (HPair (vquot_dbtm V t) (vquot_dbtm V u))"
by (auto, rule_tac y=b in dbtm.exhaust, auto)

termination
  by lexicographic_order

lemma fresh_vquot_dbtm [simp]: "i \<sharp> vquot_dbtm V tm \<longleftrightarrow> i \<sharp> tm \<or> i \<notin> atom ` V"
  by (induct tm rule: dbtm.induct) (auto simp: fresh_at_base pure_fresh)

text\<open>Infinite support, so we cannot use nominal primrec.\<close>
function vquot_dbfm :: "name set \<Rightarrow> dbfm \<Rightarrow> tm"
  where
   "vquot_dbfm V (DBMem t u) = HPair (HTuple 0) (HPair (vquot_dbtm V t) (vquot_dbtm V u))"
 | "vquot_dbfm V (DBEq t u) = HPair (HTuple 2) (HPair (vquot_dbtm V t) (vquot_dbtm V u))"
 | "vquot_dbfm V (DBDisj A B) = HPair (HTuple 3) (HPair (vquot_dbfm V A) (vquot_dbfm V B))"
 | "vquot_dbfm V (DBNeg A) = HPair (HTuple 4) (vquot_dbfm V A)"
 | "vquot_dbfm V (DBEx A) = HPair (HTuple 5) (vquot_dbfm V A)"
by (auto, rule_tac y=b in dbfm.exhaust, auto)

termination
  by lexicographic_order

lemma fresh_vquot_dbfm [simp]: "i \<sharp> vquot_dbfm V fm \<longleftrightarrow> i \<sharp> fm \<or> i \<notin> atom ` V"
  by (induct fm rule: dbfm.induct) (auto simp: HPair_def HTuple_minus_1)

class vquot =
  fixes vquot :: "'a \<Rightarrow> name set \<Rightarrow> tm"  ("\<lfloor>_\<rfloor>_"  [0,1000]1000)

instantiation tm :: vquot
begin
  definition vquot_tm :: "tm \<Rightarrow> name set \<Rightarrow> tm"
    where "vquot_tm t V = vquot_dbtm V (trans_tm [] t)"
  instance ..
end

lemma vquot_dbtm_empty [simp]: "vquot_dbtm {} t = quot_dbtm t"
  by (induct t rule: dbtm.induct) auto

lemma vquot_tm_empty [simp]: fixes t::tm shows "\<lfloor>t\<rfloor>{} = \<lceil>t\<rceil>"
  by (simp add: vquot_tm_def quot_tm_def)

lemma vquot_dbtm_eq: "atom ` V \<inter> supp t = atom ` W \<inter> supp t \<Longrightarrow> vquot_dbtm V t = vquot_dbtm W t"
  by (induct t rule: dbtm.induct) (auto simp: image_iff, blast+)

instantiation fm :: vquot
begin
  definition vquot_fm :: "fm \<Rightarrow> name set \<Rightarrow> tm"
    where "vquot_fm A V = vquot_dbfm V (trans_fm [] A)"
  instance ..
end

lemma vquot_fm_fresh [simp]: fixes A::fm shows "i \<sharp> \<lfloor>A\<rfloor>V \<longleftrightarrow> i \<sharp> A \<or> i \<notin> atom ` V"
  by (simp add: vquot_fm_def)

lemma vquot_dbfm_empty [simp]: "vquot_dbfm {} A = quot_dbfm A"
  by (induct A rule: dbfm.induct) auto

lemma vquot_fm_empty [simp]: fixes A::fm shows "\<lfloor>A\<rfloor>{} = \<lceil>A\<rceil>"
  by (simp add: vquot_fm_def quot_fm_def)

lemma vquot_dbfm_eq: "atom ` V \<inter> supp A = atom ` W \<inter> supp A \<Longrightarrow> vquot_dbfm V A = vquot_dbfm W A"
  by (induct A rule: dbfm.induct) (auto simp: intro!: vquot_dbtm_eq, blast+)

lemma vquot_fm_insert:
  fixes A::fm shows "atom i \<notin> supp A \<Longrightarrow> \<lfloor>A\<rfloor>(insert i V) = \<lfloor>A\<rfloor>V"
  by (auto simp: vquot_fm_def supp_conv_fresh intro: vquot_dbfm_eq)

declare HTuple.simps [simp del]

end
