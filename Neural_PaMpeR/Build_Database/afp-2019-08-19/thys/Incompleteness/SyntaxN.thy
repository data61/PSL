chapter\<open>Syntax of Terms and Formulas using Nominal Logic\<close>

theory SyntaxN
imports Nominal2.Nominal2 HereditarilyFinite.OrdArith
begin

section\<open>Terms and Formulas\<close>

subsection\<open>Hf is a pure permutation type\<close>

instantiation hf :: pt
begin
  definition "p \<bullet> (s::hf) = s"
  instance
    by standard (simp_all add: permute_hf_def)
end

instance hf :: pure
  proof qed (rule permute_hf_def)

atom_decl name

declare fresh_set_empty [simp]

lemma supp_name [simp]: fixes i::name shows "supp i = {atom i}"
  by (rule supp_at_base)

subsection\<open>The datatypes\<close>

nominal_datatype tm = Zero | Var name | Eats tm tm

nominal_datatype fm =
    Mem tm tm    (infixr "IN" 150)
  | Eq tm tm     (infixr "EQ" 150)
  | Disj fm fm   (infixr "OR" 130)
  | Neg fm
  | Ex x::name f::fm binds x in f

text \<open>Mem, Eq are atomic formulas; Disj, Neg, Ex are non-atomic\<close>

declare tm.supp [simp] fm.supp [simp]

subsection\<open>Substitution\<close>

nominal_function subst :: "name \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
  where
   "subst i x Zero       = Zero"
 | "subst i x (Var k)    = (if i=k then x else Var k)"
 | "subst i x (Eats t u) = Eats (subst i x t) (subst i x u)"
by (auto simp: eqvt_def subst_graph_aux_def) (metis tm.strong_exhaust)

nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_subst_if [simp]:
  "j \<sharp> subst i x t \<longleftrightarrow> (atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  by (induct t rule: tm.induct) (auto simp: fresh_at_base)

lemma forget_subst_tm [simp]: "atom a \<sharp> tm \<Longrightarrow> subst a x tm = tm"
  by (induct tm rule: tm.induct) (simp_all add: fresh_at_base)

lemma subst_tm_id [simp]: "subst a (Var a) tm = tm"
  by (induct tm rule: tm.induct) simp_all

lemma subst_tm_commute [simp]:
  "atom j \<sharp> tm \<Longrightarrow> subst j u (subst i t tm) = subst i (subst j u t) tm"
  by (induct tm rule: tm.induct) (auto simp: fresh_Pair)

lemma subst_tm_commute2 [simp]:
  "atom j \<sharp> t \<Longrightarrow> atom i \<sharp> u \<Longrightarrow> i \<noteq> j \<Longrightarrow> subst j u (subst i t tm) = subst i t (subst j u tm)"
  by (induct tm rule: tm.induct) auto

lemma repeat_subst_tm [simp]: "subst i u (subst i t tm) = subst i (subst i u t) tm"
  by (induct tm rule: tm.induct) auto

nominal_function  subst_fm :: "fm \<Rightarrow> name \<Rightarrow> tm \<Rightarrow> fm" ("_'(_::=_')" [1000, 0, 0] 200)
  where
    Mem:  "(Mem t u)(i::=x)  = Mem (subst i x t) (subst i x u)"
  | Eq:   "(Eq t u)(i::=x)   = Eq  (subst i x t) (subst i x u)"
  | Disj: "(Disj A B)(i::=x) = Disj (A(i::=x)) (B(i::=x))"
  | Neg:  "(Neg A)(i::=x)    = Neg  (A(i::=x))"
  | Ex:   "atom j \<sharp> (i, x) \<Longrightarrow> (Ex j A)(i::=x) = Ex j (A(i::=x))"
apply (simp add: eqvt_def subst_fm_graph_aux_def)
apply auto [16]
apply (rule_tac y=a and c="(aa, b)" in fm.strong_exhaust)
apply (auto simp: eqvt_at_def fresh_star_def fresh_Pair fresh_at_base)
apply (metis flip_at_base_simps(3) flip_fresh_fresh)
done

nominal_termination (eqvt)
  by lexicographic_order

lemma size_subst_fm [simp]: "size (A(i::=x)) = size A"
  by (nominal_induct A avoiding: i x rule: fm.strong_induct) auto

lemma forget_subst_fm [simp]: "atom a \<sharp> A \<Longrightarrow> A(a::=x) = A"
  by (nominal_induct A avoiding: a x rule: fm.strong_induct) (auto simp: fresh_at_base)

lemma subst_fm_id [simp]: "A(a::=Var a) = A"
  by (nominal_induct A avoiding: a rule: fm.strong_induct) (auto simp: fresh_at_base)

lemma fresh_subst_fm_if [simp]:
  "j \<sharp> (A(i::=x)) \<longleftrightarrow> (atom i \<sharp> A \<and> j \<sharp> A) \<or> (j \<sharp> x \<and> (j \<sharp> A \<or> j = atom i))"
  by (nominal_induct A avoiding: i x rule: fm.strong_induct) (auto simp: fresh_at_base)

lemma subst_fm_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (A(i::=t))(j::=u) = A(i ::= subst j u t)"
  by (nominal_induct A avoiding: i j t u rule: fm.strong_induct) (auto simp: fresh_at_base)

lemma repeat_subst_fm [simp]: "(A(i::=t))(i::=u) = A(i ::= subst i u t)"
  by (nominal_induct A avoiding: i t u rule: fm.strong_induct) auto

lemma subst_fm_Ex_with_renaming:
  "atom i' \<sharp> (A, i, j, t) \<Longrightarrow> (Ex i A)(j ::= t) = Ex i' (((i \<leftrightarrow> i') \<bullet> A)(j ::= t))"
  by (rule subst [of "Ex i' ((i \<leftrightarrow> i') \<bullet> A)" "Ex i A"])
     (auto simp: Abs1_eq_iff flip_def swap_commute)

text \<open>the simplifier cannot apply the rule above, because
it introduces a new variable at the right hand side.\<close>

simproc_setup subst_fm_renaming ("(Ex i A)(j ::= t)") = \<open>fn _ => fn ctxt => fn ctrm =>
  let
     val _ $ (_ $ i $ A) $ j $ t = Thm.term_of ctrm

     val atoms = Simplifier.prems_of ctxt
      |> map_filter (fn thm => case Thm.prop_of thm of
           _ $ (Const (@{const_name fresh}, _) $ atm $ _) => SOME (atm) | _ => NONE)
      |> distinct ((=))

     fun get_thm atm =
       let
         val goal = HOLogic.mk_Trueprop (mk_fresh atm (HOLogic.mk_tuple [A, i, j, t]))
       in
         SOME ((Goal.prove ctxt [] [] goal (K (asm_full_simp_tac ctxt 1)))
           RS @{thm subst_fm_Ex_with_renaming} RS eq_reflection)
         handle ERROR _ => NONE
       end
  in
    get_first get_thm atoms
  end
\<close>

subsection\<open>Semantics\<close>

definition e0 :: "(name, hf) finfun"    \<comment> \<open>the null environment\<close>
  where "e0 \<equiv> finfun_const 0"

nominal_function eval_tm :: "(name, hf) finfun \<Rightarrow> tm \<Rightarrow> hf"
  where
   "eval_tm e Zero = 0"
 | "eval_tm e (Var k) = finfun_apply e k"
 | "eval_tm e (Eats t u) = eval_tm e t \<triangleleft> eval_tm e u"
by (auto simp: eqvt_def eval_tm_graph_aux_def) (metis tm.strong_exhaust)

nominal_termination (eqvt)
  by lexicographic_order

syntax
  "_EvalTm" :: "tm \<Rightarrow> (name, hf) finfun \<Rightarrow> hf"      ("\<lbrakk>_\<rbrakk>_" [0,1000]1000)

translations
  "\<lbrakk>tm\<rbrakk>e"    == "CONST eval_tm e tm"

nominal_function eval_fm :: "(name, hf) finfun \<Rightarrow> fm \<Rightarrow> bool"
  where
   "eval_fm e (t IN u) \<longleftrightarrow> \<lbrakk>t\<rbrakk>e \<^bold>\<in> \<lbrakk>u\<rbrakk>e"
 | "eval_fm e (t EQ u) \<longleftrightarrow> \<lbrakk>t\<rbrakk>e = \<lbrakk>u\<rbrakk>e"
 | "eval_fm e (A OR B) \<longleftrightarrow> eval_fm e A \<or> eval_fm e B"
 | "eval_fm e (Neg A) \<longleftrightarrow> (~ eval_fm e A)"
 | "atom k \<sharp> e \<Longrightarrow> eval_fm e (Ex k A) \<longleftrightarrow> (\<exists>x. eval_fm (finfun_update e k x) A)"
apply(simp add: eqvt_def eval_fm_graph_aux_def)
apply(auto del: iffI)[16]
apply(rule_tac y=b and c="(a)" in fm.strong_exhaust)
apply(auto simp: fresh_star_def)[5]
using [[simproc del: alpha_lst]] apply clarsimp
apply(erule_tac c="(ea)" in Abs_lst1_fcb2')
apply(rule pure_fresh)
apply(simp add: fresh_star_def)
apply (simp_all add: eqvt_at_def)
apply (simp_all add: perm_supp_eq)
done

nominal_termination (eqvt)
  by lexicographic_order

lemma eval_tm_rename:
  assumes "atom k' \<sharp> t"
  shows "\<lbrakk>t\<rbrakk>(finfun_update e k x) = \<lbrakk>(k' \<leftrightarrow> k) \<bullet> t\<rbrakk>(finfun_update e k' x)"
using assms
by (induct t rule: tm.induct) (auto simp: permute_flip_at)

lemma eval_fm_rename:
  assumes "atom k' \<sharp> A"
  shows "eval_fm (finfun_update e k x) A = eval_fm (finfun_update e k' x) ((k' \<leftrightarrow> k) \<bullet> A)"
using assms
apply (nominal_induct A avoiding: e k k' x rule: fm.strong_induct)
apply (simp_all add: eval_tm_rename[symmetric], metis)
apply (simp add: fresh_finfun_update fresh_at_base finfun_update_twist)
done

lemma better_ex_eval_fm[simp]:
  "eval_fm e (Ex k A) \<longleftrightarrow> (\<exists>x. eval_fm (finfun_update e k x) A)"
proof -
  obtain k'::name where k': "atom k' \<sharp> (k, e, A)"
    by (rule obtain_fresh)
  then have eq: "Ex k' ((k' \<leftrightarrow> k) \<bullet> A) = Ex k A"
    by (simp add: Abs1_eq_iff flip_def)
  have "eval_fm e (Ex k' ((k' \<leftrightarrow> k) \<bullet> A)) = (\<exists>x. eval_fm (finfun_update e k' x) ((k' \<leftrightarrow> k) \<bullet> A))"
    using k' by simp
  also have "... = (\<exists>x. eval_fm (finfun_update e k x) A)"
    by (metis eval_fm_rename k' fresh_Pair)
  finally show ?thesis
    by (metis eq)
qed

lemma forget_eval_tm [simp]: "atom i \<sharp> t \<Longrightarrow>  \<lbrakk>t\<rbrakk>(finfun_update e i x) = \<lbrakk>t\<rbrakk>e"
  by (induct t rule: tm.induct) (simp_all add: fresh_at_base)

lemma forget_eval_fm [simp]:
   "atom k \<sharp> A \<Longrightarrow> eval_fm (finfun_update e k x) A = eval_fm e A"
  by (nominal_induct A avoiding: k e rule: fm.strong_induct)
     (simp_all add: fresh_at_base finfun_update_twist)

lemma eval_subst_tm: "\<lbrakk>subst i t u\<rbrakk>e = \<lbrakk>u\<rbrakk>(finfun_update e i \<lbrakk>t\<rbrakk>e)"
  by (induct u rule: tm.induct) (auto)

lemma eval_subst_fm: "eval_fm e (fm(i::= t)) = eval_fm (finfun_update e i \<lbrakk>t\<rbrakk>e) fm"
  by (nominal_induct fm avoiding: i t e rule: fm.strong_induct)
     (simp_all add: eval_subst_tm finfun_update_twist fresh_at_base)

subsection\<open>Derived syntax\<close>

subsubsection\<open>Ordered pairs\<close>

definition HPair :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "HPair a b = Eats (Eats Zero (Eats (Eats Zero b) a)) (Eats (Eats Zero a) a)"

lemma HPair_eqvt [eqvt]: "(p \<bullet> HPair a b) = HPair (p \<bullet> a) (p \<bullet> b)"
  by (auto simp: HPair_def)

lemma fresh_HPair [simp]: "x \<sharp> HPair a b \<longleftrightarrow> (x \<sharp> a \<and> x \<sharp> b)"
  by (auto simp: HPair_def)

lemma HPair_injective_iff [iff]: "HPair a b = HPair a' b' \<longleftrightarrow> (a = a' \<and> b = b')"
  by (auto simp: HPair_def)

lemma subst_tm_HPair [simp]: "subst i x (HPair a b) = HPair (subst i x a) (subst i x b)"
  by (auto simp: HPair_def)

lemma eval_tm_HPair [simp]: "\<lbrakk>HPair a b\<rbrakk>e = hpair \<lbrakk>a\<rbrakk>e \<lbrakk>b\<rbrakk>e"
  by (auto simp: HPair_def hpair_def)

subsubsection\<open>Ordinals\<close>

definition
  SUCC  :: "tm \<Rightarrow> tm"  where
    "SUCC x \<equiv> Eats x x"

fun ORD_OF :: "nat \<Rightarrow> tm"
  where
   "ORD_OF 0 = Zero"
 | "ORD_OF (Suc k) = SUCC (ORD_OF k)"

lemma eval_tm_SUCC [simp]: "\<lbrakk>SUCC t\<rbrakk>e = succ \<lbrakk>t\<rbrakk>e"
  by (simp add: SUCC_def succ_def)

lemma SUCC_fresh_iff [simp]: "a \<sharp> SUCC t \<longleftrightarrow> a \<sharp> t"
  by (simp add: SUCC_def)

lemma SUCC_eqvt [eqvt]: "(p \<bullet> SUCC a) = SUCC (p \<bullet> a)"
  by (simp add: SUCC_def)

lemma SUCC_subst [simp]: "subst i t (SUCC k) = SUCC (subst i t k)"
  by (simp add: SUCC_def)

lemma eval_tm_ORD_OF [simp]: "\<lbrakk>ORD_OF n\<rbrakk>e = ord_of n"
  by (induct n) auto

lemma ORD_OF_fresh [simp]: "a \<sharp> ORD_OF n"
  by (induct n) (auto simp: SUCC_def)

lemma ORD_OF_eqvt [eqvt]: "(p \<bullet> ORD_OF n) = ORD_OF (p \<bullet> n)"
  by (induct n) (auto simp: permute_pure SUCC_eqvt)

subsection\<open>Derived logical connectives\<close>

abbreviation Imp :: "fm \<Rightarrow> fm \<Rightarrow> fm"   (infixr "IMP" 125)
  where "Imp A B \<equiv> Disj (Neg A) B"

abbreviation All :: "name \<Rightarrow> fm \<Rightarrow> fm"
  where "All i A \<equiv> Neg (Ex i (Neg A))"

abbreviation All2 :: "name \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm" \<comment> \<open>bounded universal quantifier, for Sigma formulas\<close>
  where "All2 i t A \<equiv> All i ((Var i IN t) IMP A)"

subsubsection\<open>Conjunction\<close>

definition Conj :: "fm \<Rightarrow> fm \<Rightarrow> fm"   (infixr "AND" 135)
  where "Conj A B \<equiv> Neg (Disj (Neg A) (Neg B))"

lemma Conj_eqvt [eqvt]: "p \<bullet> (A AND B) = (p \<bullet> A) AND (p \<bullet> B)"
  by (simp add: Conj_def)

lemma fresh_Conj [simp]: "a \<sharp> A AND B \<longleftrightarrow> (a \<sharp> A \<and> a \<sharp> B)"
  by (auto simp: Conj_def)

lemma supp_Conj [simp]: "supp (A AND B) = supp A \<union> supp B"
  by (auto simp: Conj_def)

lemma size_Conj [simp]: "size (A AND B) = size A + size B + 4"
  by (simp add: Conj_def)

lemma Conj_injective_iff [iff]: "(A AND B) = (A' AND B') \<longleftrightarrow> (A = A' \<and> B = B')"
  by (auto simp: Conj_def)

lemma subst_fm_Conj [simp]: "(A AND B)(i::=x) = (A(i::=x)) AND (B(i::=x))"
  by (auto simp: Conj_def)

lemma eval_fm_Conj [simp]: "eval_fm e (Conj A B) \<longleftrightarrow> (eval_fm e A \<and> eval_fm e B)"
  by (auto simp: Conj_def)

subsubsection\<open>If and only if\<close>

definition Iff :: "fm \<Rightarrow> fm \<Rightarrow> fm"   (infixr "IFF" 125)
  where "Iff A B = Conj (Imp A B) (Imp B A)"

lemma Iff_eqvt [eqvt]: "p \<bullet> (A IFF B) = (p \<bullet> A) IFF (p \<bullet> B)"
  by (simp add: Iff_def)

lemma fresh_Iff [simp]: "a \<sharp> A IFF B \<longleftrightarrow> (a \<sharp> A \<and> a \<sharp> B)"
  by (auto simp: Conj_def Iff_def)

lemma size_Iff [simp]: "size (A IFF B) = 2*(size A + size B) + 8"
  by (simp add: Iff_def)

lemma Iff_injective_iff [iff]: "(A IFF B) = (A' IFF B') \<longleftrightarrow> (A = A' \<and> B = B')"
  by (auto simp: Iff_def)

lemma subst_fm_Iff [simp]: "(A IFF B)(i::=x) = (A(i::=x)) IFF (B(i::=x))"
  by (auto simp: Iff_def)

lemma eval_fm_Iff [simp]: "eval_fm e (Iff A B) \<longleftrightarrow> (eval_fm e A  \<longleftrightarrow>  eval_fm e B)"
  by (auto simp: Iff_def)


section\<open>Axioms and Theorems\<close>

subsection\<open>Logical axioms\<close>

inductive_set boolean_axioms :: "fm set"
  where
    Ident:     "A IMP A \<in> boolean_axioms"
  | DisjI1:    "A IMP (A OR B) \<in> boolean_axioms"
  | DisjCont:  "(A OR A) IMP A \<in> boolean_axioms"
  | DisjAssoc: "(A OR (B OR C)) IMP ((A OR B) OR C) \<in> boolean_axioms"
  | DisjConj:  "(C OR A) IMP (((Neg C) OR B) IMP (A OR B)) \<in> boolean_axioms"

lemma boolean_axioms_hold: "A \<in> boolean_axioms \<Longrightarrow> eval_fm e A"
  by (induct rule: boolean_axioms.induct, auto)

inductive_set special_axioms :: "fm set" where
  I: "A(i::=x) IMP (Ex i A) \<in> special_axioms"

lemma special_axioms_hold: "A \<in> special_axioms \<Longrightarrow> eval_fm e A"
  by (induct rule: special_axioms.induct, auto) (metis eval_subst_fm)

inductive_set induction_axioms :: "fm set" where
  ind:
  "atom (j::name) \<sharp> (i,A)
   \<Longrightarrow> A(i::=Zero) IMP ((All i (All j (A IMP (A(i::= Var j) IMP A(i::= Eats(Var i)(Var j))))))
      IMP (All i A))
    \<in> induction_axioms"

lemma twist_forget_eval_fm [simp]:
   "atom j \<sharp> (i, A)
    \<Longrightarrow> eval_fm (finfun_update (finfun_update (finfun_update e i x) j y) i z) A =
        eval_fm (finfun_update e i z) A"
  by (metis finfun_update_twice finfun_update_twist forget_eval_fm fresh_Pair)

lemma induction_axioms_hold: "A \<in> induction_axioms \<Longrightarrow> eval_fm e A"
  by (induction rule: induction_axioms.induct) (auto simp: eval_subst_fm intro: hf_induct_ax)

subsection \<open>Concrete variables\<close>

declare Abs_name_inject[simp]

abbreviation
  "X0 \<equiv> Abs_name (Atom (Sort ''SyntaxN.name'' []) 0)"

abbreviation
  "X1 \<equiv> Abs_name (Atom (Sort ''SyntaxN.name'' []) (Suc 0))"
   \<comment> \<open>We prefer @{term "Suc 0"} because simplification will transform 1 to that form anyway.\<close>

abbreviation
  "X2 \<equiv> Abs_name (Atom (Sort ''SyntaxN.name'' []) 2)"

abbreviation
  "X3 \<equiv> Abs_name (Atom (Sort ''SyntaxN.name'' []) 3)"

abbreviation
  "X4 \<equiv> Abs_name (Atom (Sort ''SyntaxN.name'' []) 4)"


subsection\<open>The HF axioms\<close>

definition HF1 :: fm where  \<comment> \<open>the axiom @{term"z=0 \<longleftrightarrow> (\<forall>x. \<not> x \<^bold>\<in> z)"}\<close>
  "HF1 = (Var X0 EQ Zero) IFF (All X1 (Neg (Var X1 IN Var X0)))"

lemma HF1_holds: "eval_fm e HF1"
  by (auto simp: HF1_def)


definition HF2 :: fm where  \<comment> \<open>the axiom @{term"z = x \<triangleleft> y \<longleftrightarrow> (\<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<^bold>\<in> x | u=y)"}\<close>
  "HF2 \<equiv> Var X0 EQ Eats (Var X1) (Var X2) IFF
          All X3 (Var X3 IN Var X0 IFF Var X3 IN Var X1 OR Var X3 EQ Var X2)"

lemma HF2_holds: "eval_fm e HF2"
  by (auto simp: HF2_def)

definition HF_axioms where "HF_axioms = {HF1, HF2}"

lemma HF_axioms_hold: "A \<in> HF_axioms \<Longrightarrow> eval_fm e A"
  by (auto simp: HF_axioms_def HF1_holds HF2_holds)

subsection\<open>Equality axioms\<close>

definition refl_ax :: fm where
  "refl_ax = Var X1 EQ Var X1"

lemma refl_ax_holds: "eval_fm e refl_ax"
  by (auto simp: refl_ax_def)

definition eq_cong_ax :: fm where
  "eq_cong_ax = ((Var X1 EQ Var X2) AND (Var X3 EQ Var X4)) IMP
                ((Var X1 EQ Var X3) IMP (Var X2 EQ Var X4))"

lemma eq_cong_ax_holds: "eval_fm e eq_cong_ax"
  by (auto simp: Conj_def eq_cong_ax_def)

definition mem_cong_ax :: fm where
  "mem_cong_ax = ((Var X1 EQ Var X2) AND (Var X3 EQ Var X4)) IMP
                 ((Var X1 IN Var X3) IMP (Var X2 IN Var X4))"

lemma mem_cong_ax_holds: "eval_fm e mem_cong_ax"
  by (auto simp: Conj_def mem_cong_ax_def)

definition eats_cong_ax :: fm where
  "eats_cong_ax = ((Var X1 EQ Var X2) AND (Var X3 EQ Var X4)) IMP
                  ((Eats (Var X1) (Var X3)) EQ (Eats (Var X2) (Var X4)))"

lemma eats_cong_ax_holds: "eval_fm e eats_cong_ax"
  by (auto simp: Conj_def eats_cong_ax_def)

definition equality_axioms :: "fm set" where
  "equality_axioms = {refl_ax, eq_cong_ax, mem_cong_ax, eats_cong_ax}"

lemma equality_axioms_hold: "A \<in> equality_axioms \<Longrightarrow> eval_fm e A"
  by (auto simp: equality_axioms_def refl_ax_holds eq_cong_ax_holds mem_cong_ax_holds eats_cong_ax_holds)

subsection\<open>The proof system\<close>

text\<open>This arbitrary additional axiom generalises the statements of the incompleteness theorems
  and other results to any formal system stronger than the HF theory. The additional axiom
  could be the conjunction of any finite number of assertions. Any more general extension
  must be a form that can be formalised for the proof predicate.\<close>
consts  extra_axiom :: fm

specification (extra_axiom)
  extra_axiom_holds:  "eval_fm e extra_axiom"
  by (rule exI [where x = "Zero IN Eats Zero Zero"], auto)

inductive hfthm :: "fm set \<Rightarrow> fm \<Rightarrow> bool" (infixl "\<turnstile>" 55)
  where
    Hyp:    "A \<in> H \<Longrightarrow> H \<turnstile> A"
  | Extra:  "H \<turnstile> extra_axiom"
  | Bool:   "A \<in> boolean_axioms \<Longrightarrow> H \<turnstile> A"
  | Eq:     "A \<in> equality_axioms \<Longrightarrow> H \<turnstile> A"
  | Spec:   "A \<in> special_axioms \<Longrightarrow> H \<turnstile> A"
  | HF:     "A \<in> HF_axioms \<Longrightarrow> H \<turnstile> A"
  | Ind:    "A \<in> induction_axioms \<Longrightarrow> H \<turnstile> A"
  | MP:     "H \<turnstile> A IMP B \<Longrightarrow> H' \<turnstile> A \<Longrightarrow> H \<union> H' \<turnstile> B"
  | Exists: "H \<turnstile> A IMP B \<Longrightarrow> atom i \<sharp> B \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> (Ex i A) IMP B"

text\<open>Soundness theorem!\<close>
theorem hfthm_sound: assumes "H \<turnstile> A" shows "(\<forall>B\<in>H. eval_fm e B) \<Longrightarrow> eval_fm e A"
using assms
proof (induct arbitrary: e)
  case (Hyp A H) thus ?case
    by auto
next
  case (Extra H) thus ?case
    by (metis extra_axiom_holds)
next
  case (Bool A H) thus ?case
    by (metis boolean_axioms_hold)
next
  case (Eq A H) thus ?case
    by (metis equality_axioms_hold)
next
  case (Spec A H) thus ?case
    by (metis special_axioms_hold)
next
  case (HF A H) thus ?case
    by (metis HF_axioms_hold)
next
  case (Ind A H) thus ?case
    by (metis induction_axioms_hold)
next
  case (MP H A B H') thus ?case
    by auto
next
  case (Exists H A B i e) thus ?case
    by auto (metis forget_eval_fm)
qed

subsection\<open>Derived rules of inference\<close>

lemma contraction: "insert A (insert A H) \<turnstile> B \<Longrightarrow> insert A H \<turnstile> B"
  by (metis insert_absorb2)

lemma thin_Un: "H \<turnstile> A \<Longrightarrow> H \<union> H' \<turnstile> A"
  by (metis Bool MP boolean_axioms.Ident sup_commute)

lemma thin: "H \<turnstile> A \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> H' \<turnstile> A"
  by (metis Un_absorb1 thin_Un)

lemma thin0: "{} \<turnstile> A \<Longrightarrow> H \<turnstile> A"
  by (metis sup_bot_left thin_Un)

lemma thin1: "H \<turnstile> B \<Longrightarrow> insert A H \<turnstile> B"
  by (metis subset_insertI thin)

lemma thin2: "insert A1 H \<turnstile> B \<Longrightarrow> insert A1 (insert A2 H) \<turnstile> B"
  by (blast intro: thin)

lemma thin3: "insert A1 (insert A2 H) \<turnstile> B \<Longrightarrow> insert A1 (insert A2 (insert A3 H)) \<turnstile> B"
  by (blast intro: thin)

lemma thin4:
  "insert A1 (insert A2 (insert A3 H)) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 H))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate2: "insert A2 (insert A1 H) \<turnstile> B \<Longrightarrow> insert A1 (insert A2 H) \<turnstile> B"
  by (blast intro: thin)

lemma rotate3: "insert A3 (insert A1 (insert A2 H)) \<turnstile> B \<Longrightarrow> insert A1 (insert A2 (insert A3 H)) \<turnstile> B"
  by (blast intro: thin)

lemma rotate4:
  "insert A4 (insert A1 (insert A2 (insert A3 H))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 H))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate5:
  "insert A5 (insert A1 (insert A2 (insert A3 (insert A4 H)))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 H)))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate6:
  "insert A6 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 H))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 H))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate7:
  "insert A7 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 H)))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 H)))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate8:
  "insert A8 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 H))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 H))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate9:
  "insert A9 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 H)))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 H)))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate10:
  "insert A10 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 H))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 H))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate11:
  "insert A11 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 H)))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 H)))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate12:
  "insert A12 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 H))))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 H))))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate13:
  "insert A13 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 H)))))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 H)))))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate14:
  "insert A14 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 H))))))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 (insert A14 H))))))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate15:
  "insert A15 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 (insert A14 H)))))))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 (insert A14 (insert A15 H)))))))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma MP_same: "H \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis MP Un_absorb)

lemma MP_thin: "HA \<turnstile> A IMP B \<Longrightarrow> HB \<turnstile> A \<Longrightarrow> HA \<union> HB \<subseteq> H \<Longrightarrow> H \<turnstile> B"
  by (metis MP_same le_sup_iff thin)

lemma MP_null: "{} \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis MP_same thin0)

lemma Disj_commute: "H \<turnstile> B OR A \<Longrightarrow> H \<turnstile> A OR B"
  using DisjConj [of B A B] Ident [of B]
by (metis Bool MP_same)

lemma S: assumes  "H \<turnstile> A IMP (B IMP C)" "H' \<turnstile> A IMP B" shows "H \<union> H' \<turnstile> A IMP C"
proof -
  have "H' \<union> H \<turnstile> (Neg A) OR (C OR (Neg A))"
    by (metis Bool MP MP_same boolean_axioms.DisjConj Disj_commute DisjAssoc assms)
  thus ?thesis
    by (metis Bool Disj_commute Un_commute MP_same DisjAssoc DisjCont DisjI1)
qed

lemma Assume: "insert A H \<turnstile> A"
  by (metis Hyp insertI1)

lemmas AssumeH = Assume Assume [THEN rotate2] Assume [THEN rotate3] Assume [THEN rotate4] Assume [THEN rotate5]
                 Assume [THEN rotate6] Assume [THEN rotate7] Assume [THEN rotate8] Assume [THEN rotate9] Assume [THEN rotate10]
                 Assume [THEN rotate11] Assume [THEN rotate12]
declare AssumeH [intro!]

lemma Imp_triv_I: "H \<turnstile> B \<Longrightarrow> H \<turnstile> A IMP B"
  by (metis Bool Disj_commute MP_same boolean_axioms.DisjI1)

lemma DisjAssoc1: "H \<turnstile> A OR (B OR C) \<Longrightarrow> H \<turnstile> (A OR B) OR C"
  by (metis Bool MP_same boolean_axioms.DisjAssoc)

lemma DisjAssoc2: "H \<turnstile> (A OR B) OR C \<Longrightarrow> H \<turnstile> A OR (B OR C)"
  by (metis DisjAssoc1 Disj_commute)

lemma Disj_commute_Imp: "H \<turnstile> (B OR A) IMP (A OR B)"
  using DisjConj [of B A B] Ident [of B]
  by (metis Bool DisjAssoc2 Disj_commute MP_same)

lemma Disj_Semicong_1: "H \<turnstile> A OR C \<Longrightarrow> H \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> B OR C"
  using DisjConj [of A C B]
  by (metis Bool Disj_commute MP_same)

lemma Imp_Imp_commute: "H \<turnstile> B IMP (A IMP C) \<Longrightarrow> H \<turnstile> A IMP (B IMP C)"
  by (metis DisjAssoc1 DisjAssoc2 Disj_Semicong_1 Disj_commute_Imp)


subsection\<open>The Deduction Theorem\<close>

lemma deduction_Diff: assumes "H \<turnstile> B" shows "H - {C} \<turnstile> C IMP B"
using assms
proof (induct)
  case (Hyp A H) thus ?case
    by (metis Bool Imp_triv_I boolean_axioms.Ident hfthm.Hyp member_remove remove_def)
next
  case (Extra H) thus ?case
    by (metis Imp_triv_I hfthm.Extra)
next
  case (Bool A H) thus ?case
    by (metis Imp_triv_I hfthm.Bool)
next
  case (Eq A H) thus ?case
    by (metis Imp_triv_I hfthm.Eq)
next
  case (Spec A H) thus ?case
    by (metis Imp_triv_I hfthm.Spec)
next
  case (HF A H) thus ?case
    by (metis Imp_triv_I hfthm.HF)
next
  case (Ind A H) thus ?case
    by (metis Imp_triv_I hfthm.Ind)
next
  case (MP H A B H')
  hence "(H-{C}) \<union> (H'-{C}) \<turnstile> Imp C B"
    by (simp add: S)
  thus ?case
    by (metis Un_Diff)
next
  case (Exists H A B i) show ?case
  proof (cases "C \<in> H")
    case True
    hence "atom i \<sharp> C" using Exists by auto
    moreover have "H - {C} \<turnstile> A IMP C IMP B" using Exists
      by (metis Imp_Imp_commute)
    ultimately have "H - {C} \<turnstile> (Ex i A) IMP C IMP B" using Exists
      by (metis fm.fresh(3) fm.fresh(4) hfthm.Exists member_remove remove_def)
    thus ?thesis
      by (metis Imp_Imp_commute)
  next
    case False
    hence "H - {C} = H" by auto
    thus ?thesis using Exists
      by (metis Imp_triv_I hfthm.Exists)
  qed
qed

theorem Imp_I [intro!]: "insert A H \<turnstile> B \<Longrightarrow> H \<turnstile> A IMP B"
  by (metis Diff_insert_absorb Imp_triv_I deduction_Diff insert_absorb)

lemma anti_deduction: "H \<turnstile> A IMP B \<Longrightarrow> insert A H \<turnstile> B"
   by (metis Assume MP_same thin1)

subsection\<open>Cut rules\<close>

lemma cut:  "H \<turnstile> A \<Longrightarrow> insert A H' \<turnstile> B \<Longrightarrow> H \<union> H' \<turnstile> B"
  by (metis MP Un_commute Imp_I)

lemma cut_same: "H \<turnstile> A \<Longrightarrow> insert A H \<turnstile> B \<Longrightarrow> H \<turnstile> B"
  by (metis Un_absorb cut)

lemma cut_thin: "HA \<turnstile> A \<Longrightarrow> insert A HB \<turnstile> B \<Longrightarrow> HA \<union> HB \<subseteq> H \<Longrightarrow> H \<turnstile> B"
  by (metis thin cut)

lemma cut0: "{} \<turnstile> A \<Longrightarrow> insert A H \<turnstile> B \<Longrightarrow> H \<turnstile> B"
  by (metis cut_same thin0)

lemma cut1: "{A} \<turnstile> B \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis cut sup_bot_right)

lemma rcut1: "{A} \<turnstile> B \<Longrightarrow> insert B H \<turnstile> C \<Longrightarrow> insert A H \<turnstile> C"
  by (metis Assume cut1 cut_same rotate2 thin1)

lemma cut2: "\<lbrakk>{A,B} \<turnstile> C; H \<turnstile> A; H \<turnstile> B\<rbrakk> \<Longrightarrow> H \<turnstile> C"
  by (metis Un_empty_right Un_insert_right cut cut_same)

lemma rcut2: "{A,B} \<turnstile> C \<Longrightarrow> insert C H \<turnstile> D \<Longrightarrow> H \<turnstile> B \<Longrightarrow> insert A H \<turnstile> D"
  by (metis Assume cut2 cut_same insert_commute thin1)

lemma cut3: "\<lbrakk>{A,B,C} \<turnstile> D; H \<turnstile> A; H \<turnstile> B; H \<turnstile> C\<rbrakk> \<Longrightarrow> H \<turnstile> D"
  by (metis MP_same cut2 Imp_I)

lemma cut4: "\<lbrakk>{A,B,C,D} \<turnstile> E; H \<turnstile> A; H \<turnstile> B; H \<turnstile> C; H \<turnstile> D\<rbrakk> \<Longrightarrow> H \<turnstile> E"
  by (metis MP_same cut3 [of B C D] Imp_I)


section\<open>Miscellaneous logical rules\<close>

lemma Disj_I1: "H \<turnstile> A \<Longrightarrow> H \<turnstile> A OR B"
  by (metis Bool MP_same boolean_axioms.DisjI1)

lemma Disj_I2: "H \<turnstile> B \<Longrightarrow> H \<turnstile> A OR B"
  by (metis Disj_commute Disj_I1)

lemma Peirce: "H \<turnstile> (Neg A) IMP A \<Longrightarrow> H \<turnstile> A"
  using DisjConj [of "Neg A" A A]  DisjCont [of A]
  by (metis Bool MP_same boolean_axioms.Ident)

lemma Contra: "insert (Neg A) H \<turnstile> A \<Longrightarrow> H \<turnstile> A"
  by (metis Peirce Imp_I)

lemma Imp_Neg_I: "H \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> A IMP (Neg B) \<Longrightarrow> H \<turnstile> Neg A"
  by (metis DisjConj [of B "Neg A" "Neg A"] DisjCont Bool Disj_commute MP_same)

lemma NegNeg_I: "H \<turnstile> A \<Longrightarrow> H \<turnstile> Neg (Neg A)"
  using DisjConj [of "Neg (Neg A)" "Neg A" "Neg (Neg A)"]
  by (metis Bool Ident MP_same)

lemma NegNeg_D: "H \<turnstile> Neg (Neg A) \<Longrightarrow> H \<turnstile> A"
  by (metis Disj_I1 Peirce)

lemma Neg_D: "H \<turnstile> Neg A \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis Imp_Neg_I Imp_triv_I NegNeg_D)

lemma Disj_Neg_1: "H \<turnstile> A OR B \<Longrightarrow> H \<turnstile> Neg B \<Longrightarrow> H \<turnstile> A"
  by (metis Disj_I1 Disj_Semicong_1 Disj_commute Peirce)

lemma Disj_Neg_2: "H \<turnstile> A OR B \<Longrightarrow> H \<turnstile> Neg A \<Longrightarrow> H \<turnstile> B"
  by (metis Disj_Neg_1 Disj_commute)

lemma Neg_Disj_I: "H \<turnstile> Neg A \<Longrightarrow> H \<turnstile> Neg B \<Longrightarrow> H \<turnstile> Neg (A OR B)"
by (metis Bool Disj_Neg_1 MP_same boolean_axioms.Ident DisjAssoc)

lemma Conj_I [intro!]: "H \<turnstile> A \<Longrightarrow> H \<turnstile> B \<Longrightarrow> H \<turnstile> A AND B"
  by (metis Conj_def NegNeg_I Neg_Disj_I)

lemma Conj_E1: "H \<turnstile> A AND B \<Longrightarrow> H \<turnstile> A"
  by (metis Conj_def Bool Disj_Neg_1 NegNeg_D boolean_axioms.DisjI1)

lemma Conj_E2: "H \<turnstile> A AND B \<Longrightarrow> H \<turnstile> B"
  by (metis Conj_def Bool Disj_I2 Disj_Neg_2 MP_same DisjAssoc Ident)

lemma Conj_commute: "H \<turnstile> B AND A \<Longrightarrow> H \<turnstile> A AND B"
  by (metis Conj_E1 Conj_E2 Conj_I)

lemma Conj_E: assumes "insert A (insert B H) \<turnstile> C" shows "insert (A AND B) H \<turnstile> C"
apply (rule cut_same [where A=A], metis Conj_E1 Hyp insertI1)
by (metis (full_types) AssumeH(2) Conj_E2 assms cut_same [where A=B] insert_commute thin2)

lemmas Conj_EH = Conj_E Conj_E [THEN rotate2] Conj_E [THEN rotate3] Conj_E [THEN rotate4] Conj_E [THEN rotate5]
                 Conj_E [THEN rotate6] Conj_E [THEN rotate7] Conj_E [THEN rotate8] Conj_E [THEN rotate9] Conj_E [THEN rotate10]
declare Conj_EH [intro!]

lemma Neg_I0: assumes "(\<And>B. atom i \<sharp> B \<Longrightarrow> insert A H \<turnstile> B)" shows "H \<turnstile> Neg A"
  by (rule Imp_Neg_I [where B = "Zero IN Zero"]) (auto simp: assms)

lemma Neg_mono: "insert A H \<turnstile> B \<Longrightarrow> insert (Neg B) H \<turnstile> Neg A"
  by (rule Neg_I0) (metis Hyp Neg_D insert_commute insertI1 thin1)

lemma Conj_mono: "insert A H \<turnstile> B \<Longrightarrow> insert C H \<turnstile> D \<Longrightarrow> insert (A AND C) H \<turnstile> B AND D"
  by (metis Conj_E1 Conj_E2 Conj_I Hyp Un_absorb2 cut insertI1 subset_insertI)

lemma Disj_mono:
  assumes "insert A H \<turnstile> B" "insert C H \<turnstile> D" shows "insert (A OR C) H \<turnstile> B OR D"
proof -
  { fix A B C H
    have "insert (A OR C) H \<turnstile> (A IMP B) IMP C OR B"
      by (metis Bool Hyp MP_same boolean_axioms.DisjConj insertI1)
    hence "insert A H \<turnstile> B \<Longrightarrow> insert (A OR C) H \<turnstile> C OR B"
      by (metis MP_same Un_absorb Un_insert_right Imp_I thin_Un)
  }
  thus ?thesis
    by (metis cut_same assms thin2)
qed

lemma Disj_E:
  assumes A: "insert A H \<turnstile> C" and B: "insert B H \<turnstile> C" shows "insert (A OR B) H \<turnstile> C"
  by (metis A B Disj_mono NegNeg_I Peirce)

lemmas Disj_EH = Disj_E Disj_E [THEN rotate2] Disj_E [THEN rotate3] Disj_E [THEN rotate4] Disj_E [THEN rotate5]
                 Disj_E [THEN rotate6] Disj_E [THEN rotate7] Disj_E [THEN rotate8] Disj_E [THEN rotate9] Disj_E [THEN rotate10]
declare Disj_EH [intro!]

lemma Contra': "insert A H \<turnstile> Neg A \<Longrightarrow> H \<turnstile> Neg A"
  by (metis Contra Neg_mono)

lemma NegNeg_E [intro!]: "insert A H \<turnstile> B \<Longrightarrow> insert (Neg (Neg A)) H \<turnstile> B"
  by (metis NegNeg_D Neg_mono)

declare NegNeg_E [THEN rotate2, intro!]
declare NegNeg_E [THEN rotate3, intro!]
declare NegNeg_E [THEN rotate4, intro!]
declare NegNeg_E [THEN rotate5, intro!]
declare NegNeg_E [THEN rotate6, intro!]
declare NegNeg_E [THEN rotate7, intro!]
declare NegNeg_E [THEN rotate8, intro!]

lemma Imp_E:
  assumes A: "H \<turnstile> A" and B: "insert B H \<turnstile> C" shows "insert (A IMP B) H \<turnstile> C"
proof -
  have "insert (A IMP B) H \<turnstile> B"
    by (metis Hyp A thin1 MP_same insertI1)
  thus ?thesis
    by (metis cut [where B=C] Un_insert_right sup_commute sup_idem B)
qed

lemma Imp_cut:
  assumes "insert C H \<turnstile> A IMP B" "{A} \<turnstile> C"
    shows "H \<turnstile> A IMP B"
  by (metis Contra Disj_I1 Neg_mono assms rcut1)

lemma Iff_I [intro!]: "insert A H \<turnstile> B \<Longrightarrow> insert B H \<turnstile> A \<Longrightarrow> H \<turnstile> A IFF B"
  by (metis Iff_def Conj_I Imp_I)

lemma Iff_MP_same: "H \<turnstile> A IFF B \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis Iff_def Conj_E1 MP_same)

lemma Iff_MP2_same: "H \<turnstile> A IFF B \<Longrightarrow> H \<turnstile> B \<Longrightarrow> H \<turnstile> A"
  by (metis Iff_def Conj_E2 MP_same)

lemma Iff_refl [intro!]: "H \<turnstile> A IFF A"
  by (metis Hyp Iff_I insertI1)

lemma Iff_sym: "H \<turnstile> A IFF B \<Longrightarrow> H \<turnstile> B IFF A"
  by (metis Iff_def Conj_commute)

lemma Iff_trans: "H \<turnstile> A IFF B \<Longrightarrow> H \<turnstile> B IFF C \<Longrightarrow> H \<turnstile> A IFF C"
  unfolding Iff_def
  by (metis Conj_E1 Conj_E2 Conj_I Disj_Semicong_1 Disj_commute)

lemma Iff_E:
  "insert A (insert B H) \<turnstile> C \<Longrightarrow> insert (Neg A) (insert (Neg B) H) \<turnstile> C \<Longrightarrow> insert (A IFF B) H \<turnstile> C"
  apply (auto simp: Iff_def insert_commute)
  apply (metis Disj_I1 Hyp anti_deduction insertCI)
  apply (metis Assume Disj_I1 anti_deduction)
  done

lemma Iff_E1:
  assumes A: "H \<turnstile> A" and B: "insert B H \<turnstile> C" shows "insert (A IFF B) H \<turnstile> C"
  by (metis Iff_def A B Conj_E Imp_E insert_commute thin1)

lemma Iff_E2:
  assumes A: "H \<turnstile> A" and B: "insert B H \<turnstile> C" shows "insert (B IFF A) H \<turnstile> C"
  by (metis Iff_def A B Bool Conj_E2 Conj_mono Imp_E boolean_axioms.Ident)

lemma Iff_MP_left: "H \<turnstile> A IFF B \<Longrightarrow> insert A H \<turnstile> C \<Longrightarrow> insert B H \<turnstile> C"
  by (metis Hyp Iff_E2 cut_same insertI1 insert_commute thin1)

lemma Iff_MP_left': "H \<turnstile> A IFF B \<Longrightarrow> insert B H \<turnstile> C \<Longrightarrow> insert A H \<turnstile> C"
  by (metis Iff_MP_left Iff_sym)

lemma Swap: "insert (Neg B) H \<turnstile> A \<Longrightarrow> insert (Neg A) H \<turnstile> B"
  by (metis NegNeg_D Neg_mono)

lemma Cases: "insert A H \<turnstile> B \<Longrightarrow> insert (Neg A) H \<turnstile> B \<Longrightarrow> H \<turnstile> B"
  by (metis Contra Neg_D Neg_mono)

lemma Neg_Conj_E: "H \<turnstile> B \<Longrightarrow> insert (Neg A) H \<turnstile> C \<Longrightarrow> insert (Neg (A AND B)) H \<turnstile> C"
  by (metis Conj_I Swap thin1)

lemma Disj_CI: "insert (Neg B) H \<turnstile> A \<Longrightarrow> H \<turnstile> A OR B"
  by (metis Contra Disj_I1 Disj_I2 Swap)

lemma Disj_3I: "insert (Neg A) (insert (Neg C) H) \<turnstile> B \<Longrightarrow> H \<turnstile> A OR B OR C"
  by (metis Disj_CI Disj_commute insert_commute)

lemma Contrapos1: "H \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> Neg B IMP Neg A"
  by (metis Bool MP_same boolean_axioms.DisjConj boolean_axioms.Ident)

lemma Contrapos2: "H \<turnstile> (Neg B) IMP (Neg A) \<Longrightarrow> H \<turnstile> A IMP B"
  by (metis Bool MP_same boolean_axioms.DisjConj boolean_axioms.Ident)

lemma ContraAssumeN [intro]: "B \<in> H \<Longrightarrow> insert (Neg B) H \<turnstile> A"
  by (metis Hyp Swap thin1)

lemma ContraAssume: "Neg B \<in> H \<Longrightarrow> insert B H \<turnstile> A"
  by (metis Disj_I1 Hyp anti_deduction)

lemma ContraProve: "H \<turnstile> B \<Longrightarrow> insert (Neg B) H \<turnstile> A"
  by (metis Swap thin1)

lemma Disj_IE1: "insert B H \<turnstile> C \<Longrightarrow> insert (A OR B) H \<turnstile> A OR C"
  by (metis Assume Disj_mono)

lemmas Disj_IE1H = Disj_IE1 Disj_IE1 [THEN rotate2] Disj_IE1 [THEN rotate3] Disj_IE1 [THEN rotate4] Disj_IE1 [THEN rotate5]
                 Disj_IE1 [THEN rotate6] Disj_IE1 [THEN rotate7] Disj_IE1 [THEN rotate8]
declare Disj_IE1H [intro!]

subsection\<open>Quantifier reasoning\<close>

lemma Ex_I: "H \<turnstile> A(i::=x) \<Longrightarrow> H \<turnstile> Ex i A"
  by (metis MP_same Spec special_axioms.intros)

lemma Ex_E:
  assumes "insert A H \<turnstile> B" "atom i \<sharp> B" "\<forall>C \<in> H. atom i \<sharp> C"
  shows "insert (Ex i A) H \<turnstile> B"
  by (metis Exists Imp_I anti_deduction assms)

lemma Ex_E_with_renaming:
  assumes "insert ((i \<leftrightarrow> i') \<bullet> A) H \<turnstile> B" "atom i' \<sharp> (A,i,B)" "\<forall>C \<in> H. atom i' \<sharp> C"
  shows "insert (Ex i A) H \<turnstile> B"
proof -
  have "Ex i A = Ex i' ((i \<leftrightarrow> i') \<bullet> A)" using assms
    apply (auto simp: Abs1_eq_iff fresh_Pair)
    apply (metis flip_at_simps(2) fresh_at_base_permute_iff)+
    done
  thus ?thesis
    by (metis Ex_E assms fresh_Pair)
qed

lemmas Ex_EH = Ex_E Ex_E [THEN rotate2] Ex_E [THEN rotate3] Ex_E [THEN rotate4] Ex_E [THEN rotate5]
                 Ex_E [THEN rotate6] Ex_E [THEN rotate7] Ex_E [THEN rotate8] Ex_E [THEN rotate9] Ex_E [THEN rotate10]
declare Ex_EH [intro!]

lemma Ex_mono: "insert A H \<turnstile> B \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> insert (Ex i A) H \<turnstile> (Ex i B)"
  by (auto simp add: intro: Ex_I [where x="Var i"])

lemma All_I [intro!]: "H \<turnstile> A \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> All i A"
  by (auto intro: ContraProve Neg_I0)

lemma All_D: "H \<turnstile> All i A \<Longrightarrow> H \<turnstile> A(i::=x)"
  by (metis Assume Ex_I NegNeg_D Neg_mono SyntaxN.Neg cut_same)

lemma All_E: "insert (A(i::=x)) H \<turnstile> B \<Longrightarrow> insert (All i A) H \<turnstile> B"
  by (metis Ex_I NegNeg_D Neg_mono SyntaxN.Neg)

lemma All_E': "H \<turnstile> All i A \<Longrightarrow> insert (A(i::=x)) H \<turnstile> B \<Longrightarrow> H \<turnstile> B"
  by (metis All_D cut_same)

lemma All2_E: "\<lbrakk>atom i \<sharp> t; H \<turnstile> x IN t; insert (A(i::=x)) H \<turnstile> B\<rbrakk> \<Longrightarrow> insert (All2 i t A) H \<turnstile> B"
  apply (rule All_E [where x=x], auto)
  by (metis Swap thin1)

lemma All2_E': "\<lbrakk>H \<turnstile> All2 i t A; H \<turnstile> x IN t; insert (A(i::=x)) H \<turnstile> B; atom i \<sharp> t\<rbrakk> \<Longrightarrow> H \<turnstile> B"
  by (metis All2_E cut_same)


subsection\<open>Congruence rules\<close>

lemma Neg_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> Neg A IFF Neg A'"
  by (metis Iff_def Conj_E1 Conj_E2 Conj_I Contrapos1)

lemma Disj_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> B IFF B' \<Longrightarrow> H \<turnstile> A OR B IFF A' OR B'"
  by (metis Conj_E1 Conj_E2 Disj_mono Iff_I Iff_def anti_deduction)

lemma Conj_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> B IFF B' \<Longrightarrow> H \<turnstile> A AND B IFF A' AND B'"
  by (metis Conj_def Disj_cong Neg_cong)

lemma Imp_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> B IFF B' \<Longrightarrow> H \<turnstile> (A IMP B) IFF (A' IMP B')"
  by (metis Disj_cong Neg_cong)

lemma Iff_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> B IFF B' \<Longrightarrow> H \<turnstile> (A IFF B) IFF (A' IFF B')"
  by (metis Iff_def Conj_cong Imp_cong)

lemma Ex_cong: "H \<turnstile> A IFF A' \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> (Ex i A) IFF (Ex i A')"
  apply (rule Iff_I)
   apply (metis Ex_mono Hyp Iff_MP_same Un_absorb Un_insert_right insertI1 thin_Un)
  apply (metis Ex_mono Hyp Iff_MP2_same Un_absorb Un_insert_right insertI1 thin_Un)
  done

lemma All_cong: "H \<turnstile> A IFF A' \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> (All i A) IFF (All i A')"
  by (metis Ex_cong Neg_cong)

lemma Subst: "H \<turnstile> A \<Longrightarrow> \<forall>B \<in> H. atom i \<sharp> B \<Longrightarrow> H \<turnstile> A (i::=x)"
  by (metis All_D All_I)


section\<open>Equality reasoning\<close>

subsection\<open>The congruence property for @{term Eq}, and other basic properties of equality\<close>

lemma Eq_cong1: "{} \<turnstile> (t EQ t' AND u EQ u') IMP (t EQ u IMP t' EQ u')"
proof -
  obtain v2::name and v3::name and v4::name
    where v2: "atom v2 \<sharp> (t,X1,X3,X4)"
      and v3: "atom v3 \<sharp> (t,t',X1,v2,X4)"
      and v4: "atom v4 \<sharp> (t,t',u,X1,v2,v3)"
    by (metis obtain_fresh)
  have "{} \<turnstile> (Var X1 EQ Var X2 AND Var X3 EQ Var X4) IMP (Var X1 EQ Var X3 IMP Var X2 EQ Var X4)"
    by (rule Eq) (simp add: eq_cong_ax_def equality_axioms_def)
  hence "{} \<turnstile> (Var X1 EQ Var X2 AND Var X3 EQ Var X4) IMP (Var X1 EQ Var X3 IMP Var X2 EQ Var X4)"
    by (drule_tac i=X1 and x="Var X1" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var X3 EQ Var X4) IMP (Var X1 EQ Var X3 IMP Var v2 EQ Var X4)"
    by (drule_tac i=X2 and x="Var v2" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var X4) IMP (Var X1 EQ Var v3 IMP Var v2 EQ Var X4)"
    using v2
    by (drule_tac i=X3 and x="Var v3" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var v4) IMP (Var X1 EQ Var v3 IMP Var v2 EQ Var v4)"
    using v2 v3
    by (drule_tac i=X4 and x="Var v4" in Subst) simp_all
  hence "{} \<turnstile> (t EQ Var v2 AND Var v3 EQ Var v4) IMP (t EQ Var v3 IMP Var v2 EQ Var v4)"
    using v2 v3 v4
    by (drule_tac i=X1 and x=t in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND Var v3 EQ Var v4) IMP (t EQ Var v3 IMP t' EQ Var v4)"
    using v2 v3 v4
    by (drule_tac i=v2 and x="t'" in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND u EQ Var v4) IMP (t EQ u IMP t' EQ Var v4)"
    using v3 v4
    by (drule_tac i=v3 and x=u in Subst) simp_all
  thus ?thesis
    using v4
    by (drule_tac i=v4 and x="u'" in Subst) simp_all
qed

lemma Refl [iff]: "H \<turnstile> t EQ t"
proof -
  have "{} \<turnstile> Var X1 EQ Var X1"
    by (rule Eq) (simp add: equality_axioms_def refl_ax_def)
  hence "{} \<turnstile> t EQ t"
    by (drule_tac i=X1 and x=t in Subst) simp_all
  thus ?thesis
    by (metis empty_subsetI thin)
qed

text\<open>Apparently necessary in order to prove the congruence property.\<close>
lemma Sym: assumes "H \<turnstile> t EQ u" shows "H \<turnstile> u EQ t"
proof -
  have "{} \<turnstile>  (t EQ u AND t EQ t) IMP (t EQ t IMP u EQ t)"
    by (rule Eq_cong1)
   moreover have "{t EQ u} \<turnstile> t EQ u AND t EQ t"
    by (metis Assume Conj_I Refl)
  ultimately have "{t EQ u} \<turnstile> u EQ t"
    by (metis MP_same MP Refl sup_bot_left)
  thus "H \<turnstile> u EQ t" by (metis assms cut1)
qed

lemma Sym_L: "insert (t EQ u) H \<turnstile> A \<Longrightarrow> insert (u EQ t) H \<turnstile> A"
  by (metis Assume Sym Un_empty_left Un_insert_left cut)

lemma Trans: assumes "H \<turnstile> x EQ y" "H \<turnstile> y EQ z" shows "H \<turnstile> x EQ z"
proof -
  have "\<And>H. H \<turnstile> (x EQ x AND y EQ z) IMP (x EQ y IMP x EQ z)"
    by (metis Eq_cong1 bot_least thin)
  moreover have "{x EQ y, y EQ z} \<turnstile> x EQ x AND y EQ z"
    by (metis Assume Conj_I Refl thin1)
  ultimately have "{x EQ y, y EQ z} \<turnstile> x EQ z"
    by (metis Hyp MP_same insertI1)
  thus ?thesis
    by (metis assms cut2)
qed

lemma Eq_cong:
  assumes "H \<turnstile> t EQ t'" "H \<turnstile> u EQ u'" shows "H \<turnstile> t EQ u IFF t' EQ u'"
proof -
  { fix t t' u u'
    assume  "H \<turnstile> t EQ t'" "H \<turnstile> u EQ u'"
    moreover have "{t EQ t', u EQ u'} \<turnstile> t EQ u IMP t' EQ u'" using Eq_cong1
      by (metis Assume Conj_I MP_null insert_commute)
    ultimately have "H \<turnstile> t EQ u IMP t' EQ u'"
      by (metis cut2)
  }
  thus ?thesis
    by (metis Iff_def Conj_I assms Sym)
qed

lemma Eq_Trans_E: "H \<turnstile> x EQ u \<Longrightarrow> insert (t EQ u) H \<turnstile> A \<Longrightarrow> insert (x EQ t) H \<turnstile> A"
  by (metis Assume Sym_L Trans cut_same thin1 thin2)

subsection\<open>The congruence property for @{term Mem}\<close>

lemma Mem_cong1: "{} \<turnstile> (t EQ t' AND u EQ u') IMP (t IN u IMP t' IN u')"
proof -
  obtain v2::name and v3::name and v4::name
    where v2: "atom v2 \<sharp> (t,X1,X3,X4)"
      and v3: "atom v3 \<sharp> (t,t',X1,v2,X4)"
      and v4: "atom v4 \<sharp> (t,t',u,X1,v2,v3)"
    by (metis obtain_fresh)
  have "{} \<turnstile> (Var X1 EQ Var X2 AND Var X3 EQ Var X4) IMP (Var X1 IN Var X3 IMP Var X2 IN Var X4)"
    by (metis mem_cong_ax_def equality_axioms_def insert_iff Eq)
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var X3 EQ Var X4) IMP (Var X1 IN Var X3 IMP Var v2 IN Var X4)"
    by (drule_tac i=X2 and x="Var v2" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var X4) IMP (Var X1 IN Var v3 IMP Var v2 IN Var X4)"
    using v2
    by (drule_tac i=X3 and x="Var v3" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var v4) IMP (Var X1 IN Var v3 IMP Var v2 IN Var v4)"
    using v2 v3
    by (drule_tac i=X4 and x="Var v4" in Subst) simp_all
  hence "{} \<turnstile> (t EQ Var v2 AND Var v3 EQ Var v4) IMP (t IN Var v3 IMP Var v2 IN Var v4)"
    using v2 v3 v4
    by (drule_tac i=X1 and x=t in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND Var v3 EQ Var v4) IMP (t IN Var v3 IMP t' IN Var v4)"
    using v2 v3 v4
    by (drule_tac i=v2 and x=t' in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND u EQ Var v4) IMP (t IN u IMP t' IN Var v4)"
    using v3 v4
    by (drule_tac i=v3 and x=u in Subst) simp_all
  thus ?thesis
    using v4
    by (drule_tac i=v4 and x=u' in Subst) simp_all
qed

lemma Mem_cong:
  assumes "H \<turnstile> t EQ t'" "H \<turnstile> u EQ u'" shows "H \<turnstile> t IN u IFF t' IN u'"
proof -
  { fix t t' u u'
    have cong: "{t EQ t', u EQ u'} \<turnstile> t IN u IMP t' IN u'"
      by (metis AssumeH(2) Conj_I MP_null Mem_cong1 insert_commute)
  }
  thus ?thesis
    by (metis Iff_def Conj_I cut2 assms Sym)
qed

subsection\<open>The congruence properties for @{term Eats} and @{term HPair}\<close>

lemma Eats_cong1: "{} \<turnstile> (t EQ t' AND u EQ u') IMP (Eats t u EQ Eats t' u')"
proof -
  obtain v2::name and v3::name and v4::name
    where v2: "atom v2 \<sharp> (t,X1,X3,X4)"
      and v3: "atom v3 \<sharp> (t,t',X1,v2,X4)"
      and v4: "atom v4 \<sharp> (t,t',u,X1,v2,v3)"
    by (metis obtain_fresh)
  have "{} \<turnstile> (Var X1 EQ Var X2 AND Var X3 EQ Var X4) IMP (Eats (Var X1) (Var X3) EQ Eats (Var X2) (Var X4))"
    by (metis eats_cong_ax_def equality_axioms_def insert_iff Eq)
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var X3 EQ Var X4) IMP (Eats (Var X1) (Var X3) EQ Eats (Var v2) (Var X4))"
    by (drule_tac i=X2 and x="Var v2" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var X4) IMP (Eats (Var X1) (Var v3) EQ Eats (Var v2) (Var X4))"
    using v2
    by (drule_tac i=X3 and x="Var v3" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var v4) IMP (Eats (Var X1) (Var v3) EQ Eats (Var v2) (Var v4))"
    using v2 v3
    by (drule_tac i=X4 and x="Var v4" in Subst) simp_all
  hence "{} \<turnstile> (t EQ Var v2 AND Var v3 EQ Var v4) IMP (Eats t (Var v3) EQ Eats (Var v2) (Var v4))"
    using v2 v3 v4
    by (drule_tac i=X1 and x=t in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND Var v3 EQ Var v4) IMP (Eats t (Var v3) EQ Eats t' (Var v4))"
    using v2 v3 v4
    by (drule_tac i=v2 and x=t' in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND u EQ Var v4) IMP (Eats t u EQ Eats t' (Var v4))"
    using v3 v4
    by (drule_tac i=v3 and x=u in Subst) simp_all
  thus ?thesis
    using v4
    by (drule_tac i=v4 and x=u' in Subst) simp_all
qed

lemma Eats_cong: "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'\<rbrakk> \<Longrightarrow> H \<turnstile> Eats t u EQ Eats t' u'"
  by (metis Conj_I anti_deduction Eats_cong1 cut1)

lemma HPair_cong: "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'\<rbrakk> \<Longrightarrow> H \<turnstile> HPair t u EQ HPair t' u'"
  by (metis HPair_def Eats_cong Refl)

lemma SUCC_cong: "H \<turnstile> t EQ t' \<Longrightarrow> H \<turnstile> SUCC t EQ SUCC t'"
  by (metis Eats_cong SUCC_def)

subsection\<open>Substitution for Equalities\<close>

lemma Eq_subst_tm_Iff: "{t EQ u} \<turnstile> subst i t tm EQ subst i u tm"
  by (induct tm rule: tm.induct) (auto simp: Eats_cong)

lemma Eq_subst_fm_Iff: "insert (t EQ u) H \<turnstile> A(i::=t) IFF A(i::=u)"
proof -
  have "{ t EQ u } \<turnstile> A(i::=t) IFF A(i::=u)"
    by (nominal_induct A avoiding: i t u rule: fm.strong_induct)
       (auto simp: Disj_cong Neg_cong Ex_cong Mem_cong Eq_cong Eq_subst_tm_Iff)
  thus ?thesis
    by (metis Assume cut1)
qed

lemma Var_Eq_subst_Iff: "insert (Var i EQ t) H \<turnstile> A(i::=t) IFF A"
  by (metis Eq_subst_fm_Iff Iff_sym subst_fm_id)

lemma Var_Eq_imp_subst_Iff: "H \<turnstile> Var i EQ t \<Longrightarrow> H \<turnstile> A(i::=t) IFF A"
  by (metis Var_Eq_subst_Iff cut_same)

subsection\<open>Congruence Rules for Predicates\<close>

lemma P1_cong:
  fixes tms :: "tm list"
  assumes "\<And>i t x. atom i \<sharp> tms \<Longrightarrow> (P t)(i::=x) = P (subst i x t)" and "H \<turnstile> x EQ x'"
  shows "H \<turnstile> P x IFF P x'"
proof -
  obtain i::name where i: "atom i \<sharp> tms"
    by (metis obtain_fresh)
  have "insert (x EQ x') H  \<turnstile> (P (Var i))(i::=x) IFF (P(Var i))(i::=x')"
    by (rule Eq_subst_fm_Iff)
  thus ?thesis using assms i
    by (metis cut_same subst.simps(2))
qed

lemma P2_cong:
  fixes tms :: "tm list"
  assumes sub: "\<And>i t u x. atom i \<sharp> tms \<Longrightarrow> (P t u)(i::=x) = P (subst i x t) (subst i x u)"
      and eq:  "H \<turnstile> x EQ x'" "H \<turnstile> y EQ y'"
  shows "H \<turnstile> P x y IFF P x' y'"
proof -
  have yy': "{ y EQ y' } \<turnstile> P x' y IFF P x' y'"
    by (rule P1_cong [where tms="[y,x']@tms"]) (auto simp: fresh_Cons sub)
  have "{ x EQ x' } \<turnstile> P x y IFF P x' y"
    by (rule P1_cong [where tms="[y,x']@tms"]) (auto simp: fresh_Cons sub)
  hence "{x EQ x', y EQ y'} \<turnstile> P x y IFF P x' y'"
    by (metis Assume Iff_trans cut1 rotate2 yy')
  thus ?thesis
    by (metis cut2 eq)
 qed

lemma P3_cong:
  fixes tms :: "tm list"
  assumes sub: "\<And>i t u v x. atom i \<sharp> tms \<Longrightarrow>
                   (P t u v)(i::=x) = P (subst i x t) (subst i x u) (subst i x v)"
      and eq:  "H \<turnstile> x EQ x'" "H \<turnstile> y EQ y'" "H \<turnstile> z EQ z'"
  shows "H \<turnstile> P x y z IFF P x' y' z'"
proof -
  obtain i::name where i: "atom i \<sharp> (z,z',y,y',x,x')"
    by (metis obtain_fresh)
  have tl: "{ y EQ y', z EQ z' } \<turnstile> P x' y z IFF P x' y' z'"
    by (rule P2_cong [where tms="[z,z',y,y',x,x']@tms"]) (auto simp: fresh_Cons sub)
  have hd: "{ x EQ x' } \<turnstile> P x y z IFF P x' y z"
    by (rule P1_cong [where tms="[z,y,x']@tms"]) (auto simp: fresh_Cons sub)
  have "{x EQ x', y EQ y', z EQ z'} \<turnstile> P x y z IFF P x' y' z'"
    by (metis Assume thin1 hd [THEN cut1] tl Iff_trans)
  thus ?thesis
    by (rule cut3) (rule eq)+
qed

lemma P4_cong:
  fixes tms :: "tm list"
  assumes sub: "\<And>i t1 t2 t3 t4 x. atom i \<sharp> tms \<Longrightarrow>
                 (P t1 t2 t3 t4)(i::=x) = P (subst i x t1) (subst i x t2) (subst i x t3) (subst i x t4)"
      and eq:  "H \<turnstile> x1 EQ x1'" "H \<turnstile> x2 EQ x2'" "H \<turnstile> x3 EQ x3'" "H \<turnstile> x4 EQ x4'"
  shows "H \<turnstile> P x1 x2 x3 x4 IFF P x1' x2' x3' x4'"
proof -
  obtain i::name where i: "atom i \<sharp> (x4,x4',x3,x3',x2,x2',x1,x1')"
    by (metis obtain_fresh)
  have tl: "{ x2 EQ x2', x3 EQ x3', x4 EQ x4' } \<turnstile> P x1' x2 x3 x4 IFF P x1' x2' x3' x4'"
    by (rule P3_cong [where tms="[x4,x4',x3,x3',x2,x2',x1,x1']@tms"]) (auto simp: fresh_Cons sub)
  have hd: "{ x1 EQ x1' } \<turnstile> P x1 x2 x3 x4 IFF P x1' x2 x3 x4"
    by (auto simp: fresh_Cons sub intro!: P1_cong [where tms="[x4,x3,x2,x1']@tms"])
  have "{x1 EQ x1', x2 EQ x2', x3 EQ x3', x4 EQ x4'} \<turnstile> P x1 x2 x3 x4 IFF P x1' x2' x3' x4'"
    by (metis Assume thin1 hd [THEN cut1] tl Iff_trans)
  thus ?thesis
    by (rule cut4) (rule eq)+
qed


section\<open>Zero and Falsity\<close>

lemma Mem_Zero_iff:
  assumes "atom i \<sharp> t" shows "H \<turnstile> (t EQ Zero) IFF (All i (Neg ((Var i) IN t)))"
proof -
  obtain i'::name where i': "atom i' \<sharp> (t, X0, X1, i)"
    by (rule obtain_fresh)
  have "{} \<turnstile> ((Var X0) EQ Zero) IFF (All X1 (Neg ((Var X1) IN (Var X0))))"
    by (simp add: HF HF_axioms_def HF1_def)
  then have "{} \<turnstile> (((Var X0) EQ Zero) IFF (All X1 (Neg ((Var X1) IN (Var X0)))))(X0 ::= t)"
     by (rule Subst) simp
  hence "{} \<turnstile> (t EQ Zero) IFF (All i' (Neg ((Var i') IN t)))" using i'
    by simp
  also have "... = (FRESH i'. (t EQ Zero) IFF (All i' (Neg ((Var i') IN t))))"
    using i' by simp
  also have "... = (t EQ Zero) IFF (All i (Neg ((Var i) IN t)))"
    using assms by simp
  finally show ?thesis
    by (metis empty_subsetI thin)
qed

lemma Mem_Zero_E [intro!]: "insert (x IN Zero) H \<turnstile> A"
proof -
  obtain i::name where "atom i \<sharp> Zero"
    by (rule obtain_fresh)
  hence "{} \<turnstile> All i (Neg ((Var i) IN Zero))"
    by (metis Mem_Zero_iff Iff_MP_same Refl)
  hence "{} \<turnstile> Neg (x IN Zero)"
    by (drule_tac x=x in All_D) simp
  thus ?thesis
    by (metis Contrapos2 Hyp Imp_triv_I MP_same empty_subsetI insertI1 thin)
qed

declare Mem_Zero_E [THEN rotate2, intro!]
declare Mem_Zero_E [THEN rotate3, intro!]
declare Mem_Zero_E [THEN rotate4, intro!]
declare Mem_Zero_E [THEN rotate5, intro!]
declare Mem_Zero_E [THEN rotate6, intro!]
declare Mem_Zero_E [THEN rotate7, intro!]
declare Mem_Zero_E [THEN rotate8, intro!]


subsection\<open>The Formula @{term Fls}\<close>

definition Fls  where "Fls \<equiv> Zero IN Zero"

lemma Fls_eqvt [eqvt]: "(p \<bullet> Fls) = Fls"
  by (simp add: Fls_def)

lemma Fls_fresh [simp]: "a \<sharp> Fls"
  by (simp add: Fls_def)

lemma Neg_I [intro!]: "insert A H \<turnstile> Fls \<Longrightarrow> H \<turnstile> Neg A"
  unfolding Fls_def
  by (rule Neg_I0) (metis Mem_Zero_E cut_same)

lemma Neg_E [intro!]: "H \<turnstile> A \<Longrightarrow> insert (Neg A) H \<turnstile> Fls"
  by (rule ContraProve)

declare Neg_E [THEN rotate2, intro!]
declare Neg_E [THEN rotate3, intro!]
declare Neg_E [THEN rotate4, intro!]
declare Neg_E [THEN rotate5, intro!]
declare Neg_E [THEN rotate6, intro!]
declare Neg_E [THEN rotate7, intro!]
declare Neg_E [THEN rotate8, intro!]

text\<open>We need these because Neg (A IMP B) doesn't have to be syntactically a conjunction.\<close>
lemma Neg_Imp_I [intro!]: "H \<turnstile> A \<Longrightarrow> insert B H \<turnstile> Fls \<Longrightarrow> H \<turnstile> Neg (A IMP B)"
  by (metis NegNeg_I Neg_Disj_I Neg_I)

lemma Neg_Imp_E [intro!]: "insert (Neg B) (insert A H) \<turnstile> C \<Longrightarrow> insert (Neg (A IMP B)) H \<turnstile> C"
apply (rule cut_same [where A=A])
 apply (metis Assume Disj_I1 NegNeg_D Neg_mono)
apply (metis Swap Imp_I rotate2 thin1)
done

declare Neg_Imp_E [THEN rotate2, intro!]
declare Neg_Imp_E [THEN rotate3, intro!]
declare Neg_Imp_E [THEN rotate4, intro!]
declare Neg_Imp_E [THEN rotate5, intro!]
declare Neg_Imp_E [THEN rotate6, intro!]
declare Neg_Imp_E [THEN rotate7, intro!]
declare Neg_Imp_E [THEN rotate8, intro!]

lemma Fls_E [intro!]: "insert Fls H \<turnstile> A"
  by (metis Mem_Zero_E Fls_def)

declare Fls_E [THEN rotate2, intro!]
declare Fls_E [THEN rotate3, intro!]
declare Fls_E [THEN rotate4, intro!]
declare Fls_E [THEN rotate5, intro!]
declare Fls_E [THEN rotate6, intro!]
declare Fls_E [THEN rotate7, intro!]
declare Fls_E [THEN rotate8, intro!]

lemma truth_provable: "H \<turnstile> (Neg Fls)"
  by (metis Fls_E Neg_I)

lemma ExFalso: "H \<turnstile> Fls \<Longrightarrow> H \<turnstile> A"
  by (metis Neg_D truth_provable)

subsection\<open>More properties of @{term Zero}\<close>

lemma Eq_Zero_D:
  assumes "H \<turnstile> t EQ Zero" "H \<turnstile> u IN t" shows "H \<turnstile> A"
proof -
  obtain i::name where  i: "atom i \<sharp> t"
    by (rule obtain_fresh)
  with assms have an: "H \<turnstile> (All i (Neg ((Var i) IN t)))"
    by (metis Iff_MP_same Mem_Zero_iff)
  have "H \<turnstile> Neg (u IN t)" using All_D [OF an, of u] i
    by simp
  thus ?thesis using assms
    by (metis Neg_D)
qed

lemma Eq_Zero_thm:
  assumes "atom i \<sharp> t" shows "{All i (Neg ((Var i) IN t))} \<turnstile> t EQ Zero"
by (metis Assume Iff_MP2_same Mem_Zero_iff assms)

lemma Eq_Zero_I:
  assumes insi: "insert ((Var i) IN t) H \<turnstile> Fls" and i1: "atom i \<sharp> t" and i2: "\<forall>B \<in> H. atom i \<sharp> B"
  shows "H \<turnstile> t EQ Zero"
proof -
  have "H \<turnstile> All i (Neg ((Var i) IN t))"
    by (metis All_I Neg_I i2 insi)
  thus ?thesis
    by (metis cut_same  cut [OF Eq_Zero_thm [OF i1] Hyp] insertCI insert_is_Un)
qed

subsection\<open>Basic properties of @{term Eats}\<close>

lemma Eq_Eats_iff:
  assumes "atom i \<sharp> (z,t,u)"
  shows "H \<turnstile> (z EQ Eats t u) IFF (All i (Var i IN z IFF Var i IN t OR Var i EQ u))"
proof -
  obtain v1::name and v2::name and i'::name
    where v1: "atom v1 \<sharp> (z,X0,X2,X3)"
      and v2: "atom v2 \<sharp> (t,z,X0,v1,X3)"
      and i': "atom i' \<sharp> (t,u,z,X0,v1,v2,X3)"
    by (metis obtain_fresh)
  have "{} \<turnstile> ((Var X0) EQ (Eats (Var X1) (Var X2))) IFF
             (All X3 (Var X3 IN Var X0 IFF Var X3 IN Var X1 OR Var X3 EQ Var X2))"
    by (simp add: HF HF_axioms_def HF2_def)
  hence "{} \<turnstile> ((Var X0) EQ (Eats (Var X1) (Var X2))) IFF
              (All X3 (Var X3 IN Var X0 IFF Var X3 IN Var X1 OR Var X3 EQ Var X2))"
    by (drule_tac i=X0 and x="Var X0" in Subst) simp_all
  hence "{} \<turnstile> ((Var X0) EQ (Eats (Var v1) (Var X2))) IFF
                 (All X3 (Var X3 IN Var X0 IFF Var X3 IN Var v1 OR Var X3 EQ Var X2))"
    using v1 by (drule_tac i=X1 and x="Var v1" in Subst) simp_all
  hence "{} \<turnstile> ((Var X0) EQ (Eats (Var v1) (Var v2))) IFF
                 (All X3 (Var X3 IN Var X0 IFF Var X3 IN Var v1 OR Var X3 EQ Var v2))"
    using v1 v2 by (drule_tac i=X2 and x="Var v2" in Subst) simp_all
  hence "{} \<turnstile> (((Var X0) EQ (Eats (Var v1) (Var v2))) IFF
             (All X3 (Var X3 IN Var X0 IFF Var X3 IN Var v1 OR Var X3 EQ Var v2)))(X0 ::= z)"
     by (rule Subst) simp
  hence "{} \<turnstile> ((z EQ (Eats (Var v1) (Var v2))) IFF
              (All i' (Var i' IN z IFF Var i' IN Var v1 OR Var i' EQ Var v2)))"
    using v1 v2 i' by (simp add: Conj_def Iff_def)
  hence "{} \<turnstile> (z EQ (Eats t (Var v2))) IFF
                 (All i' (Var i' IN z IFF Var i' IN t OR Var i' EQ Var v2))"
    using v1 v2 i' by (drule_tac i=v1 and x=t in Subst) simp_all
  hence "{} \<turnstile> (z EQ Eats t u) IFF
                 (All i' (Var i' IN z IFF Var i' IN t OR Var i' EQ u))"
    using v1 v2 i' by (drule_tac i=v2 and x=u in Subst) simp_all
  also have "... = (FRESH i'. (z EQ Eats t u) IFF (All i' (Var i' IN z IFF Var i' IN t OR Var i' EQ u)))"
    using i' by simp
  also have "... = (z EQ Eats t u) IFF (All i (Var i IN z IFF Var i IN t OR Var i EQ u))"
    using assms i' by simp
  finally show ?thesis
    by (rule thin0)
qed

lemma Eq_Eats_I:
  "H \<turnstile> All i (Var i IN z IFF Var i IN t OR Var i EQ u) \<Longrightarrow> atom i \<sharp> (z,t,u) \<Longrightarrow> H \<turnstile> z EQ Eats t u"
  by (metis Iff_MP2_same Eq_Eats_iff)

lemma Mem_Eats_Iff:
  "H \<turnstile> x IN (Eats t u) IFF x IN t OR x EQ u"
proof -
  obtain i::name where "atom i \<sharp> (Eats t u, t, u)"
    by (rule obtain_fresh)
  thus ?thesis
    using Iff_MP_same [OF Eq_Eats_iff, THEN All_D]
    by auto
qed

lemma Mem_Eats_I1: "H \<turnstile> u IN t \<Longrightarrow> H \<turnstile> u IN Eats t z"
  by (metis Disj_I1 Iff_MP2_same Mem_Eats_Iff)

lemma Mem_Eats_I2: "H \<turnstile> u EQ z \<Longrightarrow> H \<turnstile> u IN Eats t z"
  by (metis Disj_I2 Iff_MP2_same Mem_Eats_Iff)

lemma Mem_Eats_E:
  assumes A: "insert (u IN t) H \<turnstile> C" and B: "insert (u EQ z) H \<turnstile> C"
    shows "insert (u IN Eats t z) H \<turnstile> C"
  by (rule Mem_Eats_Iff [of _ u t z, THEN Iff_MP_left']) (metis A B Disj_E)

lemmas Mem_Eats_EH = Mem_Eats_E Mem_Eats_E [THEN rotate2] Mem_Eats_E [THEN rotate3] Mem_Eats_E [THEN rotate4] Mem_Eats_E [THEN rotate5]
                 Mem_Eats_E [THEN rotate6] Mem_Eats_E [THEN rotate7] Mem_Eats_E [THEN rotate8]
declare Mem_Eats_EH [intro!]

lemma Mem_SUCC_I1: "H \<turnstile> u IN t \<Longrightarrow> H \<turnstile> u IN SUCC t"
  by (metis Mem_Eats_I1 SUCC_def)

lemma Mem_SUCC_I2: "H \<turnstile> u EQ t \<Longrightarrow> H \<turnstile> u IN SUCC t"
  by (metis Mem_Eats_I2 SUCC_def)

lemma Mem_SUCC_Refl [simp]: "H \<turnstile> k IN SUCC k"
  by (metis Mem_SUCC_I2 Refl)

lemma Mem_SUCC_E:
  assumes "insert (u IN t) H \<turnstile> C" "insert (u EQ t) H \<turnstile> C" shows "insert (u IN SUCC t) H \<turnstile> C"
  by (metis assms Mem_Eats_E SUCC_def)

lemmas Mem_SUCC_EH = Mem_SUCC_E Mem_SUCC_E [THEN rotate2] Mem_SUCC_E [THEN rotate3] Mem_SUCC_E [THEN rotate4] Mem_SUCC_E [THEN rotate5]
                 Mem_SUCC_E [THEN rotate6] Mem_SUCC_E [THEN rotate7] Mem_SUCC_E [THEN rotate8]

lemma Eats_EQ_Zero_E: "insert (Eats t u EQ Zero) H \<turnstile> A"
  by (metis Assume Eq_Zero_D Mem_Eats_I2 Refl)

lemmas Eats_EQ_Zero_EH = Eats_EQ_Zero_E Eats_EQ_Zero_E [THEN rotate2] Eats_EQ_Zero_E [THEN rotate3] Eats_EQ_Zero_E [THEN rotate4] Eats_EQ_Zero_E [THEN rotate5]
                 Eats_EQ_Zero_E [THEN rotate6] Eats_EQ_Zero_E [THEN rotate7] Eats_EQ_Zero_E [THEN rotate8]
declare Eats_EQ_Zero_EH [intro!]

lemma Eats_EQ_Zero_E2: "insert (Zero EQ Eats t u) H \<turnstile> A"
  by (metis Eats_EQ_Zero_E Sym_L)

lemmas Eats_EQ_Zero_E2H = Eats_EQ_Zero_E2 Eats_EQ_Zero_E2 [THEN rotate2] Eats_EQ_Zero_E2 [THEN rotate3] Eats_EQ_Zero_E2 [THEN rotate4] Eats_EQ_Zero_E2 [THEN rotate5]
                 Eats_EQ_Zero_E2 [THEN rotate6] Eats_EQ_Zero_E2 [THEN rotate7] Eats_EQ_Zero_E2 [THEN rotate8]
declare Eats_EQ_Zero_E2H [intro!]


section\<open>Bounded Quantification involving @{term Eats}\<close>

lemma All2_cong: "H \<turnstile> t EQ t' \<Longrightarrow> H \<turnstile> A IFF A' \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> (All2 i t A) IFF (All2 i t' A')"
  by (metis All_cong Imp_cong Mem_cong Refl)

lemma All2_Zero_E [intro!]: "H  \<turnstile> B \<Longrightarrow> insert (All2 i Zero A) H \<turnstile> B"
  by (rule thin1)

lemma All2_Eats_I_D:
  "atom i \<sharp> (t,u) \<Longrightarrow> { All2 i t A, A(i::=u)} \<turnstile> (All2 i (Eats t u) A)"
    apply (auto, auto intro!: Ex_I [where x="Var i"])
    apply (metis Assume thin1 Var_Eq_subst_Iff [THEN Iff_MP_same])
    done

lemma All2_Eats_I:
  "\<lbrakk>atom i \<sharp> (t,u); H \<turnstile> All2 i t A; H \<turnstile> A(i::=u)\<rbrakk> \<Longrightarrow> H \<turnstile> (All2 i (Eats t u) A)"
  by (rule cut2 [OF All2_Eats_I_D], auto)

lemma All2_Eats_E1:
  "\<lbrakk>atom i \<sharp> (t,u); \<forall>C \<in> H. atom i \<sharp> C\<rbrakk> \<Longrightarrow> insert (All2 i (Eats t u) A) H \<turnstile> All2 i t A"
  by auto (metis Assume Ex_I Imp_E Mem_Eats_I1 Neg_mono subst_fm_id)

lemma All2_Eats_E2:
  "\<lbrakk>atom i \<sharp> (t,u); \<forall>C \<in> H. atom i \<sharp> C\<rbrakk> \<Longrightarrow> insert (All2 i (Eats t u) A) H \<turnstile> A(i::=u)"
  by (rule All_E [where x=u]) (auto intro: ContraProve Mem_Eats_I2)

lemma All2_Eats_E:
  assumes i: "atom i \<sharp> (t,u)"
      and B: "insert (All2 i t A) (insert (A(i::=u)) H) \<turnstile> B"
    shows "insert (All2 i (Eats t u) A) H \<turnstile> B"
  using i
  apply (rule cut_thin [OF All2_Eats_E2, where HB = "insert (All2 i (Eats t u) A) H"], auto)
  apply (rule cut_thin [OF All2_Eats_E1 B], auto)
  done

lemma All2_SUCC_I:
  "atom i \<sharp> t \<Longrightarrow> H \<turnstile> All2 i t A \<Longrightarrow> H \<turnstile> A(i::=t) \<Longrightarrow> H \<turnstile> (All2 i (SUCC t) A)"
  by (simp add: SUCC_def All2_Eats_I)

lemma All2_SUCC_E:
  assumes "atom i \<sharp> t"
      and "insert (All2 i t A) (insert (A(i::=t)) H) \<turnstile> B"
    shows "insert (All2 i (SUCC t) A) H \<turnstile> B"
  by (simp add: SUCC_def All2_Eats_E assms)

lemma All2_SUCC_E':
  assumes "H \<turnstile> u EQ SUCC t"
      and "atom i \<sharp> t" "\<forall>C \<in> H. atom i \<sharp> C"
      and "insert (All2 i t A) (insert (A(i::=t)) H) \<turnstile> B"
    shows "insert (All2 i u A) H \<turnstile> B"
  by (metis All2_SUCC_E Iff_MP_left' Iff_refl All2_cong assms)

section\<open>Induction\<close>

lemma Ind:
  assumes j: "atom (j::name) \<sharp> (i,A)"
  and prems: "H \<turnstile> A(i::=Zero)" "H \<turnstile> All i (All j (A IMP (A(i::= Var j) IMP A(i::= Eats(Var i)(Var j)))))"
  shows "H \<turnstile> A"
proof -
  have  "{A(i::=Zero), All i (All j (A IMP (A(i::= Var j) IMP A(i::= Eats(Var i)(Var j)))))} \<turnstile> All i A"
    by (metis j hfthm.Ind ind anti_deduction insert_commute)
  hence "H \<turnstile> (All i A)"
    by (metis cut2 prems)
  thus ?thesis
    by (metis All_E' Assume subst_fm_id)
qed

end
