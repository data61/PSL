chapter\<open>Formalizing Provability\<close>

theory Pf_Predicates
imports Coding_Predicates
begin

section \<open>Section 4 Predicates (Leading up to Pf)\<close>

subsection \<open>The predicate \<open>SentP\<close>, for the Sentiential (Boolean) Axioms\<close>

definition Sent_axioms :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool" where
 "Sent_axioms x y z w \<equiv>
             x = q_Imp y y \<or>
             x = q_Imp y (q_Disj y z) \<or>
             x = q_Imp (q_Disj y y) y \<or>
             x = q_Imp (q_Disj y (q_Disj z w)) (q_Disj (q_Disj y z) w) \<or>
             x = q_Imp (q_Disj y z) (q_Imp (q_Disj (q_Neg y) w) (q_Disj z w))"

definition Sent :: "hf set" where
 "Sent \<equiv> {x. \<exists>y z w. Form y \<and> Form z \<and> Form w \<and> Sent_axioms x y z w}"

nominal_function SentP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom y \<sharp> (z,w,x); atom z \<sharp> (w,x); atom w \<sharp> x\<rbrakk> \<Longrightarrow>
    SentP x = Ex y (Ex z (Ex w (FormP (Var y) AND FormP (Var z) AND FormP (Var w) AND
               ( (x EQ Q_Imp (Var y) (Var y)) OR
                 (x EQ Q_Imp (Var y) (Q_Disj (Var y) (Var z)) OR
                 (x EQ Q_Imp (Q_Disj (Var y) (Var y)) (Var y)) OR
                 (x EQ Q_Imp (Q_Disj (Var y) (Q_Disj (Var z) (Var w))) 
                             (Q_Disj (Q_Disj (Var y) (Var z)) (Var w))) OR
                 (x EQ Q_Imp (Q_Disj (Var y) (Var z))
                             (Q_Imp (Q_Disj (Q_Neg (Var y)) (Var w)) (Q_Disj (Var z) (Var w)))))))))"
  by (auto simp: eqvt_def SentP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows SentP_fresh_iff [simp]: "a \<sharp> SentP x \<longleftrightarrow> a \<sharp> x"                  (is ?thesis1)
   and eval_fm_SentP [simp]:   "eval_fm e (SentP x) \<longleftrightarrow> \<lbrakk>x\<rbrakk>e \<in> Sent"    (is ?thesis2)
   and SentP_sf [iff]:         "Sigma_fm (SentP x)"                     (is ?thsf)
proof -
  obtain y::name and z::name and w::name  where "atom y \<sharp> (z,w,x)" "atom z \<sharp> (w,x)" "atom w \<sharp> x"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: Sent_def Sent_axioms_def q_defs)
qed

subsection \<open>The predicate \<open>Equality_axP\<close>, for the Equality Axioms\<close>

definition Equality_ax :: "hf set" where
 "Equality_ax \<equiv> { \<lbrakk>\<lceil>refl_ax\<rceil>\<rbrakk>e0, \<lbrakk>\<lceil>eq_cong_ax\<rceil>\<rbrakk>e0, \<lbrakk>\<lceil>mem_cong_ax\<rceil>\<rbrakk>e0, \<lbrakk>\<lceil>eats_cong_ax\<rceil>\<rbrakk>e0 }"

function Equality_axP :: "tm \<Rightarrow> fm"
  where "Equality_axP x =
    x EQ \<lceil>refl_ax\<rceil> OR x EQ \<lceil>eq_cong_ax\<rceil> OR x EQ \<lceil>mem_cong_ax\<rceil> OR x EQ \<lceil>eats_cong_ax\<rceil>"
by auto

termination
  by lexicographic_order

lemma eval_fm_Equality_axP [simp]: "eval_fm e (Equality_axP x) \<longleftrightarrow> \<lbrakk>x\<rbrakk>e \<in> Equality_ax"
  by (auto simp: Equality_ax_def intro: eval_quot_fm_ignore)

subsection \<open>The predicate \<open>HF_axP\<close>, for the HF Axioms\<close>

definition HF_ax :: "hf set" where
  "HF_ax \<equiv> {\<lbrakk>\<lceil>HF1\<rceil>\<rbrakk>e0, \<lbrakk>\<lceil>HF2\<rceil>\<rbrakk>e0}"

function HF_axP :: "tm \<Rightarrow> fm"
  where "HF_axP x = x EQ \<lceil>HF1\<rceil> OR x EQ \<lceil>HF2\<rceil>"
by auto

termination
  by lexicographic_order

lemma eval_fm_HF_axP [simp]: "eval_fm e (HF_axP x) \<longleftrightarrow> \<lbrakk>x\<rbrakk>e \<in> HF_ax"
  by (auto simp: HF_ax_def intro: eval_quot_fm_ignore)

lemma HF_axP_sf [iff]: "Sigma_fm (HF_axP t)"
  by auto


subsection \<open>The specialisation axioms\<close>

inductive_set Special_ax :: "hf set" where
  I: "\<lbrakk>AbstForm v 0 x ax; SubstForm v y x sx; Form x; is_Var v; Term y\<rbrakk>
      \<Longrightarrow> q_Imp sx (q_Ex ax) \<in> Special_ax"

subsubsection \<open>Defining the syntax\<close>

nominal_function Special_axP :: "tm \<Rightarrow> fm" where
  "\<lbrakk>atom v \<sharp> (p,sx,y,ax,x); atom x \<sharp> (p,sx,y,ax);
    atom ax \<sharp> (p,sx,y); atom y \<sharp> (p,sx); atom sx \<sharp> p\<rbrakk> \<Longrightarrow>
  Special_axP p = Ex v (Ex x (Ex ax (Ex y (Ex sx
                   (FormP (Var x) AND VarP (Var v) AND TermP (Var y) AND
                    AbstFormP (Var v) Zero (Var x) (Var ax) AND
                    SubstFormP (Var v) (Var y) (Var x) (Var sx) AND
                    p EQ Q_Imp (Var sx) (Q_Ex (Var ax)))))))"
  by (auto simp: eqvt_def Special_axP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows Special_axP_fresh_iff [simp]: "a \<sharp> Special_axP p \<longleftrightarrow> a \<sharp> p" (is ?thesis1)
   and eval_fm_Special_axP [simp]: "eval_fm e (Special_axP p) \<longleftrightarrow> \<lbrakk>p\<rbrakk>e \<in> Special_ax" (is ?thesis2)
   and Special_axP_sf [iff]:       "Sigma_fm (Special_axP p)" (is ?thesis3)
proof -
  obtain v::name and x::name and ax::name and y::name and sx::name
    where "atom v \<sharp> (p,sx,y,ax,x)" "atom x \<sharp> (p,sx,y,ax)"
          "atom ax \<sharp> (p,sx,y)" "atom y \<sharp> (p,sx)" "atom sx \<sharp> p"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thesis3
    apply auto
    apply (metis q_Disj_def q_Ex_def q_Imp_def q_Neg_def Special_ax.intros)
    apply (metis q_Disj_def q_Ex_def q_Imp_def q_Neg_def Special_ax.cases)
    done
qed

subsubsection \<open>Correctness (or, correspondence)\<close>

lemma Special_ax_imp_special_axioms:
  assumes "x \<in> Special_ax" shows "\<exists>A. x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> A \<in> special_axioms"
using assms
proof (induction rule: Special_ax.induct)
  case (I v x ax y sx)
  obtain fm::fm and u::tm where fm: "x = \<lbrakk>\<lceil>fm\<rceil>\<rbrakk>e" and  u: "y = \<lbrakk>\<lceil>u\<rceil>\<rbrakk>e"
    using I  by (auto elim!: Form_imp_is_fm Term_imp_is_tm)
  obtain B where x: "x  = \<lbrakk>quot_dbfm B\<rbrakk>e"
            and ax: "ax = \<lbrakk>quot_dbfm (abst_dbfm (decode_Var v) 0 B)\<rbrakk>e"
    using I AbstForm_imp_abst_dbfm  by force
  obtain B' where x': "x = \<lbrakk>quot_dbfm B'\<rbrakk>e"
             and sx: "sx = \<lbrakk>quot_dbfm (subst_dbfm (trans_tm [] u) (decode_Var v) B')\<rbrakk>e"
    using I  by (metis u SubstForm_imp_subst_dbfm_lemma quot_tm_def)
  have eq: "B'=B"
    by (metis quot_dbfm_inject_lemma x x')
  have "fm(decode_Var v::=u) IMP SyntaxN.Ex (decode_Var v) fm \<in> special_axioms"
    by (metis special_axioms.intros)
  thus ?case using eq
    apply (auto simp: quot_simps q_defs 
                intro!: exI [where x = "fm((decode_Var v)::=u) IMP (Ex (decode_Var v) fm)"])
    apply (metis fm quot_dbfm_inject_lemma quot_fm_def subst_fm_trans_commute sx x')
    apply (metis abst_trans_fm ax fm quot_dbfm_inject_lemma quot_fm_def x)
    done
qed

lemma special_axioms_into_Special_ax: "A \<in> special_axioms \<Longrightarrow> \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<in> Special_ax"
proof (induct rule: special_axioms.induct)
  case (I A i t)
  have "\<lbrakk>\<lceil>A(i::=t) IMP SyntaxN.Ex i A\<rceil>\<rbrakk>e =
        q_Imp \<lbrakk>quot_dbfm (subst_dbfm (trans_tm [] t) i (trans_fm [] A))\<rbrakk>e
              (q_Ex \<lbrakk>quot_dbfm (trans_fm [i] A)\<rbrakk>e)"
    by (simp add: quot_fm_def q_defs)
  also have "... \<in> Special_ax"
    apply (rule Special_ax.intros [OF AbstForm_trans_fm])
    apply (auto simp: quot_fm_def [symmetric] intro: SubstForm_quot [unfolded eval_Var_q])
    done
  finally show ?case .
qed

text\<open>We have precisely captured the codes of the specialisation axioms.\<close>
corollary Special_ax_eq_special_axioms: "Special_ax = (\<Union>A \<in> special_axioms. { \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e })"
  by (force dest: special_axioms_into_Special_ax Special_ax_imp_special_axioms)


subsection \<open>The induction axioms\<close>

inductive_set Induction_ax :: "hf set" where
  I: "\<lbrakk>SubstForm v 0 x x0;
       SubstForm v w x xw;
       SubstForm v (q_Eats v w) x xevw;
       AbstForm w 0 (q_Imp x (q_Imp xw xevw)) allw;
       AbstForm v 0 (q_All allw) allvw;
       AbstForm v 0 x ax;
       v \<noteq> w; VarNonOccForm w x\<rbrakk>
      \<Longrightarrow> q_Imp x0 (q_Imp (q_All allvw) (q_All ax)) \<in> Induction_ax"

subsubsection \<open>Defining the syntax\<close>

nominal_function Induction_axP :: "tm \<Rightarrow> fm" where
  "\<lbrakk>atom ax \<sharp> (p,v,w,x,x0,xw,xevw,allw,allvw);
    atom allvw \<sharp> (p,v,w,x,x0,xw,xevw,allw); atom allw \<sharp> (p,v,w,x,x0,xw,xevw);
    atom xevw \<sharp> (p,v,w,x,x0,xw); atom xw \<sharp> (p,v,w,x,x0);
    atom x0 \<sharp> (p,v,w,x); atom x \<sharp> (p,v,w);
    atom w \<sharp> (p,v); atom v \<sharp> p\<rbrakk> \<Longrightarrow>
  Induction_axP p = Ex v (Ex w (Ex x (Ex x0 (Ex xw (Ex xevw (Ex allw (Ex allvw (Ex ax
               ((Var v NEQ Var w) AND VarNonOccFormP (Var w) (Var x) AND
                SubstFormP (Var v) Zero (Var x) (Var x0) AND
                SubstFormP (Var v) (Var w) (Var x) (Var xw) AND
                SubstFormP (Var v) (Q_Eats (Var v) (Var w)) (Var x) (Var xevw) AND
                AbstFormP (Var w) Zero (Q_Imp (Var x) (Q_Imp (Var xw) (Var xevw))) (Var allw) AND
                AbstFormP (Var v) Zero (Q_All (Var allw)) (Var allvw) AND
                AbstFormP (Var v) Zero (Var x) (Var ax) AND
                p EQ Q_Imp (Var x0) (Q_Imp (Q_All (Var allvw)) (Q_All (Var ax))))))))))))"
  by (auto simp: eqvt_def Induction_axP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows Induction_axP_fresh_iff [simp]: "a \<sharp> Induction_axP p \<longleftrightarrow> a \<sharp> p" (is ?thesis1)
   and eval_fm_Induction_axP [simp]:
      "eval_fm e (Induction_axP p) \<longleftrightarrow> \<lbrakk>p\<rbrakk>e \<in> Induction_ax"    (is ?thesis2)
   and Induction_axP_sf [iff]: "Sigma_fm (Induction_axP p)" (is ?thesis3)
proof -
  obtain v::name and w::name and x::name and x0::name and xw::name and xevw::name
                 and allw::name and allvw::name and ax::name
    where atoms: "atom ax \<sharp> (p,v,w,x,x0,xw,xevw,allw,allvw)"
                 "atom allvw \<sharp> (p,v,w,x,x0,xw,xevw,allw)" "atom allw \<sharp> (p,v,w,x,x0,xw,xevw)"
                 "atom xevw \<sharp> (p,v,w,x,x0,xw)" "atom xw \<sharp> (p,v,w,x,x0)" "atom x0 \<sharp> (p,v,w,x)"
                 "atom x \<sharp> (p,v,w)" "atom w \<sharp> (p,v)" "atom v \<sharp> p"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis3
    by auto
  show ?thesis2
    proof
      assume "eval_fm e (Induction_axP p)"
      thus "\<lbrakk>p\<rbrakk>e \<in> Induction_ax" using atoms
        by (auto intro!: Induction_ax.I [unfolded q_defs])
    next
      assume "\<lbrakk>p\<rbrakk>e \<in> Induction_ax"
      thus "eval_fm e (Induction_axP p)"
        apply (rule Induction_ax.cases) using atoms
        apply (force simp: q_defs htuple_minus_1 intro!: AbstForm_imp_Ord)
        done
    qed
qed

subsubsection \<open>Correctness (or, correspondence)\<close>

lemma Induction_ax_imp_induction_axioms:
  assumes "x \<in> Induction_ax" shows "\<exists>A. x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> A \<in> induction_axioms"
using assms
proof (induction rule: Induction_ax.induct)
  case (I v x x0 w xw xevw allw allvw ax)
  then have v: "is_Var v" and w: "is_Var w"
        and dvw [simp]: "decode_Var v \<noteq> decode_Var w"  "atom (decode_Var w) \<sharp> [decode_Var v]" 
    by (auto simp: AbstForm_def fresh_Cons)
  obtain A::fm where A: "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e" and wfresh: "atom (decode_Var w) \<sharp> A"
    using I VarNonOccForm_imp_fresh  by blast
  then obtain A' A'' where A': "q_Imp (\<lbrakk>\<lceil>A\<rceil>\<rbrakk>e) (q_Imp xw xevw) = \<lbrakk>quot_dbfm A'\<rbrakk>e"
                       and A'': "q_All allw = \<lbrakk>quot_dbfm A''\<rbrakk>e"
    using I VarNonOccForm_imp_fresh by (auto dest!: AbstForm_imp_abst_dbfm)
  define Aw where "Aw = A(decode_Var v::=Var (decode_Var w))"
  define Ae where "Ae = A(decode_Var v::= Eats (Var (decode_Var v)) (Var (decode_Var w)))"
  have x0: "x0 = \<lbrakk>\<lceil>A(decode_Var v::=Zero)\<rceil>\<rbrakk>e"  using I SubstForm_imp_subst_fm 
    by (metis A Form_quot_fm eval_fm_inject eval_tm.simps(1) quot_Zero)
  have xw: "xw = \<lbrakk>\<lceil>Aw\<rceil>\<rbrakk>e"  using I SubstForm_imp_subst_fm
    by (metis A Form_quot_fm eval_fm_inject is_Var_imp_decode_Var w Aw_def)
  have "SubstForm v (\<lbrakk>\<lceil>Eats (Var (decode_Var v)) (Var (decode_Var w))\<rceil>\<rbrakk>e) x xevw"
    using I  by (simp add: quot_simps q_defs) (metis is_Var_iff v w)
  hence xevw: "xevw = \<lbrakk>\<lceil>Ae\<rceil>\<rbrakk>e"
    by (metis A Ae_def Form_quot_fm SubstForm_imp_subst_fm eval_fm_inject)
  have ax: "ax = \<lbrakk>quot_dbfm (abst_dbfm (decode_Var v) 0 (trans_fm [] A))\<rbrakk>e"
    using I  by (metis A AbstForm_imp_abst_dbfm nat_of_ord_0 quot_dbfm_inject_lemma quot_fm_def)
  have evw: "q_Imp x (q_Imp xw xevw) =
             \<lbrakk>quot_dbfm (trans_fm [] (A IMP (Aw IMP Ae)))\<rbrakk>e"
    using A xw xevw  by (auto simp: quot_simps q_defs quot_fm_def)
  hence allw: "allw = \<lbrakk>quot_dbfm (abst_dbfm (decode_Var w) 0
                                    (trans_fm [] (A IMP (Aw IMP Ae))))\<rbrakk>e"
    using I  by (metis AbstForm_imp_abst_dbfm nat_of_ord_0 quot_dbfm_inject_lemma)
  then have evw: "q_All allw = \<lbrakk>quot_dbfm (trans_fm [] (All (decode_Var w) (A IMP (Aw IMP Ae))))\<rbrakk>e"
    by (auto simp: q_defs abst_trans_fm)
  hence allvw: "allvw = \<lbrakk>quot_dbfm (abst_dbfm (decode_Var v) 0
                                     (trans_fm [] (All (decode_Var w) (A IMP (Aw IMP Ae)))))\<rbrakk>e"
    using I  by (metis AbstForm_imp_abst_dbfm nat_of_ord_0 quot_dbfm_inject_lemma)
  define ind_ax
    where "ind_ax =
        A(decode_Var v::=Zero) IMP
        ((All (decode_Var v) (All (decode_Var w) (A IMP (Aw IMP Ae)))) IMP
        (All (decode_Var v) A))"
  have "atom (decode_Var w) \<sharp> (decode_Var v, A)" using I wfresh v w
    by (metis atom_eq_iff decode_Var_inject fresh_Pair fresh_ineq_at_base)
  hence "ind_ax \<in> induction_axioms"
    by (auto simp: ind_ax_def Aw_def Ae_def induction_axioms.intros)
  thus ?case
    by (force simp: quot_simps q_defs ind_ax_def allvw ax x0 abst_trans_fm2 abst_trans_fm)
qed


lemma induction_axioms_into_Induction_ax:
  "A \<in> induction_axioms \<Longrightarrow> \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<in> Induction_ax"
proof (induct rule: induction_axioms.induct)
  case (ind j i A)
  hence eq: "\<lbrakk>\<lceil>A(i::=Zero) IMP All i (All j (A IMP A(i::=Var j) IMP A(i::=Eats (Var i) (Var j)))) IMP All i A\<rceil>\<rbrakk>e =
            q_Imp \<lbrakk>quot_dbfm (subst_dbfm (trans_tm [] Zero) i (trans_fm [] A))\<rbrakk>e
            (q_Imp (q_All (q_All
                  (q_Imp \<lbrakk>quot_dbfm (trans_fm [j, i] A)\<rbrakk>e
                    (q_Imp
                      \<lbrakk>quot_dbfm (trans_fm [j, i] (A(i::=Var j)))\<rbrakk>e
                      \<lbrakk>quot_dbfm (trans_fm [j, i] (A(i::=Eats (Var i) (Var j))))\<rbrakk>e))))
              (q_All \<lbrakk>quot_dbfm (trans_fm [i] A)\<rbrakk>e))"
    by (simp add: quot_simps q_defs quot_subst_eq fresh_Cons fresh_Pair)
  have [simp]: "atom j \<sharp> [i]" using ind
    by (metis fresh_Cons fresh_Nil fresh_Pair)
  show ?case
  proof (simp only: eq, rule Induction_ax.intros [where v = "q_Var i" and w = "q_Var j"])
    show "SubstForm (q_Var i) 0 \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e
           \<lbrakk>quot_dbfm (subst_dbfm (trans_tm [] Zero) i (trans_fm [] A))\<rbrakk>e"
     by (metis SubstForm_subst_dbfm_eq Term_quot_tm eval_tm.simps(1) quot_Zero quot_fm_def quot_tm_def)
  next
    show "SubstForm (q_Var i) (q_Var j) \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<lbrakk>quot_dbfm (subst_dbfm (DBVar j) i (trans_fm [] A))\<rbrakk>e"
      by (auto simp: quot_fm_def intro!: SubstForm_subst_dbfm_eq Term_Var)
         (metis q_Var_def)
  next
    show "SubstForm (q_Var i) (q_Eats (q_Var i) (q_Var j)) \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e
              \<lbrakk>quot_dbfm (subst_dbfm (DBEats (DBVar i) (DBVar j)) i (trans_fm [] A))\<rbrakk>e"
      unfolding quot_fm_def
        by (auto intro!: SubstForm_subst_dbfm_eq Term_Eats Term_Var) (simp add: q_defs)
  next
    show "AbstForm (q_Var j) 0
           (q_Imp \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e
              (q_Imp \<lbrakk>quot_dbfm (subst_dbfm (DBVar j) i (trans_fm [] A))\<rbrakk>e
                     \<lbrakk>quot_dbfm (subst_dbfm (DBEats (DBVar i) (DBVar j)) i (trans_fm [] A))\<rbrakk>e))
           \<lbrakk>quot_dbfm (trans_fm [j] (A IMP (A(i::= Var j) IMP A(i::= Eats(Var i)(Var j)))))\<rbrakk>e"
      by (rule AbstForm_trans_fm_eq [where A = "(A IMP A(i::= Var j) IMP A(i::= Eats(Var i)(Var j)))"])
         (auto simp: quot_simps q_defs quot_fm_def subst_fm_trans_commute_eq)
  next
    show "AbstForm (q_Var i) 0
     (q_All \<lbrakk>quot_dbfm (trans_fm [j] (A IMP A(i::=Var j) IMP A(i::=Eats (Var i) (Var j))))\<rbrakk>e)
     (q_All
       (q_Imp \<lbrakk>quot_dbfm (trans_fm [j, i] A)\<rbrakk>e
         (q_Imp \<lbrakk>quot_dbfm (trans_fm [j, i] (A(i::=Var j)))\<rbrakk>e
                \<lbrakk>quot_dbfm (trans_fm [j, i] (A(i::=Eats (Var i) (Var j))))\<rbrakk>e)))"
      apply (rule AbstForm_trans_fm_eq
               [where A = "All j (A IMP (A(i::= Var j) IMP A(i::= Eats(Var i)(Var j))))"])
      apply (auto simp: q_defs quot_fm_def)
      done
  next
    show "AbstForm (q_Var i) 0 (\<lbrakk>\<lceil>A\<rceil>\<rbrakk>e) \<lbrakk>quot_dbfm (trans_fm [i] A)\<rbrakk>e"
      by (metis AbstForm_trans_fm)
  next
    show "q_Var i \<noteq> q_Var j" using ind
      by (simp add: q_Var_def)
  next
    show "VarNonOccForm (q_Var j) (\<lbrakk>\<lceil>A\<rceil>\<rbrakk>e)"
      by (metis fresh_Pair fresh_imp_VarNonOccForm ind)
  qed
qed

text\<open>We have captured the codes of the induction axioms.\<close>
corollary Induction_ax_eq_induction_axioms:
  "Induction_ax = (\<Union>A \<in> induction_axioms. {\<lbrakk>\<lceil>A\<rceil>\<rbrakk>e})"
  by (force dest: induction_axioms_into_Induction_ax Induction_ax_imp_induction_axioms)


subsection \<open>The predicate \<open>AxiomP\<close>, for any Axioms\<close>

definition Extra_ax :: "hf set" where
 "Extra_ax \<equiv> {\<lbrakk>\<lceil>extra_axiom\<rceil>\<rbrakk>e0}"

definition Axiom :: "hf set" where
  "Axiom \<equiv> Extra_ax \<union> Sent \<union> Equality_ax \<union> HF_ax \<union> Special_ax \<union> Induction_ax"

definition AxiomP :: "tm \<Rightarrow> fm"
  where "AxiomP x \<equiv> x EQ \<lceil>extra_axiom\<rceil> OR SentP x OR Equality_axP x OR
                    HF_axP x OR Special_axP x OR Induction_axP x"

lemma AxiomP_eqvt [eqvt]: "(p \<bullet> AxiomP x) = AxiomP (p \<bullet> x)"
  by (simp add: AxiomP_def)

lemma AxiomP_fresh_iff [simp]: "a \<sharp> AxiomP x \<longleftrightarrow> a \<sharp> x"
  by (auto simp: AxiomP_def)

lemma eval_fm_AxiomP [simp]: "eval_fm e (AxiomP x) \<longleftrightarrow> \<lbrakk>x\<rbrakk>e \<in> Axiom"
  unfolding AxiomP_def Axiom_def Extra_ax_def
  by (auto simp del: Equality_axP.simps HF_axP.simps intro: eval_quot_fm_ignore)

lemma AxiomP_sf [iff]: "Sigma_fm (AxiomP t)"
  by (auto simp: AxiomP_def)


subsection \<open>The predicate \<open>ModPonP\<close>, for the inference rule Modus Ponens\<close>

definition ModPon :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool" where
  "ModPon x y z \<equiv> (y = q_Imp x z)"

definition ModPonP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "ModPonP x y z = (y EQ Q_Imp x z)"

lemma ModPonP_eqvt [eqvt]: "(p \<bullet> ModPonP x y z) = ModPonP (p \<bullet> x) (p \<bullet> y) (p \<bullet> z)"
  by (simp add: ModPonP_def)

lemma ModPonP_fresh_iff [simp]: "a \<sharp> ModPonP x y z \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> y \<and> a \<sharp> z"
  by (auto simp: ModPonP_def)

lemma eval_fm_ModPonP [simp]: "eval_fm e (ModPonP x y z) \<longleftrightarrow> ModPon \<lbrakk>x\<rbrakk>e \<lbrakk>y\<rbrakk>e \<lbrakk>z\<rbrakk>e"
  by (auto simp: ModPon_def ModPonP_def q_defs)

lemma ModPonP_sf [iff]: "Sigma_fm (ModPonP t u v)"
  by (auto simp: ModPonP_def)

lemma ModPonP_subst [simp]:
  "(ModPonP t u v)(i::=w) = ModPonP (subst i w t) (subst i w u) (subst i w v)"
  by (auto simp: ModPonP_def)


subsection \<open>The predicate \<open>ExistsP\<close>, for the existential rule\<close>
subsubsection \<open>Definition\<close>

(*  "\<turnstile> A IMP B \<Longrightarrow> atom i \<sharp> B \<Longrightarrow>  \<turnstile> (Ex i A) IMP B" *)
definition Exists :: "hf \<Rightarrow> hf \<Rightarrow> bool" where
 "Exists p q \<equiv> (\<exists>x x' y v. Form x \<and> VarNonOccForm v y \<and> AbstForm v 0 x x' \<and>
                p = q_Imp x y \<and> q = q_Imp (q_Ex x') y)"

nominal_function ExistsP :: "tm \<Rightarrow> tm \<Rightarrow> fm" where
  "\<lbrakk>atom x \<sharp> (p,q,v,y,x'); atom x' \<sharp> (p,q,v,y);
    atom y \<sharp> (p,q,v); atom v \<sharp> (p,q)\<rbrakk> \<Longrightarrow>
  ExistsP p q = Ex x (Ex x' (Ex y (Ex v (FormP (Var x) AND
                    VarNonOccFormP (Var v) (Var y) AND
                    AbstFormP (Var v) Zero (Var x) (Var x') AND
                    p EQ Q_Imp (Var x) (Var y) AND
                    q EQ Q_Imp (Q_Ex (Var x')) (Var y)))))"
  by (auto simp: eqvt_def ExistsP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows ExistsP_fresh_iff [simp]: "a \<sharp> ExistsP p q \<longleftrightarrow> a \<sharp> p \<and> a \<sharp> q"    (is ?thesis1)
   and eval_fm_ExistsP [simp]: "eval_fm e (ExistsP p q) \<longleftrightarrow> Exists \<lbrakk>p\<rbrakk>e \<lbrakk>q\<rbrakk>e"  (is ?thesis2)
   and ExistsP_sf [iff]:       "Sigma_fm (ExistsP p q)"   (is ?thesis3)
proof -
  obtain x::name and x'::name and y::name and v::name
    where "atom x \<sharp> (p,q,v,y,x')"  "atom x' \<sharp> (p,q,v,y)" "atom y \<sharp> (p,q,v)"  "atom v \<sharp> (p,q)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thesis3
    by (auto simp: Exists_def q_defs)
qed

lemma ExistsP_subst [simp]: "(ExistsP p q)(j::=w) = ExistsP (subst j w p) (subst j w q)"
proof -
  obtain x::name and x'::name and y::name and v::name
    where "atom x \<sharp> (j,w,p,q,v,y,x')"   "atom x' \<sharp> (j,w,p,q,v,y)"
          "atom y \<sharp> (j,w,p,q,v)"   "atom v \<sharp> (j,w,p,q)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: ExistsP.simps [of x _ _ x' y v])
qed

subsubsection \<open>Correctness\<close>

lemma Exists_imp_exists:
  assumes "Exists p q"
  shows "\<exists>A B i. p = \<lbrakk>\<lceil>A IMP B\<rceil>\<rbrakk>e \<and> q = \<lbrakk>\<lceil>(Ex i A) IMP B\<rceil>\<rbrakk>e \<and> atom i \<sharp> B"
proof -
  obtain x ax y v
    where x:    "Form x"
      and noc:  "VarNonOccForm v y"
      and abst: "AbstForm v 0 x ax"
      and p: "p = q_Imp x y"
      and q: "q = q_Imp (q_Ex ax) y"
    using assms  by (auto simp: Exists_def)
  then obtain B::fm where B: "y = \<lbrakk>\<lceil>B\<rceil>\<rbrakk>e" and vfresh: "atom (decode_Var v) \<sharp> B"
   by (metis VarNonOccForm_imp_fresh)
  obtain A::fm where A: "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e" 
    by (metis Form_imp_is_fm x)
  with AbstForm_imp_abst_dbfm [OF abst, of e]
  have ax: "ax = \<lbrakk>quot_dbfm (abst_dbfm (decode_Var v) 0 (trans_fm [] A))\<rbrakk>e"
           "p = \<lbrakk>\<lceil>A IMP B\<rceil>\<rbrakk>e" using p A B
    by (auto simp: quot_simps quot_fm_def q_defs)
  have "q = \<lbrakk>\<lceil>(Ex (decode_Var v) A) IMP B\<rceil>\<rbrakk>e" using q A B ax
    by (auto simp: abst_trans_fm quot_simps q_defs)
  then show ?thesis using vfresh ax
    by blast
qed

lemma Exists_intro: "atom i \<sharp> B \<Longrightarrow> Exists (\<lbrakk>\<lceil>A IMP B\<rceil>\<rbrakk>e) \<lbrakk>\<lceil>(Ex i A) IMP B\<rceil>\<rbrakk>e"
  by (simp add: Exists_def quot_simps q_defs)
     (metis AbstForm_trans_fm Form_quot_fm fresh_imp_VarNonOccForm)

text\<open>Thus, we have precisely captured the codes of the specialisation axioms.\<close>
corollary Exists_iff_exists:
  "Exists p q \<longleftrightarrow> (\<exists>A B i. p = \<lbrakk>\<lceil>A IMP B\<rceil>\<rbrakk>e \<and> q = \<lbrakk>\<lceil>(Ex i A) IMP B\<rceil>\<rbrakk>e \<and> atom i \<sharp> B)"
  by (force dest: Exists_imp_exists Exists_intro)


subsection \<open>The predicate \<open>SubstP\<close>, for the substitution rule\<close>

text\<open>Although the substitution rule is derivable in the calculus, the derivation is
too complicated to reproduce within the proof function. It is much easier to
provide it as an immediate inference step, justifying its soundness in terms
of other inference rules.\<close>

subsubsection \<open>Definition\<close>

text\<open>This is the inference \<open>H \<turnstile> A \<Longrightarrow> H \<turnstile> A (i::=x)\<close>\<close>
definition Subst :: "hf \<Rightarrow> hf \<Rightarrow> bool" where
  "Subst p q \<equiv> (\<exists>v u. SubstForm v u p q)"

nominal_function SubstP :: "tm \<Rightarrow> tm \<Rightarrow> fm" where
  "\<lbrakk>atom u \<sharp> (p,q,v); atom v \<sharp> (p,q)\<rbrakk> \<Longrightarrow>
   SubstP p q = Ex v (Ex u (SubstFormP (Var v) (Var u) p q))"
  by (auto simp: eqvt_def SubstP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows SubstP_fresh_iff [simp]: "a \<sharp> SubstP p q \<longleftrightarrow> a \<sharp> p \<and> a \<sharp> q"        (is ?thesis1)
   and eval_fm_SubstP [simp]: "eval_fm e (SubstP p q) \<longleftrightarrow> Subst \<lbrakk>p\<rbrakk>e \<lbrakk>q\<rbrakk>e" (is ?thesis2)
   and SubstP_sf [iff]: "Sigma_fm (SubstP p q)"                           (is ?thesis3)
proof -
  obtain u::name and v::name  where "atom u \<sharp> (p,q,v)" "atom v \<sharp> (p,q)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thesis3
    by (auto simp: Subst_def q_defs)
qed

lemma SubstP_subst [simp]: "(SubstP p q)(j::=w) = SubstP (subst j w p) (subst j w q)"
proof -
  obtain u::name and v::name  where "atom u \<sharp> (j,w,p,q,v)"  "atom v \<sharp> (j,w,p,q)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: SubstP.simps [of u _ _ v])
qed

subsubsection \<open>Correctness\<close>

lemma Subst_imp_subst:
  assumes "Subst p q" "Form p"
  shows "\<exists>A::fm. \<exists>i t. p = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> q = \<lbrakk>\<lceil>A(i::=t)\<rceil>\<rbrakk>e"
proof -
  obtain v u where subst: "SubstForm v u p q" using assms
    by (auto simp: Subst_def)
  then obtain t::tm where substt: "SubstForm v \<lbrakk>\<lceil>t\<rceil>\<rbrakk>e p q"
    by (metis SubstForm_def Term_imp_is_tm)
  with SubstForm_imp_subst_fm [OF substt] assms
  obtain A where "p = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e"  "q = \<lbrakk>\<lceil>A(decode_Var v::=t)\<rceil>\<rbrakk>e"
    by auto
  thus ?thesis
    by blast
qed


subsection \<open>The predicate \<open>PrfP\<close>\<close>

(*Prf(s,k,t) \<equiv> LstSeq(s,k,t) \<and> (\<forall>n\<in>k)[Sent (s n) \<or> (\<exists>m,l\<in>n)[ModPon (s m) (s l) (s n)]]*)
definition Prf :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "Prf s k y \<equiv> BuildSeq (\<lambda>x. x \<in> Axiom) (\<lambda>u v w. ModPon v w u \<or> Exists v u \<or> Subst v u) s k y"

nominal_function PrfP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,sl,m,n,sm,sn); atom sl \<sharp> (s,m,n,sm,sn);
          atom m \<sharp> (s,n,sm,sn); atom n \<sharp> (s,k,sm,sn);
          atom sm \<sharp> (s,sn); atom sn \<sharp> (s)\<rbrakk> \<Longrightarrow>
    PrfP s k t =
      LstSeqP s k t AND
      All2 n (SUCC k) (Ex sn (HPair (Var n) (Var sn) IN s AND (AxiomP (Var sn) OR
                Ex m (Ex l (Ex sm (Ex sl (Var m IN Var n AND Var l IN Var n AND
                       HPair (Var m) (Var sm) IN s AND HPair (Var l) (Var sl) IN s AND
                       (ModPonP (Var sm) (Var sl) (Var sn) OR
                        ExistsP (Var sm) (Var sn) OR
                        SubstP (Var sm) (Var sn)))))))))"
  by (auto simp: eqvt_def PrfP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows PrfP_fresh_iff [simp]: "a \<sharp> PrfP s k t \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> t"      (is ?thesis1)
  and eval_fm_PrfP [simp]:     "eval_fm e (PrfP s k t) \<longleftrightarrow> Prf \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e \<lbrakk>t\<rbrakk>e"  (is ?thesis2)
  and PrfP_imp_OrdP [simp]:    "{PrfP s k t} \<turnstile> OrdP k"         (is ?thord)
  and PrfP_imp_LstSeqP [simp]: "{PrfP s k t} \<turnstile> LstSeqP s k t"  (is ?thlstseq)
  and PrfP_sf [iff]:           "Sigma_fm (PrfP s k t)"         (is ?thsf)
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms: "atom l \<sharp> (s,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,m,n,sm,sn)"
        "atom m \<sharp> (s,n,sm,sn)"   "atom n \<sharp> (s,k,sm,sn)"
        "atom sm \<sharp> (s,sn)"   "atom sn \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thord ?thlstseq ?thsf
    by (auto intro: LstSeqP_OrdP)
  show ?thesis2 using atoms
    by simp
       (simp cong: conj_cong add: LstSeq_imp_Ord Prf_def BuildSeq_def Builds_def
             ModPon_def Exists_def HBall_def HBex_def
             Seq_iff_app [OF LstSeq_imp_Seq_succ]
             Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"])
qed

lemma PrfP_subst [simp]:
     "(PrfP t u v)(j::=w) = PrfP (subst j w t) (subst j w u) (subst j w v)"
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where "atom l \<sharp> (t,u,v,j,w,sl,m,n,sm,sn)"   "atom sl \<sharp> (t,u,v,j,w,m,n,sm,sn)"
          "atom m \<sharp> (t,u,v,j,w,n,sm,sn)"   "atom n \<sharp> (t,u,v,j,w,sm,sn)"
          "atom sm \<sharp> (t,u,v,j,w,sn)"   "atom sn \<sharp> (t,u,v,j,w)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: PrfP.simps [of l _ sl m n sm sn])
qed


subsection \<open>The predicate \<open>PfP\<close>\<close>

definition Pf :: "hf \<Rightarrow> bool"
  where "Pf y \<equiv> (\<exists>s k. Prf s k y)"

nominal_function PfP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom k \<sharp> (s,y); atom s \<sharp> y\<rbrakk> \<Longrightarrow>
    PfP y = Ex k (Ex s (PrfP (Var s) (Var k) y))"
  by (auto simp: eqvt_def PfP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows PfP_fresh_iff [simp]: "a \<sharp> PfP y \<longleftrightarrow> a \<sharp> y"           (is ?thesis1)
   and eval_fm_PfP [simp]:  "eval_fm e (PfP y) \<longleftrightarrow> Pf \<lbrakk>y\<rbrakk>e"  (is ?thesis2)
   and PfP_sf [iff]: "Sigma_fm (PfP y)"                      (is ?thsf)
proof -
  obtain k::name and s::name where "atom k \<sharp> (s,y)" "atom s \<sharp> y"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: Pf_def)
qed

lemma PfP_subst [simp]: "(PfP t)(j::=w) = PfP (subst j w t)"
proof -
  obtain k::name and s::name where "atom k \<sharp> (s,t,j,w)" "atom s \<sharp> (t,j,w)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: PfP.simps [of k s])
qed

lemma ground_PfP [simp]: "ground_fm (PfP y) = ground y"
  by (simp add: ground_aux_def ground_fm_aux_def supp_conv_fresh)


section\<open>Proposition 4.4\<close>

subsection\<open>Left-to-Right Proof\<close>

lemma extra_axiom_imp_Pf: "Pf \<lbrakk>\<lceil>extra_axiom\<rceil>\<rbrakk>e"
proof -
  have "\<lbrakk>\<lceil>extra_axiom\<rceil>\<rbrakk>e \<in> Extra_ax"
    by (simp add: Extra_ax_def) (rule eval_quot_fm_ignore)
  thus ?thesis
    by (force simp add: Pf_def Prf_def Axiom_def intro: BuildSeq_exI)
qed

lemma boolean_axioms_imp_Pf:
  assumes "\<alpha> \<in> boolean_axioms" shows "Pf \<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e"
proof -
  have "\<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e \<in> Sent" using assms
    by (rule boolean_axioms.cases)
       (auto simp: Sent_def Sent_axioms_def quot_Disj quot_Neg q_defs)
  thus ?thesis
    by (force simp add: Pf_def Prf_def Axiom_def intro: BuildSeq_exI)
qed

lemma equality_axioms_imp_Pf:
  assumes "\<alpha> \<in> equality_axioms" shows "Pf \<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e"
proof -
  have "\<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e \<in> Equality_ax" using assms [unfolded equality_axioms_def]
    by (auto simp: Equality_ax_def eval_quot_fm_ignore)
  thus ?thesis
    by (force simp add: Pf_def Prf_def Axiom_def intro: BuildSeq_exI)
qed

lemma HF_axioms_imp_Pf:
  assumes "\<alpha> \<in> HF_axioms" shows "Pf \<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e"
proof -
  have "\<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e \<in> HF_ax" using assms [unfolded HF_axioms_def]
    by (auto simp: HF_ax_def eval_quot_fm_ignore)
  thus ?thesis
    by (force simp add: Pf_def Prf_def Axiom_def intro: BuildSeq_exI)
qed

lemma special_axioms_imp_Pf:
  assumes "\<alpha> \<in> special_axioms" shows "Pf \<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e"
proof -
  have "\<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e \<in> Special_ax"
    by (metis special_axioms_into_Special_ax assms)
  thus ?thesis
    by (force simp add: Pf_def Prf_def Axiom_def intro: BuildSeq_exI)
qed

lemma induction_axioms_imp_Pf:
  assumes "\<alpha> \<in> induction_axioms" shows "Pf \<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e"
proof -
  have "\<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e \<in> Induction_ax"
    by (metis induction_axioms_into_Induction_ax assms)
  thus ?thesis
    by (force simp add: Pf_def Prf_def Axiom_def intro: BuildSeq_exI)
qed

lemma ModPon_imp_Pf: "\<lbrakk>Pf \<lbrakk>Q_Imp x y\<rbrakk>e; Pf \<lbrakk>x\<rbrakk>e\<rbrakk> \<Longrightarrow> Pf \<lbrakk>y\<rbrakk>e"
  by (auto simp: Pf_def Prf_def ModPon_def q_defs intro: BuildSeq_combine)

lemma quot_ModPon_imp_Pf: "\<lbrakk>Pf \<lbrakk>\<lceil>\<alpha> IMP \<beta>\<rceil>\<rbrakk>e; Pf \<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e\<rbrakk> \<Longrightarrow> Pf \<lbrakk>\<lceil>\<beta>\<rceil>\<rbrakk>e"
  by (simp add: ModPon_imp_Pf quot_fm_def quot_simps q_defs)

lemma quot_Exists_imp_Pf: "\<lbrakk>Pf \<lbrakk>\<lceil>\<alpha> IMP \<beta>\<rceil>\<rbrakk>e; atom i \<sharp> \<beta>\<rbrakk> \<Longrightarrow> Pf \<lbrakk>\<lceil>Ex i \<alpha> IMP \<beta>\<rceil>\<rbrakk>e"
  by (force simp: Pf_def Prf_def Exists_def quot_simps q_defs 
            intro: BuildSeq_combine AbstForm_trans_fm_eq fresh_imp_VarNonOccForm)

lemma proved_imp_Pf: assumes "H \<turnstile> \<alpha>" "H={}" shows "Pf \<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e"
using assms
proof (induct)
  case (Hyp A H) thus ?case
    by auto
next
  case (Extra H) thus ?case
    by (metis extra_axiom_imp_Pf)
next
  case (Bool A H) thus ?case
    by (metis boolean_axioms_imp_Pf)
next
  case (Eq A H) thus ?case
    by (metis equality_axioms_imp_Pf)
next
  case (HF A H) thus ?case
    by (metis HF_axioms_imp_Pf)
next
  case (Spec A H) thus ?case
    by (metis special_axioms_imp_Pf)
next
  case (Ind A H) thus ?case
    by (metis induction_axioms_imp_Pf)
next
  case (MP H A B H') thus ?case
    by (metis quot_ModPon_imp_Pf Un_empty)
next
  case (Exists H A B i) thus ?case
    by (metis quot_Exists_imp_Pf)
qed

corollary proved_imp_proved_PfP: "{} \<turnstile> \<alpha> \<Longrightarrow> {} \<turnstile> PfP \<lceil>\<alpha>\<rceil>"
  by (rule Sigma_fm_imp_thm [OF PfP_sf]) 
     (auto simp: ground_aux_def supp_conv_fresh proved_imp_Pf)

subsection\<open>Right-to-Left Proof\<close>

lemma Sent_imp_hfthm:
  assumes "x \<in> Sent" shows "\<exists>A. x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
proof -
  obtain y z w where "Form y" "Form z" "Form w" and axs: "Sent_axioms x y z w"
    using assms  by (auto simp: Sent_def)
  then obtain A::fm and B::fm and C::fm 
         where A: "y = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e" and B: "z = \<lbrakk>\<lceil>B\<rceil>\<rbrakk>e" and C: "w = \<lbrakk>\<lceil>C\<rceil>\<rbrakk>e"
    by (metis Form_imp_is_fm)
  have "\<exists>A. q_Imp y y = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
      by (force simp add: A quot_Disj quot_Neg q_defs hfthm.Bool boolean_axioms.intros)
  moreover have "\<exists>A. q_Imp y (q_Disj y z) = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
      by (force intro!: exI [where x="A IMP (A OR B)"]
                simp add: A B quot_Disj quot_Neg q_defs hfthm.Bool boolean_axioms.intros)
  moreover have "\<exists>A. q_Imp (q_Disj y y) y = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
      by (force intro!: exI [where x="(A OR A) IMP A"]
                simp add: A quot_Disj quot_Neg q_defs hfthm.Bool boolean_axioms.intros)
  moreover have "\<exists>A. q_Imp (q_Disj y (q_Disj z w)) (q_Disj (q_Disj y z) w) = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
      by (force intro!: exI [where x="(A OR (B OR C)) IMP ((A OR B) OR C)"]
                simp add: A B C quot_Disj quot_Neg q_defs hfthm.Bool boolean_axioms.intros)
  moreover have "\<exists>A. q_Imp (q_Disj y z) (q_Imp (q_Disj (q_Neg y) w) (q_Disj z w)) = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
      by (force intro!: exI [where x="(A OR B) IMP ((Neg A OR C) IMP (B OR C))"]
                simp add: A B C quot_Disj quot_Neg q_defs hfthm.Bool boolean_axioms.intros)
  ultimately show ?thesis using axs [unfolded Sent_axioms_def]
    by blast
qed

lemma Extra_ax_imp_hfthm:
  assumes "x \<in> Extra_ax" obtains A where "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
  using assms unfolding Extra_ax_def
  by (auto intro: eval_quot_fm_ignore hfthm.Extra)

lemma Equality_ax_imp_hfthm:
  assumes "x \<in> Equality_ax" obtains A where "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
  using assms unfolding Equality_ax_def
  by (auto intro: eval_quot_fm_ignore hfthm.Eq [unfolded equality_axioms_def])

lemma HF_ax_imp_hfthm:
  assumes "x \<in> HF_ax" obtains A where "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
  using assms unfolding HF_ax_def
  by (auto intro: eval_quot_fm_ignore hfthm.HF [unfolded HF_axioms_def])

lemma Special_ax_imp_hfthm:
  assumes "x \<in> Special_ax" obtains A where "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e" "{} \<turnstile> A"
  by (metis Spec Special_ax_imp_special_axioms assms)

lemma Induction_ax_imp_hfthm:
  assumes "x \<in> Induction_ax" obtains A where "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e" "{} \<turnstile> A"
  by (metis Induction_ax_imp_induction_axioms assms hfthm.Ind)

lemma Exists_imp_hfthm: "\<lbrakk>Exists \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e y; {} \<turnstile> A\<rbrakk> \<Longrightarrow> \<exists>B. y = \<lbrakk>\<lceil>B\<rceil>\<rbrakk>e \<and> {} \<turnstile> B"
  by (drule Exists_imp_exists [where e=e]) (auto intro: anti_deduction)

lemma Subst_imp_hfthm:  "\<lbrakk>Subst \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e y; {} \<turnstile> A\<rbrakk> \<Longrightarrow> \<exists>B. y = \<lbrakk>\<lceil>B\<rceil>\<rbrakk>e \<and> {} \<turnstile> B"
  by (drule Subst_imp_subst [where e=e], auto intro: Subst)

lemma eval_Neg_imp_Neg: "\<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e = q_Neg x \<Longrightarrow> \<exists>A. \<alpha> = Neg A \<and> \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e = x" 
  by (cases \<alpha> rule: fm.exhaust) (auto simp: quot_simps q_defs htuple_minus_1)

lemma eval_Disj_imp_Disj: "\<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e = q_Disj x y \<Longrightarrow> \<exists>A B. \<alpha> = A OR B \<and> \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e = x \<and> \<lbrakk>\<lceil>B\<rceil>\<rbrakk>e = y"
  by (cases \<alpha> rule: fm.exhaust) (auto simp: quot_simps q_defs htuple_minus_1)

lemma Prf_imp_proved: assumes "Prf s k x" shows "\<exists>A. x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> {} \<turnstile> A"
using assms [unfolded Prf_def Axiom_def]
proof (induction x rule: BuildSeq_induct)
  case (B x) thus ?case
    by (auto intro: Extra_ax_imp_hfthm Sent_imp_hfthm Equality_ax_imp_hfthm HF_ax_imp_hfthm
                    Special_ax_imp_hfthm Induction_ax_imp_hfthm)
next
  case (C x y z)
  then obtain A::fm and B::fm where "y = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e" "{} \<turnstile> A" "z = \<lbrakk>\<lceil>B\<rceil>\<rbrakk>e" "{} \<turnstile> B"
    by blast
  thus ?case using C.hyps ModPon_def q_Imp_def
    by (auto dest!: MP_same eval_Neg_imp_Neg eval_Disj_imp_Disj Exists_imp_hfthm Subst_imp_hfthm)
qed

corollary Pf_quot_imp_is_proved: "Pf \<lbrakk>\<lceil>\<alpha>\<rceil>\<rbrakk>e \<Longrightarrow> {} \<turnstile> \<alpha>"
  by (metis Pf_def Prf_imp_proved eval_fm_inject)

text\<open>Proposition 4.4!\<close>
theorem proved_iff_proved_PfP: "{} \<turnstile> \<alpha> \<longleftrightarrow> {} \<turnstile> PfP \<lceil>\<alpha>\<rceil>"
  by (metis Pf_quot_imp_is_proved emptyE eval_fm_PfP hfthm_sound proved_imp_proved_PfP)

end

