theory RelationalIncorrectness
  imports "HOL-IMP.Big_Step"
begin

(* Author: Toby Murray *)

section "Under-Approximate Relational Judgement"

text {*
  This is the relational analogue of OHearn's~\cite{OHearn_19} and de Vries \& Koutavas'~\cite{deVries_Koutavas_11}
  judgements.

  Note that in our case it doesn't really make sense to talk about ``erroneous'' states: the
  presence of an error can be seen only by the violation of a relation. Unlike O'Hearn, we cannot
  encode it directly into the semantics of our programs, without giving them a relational semantics.
  We use the standard big step semantics of IMP unchanged.
*}

type_synonym rassn = "state \<Rightarrow> state \<Rightarrow> bool"

definition 
  ir_valid :: "rassn \<Rightarrow> com \<Rightarrow> com \<Rightarrow> rassn \<Rightarrow> bool"
  where
  "ir_valid P c c' Q \<equiv> (\<forall> t t'. Q t t' \<longrightarrow> (\<exists>s s'. P s s' \<and> (c,s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t'))"


section "Rules of the Logic"

definition
  flip :: "rassn \<Rightarrow> rassn"
  where
  "flip P \<equiv> \<lambda>s s'. P s' s"


inductive
  ir_hoare :: "rassn \<Rightarrow> com \<Rightarrow> com \<Rightarrow> rassn \<Rightarrow> bool"
  where
  ir_Skip: "(\<And>t t'. Q t t' \<Longrightarrow> \<exists>s'. P t s' \<and> (c',s') \<Rightarrow> t') \<Longrightarrow>
            ir_hoare P SKIP c' Q" |
  ir_If_True:   "ir_hoare (\<lambda>s s'. P s s' \<and> bval b s) c\<^sub>1 c' Q \<Longrightarrow> 
                 ir_hoare P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) c' Q" |
  ir_If_False:   "ir_hoare (\<lambda>s s'. P s s' \<and> \<not> bval b s) c\<^sub>2 c' Q \<Longrightarrow> 
                  ir_hoare P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) c' Q" |
  ir_Seq1: "ir_hoare P c c' Q \<Longrightarrow> ir_hoare Q d SKIP R \<Longrightarrow> ir_hoare P (Seq c d) c' R" |
  ir_Assign: "ir_hoare (\<lambda>t t'. \<exists> v. P (t(x := v)) t' \<and> (t x) = aval e (t(x := v))) SKIP c' Q \<Longrightarrow>
              ir_hoare P (Assign x e) c' Q" |
  ir_While_False: "ir_hoare (\<lambda>s s'. P s s' \<and> \<not> bval b s) SKIP c' Q \<Longrightarrow>
                  ir_hoare P (WHILE b DO c) c' Q" |
  ir_While_True: "ir_hoare (\<lambda>s s'. P s s' \<and> bval b s) (c;; WHILE b DO c) c' Q \<Longrightarrow>
                  ir_hoare P (WHILE b DO c) c' Q" |
  ir_While_backwards_frontier: "(\<And>n. ir_hoare (\<lambda> s s'. P n s s' \<and> bval b s) c SKIP (P (Suc n))) \<Longrightarrow>
                                ir_hoare (\<lambda>s s'. \<exists>n. P n s s') (WHILE b DO c) c' Q \<Longrightarrow>
                                ir_hoare (P 0) (WHILE b DO c) c' Q" |
  ir_conseq:      "ir_hoare P c c' Q \<Longrightarrow> (\<And>s s'. P s s' \<Longrightarrow> P' s s') \<Longrightarrow> (\<And>s s'. Q' s s' \<Longrightarrow> Q s s') \<Longrightarrow>
                   ir_hoare P' c c' Q'" |
  ir_disj:        "ir_hoare P\<^sub>1 c c' Q\<^sub>1 \<Longrightarrow> ir_hoare P\<^sub>2 c c' Q\<^sub>2 \<Longrightarrow>
                   ir_hoare (\<lambda>s s'. P\<^sub>1 s s' \<or> P\<^sub>2 s s') c c' (\<lambda> t t'. Q\<^sub>1 t t' \<or> Q\<^sub>2 t t')" |
  ir_sym: "ir_hoare (flip P) c c' (flip Q) \<Longrightarrow> ir_hoare P c' c Q"

section "Simple Derived Rules"

lemma meh_simp[simp]: "(SKIP, s') \<Rightarrow> t' = (s' = t')"
  by auto


lemma ir_pre: "ir_hoare P c c' Q \<Longrightarrow> (\<And>s s'. P s s' \<Longrightarrow> P' s s')  \<Longrightarrow>
                  ir_hoare P' c c' Q"
  by(erule ir_conseq, blast+)

lemma ir_post: "ir_hoare P c c' Q \<Longrightarrow> (\<And>s s'. Q' s s' \<Longrightarrow> Q s s')  \<Longrightarrow>
                  ir_hoare P c c' Q'"
  by(erule ir_conseq, blast+)

section "Soundness"

lemma Skip_ir_valid[intro]:
  "(\<And>t t'. Q t t' \<Longrightarrow> \<exists>s'. P t s' \<and> (c', s') \<Rightarrow> t') \<Longrightarrow> ir_valid P SKIP c' Q"
  by(auto simp: ir_valid_def)

lemma sym_ir_valid[intro]:
  "ir_valid (flip P) c' c (flip Q) \<Longrightarrow> ir_valid P c c' Q"
  by(fastforce simp: ir_valid_def flip_def)

lemma If_True_ir_valid[intro]:
  "ir_valid (\<lambda>a c. P a c \<and> bval b a) c\<^sub>1 c' Q \<Longrightarrow>
   ir_valid P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) c' Q"
  by(fastforce simp: ir_valid_def)

lemma If_False_ir_valid[intro]:
  "ir_valid (\<lambda>a c. P a c \<and> \<not> bval b a) c\<^sub>2 c' Q \<Longrightarrow>
   ir_valid P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) c' Q"
  by(fastforce simp: ir_valid_def)

lemma Seq1_ir_valid[intro]:
  "ir_valid P c c' Q \<Longrightarrow> ir_valid Q d SKIP R \<Longrightarrow> ir_valid P (c;; d) c' R"
  by(fastforce simp: ir_valid_def)

lemma Seq2_ir_valid[intro]:
  "ir_valid P c SKIP Q \<Longrightarrow> ir_valid Q d c' R \<Longrightarrow> ir_valid P (c;; d) c' R"
  by(fastforce simp: ir_valid_def)

lemma Seq_ir_valid[intro]:
  "ir_valid P c c' Q \<Longrightarrow> ir_valid Q d d' R \<Longrightarrow> ir_valid P (c;; d) (c';; d') R"
  by(fastforce simp: ir_valid_def)

lemma Assign_blah[intro]:
  "t x = aval e (t(x := v))
       \<Longrightarrow> (x ::= e, t(x := v)) \<Rightarrow> t"
  using Assign 
  by (metis fun_upd_triv fun_upd_upd)

lemma Assign_ir_valid[intro]:
  "ir_valid (\<lambda>t t'. \<exists> v. P (t(x := v)) t' \<and> (t x) = aval e (t(x := v))) SKIP c' Q \<Longrightarrow> ir_valid P (Assign x e) c' Q"
  by(fastforce simp: ir_valid_def)

lemma While_False_ir_valid[intro]:
  "ir_valid (\<lambda>s s'. P s s' \<and> \<not> bval b s) SKIP c' Q \<Longrightarrow>
   ir_valid P (WHILE b DO c) c' Q"
  by(fastforce simp: ir_valid_def)

lemma While_True_ir_valid[intro]:
  "ir_valid (\<lambda>s s'. P s s' \<and> bval b s) (Seq c (WHILE b DO c)) c' Q \<Longrightarrow>
   ir_valid P (WHILE b DO c) c' Q"
  by(clarsimp simp: ir_valid_def, blast)


lemma While_backwards_frontier_ir_valid':
  assumes asm: "\<And>n. \<forall>t t'. P (k + Suc n) t t' \<longrightarrow>
                    (\<exists>s. P (k + n) s t' \<and> bval b s \<and> (c, s) \<Rightarrow> t)"
  assumes last: "\<forall>t t'. Q t t' \<longrightarrow> (\<exists>s s'. (\<exists>n. P (k + n) s s') \<and> (WHILE b DO c, s) \<Rightarrow> t \<and> (c', s') \<Rightarrow> t')"
  assumes post: "Q t t'"
  shows "\<exists>s s'. P k s s' \<and> (WHILE b DO c, s) \<Rightarrow> t \<and> (c', s') \<Rightarrow> t'"
proof -
  from post last obtain s s' n where 
    "P (k + n) s s'" "(WHILE b DO c, s) \<Rightarrow> t" "(c', s') \<Rightarrow> t'"
    by blast
  with asm  show ?thesis
  proof(induction n arbitrary: k t t')
    case 0 
    then show ?case 
      by (metis WhileFalse WhileTrue add.right_neutral)
  next
    case (Suc n)
    from Suc
    obtain r r' where final_iteration: "P (Suc k) r r'" "(WHILE b DO c, r) \<Rightarrow> t" "(c', r') \<Rightarrow> t'"
      by (metis add_Suc_shift)
    from final_iteration(1) obtain q q' where
     "P k q r' \<and> bval b q \<and>  (c, q) \<Rightarrow> r" 
      by (metis Nat.add_0_right Suc.prems(1) plus_1_eq_Suc semiring_normalization_rules(24))
    with final_iteration show ?case by blast
  qed
qed


lemma While_backwards_frontier_ir_valid[intro]:
  "(\<And>n. ir_valid (\<lambda> s s'. P n s s' \<and> bval b s) c SKIP (P (Suc n))) \<Longrightarrow>
   ir_valid (\<lambda>s s'. \<exists>n. P n s s') (WHILE b DO c) c' Q \<Longrightarrow>
   ir_valid (P 0) (WHILE b DO c) c' Q"
  by(auto simp: meh_simp ir_valid_def intro: While_backwards_frontier_ir_valid')

lemma conseq_ir_valid:
  "ir_valid P c c' Q \<Longrightarrow> (\<And>s s'. P s s' \<Longrightarrow> P' s s') \<Longrightarrow> (\<And>s s'. Q' s s' \<Longrightarrow> Q s s') \<Longrightarrow>
                  ir_valid P' c c' Q'"
  by(clarsimp simp: ir_valid_def, blast)

lemma disj_ir_valid[intro]:
  "ir_valid P\<^sub>1 c c' Q\<^sub>1 \<Longrightarrow> ir_valid P\<^sub>2 c c' Q\<^sub>2 \<Longrightarrow>
                  ir_valid (\<lambda>s s'. P\<^sub>1 s s' \<or> P\<^sub>2 s s') c c' (\<lambda> t t'. Q\<^sub>1 t t' \<or> Q\<^sub>2 t t')"
  by(fastforce simp: ir_valid_def)


theorem soundness:
  "ir_hoare P c c' Q \<Longrightarrow> ir_valid P c c' Q"
  apply(induction rule: ir_hoare.induct)
              apply(blast intro!: Skip_ir_valid)
  by (blast intro: conseq_ir_valid)+

section "Completeness"

lemma ir_Skip_Skip[intro]:
  "ir_hoare P SKIP SKIP P"
  by(rule ir_Skip, simp)

lemma ir_hoare_Skip_Skip[simp]:
  "ir_hoare P SKIP SKIP Q = (\<forall>s s'. Q s s' \<longrightarrow> P s s')"
  using soundness ir_valid_def meh_simp ir_conseq ir_Skip by metis

lemma ir_valid_Seq1:
  "ir_valid P (c1;; c2) c' Q \<Longrightarrow> ir_valid P c1 c' (\<lambda>t t'. \<exists>s s'. P s s' \<and> (c1,s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t' \<and> (\<exists>u. (c2,t) \<Rightarrow> u \<and> Q u t'))"
  by(auto simp: ir_valid_def)

lemma ir_valid_Seq1':
  "ir_valid P (c1;; c2) c' Q \<Longrightarrow> ir_valid (\<lambda>t t'. \<exists>s s'. P s s' \<and> (c1,s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t' \<and> (\<exists>u. (c2,t) \<Rightarrow> u \<and> Q u t')) c2 SKIP Q"
  by(clarsimp simp: ir_valid_def, meson SeqE)

lemma ir_valid_track_history:
  "ir_valid P c c' Q \<Longrightarrow>
   ir_valid P c c' (\<lambda>t t'. Q s s' \<and> (\<exists>s s'. P s s' \<and> (c,s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t'))"
  by(auto simp: ir_valid_def)

lemma ir_valid_If:
  "ir_valid (\<lambda>s s'. P s s') (IF b THEN c1 ELSE c2) c' Q \<Longrightarrow>
   ir_valid (\<lambda>s s'. P s s' \<and> bval b s) c1 c' (\<lambda>t t'. Q t t' \<and> (\<exists>s s'. P s s' \<and> (c1,s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t' \<and> bval b s)) \<and>
   ir_valid (\<lambda>s s'. P s s' \<and> \<not> bval b s) c2 c' (\<lambda>t t'. Q t t' \<and> (\<exists>s s'. P s s' \<and> (c2,s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t' \<and> \<not> bval b s))"
  by(clarsimp simp: ir_valid_def, blast)

text {*
  Inspired by the 
  ``@{text "p(n) = {\<sigma> | you can get back from \<sigma> to some state in p by executing C backwards n times}"}''
  part of OHearn~\cite{OHearn_19}.
*}
primrec get_back where
  "get_back P b c 0 = (\<lambda>t t'. P t t')" |
  "get_back P b c (Suc n) = (\<lambda>t t'. \<exists>s. (c,s) \<Rightarrow> t \<and> bval b s \<and> get_back P b c n s t')"

(* Currently not used anywhere *)
lemma ir_valid_get_back:
  "ir_valid (get_back P b c (Suc k)) (WHILE b DO c) c' Q \<Longrightarrow>
   ir_valid (get_back P b c k) (WHILE b DO c) c' Q"
proof(induct k)
  case 0
  then show ?case by(clarsimp simp: ir_valid_def, blast)
next
  case (Suc k)
  then show ?case  using  WhileTrue get_back.simps(2) ir_valid_def by smt 
qed

(* both this an the next one get used in the completeness proof *)
lemma ir_valid_While1:
  "ir_valid (get_back P b c k) (WHILE b DO c) c' Q \<Longrightarrow>
   (ir_valid (\<lambda>s s'. get_back P b c k s s' \<and> bval b s) c SKIP (\<lambda>t t'. get_back P b c (Suc k) t t' \<and> (\<exists>u u'. (WHILE b DO c,t) \<Rightarrow> u \<and> (c',t') \<Rightarrow> u' \<and> Q u u')))"
proof (subst ir_valid_def, clarsimp)
  fix t t' s u u'
  assume "ir_valid (get_back P b c k) (WHILE b DO c) c' Q" 
         "(WHILE b DO c, t) \<Rightarrow> u"
         "(c, s) \<Rightarrow> t" 
         "(c', t') \<Rightarrow> u'"
         "Q u u'"
         "bval b s"
         "get_back P b c k s t'"
  thus "\<exists>s. get_back P b c k s t' \<and> bval b s \<and> (c, s) \<Rightarrow> t"
  proof(induction k arbitrary: t t' s u u')
    case 0
    then show ?case 
      by auto
  next
    case (Suc k)
    show ?case
      using Suc.prems(3) Suc.prems(6) Suc.prems(7) by blast
  qed
qed

lemma ir_valid_While3:
  "ir_valid (get_back P b c k) (WHILE b DO c) c' Q \<Longrightarrow>
   (ir_valid (\<lambda>s s'. get_back P b c k s s' \<and> bval b s) c c' (\<lambda>t t'. (\<exists>s'. (c',s') \<Rightarrow> t' \<and> get_back P b c (Suc k) t s' \<and> (\<exists>u. (WHILE b DO c,t) \<Rightarrow> u \<and>  Q u t'))))"
  apply(subst ir_valid_def, clarsimp)
proof -
  fix t t' s' s u
  assume "ir_valid (get_back P b c k) (WHILE b DO c) c' Q" 
         "(WHILE b DO c, t) \<Rightarrow> u"
         "(c, s) \<Rightarrow> t" 
         "(c', s') \<Rightarrow> t'"
         "Q u t'"
         "bval b s"
         "get_back P b c k s s'"
  thus "\<exists>s s'. get_back P b c k s s' \<and> bval b s \<and> (c, s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t'"
  proof(induction k arbitrary: t t' s' s u)
    case 0
    then show ?case 
      by auto
  next
    case (Suc k)
    show ?case
      using Suc.prems(3) Suc.prems(4) Suc.prems(6) Suc.prems(7) by blast
  qed
qed

(* not used anywhere *)
lemma ir_valid_While2:
   "ir_valid P (WHILE b DO c) c' Q \<Longrightarrow>
   ir_valid (\<lambda>s s'. P s s' \<and> \<not> bval b s) SKIP c' (\<lambda>t t'. Q t t' \<and> (\<exists>s'. (c',s') \<Rightarrow> t' \<and> P t s' \<and> \<not> bval b t))"  
  by(clarsimp simp: ir_valid_def, blast)

lemma assign_upd_blah:
  "(\<lambda>a. if a = x1 then s x1 else (s(x1 := aval x2 s)) a) = s"
  by(rule ext, auto)

lemma Assign_complete:
  assumes v: "ir_valid P (x1 ::= x2) c' Q"
  assumes q: "Q t t'"
  shows  "\<exists>s'. (\<exists>v. P (t(x1 := v)) s' \<and> t x1 = aval x2 (t(x1 := v))) \<and> (c', s') \<Rightarrow> t'"
proof -
  from v and q obtain s s' where a: "P s s' \<and> (x1 ::= x2,s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t'"
    using ir_valid_def by smt
  hence "P (\<lambda>a. if a = x1 then s x1 else (s(x1 := aval x2 s)) a) s' \<and> aval x2 s = aval x2 (s(x1 := s x1))"
    using assign_upd_blah 
    by simp
  thus ?thesis 
    using assign_upd_blah a 
    by (metis AssignE fun_upd_same fun_upd_triv fun_upd_upd)
qed

lemmas ir_Skip_sym = ir_sym[OF ir_Skip, simplified flip_def]

theorem completeness:
  "ir_valid P c c' Q \<Longrightarrow> ir_hoare P c c' Q"
proof(induct c arbitrary: P c' Q)
case SKIP
  show ?case 
    apply(rule ir_Skip)
    using SKIP by(fastforce simp: ir_valid_def)
next
  case (Assign x1 x2)
  show ?case
    apply(rule ir_Assign)
    apply(rule ir_Skip)
    using Assign_complete Assign by blast
next
  case (Seq c1 c2)
  have a: "ir_hoare P c1 c' (\<lambda>t t'. \<exists>s s'. P s s' \<and> (c1, s) \<Rightarrow> t \<and> (c', s') \<Rightarrow> t' \<and> (\<exists>u. (c2, t) \<Rightarrow> u \<and> Q u t'))"
    using ir_valid_Seq1 Seq by blast
  show ?case 
    apply(rule ir_Seq1)
     apply (blast intro: a)
    apply(rule ir_Skip_sym)
    by(metis SeqE ir_valid_def Seq)
next
  case (If x1 c1 c2)
  have t: "ir_hoare (\<lambda>s s'. P s s' \<and> bval x1 s) c1 c'
      (\<lambda>t t'. Q t t' \<and> (\<exists>s s'. P s s' \<and> (c1, s) \<Rightarrow> t \<and> (c', s') \<Rightarrow> t' \<and> bval x1 s))" and
       f: " ir_hoare (\<lambda>s s'. P s s' \<and> \<not> bval x1 s) c2 c'
      (\<lambda>t t'. Q t t' \<and> (\<exists>s s'. P s s' \<and> (c2, s) \<Rightarrow> t \<and> (c', s') \<Rightarrow> t' \<and> \<not> bval x1 s))"
    using ir_valid_If If by blast+
  show ?case 
    (* consider both cases of the if via conseq, disj, then _True and _False *)
    apply(rule ir_conseq)
      apply(rule ir_disj)
       apply(rule ir_If_True,fastforce intro: t)
      apply(rule ir_If_False, fastforce intro: f)    
     apply blast
    by (smt IfE ir_valid_def If)
next
  case (While x1 c)
  have a: "\<And>n. ir_hoare (\<lambda>s s'. get_back P x1 c n s s' \<and> bval x1 s) c SKIP (get_back P x1 c (Suc n))"
    using ir_valid_While1  While
    by (smt get_back.simps(2) ir_valid_def meh_simp)
  have b: "ir_hoare (\<lambda>s s'. P s s' \<and> bval x1 s) c c'
                    (\<lambda>t t'.  \<exists>s'. (c', s') \<Rightarrow> t' \<and> (\<exists>s. (c, s) \<Rightarrow> t \<and> bval x1 s \<and> P s s') \<and> 
                    (\<exists>u. (WHILE x1 DO c, t) \<Rightarrow> u \<and> Q u t'))"
    using ir_valid_While3[where k=0,simplified] While by blast
  have gb: "\<And>t t'. Q t t' \<and> (\<exists>s'. (c', s') \<Rightarrow> t' \<and> P t s' \<and> \<not> bval x1 t) \<Longrightarrow>
                    \<exists>s'. ((\<exists>n. get_back P x1 c n t s') \<and> \<not> bval x1 t) \<and> (c', s') \<Rightarrow> t'"
    by (meson get_back.simps(1))
  
  show ?case 
    (* use the frontier rule much as in OHearn POPL *)
    apply(rule ir_conseq)
      apply(rule_tac P="get_back P x1 c" in ir_While_backwards_frontier)
       apply(blast intro: a)
      (* consider both cases of the While via conseq, disj, then _True and _False *)
      apply(rule ir_conseq)
        apply(rule ir_disj)
         apply(rule_tac P="\<lambda>s s'. \<exists>n. get_back P x1 c n s s'" and Q="(\<lambda>t t'. Q t t' \<and> (\<exists>s'. (c', s') \<Rightarrow> t' \<and> P t s' \<and> \<not> bval x1 t))" in ir_While_False)
         apply(rule ir_Skip, blast intro: gb)
        apply(rule ir_While_True)
        apply(rule ir_Seq1[OF b])
        apply(rule ir_Skip_sym)
        apply(fastforce)
       apply (metis get_back.simps(1))
      apply assumption
     apply simp
    by (metis While.prems WhileE ir_valid_def)
qed




section "A Decomposition Principle: Proofs via Under-Approximate Hoare Logic"

text {*
  We show the under-approximate analogue holds for Beringer's~\cite{Beringer_11} decomposition
  principle for over-approximate relational logic.
*}


definition
  decomp :: "rassn \<Rightarrow> com \<Rightarrow> com \<Rightarrow> rassn \<Rightarrow> rassn" where
  "decomp P c c' Q \<equiv> \<lambda>t s'. \<exists>s t'. P s s' \<and> (c,s) \<Rightarrow> t \<and> (c',s') \<Rightarrow> t' \<and> Q t t'"


lemma ir_valid_decomp1:
  "ir_valid P c c' Q \<Longrightarrow> ir_valid P c SKIP (decomp P c c' Q) \<and> ir_valid (decomp P c c' Q) SKIP c' Q"
  by(fastforce simp: ir_valid_def meh_simp decomp_def)

lemma ir_valid_decomp2:
  "ir_valid P c SKIP R \<and> ir_valid R SKIP c' Q \<Longrightarrow> ir_valid P c c' Q"
  by(fastforce simp: ir_valid_def meh_simp decomp_def)

lemma ir_valid_decomp:
  "ir_valid P c c' Q = (ir_valid P c SKIP (decomp P c c' Q) \<and> ir_valid (decomp P c c' Q) SKIP c' Q)"
  using ir_valid_decomp1 ir_valid_decomp2 by blast

text {*
  Completeness with soundness means we can prove proof rules about @{term ir_hoare} in terms
  of @{term ir_valid}.
*}

lemma ir_to_Skip:     
  "ir_hoare P c c' Q = (ir_hoare P c SKIP (decomp P c c' Q) \<and> ir_hoare (decomp P c c' Q) SKIP c' Q)"
  using soundness completeness ir_valid_decomp 
  by meson

text {*
  O'Hearn's under-approximate Hoare triple, for the ``ok'' case (since that is the only case we have)
  This is also likely the same as from the "Reverse Hoare Logic" paper (SEFM).
*}
type_synonym assn = "state \<Rightarrow> bool"
definition
  ohearn :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool"
  where
  "ohearn P c Q \<equiv> (\<forall>t. Q t \<longrightarrow> (\<exists>s. P s \<and> (c,s) \<Rightarrow> t))"

lemma fold_ohearn1:
  "ir_valid P c SKIP Q = (\<forall>t'. ohearn (\<lambda>t. P t t') c (\<lambda>t. Q t t'))"
  by(fastforce simp add: ir_valid_def ohearn_def)

lemma fold_ohearn2:
  "ir_valid P SKIP c' Q = (\<forall>t. ohearn (P t) c' (Q t))"
  by(simp add: ir_valid_def ohearn_def)

theorem relational_via_hoare:
  "ir_hoare P c c' Q = ((\<forall>t'. ohearn (\<lambda>t. P t t') c (\<lambda>t. decomp P c c' Q t t')) \<and> (\<forall>t. ohearn (decomp P c c' Q t) c' (Q t)))"
proof -
  have a: "\<And>P c c' Q. ir_hoare P c c' Q = ir_valid P c c' Q"
    using soundness completeness by auto
  show ?thesis
    using ir_to_Skip a fold_ohearn1 fold_ohearn2 by metis
qed

section "Deriving Proof Rules from Completeness"

text {*
  Note that we can more easily derive proof rules sometimes by appealing to the
   corresponding properties of @{term ir_valid} than from the proof rules directly.

  We see more examples of this later on when we consider examples.
*}

lemma ir_Seq2: 
  "ir_hoare P c SKIP Q \<Longrightarrow> ir_hoare Q d c' R \<Longrightarrow> ir_hoare P (Seq c d) c' R"
  using soundness completeness Seq2_ir_valid by metis

lemma ir_Seq: 
  "ir_hoare P c c' Q \<Longrightarrow> ir_hoare Q d d' R \<Longrightarrow> ir_hoare P (Seq c d) (Seq c' d') R"
  using soundness completeness Seq_ir_valid by metis

section "Examples"

subsection "Some Derived Proof Rules"

text {* 
First derive some proof rules -- here not by appealing to completeness but just using
the existing rules 
*}

lemma ir_If_True_False:   
  "ir_hoare (\<lambda>s s'. P s s' \<and> bval b s \<and> \<not> bval b' s') c\<^sub>1 c\<^sub>2' Q \<Longrightarrow> 
   ir_hoare P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (IF b' THEN c\<^sub>1' ELSE c\<^sub>2') Q"
  apply(rule ir_If_True)
  apply(rule ir_sym)
  apply(rule ir_If_False)
  apply(rule ir_sym)
  by(simp add: flip_def)


lemma ir_Assign_Assign:
  "ir_hoare P (x ::= e) (x' ::= e') (\<lambda>t t'. \<exists>v v'. P (t(x := v)) (t'(x' := v')) \<and> t x = aval e (t(x := v)) \<and> t' x' = aval e' (t'(x' := v')))"
  apply(rule ir_Assign)
  apply(rule ir_sym)
  apply(rule ir_Assign)
  by(simp add: flip_def, auto)

subsection "prog1"

text {*
  A tiny insecure program. Note that we only need to reason on one path through this program to
  detect that it is insecure. 
*}

abbreviation low_eq :: rassn where "low_eq s s' \<equiv> s ''low'' = s' ''low''"
abbreviation low_neq :: rassn where "low_neq s s' \<equiv> \<not> low_eq s s'"
definition prog1 :: com where
  "prog1 \<equiv> (IF (Less (N 0) (V ''x'')) THEN (Assign ''low'' (N 1)) ELSE (Assign ''low'' (N 0)))"

text {* 
  We prove that @{term prog1} is definitely insecure. To do that, we need to find some non-empty
  post-relation that implies insecurity. The following property encodes the idea that the 
  post-relation is non-empty, i.e. represents a feasible pair of execution paths.
*}
definition
  nontrivial :: "rassn \<Rightarrow> bool"
  where
  "nontrivial Q \<equiv> (\<exists>t t'. Q t t')"

text {*
  Note the property we prove here explicitly encodes the fact that the postcondition can be anything
  that implies insecurity, i.e. implies @{term low_neq}. In particular we should not necessarily
  expect it to cover the entirely of all states that satisfy @{term low_neq}. 

  Also note that we also have to prove that the postcondition is non-trivial. This is necessary to 
  make sure that the violation we find is not an infeasible path.
*}
lemma prog1:
  "\<exists>Q. ir_hoare low_eq prog1 prog1 Q \<and> (\<forall>s s'. Q s s' \<longrightarrow> low_neq s s') \<and> nontrivial Q"
  apply(rule exI)
  apply(rule conjI)
   apply(simp add: prog1_def)
   apply(rule ir_If_True_False)
   apply(rule ir_Assign_Assign)
  apply(rule conjI)
   apply auto[1]
  apply(clarsimp simp: nontrivial_def)
  apply(rule_tac x="\<lambda>v. 1" in exI)
  apply simp
  apply(rule_tac x="\<lambda>v. 0" in exI)
  by auto

subsection "More Derived Proof Rules for Examples"

definition BEq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
  "BEq a b \<equiv> And (Less a (Plus b (N 1))) (Less b (Plus a (N 1)))"


lemma BEq_aval[simp]: 
  "bval (BEq a b) s = ((aval a s) = (aval b s))"
  by(auto simp add: BEq_def)

lemma ir_If_True_True:
  "ir_hoare (\<lambda>s s'. P s s' \<and> bval b s \<and> bval b' s') c\<^sub>1 c\<^sub>1' Q\<^sub>1 \<Longrightarrow>
   ir_hoare P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (IF b' THEN c\<^sub>1' ELSE c\<^sub>2') (\<lambda>t t'. Q\<^sub>1 t t')"
  by(simp add: ir_If_True ir_sym flip_def)

lemma ir_If_False_False:
  "ir_hoare (\<lambda>s s'. P s s' \<and> \<not> bval b s \<and> \<not> bval b' s') c\<^sub>2 c\<^sub>2' Q\<^sub>2 \<Longrightarrow>
   ir_hoare P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (IF b' THEN c\<^sub>1' ELSE c\<^sub>2') (\<lambda>t t'. Q\<^sub>2 t t')"
  by(simp add: ir_If_False ir_sym flip_def)

lemma ir_If':
  "ir_hoare (\<lambda>s s'. P s s' \<and> bval b s \<and> bval b' s') c\<^sub>1 c\<^sub>1' Q\<^sub>1 \<Longrightarrow>
   ir_hoare (\<lambda>s s'. P s s' \<and> \<not> bval b s \<and> \<not> bval b' s') c\<^sub>2 c\<^sub>2' Q\<^sub>2 \<Longrightarrow>
   ir_hoare P (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (IF b' THEN c\<^sub>1' ELSE c\<^sub>2') (\<lambda>t t'. Q\<^sub>1 t t' \<or> Q\<^sub>2 t t')"
  apply(rule ir_pre)
   apply(rule ir_disj)
    apply(rule ir_If_True_True)
    apply assumption
   apply(rule ir_If_False_False)
   apply assumption
  apply blast
  done

lemma ir_While_triv:
  "ir_hoare (\<lambda>s s'. P s s' \<and> \<not> bval b s \<and> \<not> bval b' s') SKIP SKIP Q\<^sub>2 \<Longrightarrow>
   ir_hoare P (WHILE b DO c) (WHILE b' DO c') (\<lambda>s s'. (Q\<^sub>2 s s'))"
  by(simp add: ir_While_False ir_sym flip_def)

lemma ir_While':
  "ir_hoare (\<lambda>s s'. P s s' \<and> bval b s \<and> bval b' s') (c;;WHILE b DO c) (c';;WHILE b' DO c') Q\<^sub>1 \<Longrightarrow>
   ir_hoare (\<lambda>s s'. P s s' \<and> \<not> bval b s \<and> \<not> bval b' s') SKIP SKIP Q\<^sub>2 \<Longrightarrow>
   ir_hoare P (WHILE b DO c) (WHILE b' DO c') (\<lambda>s s'. (Q\<^sub>1 s s' \<or> Q\<^sub>2 s s'))"
  apply(rule ir_pre)
   apply(rule ir_disj)
     apply(rule ir_While_True)
     apply(rule ir_sym)
     apply(simp add: flip_def)
     apply(rule ir_While_True)
     apply(rule ir_sym)
    apply(simp add: flip_def)
   apply(rule ir_While_triv)
   apply assumption
  apply simp
  done 

subsection "client0"   

definition low_eq_strong where
  "low_eq_strong s s' \<equiv> (s ''high'' \<noteq> s' ''high'') \<and> low_eq s s'"

lemma low_eq_strong_upd[simp]:
  "var \<noteq> ''high'' \<and> var \<noteq> ''low'' \<Longrightarrow> low_eq_strong(s(var := v)) (s'(var := v')) = low_eq_strong s s'"
  by(auto simp: low_eq_strong_def)

text {*
  A variation on client0 from O'Hearn~\cite{OHearn_19}: how to reason about loops via a single unfolding
*}
definition client0 :: com where
  "client0 \<equiv> (Assign ''x'' (N 0);;
              (While (Less (N 0) (V ''n''))
                     ((Assign ''x'' (Plus (V ''x'') (V ''n'')));;
                      (Assign ''n'' (V ''nondet''))));;
              (If (BEq (V ''x'') (N 2000000)) (Assign ''low'' (V ''high'')) SKIP))"



lemma client0:
  "\<exists>Q. ir_hoare low_eq client0 client0 Q \<and> (\<forall>s s'. Q s s' \<longrightarrow> low_neq s s') \<and> nontrivial Q"
  apply(rule exI, rule conjI, simp add: client0_def)
   apply(rule_tac P=low_eq_strong in ir_pre)  
   apply(rule ir_Seq)
    apply(rule ir_Seq)
      apply(rule ir_Assign_Assign)
     apply clarsimp

    apply(rule ir_While')
      apply clarsimp

      apply(rule ir_Seq)
       apply(rule ir_Seq)
        apply(rule ir_Assign_Assign)
       apply(rule ir_Assign_Assign)
      apply clarsimp

      apply(rule ir_While_triv)
      apply clarsimp
      apply assumption

     apply clarsimp
     apply assumption


    apply(rule ir_If_True_True)
    apply(rule ir_Assign_Assign)
   apply(fastforce simp: low_eq_strong_def)
  apply(rule conjI)
   apply(clarsimp simp: low_eq_strong_def split: if_splits)

  (* ugh having to manually do constraint solving here... *)
  apply(clarsimp simp: low_eq_strong_def nontrivial_def)
  apply(rule_tac x="\<lambda>v. if v = ''x'' then 2000000 else if v = ''high'' then 1 else if v = ''n'' then -1 else if v = ''nondet'' then -1 else if v = ''low'' then 1 else undefined" in exI)
  apply(rule_tac x="\<lambda>v. if v = ''x'' then 2000000 else if v = ''high'' then 0 else if v = ''n'' then -1 else if v = ''nondet'' then -1 else if v = ''low'' then 0 else undefined" in exI)
  apply clarsimp
  done

(* Not needed? *)
lemma ir_While_backwards:
  "(\<And>n. ir_hoare (\<lambda> s s'. P n s s' \<and> bval b s) c SKIP (P (Suc n))) \<Longrightarrow>
                       ir_hoare (\<lambda>s s'. \<exists>n. P n s s' \<and> \<not> bval b s) SKIP c' Q \<Longrightarrow>
                       ir_hoare (P 0) (WHILE b DO c) c' Q"
  apply(rule ir_While_backwards_frontier)
   apply assumption
  apply(rule ir_While_False)
  apply auto
  done

subsection "Derive a variant of the backwards variant rule"

text {* Here we appeal to completeness again to derive this rule from the corresponding
        property about @{term ir_valid}. *}

subsection "A variant of the frontier rule"

text {*
  Agin we derive this rule by appealing to completeness and the corresponding property of
  @{term ir_valid}
*}

lemma While_backwards_frontier_both_ir_valid':
  assumes asm: "\<And>n. \<forall>t t'. P (k + Suc n) t t' \<longrightarrow>
                    (\<exists>s s'. P (k + n) s s' \<and> bval b s \<and> bval b' s' \<and> (c, s) \<Rightarrow> t \<and> (c', s') \<Rightarrow> t')"
  assumes last: "\<forall>t t'. Q t t' \<longrightarrow> (\<exists>s s'. (\<exists>n. P (k + n) s s') \<and> (WHILE b DO c, s) \<Rightarrow> t \<and> (WHILE b' DO c', s') \<Rightarrow> t')"
  assumes post: "Q t t'"
  shows "\<exists>s s'. P k s s' \<and> (WHILE b DO c, s) \<Rightarrow> t \<and> (WHILE b' DO c', s') \<Rightarrow> t'"
proof -
  from post last obtain s s' n where 
    "P (k + n) s s'" "(WHILE b DO c, s) \<Rightarrow> t" "(WHILE b' DO c', s') \<Rightarrow> t'"
    by blast
  with asm  show ?thesis
  proof(induction n arbitrary: k t t')
    case 0 
    then show ?case 
      by (metis WhileFalse WhileTrue add.right_neutral)
  next
    case (Suc n)
    from Suc
    obtain r r' where final_iteration: "P (Suc k) r r'" "(WHILE b DO c, r) \<Rightarrow> t" "(WHILE b' DO c', r') \<Rightarrow> t'"
      by (metis add_Suc_shift)
    from final_iteration(1) obtain q q' where
     "P k q q' \<and> bval b q \<and> bval b' q' \<and> (c, q) \<Rightarrow> r \<and> (c', q') \<Rightarrow> r'" 
      by (metis Nat.add_0_right Suc.prems(1) plus_1_eq_Suc semiring_normalization_rules(24))
    with final_iteration show ?case by blast
  qed
qed

lemma While_backwards_frontier_both_ir_valid[intro]:
  "(\<And>n. ir_valid (\<lambda> s s'. P n s s' \<and> bval b s \<and> bval b' s') c c' (P (Suc n))) \<Longrightarrow>
   ir_valid (\<lambda>s s'. \<exists>n. P n s s') (WHILE b DO c) (WHILE b' DO c') Q \<Longrightarrow>
   ir_valid (P 0) (WHILE b DO c) (WHILE b' DO c') (\<lambda>s s'. Q s s')"
  by(auto simp: ir_valid_def intro: While_backwards_frontier_both_ir_valid')

lemma ir_While_backwards_frontier_both:
  "\<lbrakk>\<And>n. ir_hoare (\<lambda>s s'. P n s s' \<and> bval b s \<and> bval b' s') c c' (P (Suc n));
   ir_hoare (\<lambda>s s'. \<exists>n. P n s s') (WHILE b DO c) (WHILE b' DO c') Q\<rbrakk>
   \<Longrightarrow> ir_hoare (P 0) (WHILE b DO c) (WHILE b' DO c') (\<lambda>s s'. Q s s')"
  using soundness completeness While_backwards_frontier_both_ir_valid by auto

text {*
  The following rule then follows easily as a special case
*}
lemma ir_While_backwards_both:
  "(\<And>n. ir_hoare (\<lambda> s s'. P n s s' \<and> bval b s \<and> bval b' s') c c' (P (Suc n))) \<Longrightarrow>
                       ir_hoare (P 0) (WHILE b DO c) (WHILE b' DO c') (\<lambda>s s'. \<exists>n. P n s s' \<and> \<not> bval b s \<and> \<not> bval b' s')"
  apply(rule ir_While_backwards_frontier_both)
   apply blast
  by(simp add: ir_While_False ir_sym flip_def)


subsection "client1"


text {*
  An example roughly equivalent to cient1 from O'Hearn~\cite{OHearn_19}0 

  In particular we use the backwards variant rule to reason about the loop.
*}
definition client1 :: com where
  "client1 \<equiv> (Assign ''x'' (N 0);;
              (While (Less (V ''x'') (V ''n''))
                     ((Assign ''x'' (Plus (V ''x'') (N 1)))));;
              (If (BEq (V ''x'') (N 2000000)) (Assign ''low'' (V ''high'')) SKIP))"


lemma client1:
  "\<exists>Q. ir_hoare low_eq client1 client1 Q \<and> (\<forall>s s'. Q s s' \<longrightarrow> low_neq s s') \<and> nontrivial Q"
  apply(rule exI, rule conjI, simp add: client1_def)
   apply(rule_tac P=low_eq_strong in ir_pre)  
   apply(rule ir_Seq)
    apply(rule ir_Seq)
      apply(rule ir_Assign_Assign)
     apply clarsimp

  apply(rule ir_pre)
      apply(rule ir_While_backwards_both[where P="\<lambda>n s s'. low_eq_strong s s' \<and> s ''x'' = int n \<and> s' ''x'' = int n \<and> int n \<le> s ''n'' \<and> int n \<le> s' ''n''"])
      apply(rule ir_post)
       apply(rule ir_Assign_Assign)
      apply clarsimp
  
     apply clarsimp

    apply(rule ir_If_True_True)
    apply(rule ir_Assign_Assign)
   apply(fastforce simp: low_eq_strong_def)
  apply(rule conjI)
   apply(clarsimp simp: low_eq_strong_def split: if_splits)

  apply clarsimp
  (* ugh having to manually do constraint solving here... *)
  apply(clarsimp simp: low_eq_strong_def nontrivial_def)
  apply(rule_tac x="\<lambda>v. if v = ''x'' then 2000000 else if v = ''high'' then 1 else if v = ''n'' then 2000000 else if v = ''nondet'' then -1 else if v = ''low'' then 1 else undefined" in exI)
  apply(rule_tac x="\<lambda>v. if v = ''x'' then 2000000 else if v = ''high'' then 0 else if v = ''n'' then 2000000 else if v = ''nondet'' then -1 else if v = ''low'' then 0 else undefined" in exI)
  apply clarsimp
  done


subsection "client2"

text {*
  An example akin to client2 from O'Hearn~\cite{OHearn_19}. 

  Note that this example is carefully written to show use of the frontier rule first to
  reason up to the broken loop iteration, and then we unfold the loop at that point to
  reason about the broken iteration, and then use the plain backwards variant rule to
  reason over the remainder of the loop.
*}
definition client2 :: com where
  "client2 \<equiv> (Assign ''x'' (N 0);;
              (While (Less (V ''x'') (N 4000000))
                     ((Assign ''x'' (Plus (V ''x'') (N 1)));;
                       (If (BEq (V ''x'') (N 2000000)) (Assign ''low'' (V ''high'')) SKIP))
                       )
              )"

lemma client2:
  "\<exists>Q. ir_hoare low_eq client2 client2 Q \<and> (\<forall>s s'. Q s s' \<longrightarrow> low_neq s s') \<and> nontrivial Q"
  apply(rule exI, rule conjI, simp add: client2_def)
   apply(rule_tac P=low_eq_strong in ir_pre)  
   apply(rule ir_Seq)
     apply(rule ir_Assign_Assign)
    apply clarsimp

  apply(rule ir_pre)
     apply(rule ir_While_backwards_frontier_both[where P="\<lambda>n s s'. low_eq_strong s s' \<and> s ''x'' = int n \<and> s' ''x'' = int n \<and> s ''x'' \<ge> 0 \<and> s ''x'' \<le> 2000000 - 1 \<and> s' ''x'' \<ge> 0 \<and> s' ''x'' \<le> 2000000 - 1"])
      apply(rule ir_Seq)
       apply(rule ir_Assign_Assign)
  apply clarsimp
      apply(rule ir_post)
       apply(rule ir_If')
        apply(rule ir_Assign_Assign)
       apply(rule ir_Skip_Skip)
      apply clarsimp

     apply clarsimp
     apply(rule ir_While')
      apply clarsimp
      apply(rule ir_Seq)
       apply(rule ir_Seq)
       apply(rule ir_Assign_Assign)
      apply(rule ir_If_True_True)
      apply(rule ir_Assign_Assign)
     apply clarsimp

  apply(rule ir_pre)
     apply(rule ir_While_backwards_both[where P="\<lambda>n s s'.  s ''x'' = 2000000 + int n \<and> s' ''x'' = 2000000 + int n \<and> s ''x'' \<ge> 2000000 \<and> s ''x'' \<le> 4000000 \<and> s' ''x'' \<ge> 2000000 \<and> s' ''x'' \<le> 4000000 \<and> s ''low'' = s ''high'' \<and> s' ''low'' = s' ''high'' \<and> s ''high'' \<noteq> s' ''high''"])


     apply(rule ir_Seq)
      apply(rule ir_Assign_Assign)
      apply(rule ir_If_False_False)
       apply fastforce
      apply (fastforce simp: low_eq_strong_def)
     apply fastforce
    apply(fastforce simp: low_eq_strong_def)
   apply(fastforce simp: low_eq_strong_def)

  apply(rule conjI)
   apply(clarsimp simp: low_eq_strong_def split: if_splits)

  apply clarsimp
  (* ugh having to manually do constraint solving here... *)
  apply(clarsimp simp: low_eq_strong_def nontrivial_def)
  apply(rule_tac x="\<lambda>v. if v = ''x'' then 4000000 else if v = ''high'' then 1 else if v = ''n'' then 2000000 else if v = ''nondet'' then -1 else if v = ''low'' then 1 else undefined" in exI)
  apply(rule_tac x="\<lambda>v. if v = ''x'' then 4000000 else if v = ''high'' then 0 else if v = ''n'' then 2000000 else if v = ''nondet'' then -1 else if v = ''low'' then 0 else undefined" in exI)
  apply clarsimp
  done

end
