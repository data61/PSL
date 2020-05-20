(*  Author:     Tobias Nipkow, 2007  *)

section\<open>Quantifier elimination\<close>

theory QE
imports Logic
begin

text\<open>\noindent
The generic, i.e.\ theory-independent part of quantifier elimination.
Both DNF and an NNF-based procedures are defined and proved correct.\<close>

notation (input) Collect ("|_|")

subsection\<open>No Equality\<close>

context ATOM
begin

subsubsection\<open>DNF-based\<close>

text\<open>\noindent Taking care of atoms independent of variable 0:\<close>

definition
"qelim qe as =
 (let qf = qe [a\<leftarrow>as. depends\<^sub>0 a];
      indep = [Atom(decr a). a\<leftarrow>as, \<not> depends\<^sub>0 a]
  in and qf (list_conj indep))"

abbreviation is_dnf_qe :: "('a list \<Rightarrow> 'a fm) \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_dnf_qe qe as \<equiv> \<forall>xs. I(qe as) xs = (\<exists>x.\<forall>a\<in>set as. I\<^sub>a a (x#xs))"

text\<open>\noindent
Note that the exported abbreviation will have as a first parameter
the type @{typ"'b"} of values \<open>xs\<close> ranges over.\<close>

lemma I_qelim:
assumes qe: "\<And>as. (\<forall>a \<in> set as. depends\<^sub>0 a) \<Longrightarrow> is_dnf_qe qe as"
shows "is_dnf_qe (qelim qe) as" (is "\<forall>xs. ?P xs")
proof
  fix  xs
  let ?as0 = "filter depends\<^sub>0 as"
  let ?as1 = "filter (Not \<circ> depends\<^sub>0) as"
  have "I (qelim qe as) xs =
        (I (qe ?as0) xs \<and> (\<forall>a\<in>set(map decr ?as1). I\<^sub>a a xs))"
    (is "_ = (_ \<and> ?B)") by(force simp add:qelim_def)
  also have "\<dots> = ((\<exists>x. \<forall>a \<in> set ?as0. I\<^sub>a a (x#xs)) \<and> ?B)"
    by(simp add:qe not_dep_decr)
  also have "\<dots> = (\<exists>x. (\<forall>a \<in> set ?as0. I\<^sub>a a (x#xs)) \<and> ?B)" by blast
  also have "?B = (\<forall>a \<in> set ?as1. I\<^sub>a (decr a) xs)" by simp
  also have "(\<exists>x. (\<forall>a \<in> set ?as0. I\<^sub>a a (x#xs)) \<and> \<dots>) =
             (\<exists>x. (\<forall>a \<in> set ?as0. I\<^sub>a a (x#xs)) \<and>
                  (\<forall>a \<in> set ?as1. I\<^sub>a a (x#xs)))"
    by(simp add: not_dep_decr)
  also have "\<dots> = (\<exists>x. \<forall>a \<in> set(?as0 @ ?as1). I\<^sub>a a (x#xs))"
    by (simp add:ball_Un)
  also have "\<dots> = (\<exists>x. \<forall>a \<in> set(as). I\<^sub>a a (x#xs))"
    by simp blast
  finally show "?P xs" .
qed

text\<open>\noindent The generic DNF-based quantifier elimination procedure:\<close>

fun lift_dnf_qe :: "('a list \<Rightarrow> 'a fm) \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
"lift_dnf_qe qe (And \<phi>\<^sub>1 \<phi>\<^sub>2) = and (lift_dnf_qe qe \<phi>\<^sub>1) (lift_dnf_qe qe \<phi>\<^sub>2)" |
"lift_dnf_qe qe (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = or (lift_dnf_qe qe \<phi>\<^sub>1) (lift_dnf_qe qe \<phi>\<^sub>2)" |
"lift_dnf_qe qe (Neg \<phi>) = neg(lift_dnf_qe qe \<phi>)" |
"lift_dnf_qe qe (ExQ \<phi>) = Disj (dnf(nnf(lift_dnf_qe qe \<phi>))) (qelim qe)" |
"lift_dnf_qe qe \<phi> = \<phi>"

lemma qfree_lift_dnf_qe: "(\<And>as. (\<forall>a\<in>set as. depends\<^sub>0 a) \<Longrightarrow> qfree(qe as))
 \<Longrightarrow> qfree(lift_dnf_qe qe \<phi>)"
by (induct \<phi>) (simp_all add:qelim_def)

lemma qfree_lift_dnf_qe2: "qe \<in> lists |depends\<^sub>0| \<rightarrow> |qfree|
 \<Longrightarrow> qfree(lift_dnf_qe qe \<phi>)"
using in_lists_conv_set[where ?'a = 'a]
by (simp add:Pi_def qfree_lift_dnf_qe)

lemma lem: "\<forall>P A. (\<exists>x\<in>A. \<exists>y. P x y) = (\<exists>y. \<exists>x\<in>A. P x y)" by blast

lemma I_lift_dnf_qe:
assumes  "\<And>as. (\<forall>a \<in> set as. depends\<^sub>0 a) \<Longrightarrow> qfree(qe as)"
and "\<And>as. (\<forall>a \<in> set as. depends\<^sub>0 a) \<Longrightarrow> is_dnf_qe qe as"
shows "I (lift_dnf_qe qe \<phi>) xs = I \<phi> xs"
proof(induct \<phi> arbitrary:xs)
  case ExQ thus ?case
    by (simp add: assms I_qelim lem I_dnf nqfree_nnf qfree_lift_dnf_qe
                  I_nnf)
qed simp_all

lemma I_lift_dnf_qe2:
assumes  "qe \<in> lists |depends\<^sub>0| \<rightarrow> |qfree|"
and "\<forall>as \<in> lists |depends\<^sub>0|. is_dnf_qe qe as"
shows "I (lift_dnf_qe qe \<phi>) xs = I \<phi> xs"
using assms in_lists_conv_set[where ?'a = 'a]
by(simp add:Pi_def I_lift_dnf_qe)

text\<open>\noindent Quantifier elimination with invariant (needed for Presburger):\<close>

lemma I_qelim_anormal:
assumes qe: "\<And>xs as. \<forall>a \<in> set as. depends\<^sub>0 a \<and> anormal a \<Longrightarrow> is_dnf_qe qe as"
and nm: "\<forall>a \<in> set as. anormal a"
shows "I (qelim qe as) xs = (\<exists>x. \<forall>a\<in>set as. I\<^sub>a a (x#xs))"
proof -
  let ?as0 = "filter depends\<^sub>0 as"
  let ?as1 = "filter (Not \<circ> depends\<^sub>0) as"
  have "I (qelim qe as) xs =
        (I (qe ?as0) xs \<and> (\<forall>a\<in>set(map decr ?as1). I\<^sub>a a xs))"
    (is "_ = (_ \<and> ?B)") by(force simp add:qelim_def)
  also have "\<dots> = ((\<exists>x. \<forall>a \<in> set ?as0. I\<^sub>a a (x#xs)) \<and> ?B)"
    by(simp add:qe nm not_dep_decr)
  also have "\<dots> = (\<exists>x. (\<forall>a \<in> set ?as0. I\<^sub>a a (x#xs)) \<and> ?B)" by blast
  also have "?B = (\<forall>a \<in> set ?as1. I\<^sub>a (decr a) xs)" by simp
  also have "(\<exists>x. (\<forall>a \<in> set ?as0. I\<^sub>a a (x#xs)) \<and> \<dots>) =
             (\<exists>x. (\<forall>a \<in> set ?as0. I\<^sub>a a (x#xs)) \<and>
                  (\<forall>a \<in> set ?as1. I\<^sub>a a (x#xs)))"
    by(simp add: not_dep_decr)
  also have "\<dots> = (\<exists>x. \<forall>a \<in> set(?as0 @ ?as1). I\<^sub>a a (x#xs))"
    by (simp add:ball_Un)
  also have "\<dots> = (\<exists>x. \<forall>a \<in> set(as). I\<^sub>a a (x#xs))"
    by simp blast
  finally show ?thesis .
qed

context notes [[simp_depth_limit = 5]]
begin

lemma anormal_atoms_qelim:
  "(\<And>as. \<forall>a \<in> set as. depends\<^sub>0 a \<and> anormal a \<Longrightarrow> normal(qe as)) \<Longrightarrow>
   \<forall>a \<in> set as. anormal a \<Longrightarrow> a \<in> atoms(qelim qe as) \<Longrightarrow> anormal a"
apply(auto simp add:qelim_def and_def normal_def split:if_split_asm)
apply(auto simp add:anormal_decr dest!: atoms_list_conjE)
 apply(erule_tac x = "filter depends\<^sub>0 as" in meta_allE)
 apply(simp)
apply(erule_tac x = "filter depends\<^sub>0 as" in meta_allE)
apply(simp)
done

lemma normal_lift_dnf_qe:
assumes "\<And>as. \<forall>a \<in> set as. depends\<^sub>0 a \<Longrightarrow> qfree(qe as)"
and "\<And>as. \<forall>a \<in> set as. depends\<^sub>0 a \<and> anormal a \<Longrightarrow> normal(qe as)"
shows  "normal \<phi> \<Longrightarrow> normal(lift_dnf_qe qe \<phi>)"
proof(simp add:normal_def, induct \<phi>)
  case ExQ thus ?case
    apply (auto dest!: atoms_list_disjE)
    apply(rule anormal_atoms_qelim)
      prefer 3 apply assumption
     apply(simp add:assms)
    apply (simp add:normal_def qfree_lift_dnf_qe anormal_dnf_nnf assms)
    done
qed (simp_all add:and_def or_def neg_def Ball_def)

end

context notes [[simp_depth_limit = 9]]
begin

lemma I_lift_dnf_qe_anormal:
assumes "\<And>as. \<forall>a \<in> set as. depends\<^sub>0 a \<Longrightarrow> qfree(qe as)"
and "\<And>as. \<forall>a \<in> set as. depends\<^sub>0 a \<and> anormal a \<Longrightarrow> normal(qe as)"
and "\<And>xs as. \<forall>a \<in> set as. depends\<^sub>0 a \<and> anormal a \<Longrightarrow> is_dnf_qe qe as"
shows "normal f \<Longrightarrow> I (lift_dnf_qe qe f) xs = I f xs"
proof(induct f arbitrary:xs)
  case ExQ thus ?case using normal_lift_dnf_qe[of qe]
    by (simp add: assms[simplified normal_def] anormal_dnf_nnf I_qelim_anormal lem I_dnf nqfree_nnf qfree_lift_dnf_qe I_nnf normal_def)
qed (simp_all add:normal_def)

end

lemma I_lift_dnf_qe_anormal2:
assumes "qe \<in> lists |depends\<^sub>0| \<rightarrow> |qfree|"
and "qe \<in> lists ( |depends\<^sub>0| \<inter> |anormal| ) \<rightarrow> |normal|"
and "\<forall>as \<in> lists( |depends\<^sub>0| \<inter> |anormal| ). is_dnf_qe qe as"
shows "normal f \<Longrightarrow> I (lift_dnf_qe qe f) xs = I f xs"
using assms in_lists_conv_set[where ?'a = 'a]
by(simp add:Pi_def I_lift_dnf_qe_anormal Int_def)


subsubsection\<open>NNF-based\<close>

fun lift_nnf_qe :: "('a fm \<Rightarrow> 'a fm) \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
"lift_nnf_qe qe (And \<phi>\<^sub>1 \<phi>\<^sub>2) = and (lift_nnf_qe qe \<phi>\<^sub>1) (lift_nnf_qe qe \<phi>\<^sub>2)" |
"lift_nnf_qe qe (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = or (lift_nnf_qe qe \<phi>\<^sub>1) (lift_nnf_qe qe \<phi>\<^sub>2)" |
"lift_nnf_qe qe (Neg \<phi>) = neg(lift_nnf_qe qe \<phi>)" |
"lift_nnf_qe qe (ExQ \<phi>) = qe(nnf(lift_nnf_qe qe \<phi>))" |
"lift_nnf_qe qe \<phi> = \<phi>"

lemma qfree_lift_nnf_qe: "(\<And>\<phi>. nqfree \<phi> \<Longrightarrow> qfree(qe \<phi>))
 \<Longrightarrow> qfree(lift_nnf_qe qe \<phi>)"
by (induct \<phi>) (simp_all add:nqfree_nnf)

lemma qfree_lift_nnf_qe2:
  "qe \<in> |nqfree| \<rightarrow> |qfree| \<Longrightarrow> qfree(lift_nnf_qe qe \<phi>)"
by(simp add:Pi_def qfree_lift_nnf_qe)

lemma I_lift_nnf_qe:
assumes  "\<And>\<phi>. nqfree \<phi> \<Longrightarrow> qfree(qe \<phi>)"
and "\<And>xs \<phi>. nqfree \<phi> \<Longrightarrow> I (qe \<phi>) xs = (\<exists>x. I \<phi> (x#xs))"
shows "I (lift_nnf_qe qe \<phi>) xs = I \<phi> xs"
proof(induct "\<phi>" arbitrary:xs)
  case ExQ thus ?case
    by (simp add: assms nqfree_nnf qfree_lift_nnf_qe I_nnf)
qed simp_all

lemma I_lift_nnf_qe2:
assumes  "qe \<in> |nqfree| \<rightarrow> |qfree|"
and "\<forall>\<phi> \<in> |nqfree|. \<forall>xs. I (qe \<phi>) xs = (\<exists>x. I \<phi> (x#xs))"
shows "I (lift_nnf_qe qe \<phi>) xs = I \<phi> xs"
using assms by(simp add:Pi_def I_lift_nnf_qe)

lemma normal_lift_nnf_qe:
assumes "\<And>\<phi>. nqfree \<phi> \<Longrightarrow> qfree(qe \<phi>)"
and     "\<And>\<phi>. nqfree \<phi> \<Longrightarrow> normal \<phi> \<Longrightarrow> normal(qe \<phi>)"
shows "normal \<phi> \<Longrightarrow> normal(lift_nnf_qe qe \<phi>)"
by (induct \<phi>)
   (simp_all add: assms Logic.neg_def normal_nnf
                  nqfree_nnf qfree_lift_nnf_qe)

lemma I_lift_nnf_qe_normal:
assumes  "\<And>\<phi>. nqfree \<phi> \<Longrightarrow> qfree(qe \<phi>)"
and "\<And>\<phi>. nqfree \<phi> \<Longrightarrow> normal \<phi> \<Longrightarrow> normal(qe \<phi>)"
and "\<And>xs \<phi>. normal \<phi> \<Longrightarrow> nqfree \<phi> \<Longrightarrow> I (qe \<phi>) xs = (\<exists>x. I \<phi> (x#xs))"
shows "normal \<phi> \<Longrightarrow> I (lift_nnf_qe qe \<phi>) xs = I \<phi> xs"
proof(induct "\<phi>" arbitrary:xs)
  case ExQ thus ?case
    by (simp add: assms nqfree_nnf qfree_lift_nnf_qe I_nnf
                  normal_lift_nnf_qe normal_nnf)
qed auto

lemma I_lift_nnf_qe_normal2:
assumes  "qe \<in> |nqfree| \<rightarrow> |qfree|"
and "qe \<in> |nqfree| \<inter> |normal| \<rightarrow> |normal|"
and "\<forall>\<phi> \<in> |normal| \<inter> |nqfree|. \<forall>xs. I (qe \<phi>) xs = (\<exists>x. I \<phi> (x#xs))"
shows "normal \<phi> \<Longrightarrow> I (lift_nnf_qe qe \<phi>) xs = I \<phi> xs"
using assms by(simp add:Pi_def I_lift_nnf_qe_normal Int_def)

end


subsection\<open>With equality\<close>

text\<open>DNF-based quantifier elimination can accommodate equality atoms
in a generic fashion.\<close>

locale ATOM_EQ = ATOM +
fixes solvable\<^sub>0 :: "'a \<Rightarrow> bool"
and trivial :: "'a \<Rightarrow> bool" 
and subst\<^sub>0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
assumes subst\<^sub>0:
  "\<lbrakk> solvable\<^sub>0 eq;  \<not>trivial eq;  I\<^sub>a eq (x#xs);  depends\<^sub>0 a \<rbrakk>
   \<Longrightarrow> I\<^sub>a (subst\<^sub>0 eq a) xs = I\<^sub>a a (x#xs)"
and trivial: "trivial eq \<Longrightarrow> I\<^sub>a eq xs"
and solvable: "solvable\<^sub>0 eq \<Longrightarrow> \<exists>x. I\<^sub>a eq (x#xs)"
and is_triv_self_subst: "solvable\<^sub>0 eq \<Longrightarrow> trivial (subst\<^sub>0 eq eq)"

begin

definition lift_eq_qe :: "('a list \<Rightarrow> 'a fm) \<Rightarrow> 'a list \<Rightarrow> 'a fm" where
"lift_eq_qe qe as =
 (let as = [a\<leftarrow>as. \<not> trivial a]
  in case [a\<leftarrow>as. solvable\<^sub>0 a] of
    [] \<Rightarrow> qe as
  | eq # eqs \<Rightarrow>
        (let ineqs = [a\<leftarrow>as. \<not> solvable\<^sub>0 a]
         in list_conj (map (Atom \<circ> (subst\<^sub>0 eq)) (eqs @ ineqs))))"

theorem I_lift_eq_qe:
assumes dep: "\<forall>a\<in>set as. depends\<^sub>0 a"
assumes qe: "\<And>as. (\<forall>a \<in> set as. depends\<^sub>0 a \<and> \<not> solvable\<^sub>0 a) \<Longrightarrow>
   I (qe as) xs = (\<exists>x. \<forall>a \<in> set as. I\<^sub>a a (x#xs))"
shows "I (lift_eq_qe qe as) xs = (\<exists>x. \<forall>a \<in> set as. I\<^sub>a a (x#xs))"
  (is "?L = ?R")
proof -
  let ?as = "[a\<leftarrow>as. \<not> trivial a]"
  show ?thesis
  proof (cases "[a\<leftarrow>?as. solvable\<^sub>0 a]")
    case Nil
    hence "\<forall>a\<in>set as. \<not> trivial a \<longrightarrow> \<not> solvable\<^sub>0 a"
      by(auto simp: filter_empty_conv)
    thus "?L = ?R"
      by(simp add:lift_eq_qe_def dep qe cong:conj_cong) (metis trivial)
  next
    case (Cons eq _)
    then have "eq \<in> set as" "solvable\<^sub>0 eq" "\<not> trivial eq"
      by (auto simp: filter_eq_Cons_iff)
    then obtain e where "I\<^sub>a eq (e#xs)" by(metis solvable)
    have "\<forall>a \<in> set as. I\<^sub>a a (e # xs) = I\<^sub>a (subst\<^sub>0 eq a) xs"
      by(simp add: subst\<^sub>0[OF \<open>solvable\<^sub>0 eq\<close> \<open>\<not> trivial eq\<close> \<open>I\<^sub>a eq (e#xs)\<close>] dep)
    thus ?thesis using Cons dep
      apply(simp add: lift_eq_qe_def,
            clarsimp simp: filter_eq_Cons_iff ball_Un)
      apply(rule iffI)
      apply(fastforce intro!:exI[of _ e] simp: trivial is_triv_self_subst)
      apply (metis subst\<^sub>0)
      done
  qed
qed

definition "lift_dnfeq_qe = lift_dnf_qe \<circ> lift_eq_qe"

lemma qfree_lift_eq_qe:
  "(\<And>as. \<forall>a\<in>set as. depends\<^sub>0 a \<Longrightarrow> qfree (qe as)) \<Longrightarrow>
   \<forall>a\<in>set as. depends\<^sub>0 a \<Longrightarrow> qfree(lift_eq_qe qe as)"
by(simp add:lift_eq_qe_def ball_Un split:list.split)

lemma qfree_lift_dnfeq_qe: "(\<And>as. (\<forall>a\<in>set as. depends\<^sub>0 a) \<Longrightarrow> qfree(qe as))
  \<Longrightarrow> qfree(lift_dnfeq_qe qe \<phi>)"
by(simp add: lift_dnfeq_qe_def qfree_lift_dnf_qe qfree_lift_eq_qe)

lemma I_lift_dnfeq_qe:
  "(\<And>as. (\<forall>a \<in> set as. depends\<^sub>0 a) \<Longrightarrow> qfree(qe as)) \<Longrightarrow>
   (\<And>as. (\<forall>a \<in> set as. depends\<^sub>0 a \<and> \<not> solvable\<^sub>0 a) \<Longrightarrow> is_dnf_qe qe as) \<Longrightarrow>
   I (lift_dnfeq_qe qe \<phi>) xs = I \<phi> xs"
by(simp add:lift_dnfeq_qe_def I_lift_dnf_qe qfree_lift_eq_qe I_lift_eq_qe)

lemma I_lift_dnfeq_qe2:
  "qe \<in> lists |depends\<^sub>0| \<rightarrow> |qfree| \<Longrightarrow>
   (\<forall>as \<in> lists( |depends\<^sub>0| \<inter> - |solvable\<^sub>0| ). is_dnf_qe qe as) \<Longrightarrow>
   I (lift_dnfeq_qe qe \<phi>) xs = I \<phi> xs"
using in_lists_conv_set[where ?'a = 'a]
by(simp add:Pi_def I_lift_dnfeq_qe Int_def Compl_eq)

end

end
