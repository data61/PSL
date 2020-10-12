(*  Title:       A simple ROBDD implementation
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
section \<open>\isaheader{ROBDDs}\<close>
theory Robdd
imports Main "../ICF/spec/MapSpec" "../Iterator/SetIteratorOperations"
        
begin

text \<open>Let's first fix some datatypes for BDDs or more specifically
for reduced ordered binary decision diagrams (OBDDs).\<close>

type_synonym node_id = nat
type_synonym var = nat
type_synonym assigment = "var \<Rightarrow> bool"

datatype robdd = robdd_leaf bool | robdd_var node_id robdd var robdd 
abbreviation "robdd_zero \<equiv> robdd_leaf False"
abbreviation "robdd_one \<equiv> robdd_leaf True"

primrec robdd_\<alpha> where
   "robdd_\<alpha> (robdd_leaf f) a = f"
 | "robdd_\<alpha> (robdd_var i l v r) a = (if a v then robdd_\<alpha> l a else robdd_\<alpha> r a)"

lemma robdd_\<alpha>_simps_leafs [simp] : 
  "robdd_\<alpha> (robdd_leaf f1) = robdd_\<alpha> (robdd_leaf f2) \<longleftrightarrow> (f1 = f2)" 
by (simp add: fun_eq_iff)

primrec robdd_get_id :: "robdd \<Rightarrow> node_id" where
   "robdd_get_id (robdd_leaf f) = (if f then 1 else 0)"
 | "robdd_get_id (robdd_var i l v r) = i"

primrec robdd_get_var :: "robdd \<Rightarrow> var" where
   "robdd_get_var (robdd_leaf f) = 0"
 | "robdd_get_var (robdd_var i l v r) = v"

primrec robdd_get_left :: "robdd \<Rightarrow> robdd" where
   "robdd_get_left (robdd_leaf f) = robdd_leaf f"
 | "robdd_get_left (robdd_var i l v r) = l"

primrec robdd_get_right :: "robdd \<Rightarrow> robdd" where
   "robdd_get_right (robdd_leaf f) = robdd_leaf f"
 | "robdd_get_right (robdd_var i l v r) = r"

primrec robdd_to_bool :: "robdd \<Rightarrow> bool option" where
   "robdd_to_bool (robdd_leaf f) = Some f"
 | "robdd_to_bool (robdd_var i l v r) = None"

primrec robdd_is_leaf where
   "robdd_is_leaf (robdd_leaf _) = True"
 | "robdd_is_leaf (robdd_var _ _ _ _) = False"

lemma robdd_is_leaf_alt_def :
  "robdd_is_leaf b \<longleftrightarrow> (b = robdd_one \<or> b = robdd_zero)"
by (cases b) auto

text \<open>IDs are just used a convinience for performance reasons. Therefore,
        we define two robdds to be equivalent if they are equal up to ids.\<close>
primrec robdd_equiv where
   "robdd_equiv (robdd_leaf f) b = (b = robdd_leaf f)"
 | "robdd_equiv (robdd_var i l v r) b = 
    (\<exists>i' l' r'. b = robdd_var i' l' v r' \<and> robdd_equiv l l' \<and> robdd_equiv r r')"

lemma robdd_equiv_simps[simp] :
   "robdd_equiv b (robdd_leaf f) = (b = robdd_leaf f)"
   "robdd_equiv b b"
  by (induct b, auto)

subsection \<open>subrobdds\<close>

text \<open>It is for later definitions important to be able to talk about all the
robdds that form a robdd. This leads to the definition of subrobdds.\<close>

primrec subrobdds :: "robdd \<Rightarrow> robdd set" where
   "subrobdds (robdd_leaf f) = {robdd_leaf f}"
 | "subrobdds (robdd_var i l v r) = 
    (insert (robdd_var i l v r) (subrobdds l \<union> subrobdds r))"

definition subrobdds_proper :: "robdd \<Rightarrow> robdd set" where
   "subrobdds_proper b = (subrobdds b) - {b}"

lemma subrobdds_alt_def :
  "subrobdds b = insert b (subrobdds_proper b)"
by (cases b) (simp_all add: subrobdds_proper_def)

lemma subobbds_proper_size: 
  "b1 \<in> subrobdds_proper b2 \<Longrightarrow> size_robdd b1 < size_robdd b2"
proof (induct b2 arbitrary: b1)
  case (robdd_leaf f) thus ?case by (simp add: subrobdds_proper_def)
next
  case (robdd_var i l v r) 
  note indhyp_l = robdd_var(1)
  note indhyp_r = robdd_var(2)

  from robdd_var(3) have b1_in_cases: "b1 \<in> subrobdds l \<or> b1 \<in> subrobdds r" by (simp add: subrobdds_proper_def)
  show ?case
  proof (cases "b1 \<in> subrobdds l")
    case True with indhyp_l[of b1] show ?thesis
      apply (cases "b1 = l")
      apply (simp_all add: subrobdds_proper_def)
    done
  next
    case False 
    with b1_in_cases have "b1 \<in> subrobdds r" by blast
    with indhyp_r[of b1] show ?thesis
      apply (cases "b1 = r")
      apply (simp_all add: subrobdds_proper_def)
    done
  qed
qed

lemma subrobdds_size: 
  "b1 \<in> subrobdds b2 \<Longrightarrow> size_robdd b1 \<le> size_robdd b2"
unfolding subrobdds_alt_def by simp (metis le_eq_less_or_eq subobbds_proper_size)

lemma subrobdds_refl[simp]:  "b \<in> subrobdds b" by (simp add: subrobdds_alt_def)

lemma subrobdds_antisym:  
  "b1 \<in> subrobdds b2 \<Longrightarrow> b2 \<in> subrobdds b1 \<Longrightarrow> b1 = b2"
  apply (cases "b1 = b2")
  apply (simp_all add: subrobdds_alt_def)
  apply (metis order_less_asym' subobbds_proper_size)
done

lemma subrobdds_trans :  
  "b1 \<in> subrobdds b2 \<Longrightarrow> b2 \<in> subrobdds b3 \<Longrightarrow> b1 \<in> subrobdds b3"
  apply (induct b3 arbitrary: b1 b2)
  apply (simp_all)
  apply (elim disjE)
  apply (simp_all)
done

lemma subrobdds_proper_simps [simp] :
   "subrobdds_proper (robdd_leaf f) = {}"
   "subrobdds_proper (robdd_var i l v r) = 
    (insert l (insert r (subrobdds_proper l \<union> subrobdds_proper r)))"
proof -
  show "subrobdds_proper (robdd_leaf f) = {}" 
    by (simp_all add: subrobdds_proper_def)
next
  have "subrobdds_proper (robdd_var i l v r) = subrobdds l \<union> subrobdds r - {robdd_var i l v r}"
    by (simp add: subrobdds_proper_def)
  also have "... = subrobdds l \<union> subrobdds r" 
  proof -
    from subrobdds_size [of "robdd_var i l v r" l] subrobdds_size [of "robdd_var i l v r" r]
    have "robdd_var i l v r \<notin> subrobdds l" "robdd_var i l v r \<notin> subrobdds r" by auto
    thus ?thesis by auto  
  qed
  also have "... = (insert l (insert r (subrobdds_proper l \<union> subrobdds_proper r)))"
     by (auto simp add: subrobdds_proper_def)
  finally show "subrobdds_proper (robdd_var i l v r) = 
        (insert l (insert r (subrobdds_proper l \<union> subrobdds_proper r)))" .
qed

lemma subrobdds_subset_simp :
  "subrobdds b1 \<subseteq> subrobdds b2 \<longleftrightarrow> b1 \<in> subrobdds b2"
by (metis subrobdds_refl subrobdds_trans subset_iff)

definition subrobdds_set where
  "subrobdds_set bs = \<Union>(subrobdds ` bs)"

lemma subrobdds_set_simps [simp] :
  "subrobdds_set {} = {}"
  "subrobdds_set (insert b bs) = subrobdds b \<union> subrobdds_set bs"
  "subrobdds_set (bs1 \<union> bs2) = subrobdds_set bs1 \<union> subrobdds_set bs2"
unfolding subrobdds_set_def by simp_all

lemma subrobdds_set_subset_simp :
  "subrobdds b \<subseteq> subrobdds_set bs \<longleftrightarrow> b \<in> subrobdds_set bs"
unfolding subrobdds_set_def
by (auto simp add: subset_iff dest: subrobdds_trans)

lemma subrobdds_set_idempot [simp] :
  "subrobdds_set (subrobdds_set bs) = subrobdds_set bs"
unfolding subrobdds_set_def
by (auto dest: subrobdds_trans intro: subrobdds_refl)

lemma subrobdds_set_idempot2 [simp] :
  "subrobdds_set (subrobdds b) = subrobdds b"
using subrobdds_set_idempot[of "{b}"]
by simp

lemma subrobdds_set_mono :
  "bs \<subseteq> subrobdds_set bs"
unfolding subrobdds_set_def by auto

lemma subrobdds_set_mono2 :
  "bs1 \<subseteq> bs2 \<Longrightarrow> (subrobdds_set bs1 \<subseteq> subrobdds_set bs2)"
unfolding subrobdds_set_def by auto

subsection \<open>Invariants\<close>

subsubsection \<open>IDs\<close>

text \<open>Ids are just added for convienience and performance. Two ROBDDs should have
the same id if and only if they have the same semantics. This way, the equivalence check
of ROBDDs can be reduced to an equality check of ids.\<close>

definition robdd_invar_ids where
  "robdd_invar_ids bs =
   (\<forall>b1 b2. (b1 \<in> subrobdds_set bs \<and> b2 \<in> subrobdds_set bs) \<longrightarrow>
              ((robdd_\<alpha> b1 = robdd_\<alpha> b2) \<longleftrightarrow> robdd_get_id b1 = robdd_get_id b2))" 

text \<open>leafs can often be implicitly added\<close>
definition robdd_invar_ids_leafs where
  "robdd_invar_ids_leafs bs =
   (\<forall>b f. (b \<in> subrobdds_set bs) \<longrightarrow>
          ((robdd_\<alpha> b = robdd_\<alpha> (robdd_leaf f)) \<longleftrightarrow> robdd_get_id b = robdd_get_id (robdd_leaf f)))" 

definition robdd_invar_ids_full where
  "robdd_invar_ids_full bs \<equiv>
   robdd_invar_ids bs \<and> robdd_invar_ids_leafs bs"

lemma robdd_invar_ids_full_alt_def :
  "robdd_invar_ids_full bs =
   robdd_invar_ids (insert robdd_zero (insert robdd_one bs))"
unfolding robdd_invar_ids_full_def robdd_invar_ids_def robdd_invar_ids_leafs_def
  apply (simp)
  apply (intro iffI allI impI, elim conjE impE disjE)
  apply (simp_all)
  apply (metis+) [3]
  apply (elim conjE impE disjE)
  apply (simp_all)
  apply (metis+) 
done

text \<open>Together with other invariants it can the later be derived that
        two robdds have the same id if and only if they are equal.\<close>
definition robdd_invar_ids_equal where
  "robdd_invar_ids_equal bs =
   (\<forall>b1 b2. (b1 \<in> subrobdds_set bs \<and> b2 \<in> subrobdds_set bs) \<longrightarrow>
              ((robdd_get_id b1 = robdd_get_id b2) \<longleftrightarrow> b1 = b2))" 

definition robdd_invar_ids_leafs_equal where
  "robdd_invar_ids_leafs_equal bs =
   (\<forall>b f. (b \<in> subrobdds_set bs) \<longrightarrow>
              ((robdd_get_id b = robdd_get_id (robdd_leaf f)) \<longleftrightarrow> b = (robdd_leaf f)))" 

definition robdd_invar_ids_full_equal where
  "robdd_invar_ids_full_equal bs \<equiv>
   robdd_invar_ids_equal bs \<and> robdd_invar_ids_leafs_equal bs"

lemma robdd_invar_ids_full_equal_alt_def :
  "robdd_invar_ids_full_equal bs =
   robdd_invar_ids_equal (insert robdd_zero (insert robdd_one bs))"
unfolding robdd_invar_ids_full_equal_def robdd_invar_ids_equal_def robdd_invar_ids_leafs_equal_def
  apply (simp)
  apply (intro iffI allI impI)
  apply (elim conjE impE disjE)
  apply (simp_all)
  apply (metis+) [3]
  apply (metis One_nat_def robdd_get_id.simps(1))
done

lemma robdd_invar_idsI:
assumes "\<And>b1 b2. \<lbrakk>b1 \<in> (subrobdds_set bs); b2 \<in> (subrobdds_set bs)\<rbrakk> \<Longrightarrow>
                         (robdd_\<alpha> b1 = robdd_\<alpha> b2) \<longleftrightarrow> (robdd_get_id b1 = robdd_get_id b2)" 
shows "robdd_invar_ids bs"
using assms unfolding robdd_invar_ids_def by blast

lemma robdd_invar_idsD:
assumes "robdd_invar_ids bs"
assumes "b1 \<in> (subrobdds_set bs)"
        "b2 \<in> (subrobdds_set bs)"
shows "robdd_\<alpha> b1 = robdd_\<alpha> b2 \<longleftrightarrow> robdd_get_id b1 = robdd_get_id b2"
using assms unfolding robdd_invar_ids_def by blast

lemma robdd_invar_ids_subset_rule :
  "robdd_invar_ids bs1 \<Longrightarrow> bs2 \<subseteq> bs1 \<Longrightarrow> robdd_invar_ids bs2"
by (simp add: robdd_invar_ids_def subset_iff subrobdds_set_def) metis

lemma robdd_invar_ids_expand :
shows "robdd_invar_ids (subrobdds_set bs) = robdd_invar_ids bs"
by (simp add: robdd_invar_ids_def subrobdds_set_idempot)

lemma robdd_invar_ids_subset_subrobdds_rule :
assumes pre: "\<And>b2. b2 \<in> bs2 \<Longrightarrow> \<exists>b1 \<in> bs1. b2 \<in> (subrobdds b1)"
    and invar_bs1: "robdd_invar_ids bs1"
shows "robdd_invar_ids bs2"
apply (rule robdd_invar_ids_subset_rule [of "subrobdds_set bs1"])
apply (simp add: robdd_invar_ids_expand invar_bs1)
apply (simp add: subset_iff pre subrobdds_set_def)
done

text \<open>If two ROBDDs are equal up to ids and then they are in fact equal.\<close>
lemma robdd_invar_ids_equiv_implies_eq:
assumes "robdd_invar_ids bs"
    and "b1 \<in> bs" "b2 \<in> bs"
    and "robdd_equiv b1 b2"
  shows "b1 = b2"
using assms
proof (induct b1 arbitrary: b2 bs)
  case (robdd_var i l v r)
  note indhyp_l = robdd_var(1)
  note indhyp_r = robdd_var(2)
  note invar_ids = robdd_var(3)
  note in_bs = robdd_var(4,5)
  note equiv_b2 = robdd_var(6)

  from equiv_b2 obtain i' l' r' where
    b2_eq: "b2 = robdd_var i' l' v r'" and
    equiv_l: "robdd_equiv l l'" and
    equiv_r: "robdd_equiv r r'"
    unfolding robdd_equiv.simps by blast 

  have invar_ids': "robdd_invar_ids {robdd_var i l v r, b2}"
    apply (rule robdd_invar_ids_subset_subrobdds_rule[OF _ invar_ids])
    apply (auto simp add: subrobdds_alt_def in_bs)
  done
  have invar_ids_sub: "robdd_invar_ids {l, r, l', r'}"
    apply (rule robdd_invar_ids_subset_subrobdds_rule[OF _ invar_ids'])
    apply (auto simp add: b2_eq subrobdds_alt_def) 
  done

  from indhyp_l [OF invar_ids_sub _ _ equiv_l] 
       indhyp_r [OF invar_ids_sub _ _ equiv_r] 
  have l'_eq[simp]: "l' = l" and  r'_eq[simp]: "r' = r" by simp_all

  from robdd_invar_idsD[OF invar_ids', of "robdd_var i l v r" b2]
  have i'_eq[simp]: "i' = i" by (simp add: b2_eq robdd_\<alpha>_def subrobdds_set_def)

  show ?case by (simp add: b2_eq)
qed simp_all


subsubsection \<open>Variable order\<close>

text \<open>We are formalising reduced \emph{ordered} binary decision diagrams. Therefore, the
variables need to appear in order.\<close>

primrec robdd_invar_vars_greater where
   "robdd_invar_vars_greater n (robdd_leaf f) = True"
 | "robdd_invar_vars_greater n (robdd_var i l v r) = 
    (n \<le> v \<and> (robdd_invar_vars_greater (Suc v) l) \<and> (robdd_invar_vars_greater (Suc v) r))"

definition robdd_invar_vars where
   "robdd_invar_vars b = robdd_invar_vars_greater 0 b"

lemma robdd_invar_vars_greater___weaken :
   "robdd_invar_vars_greater n b \<Longrightarrow> n' \<le> n \<Longrightarrow> robdd_invar_vars_greater n' b"
by (cases b) (simp_all)

lemma robdd_invar_vars_impl: 
  "robdd_invar_vars_greater n robdd  \<Longrightarrow> robdd_invar_vars robdd"
unfolding robdd_invar_vars_def
by (rule robdd_invar_vars_greater___weaken[of n]) (simp_all)


subsubsection \<open>Reduced\<close>

text \<open>We are formalising \emph{reduced} ordered binary decision diagrams. Therefore, it should
be reduced.\<close>

primrec robdd_invar_reduced where
   "robdd_invar_reduced (robdd_leaf f) = True"
 | "robdd_invar_reduced (robdd_var i l v r) =       
     (\<not>(robdd_equiv l r) \<and> (robdd_invar_reduced l) \<and> (robdd_invar_reduced r))"

lemma robdd_invar_reduced_leaf [simp]: 
   "robdd_invar_reduced (robdd_leaf v) = True"
by (cases v) (simp_all)

lemma subrobdds_leaf_in_reduced: 
"robdd_invar_reduced b \<Longrightarrow> \<not>(robdd_is_leaf b) \<Longrightarrow> (robdd_one \<in> subrobdds b \<and> robdd_zero \<in> subrobdds b)"
proof (induct b)
  case (robdd_leaf f)
  thus ?case by simp
next
  case (robdd_var i l v r)
  note reduced_b = robdd_var(3)
  from reduced_b have not_equiv_lr: "\<not> robdd_equiv l r" and
    reduced_l: "robdd_invar_reduced l" and reduced_r: "robdd_invar_reduced r"
    by simp_all

  note indhyp_l = robdd_var(1)[OF reduced_l]
  note indhyp_r = robdd_var(2)[OF reduced_r]

  show ?case
  proof (cases "robdd_is_leaf l")
    case False
    with indhyp_l show ?thesis by simp
  next
    case True note l_is_leaf = this

    show ?thesis
    proof (cases "robdd_is_leaf r")
      case False
      with indhyp_r show ?thesis by simp
    next
      case True note r_is_leaf = this

      from l_is_leaf r_is_leaf not_equiv_lr show ?thesis
        unfolding robdd_is_leaf_alt_def by auto
    qed
  qed
qed 

lemma subrobdds_set_leaf_in_reduced: 
assumes bs_OK: "\<And>b. b \<in> bs \<Longrightarrow> robdd_invar_reduced b" 
    and bs_neq_leaf_set: "bs \<noteq> {robdd_one}" "bs \<noteq> {robdd_zero}" 
    and bs_neq_emp: "bs \<noteq> {}"
shows "robdd_one \<in> subrobdds_set bs \<and> robdd_zero \<in> subrobdds_set bs"
proof (cases "\<exists>b\<in>bs. \<not>(robdd_is_leaf b)")
  case True
  then obtain b where b_in: "b \<in> bs" and not_leaf_b: "\<not>(robdd_is_leaf b)" by blast

  from bs_OK b_in have invar_reduced: "robdd_invar_reduced b" by simp

  from subrobdds_leaf_in_reduced[OF invar_reduced not_leaf_b]
  have in_b: "robdd_one \<in> subrobdds b \<and> robdd_zero \<in> subrobdds b" .

  from in_b b_in show ?thesis
    unfolding subrobdds_set_def by auto
next
  case False hence only_leafs: "\<And>b. b \<in> bs \<Longrightarrow> robdd_is_leaf b" by simp

  from bs_neq_emp obtain b1 where b1_in: "b1 \<in> bs" by auto
  with only_leafs have leaf_b1: "robdd_is_leaf b1" by simp

  from leaf_b1 bs_neq_leaf_set have "bs \<noteq> {b1}"
    by (auto simp add: robdd_is_leaf_alt_def)
  with b1_in obtain b2 where b2_in: "b2 \<in> bs" and b2_neq: "b1 \<noteq> b2"
    by auto

  from b2_in only_leafs have leaf_b2: "robdd_is_leaf b2" by simp

  from b1_in b2_in b2_neq leaf_b1 leaf_b2 
  have "robdd_one \<in> bs \<and> robdd_zero \<in> bs" 
    unfolding robdd_is_leaf_alt_def by auto
  thus ?thesis unfolding subrobdds_set_def
    by simp (metis subrobdds_refl)
qed

lemma robdd_invar_ids_leafs_intro :
assumes bs_OK: "\<And>b. b \<in> bs \<Longrightarrow> robdd_invar_reduced b"
    and weak_invar: "robdd_invar_ids bs"
shows "robdd_invar_ids_leafs bs"
proof (cases "bs = {} \<or> bs = {robdd_one} \<or> bs = {robdd_zero}")
  case True thus ?thesis
  proof (elim disjE)
    assume "bs = {}" thus "robdd_invar_ids_leafs bs"
      unfolding robdd_invar_ids_leafs_def by simp
  next
    assume "bs = {robdd_one}" thus "robdd_invar_ids_leafs bs"
      unfolding robdd_invar_ids_leafs_def 
      by simp
  next
    assume "bs = {robdd_zero}" thus "robdd_invar_ids_leafs bs"
      unfolding robdd_invar_ids_leafs_def 
      by simp
  qed
next
  case False
  with subrobdds_set_leaf_in_reduced[of bs, OF bs_OK]
  have one_in: "robdd_one \<in> subrobdds_set bs" and
       zero_in: "robdd_zero \<in> subrobdds_set bs" by auto

  with weak_invar show ?thesis
    unfolding robdd_invar_ids_leafs_def robdd_invar_ids_def 
    by auto
qed


subsubsection \<open>Overall Invariant\<close>

definition robdd_invar_ext where
  "robdd_invar_ext bs n b = (b \<in> subrobdds_set bs \<and> robdd_invar_ids bs \<and> robdd_invar_vars_greater n b \<and> robdd_invar_reduced b)"

definition robdd_invar where
  "robdd_invar b = robdd_invar_ext {b} 0 b"

lemma robdd_invar_alt_def :
  "robdd_invar b = (robdd_invar_ids {b} \<and> robdd_invar_vars b \<and> robdd_invar_reduced b)"
unfolding robdd_invar_def robdd_invar_ext_def robdd_invar_vars_def subrobdds_set_def
by simp

lemma robdd_invar_simps_leafs [simp]: "robdd_invar (robdd_leaf value)"
  by (simp add: robdd_invar_alt_def robdd_invar_vars_def robdd_invar_ids_def subrobdds_set_def)

lemma robdd_invar_simps_var :
   "robdd_invar (robdd_var i l v r) \<Longrightarrow> (\<not>(robdd_equiv l r) \<and> robdd_invar l \<and> robdd_invar r)"
  apply (simp add: robdd_invar_alt_def robdd_invar_ids_def robdd_invar_vars_def subrobdds_set_def)
  apply (metis robdd_invar_vars_def robdd_invar_vars_impl)
done

lemma robdd_invar_subrobdds_set :
assumes bs_OK: "\<And>b. b \<in> bs \<Longrightarrow> robdd_invar b"
    and b_in: "b \<in> subrobdds_set bs"
  shows "robdd_invar b"
proof -
  from b_in obtain b' where b'_in: "b' \<in> bs" and b_in': "b \<in> subrobdds b'"
    unfolding subrobdds_set_def by auto

  from bs_OK[OF b'_in] have "robdd_invar b'" .
  with b_in' show "robdd_invar b"
    apply (induct b')
    apply simp_all
    apply (metis robdd_invar_simps_var)
  done
qed

lemma robdd_invar_ext_simps [simp] :
   "robdd_invar_ext bs n (robdd_leaf f) = (robdd_invar_ids bs \<and> ((robdd_leaf f) \<in> (subrobdds_set bs)))" (is ?T1)
   "robdd_invar_ext bs n (robdd_var i l v r) =
     ((robdd_var i l v r) \<in> (subrobdds_set bs) \<and> \<not>(robdd_equiv l r) \<and> n \<le> v \<and> robdd_invar_ext bs (Suc v) l \<and> robdd_invar_ext bs (Suc v) r)" (is ?T2)
proof -
  show ?T1 by (auto simp add: robdd_invar_ext_def)
next
  show ?T2 (is "?ls = ?rs")
  proof
    assume ?rs thus ?ls by (simp add: robdd_invar_ext_def subrobdds_set_def)
  next
    assume ?ls 
    then obtain b where b_props: "b \<in> bs"  "robdd_var i l v r \<in> subrobdds b" 
      by (auto simp add: robdd_invar_ext_def subrobdds_set_def)

    from subrobdds_trans [of l "robdd_var i l v r" b]
         subrobdds_trans [of r "robdd_var i l v r" b] 
    have "r \<in> subrobdds b" "l \<in> subrobdds b" by (simp_all add: b_props)
    with \<open>?ls\<close> \<open>b \<in> bs\<close> show ?rs by (auto simp add: robdd_invar_ext_def subrobdds_set_def)
  qed
qed

lemma rodd_invar_ext_idempot_subrobdds_set [simp]: 
   "robdd_invar_ext (subrobdds_set bs) n b = robdd_invar_ext bs n b" 
unfolding robdd_invar_ext_def robdd_invar_ids_def
by simp

lemma robdd_invar_ext_weaken :
assumes pre: "robdd_invar_ext bs2 n b"
    and bs2_props: "\<And>b2.  b \<in> subrobdds_set bs2 \<Longrightarrow> b2 \<in> bs1 \<Longrightarrow> \<exists>b1 \<in> bs2. b2 \<in> (subrobdds b1)"
    and b_in: "b \<in> subrobdds_set bs2 \<Longrightarrow> b \<in> subrobdds_set bs1"
    and m_le: "m \<le> n"
shows "robdd_invar_ext bs1 m b"
proof -
  from pre have 
    "b \<in> subrobdds_set bs2"
    "robdd_invar_ids bs2"
    "robdd_invar_vars_greater n b" 
    "robdd_invar_reduced b" 
  unfolding robdd_invar_ext_def by simp_all

  from \<open>b \<in> subrobdds_set bs2\<close> b_in
  have b_in: "b \<in> subrobdds_set bs1" by simp

  have invar_ids: "robdd_invar_ids bs1"
    apply (rule robdd_invar_ids_subset_subrobdds_rule [OF bs2_props])
    apply (simp add: \<open>b \<in> subrobdds_set bs2\<close>)
    apply simp
    apply fact
  done

  have invar_greater: "robdd_invar_vars_greater m b"
    by (rule robdd_invar_vars_greater___weaken[OF \<open>robdd_invar_vars_greater n b\<close> m_le])

  show ?thesis 
    unfolding robdd_invar_ext_def
    by (simp add: b_in invar_ids \<open>robdd_invar_reduced b\<close> invar_greater)
qed

lemma robdd_invar_ext_weaken_var :
assumes pre: "robdd_invar_ext bs n b"
    and m_le: "m \<le> n"
shows "robdd_invar_ext bs m b"
  apply (rule robdd_invar_ext_weaken[OF pre _ _ m_le])
  apply (simp_all add: Bex_def)
  apply (metis subrobdds_refl)
done

lemma robdd_invar_impl :
assumes invar_ext: "robdd_invar_ext bs n b"
shows "robdd_invar b"
unfolding robdd_invar_def
apply (rule robdd_invar_ext_weaken[OF invar_ext])
apply (simp_all add: subrobdds_set_def)
done

lemma robdd_\<alpha>_invar_greater :
assumes invar_vars: "robdd_invar_vars_greater n b"
    and a_equiv: "\<And>v. v \<ge> n \<Longrightarrow> a1 v = a2 v"
shows  "robdd_\<alpha> b a1 = robdd_\<alpha> b a2"
using assms
  apply (induct b) 
  apply (simp_all)
  apply (metis le_Suc_eq robdd_invar_vars_greater___weaken)
done

subsection \<open>ROBDDs are unique\<close>

text \<open>An important property of ROBDDs is that two ROBDDs have the same semantics if and only
if they are equal (up to ids in our case). Before we can prove this property some 
lemmata are needed.\<close>

lemma robdd_unique_leaf :
assumes invars_b: "robdd_invar_vars b" "robdd_invar_reduced b"
    and sem_eq: "robdd_\<alpha> b = robdd_\<alpha> (robdd_leaf value)"
shows "b = (robdd_leaf value)"
using assms
proof (induct b)
  case (robdd_leaf f) thus ?case by (simp add: fun_eq_iff) 
next
  case (robdd_var i l v r)
  note invar_l = robdd_var(1)
  note invar_r = robdd_var(2)
  note invars = robdd_var(3,4)
  note \<alpha>_eq = robdd_var(5)

  { fix a
    from invars(1) have invars_b11_b12: "robdd_invar_vars_greater (Suc v) l"
                                    "robdd_invar_vars_greater (Suc v) r"
      by (simp_all add: robdd_invar_vars_def)

    let ?a1 = "\<lambda>v'. if v = v' then True else a v'"
    let ?a2 = "\<lambda>v'. if v = v' then False else a v'"
    from \<alpha>_eq have a_neg: "\<And>a. (if a v then robdd_\<alpha> l a else robdd_\<alpha> r a) \<longleftrightarrow> value" 
      by (simp add: fun_eq_iff)

    from robdd_\<alpha>_invar_greater [OF invars_b11_b12(1), of a ?a1, symmetric]
         robdd_\<alpha>_invar_greater [OF invars_b11_b12(2), of a ?a2, symmetric]
         a_neg[of ?a1] a_neg[of ?a2]
    have "robdd_\<alpha> l a = value \<and> robdd_\<alpha> r a = value" by simp
  } 
  hence \<alpha>_l: "robdd_\<alpha> l = robdd_\<alpha> (robdd_leaf value)" and 
        \<alpha>_r: "robdd_\<alpha> r = robdd_\<alpha> (robdd_leaf value)"
    by (simp_all add: fun_eq_iff)

  from invars have "robdd_invar_vars l" "robdd_invar_vars r"
                   "robdd_invar_reduced l" "robdd_invar_reduced r" 
      apply (simp_all add: robdd_invar_vars_def)
      apply (metis robdd_invar_vars_def robdd_invar_vars_impl)+
    done
  with invar_l[OF _ _ \<alpha>_l] invar_r[OF _ _ \<alpha>_r] 
  have "l = r" by simp
  with invars(2) have "False" by simp
  thus ?case by simp
qed

lemma robdd_unique_var :
assumes invars_b1: "robdd_invar_vars (robdd_var i1 l1 v1 r1)" "robdd_invar_reduced (robdd_var i1 l1 v1 r1)"
    and invars_b2: "robdd_invar_vars (robdd_var i2 l2 v2 r2)" "robdd_invar_reduced (robdd_var i2 l2 v2 r2)"
    and sem_neq_b1: "robdd_\<alpha> l1 \<noteq> robdd_\<alpha> r1"
    and sem_neq_b2: "robdd_\<alpha> l2 \<noteq> robdd_\<alpha> r2"
    and sem_eq: "robdd_\<alpha> (robdd_var i1 l1 v1 r1) = robdd_\<alpha> (robdd_var i2 l2 v2 r2)"
shows "v1 = v2 \<and> robdd_\<alpha> l1 = robdd_\<alpha> l2 \<and> robdd_\<alpha> r1 = robdd_\<alpha> r2"
proof -
  { fix i1 l1 v1 r1 i2 l2 v2 r2 n1 n2
    assume invars_b1: "robdd_invar_vars_greater n1 (robdd_var i1 l1 v1 r1)" "robdd_invar_reduced (robdd_var i1 l1 v1 r1)"
       and invars_b2: "robdd_invar_vars_greater n2 (robdd_var i2 l2 v2 r2)" "robdd_invar_reduced (robdd_var i2 l2 v2 r2)"
       and sem_neq: "robdd_\<alpha> l1 \<noteq> robdd_\<alpha> r1"
       and sem_eq: "robdd_\<alpha> (robdd_var i1 l1 v1 r1) = robdd_\<alpha> (robdd_var i2 l2 v2 r2)"
       and ord: "v1 \<le> v2"

    from invars_b1(1) have invars_lr1: "robdd_invar_vars_greater (Suc v1) l1"
                                       "robdd_invar_vars_greater (Suc v1) r1" by simp_all

    from invars_b2(1) have invars_lr2: "robdd_invar_vars_greater (Suc v1) l2"
                                       "robdd_invar_vars_greater (Suc v1) r2"
                                       "v1 \<noteq> v2 \<Longrightarrow> robdd_invar_vars_greater v1 (robdd_var i1 l1 v1 r1)"
      apply (simp_all add: robdd_invar_ext_def robdd_invar_vars_def)
      apply (metis not_less_eq_eq robdd_invar_vars_greater___weaken ord)
      apply (metis not_less_eq_eq robdd_invar_vars_greater___weaken ord)
      apply (simp add: invars_lr1)
    done

    from sem_eq have sem_eq_a: "\<And>a. robdd_\<alpha> (robdd_var i1 l1 v1 r1) a = robdd_\<alpha> (robdd_var i2 l2 v2 r2) a" 
      by (simp add: fun_eq_iff)

    define a1 where "a1 a v' = (if v1 = v' then True else a v')" for a v'
    define a2 where "a2 a v' = (if v1 = v' then False else a v')" for a v'

    have a12_eval: "\<And>a. a1 a v1" "\<And>a. ~(a2 a v1)" "\<And>a v. v \<noteq> v1 \<Longrightarrow> a1 a v = a v \<and> a2 a v = a v"
      unfolding a1_def a2_def by simp_all

    { fix a
      from robdd_\<alpha>_invar_greater [OF invars_lr1(1), of a "a1 a", symmetric]
           robdd_\<alpha>_invar_greater [OF invars_lr1(2), of a "a2 a", symmetric]
           robdd_\<alpha>_invar_greater [OF invars_lr2(1), of a "a1 a", symmetric]
           robdd_\<alpha>_invar_greater [OF invars_lr2(2), of a "a2 a", symmetric]
           robdd_\<alpha>_invar_greater [OF invars_lr1(1), of a "a2 a", symmetric]
           robdd_\<alpha>_invar_greater [OF invars_lr1(2), of a "a1 a", symmetric]
           robdd_\<alpha>_invar_greater [OF invars_lr2(1), of a "a2 a", symmetric]
           robdd_\<alpha>_invar_greater [OF invars_lr2(2), of a "a1 a", symmetric]
           sem_eq_a[of "a1 a"] sem_eq_a[of "a2 a"]
      have a12_sem : "robdd_\<alpha> l1 (a1 a) = robdd_\<alpha> l1 a" "robdd_\<alpha> l2 (a1 a) = robdd_\<alpha> l2 a"
                     "robdd_\<alpha> r1 (a2 a) = robdd_\<alpha> r1 a" "robdd_\<alpha> r2 (a2 a) = robdd_\<alpha> r2 a"
                     "robdd_\<alpha> l1 (a2 a) = robdd_\<alpha> l1 a" "robdd_\<alpha> l2 (a2 a) = robdd_\<alpha> l2 a"
                     "robdd_\<alpha> r1 (a1 a) = robdd_\<alpha> r1 a" "robdd_\<alpha> r2 (a2 a) = robdd_\<alpha> r2 a"
                     "v1 \<noteq> v2 \<Longrightarrow> robdd_\<alpha> r1 a = robdd_\<alpha> (robdd_var i2 l2 v2 r2) a"
                     "v1 \<noteq> v2 \<Longrightarrow> robdd_\<alpha> l1 a = robdd_\<alpha> (robdd_var i2 l2 v2 r2) a"
        unfolding a1_def a2_def by simp_all
    } note a12_sem = this

    from a12_sem(9,10) have "v1 \<noteq> v2 \<Longrightarrow> robdd_\<alpha> l1 = robdd_\<alpha> r1"
       by (simp add: fun_eq_iff)
    with sem_neq have v2_eq: "v2 = v1" by metis

    { fix a
      from sem_eq_a[of "a1 a"] sem_eq_a[of "a2 a"] a12_sem[of a]
      have "robdd_\<alpha> l1 a = robdd_\<alpha> l2 a \<and> robdd_\<alpha> r1 a = robdd_\<alpha> r2 a"
        by (simp add: v2_eq a12_eval)
    }
    hence "v1 = v2 \<and> robdd_\<alpha> l1 = robdd_\<alpha> l2 \<and> robdd_\<alpha> r1 = robdd_\<alpha> r2"
      by (simp add: fun_eq_iff v2_eq)
  } note aux = this

  show ?thesis
  proof (cases "v1 \<le> v2")
    case True note v1_le = this
    from aux[OF invars_b1[unfolded robdd_invar_vars_def] invars_b2[unfolded robdd_invar_vars_def] sem_neq_b1 sem_eq v1_le]
    show ?thesis by simp
  next
    case False
    hence v2_le: "v2 \<le> v1" by simp
    from aux[OF invars_b2[unfolded robdd_invar_vars_def] invars_b1[unfolded robdd_invar_vars_def] sem_neq_b2 sem_eq[symmetric] v2_le]
    show ?thesis by simp
  qed
qed

lemma robdd_equiv_implies_sem_equiv :
  "robdd_equiv b1 b2 \<Longrightarrow> robdd_\<alpha> b1 = robdd_\<alpha> b2"
proof (induct b1 arbitrary: b2)
  case (robdd_var i l v r)
  note ind_hyp_l = robdd_var(1) 
  note ind_hyp_r = robdd_var(2) 
  note equiv_b2 = robdd_var(3)

  from equiv_b2 obtain i' l' r' where
    b2_eq: "b2 = robdd_var i' l' v r'" and
    equiv_l: "robdd_equiv l l'" and
    equiv_r: "robdd_equiv r r'"
    unfolding robdd_equiv.simps by blast 

  from ind_hyp_l[OF equiv_l] ind_hyp_r[OF equiv_r] b2_eq
  show ?case by simp
qed simp_all

lemma sem_equiv_implies_robdd_equiv :
assumes "robdd_invar_vars b1" "robdd_invar_reduced b1"
    and "robdd_invar_vars b2" "robdd_invar_reduced b2"
    and "robdd_\<alpha> b1 = robdd_\<alpha> b2"
shows "robdd_equiv b1 b2"
using assms
proof (induct "(b1, b2)" arbitrary: b1 b2 rule: measure_induct_rule [of "\<lambda>(b1,b2). size_robdd b1 + size_robdd b2"])
  case less 
  note ind_hyp = less(1)
  note invars_b1 = less(2,3)
  note invars_b2 = less(4,5)
  note sem_eq = less(6)

  show ?case
  proof (cases b1)
    case (robdd_leaf f) thus ?thesis using robdd_unique_leaf[OF invars_b2] sem_eq by simp
  next
    case (robdd_var i1 l1 v1 r1) note b1_eq = this

    show ?thesis
    proof (cases b2)
      case (robdd_leaf f) thus ?thesis using robdd_unique_leaf[OF invars_b1] sem_eq
        by (simp add: fun_eq_iff)
    next
      case (robdd_var i2 l2 v2 r2) note b2_eq = this

      from invars_b1 invars_b2
      have invars_sub: "robdd_invar_vars l1" "robdd_invar_vars r1" 
                       "robdd_invar_vars l2" "robdd_invar_vars r2" 
                       "robdd_invar_reduced l1" "robdd_invar_reduced r1" 
                       "robdd_invar_reduced l2" "robdd_invar_reduced r2" 
           "\<not>(robdd_equiv l1 r1)" "\<not>(robdd_equiv l2 r2)"
        unfolding b1_eq b2_eq by (simp_all add: robdd_invar_vars_def) (metis robdd_invar_vars_def robdd_invar_vars_impl)+

      have aux: "v1 = v2 \<and> robdd_\<alpha> l1 = robdd_\<alpha> l2 \<and> robdd_\<alpha> r1 = robdd_\<alpha> r2" 
      proof (rule robdd_unique_var[OF invars_b1[unfolded b1_eq] invars_b2[unfolded b2_eq]])
        show "robdd_\<alpha> (robdd_var i1 l1 v1 r1) = robdd_\<alpha> (robdd_var i2 l2 v2 r2)"
           using invars_b1 invars_b2 sem_eq unfolding b1_eq b2_eq by simp_all
      next
        show "robdd_\<alpha> l1 \<noteq> robdd_\<alpha> r1"
        proof (rule notI)   
          assume l1_\<alpha>_eq: "robdd_\<alpha> l1 = robdd_\<alpha> r1"
          with ind_hyp [of l1 r1] invars_sub 
          show False by (simp add: b1_eq b2_eq l1_\<alpha>_eq)
        qed
      next
        show "robdd_\<alpha> l2 \<noteq> robdd_\<alpha> r2"
        proof (rule notI)   
          assume l2_\<alpha>_eq: "robdd_\<alpha> l2 = robdd_\<alpha> r2"
          with ind_hyp [of l2 r2] invars_sub 
          show False by (simp add: b1_eq b2_eq l2_\<alpha>_eq)
        qed
      qed

      with aux ind_hyp [of l1 l2] 
               ind_hyp [of r1 r2] invars_sub
      show ?thesis by (simp_all add: b1_eq b2_eq)
    qed
  qed
qed

lemma robdd_equiv_alt_def_full :
assumes "robdd_invar_vars b1" "robdd_invar_reduced b1"
    and "robdd_invar_vars b2" "robdd_invar_reduced b2"
shows "robdd_equiv b1 b2 \<longleftrightarrow> robdd_\<alpha> b1 = robdd_\<alpha> b2"
by (metis robdd_equiv_implies_sem_equiv sem_equiv_implies_robdd_equiv[OF assms])

lemma robdd_equiv_alt_def :
assumes "robdd_invar b1"
    and "robdd_invar b2"
shows "robdd_equiv b1 b2 \<longleftrightarrow> robdd_\<alpha> b1 = robdd_\<alpha> b2"
using assms
apply (rule_tac robdd_equiv_alt_def_full)
apply (simp_all add: robdd_invar_def robdd_invar_ext_def robdd_invar_vars_def)
done

lemma robdd_unique :
assumes "robdd_invar b1"
    and "robdd_invar b2"
    and "robdd_invar_ids bs"
    and "b1 \<in> bs" "b2 \<in> bs"
shows "robdd_\<alpha> b1 = robdd_\<alpha> b2 \<longleftrightarrow> b1 = b2"
using robdd_equiv_alt_def [OF assms(1,2)]
      robdd_invar_ids_equiv_implies_eq[of bs, OF assms(3,4,5)]
by blast

lemma robdd_invar_ids_equal_intro :
assumes bs_OK: "\<And>b. b \<in> bs \<Longrightarrow> robdd_invar b"
    and weak_invar: "robdd_invar_ids bs"
shows "robdd_invar_ids_equal bs"
proof -  
  { fix b1 b2
    assume b1_in: "b1 \<in> subrobdds_set bs" and b2_in: "b2 \<in> subrobdds_set bs"
    hence "robdd_invar b1 \<and> robdd_invar b2"
      by (metis robdd_invar_subrobdds_set bs_OK)
    with robdd_unique[of b1 b2 "subrobdds_set bs"] b1_in b2_in weak_invar
    have "(robdd_\<alpha> b1 = robdd_\<alpha> b2) = (b1 = b2)" by (simp add: robdd_invar_ids_expand)
  }
  with weak_invar show ?thesis
    unfolding robdd_invar_ids_equal_def robdd_invar_ids_def
    by (simp)
qed

lemma robdd_invar_ids_full_equal_intro :
assumes bs_OK: "\<And>b. b \<in> bs \<Longrightarrow> robdd_invar b"
    and weak_invar: "robdd_invar_ids_full bs"
shows "robdd_invar_ids_full_equal bs"
unfolding robdd_invar_ids_full_equal_alt_def
apply (rule robdd_invar_ids_equal_intro)
apply (simp, elim disjE)
apply (simp)
apply (simp)
apply (simp add: bs_OK)
apply (simp add: robdd_invar_ids_full_alt_def[symmetric] weak_invar)
done


subsection \<open>Variable dependency\<close>

text \<open>ROBDDs talk about assignments that consider infinitely many variables. However,
the result depends only on a finite set of variables. Let's have a closer look at these
variables.\<close>

definition robdd_depends_on_var where
  "robdd_depends_on_var v b \<longleftrightarrow> (\<exists>a. robdd_\<alpha> b (a(v := True)) \<noteq> robdd_\<alpha> b (a(v := False)))"

lemma robdd_depends_on_varI :
  "robdd_\<alpha> b (a(v := True)) \<noteq> robdd_\<alpha> b (a(v := False)) \<Longrightarrow>
   robdd_depends_on_var v b"
unfolding robdd_depends_on_var_def by auto

lemma robbd_depends_on_var_leaf [simp] :
  "\<not>(robdd_depends_on_var v (robdd_leaf f))"
by (simp_all add: robdd_depends_on_var_def fun_eq_iff)

lemma robdd_depends_on_var_invar_greater:
assumes invar: "robdd_invar_vars_greater n b"
    and m_less: "m < n"
   shows "\<not>(robdd_depends_on_var m b)"
proof -
  { fix a f

    have "robdd_\<alpha> b (a(m := f)) = robdd_\<alpha> b a"
      apply (rule robdd_\<alpha>_invar_greater[OF invar, of "a(m := f)" a])
      apply (insert m_less)
      apply (simp)
    done
  }
  thus ?thesis by (simp add: robdd_depends_on_var_def)
qed

lemma robbd_depends_on_var_var_impl1 :
assumes depend: "robdd_depends_on_var v (robdd_var i l v' r)"
shows "(v = v') \<or> robdd_depends_on_var v l \<or> robdd_depends_on_var v r"
proof (cases "v = v'")
  case True thus ?thesis by simp
next
  case False note v_neq = this

  from depend obtain a where a_props: 
    "(if a v' then robdd_\<alpha> l (a(v := True)) else robdd_\<alpha> r (a(v := True))) \<noteq>
     (if a v' then robdd_\<alpha> l (a(v := False)) else robdd_\<alpha> r (a(v := False)))" 
    unfolding robdd_depends_on_var_def by (auto simp add: v_neq v_neq[symmetric])

  show ?thesis
  proof (cases "a v'")
    case True note a_v'_eq = this

    have "robdd_depends_on_var v l"
      apply (rule robdd_depends_on_varI[of _ a])
      apply (insert a_props a_v'_eq)
      apply (simp)
    done
    thus ?thesis by simp
  next
    case False note a_v'_eq = this

    have "robdd_depends_on_var v r"
      apply (rule robdd_depends_on_varI[of _ a])
      apply (insert a_props a_v'_eq)
      apply (simp)
    done
    thus ?thesis by simp
  qed
qed

lemma robbd_depends_on_var_var :
assumes invar: "robdd_invar (robdd_var i l v' r)"
shows "robdd_depends_on_var v (robdd_var i l v' r) \<longleftrightarrow>
       (v = v') \<or> robdd_depends_on_var v l \<or> robdd_depends_on_var v r"
proof (cases "v = v'")
  case True note v_eq = this

  from invar 
      have invar_greater: "robdd_invar_vars_greater (Suc v) l" "robdd_invar_vars_greater (Suc v) r"
     unfolding robdd_invar_def robdd_invar_ext_def v_eq by simp_all

  from invar robdd_equiv_alt_def[of l r]
  have "robdd_\<alpha> l \<noteq> robdd_\<alpha> r" by (metis robdd_invar_simps_var)
  then obtain a where not_equiv: "robdd_\<alpha> l a \<noteq> robdd_\<alpha> r a" by (simp add: fun_eq_iff) metis

  from robdd_\<alpha>_invar_greater[OF invar_greater(1), of "a (v := True)" a]
  have l_eval: "robdd_\<alpha> l (a(v := True)) = robdd_\<alpha> l a" by simp

  from robdd_\<alpha>_invar_greater[OF invar_greater(2), of "a (v := False)" a]
  have r_eval: "robdd_\<alpha> r (a(v := False)) = robdd_\<alpha> r a" by simp

  show ?thesis 
    apply (simp add: v_eq[symmetric] robdd_depends_on_var_def)
    apply (rule exI [where x = a])
    apply (insert not_equiv)
    apply (simp add: r_eval l_eval)
  done
next
  case False note v_neq = this

  from invar have invar_greater: "robdd_invar_vars_greater (Suc v') l" "robdd_invar_vars_greater (Suc v') r"
     unfolding robdd_invar_def robdd_invar_ext_def by simp_all

  { fix a f1 f2

    from robdd_\<alpha>_invar_greater[OF invar_greater(1), of "a (v' := f1, v := f2)" "a (v := f2)"] 
         robdd_\<alpha>_invar_greater[OF invar_greater(2), of "a (v' := f1, v := f2)" "a (v := f2)"] 
    have "robdd_\<alpha> l (a(v' := f1, v := f2)) = robdd_\<alpha> l (a (v:=f2))" 
         "robdd_\<alpha> r (a(v' := f1, v := f2)) = robdd_\<alpha> r (a (v:=f2))" by simp_all
  } note robdd_\<alpha>_lr_modified = this

  show ?thesis
  proof (cases "robdd_depends_on_var v l")
    case True note depends_on_l = this

    from depends_on_l
    obtain a where not_equiv: "robdd_\<alpha> l (a(v := True)) \<noteq> robdd_\<alpha> l (a(v := False))" 
      unfolding robdd_depends_on_var_def by metis

    have "robdd_depends_on_var v (robdd_var i l v' r)"
       unfolding robdd_depends_on_var_def 
       apply (simp add: v_neq[symmetric]) 
       apply (rule exI [where x = "a (v':=True)"])
       apply (insert not_equiv)
       apply (simp add: robdd_\<alpha>_lr_modified)
    done
    thus ?thesis by (simp add: depends_on_l)
  next
    case False note not_depends_on_l = this
    hence l_simp: "\<And>a. robdd_\<alpha> l (a(v := True)) = robdd_\<alpha> l (a(v := False))" 
       unfolding robdd_depends_on_var_def by simp

    { fix a 
      assume "robdd_\<alpha> r (a(v := True)) \<noteq> robdd_\<alpha> r (a(v := False))"
      hence "robdd_\<alpha> r (a(v' := False, v := True)) \<noteq> robdd_\<alpha> r (a(v' := False, v := False))"
       by (simp add: robdd_\<alpha>_lr_modified)
    }
    thus ?thesis
       unfolding robdd_depends_on_var_def 
       apply (simp add: v_neq[symmetric] v_neq l_simp) 
       by (metis fun_upd_same)
  qed
qed

primrec robdd_used_vars where
   "robdd_used_vars (robdd_leaf f) = {}"
 | "robdd_used_vars (robdd_var i l v r) = robdd_used_vars l \<union> {v} \<union> robdd_used_vars r"

lemma robdd_depends_on_var_eq_used :
  "robdd_invar b \<Longrightarrow>
   robdd_depends_on_var v b \<longleftrightarrow> v \<in> robdd_used_vars b"
proof (induct b)
  case (robdd_leaf f)
  thus ?case by (simp add: robdd_depends_on_var_def)
next
  case (robdd_var i l v' r) 
  note indhyp_l = robdd_var(1)
  note indhyp_r = robdd_var(2)

  note invar_b = robdd_var(3)
  from invar_b have invar_l: "robdd_invar l" and invar_r: "robdd_invar r" by (metis robdd_invar_simps_var)+

  from robbd_depends_on_var_var[OF invar_b, of v] indhyp_l[OF invar_l] indhyp_r[OF invar_r]
  show ?case by simp
qed

lemma robdd_depends_on_var_implies_used :
  "robdd_depends_on_var v b \<Longrightarrow> v \<in> robdd_used_vars b"
apply (induct b)
apply (simp_all)
apply (metis robbd_depends_on_var_var_impl1)
done


subsection \<open>Inverse Map\<close>

text \<open>If the invariant for ids is satisfied, one can find a find a unique mapping between ids
and ROBDDs.\<close>

definition robdd_id_map_OK where
   "robdd_id_map_OK bs m \<longleftrightarrow> (\<forall>b \<in> subrobdds_set bs. m (robdd_get_id b) = Some b)"

lemma robdd_id_map_OK_D :
  "\<lbrakk>robdd_id_map_OK bs m; b \<in> subrobdds_set bs\<rbrakk> \<Longrightarrow> m (robdd_get_id b) = Some b"
unfolding robdd_id_map_OK_def by blast

definition robdd_id_map where
  "robdd_id_map bs i = Eps_Opt (\<lambda>b. b \<in> subrobdds_set bs \<and> robdd_get_id b = i)"

lemma robdd_id_map_properties :
shows "robdd_invar_ids_equal bs \<longleftrightarrow> (robdd_id_map_OK bs (robdd_id_map bs))"
proof
  assume ids_strong: "robdd_invar_ids_equal bs"

  { fix b1 b2
    assume "b1 \<in> subrobdds_set bs"

    with ids_strong 
    have "b2 \<in> subrobdds_set bs \<and> robdd_get_id b2 = robdd_get_id b1 \<longleftrightarrow> b2 = b1"
      unfolding robdd_invar_ids_equal_def by metis
  }
  thus "robdd_id_map_OK bs (robdd_id_map bs)"
    unfolding robdd_id_map_OK_def robdd_id_map_def
    by simp
next
  assume map_OK: "robdd_id_map_OK bs (robdd_id_map bs)"

  show "robdd_invar_ids_equal bs"
    unfolding robdd_invar_ids_equal_def
  proof (intro allI impI iffI, elim conjE)
    fix b1 b2
    assume b1_in: "b1 \<in> subrobdds_set bs"
    assume b2_in: "b2 \<in> subrobdds_set bs"
    assume id_eq: "robdd_get_id b1 = robdd_get_id b2"
    
    let ?P = "\<lambda>b b'. b' \<in> subrobdds_set bs \<and> robdd_get_id b' = robdd_get_id b"

    from map_OK b1_in b2_in have Eps_Opt_Eval: "Eps_Opt (?P b1) = Some b1"  "Eps_Opt (?P b2) = Some b2" 
       unfolding robdd_id_map_OK_def robdd_id_map_def by simp_all

    from id_eq have "?P b1 = ?P b2" by simp
    with Eps_Opt_Eval show "b1 = b2" by (metis option.inject)
  qed simp
qed

lemma robdd_id_map_union :
assumes invar_ids_bs12: "robdd_invar_ids_equal (bs1 \<union> bs2)"
shows "robdd_id_map (bs1 \<union> bs2) = (robdd_id_map bs1) ++ (robdd_id_map bs2)"
proof 
  fix i
  from invar_ids_bs12 
  have invar_ids_bs1: "robdd_invar_ids_equal bs1" 
   and invar_ids_bs2: "robdd_invar_ids_equal bs2"
     unfolding robdd_invar_ids_equal_def
     by auto
  
  from invar_ids_bs1 invar_ids_bs2 invar_ids_bs12 robdd_id_map_properties
  have map_OK_bs1: "robdd_id_map_OK bs1 (robdd_id_map bs1)"
   and map_OK_bs2: "robdd_id_map_OK bs2 (robdd_id_map bs2)" 
   and map_OK_bs12: "robdd_id_map_OK (bs1 \<union> bs2) (robdd_id_map (bs1 \<union> bs2))" 
    by simp_all

  show "robdd_id_map (bs1 \<union> bs2) i = (robdd_id_map bs1 ++ robdd_id_map bs2) i"
  proof (cases "\<exists>b. b \<in> subrobdds_set (bs1 \<union> bs2) \<and> robdd_get_id b = i")
    case False 
    hence "robdd_id_map (bs1 \<union> bs2) i = None" and
          "robdd_id_map bs1 i = None" and
          "robdd_id_map bs2 i = None"
      unfolding robdd_id_map_def Eps_Opt_eq_None by auto
    thus ?thesis by (simp add: map_add_find_left)
  next
    case True then obtain b where 
        b_in: "b \<in> subrobdds_set (bs1 \<union> bs2)" 
    and b_id: "robdd_get_id b = i" by auto

    from map_OK_bs12 b_in b_id
    have ls_eq: "robdd_id_map (bs1 \<union> bs2) i = Some b"
      unfolding robdd_id_map_OK_def by metis

    have rs_eq: "(robdd_id_map bs1 ++ robdd_id_map bs2) i = Some b"
    proof (cases "b \<in> subrobdds_set bs2")
      case True
      with map_OK_bs2 b_id 
      have rs_eq2: "robdd_id_map bs2 i = Some b"
        unfolding robdd_id_map_OK_def by metis
      from ls_eq rs_eq2 show ?thesis by simp
    next
      case False note b_nin_bs2 = this

      from b_in b_nin_bs2 have "b \<in> subrobdds_set bs1" by simp
      with map_OK_bs1 b_id have rs_eq1: "robdd_id_map bs1 i = Some b"
        unfolding robdd_id_map_OK_def by metis

      from invar_ids_bs12 b_in b_nin_bs2 b_id have "\<And>b'. b' \<in> subrobdds_set bs2 \<Longrightarrow> robdd_get_id b' \<noteq> i"
        unfolding robdd_invar_ids_equal_def by simp metis
      hence rs_eq2: "robdd_id_map bs2 i = None"
        unfolding robdd_id_map_def Eps_Opt_eq_None by auto

      from ls_eq rs_eq1 rs_eq2 show ?thesis by (simp add: map_add_find_left)
    qed

    from ls_eq rs_eq show ?thesis by simp
  qed
qed


subsection \<open>Extended Boolean Operations\<close>

text \<open>For Boolean Operations on ROBDDs it is important to extend boolean operations
to option types. This allows to get the information that the result of the operation does
not depend on the value of some arguments.\<close>

fun bool_op_extend :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 
                                (bool option \<Rightarrow> bool option \<Rightarrow> bool option)" where
    "bool_op_extend bop None None =
       (if ((bop True False = bop True True) \<and> 
            (bop False True = bop True True) \<and> 
            (bop False False = bop True True)) then Some (bop True True) else None)" 
  | "bool_op_extend bop None (Some b') = 
       (if (bop True b' \<longleftrightarrow> bop False b') then Some (bop False b') else None)"
  | "bool_op_extend bop (Some b) None =
       (if (bop b True \<longleftrightarrow> bop b False) then Some (bop b True) else None)"
  | "bool_op_extend bop (Some b) (Some b') = Some (bop b b')"

text \<open>Common Operations\<close>

fun bope_neg where
   "bope_neg None = None"
 | "bope_neg (Some True) = Some False"
 | "bope_neg (Some False) = (Some True)"

definition "bope_and = bool_op_extend (\<lambda>x y. x \<and> y)"
definition "bope_or = bool_op_extend (\<lambda>x y. x \<or> y)"
definition "bope_nand = bool_op_extend (\<lambda>x y. \<not>(x \<and> y))"
definition "bope_nor = bool_op_extend (\<lambda>x y. \<not>(x \<or> y))"
definition "bope_xor = bool_op_extend (\<lambda>x y. x \<noteq> y)"
definition "bope_eq = bool_op_extend (\<lambda>x y. x = y)"
definition "bope_imp = bool_op_extend (\<lambda>x y. x \<longrightarrow> y)"

lemma bool_opt_exhaust:
  "(y = None \<Longrightarrow> P) \<Longrightarrow> (y = Some True \<Longrightarrow> P) \<Longrightarrow> (y = Some False \<Longrightarrow> P) \<Longrightarrow> P"
by auto 
 
lemma bope_and_code [code] :
   "bope_and None None = None"
   "bope_and bo (Some True) = bo"
   "bope_and bo (Some False) = (Some False)"
   "bope_and (Some True) bo = bo"
   "bope_and (Some False) bo = (Some False)"
unfolding bope_and_def
  apply (case_tac [!] bo  rule: bool_opt_exhaust)
  apply (simp_all)
done

lemma bope_or_code [code] :
   "bope_or None None = None"
   "bope_or bo (Some False) = bo"
   "bope_or bo (Some True) = (Some True)"
   "bope_or (Some False) bo = bo"
   "bope_or (Some True) bo = (Some True)"
unfolding bope_or_def
  apply (case_tac [!] bo  rule: bool_opt_exhaust)
  apply (simp_all)
done

lemma bope_nand_code [code] :
   "bope_nand None None = None"
   "bope_nand bo (Some False) = (Some True)"
   "bope_nand (Some False) bo = (Some True)"
   "bope_nand (Some True) (Some True) = (Some False)"
   "bope_nand None (Some True) = None"
   "bope_nand (Some True) None = None"
unfolding bope_nand_def
  apply (case_tac [!] bo  rule: bool_opt_exhaust)
  apply (simp_all)
done

lemma bope_nor_code [code] :
   "bope_nor None None = None"
   "bope_nor bo (Some True) = (Some False)"
   "bope_nor (Some True) bo = (Some False)"
   "bope_nor (Some False) (Some False) = (Some True)"
   "bope_nor None (Some False) = None"
   "bope_nor (Some False) None = None"
unfolding bope_nor_def
  apply (case_tac [!] bo  rule: bool_opt_exhaust)
  apply (simp_all)
done

lemma bope_eq_code [code] :
   "bope_eq None bo = None"
   "bope_eq bo None = None"
   "bope_eq (Some True)  (Some True)  = Some True"
   "bope_eq (Some True)  (Some False) = Some False"
   "bope_eq (Some False) (Some True)  = Some False"
   "bope_eq (Some False) (Some False) = Some True"
unfolding bope_eq_def
  apply (case_tac [!] bo  rule: bool_opt_exhaust)
  apply (simp_all)
done

lemma bope_xor_code [code] :
   "bope_xor None bo = None"
   "bope_xor bo None = None"
   "bope_xor (Some True)  (Some True)  = Some False"
   "bope_xor (Some True)  (Some False) = Some True"
   "bope_xor (Some False) (Some True)  = Some True"
   "bope_xor (Some False) (Some False) = Some False"
unfolding bope_xor_def
  apply (case_tac [!] bo  rule: bool_opt_exhaust)
  apply (simp_all)
done

lemma bope_imp_code [code] :
   "bope_imp None None = None"
   "bope_imp None (Some True) = Some True"
   "bope_imp None (Some False) = None"
   "bope_imp (Some True) bo = bo"
   "bope_imp (Some False) bo = (Some True)"
unfolding bope_imp_def
  apply (case_tac [!] bo  rule: bool_opt_exhaust)
  apply (simp_all)
done


subsection \<open>Implementing boolean Combination\<close>

text \<open>For building boolean combinations of BDDs it is essential to use
a map storing already used IDs and a cache. 
These datastructures cache can be implemented in different ways. Therefore, here the
needed properties are abstracted by using a locale.\<close>

locale robdd_locale = 
  c: map_empty c_\<alpha> c_invar c_empty +
  c: map_lookup c_\<alpha> c_invar c_lookup +
  c: map_update c_\<alpha> c_invar c_update +
  r: map_empty r_\<alpha> r_invar r_empty +
  r: map_lookup r_\<alpha> r_invar r_lookup +
  r: map_update_dj r_\<alpha> r_invar r_update 
  for c_\<alpha> :: "'c_map \<Rightarrow> (nat \<times> nat \<Rightarrow> robdd option)" and
      c_invar c_empty c_lookup c_update and
      r_\<alpha> :: "'r_map \<Rightarrow> (nat \<times> nat \<times> nat \<Rightarrow> robdd option)" and
      r_invar r_empty r_lookup r_update
  begin

  definition rev_map_invar where
     "rev_map_invar bs rev_map = (r_invar (fst rev_map) \<and> snd rev_map > 1 \<and>
        (\<forall>b \<in> subrobdds_set bs. robdd_invar_ext bs 0 b \<and> robdd_get_id b < (snd rev_map)) \<and>
        (\<forall>li v ri b. r_\<alpha> (fst rev_map) (li, v, ri) = Some b \<longrightarrow> 
               (robdd_invar_ext bs v b \<and> b \<in> bs \<and>
                (\<exists>l r i. b = robdd_var i l v r \<and>  
                         robdd_get_id l = li \<and> robdd_get_id r = ri))) \<and>
        (\<forall>i l r v. robdd_var i l v r \<in> subrobdds_set bs \<longrightarrow>
                   r_\<alpha> (fst rev_map) (robdd_get_id l, v, robdd_get_id r) = Some (robdd_var i l v r)))"

  lemma rev_map_invar_empty: 
     "rev_map_invar {} (r_empty(), 2)"
    unfolding rev_map_invar_def by (simp add: r.empty_correct)

  lemma rev_map_invarI[intro!] :
     "\<lbrakk>r_invar (fst rev_map); snd rev_map > 1;
       \<And>b. b \<in> subrobdds_set bs \<Longrightarrow> robdd_invar_ext bs 0 b \<and> robdd_get_id b < (snd rev_map);
       \<And>li v ri b. r_\<alpha> (fst rev_map) (li, v, ri) = Some b \<Longrightarrow> 
               (robdd_invar_ext bs v b \<and> b \<in> bs \<and>
                (\<exists>l r i. b = robdd_var i l v r \<and>  
                         robdd_get_id l = li \<and> robdd_get_id r = ri));
       \<And>i l r v. robdd_var i l v r \<in> subrobdds_set bs \<Longrightarrow>
                   r_\<alpha> (fst rev_map) (robdd_get_id l, v, robdd_get_id r) = Some (robdd_var i l v r)\<rbrakk> \<Longrightarrow>
       rev_map_invar bs rev_map"
    unfolding rev_map_invar_def by blast

  lemma rev_map_invar_D1 :
  assumes "rev_map_invar bs rev_map"
      and "robdd_var i l v r \<in> subrobdds_set bs"
   shows "r_\<alpha> (fst rev_map) (robdd_get_id l, v, robdd_get_id r) = Some (robdd_var i l v r)"
   using assms unfolding rev_map_invar_def by blast                            

  lemma rev_map_invar_D2 :
  assumes "rev_map_invar bs rev_map"
      and "r_\<alpha> (fst rev_map) (li, v, ri) = Some b"
   shows "robdd_invar_ext bs v b \<and> b \<in> bs \<and>
          (\<exists>l r i. b = robdd_var i l v r \<and>  
                      robdd_get_id l = li \<and> robdd_get_id r = ri)"
   using assms unfolding rev_map_invar_def by blast                            

  lemma rev_map_invar_D3 :
  assumes "rev_map_invar bs rev_map"
      and "b \<in> subrobdds_set bs"
   shows "robdd_invar_ext bs 0 b" "robdd_get_id b < snd (rev_map)"
   using assms unfolding rev_map_invar_def by blast+                           

  lemma rev_map_invar_implies_invar_ids :
     assumes invar: "rev_map_invar bs rev_map"
       shows "robdd_invar_ids bs"
  proof (cases "bs = {}")
    case True thus ?thesis by (simp add: robdd_invar_ids_def subrobdds_set_def)
  next
    case False 
    then obtain b where "b \<in> bs" by auto
    then have b_in: "b \<in> subrobdds_set bs" 
      unfolding subrobdds_set_def by rule simp
    from rev_map_invar_D3(1)[OF invar b_in]
    show ?thesis by (simp add: robdd_invar_ext_def)
  qed

  lemma rev_map_invar_implies_invar_bs :
     assumes invar: "rev_map_invar bs rev_map"
         and b_in: "b \<in> subrobdds_set bs"
       shows "robdd_invar b"
  using rev_map_invar_D3(1)[OF invar b_in]
  by (rule robdd_invar_impl)

  lemma rev_map_invar_implies_invar_ids_equal :
     assumes invar: "rev_map_invar bs rev_map"
       shows "robdd_invar_ids_equal bs"
  proof -
    note invar_ids = rev_map_invar_implies_invar_ids[OF invar]

    note bs_OK_full = rev_map_invar_implies_invar_bs[OF invar]
    have bs_OK: "\<And>b. b \<in> bs \<Longrightarrow> robdd_invar b" 
      by (metis bs_OK_full subrobdds_set_mono subsetD)

    show "robdd_invar_ids_equal bs"
      by (rule robdd_invar_ids_equal_intro [OF bs_OK invar_ids])
  qed

  definition robdd_construct :: "'r_map \<times> node_id \<Rightarrow> robdd \<Rightarrow> var \<Rightarrow> robdd \<Rightarrow> robdd \<times> ('r_map \<times> node_id)" where
    "robdd_construct rev_map l v r =
     (let l_id = robdd_get_id l in
      let r_id = robdd_get_id r in
      (if l_id = r_id then (l, rev_map) else
       (case r_lookup (l_id, v, r_id) (fst rev_map) of
           Some b \<Rightarrow> (b, rev_map) 
         | None \<Rightarrow> (let b = robdd_var (snd rev_map) l v r in
                    (b, (r_update (l_id, v, r_id) b (fst rev_map), Suc (snd rev_map)))))))"

  lemma robdd_construct_correct :
  fixes l v r bs rev_map
  defines "res \<equiv> robdd_construct rev_map l v r"
  defines "rev_map' \<equiv> (snd res)"
  defines "b \<equiv> fst res"
  defines "bs' \<equiv> insert b bs"
  assumes invar_rev_map: "rev_map_invar bs rev_map"
      and lr_in: "l \<in> bs" "r \<in> bs"
      and invar_lr: "robdd_invar_ext bs (Suc v) l" "robdd_invar_ext bs (Suc v) r"
  shows "robdd_invar_ext bs' v b \<and> rev_map_invar bs' rev_map' \<and>
         robdd_\<alpha> b = robdd_\<alpha> (robdd_var 0 l v r)"
  proof -
    define l_id where "l_id = robdd_get_id l"
    define r_id where "r_id = robdd_get_id r"

    note bs_OK = rev_map_invar_implies_invar_bs[OF invar_rev_map] 

    from invar_lr have invar_ids: "robdd_invar_ids bs"
     and lr_in': "l \<in> subrobdds_set bs" "r \<in> subrobdds_set bs"
     unfolding robdd_invar_ext_def by simp_all

    from robdd_invar_ids_equal_intro[of bs, OF bs_OK invar_ids]
         subrobdds_set_mono[of bs]
    have invar_ids_equal: "robdd_invar_ids_equal bs" by (simp add: subset_iff)

    from invar_rev_map have r_invar: "r_invar (fst rev_map)" unfolding rev_map_invar_def by simp

    show ?thesis
    proof (cases "l_id = r_id")
      case True note l_id_eq = this

      from lr_in' invar_ids l_id_eq have l_\<alpha>: "robdd_\<alpha> l = robdd_\<alpha> r"
        unfolding robdd_invar_ids_def l_id_def r_id_def by simp

      from invar_lr(1) have invar_l': "robdd_invar_ext bs v l"
        apply (rule robdd_invar_ext_weaken_var)
        apply (simp)
      done
      from lr_in(1) have bs'_eq: "insert l bs = bs" by auto         
      from res_def l_id_eq show ?thesis
        unfolding robdd_construct_def l_id_def[symmetric] r_id_def[symmetric]
                  b_def bs'_def rev_map'_def
        by (simp add: fun_eq_iff l_\<alpha> bs'_eq invar_lr(1) invar_rev_map invar_l')
    next
      case False note l_id_neq = this

      show ?thesis
      proof (cases "r_lookup (l_id, v, r_id) (fst rev_map)")
        case (Some b) note map_eq = this

        from r_invar rev_map_invar_D2[OF invar_rev_map, of l_id v r_id b] map_eq 
        obtain l' r' i where
           invar_b: "robdd_invar_ext bs v b" and
           b_in: "b \<in> bs" and
           b_eq: "b = robdd_var i l' v r'" and
           l_id_eq: "robdd_get_id l' = l_id" and 
           r_id_eq: "robdd_get_id r' = r_id"
          unfolding rev_map_invar_def by (auto simp add: r.lookup_correct) 

        from b_in have bs'_eq: "insert b bs = bs" by auto

        have b_\<alpha>: "robdd_\<alpha> b = robdd_\<alpha> (robdd_var 0 l' v r')"
          unfolding b_eq by (simp add: fun_eq_iff) 

        have lr'_eq: "l' = l" "r' = r"
        proof -
          from b_in b_eq have lr'_in': "l' \<in> subrobdds_set bs" "r' \<in> subrobdds_set bs"
            apply (simp_all add: subrobdds_set_def)
            apply (auto intro: bexI [of _ b])
            done

          from invar_ids_equal lr_in' lr'_in' l_id_eq r_id_eq 
          show "l' = l" "r' = r"
             unfolding robdd_invar_ids_equal_def l_id_def r_id_def by auto
        qed
        from res_def l_id_neq show ?thesis
        unfolding robdd_construct_def l_id_def[symmetric] r_id_def[symmetric]
                  bs'_def rev_map'_def b_def
          by (simp add: map_eq bs'_eq invar_b b_\<alpha> lr'_eq invar_rev_map)
      next
        case None note map_eq = this
        define b' where "b' = robdd_var (snd rev_map) l v r"

        have \<alpha>_b': "robdd_\<alpha> b' = robdd_\<alpha> (robdd_var 0 l v r)"
          unfolding b'_def by (simp add: fun_eq_iff)

        from lr_in' invar_ids l_id_neq have "robdd_\<alpha> l \<noteq> robdd_\<alpha> r"
          unfolding robdd_invar_ids_def l_id_def r_id_def by simp
        with robdd_equiv_implies_sem_equiv[of l r] have l_not_equiv: "~(robdd_equiv l r)" by blast

        from invar_lr
        have b'_invar_vars: "robdd_invar_vars b'" and b'_invar_reduced: "robdd_invar_reduced b'"
          unfolding b'_def robdd_invar_vars_def
          by (simp_all add: robdd_invar_ext_def l_not_equiv)
       
        { fix b2
          assume b2_in: "b2 \<in> subrobdds_set bs"

          from rev_map_invar_D3[OF invar_rev_map b2_in]
          have id_neq: "robdd_get_id b2 \<noteq> robdd_get_id b'"
            unfolding b'_def by simp

          have invar_b2: "robdd_invar b2" by (metis b2_in bs_OK)

          have \<alpha>_b2: "robdd_\<alpha> b2 \<noteq> robdd_\<alpha> b'"
          proof (rule notI)
            assume sem_eq: "robdd_\<alpha> b2 = robdd_\<alpha> b'"

            with invar_b2 robdd_equiv_alt_def_full[OF b'_invar_vars b'_invar_reduced, of b2]
            have "robdd_equiv b' b2" by (metis robdd_invar_alt_def)
            then obtain i' l' r' where 
               b2_eq: "b2 = robdd_var i' l' v r'" and
               l'_equiv: "robdd_equiv l l'" and
               r'_equiv: "robdd_equiv r r'"
              unfolding b'_def by auto

            have r'_eq[simp]: "r' = r" and l'_eq[simp]: "l' = l"
            proof -        
              have "l' \<in> subrobdds b2" "r' \<in> subrobdds b2"
                unfolding b2_eq by simp_all
              with b2_in have "l' \<in> subrobdds_set bs" "r' \<in> subrobdds_set bs"
                 by (metis subrobdds_set_subset_simp subsetD)+
              with robdd_invar_ids_equiv_implies_eq[of "subrobdds_set bs" l l']
                   robdd_invar_ids_equiv_implies_eq[of "subrobdds_set bs" r r']
              show "r' = r" "l' = l"
                by (simp_all add: l'_equiv r'_equiv robdd_invar_ids_expand invar_ids lr_in')
            qed

            from rev_map_invar_D1[OF invar_rev_map b2_in[unfolded b2_eq]] map_eq
            show "False" by (simp add: l_id_def r_id_def r.lookup_correct r_invar)
          qed
          
          note invar_b2 \<alpha>_b2 id_neq
        } note in_bs_b'_props = this

        have subrobdds_set_bs_simp: "subrobdds_set (insert b' bs) = insert b' (subrobdds_set bs)"
          unfolding subrobdds_set_def b'_def using lr_in
          by (auto simp add: set_eq_iff Bex_def)

        have invar_ids': "robdd_invar_ids (insert b' bs)" 
        proof (rule robdd_invar_idsI)
          fix b1 b2

          assume b1_in: "b1 \<in> subrobdds_set (insert b' bs)" and
                 b2_in: "b2 \<in> subrobdds_set (insert b' bs)"

          from b1_in b2_in      
          show "(robdd_\<alpha> b1 = robdd_\<alpha> b2) = (robdd_get_id b1 = robdd_get_id b2)"
            unfolding subrobdds_set_bs_simp
            using robdd_invar_idsD[OF invar_ids, of b1 b2] in_bs_b'_props
            by simp metis
        qed

        from invar_ids' b'_invar_reduced b'_invar_vars
        have invar_b': "robdd_invar_ext (insert b' bs) v b'"
          by (simp add: robdd_invar_ext_def robdd_invar_vars_def b'_def)
        
        have invar_rev_map': "rev_map_invar bs' rev_map'"
        proof -          
          let ?rm = "(r_update (l_id, v, r_id) b' (fst rev_map), Suc (snd rev_map))"
          have "rev_map_invar (insert b' bs) ?rm"
          proof 
            from map_eq
            show "r_invar (fst ?rm)" 
              apply (simp)
              apply (rule r.update_dj_correct)
              apply (simp_all add: r_invar r.lookup_correct dom_def)
            done
          next
            from invar_rev_map 
            show "1 < snd ?rm" unfolding rev_map_invar_def by simp
          next
            fix b
            assume b_in: "b \<in> subrobdds_set (insert b' bs)"
            show "robdd_invar_ext (insert b' bs) 0 b \<and> robdd_get_id b < snd ?rm"
            proof (cases "b = b'")
              case True with invar_b' show ?thesis unfolding b'_def by simp
            next
              case False 
              with subrobdds_set_bs_simp b_in 
              have b_in': "b \<in> subrobdds_set bs" by simp
                   
              from rev_map_invar_D3[OF invar_rev_map b_in']
              show ?thesis by (simp add: robdd_invar_ext_def invar_ids')
            qed
          next
            fix i l r v'
            assume b_in: "robdd_var i l v' r \<in> subrobdds_set (insert b' bs)"
            show "r_\<alpha> (fst ?rm) (robdd_get_id l, v', robdd_get_id r) =
                  Some (robdd_var i l v' r)"
            proof (cases "robdd_var i l v' r = b'")
              case True with map_eq show ?thesis
                by (simp add: b'_def l_id_def[symmetric] r_id_def[symmetric] 
                              r.lookup_correct r_invar dom_def r.update_dj_correct)
            next
              case False
              with subrobdds_set_bs_simp b_in 
              have b_in': "robdd_var i l v' r \<in> subrobdds_set bs" by simp

              from rev_map_invar_D1[OF invar_rev_map b_in'] map_eq
              show ?thesis by (auto simp add: r.lookup_correct r.update_dj_correct dom_def r_invar)
            qed
          next 
            fix li v' ri b
            assume b_intro: "r_\<alpha> (fst ?rm) (li, v', ri) = Some b"
            show "robdd_invar_ext (insert b' bs) v' b \<and> b \<in> insert b' bs \<and>
                  (\<exists>l r i. b = robdd_var i l v' r \<and> robdd_get_id l = li \<and> robdd_get_id r = ri)"
            proof (cases "(li, v', ri) = (robdd_get_id l, v, robdd_get_id r)")
              case True note lriv'_eq = this
              with b_intro map_eq have b_eq: "b = b'" 
                by (simp_all add: r.update_dj_correct dom_def r.lookup_correct r_invar l_id_def r_id_def)
              with lriv'_eq show ?thesis 
                apply (simp add: invar_b')
                apply (simp add: b'_def)
              done
            next
              case False
              with b_intro map_eq have b_intro': "r_\<alpha> (fst rev_map) (li, v', ri) = Some b"
                by (auto simp add: r.lookup_correct r.update_dj_correct dom_def r_invar l_id_def r_id_def)

              from rev_map_invar_D2[OF invar_rev_map b_intro']
              show ?thesis
                apply simp
                apply (simp add: robdd_invar_ext_def invar_ids')
              done
            qed
          qed

          thus ?thesis
          unfolding bs'_def rev_map'_def res_def robdd_construct_def l_id_def[symmetric]
                    r_id_def[symmetric] b_def
            by (simp add: map_eq b'_def[symmetric] \<alpha>_b' invar_b' l_id_neq)
        qed

        from res_def l_id_neq invar_rev_map'
        show ?thesis
          unfolding robdd_construct_def l_id_def[symmetric] r_id_def[symmetric]
                    bs'_def rev_map'_def b_def
          by (simp add: map_eq b'_def[symmetric] \<alpha>_b' invar_b' )
      qed
    qed
  qed

  fun (in -) robdd_apply_next where
     "robdd_apply_next (robdd_leaf f) (robdd_leaf f') = 
         (robdd_leaf f, robdd_leaf f, 0, robdd_leaf f', robdd_leaf f')"
   | "robdd_apply_next (robdd_leaf f) (robdd_var i l v r) = (robdd_leaf f, robdd_leaf f, v, l, r)"
   | "robdd_apply_next (robdd_var i l v r) (robdd_leaf f) = (l, r, v, robdd_leaf f, robdd_leaf f)"
   | "robdd_apply_next (robdd_var i l v r) (robdd_var i' l' v' r') = 
     (if v < v' then
       (l, r, v, (robdd_var i' l' v' r'), (robdd_var i' l' v' r'))
     else (if v = v' then
       (l, r, v, l', r')
     else
       ((robdd_var i l v r), (robdd_var i l v r), v', l', r')))"

  definition (in -) robdd_neg_next where
     "robdd_neg_next b = (let (l, r, v, _, _) = robdd_apply_next b robdd_one in (l, r, v))"

  lemma (in -) robdd_neg_simps[code, simp] :
     "robdd_neg_next (robdd_leaf f) = 
         (robdd_leaf f, robdd_leaf f, 0)"
     "robdd_neg_next (robdd_var i l v r) = (l, r, v)"
   unfolding robdd_neg_next_def by simp_all

  fun (in -) robdd_get_min_var where
     "robdd_get_min_var (robdd_leaf _) (robdd_leaf _) = 0"
   | "robdd_get_min_var (robdd_leaf _) (robdd_var _ _ v _) = v"
   | "robdd_get_min_var (robdd_var _ _ v _) (robdd_leaf _) = v"
   | "robdd_get_min_var (robdd_var _ _ v1 _) (robdd_var _ _ v2 _) = (if v1 \<le> v2 then v1 else v2)"

  lemma (in -) robdd_apply_next_correct :
    assumes invar_b1: "robdd_invar_ext bs1 n1 b1" 
        and invar_b2: "robdd_invar_ext bs2 n2 b2" 
        and eval: "robdd_apply_next b1 b2 = (b1_l, b1_r, v'', b2_l, b2_r)"
  shows "robdd_\<alpha> b1_l = (\<lambda>a. robdd_\<alpha> b1 (a (v'' := True)))"  (is ?T1)
        "robdd_\<alpha> b1_r = (\<lambda>a. robdd_\<alpha> b1 (a (v'' := False)))"  (is ?T2)
        "robdd_\<alpha> b2_l = (\<lambda>a. robdd_\<alpha> b2 (a (v'' := True)))"  (is ?T3)
        "robdd_\<alpha> b2_r = (\<lambda>a. robdd_\<alpha> b2 (a (v'' := False)))"  (is ?T4)
        "robdd_invar_ext bs1 (Suc v'') b1_l"  (is ?T5)
        "robdd_invar_ext bs1 (Suc v'') b1_r"  (is ?T6)
        "robdd_invar_ext bs2 (Suc v'') b2_l"  (is ?T7)
        "robdd_invar_ext bs2 (Suc v'') b2_r"  (is ?T8)
        "b1_l \<in> subrobdds b1" (is ?T9)
        "b2_l \<in> subrobdds b2" (is ?T10)
        "b1_r \<in> subrobdds b1" (is ?T11)
        "b2_r \<in> subrobdds b2" (is ?T12)
        "robdd_get_min_var b1 b2 = v''" (is ?T13)
        "~(robdd_is_leaf b1 \<and> robdd_is_leaf b2) \<longrightarrow>
         size_robdd b1_l + size_robdd b2_l < size_robdd b1 + size_robdd b2" (is ?T14)
        "~(robdd_is_leaf b1 \<and> robdd_is_leaf b2) \<longrightarrow> 
         size_robdd b1_r + size_robdd b2_r < size_robdd b1 + size_robdd b2" (is ?T15)
  proof -
    have "?T1 \<and> ?T2 \<and> ?T3 \<and> ?T4 \<and> ?T5 \<and> ?T6 \<and> ?T7 \<and> ?T8 \<and> ?T9 \<and> ?T10 \<and> ?T11 \<and> ?T12 \<and> ?T13 \<and> ?T14 \<and> ?T15"
    proof (cases b1)
      case (robdd_leaf f) note b1_eq = this
      show ?thesis
      proof (cases b2)
        case (robdd_leaf f') note b2_eq = this
        with b1_eq eval[symmetric] invar_b1 invar_b2 show ?thesis by (simp add: fun_eq_iff)
      next
        case (robdd_var i' l' v' r') note b2_eq = this
        with b1_eq eval[symmetric] invar_b1 invar_b2 show ?thesis 
          apply (simp add: fun_eq_iff)
          apply (intro allI conjI robdd_\<alpha>_invar_greater [of "Suc v'"])
          apply (simp_all add: robdd_invar_ext_def)
        done
      qed
    next
      case (robdd_var i l v r) note b1_eq = this
      show ?thesis
      proof (cases b2)
        case (robdd_leaf f') note b2_eq = this
        with b1_eq eval[symmetric] invar_b1 invar_b2 show ?thesis 
          apply (simp add: fun_eq_iff)
          apply (intro allI conjI robdd_\<alpha>_invar_greater [of "Suc v"])
          apply (simp_all add: robdd_invar_ext_def)
        done
      next
        case (robdd_var i' l' v' r') note b2_eq = this
        show ?thesis
        proof (cases "v < v'")
          case True 
          with robdd_invar_vars_greater___weaken[of "Suc v'" _ "Suc v"] b1_eq b2_eq eval[symmetric] invar_b1 invar_b2 show ?thesis
            apply (simp add: fun_eq_iff)
            apply (intro allI conjI impI robdd_\<alpha>_invar_greater [of "Suc v''"])
            apply (simp_all add: robdd_invar_ext_def)
          done
        next
          case False hence v'_le: "v' \<le> v" by simp
          show ?thesis
          proof (cases "v = v'")
            case True
            with robdd_invar_vars_greater___weaken[of "Suc v'" _ "Suc v"] b1_eq b2_eq eval[symmetric] invar_b1 invar_b2 show ?thesis
              apply (simp add: fun_eq_iff)
              apply (intro allI conjI impI robdd_\<alpha>_invar_greater [of "Suc v''"])
              apply (simp_all add: robdd_invar_ext_def)
            done
          next
            case False
            with v'_le have "v' < v" by simp
            with robdd_invar_vars_greater___weaken[of "Suc v" _ "Suc v'"] b1_eq b2_eq eval[symmetric] invar_b1 invar_b2 show ?thesis
              apply (simp add: fun_eq_iff)
              apply (intro allI conjI impI robdd_\<alpha>_invar_greater [of "Suc v''"])
              apply (simp_all add: robdd_invar_ext_def)
            done
          qed
        qed
      qed
    qed
    thus ?T1 ?T2 ?T3 ?T4 ?T5 ?T6 ?T7 ?T8 ?T9 ?T10 ?T11 ?T12 ?T13 ?T14 ?T15 by auto
  qed

  function robdd_apply where
    "robdd_apply apply_map rev_map bop b1 b2 = 
      (case (bool_op_extend bop (robdd_to_bool b1) (robdd_to_bool b2)) of 
         Some f \<Rightarrow> (robdd_leaf f, apply_map, rev_map)
       | None \<Rightarrow> (case c_lookup (robdd_get_id b1, robdd_get_id b2) apply_map of
            Some b3 \<Rightarrow> (b3, apply_map, rev_map)
          | None \<Rightarrow> (let (l1, r1, var, l2, r2) = robdd_apply_next b1 b2 in 
                     let (l, apply_map, rev_map) = robdd_apply apply_map rev_map bop l1 l2 in
                     let (r, apply_map, rev_map) = robdd_apply apply_map rev_map bop r1 r2 in
                     let (b, rev_map) = robdd_construct rev_map l var r in
                     let apply_map = c_update (robdd_get_id b1, robdd_get_id b2) b apply_map in
                     (b, apply_map, rev_map))))"
   by pat_completeness auto
   termination 
      apply (relation "measure (\<lambda>(_, _, _, b1, b2). size_robdd b1 + size_robdd b2)")
      apply simp
      apply (clarify, simp) 
      defer
      apply (clarify, simp) 
   proof -
     fix b1 b2 l1 l2 r1 r2 v bop
     assume bop_eq: "bool_op_extend bop (robdd_to_bool b1) (robdd_to_bool b2) = None"
        and next_eq: "(l1, r1, v, l2, r2) = robdd_apply_next b1 b2"

     hence "size_robdd l1 + size_robdd l2 < size_robdd b1 + size_robdd b2 \<and> 
           size_robdd r1 + size_robdd r2 < size_robdd b1 + size_robdd b2" 
       apply (case_tac [!] b1)
       apply (case_tac [!] b2)
       apply (simp_all split: if_splits)
     done
     thus "size_robdd l1 + size_robdd l2 < size_robdd b1 + size_robdd b2" 
          "size_robdd r1 + size_robdd r2 < size_robdd b1 + size_robdd b2" by simp_all
  qed
  declare robdd_apply.simps[simp del]

  definition apply_map_invar where
     "apply_map_invar bop bs bs1 bs2 apply_map \<longleftrightarrow>
       c_invar apply_map \<and>
       (\<forall>i1 i2 b. c_lookup (i1, i2) apply_map = Some b \<longrightarrow>
          (\<exists>b1 b2. robdd_id_map bs1 i1 = Some b1 \<and> robdd_id_map bs2 i2 = Some b2 \<and>            
                  robdd_invar_ext bs (robdd_get_min_var b1 b2) b \<and> (\<forall>a. robdd_\<alpha> b a \<longleftrightarrow> bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a))))"

  lemma apply_map_invar_empty : 
    "apply_map_invar bop bs bs1 bs2 (c_empty ())"
    unfolding apply_map_invar_def by (simp add: c.empty_correct c.lookup_correct)

  lemma apply_map_invar_I :
    "\<lbrakk>c_invar apply_map;
      \<And>i1 i2 b. c_lookup (i1, i2) apply_map = Some b \<Longrightarrow>
      \<exists>b1 b2. robdd_id_map bs1 i1 = Some b1 \<and> robdd_id_map bs2 i2 = Some b2 \<and>            
                  robdd_invar_ext bs (robdd_get_min_var b1 b2) b \<and> (\<forall>a. robdd_\<alpha> b a \<longleftrightarrow> bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a))\<rbrakk> \<Longrightarrow>
      apply_map_invar bop bs bs1 bs2 apply_map"
   unfolding apply_map_invar_def by blast

  lemma apply_map_invar_D1 :
    "apply_map_invar bop bs bs1 bs2 apply_map \<Longrightarrow> c_invar apply_map"
   unfolding apply_map_invar_def by blast

  lemma apply_map_invar_D2 :
    "\<lbrakk>apply_map_invar bop bs bs1 bs2 apply_map;
      c_lookup (i1, i2) apply_map = Some b\<rbrakk> \<Longrightarrow>
      \<exists>b1 b2. robdd_id_map bs1 i1 = Some b1 \<and> robdd_id_map bs2 i2 = Some b2 \<and>            
                  robdd_invar_ext bs (robdd_get_min_var b1 b2) b \<and> (\<forall>a. robdd_\<alpha> b a \<longleftrightarrow> bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a))"
   unfolding apply_map_invar_def by blast

  lemma apply_map_invar_extend :
    assumes invar: "apply_map_invar bop bs bs1 bs2 apply_map"
        and bs1'_OK: "bs1 \<subseteq> bs1'" "robdd_invar_ids bs1'" "\<And>b. b \<in> bs1' \<Longrightarrow> robdd_invar b"
        and bs2'_OK: "bs2 \<subseteq> bs2'" "robdd_invar_ids bs2'" "\<And>b. b \<in> bs2' \<Longrightarrow> robdd_invar b"
    shows "apply_map_invar bop bs bs1' bs2' apply_map"
  proof (rule apply_map_invar_I, goal_cases)
    case 1
    thus ?case using apply_map_invar_D1[OF invar] .
  next
    case lookup_eq: (2 i1 i2 b)
  
    from apply_map_invar_D2[OF invar lookup_eq]
    obtain b1 b2 where
       id_map_bs1: "robdd_id_map bs1 i1 = Some b1" and
       id_map_bs2: "robdd_id_map bs2 i2 = Some b2" and
       invar_b:    "robdd_invar_ext bs (robdd_get_min_var b1 b2) b" and
       sem_b:      "\<forall>a. robdd_\<alpha> b a = bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a)"
      by blast

    from bs1'_OK(1) obtain bs1'' where bs1'_eq: "bs1' = bs1'' \<union> bs1" by auto
    from bs2'_OK(1) obtain bs2'' where bs2'_eq: "bs2' = bs2'' \<union> bs2" by auto
  
    from robdd_invar_ids_equal_intro  [OF bs1'_OK(3) bs1'_OK(2)] bs1'_eq
    have ids_equal_bs1': "robdd_invar_ids_equal (bs1'' \<union> bs1)" by simp

    from robdd_invar_ids_equal_intro  [OF bs2'_OK(3) bs2'_OK(2)] bs2'_eq
    have ids_equal_bs2': "robdd_invar_ids_equal (bs2'' \<union> bs2)" by simp

    show ?case
      apply (rule_tac exI[where x = b1])
      apply (rule_tac exI[where x = b2])
      apply (simp add: invar_b sem_b bs1'_eq bs2'_eq
                       robdd_id_map_union [OF ids_equal_bs1']
                       robdd_id_map_union [OF ids_equal_bs2']
                       map_add_Some_iff id_map_bs1 id_map_bs2)
    done
  qed

  lemma robdd_apply_correct_full :
  fixes b1 b2 bop rev_map apply_map bs
  defines "res \<equiv> robdd_apply apply_map rev_map bop b1 b2"
  defines "b \<equiv> fst res"
  defines "apply_map' \<equiv> fst (snd res)"
  defines "rev_map' \<equiv> snd (snd res)"
  assumes invar_rev_map: "rev_map_invar bs rev_map"
      and invar_apply_map: "apply_map_invar bop bs bs1 bs2 apply_map"
      and b1_invar: "robdd_invar_ext bs1 n b1"      
      and b2_invar: "robdd_invar_ext bs2 n b2"      
      and bs1_OK: "\<And>b. b \<in> bs1 \<Longrightarrow> robdd_invar b"
      and bs2_OK: "\<And>b. b \<in> bs2 \<Longrightarrow> robdd_invar b"
  shows "\<exists>bs'. 
         subrobdds b \<union> bs \<subseteq> bs' \<and> 
         robdd_invar_ext bs' n b \<and>
         apply_map_invar bop bs' bs1 bs2 apply_map' \<and>
         rev_map_invar bs' rev_map' \<and>
         (\<forall>a. robdd_\<alpha> b a \<longleftrightarrow> bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a))"         
  using invar_rev_map invar_apply_map b1_invar b2_invar 
  unfolding b_def apply_map'_def rev_map'_def res_def
  proof (induct "(b1, b2)" arbitrary: b1 b2 bs n apply_map rev_map  rule: measure_induct_rule [of "\<lambda>(b1, b2). size_robdd b1 + size_robdd b2"])
    case less
    note indhyp = less(1)
    note invar_rev_map = less(2)
    note invar_apply_map = less(3)
    note b1_invar = less(4)
    note b2_invar = less(5)
    let ?res = "robdd_apply apply_map rev_map bop b1 b2"
    note res_def = robdd_apply.simps [of apply_map rev_map bop b1 b2]

    from rev_map_invar_implies_invar_ids[OF invar_rev_map] 
    have invar_ids_bs: "robdd_invar_ids bs" by simp
    note bs_OK_full = rev_map_invar_implies_invar_bs[OF invar_rev_map]
    have bs_OK: "\<And>b. b \<in> bs \<Longrightarrow> robdd_invar b" by (metis bs_OK_full subrobdds_set_mono subsetD)

    from b1_invar have b1_in: "b1 \<in> subrobdds_set bs1" unfolding robdd_invar_ext_def by simp
    from b2_invar have b2_in: "b2 \<in> subrobdds_set bs2" unfolding robdd_invar_ext_def by simp
    from b1_invar have invar_ids_bs1: "robdd_invar_ids bs1" unfolding robdd_invar_ext_def by simp
    from b2_invar have invar_ids_bs2: "robdd_invar_ids bs2" unfolding robdd_invar_ext_def by simp
    have invar_ids_equal_bs1: "robdd_invar_ids_equal bs1"
      by (rule robdd_invar_ids_equal_intro [OF bs1_OK invar_ids_bs1])
    have invar_ids_equal_bs2: "robdd_invar_ids_equal bs2"
      by (rule robdd_invar_ids_equal_intro [OF bs2_OK invar_ids_bs2])

    have invar_ids_leafs_bs : "robdd_invar_ids_leafs bs"
    proof (rule robdd_invar_ids_leafs_intro[of bs, OF _ invar_ids_bs])
      fix b
      assume "b \<in> bs"
      with bs_OK[of b] have "robdd_invar b" by simp
      thus "robdd_invar_reduced b" unfolding robdd_invar_def robdd_invar_ext_def by simp
    qed 

    show "\<exists>bs'. subrobdds (fst ?res) \<union> bs \<subseteq> bs' \<and> 
          robdd_invar_ext bs' n (fst ?res) \<and>
          apply_map_invar bop bs' bs1 bs2 (fst (snd ?res)) \<and>
          rev_map_invar bs' (snd (snd ?res)) \<and>
          (\<forall>a. robdd_\<alpha> (fst ?res) a = bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a))" 
          (is "\<exists>bs'. ?P bs'")
    proof (cases "bool_op_extend bop (robdd_to_bool b1) (robdd_to_bool b2)")
      case (Some f) note extend_eq_Some = this
  
      have res_eq[simp]: "?res = (robdd_leaf f, apply_map, rev_map)" 
        using res_def
        by (simp add: extend_eq_Some)

      from extend_eq_Some have f_eq: "\<forall>a. f = bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a)"
        apply (case_tac b1, case_tac [!] b2)
        apply (simp_all split: if_splits)
        apply (auto, (metis(full_types))+)
      done

      from invar_ids_leafs_bs invar_ids_bs 
      have invar_ids_bs': "robdd_invar_ids (insert (robdd_leaf f) bs)"
        apply (simp add: robdd_invar_ids_leafs_def robdd_invar_ids_def) 
        apply (intro allI impI)
        apply (elim conjE disjE)
        apply (simp_all)
        apply (metis One_nat_def)
      done

      have invar_ids_equal_bs': "robdd_invar_ids_equal (insert (robdd_leaf f) bs)"
        apply (rule robdd_invar_ids_equal_intro [OF _ invar_ids_bs'])
        apply (auto simp add: bs_OK)
      done

      from invar_rev_map invar_ids_bs'
      have invar_rev_map': "rev_map_invar (insert (robdd_leaf f) bs) rev_map"
        unfolding rev_map_invar_def by (simp add: robdd_invar_ext_def)
 
      from robdd_id_map_union [of "{robdd_leaf f}" bs] invar_ids_equal_bs'
      have id_map'_eq: "robdd_id_map (insert (robdd_leaf f) bs) = robdd_id_map {robdd_leaf f} ++ robdd_id_map bs" 
        by simp

      from invar_apply_map 
      have invar_apply_map': "apply_map_invar bop (insert (robdd_leaf f) bs) bs1 bs2 apply_map"
        unfolding apply_map_invar_def robdd_invar_ext_def invar_ids_equal_bs'
        by (simp add: invar_ids_bs') metis

      have "?P (insert (robdd_leaf f) bs)" by (simp add: invar_ids_bs' f_eq invar_rev_map' invar_apply_map')
      thus ?thesis by blast
    next
      case None note extend_eq_None = this

      have min_var_b12_ge_n: "(robdd_get_min_var b1 b2) \<ge> n"
      proof - 
        from b1_invar b2_invar have "robdd_invar_vars_greater n b1 \<and> robdd_invar_vars_greater n b2"
          unfolding robdd_invar_ext_def by simp_all
        with extend_eq_None show "(robdd_get_min_var b1 b2) \<ge> n"
          by (cases b1, case_tac [!] b2, simp_all)
      qed

      show ?thesis
      proof (cases "c_lookup (robdd_get_id b1, robdd_get_id b2) apply_map")
        case (Some b3) note lookup_eq_Some = this

        from extend_eq_None lookup_eq_Some res_def 
        have res_eq[simp]: "?res = (b3, apply_map, rev_map)" 
          by simp

        from apply_map_invar_D2[OF invar_apply_map, OF lookup_eq_Some]
             robdd_id_map_properties[of bs1] invar_ids_equal_bs1
             robdd_id_map_properties[of bs2] invar_ids_equal_bs2 
             b1_in b2_in
        have invar_b3: "robdd_invar_ext bs (robdd_get_min_var b1 b2) b3" and
             sem_b3: "\<And>a. robdd_\<alpha> b3 a = bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a)" 
          by (simp_all add: robdd_id_map_OK_def)

        from invar_b3 have b3_in: "b3 \<in> subrobdds_set bs" unfolding robdd_invar_ext_def by simp
        hence subrobdds_b3_bs_eq: "subrobdds_set (subrobdds b3 \<union> bs) = subrobdds_set bs"
          using subrobdds_set_subset_simp[of b3 bs] by auto

        from subrobdds_b3_bs_eq invar_b3 
        have invar_b3': "robdd_invar_ext (subrobdds b3 \<union> bs) n b3"           
           unfolding robdd_invar_ext_def
           using robdd_invar_ids_expand[of "subrobdds b3 \<union> bs", symmetric]
                 robdd_invar_ids_expand[of bs]
                 robdd_invar_vars_greater___weaken[OF _ min_var_b12_ge_n, of b3] by simp 
        from invar_b3' have invar_ids': "robdd_invar_ids (subrobdds b3 \<union> bs)" 
          unfolding robdd_invar_ext_def by simp

        from invar_rev_map invar_ids'
        have invar_rev_map': "rev_map_invar (subrobdds b3 \<union> bs) rev_map"
          unfolding rev_map_invar_def subrobdds_b3_bs_eq robdd_invar_ext_def
          by simp
 
        from invar_apply_map invar_ids'
        have invar_apply_map': "apply_map_invar bop (subrobdds b3 \<union> bs) bs1 bs2 apply_map" 
           unfolding apply_map_invar_def robdd_invar_ext_def by simp blast

        have "?P (subrobdds b3 \<union> bs)" by (simp add: invar_b3' sem_b3 invar_rev_map' invar_apply_map')
        thus ?thesis by blast
      next
        case None note lookup_eq_None = this

        from extend_eq_None have not_leaf_b12: "~(robdd_is_leaf b1 \<and> robdd_is_leaf b2)"
          by (cases b1, case_tac [!] b2) simp_all

        obtain b1_l b1_r v'' b2_l b2_r where 
          next_eq: "robdd_apply_next b1 b2 = (b1_l, b1_r, v'', b2_l, b2_r)" by (metis prod.exhaust)
        obtain l apply_map' rev_map' where 
          apply_l_eq: "robdd_apply apply_map rev_map bop b1_l b2_l = (l, apply_map', rev_map')"
          by (metis prod.exhaust)
        obtain r apply_map'' rev_map'' where 
          apply_r_eq: "robdd_apply apply_map' rev_map' bop b1_r b2_r = (r, apply_map'', rev_map'')"
          by (metis prod.exhaust)
        obtain b' rev_map''' where const_eq: "robdd_construct rev_map'' l v'' r = (b', rev_map''')"
          by (metis prod.exhaust)
        define apply_map'''
          where "apply_map''' = c_update (robdd_get_id b1, robdd_get_id b2) b' apply_map''"
        note next_props = robdd_apply_next_correct [OF b1_invar b2_invar next_eq] not_leaf_b12
        note v''_eq = next_props(13)

        have res_eq[simp]: "?res =(b', apply_map''', rev_map''')"
          by (simp_all add: b_def next_eq res_def extend_eq_None lookup_eq_None apply_r_eq apply_l_eq
                               const_eq apply_map'_def apply_map'''_def rev_map'_def)      

        from indhyp [of b1_l b2_l bs rev_map apply_map "Suc v''"]
        obtain bs' where
             subset_bs': "subrobdds l \<union> bs \<subseteq> bs'" and
             l_invar0: "robdd_invar_ext bs' (Suc v'') l" and
             invar_apply_map': "apply_map_invar bop bs' bs1 bs2 apply_map'" and
             invar_rev_map': "rev_map_invar bs' rev_map'" and
             sem_l: "\<forall>a. robdd_\<alpha> l a = bop (robdd_\<alpha> b1 (a(v'' := True))) 
                                           (robdd_\<alpha> b2 (a(v'' := True)))"
          by (simp add: apply_l_eq next_props  invar_rev_map invar_apply_map) metis

        from indhyp [of b1_r b2_r bs' rev_map' apply_map' "Suc v''"]
        obtain bs'' where
             subset_bs'': "subrobdds r \<union> bs' \<subseteq> bs''" and
             r_invar1: "robdd_invar_ext bs'' (Suc v'') r" and
             invar_apply_map'': "apply_map_invar bop bs'' bs1 bs2 apply_map''" and
             invar_rev_map'': "rev_map_invar bs'' rev_map''" and
             sem_r: "\<forall>a. robdd_\<alpha> r a = bop (robdd_\<alpha> b1 (a(v'' := False))) 
                                           (robdd_\<alpha> b2 (a(v'' := False)))"
          by (simp add: apply_r_eq next_props invar_rev_map' invar_apply_map') metis

        from subset_bs' have "l \<in> bs'" by auto
        with subset_bs'' have l_in_bs'': "l \<in> bs''" by auto
        from subset_bs'' have r_in_bs'': "r \<in> bs''" by auto

        from l_invar0 r_invar1 l_in_bs''
        have l_invar1: "robdd_invar_ext bs'' (Suc v'') l"
          unfolding robdd_invar_ext_def by simp (metis subrobdds_set_mono subsetD)

        define bs''' where "bs''' = insert b' bs''"
        from robdd_construct_correct[OF invar_rev_map'' _ _ l_invar1 r_invar1]
        have b'_invar: "robdd_invar_ext bs''' v'' b'"
         and invar_rev_map''': "rev_map_invar bs''' rev_map'''"
         and sem_b': "robdd_\<alpha> b' = robdd_\<alpha> (robdd_var 0 l v'' r)" 
          by (simp_all add: const_eq bs'''_def l_in_bs'' r_in_bs'')

        have sem_OK: "\<forall>a. robdd_\<alpha> b' a = bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a)"
          by (simp add: sem_b' sem_l sem_r fun_upd_idem)

        have "?P (subrobdds_set bs''')"
          unfolding res_eq fst_conv snd_conv
        proof (intro conjI)
          from subset_bs'' subset_bs' have "bs \<subseteq> bs''" by auto
          with subrobdds_set_mono2 [of bs bs''] 
          have "subrobdds_set bs \<subseteq> subrobdds_set bs''" by simp
          with subrobdds_set_mono[of bs]
          have "bs \<subseteq> subrobdds_set bs''" by simp
          thus "subrobdds b' \<union> bs \<subseteq> subrobdds_set bs'''"
            unfolding bs'''_def            
            by (simp add: subset_iff)
        next
          from b'_invar
          show "robdd_invar_ext (subrobdds_set bs''') n b'"
            unfolding robdd_invar_ext_def robdd_invar_ids_def
            using robdd_invar_vars_greater___weaken[of v'' b' n]
                  v''_eq min_var_b12_ge_n by simp
        next
          show "\<forall>a. robdd_\<alpha> b' a = bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a)" by fact
        next
          from invar_rev_map''' subrobdds_set_mono[of bs''']
          show "rev_map_invar (subrobdds_set bs''') rev_map'''"
            unfolding rev_map_invar_def by (simp add: subset_iff)
        next          
          from robdd_id_map_properties[of bs1] invar_ids_equal_bs1 b1_in
          have id_map_b1: "robdd_id_map bs1 (robdd_get_id b1) = Some b1"
            by (simp add: robdd_id_map_OK_def)

          from robdd_id_map_properties[of bs2] invar_ids_equal_bs2 b2_in
          have id_map_b2: "robdd_id_map bs2 (robdd_get_id b2) = Some b2"
            by (simp add: robdd_id_map_OK_def)

          { fix n b
            assume b_invar: "robdd_invar_ext bs'' n b"

            from b'_invar have ids_bs''': "robdd_invar_ids bs'''" unfolding robdd_invar_ext_def by simp
 
            from b_invar subrobdds_set_mono2 [of bs'' bs'''] ids_bs'''
            have "robdd_invar_ext bs''' n b"
              unfolding robdd_invar_ext_def bs'''_def by simp
          } note invar_bs'''_ext = this

          from invar_apply_map'' b'_invar
          show "apply_map_invar bop (subrobdds_set bs''') bs1 bs2 apply_map'''"
            unfolding apply_map'''_def apply_map_invar_def
            apply (elim conjE)
            apply (simp add: c.lookup_correct c.update_correct id_map_b1 id_map_b2 v''_eq sem_OK)
            apply (metis invar_bs'''_ext)
          done
        qed
        thus ?thesis by blast
      qed 
    qed
  qed
  
  lemma robdd_apply_correct :
  fixes b1 b2 bop rev_map apply_map 
  defines "res \<equiv> robdd_apply (c_empty ()) (r_empty (), 2) bop b1 b2"
  defines "b \<equiv> fst res"
  assumes b1_invar: "robdd_invar b1"      
      and b2_invar: "robdd_invar b2"      
  shows "robdd_invar b \<and> (\<forall>a. robdd_\<alpha> b a \<longleftrightarrow> bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a))"         
  proof -
    from robdd_apply_correct_full [OF rev_map_invar_empty apply_map_invar_empty
          b1_invar[unfolded robdd_invar_def] b2_invar[unfolded robdd_invar_def], of bop,
          folded res_def b_def] b1_invar b2_invar
    obtain bs where invar_ext: "robdd_invar_ext bs 0 b"
                and sem_OK: "\<forall>a. robdd_\<alpha> b a = bop (robdd_\<alpha> b1 a) (robdd_\<alpha> b2 a)" by auto

    from invar_ext have invar: "robdd_invar b"
      by (rule robdd_invar_impl)
    
    from invar sem_OK show ?thesis by simp
  qed

  definition robdd_neg where
    "robdd_neg apply_map rev_map b = robdd_apply apply_map rev_map (\<lambda>b1 b2. \<not>(b1 \<and> b2)) b robdd_one"

  lemma robdd_neg_correct_full :
  fixes b rev_map apply_map bs
  defines "res \<equiv> robdd_neg apply_map rev_map b"
  defines "b' \<equiv> fst res"
  defines "apply_map' \<equiv> fst (snd res)"
  defines "rev_map' \<equiv> snd (snd res)"
  assumes invar_rev_map: "rev_map_invar bs rev_map"
      and invar_apply_map: "apply_map_invar (\<lambda>b1 b2. \<not>(b1 \<and> b2)) bs bs1 bs2 apply_map"
      and b_invar: "robdd_invar_ext bs1 n b"      
      and bs1_OK: "\<And>b. b \<in> bs1 \<Longrightarrow> robdd_invar b"
      and bs2_OK: "\<And>b. b \<in> bs2 \<Longrightarrow> robdd_invar b" "robdd_invar_ids bs2"
  shows "\<exists>bs'. 
         subrobdds b' \<union> bs \<subseteq> bs' \<and> 
         robdd_invar_ext bs' n b' \<and>
         apply_map_invar (\<lambda>b1 b2. \<not>(b1 \<and> b2)) bs' bs1 
              (insert robdd_zero (insert robdd_one bs2)) apply_map' \<and>
         rev_map_invar bs' rev_map' \<and>
         (\<forall>a. robdd_\<alpha> b' a \<longleftrightarrow> \<not> (robdd_\<alpha> b a))"
  proof -

    from bs2_OK have "robdd_invar_ids_leafs bs2"
      apply (rule_tac robdd_invar_ids_leafs_intro)
      apply (simp_all add: robdd_invar_def robdd_invar_ext_def)
    done
    with bs2_OK(2) have "robdd_invar_ids_full bs2" by (simp add: robdd_invar_ids_full_def)
    hence bs2'_invar: "robdd_invar_ids (insert robdd_zero (insert robdd_one bs2))"
      unfolding robdd_invar_ids_full_alt_def by simp 

    from b_invar
    have bs1_invar: "robdd_invar_ids bs1"
      unfolding robdd_invar_ext_def by simp 
   
    from invar_apply_map have
      invar_apply_map': "apply_map_invar (\<lambda>b1 b2. \<not>(b1 \<and> b2)) bs bs1 
           (insert robdd_zero (insert robdd_one bs2)) apply_map"
      apply (rule apply_map_invar_extend)
      apply (auto simp add: subset_iff bs1_OK bs2_OK bs2'_invar bs1_invar)
    done

    from robdd_apply_correct_full[OF invar_rev_map invar_apply_map' b_invar _ bs1_OK, of robdd_one]
         res_def[symmetric]
    show ?thesis apply (simp add: robdd_neg_def b'_def[symmetric] apply_map'_def[symmetric]
       rev_map'_def[symmetric])
       by (metis bs2_OK(1) bs2'_invar robdd_invar_simps_leafs)
  qed

  lemma robdd_neg_correct :
  fixes b rev_map apply_map bs
  defines "res \<equiv> robdd_neg (c_empty ()) (r_empty (), 2) b"
  defines "bn \<equiv> fst res"
  assumes b_invar: "robdd_invar b"      
  shows "robdd_invar bn \<and> (\<forall>a. robdd_\<alpha> bn a \<longleftrightarrow> \<not>(robdd_\<alpha> b a))"         
    unfolding res_def bn_def robdd_neg_def
    using robdd_apply_correct [OF b_invar, of robdd_one "(\<lambda>b1 b2. \<not>(b1 \<and> b2))"]
    by simp

  lemma robdd_neg_alt_def :
    "robdd_neg apply_map rev_map b = 
      (case (bope_neg (robdd_to_bool b)) of 
         Some f \<Rightarrow> (robdd_leaf f, apply_map, rev_map)
       | None \<Rightarrow> (case c_lookup (robdd_get_id b, 1) apply_map of
            Some b3 \<Rightarrow> (b3, apply_map, rev_map)
          | None \<Rightarrow> (let (l1, r1, var) = robdd_neg_next b in 
                     let (l, apply_map, rev_map) = robdd_neg apply_map rev_map l1 in
                     let (r, apply_map, rev_map) = robdd_neg apply_map rev_map r1 in
                     let (b3, rev_map) = robdd_construct rev_map l var r in
                     let apply_map = c_update (robdd_get_id b, 1) b3 apply_map in
                     (b3, apply_map, rev_map))))"
   proof -
     have bope_neg_intro: 
        "(bool_op_extend (\<lambda>b1 b2. b1 \<longrightarrow> \<not> b2) (robdd_to_bool b) (Some True)) =
         (bope_neg (robdd_to_bool b))" 
        apply (cases "robdd_to_bool b" rule: bool_opt_exhaust)
        apply (simp_all)
     done

     obtain b1_l b1_r v'' b2_l b2_r where 
       next_eq: "robdd_apply_next b robdd_one = (b1_l, b1_r, v'', b2_l, b2_r)" by (metis prod.exhaust)

     from next_eq have b2_eq[simp]: "b2_l = robdd_one" "b2_r = robdd_one"
       by (case_tac[!] b) auto

     show ?thesis
       unfolding robdd_neg_def robdd_apply.simps[of _ _ _ b]
       by (simp split: option.splits add: bope_neg_intro next_eq split_def robdd_neg_next_def)
   qed

  text \<open>An auxiliary construct to get the ids of a ROBDD consistent with some cache or
          other ROBDDs.\<close>
  definition robdd_copy where
    "robdd_copy apply_map rev_map b = robdd_apply apply_map rev_map (\<lambda>b1 b2. (b1 \<and> b2)) b robdd_one"

  lemma robdd_copy_correct_full :
  fixes b rev_map apply_map bs
  defines "res \<equiv> robdd_copy apply_map rev_map b"
  defines "b' \<equiv> fst res"
  defines "apply_map' \<equiv> fst (snd res)"
  defines "rev_map' \<equiv> snd (snd res)"
  assumes invar_rev_map: "rev_map_invar bs rev_map"
      and invar_apply_map: "apply_map_invar (\<lambda>b1 b2. (b1 \<and> b2)) bs bs1 bs2 apply_map"
      and b_invar: "robdd_invar_ext bs1 n b"      
      and bs1_OK: "\<And>b. b \<in> bs1 \<Longrightarrow> robdd_invar b"
      and bs2_OK: "\<And>b. b \<in> bs2 \<Longrightarrow> robdd_invar b" "robdd_invar_ids bs2"
  shows "\<exists>bs'. 
         subrobdds b' \<union> bs \<subseteq> bs' \<and> 
         robdd_invar_ext bs' n b' \<and>
         apply_map_invar (\<lambda>b1 b2. (b1 \<and> b2)) bs' bs1 
              (insert robdd_zero (insert robdd_one bs2)) apply_map' \<and>
         rev_map_invar bs' rev_map' \<and>
         (\<forall>a. robdd_\<alpha> b' a \<longleftrightarrow> (robdd_\<alpha> b a))"
  proof -

    from bs2_OK have "robdd_invar_ids_leafs bs2"
      apply (rule_tac robdd_invar_ids_leafs_intro)
      apply (simp_all add: robdd_invar_def robdd_invar_ext_def)
    done
    with bs2_OK(2) have "robdd_invar_ids_full bs2" by (simp add: robdd_invar_ids_full_def)
    hence bs2'_invar: "robdd_invar_ids (insert robdd_zero (insert robdd_one bs2))"
      unfolding robdd_invar_ids_full_alt_def by simp 

    from b_invar
    have bs1_invar: "robdd_invar_ids bs1"
      unfolding robdd_invar_ext_def by simp 
   
    from invar_apply_map have
      invar_apply_map': "apply_map_invar (\<lambda>b1 b2. (b1 \<and> b2)) bs bs1 
           (insert robdd_zero (insert robdd_one bs2)) apply_map"
      apply (rule apply_map_invar_extend)
      apply (auto simp add: subset_iff bs1_OK bs2_OK bs2'_invar bs1_invar)
    done

    from robdd_apply_correct_full[OF invar_rev_map invar_apply_map' b_invar _ bs1_OK, of robdd_one]
         res_def[symmetric]
    show ?thesis apply (simp add: robdd_copy_def b'_def[symmetric] apply_map'_def[symmetric]
       rev_map'_def[symmetric])
       by (metis bs2_OK(1) bs2'_invar robdd_invar_simps_leafs)
  qed

  lemma robdd_copy_correct :
  fixes b rev_map apply_map bs
  defines "res \<equiv> robdd_copy (c_empty ()) rev_map b"
  defines "b' \<equiv> fst res"
  defines "rev_map' \<equiv> snd (snd res)"
  assumes invar_rev_map: "rev_map_invar bs rev_map"
      and b_invar: "robdd_invar_ext {b} n b"      
  shows "\<exists>bs'. 
         subrobdds b' \<union> bs \<subseteq> bs' \<and> 
         robdd_invar_ext bs' n b' \<and>
         rev_map_invar bs' rev_map' \<and>
         (\<forall>a. robdd_\<alpha> b' a \<longleftrightarrow> (robdd_\<alpha> b a))"
    using res_def[symmetric] 
    using robdd_copy_correct_full [OF invar_rev_map _ b_invar, of "{}" "c_empty ()"]
      apply (simp add: apply_map_invar_def c.empty_correct c.lookup_correct robdd_invar_ids_def
                       b'_def[symmetric] rev_map'_def[symmetric])
      apply (metis b_invar robdd_invar_impl)
    done

  lemma robdd_copy_alt_def :
    "robdd_copy apply_map rev_map b = 
      (case (robdd_to_bool b) of 
         Some f \<Rightarrow> (robdd_leaf f, apply_map, rev_map)
       | None \<Rightarrow> (case c_lookup (robdd_get_id b, 1) apply_map of
            Some b3 \<Rightarrow> (b3, apply_map, rev_map)
          | None \<Rightarrow> (let (l1, r1, var) = robdd_neg_next b in 
                     let (l, apply_map, rev_map) = robdd_copy apply_map rev_map l1 in
                     let (r, apply_map, rev_map) = robdd_copy apply_map rev_map r1 in
                     let (b3, rev_map) = robdd_construct rev_map l var r in
                     let apply_map = c_update (robdd_get_id b, 1) b3 apply_map in
                     (b3, apply_map, rev_map))))"
   proof -
     have bope_neg_intro: 
        "(bool_op_extend (\<lambda>b1 b2. b1 \<and> b2) (robdd_to_bool b) (Some True)) =
         (robdd_to_bool b)" 
        apply (cases "robdd_to_bool b" rule: bool_opt_exhaust)
        apply (simp_all)
     done

     obtain b1_l b1_r v'' b2_l b2_r where 
       next_eq: "robdd_apply_next b robdd_one = (b1_l, b1_r, v'', b2_l, b2_r)" by (metis prod.exhaust)

     from next_eq have b2_eq[simp]: "b2_l = robdd_one" "b2_r = robdd_one"
       by (case_tac[!] b) auto

     show ?thesis
       unfolding robdd_copy_def robdd_apply.simps[of _ _ _ b]
       by (simp split: option.splits add: bope_neg_intro next_eq split_def robdd_neg_next_def)
   qed

  definition restrict_map_invar where
     "restrict_map_invar f bs res_map \<longleftrightarrow>
       c_invar res_map \<and>
       (\<forall>i v b. c_lookup (v, i) res_map = Some b \<longrightarrow>
          (\<exists>b'. robdd_id_map bs i = Some b' \<and> b \<in> bs \<and>            
                robdd_invar_ext bs (robdd_get_var b') b \<and> 
                (\<forall>a. robdd_\<alpha> b a \<longleftrightarrow> robdd_\<alpha> b' (a(v := f)))))"

  lemma restrict_map_invar_empty : 
    "restrict_map_invar f bs (c_empty ())"
    unfolding restrict_map_invar_def by (simp add: c.empty_correct c.lookup_correct)

  lemma restrict_map_invar_I :
    "\<lbrakk>c_invar res_map;
      \<And>i v b. c_lookup (v, i) res_map = Some b \<Longrightarrow>
      (\<exists>b'. robdd_id_map bs i = Some b' \<and> b \<in> bs \<and>
                robdd_invar_ext bs (robdd_get_var b') b \<and> 
                (\<forall>a. robdd_\<alpha> b a \<longleftrightarrow> robdd_\<alpha> b' (a(v := f))))\<rbrakk> \<Longrightarrow>
      restrict_map_invar f bs res_map"
   unfolding restrict_map_invar_def by blast

  lemma restrict_map_invar_D1 :
    "restrict_map_invar f bs res_map \<Longrightarrow> c_invar res_map"
   unfolding restrict_map_invar_def by blast

  lemma restrict_map_invar_D2 :
    "\<lbrakk>restrict_map_invar f bs res_map;
      c_lookup (v, i) res_map = Some b\<rbrakk> \<Longrightarrow>
      (\<exists>b'. robdd_id_map bs i = Some b' \<and> b \<in> bs \<and>
                robdd_invar_ext bs (robdd_get_var b') b \<and> 
                (\<forall>a. robdd_\<alpha> b a \<longleftrightarrow> robdd_\<alpha> b' (a(v := f))))"
   unfolding restrict_map_invar_def by blast

  fun robdd_restrict where
    "robdd_restrict res_map rev_map f rv b =
     (case b of (robdd_leaf f') \<Rightarrow> (robdd_leaf f', res_map, rev_map)
             | (robdd_var i l v r) \<Rightarrow> 
        (if (rv < v) then (b, res_map, rev_map) else (
         if (rv = v) then (if f then l else r, res_map, rev_map) else (
         (case c_lookup (rv, i) res_map of
             Some b3 \<Rightarrow> (b3, res_map, rev_map)
           | None \<Rightarrow> (let (l', res_map, rev_map) = robdd_restrict res_map rev_map f rv l in
                      let (r', res_map, rev_map) = robdd_restrict res_map rev_map f rv r in
                      let (b3, rev_map) = robdd_construct rev_map l' v r' in
                      let res_map = c_update (rv, i) b3 res_map in
                      (b3, res_map, rev_map))                    
        )))))"
  declare robdd_restrict.simps [simp del]

  lemma robdd_restrict_correct_full :
  fixes b f rv rev_map res_map bs
  defines "res \<equiv> robdd_restrict res_map rev_map f rv b"
  defines "b' \<equiv> fst res"
  defines "res_map' \<equiv> fst (snd res)"
  defines "rev_map' \<equiv> snd (snd res)"
  assumes invar_rev_map: "rev_map_invar bs rev_map"
      and invar_res_map: "restrict_map_invar f bs res_map"
      and b_invar: "robdd_invar_ext bs n b"
      and b_sub: "subrobdds b \<subseteq> bs"      
  shows "\<exists>bs'. insert b' bs \<subseteq> bs' \<and> 
         robdd_invar_ext bs' n b' \<and>
         restrict_map_invar f bs' res_map' \<and>
         rev_map_invar bs' rev_map' \<and>
         (\<forall>a. robdd_\<alpha> b' a \<longleftrightarrow> (robdd_\<alpha> b (a(rv := f))))"         
  using invar_rev_map invar_res_map b_invar b_sub
  unfolding b'_def res_map'_def rev_map'_def res_def
  proof (induct b arbitrary: bs n res_map rev_map)
    case (robdd_leaf f')
    thus ?case by (rule_tac exI [where x = bs]) (simp add: robdd_restrict.simps)
  next 
    case (robdd_var i l v r)
    note indhyp_l = robdd_var(1)
    note indhyp_r = robdd_var(2)
    note invar_rev_map = robdd_var(3)
    note invar_res_map = robdd_var(4)
    note b_invar = robdd_var(5)
    note b_sub = robdd_var(6)

    let ?b = "robdd_var i l v r"
    let ?res = "robdd_restrict res_map rev_map f rv ?b"

    from b_invar have b_in_bs: "?b \<in> subrobdds_set bs" unfolding robdd_invar_ext_def by simp
    from rev_map_invar_implies_invar_ids[OF invar_rev_map] 
    have invar_ids_bs: "robdd_invar_ids bs" by simp
    note bs_OK_full = rev_map_invar_implies_invar_bs[OF invar_rev_map]
    have bs_OK: "\<And>b. b \<in> bs \<Longrightarrow> robdd_invar b" by (metis bs_OK_full subrobdds_set_mono subsetD)
    have invar_ids_equal_bs: "robdd_invar_ids_equal bs"
      by (rule robdd_invar_ids_equal_intro [OF bs_OK invar_ids_bs])

    have invar_ids_leafs_bs : "robdd_invar_ids_leafs bs"
    proof (rule robdd_invar_ids_leafs_intro[of bs, OF _ invar_ids_bs])
      fix b
      assume "b \<in> bs"
      with bs_OK[of b] have "robdd_invar b" by simp
      thus "robdd_invar_reduced b" unfolding robdd_invar_def robdd_invar_ext_def by simp
    qed 

    from b_invar have invars_greater: "robdd_invar_vars_greater (Suc v) l"  "robdd_invar_vars_greater (Suc v) r"
      by (simp_all add: robdd_invar_ext_def)

    show ?case
    proof (cases "rv < v")
      case True note rv_less = this

      have sem_simp :
         "\<And>a bb. robdd_invar_vars_greater (Suc v) bb \<Longrightarrow> 
                 robdd_\<alpha> bb (\<lambda>x. (x = rv \<longrightarrow> f) \<and> (x \<noteq> rv \<longrightarrow> a x)) = robdd_\<alpha> bb a"      
        apply (rule_tac robdd_\<alpha>_invar_greater[of "Suc v"])
        apply (insert rv_less)
        apply (simp_all)
      done
        
      show ?thesis using rv_less b_invar b_sub
        apply (rule_tac exI[where x = bs]) 
        apply (simp add: invar_rev_map invar_res_map robdd_restrict.simps)
        apply (simp add: invars_greater sem_simp)
      done
    next
      case False hence v_le: "v \<le> rv" by simp

      show ?thesis
      proof (cases "rv = v")
        case True note rv_eq [simp] = this

        from invars_greater(2) have r_simp :
           "\<And>a. robdd_\<alpha> r (\<lambda>x. x \<noteq> v \<and> a x) = robdd_\<alpha> r a"      
          apply (rule_tac robdd_\<alpha>_invar_greater[of "Suc v"])
          apply (simp_all)
        done

        from invars_greater(1) have l_simp :
           "\<And>a. robdd_\<alpha> l (\<lambda>x. (x \<noteq> v \<longrightarrow> a x)) = robdd_\<alpha> l a"      
          apply (rule_tac robdd_\<alpha>_invar_greater[of "Suc v"])
          apply (simp_all)
        done

        from b_invar robdd_invar_ext_weaken_var[of bs "Suc v" _ n]
        have "robdd_invar_ext bs n l" "robdd_invar_ext bs n r" by simp_all
        thus ?thesis using b_invar b_sub
          supply map_upd_eq_restrict[simp]  
          apply (rule_tac exI[where x = bs]) 
          apply (simp add: invar_rev_map invar_res_map robdd_restrict.simps)
          apply (simp add: l_simp r_simp subset_iff)
        done
      next
        case False with v_le have v_less: "v < rv" by simp

        show ?thesis 
        proof (cases "c_lookup (rv, i) res_map")
          case (Some b3) note lookup_eq = this

          from robdd_id_map_properties[of bs] invar_ids_equal_bs
          have "robdd_id_map_OK bs (robdd_id_map bs)" by simp
          with robdd_id_map_OK_D[of bs "robdd_id_map bs", OF _ b_in_bs]
          have "robdd_id_map bs i = Some ?b" by simp

          with restrict_map_invar_D2[OF invar_res_map lookup_eq] v_less
          have invar_b3: "robdd_invar_ext bs v b3" and
               b3_in_bs: "b3 \<in> bs" and
               sem_b3: "\<forall>a. robdd_\<alpha> b3 a = (if a v then robdd_\<alpha> l (a(rv := f)) else 
                   robdd_\<alpha> r (a(rv := f)))" by simp_all

          from invar_b3 b_invar have invar_b3': "robdd_invar_ext bs n b3"
            apply (rule_tac robdd_invar_ext_weaken_var[of _ v])
            apply simp_all
          done

          have "\<And>a. (\<lambda>x. (x = rv \<longrightarrow> f) \<and> (x \<noteq> rv \<longrightarrow> a x)) = a (rv := f)"
            by (simp add: fun_eq_iff)
          with lookup_eq 
          show ?thesis using v_less b3_in_bs
            apply (rule_tac exI[where x = bs]) 
            apply (simp add: sem_b3 invar_b3' invar_rev_map invar_res_map robdd_restrict.simps)
          done
        next
          case None note lookup_eq = this

          obtain l' res_map' rev_map' where 
            res_l_eq: "robdd_restrict res_map rev_map f rv l = (l', res_map', rev_map')"
            by (metis prod.exhaust)
          obtain r' res_map'' rev_map'' where 
            res_r_eq: "robdd_restrict res_map' rev_map' f rv r = (r', res_map'', rev_map'')"
            by (metis prod.exhaust)
          obtain b3 rev_map''' where 
            const_eq: "robdd_construct rev_map'' l' v r' = (b3, rev_map''')"
            by (metis prod.exhaust)

          from b_invar b_sub indhyp_l [OF invar_rev_map invar_res_map, of "Suc v"]
          obtain bs' where
             subset_bs': "insert l' bs \<subseteq> bs'" and
             l'_invar: "robdd_invar_ext bs' (Suc v) l'" and
             invar_res_map': "restrict_map_invar f bs' res_map'" and
             invar_rev_map': "rev_map_invar bs' rev_map'" and
             sem_l': "\<forall>a. robdd_\<alpha> l' a = (robdd_\<alpha> l (\<lambda>b. if b = rv then f else a b))"
            by (simp add: invar_rev_map invar_res_map res_l_eq) blast

          from b_invar have "robdd_invar_ext bs (Suc v) r" by simp
          with l'_invar subset_bs' have "robdd_invar_ext bs' (Suc v) r"
            unfolding robdd_invar_ext_def by simp (metis subrobdds_set_mono2 subsetD)
          with b_sub subset_bs' indhyp_r [OF invar_rev_map' invar_res_map', of "Suc v"]
          obtain bs'' where
             subset_bs'': "insert r' bs' \<subseteq> bs''" and
             r'_invar: "robdd_invar_ext bs'' (Suc v) r'" and
             invar_res_map'': "restrict_map_invar f bs'' res_map''" and
             invar_rev_map'': "rev_map_invar bs'' rev_map''" and
             sem_r': "\<forall>a. robdd_\<alpha> r' a = (robdd_\<alpha> r (\<lambda>b. if b = rv then f else a b))"
            by (simp add: subset_iff invar_rev_map invar_res_map res_r_eq) blast
          from l'_invar r'_invar subset_bs' subset_bs'' 
          have l'_invar': "robdd_invar_ext bs'' (Suc v) l'"
            unfolding robdd_invar_ext_def by simp (metis subrobdds_set_mono2 subsetD)

          from subset_bs' subset_bs'' have "l' \<in> bs''" "r' \<in> bs''"
            by (simp_all add: subset_iff)

          from robdd_construct_correct [OF invar_rev_map'' \<open>l' \<in> bs''\<close> \<open>r' \<in> bs''\<close>
              l'_invar' r'_invar]
          have b3_invar: "robdd_invar_ext (insert b3 bs'') v b3" and
               invar_rev_map''': "rev_map_invar (insert b3 bs'') rev_map'''" and
               sem_b3: "robdd_\<alpha> b3 = robdd_\<alpha> (robdd_var 0 l' v r')"
            by (simp_all add: const_eq) 

          from b3_invar b_invar have b3_invar': "robdd_invar_ext (insert b3 bs'') n b3"
            apply (rule_tac robdd_invar_ext_weaken_var[of _ v])
            apply simp_all
          done

          from subset_bs' subset_bs'' have bs_sub: "bs \<subseteq> insert b3 bs''"
            by (simp add: subset_iff)

          have invar_res_map''':
            "restrict_map_invar f (insert b3 bs'') (c_update (rv, i) b3 res_map'')" 
          proof -
            from b_in_bs subset_bs' subset_bs''
            have b_in': "robdd_var i l v r \<in> subrobdds_set bs''"
              unfolding subrobdds_set_def by (simp add: subset_iff Bex_def) blast

            from robdd_id_map_union [of "{b3}" bs'']
                 rev_map_invar_implies_invar_ids_equal[OF invar_rev_map''']
            have id_map_eq: "robdd_id_map (insert b3 bs'') = robdd_id_map {b3} ++ robdd_id_map bs''" by simp

            from robdd_id_map_properties[of "insert b3 bs''"] b_in'
                 rev_map_invar_implies_invar_ids_equal[OF invar_rev_map''']
                 robdd_id_map_OK_D [of "insert b3 bs''" "robdd_id_map (insert b3 bs'')" ?b]
            have map_id_i: "robdd_id_map (insert b3 bs'') i = Some ?b" by simp
            note c_invar = restrict_map_invar_D1[OF invar_res_map'']
  
            show ?thesis 
            proof (rule restrict_map_invar_I, goal_cases)
              from restrict_map_invar_D1[OF invar_res_map'']
              show "c_invar (c_update (rv, i) b3 res_map'')" by (simp add: c.update_correct)
            next
              case prems: (2 i' v' b')
              note lookup_eq = prems(1)
     
              show ?case
              proof (cases "i' = i \<and> v' = rv")
                case True note iv'_eq = this
                with lookup_eq map_id_i sem_b3 b3_invar v_less show ?thesis
                  by (simp add: c_invar c.update_correct c.lookup_correct
                                sem_l' sem_r' fun_upd_def)
              next
                case False
                with lookup_eq have lookup_eq': "c_lookup (v', i') res_map'' = Some b'"
                  by (auto simp add: c_invar c.lookup_correct c.update_correct)

                from restrict_map_invar_D2[OF invar_res_map'' lookup_eq'] 
                obtain b'' where b''_props:
                  "robdd_id_map bs'' i' = Some b''" "b' \<in> bs''"
                  "robdd_invar_ext bs'' (robdd_get_var b'') b'"
                  "\<forall>a. robdd_\<alpha> b' a = robdd_\<alpha> b'' (a(v' := f))" by auto
 
               show ?thesis
                 apply (rule_tac exI[where x = b''])
                 apply (simp add: id_map_eq map_add_Some_iff b''_props)
                 apply (insert b3_invar b''_props(3))
                 apply (simp add: robdd_invar_ext_def)
                 done             
              qed
            qed
          qed

          from robdd_restrict.simps[of res_map rev_map f rv ?b]
          show ?thesis using v_less 
            apply (rule_tac exI[where x = "insert b3 bs''"])
            apply (simp add: lookup_eq res_l_eq res_r_eq const_eq invar_rev_map'''
                             sem_b3 sem_l' sem_r' b3_invar' bs_sub invar_res_map''')
          done
        qed
      qed
    qed
  qed


end


subsection \<open>Semantics on lists\<close>

text \<open>BDDs represent boolean expression. I.e. they are functions from assignments to 
  \texttt{True} or \texttt{False}. Here, assignments are represented by functions from
  variable indices to the values of these Boolean variables. While this reprentation of 
  is convenient for proofs, a representation based on lists is more convinient for execution.\<close>

definition list_to_assignment_set :: "bool option list \<Rightarrow> (nat \<Rightarrow> bool) set" where
"list_to_assignment_set l = {a . (\<forall>v < length l. (\<forall>f. l ! v = Some f \<longrightarrow> a v = f))}"

definition shift_assignment where
  "shift_assignment (b::bool) a = (\<lambda>v. case v of 0 \<Rightarrow> b | Suc v' \<Rightarrow> a v')" 

lemma inj_shift_assignement :
  "inj_on (shift_assignment b) S"
unfolding inj_on_def shift_assignment_def
by (simp add: fun_eq_iff split: nat.splits)

lemma list_to_assignment_set_None_simp [simp] :
  "list_to_assignment_set (None # l) = 
   list_to_assignment_set (Some True # l) \<union> list_to_assignment_set (Some False # l)"
unfolding list_to_assignment_set_def
apply (simp add: set_eq_iff less_Suc_eq_0_disj 
            del: all_simps add: all_simps[symmetric])
apply (simp add: all_conj_distrib)
apply (intro allI iffI)
apply simp
apply (elim disjE conjE)
apply simp_all
done
 
lemma list_to_assignment_set_simps [simp]: 
  "list_to_assignment_set [] = UNIV" (is ?T1)
  "list_to_assignment_set (Some b # l) = (shift_assignment b) ` (list_to_assignment_set l)" (is "?T3 b")
proof -
  show ?T1 unfolding list_to_assignment_set_def by simp
next
  show "?T3 b"
    unfolding list_to_assignment_set_def 
    apply (simp add: set_eq_iff less_Suc_eq_0_disj shift_assignment_def 
                  del: all_simps add: all_simps[symmetric])
    apply (simp add: all_conj_distrib image_iff)
    apply (intro allI iffI)
    apply (rule_tac x = "\<lambda>v. x (Suc v)" in exI)
    apply (simp add: fun_eq_iff split: nat.split)
    apply auto    
    done
qed


lemma infinite_list_to_assignment_set :
  "\<not>(finite (list_to_assignment_set l))"
proof (induct l)
  case Nil note l_eq = this

  have inf_UNIV: "\<not>(finite (UNIV :: (nat \<Rightarrow> bool) set))"
  proof (rule notI)
    assume fin_UNIV: "finite (UNIV :: (nat \<Rightarrow> bool) set)"
    from finite_fun_UNIVD1[OF fin_UNIV] 
    show False by simp
  qed
  thus ?case by simp
next
  case (Cons bo l')
  note ind_hyp = Cons

  obtain b where sub_b: "list_to_assignment_set (Some b # l') \<subseteq> list_to_assignment_set (bo # l')"
    by (cases bo) auto

  have not_fin_b: "\<not>(finite (list_to_assignment_set (Some b # l')))"
  proof (rule notI)
    assume "finite (list_to_assignment_set (Some b # l'))"
    hence "finite (list_to_assignment_set l')"
      apply (simp) apply (rule finite_imageD [of "shift_assignment b"])
      apply (simp_all add: inj_shift_assignement)
    done
    with ind_hyp show False by simp
  qed
  from finite_subset[OF sub_b] not_fin_b
  show ?case by blast
qed

lemma list_to_assignment_set_not_empty :
  "(list_to_assignment_set l) \<noteq> {}"
by (metis finite.emptyI infinite_list_to_assignment_set)

fun robdd_list_\<alpha> where
   "robdd_list_\<alpha> (robdd_leaf f) n l = f"
 | "robdd_list_\<alpha> (robdd_var i l v r) n [] = False"
 | "robdd_list_\<alpha> (robdd_var i l v r) n (bo # bs) =
     (if n = v then 
        (case bo of None \<Rightarrow> robdd_list_\<alpha> l (Suc n) bs \<and> robdd_list_\<alpha> r (Suc n) bs
                  | Some True \<Rightarrow> robdd_list_\<alpha> l (Suc n) bs
                  | Some False \<Rightarrow> robdd_list_\<alpha> r (Suc n) bs) 
      else (robdd_list_\<alpha> (robdd_var i l v r) (Suc n) bs))"

lemma robdd_list_\<alpha>_correct_aux :
assumes invar: "robdd_invar_vars_greater n b" "robdd_invar_reduced b"
shows "robdd_list_\<alpha> b n l \<longleftrightarrow> (\<forall>a \<in> (list_to_assignment_set l). robdd_\<alpha> b (\<lambda>v. a (v - n)))"
using invar
proof (induct b n l rule: robdd_list_\<alpha>.induct)
  case (1 f n l)
  with list_to_assignment_set_not_empty[of l] show ?case by auto
next
  case prems: (2 i ll v rr n)
  note invar = prems(1,2)

  from invar have "robdd_\<alpha> ll \<noteq> robdd_\<alpha> rr"
    by (metis robdd_equiv_alt_def_full robdd_invar_reduced.simps(2) 
              robdd_invar_vars_greater.simps(2) robdd_invar_vars_impl)
  then obtain a where a_sem_neq: "robdd_\<alpha> ll a \<noteq> robdd_\<alpha> rr a" by (auto simp add: fun_eq_iff)

  define aa where "aa v = a (v + n)" for v
  from invar(1) have ll_sem: "\<And>b. robdd_\<alpha> ll (\<lambda>v'. (aa(v - n := b)) (v' - n)) = robdd_\<alpha> ll a"
    apply (rule_tac robdd_\<alpha>_invar_greater [of "Suc v"]) 
    apply (simp_all add: aa_def)
    apply auto
    done
  from invar(1) have rr_sem: "\<And>b. robdd_\<alpha> rr (\<lambda>v'. (aa(v - n := b)) (v' - n)) = robdd_\<alpha> rr a"
    apply (rule_tac robdd_\<alpha>_invar_greater [of "Suc v"]) 
    apply (simp_all add: aa_def)
    apply auto
    done
    
  show ?case
  proof (cases "robdd_\<alpha> ll a")
    case True with a_sem_neq rr_sem show ?thesis 
      apply (simp)
      apply (rule_tac exI[where x = "aa(v-n := False)"]) 
      apply simp
      done
  next
    case False with a_sem_neq ll_sem show ?thesis 
      apply (simp)
      apply (rule_tac exI[where x = "aa(v-n := True)"]) 
      apply simp
      done
  qed
next
  case prems: (3 i ll v rr n b bs)

  note invar = prems(6,7)
  hence invar_rr: "robdd_invar_vars_greater (Suc n) rr" and red_ll: "robdd_invar_reduced ll"
    and invar_ll: "robdd_invar_vars_greater (Suc n) ll" and red_rr: "robdd_invar_reduced rr"
    and invar_n: "n \<noteq> v \<Longrightarrow> robdd_invar_vars_greater (Suc n) (robdd_var i ll v rr)"
    and n_le: "n \<le> v"
  using robdd_invar_vars_greater___weaken [of "Suc v" _ "Suc n"] by simp_all

  note indhyp_1 = prems(1)[OF _ _ invar_ll red_ll]
  note indhyp_2 = prems(2)[OF _ _ invar_rr red_rr]
  note indhyp_3 = prems(3)[of True, OF _ _ _ invar_ll red_ll, simplified]
  note indhyp_4 = prems(4)[of False, OF _ _ _ invar_rr red_rr, simplified]
  note indhyp_5 = prems(5)[OF _ invar_n invar(2), simplified]

  from invar_ll have ll_sem: "\<And>a b. robdd_\<alpha> ll (\<lambda>v. case_nat b a (v - n)) = robdd_\<alpha> ll 
                                     (\<lambda>v. a (v - Suc n))"
    apply (rule_tac robdd_\<alpha>_invar_greater [of "Suc n"]) 
    apply (simp_all split: nat.splits)
    apply (metis diff_Suc nat.case(2))
    done

  from invar_rr have rr_sem: "\<And>a b. robdd_\<alpha> rr (\<lambda>v. case_nat b a (v - n)) = robdd_\<alpha> rr 
                                     (\<lambda>v. a (v - Suc n))"
    apply (rule_tac robdd_\<alpha>_invar_greater [of "Suc n"]) 
    apply (simp_all split: nat.splits)
    apply (metis diff_Suc nat.case(2))
    done

  show ?case
  proof (cases "n = v")
    case False with n_le have n_less: "n < v" by simp
    hence "v - n = Suc (v - (Suc n))" by simp
    with indhyp_5 n_less
    show ?thesis 
      apply (simp add: Ball_def all_conj_distrib del: Suc_diff)
      apply (cases b)
      apply (simp_all add: image_iff Bex_def ex_disj_distrib all_conj_distrib imp_conjR
                       shift_assignment_def imp_ex all_simps(6)[symmetric]
                       ll_sem rr_sem split: nat.split
                  del: ex_simps all_simps Suc_diff)
      
      
    done
  next
    case True note n_eq[simp] = this

    from indhyp_1 indhyp_2 indhyp_3 indhyp_4
    show ?thesis apply (simp add: Ball_def split: option.splits bool.splits)  
      apply (simp_all add: image_iff Bex_def ex_disj_distrib all_conj_distrib imp_conjR
                       shift_assignment_def imp_ex all_simps(6)[symmetric]
                       ll_sem[unfolded n_eq] rr_sem[unfolded n_eq] 
                  del: ex_simps all_simps)
    done
  qed
qed

lemma robdd_list_\<alpha>_correct:
assumes b_OK: "robdd_invar_vars b" "robdd_invar_reduced b"
shows "robdd_list_\<alpha> b 0 l \<longleftrightarrow> (\<forall>a \<in> (list_to_assignment_set l). robdd_\<alpha> b a)"
using robdd_list_\<alpha>_correct_aux [of 0 b] b_OK unfolding robdd_invar_vars_def by simp


fun robdd_iteratei where
  "robdd_iteratei n ac (robdd_leaf f) = (if f then set_iterator_sng ac else set_iterator_emp)" |
  "robdd_iteratei n ac (robdd_var i l v r) = 
   (set_iterator_union (robdd_iteratei (Suc v) ((Some True) # ((replicate (v-n) None) @ ac)) l)
                       (robdd_iteratei (Suc v) ((Some False) # ((replicate (v-n) None) @ ac)) r))"

(* TODO: Prove correctness of this iterator *)      


end
