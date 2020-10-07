(* Martin Kleppmann, University of Cambridge
   Victor B. F. Gomes, University of Cambridge
   Dominic P. Mulligan, Arm Research, Cambridge
   Alastair Beresford, University of Cambridge
*)

section\<open>The Replicated Growable Array (RGA)\<close>

text\<open>The RGA algorithm \cite{Roh:2011dw} is a replicated list (or
collaborative text-editing) algorithm. In this section we prove that
RGA satisfies our list specification. The Isabelle/HOL definition of
RGA in this section is based on our prior work on formally verifying
CRDTs \cite{Gomes:2017gy,Gomes:2017vo}.\<close>

theory RGA
  imports Insert_Spec
begin

fun insert_body :: "'oid::{linorder} list \<Rightarrow> 'oid \<Rightarrow> 'oid list" where
  "insert_body []       e = [e]" |
  "insert_body (x # xs) e =
     (if x < e then e # x # xs
               else x # insert_body xs e)"

fun insert_rga :: "'oid::{linorder} list \<Rightarrow> ('oid \<times> 'oid option) \<Rightarrow> 'oid list" where
  "insert_rga  xs      (e, None)   = insert_body xs e" |
  "insert_rga  []      (e, Some i) = []" |
  "insert_rga (x # xs) (e, Some i) =
     (if x = i then
        x # insert_body xs e
      else
        x # insert_rga xs (e, Some i))"

definition interp_rga :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> 'oid list" where
  "interp_rga ops \<equiv> foldl insert_rga [] ops"


subsection\<open>Commutativity of \isa{insert-rga}\<close>

lemma insert_body_set_ins [simp]:
  shows  "set (insert_body xs e) = insert e (set xs)"
  by (induction xs, auto)

lemma insert_rga_set_ins:
  assumes "i \<in> set xs"
  shows "set (insert_rga xs (oid, Some i)) = insert oid (set xs)"
  using assms by (induction xs, auto)

lemma insert_body_commutes:
  shows "insert_body (insert_body xs e1) e2 = insert_body (insert_body xs e2) e1"
  by (induction xs, auto)

lemma insert_rga_insert_body_commute:
  assumes "i2 \<noteq> Some e1"
  shows "insert_rga (insert_body xs e1) (e2, i2) = insert_body (insert_rga xs (e2, i2)) e1"
  using assms by (induction xs; cases i2) (auto simp add: insert_body_commutes)

lemma insert_rga_None_commutes:
  assumes "i2 \<noteq> Some e1"
  shows "insert_rga (insert_rga xs (e1, None)) (e2, i2  ) =
         insert_rga (insert_rga xs (e2, i2  )) (e1, None)"
  using assms by (induction xs; cases i2) (auto simp add: insert_body_commutes)

lemma insert_rga_nonexistent:
  assumes "i \<notin> set xs"
  shows "insert_rga xs (e, Some i) = xs"
  using assms by (induction xs, auto)

lemma insert_rga_Some_commutes:
  assumes "i1 \<in> set xs" and "i2 \<in> set xs"
    and "e1 \<noteq> i2" and "e2 \<noteq> i1"
  shows "insert_rga (insert_rga xs (e1, Some i1)) (e2, Some i2) =
         insert_rga (insert_rga xs (e2, Some i2)) (e1, Some i1)"
  using assms proof (induction xs, simp)
  case (Cons a xs)
  then show ?case
    by (cases "a = i1"; cases "a = i2";
        auto simp add: insert_body_commutes insert_rga_insert_body_commute)
qed

lemma insert_rga_commutes:
  assumes "i2 \<noteq> Some e1" and "i1 \<noteq> Some e2"
  shows "insert_rga (insert_rga xs (e1, i1)) (e2, i2) =
         insert_rga (insert_rga xs (e2, i2)) (e1, i1)"
proof(cases i1)
  case None
  then show ?thesis
    using assms(1) insert_rga_None_commutes by (cases i2, fastforce, blast)
next
  case some_r1: (Some r1)
  then show ?thesis
  proof(cases i2)
    case None
    then show ?thesis 
      using assms(2) insert_rga_None_commutes by fastforce
  next
    case some_r2: (Some r2)
    then show ?thesis
    proof(cases "r1 \<in> set xs \<and> r2 \<in> set xs")
      case True
      then show ?thesis
        using assms some_r1 some_r2 by (simp add: insert_rga_Some_commutes)
    next
      case False
      then show ?thesis
        using assms some_r1 some_r2
        by (metis insert_iff insert_rga_nonexistent insert_rga_set_ins)
    qed
  qed
qed

lemma insert_body_split:
  shows "\<exists>p s. xs = p @ s \<and> insert_body xs e = p @ e # s"
proof(induction xs, force)
  case (Cons a xs)
  then obtain p s where IH: "xs = p @ s \<and> insert_body xs e = p @ e # s"
    by blast
  then show "\<exists>p s. a # xs = p @ s \<and> insert_body (a # xs) e = p @ e # s"
  proof(cases "a < e")
    case True
    then have "a # xs = [] @ (a # p @ s) \<and> insert_body (a # xs) e = [] @ e # (a # p @ s)"
      by (simp add: IH)
    then show ?thesis by blast
  next
    case False
    then have "a # xs = (a # p) @ s \<and> insert_body (a # xs) e = (a # p) @ e # s"
      using IH by auto
    then show ?thesis by blast
  qed
qed

lemma insert_between_elements:
  assumes "xs = pre @ ref # suf"
    and "distinct xs"
    and "\<And>i. i \<in> set xs \<Longrightarrow> i < e"
  shows "insert_rga xs (e, Some ref) = pre @ ref # e # suf"
  using assms proof(induction xs arbitrary: pre, force)
  case (Cons a xs)
  then show "insert_rga (a # xs) (e, Some ref) = pre @ ref # e # suf"
  proof(cases pre)
    case pre_nil: Nil
    then have "a = ref"
      using Cons.prems(1) by auto
    then show ?thesis
      using Cons.prems pre_nil by (cases suf, auto)
  next
    case (Cons b pre')
    then have "insert_rga xs (e, Some ref) = pre' @ ref # e # suf"
      using Cons.IH Cons.prems by auto
    then show ?thesis
      using Cons.prems(1) Cons.prems(2) local.Cons by auto
  qed
qed

lemma insert_rga_after_ref:
  assumes "\<forall>x\<in>set as. a \<noteq> x"
    and "insert_body (cs @ ds) e = cs @ e # ds"
  shows "insert_rga (as @ a # cs @ ds) (e, Some a) = as @ a # cs @ e # ds"
  using assms by (induction as; auto)

lemma insert_rga_preserves_order:
  assumes "i = None \<or> (\<exists>i'. i = Some i' \<and> i' \<in> set xs)"
    and "distinct xs"
  shows "\<exists>pre suf. xs = pre @ suf \<and> insert_rga xs (e, i) = pre @ e # suf"
proof(cases i)
  case None
  then show "\<exists>pre suf. xs = pre @ suf \<and> insert_rga xs (e, i) = pre @ e # suf"
    using insert_body_split by auto
next
  case (Some r)
  moreover from this obtain as bs where "xs = as @ r # bs \<and> (\<forall>x \<in> set as. x \<noteq> r)"
    using assms(1) split_list_first by fastforce
  moreover have "\<exists>cs ds. bs = cs @ ds \<and> insert_body bs e = cs @ e # ds"
    by (simp add: insert_body_split)
  then obtain cs ds where "bs = cs @ ds \<and> insert_body bs e = cs @ e # ds"
    by blast
  ultimately have "xs = (as @ r # cs) @ ds \<and> insert_rga xs (e, i) = (as @ r # cs) @ e # ds"
    using insert_rga_after_ref by fastforce
  then show ?thesis by blast
qed


subsection\<open>Lemmas about the \isa{rga-ops} predicate\<close>

definition rga_ops :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> bool" where
  "rga_ops list \<equiv> crdt_ops list set_option"

lemma rga_ops_rem_last:
  assumes "rga_ops (xs @ [x])"
  shows "rga_ops xs"
  using assms crdt_ops_rem_last rga_ops_def by blast

lemma rga_ops_rem_penultimate:
  assumes "rga_ops (xs @ [(i1, r1), (i2, r2)])"
    and "\<And>r. r2 = Some r \<Longrightarrow> r \<noteq> i1"
  shows "rga_ops (xs @ [(i2, r2)])"
  using assms proof -
  have "crdt_ops (xs @ [(i2, r2)]) set_option"
    using assms crdt_ops_rem_penultimate rga_ops_def by fastforce
  thus "rga_ops (xs @ [(i2, r2)])"
    by (simp add: rga_ops_def)
qed

lemma rga_ops_ref_exists:
  assumes "rga_ops (pre @ (oid, Some ref) # suf)"
  shows "ref \<in> fst ` set pre"
proof -
  from assms have "crdt_ops (pre @ (oid, Some ref) # suf) set_option"
    by (simp add: rga_ops_def)
  moreover have "set_option (Some ref) = {ref}"
    by simp
  ultimately show "ref \<in> fst ` set pre"
    using crdt_ops_ref_exists by fastforce
qed


subsection\<open>Lemmas about the \isa{interp-rga} function\<close>

lemma interp_rga_tail_unfold:
  shows "interp_rga (xs@[x]) = insert_rga (interp_rga (xs)) x"
  by (clarsimp simp add: interp_rga_def)

lemma interp_rga_ids:
  assumes "rga_ops xs"
  shows "set (interp_rga xs) = set (map fst xs)"
  using assms proof(induction xs rule: List.rev_induct)
  case Nil
  then show "set (interp_rga []) = set (map fst [])"
    by (simp add: interp_rga_def)
next
  case (snoc x xs)
  hence IH: "set (interp_rga xs) = set (map fst xs)"
    using rga_ops_rem_last by blast
  obtain xi xr where x_pair: "x = (xi, xr)" by force
  then show "set (interp_rga (xs @ [x])) = set (map fst (xs @ [x]))"
  proof(cases xr)
    case None
    then show ?thesis
      using IH x_pair by (clarsimp simp add: interp_rga_def)
  next
    case (Some r)
    moreover from this have "r \<in> set (interp_rga xs)"
      using IH rga_ops_ref_exists by (metis x_pair list.set_map snoc.prems)
    ultimately have "set (interp_rga (xs @ [(xi, xr)])) = insert xi (set (interp_rga xs))"
      by (simp add: insert_rga_set_ins interp_rga_tail_unfold)
    then show "set (interp_rga (xs @ [x])) = set (map fst (xs @ [x]))"
      using IH x_pair by auto
  qed
qed

lemma interp_rga_distinct:
  assumes "rga_ops xs"
  shows "distinct (interp_rga xs)"
  using assms proof(induction xs rule: List.rev_induct)
  case Nil
  then show "distinct (interp_rga [])" by (simp add: interp_rga_def)
next
  case (snoc x xs)
  hence IH: "distinct (interp_rga xs)"
    using rga_ops_rem_last by blast
  moreover obtain xi xr where x_pair: "x = (xi, xr)"
    by force
  moreover from this have "xi \<notin> set (interp_rga xs)"
    using interp_rga_ids crdt_ops_unique_last rga_ops_rem_last
    by (metis rga_ops_def snoc.prems)
  moreover have "\<exists>pre suf. interp_rga xs = pre@suf \<and>
           insert_rga (interp_rga xs) (xi, xr) = pre @ xi # suf"
  proof -
    have "\<And>r. r \<in> set_option xr \<Longrightarrow> r \<in> set (map fst xs)"
      using crdt_ops_ref_exists rga_ops_def snoc.prems x_pair by fastforce
    hence "xr = None \<or> (\<exists>r. xr = Some r \<and> r \<in> set (map fst xs))"
      using option.set_sel by blast
    hence "xr = None \<or> (\<exists>r. xr = Some r \<and> r \<in> set (interp_rga xs))"
      using interp_rga_ids rga_ops_rem_last snoc.prems by blast
    thus ?thesis
      using IH insert_rga_preserves_order by blast
  qed
  ultimately show "distinct (interp_rga (xs @ [x]))" 
    by (metis Un_iff disjoint_insert(1) distinct.simps(2) distinct_append 
        interp_rga_tail_unfold list.simps(15) set_append)
qed


subsection\<open>Proof that RGA satisfies the list specification\<close>

lemma final_insert:
  assumes "set (xs @ [x]) = set (ys @ [x])"
    and "rga_ops (xs @ [x])"
    and "insert_ops (ys @ [x])"
    and "interp_rga xs = interp_ins ys"
  shows "interp_rga (xs @ [x]) = interp_ins (ys @ [x])"
proof -
  obtain oid ref where x_pair: "x = (oid, ref)" by force
  have "distinct (xs @ [x])" and "distinct (ys @ [x])"
    using assms crdt_ops_distinct spec_ops_distinct rga_ops_def insert_ops_def by blast+
  then have "set xs = set ys"
    using assms(1) by force
  have oid_greatest: "\<And>i. i \<in> set (interp_rga xs) \<Longrightarrow> i < oid"
  proof -
    have "\<And>i. i \<in> set (map fst ys) \<Longrightarrow> i < oid"
      using assms(3) by (simp add: spec_ops_id_inc x_pair insert_ops_def)
    hence "\<And>i. i \<in> set (map fst xs) \<Longrightarrow> i < oid"
      using \<open>set xs = set ys\<close> by auto
    thus "\<And>i. i \<in> set (interp_rga xs) \<Longrightarrow> i < oid"
      using assms(2) interp_rga_ids rga_ops_rem_last by blast
  qed
  thus "interp_rga (xs @ [x]) = interp_ins (ys @ [x])"
  proof(cases ref)
    case None
    moreover from this have "insert_rga (interp_rga xs) (oid, ref) = oid # interp_rga xs"
      using oid_greatest hd_in_set insert_body.elims insert_body.simps(1)
        insert_rga.simps(1) list.sel(1) by metis
    ultimately show "interp_rga (xs @ [x]) = interp_ins (ys @ [x])" 
      using assms(4) by (simp add: interp_ins_tail_unfold interp_rga_tail_unfold x_pair)
  next
    case (Some r)
    have "\<exists>as bs. interp_rga xs = as @ r # bs"
    proof -
      have "r \<in> set (map fst xs)"
        using assms(2) Some by (simp add: rga_ops_ref_exists x_pair)
      hence "r \<in> set (interp_rga xs)"
        using assms(2) interp_rga_ids rga_ops_rem_last by blast
      thus ?thesis by (simp add: split_list)
    qed
    from this obtain as bs where as_bs: "interp_rga xs = as @ r # bs" by force
    hence "distinct (as @ r # bs)"
      by (metis assms(2) interp_rga_distinct rga_ops_rem_last)
    hence "insert_rga (as @ r # bs) (oid, Some r) = as @ r # oid # bs"
      by (metis as_bs insert_between_elements oid_greatest)
    moreover have "insert_spec (as @ r # bs) (oid, Some r) = as @ r # oid # bs"
      by (meson \<open>distinct (as @ r # bs)\<close> insert_after_ref)
    ultimately show "interp_rga (xs @ [x]) = interp_ins (ys @ [x])" 
      by (metis assms(4) Some as_bs interp_ins_tail_unfold interp_rga_tail_unfold x_pair)
  qed
qed

lemma interp_rga_reorder:
  assumes "rga_ops (pre @ suf @ [(oid, ref)])"
    and "\<And>i r. (i, Some r) \<in> set suf \<Longrightarrow> r \<noteq> oid"
    and "\<And>r. ref = Some r \<Longrightarrow> r \<notin> fst ` set suf"
  shows "interp_rga (pre @ (oid, ref) # suf) = interp_rga (pre @ suf @ [(oid, ref)])"
  using assms proof(induction suf rule: List.rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  have ref_not_x: "\<And>r. ref = Some r \<Longrightarrow> r \<noteq> fst x" using snoc.prems(3) by auto
  have IH: "interp_rga (pre @ (oid, ref) # xs) = interp_rga (pre @ xs @ [(oid, ref)])"
  proof -
    have "rga_ops ((pre @ xs) @ [x] @ [(oid, ref)])"
      using snoc.prems(1) by auto
    moreover have "\<And>r. ref = Some r \<Longrightarrow> r \<noteq> fst x"
      by (simp add: ref_not_x)
    ultimately have "rga_ops ((pre @ xs) @ [(oid, ref)])"
      using rga_ops_rem_penultimate
      by (metis (no_types, lifting) Cons_eq_append_conv prod.collapse)
    thus ?thesis using snoc by force
  qed
  obtain xi xr where x_pair: "x = (xi, xr)" by force
  have "interp_rga (pre @ (oid, ref) # xs @ [(xi, xr)]) =
        insert_rga (interp_rga (pre @ xs @ [(oid, ref)])) (xi, xr)"
    using IH interp_rga_tail_unfold by (metis append.assoc append_Cons)
  moreover have "... = insert_rga (insert_rga (interp_rga (pre @ xs)) (oid, ref)) (xi, xr)"
    using interp_rga_tail_unfold by (metis append_assoc)
  moreover have "... = insert_rga (insert_rga (interp_rga (pre @ xs)) (xi, xr)) (oid, ref)"
  proof -
    have "\<And>xrr. xr = Some xrr \<Longrightarrow> xrr \<noteq> oid"
      using x_pair snoc.prems(2) by auto
    thus ?thesis
      using insert_rga_commutes ref_not_x by (metis fst_conv x_pair)
  qed
  moreover have "... = interp_rga (pre @ xs @ [x] @ [(oid, ref)])"
    by (metis append_assoc interp_rga_tail_unfold x_pair)
  ultimately show "interp_rga (pre @ (oid, ref) # xs @ [x]) =
                   interp_rga (pre @ (xs @ [x]) @ [(oid, ref)])"
    by (simp add: x_pair)
qed

lemma rga_spec_equal:
  assumes "set xs = set ys"
    and "insert_ops xs"
    and "rga_ops ys"
  shows "interp_ins xs = interp_rga ys"
  using assms proof(induction xs arbitrary: ys rule: rev_induct)
  case Nil
  then show ?case by (simp add: interp_rga_def interp_ins_def)
next
  case (snoc x xs)
  hence "x \<in> set ys"
    by (metis last_in_set snoc_eq_iff_butlast)
  from this obtain pre suf where ys_split: "ys = pre @ [x] @ suf"
    using split_list_first by fastforce
  have IH: "interp_ins xs = interp_rga (pre @ suf)"
  proof -
    have "crdt_ops (pre @ suf) set_option"
    proof -
      have "crdt_ops (pre @ [x] @ suf) set_option"
        using rga_ops_def snoc.prems(3) ys_split by blast
      thus "crdt_ops (pre @ suf) set_option"
        using crdt_ops_rem_spec snoc.prems ys_split insert_ops_def by blast
    qed
    hence "rga_ops (pre @ suf)"
      using rga_ops_def by blast
    moreover have "set xs = set (pre @ suf)"
      by (metis append_set_rem_last crdt_ops_distinct insert_ops_def rga_ops_def
          snoc.prems spec_ops_distinct ys_split)
    ultimately show ?thesis
      using insert_ops_rem_last ys_split snoc by metis
  qed
  have valid_rga: "rga_ops (pre @ suf @ [x])"
  proof -
    have "crdt_ops (pre @ suf @ [x]) set_option"
      using snoc.prems ys_split
      by (simp add: crdt_ops_reorder_spec insert_ops_def rga_ops_def)
    thus "rga_ops (pre @ suf @ [x])"
      by (simp add: rga_ops_def)
  qed
  have "interp_ins (xs @ [x]) = interp_rga (pre @ suf @ [x])"
  proof -
    have "set (xs @ [x]) = set (pre @ suf @ [x])"
      using snoc.prems(1) ys_split by auto
    thus ?thesis
      using IH snoc.prems(2) valid_rga final_insert append_assoc by metis
  qed
  moreover have "... = interp_rga (pre @ [x] @ suf)"
  proof -
    obtain oid ref where x_pair: "x = (oid, ref)"
      by force
    have "\<And>op2 r. op2 \<in> snd ` set suf \<Longrightarrow> r \<in> set_option op2 \<Longrightarrow> r \<noteq> oid"
      using snoc.prems
      by (simp add: crdt_ops_independent_suf insert_ops_def rga_ops_def x_pair ys_split)
    hence "\<And>i r. (i, Some r) \<in> set suf \<Longrightarrow> r \<noteq> oid"
      by fastforce 
    moreover have "\<And>r. ref = Some r \<Longrightarrow> r \<notin> fst ` set suf"
      using crdt_ops_no_future_ref snoc.prems(3) x_pair ys_split
      by (metis option.set_intros rga_ops_def)
    ultimately show "interp_rga (pre @ suf @ [x]) = interp_rga (pre @ [x] @ suf)"
      using interp_rga_reorder valid_rga x_pair by force
  qed
  ultimately show "interp_ins (xs @ [x]) = interp_rga ys"
    by (simp add: ys_split)
qed

lemma insert_ops_exist:
  assumes "rga_ops xs"
  shows "\<exists>ys. set xs = set ys \<and> insert_ops ys"
  using assms by (simp add: crdt_ops_spec_ops_exist insert_ops_def rga_ops_def)

theorem rga_meets_spec:
  assumes "rga_ops xs"
  shows "\<exists>ys. set ys = set xs \<and> insert_ops ys \<and> interp_ins ys = interp_rga xs"
  using assms rga_spec_equal insert_ops_exist by metis

end
