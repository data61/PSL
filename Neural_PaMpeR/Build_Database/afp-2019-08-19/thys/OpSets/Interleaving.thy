(* Martin Kleppmann, University of Cambridge
   Victor B. F. Gomes, University of Cambridge
   Dominic P. Mulligan, Arm Research, Cambridge
   Alastair Beresford, University of Cambridge
*)

section\<open>Interleaving of concurrent insertions\<close>

text\<open>In this section we prove that our list specification rules out
interleaving of concurrent insertion sequences starting at the same position.\<close>

theory Interleaving
  imports Insert_Spec
begin

subsection\<open>Lemmas about \isa{insert-ops}\<close>

lemma map_fst_append1:
  assumes "\<forall>i \<in> set (map fst xs). P i"
    and "P x"
  shows "\<forall>i \<in> set (map fst (xs @ [(x, y)])). P i"
  using assms by (induction xs, auto)

lemma insert_ops_split:
  assumes "insert_ops ops"
    and "(oid, ref) \<in> set ops"
  shows "\<exists>pre suf. ops = pre @ [(oid, ref)] @ suf \<and>
            (\<forall>i \<in> set (map fst pre). i < oid) \<and>
            (\<forall>i \<in> set (map fst suf). oid < i)"
  using assms proof(induction ops rule: List.rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case
  proof(cases "x = (oid, ref)")
    case True
    moreover from this have "\<forall>i \<in> set (map fst xs). i < oid"
      using last_op_greatest snoc.prems(1) by blast
    ultimately have "xs @ [x] = xs @ [(oid, ref)] @ [] \<and>
            (\<forall>i \<in> set (map fst xs). i < oid) \<and>
            (\<forall>i \<in> set (map fst []). oid < i)"
      by auto
    then show ?thesis by force
  next
    case False
    hence "(oid, ref) \<in> set xs"
      using snoc.prems(2) by auto
    from this obtain pre suf where IH: "xs = pre @ [(oid, ref)] @ suf \<and>
         (\<forall>i \<in> set (map fst pre). i < oid) \<and>
         (\<forall>i \<in> set (map fst suf). oid < i)"
      using snoc.IH snoc.prems(1) by blast
    obtain xi xr where x_pair: "x = (xi, xr)"
      by force
    hence "distinct (map fst (pre @ [(oid, ref)] @ suf @ [(xi, xr)]))"
      by (metis IH append.assoc insert_ops_def spec_ops_def snoc.prems(1))
    hence "xi \<noteq> oid"
      by auto
    have xi_max: "\<forall>x \<in> set (map fst (pre @ [(oid, ref)] @ suf)). x < xi"
      using IH last_op_greatest snoc.prems(1) x_pair by blast
    then show ?thesis
    proof(cases "xi < oid")
      case True
      moreover from this have "\<forall>x \<in> set suf. fst x < oid"
        using xi_max by auto
      hence "suf = []"
        using IH last_in_set by fastforce
      ultimately have "xs @ [x] = (pre @ [(xi, xr)]) @ [] \<and>
              (\<forall>i \<in> set (map fst ((pre @ [(xi, xr)]))). i < oid) \<and>
              (\<forall>i \<in> set (map fst []). oid < i)"
        using dual_order.asym xi_max by auto
      then show ?thesis by (simp add: IH)
    next
      case False
      hence "oid < xi"
        using \<open>xi \<noteq> oid\<close> by auto
      hence "\<forall>i \<in> set (map fst (suf @ [(xi, xr)])). oid < i"
        using IH map_fst_append1 by auto
      hence "xs @ [x] = pre @ [(oid, ref)] @ (suf @ [(xi, xr)]) \<and>
              (\<forall>i \<in> set (map fst pre). i < oid) \<and>
              (\<forall>i \<in> set (map fst (suf @ [(xi, xr)])). oid < i)"
        by (simp add: IH x_pair)
      then show ?thesis by blast
    qed
  qed
qed

lemma insert_ops_split_2:
  assumes "insert_ops ops"
    and "(xid, xr) \<in> set ops"
    and "(yid, yr) \<in> set ops"
    and "xid < yid"
  shows "\<exists>as bs cs. ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs \<and>
           (\<forall>i \<in> set (map fst as). i < xid) \<and>
           (\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid) \<and>
           (\<forall>i \<in> set (map fst cs). yid < i)"
proof -
  obtain as as1 where x_split: "ops = as @ [(xid, xr)] @ as1 \<and>
      (\<forall>i \<in> set (map fst as). i < xid) \<and> (\<forall>i \<in> set (map fst as1). xid < i)"
    using assms insert_ops_split by blast
  hence "insert_ops ((as @ [(xid, xr)]) @ as1)"
    using assms(1) by auto
  hence "insert_ops as1"
    using assms(1) insert_ops_rem_prefix by blast
  have "(yid, yr) \<in> set as1"
    using x_split assms by auto
  from this obtain bs cs where y_split: "as1 = bs @ [(yid, yr)] @ cs \<and>
      (\<forall>i \<in> set (map fst bs). i < yid) \<and> (\<forall>i \<in> set (map fst cs). yid < i)"
    using assms insert_ops_split \<open>insert_ops as1\<close> by blast
  hence "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs"
    using x_split by blast
  moreover have "\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid"
    by (simp add: x_split y_split)
  ultimately show ?thesis
    using x_split y_split by blast
qed

lemma insert_ops_sorted_oids:
  assumes "insert_ops (xs @ [(i1, r1)] @ ys @ [(i2, r2)])"
  shows "i1 < i2"
proof -
  have "\<And>i. i \<in> set (map fst (xs @ [(i1, r1)] @ ys)) \<Longrightarrow> i < i2"
    by (metis append.assoc assms last_op_greatest)
  moreover have "i1 \<in> set (map fst (xs @ [(i1, r1)] @ ys))"
    by auto
  ultimately show "i1 < i2"
    by blast
qed

lemma insert_ops_subset_last:
  assumes "insert_ops (xs @ [x])"
    and "insert_ops ys"
    and "set ys \<subseteq> set (xs @ [x])"
    and "x \<in> set ys"
  shows "x = last ys"
  using assms proof(induction ys, simp)
  case (Cons y ys)
  then show "x = last (y # ys)"
  proof(cases "ys = []")
    case True
    then show "x = last (y # ys)"
      using Cons.prems(4) by auto
  next
    case ys_nonempty: False
    have "x \<noteq> y"
    proof -
      obtain mid l where "ys = mid @ [l]"
        using append_butlast_last_id ys_nonempty by metis
      moreover obtain li lr where "l = (li, lr)"
        by force
      moreover have "\<And>i. i \<in> set (map fst (y # mid)) \<Longrightarrow> i < li"
        by (metis last_op_greatest Cons.prems(2) calculation append_Cons)
      hence "fst y < li"
        by simp
      moreover have "\<And>i. i \<in> set (map fst xs) \<Longrightarrow> i < fst x"
        using assms(1) last_op_greatest by (metis prod.collapse)
      hence "\<And>i. i \<in> set (map fst (y # ys)) \<Longrightarrow> i \<le> fst x"
        using Cons.prems(3) by fastforce
      ultimately show "x \<noteq> y"
        by fastforce
    qed
    then show "x = last (y # ys)"
      using Cons.IH Cons.prems insert_ops_rem_cons ys_nonempty
      by (metis dual_order.trans last_ConsR set_ConsD set_subset_Cons)
  qed
qed

lemma subset_butlast:
  assumes "set xs \<subseteq> set (ys @ [y])"
    and "last xs = y"
    and "distinct xs"
  shows "set (butlast xs) \<subseteq> set ys"
  using assms by (induction xs, auto)

lemma distinct_append_butlast1:
  assumes "distinct (map fst xs @ map fst ys)"
  shows "distinct (map fst (butlast xs) @ map fst ys)"
  using assms proof(induction xs, simp)
  case (Cons a xs)
  have "fst a \<notin> set (map fst xs @ map fst ys)"
    using Cons.prems by auto
  moreover have "set (map fst (butlast xs)) \<subseteq> set (map fst xs)"
    by (metis in_set_butlastD map_butlast subsetI)
  hence "set (map fst (butlast xs) @ map fst ys) \<subseteq> set (map fst xs @ map fst ys)"
    by auto
  ultimately have "fst a \<notin> set (map fst (butlast xs) @ map fst ys)"
    by blast
  then show "distinct (map fst (butlast (a # xs)) @ map fst ys)"
    using Cons.IH Cons.prems by auto
qed

lemma distinct_append_butlast2:
  assumes "distinct (map fst xs @ map fst ys)"
  shows "distinct (map fst xs @ map fst (butlast ys))"
  using assms proof(induction xs)
  case Nil
  then show "distinct (map fst [] @ map fst (butlast ys))"
    by (simp add: distinct_butlast map_butlast)
next
  case (Cons a xs)
  have "fst a \<notin> set (map fst xs @ map fst ys)"
    using Cons.prems by auto
  moreover have "set (map fst (butlast ys)) \<subseteq> set (map fst ys)"
    by (metis in_set_butlastD map_butlast subsetI)
  hence "set (map fst xs @ map fst (butlast ys)) \<subseteq> set (map fst xs @ map fst ys)"
    by auto
  ultimately have "fst a \<notin> set (map fst xs @ map fst (butlast ys))"
    by blast
  then show ?case
    using Cons.IH Cons.prems by auto
qed


subsection\<open>Lemmas about \isa{interp-ins}\<close>

lemma interp_ins_maybe_grow:
  assumes "insert_ops (xs @ [(oid, ref)])"
  shows "set (interp_ins (xs @ [(oid, ref)])) = set (interp_ins xs) \<or>
         set (interp_ins (xs @ [(oid, ref)])) = (set (interp_ins xs) \<union> {oid})"
  by (cases ref, simp add: interp_ins_tail_unfold,
      metis insert_spec_nonex insert_spec_set interp_ins_tail_unfold)

lemma interp_ins_maybe_grow2:
  assumes "insert_ops (xs @ [x])"
  shows "set (interp_ins (xs @ [x])) = set (interp_ins xs) \<or>
         set (interp_ins (xs @ [x])) = (set (interp_ins xs) \<union> {fst x})"
  using assms interp_ins_maybe_grow by (cases x, auto)

lemma interp_ins_maybe_grow3:
  assumes "insert_ops (xs @ ys)"
  shows "\<exists>A. A \<subseteq> set (map fst ys) \<and> set (interp_ins (xs @ ys)) = set (interp_ins xs) \<union> A"
  using assms proof(induction ys rule: List.rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x ys)
  then have "insert_ops (xs @ ys)"
    by (metis append_assoc insert_ops_rem_last)
  then obtain A where IH: "A \<subseteq> set (map fst ys) \<and>
            set (interp_ins (xs @ ys)) = set (interp_ins xs) \<union> A"
    using snoc.IH by blast
  then show ?case
  proof(cases "set (interp_ins (xs @ ys @ [x])) = set (interp_ins (xs @ ys))")
    case True
    moreover have "A \<subseteq> set (map fst (ys @ [x]))"
      using IH by auto
    ultimately show ?thesis
      using IH by auto
  next
    case False
    then have "set (interp_ins (xs @ ys @ [x])) = set (interp_ins (xs @ ys)) \<union> {fst x}"
      by (metis append_assoc interp_ins_maybe_grow2 snoc.prems)
    moreover have "A \<union> {fst x} \<subseteq> set (map fst (ys @ [x]))"
      using IH by auto
    ultimately show ?thesis
      using IH Un_assoc by metis
  qed
qed

lemma interp_ins_ref_nonex:
  assumes "insert_ops ops"
    and "ops = xs @ [(oid, Some ref)] @ ys"
    and "ref \<notin> set (interp_ins xs)"
  shows "oid \<notin> set (interp_ins ops)"
  using assms proof(induction ys arbitrary: ops rule: List.rev_induct)
  case Nil
  then have "interp_ins ops = insert_spec (interp_ins xs) (oid, Some ref)"
    by (simp add: interp_ins_tail_unfold)
  moreover have "\<And>i. i \<in> set (map fst xs) \<Longrightarrow> i < oid"
    using Nil.prems last_op_greatest by fastforce
  hence "\<And>i. i \<in> set (interp_ins xs) \<Longrightarrow> i < oid"
    by (meson interp_ins_subset subsetCE)
  ultimately show "oid \<notin> set (interp_ins ops)"
    using assms(3) by auto
next
  case (snoc x ys)
  then have "insert_ops (xs @ (oid, Some ref) # ys)"
    by (metis append.assoc append.simps(1) append_Cons insert_ops_appendD)
  hence IH: "oid \<notin> set (interp_ins (xs @ (oid, Some ref) # ys))"
    by (simp add: snoc.IH snoc.prems(3))
  moreover have "distinct (map fst (xs @ (oid, Some ref) # ys @ [x]))"
    using snoc.prems by (metis append_Cons append_self_conv2 insert_ops_def spec_ops_def)
  hence "fst x \<noteq> oid"
    using empty_iff by auto
  moreover have "insert_ops ((xs @ (oid, Some ref) # ys) @ [x])"
    using snoc.prems by auto
  hence "set (interp_ins ((xs @ (oid, Some ref) # ys) @ [x])) =
         set (interp_ins (xs @ (oid, Some ref) # ys)) \<or> 
         set (interp_ins ((xs @ (oid, Some ref) # ys) @ [x])) =
         set (interp_ins (xs @ (oid, Some ref) # ys)) \<union> {fst x}"
    using interp_ins_maybe_grow2 by blast
  ultimately show "oid \<notin> set (interp_ins ops)"
    using snoc.prems(2) by auto
qed

lemma interp_ins_last_None:
  shows "oid \<in> set (interp_ins (ops @ [(oid, None)]))"
  by (simp add: interp_ins_tail_unfold)

lemma interp_ins_monotonic:
  assumes "insert_ops (pre @ suf)"
    and "oid \<in> set (interp_ins pre)"
  shows "oid \<in> set (interp_ins (pre @ suf))"
  using assms interp_ins_maybe_grow3 by auto

lemma interp_ins_append_non_memb:
  assumes "insert_ops (pre @ [(oid, Some ref)] @ suf)"
    and "ref \<notin> set (interp_ins pre)"
  shows "ref \<notin> set (interp_ins (pre @ [(oid, Some ref)] @ suf))"
  using assms proof(induction suf rule: List.rev_induct)
  case Nil
  then show "ref \<notin> set (interp_ins (pre @ [(oid, Some ref)] @ []))"
    by (metis append_Nil2 insert_spec_nonex interp_ins_tail_unfold)
next
  case (snoc x xs)
  hence IH: "ref \<notin> set (interp_ins (pre @ [(oid, Some ref)] @ xs))"
    by (metis append_assoc insert_ops_rem_last)
  moreover have "ref < oid"
    using insert_ops_ref_older snoc.prems(1) by auto
  moreover have "oid < fst x"
    using insert_ops_sorted_oids by (metis prod.collapse snoc.prems(1))
  have "set (interp_ins ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (interp_ins (pre @ [(oid, Some ref)] @ xs)) \<or>
        set (interp_ins ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (interp_ins (pre @ [(oid, Some ref)] @ xs)) \<union> {fst x}"
    by (metis (full_types) append.assoc interp_ins_maybe_grow2 snoc.prems(1))
  ultimately show "ref \<notin> set (interp_ins (pre @ [(oid, Some ref)] @ xs @ [x]))"
    using \<open>oid < fst x\<close> by auto
qed

lemma interp_ins_append_memb:
  assumes "insert_ops (pre @ [(oid, Some ref)] @ suf)"
    and "ref \<in> set (interp_ins pre)"
  shows "oid \<in> set (interp_ins (pre @ [(oid, Some ref)] @ suf))"
  using assms by (metis UnCI append_assoc insert_spec_set interp_ins_monotonic
      interp_ins_tail_unfold singletonI)

lemma interp_ins_append_forward:
  assumes "insert_ops (xs @ ys)"
    and "oid \<in> set (interp_ins (xs @ ys))"
    and "oid \<in> set (map fst xs)"
  shows "oid \<in> set (interp_ins xs)"
  using assms proof(induction ys rule: List.rev_induct, simp)
  case (snoc y ys)
  obtain cs ds ref where "xs = cs @ (oid, ref) # ds"
    by (metis (no_types, lifting) imageE prod.collapse set_map snoc.prems(3) split_list_last)
  hence "insert_ops (cs @ [(oid, ref)] @ (ds @ ys) @ [y])"
    using snoc.prems(1) by auto
  hence "oid < fst y"
    using insert_ops_sorted_oids by (metis prod.collapse)
  hence "oid \<noteq> fst y"
    by blast
  then show ?case
    using snoc.IH snoc.prems(1) snoc.prems(2) assms(3) inserted_item_ident
    by (metis append_assoc insert_ops_appendD interp_ins_tail_unfold prod.collapse)
qed

lemma interp_ins_find_ref:
  assumes "insert_ops (xs @ [(oid, Some ref)] @ ys)"
    and "ref \<in> set (interp_ins (xs @ [(oid, Some ref)] @ ys))"
  shows "\<exists>r. (ref, r) \<in> set xs"
proof -
  have "ref < oid"
    using assms(1) insert_ops_ref_older by blast
  have "ref \<in> set (map fst (xs @ [(oid, Some ref)] @ ys))"
    by (meson assms(2) interp_ins_subset subsetCE)
  then obtain x where x_prop: "x \<in> set (xs @ [(oid, Some ref)] @ ys) \<and> fst x = ref"
    by fastforce
  obtain xr where x_pair: "x = (ref, xr)"
    using prod.exhaust_sel x_prop by blast
  show "\<exists>r. (ref, r) \<in> set xs"
  proof(cases "x \<in> set xs")
    case True
    then show "\<exists>r. (ref, r) \<in> set xs"
      by (metis x_prop prod.collapse)
  next
    case False
    hence "(ref, xr) \<in> set ([(oid, Some ref)] @ ys)"
      using x_prop x_pair by auto
    hence "(ref, xr) \<in> set ys"
      using \<open>ref < oid\<close> x_prop
      by (metis append_Cons append_self_conv2 fst_conv min.strict_order_iff set_ConsD)
    then obtain as bs where "ys = as @ (ref, xr) # bs"
      by (meson split_list)
    hence "insert_ops ((xs @ [(oid, Some ref)] @ as @ [(ref, xr)]) @ bs)"
      using assms(1) by auto
    hence "insert_ops (xs @ [(oid, Some ref)] @ as @ [(ref, xr)])"
      using insert_ops_appendD by blast
    hence "oid < ref" (* contradiction *)
      using insert_ops_sorted_oids by auto
    then show ?thesis
      using \<open>ref < oid\<close> by force
  qed
qed


subsection\<open>Lemmas about \isa{list-order}\<close>

lemma list_order_append:
  assumes "insert_ops (pre @ suf)"
    and "list_order pre x y"
  shows "list_order (pre @ suf) x y"
  by (metis Un_iff assms list_order_monotonic insert_ops_appendD set_append subset_code(1))

lemma list_order_insert_ref:
  assumes "insert_ops (ops @ [(oid, Some ref)])"
    and "ref \<in> set (interp_ins ops)"
  shows "list_order (ops @ [(oid, Some ref)]) ref oid"
proof -
  have "interp_ins (ops @ [(oid, Some ref)]) = insert_spec (interp_ins ops) (oid, Some ref)"
    by (simp add: interp_ins_tail_unfold)
  moreover obtain xs ys where "interp_ins ops = xs @ [ref] @ ys"
    using assms(2) split_list_first by fastforce
  hence "insert_spec (interp_ins ops) (oid, Some ref) = xs @ [ref] @ [] @ [oid] @ ys"
    using assms(1) insert_after_ref interp_ins_distinct by fastforce
  ultimately show "list_order (ops @ [(oid, Some ref)]) ref oid"
    using assms(1) list_orderI by metis
qed

lemma list_order_insert_none:
  assumes "insert_ops (ops @ [(oid, None)])"
    and "x \<in> set (interp_ins ops)"
  shows "list_order (ops @ [(oid, None)]) oid x"
proof -
  have "interp_ins (ops @ [(oid, None)]) = insert_spec (interp_ins ops) (oid, None)"
    by (simp add: interp_ins_tail_unfold)
  moreover obtain xs ys where "interp_ins ops = xs @ [x] @ ys"
    using assms(2) split_list_first by fastforce
  hence "insert_spec (interp_ins ops) (oid, None) = [] @ [oid] @ xs @ [x] @ ys"
    by simp
  ultimately show "list_order (ops @ [(oid, None)]) oid x"
    using assms(1) list_orderI by metis
qed

lemma list_order_insert_between:
  assumes "insert_ops (ops @ [(oid, Some ref)])"
    and "list_order ops ref x"
  shows "list_order (ops @ [(oid, Some ref)]) oid x"
proof -
  have "interp_ins (ops @ [(oid, Some ref)]) = insert_spec (interp_ins ops) (oid, Some ref)"
    by (simp add: interp_ins_tail_unfold)
  moreover obtain xs ys zs where "interp_ins ops = xs @ [ref] @ ys @ [x] @ zs"
    using assms list_orderE by blast
  moreover have "... = xs @ ref # (ys @ [x] @ zs)"
    by simp
  moreover have "distinct (xs @ ref # (ys @ [x] @ zs))"
    using assms(1) calculation by (metis interp_ins_distinct insert_ops_rem_last)
  hence "insert_spec (xs @ ref # (ys @ [x] @ zs)) (oid, Some ref) = xs @ ref # oid # (ys @ [x] @ zs)"
    using assms(1) calculation by (simp add: insert_after_ref)
  moreover have "... = (xs @ [ref]) @ [oid] @ ys @ [x] @ zs"
    by simp
  ultimately show "list_order (ops @ [(oid, Some ref)]) oid x"
    using assms(1) list_orderI by metis
qed


subsection\<open>The \isa{insert-seq} predicate\<close>

text\<open>The predicate \isa{insert-seq start ops} is true iff \isa{ops} is a list
of insertion operations that begins by inserting after \isa{start}, and then
continues by placing each subsequent insertion directly after its predecessor.
This definition models the sequential insertion of text at a particular place
in a text document.\<close>

inductive insert_seq :: "'oid option \<Rightarrow> ('oid \<times> 'oid option) list \<Rightarrow> bool" where
  "insert_seq start [(oid, start)]" |
  "\<lbrakk>insert_seq start (list @ [(prev, ref)])\<rbrakk>
      \<Longrightarrow> insert_seq start (list @ [(prev, ref), (oid, Some prev)])"

lemma insert_seq_nonempty:
  assumes "insert_seq start xs"
  shows "xs \<noteq> []"
  using assms by (induction rule: insert_seq.induct, auto)

lemma insert_seq_hd:
  assumes "insert_seq start xs"
  shows "\<exists>oid. hd xs = (oid, start)"
  using assms by (induction rule: insert_seq.induct, simp,
      metis append_self_conv2 hd_append2 list.sel(1))

lemma insert_seq_rem_last:
  assumes "insert_seq start (xs @ [x])"
    and "xs \<noteq> []"
  shows "insert_seq start xs"
  using assms insert_seq.cases by fastforce

lemma insert_seq_butlast:
  assumes "insert_seq start xs"
    and "xs \<noteq> []" and "xs \<noteq> [last xs]"
  shows "insert_seq start (butlast xs)"
proof -
  have "length xs > 1"
    by (metis One_nat_def Suc_lessI add_0_left append_butlast_last_id append_eq_append_conv
        append_self_conv2 assms(2) assms(3) length_greater_0_conv list.size(3) list.size(4))
  hence "butlast xs \<noteq> []"
    by (metis length_butlast less_numeral_extra(3) list.size(3) zero_less_diff)
  then show "insert_seq start (butlast xs)"
    using assms by (metis append_butlast_last_id insert_seq_rem_last)
qed

lemma insert_seq_last_ref:
  assumes "insert_seq start (xs @ [(xi, xr), (yi, yr)])"
  shows "yr = Some xi"
  using assms insert_seq.cases by fastforce

lemma insert_seq_start_none:
  assumes "insert_ops ops"
    and "insert_seq None xs" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
  shows "\<forall>i \<in> set (map fst xs). i \<in> set (interp_ins ops)"
  using assms proof(induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  then have IH: "\<forall>i \<in> set (map fst xs). i \<in> set (interp_ins ops)"
    by (metis Nil_is_map_conv append_is_Nil_conv insert_ops_appendD insert_seq_rem_last
        le_supE list.simps(3) set_append split_list)
  then show "\<forall>i \<in> set (map fst (xs @ [x])). i \<in> set (interp_ins ops)"
  proof(cases "xs = []")
    case True
    then obtain oid where "xs @ [x] = [(oid, None)]"
      using insert_seq_hd snoc.prems(2) by fastforce
    hence "(oid, None) \<in> set ops"
      using snoc.prems(4) by auto
    then obtain as bs where "ops = as @ (oid, None) # bs"
      by (meson split_list)
    hence "ops = (as @ [(oid, None)]) @ bs"
      by (simp add: \<open>ops = as @ (oid, None) # bs\<close>)
    moreover have "oid \<in> set (interp_ins (as @ [(oid, None)]))"
      by (simp add: interp_ins_last_None)
    ultimately have "oid \<in> set (interp_ins ops)"
      using interp_ins_monotonic snoc.prems(1) by blast
    then show "\<forall>i \<in> set (map fst (xs @ [x])). i \<in> set (interp_ins ops)" 
      using \<open>xs @ [x] = [(oid, None)]\<close> by auto
  next
    case False
    then obtain rest y where snoc_y: "xs = rest @ [y]"
      using append_butlast_last_id by metis
    obtain yi yr xi xr where yx_pairs: "y = (yi, yr) \<and> x = (xi, xr)"
      by force
    then have "xr = Some yi"
      using insert_seq_last_ref snoc.prems(2) snoc_y by fastforce
    have "yi < xi"
      using insert_ops_sorted_oids snoc_y yx_pairs snoc.prems(3)
      by (metis (no_types, lifting) append_eq_append_conv2)
    have "(yi, yr) \<in> set ops" and "(xi, Some yi) \<in> set ops"
      using snoc.prems(4) snoc_y yx_pairs \<open>xr = Some yi\<close> by auto
    then obtain as bs cs where ops_split: "ops = as @ [(yi, yr)] @ bs @ [(xi, Some yi)] @ cs"
      using insert_ops_split_2 \<open>yi < xi\<close> snoc.prems(1) by blast
    hence "yi \<in> set (interp_ins (as @ [(yi, yr)] @ bs))"
    proof -
      have "yi \<in> set (interp_ins ops)"
        by (simp add: IH snoc_y yx_pairs)
      moreover have "ops = (as @ [(yi, yr)] @ bs) @ ([(xi, Some yi)] @ cs)"
        using ops_split by simp
      moreover have "yi \<in> set (map fst (as @ [(yi, yr)] @ bs))"
        by simp
      ultimately show ?thesis
        using snoc.prems(1) interp_ins_append_forward by blast
    qed
    hence "xi \<in> set (interp_ins ((as @ [(yi, yr)] @ bs) @ [(xi, Some yi)] @ cs))"
      using snoc.prems(1) interp_ins_append_memb ops_split by force
    hence "xi \<in> set (interp_ins ops)"
      by (simp add: ops_split)
    then show "\<forall>i \<in> set (map fst (xs @ [x])). i \<in> set (interp_ins ops)"
      using IH yx_pairs by auto
  qed
qed

lemma insert_seq_after_start:
  assumes "insert_ops ops"
    and "insert_seq (Some ref) xs" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
    and "ref \<in> set (interp_ins ops)"
  shows "\<forall>i \<in> set (map fst xs). list_order ops ref i"
  using assms proof(induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  have IH: "\<forall>i \<in> set (map fst xs). list_order ops ref i"
    using snoc.IH snoc.prems insert_seq_rem_last insert_ops_appendD
    by (metis Nil_is_map_conv Un_subset_iff empty_set equals0D set_append)
  moreover have "list_order ops ref (fst x)"
  proof(cases "xs = []")
    case True
    hence "snd x = Some ref"
      using insert_seq_hd snoc.prems(2) by fastforce
    moreover have "x \<in> set ops"
      using snoc.prems(4) by auto
    then obtain cs ds where x_split: "ops = cs @ x # ds"
      by (meson split_list)
    have "list_order (cs @ [(fst x, Some ref)]) ref (fst x)"
    proof -
      have "insert_ops (cs @ [(fst x, Some ref)] @ ds)"
        using x_split \<open>snd x = Some ref\<close>
        by (metis append_Cons append_self_conv2 prod.collapse snoc.prems(1))
      moreover from this obtain rr where "(ref, rr) \<in> set cs"
        using interp_ins_find_ref x_split \<open>snd x = Some ref\<close> assms(5)
        by (metis (no_types, lifting) append_Cons append_self_conv2 prod.collapse)
      hence "ref \<in> set (interp_ins cs)"
      proof -
        have "ops = cs @ ([(fst x, Some ref)] @ ds)"
          by (metis x_split \<open>snd x = Some ref\<close> append_Cons append_self_conv2 prod.collapse)
        thus "ref \<in> set (interp_ins cs)"
          using assms(5) calculation interp_ins_append_forward interp_ins_append_non_memb by blast
      qed
      ultimately show "list_order (cs @ [(fst x, Some ref)]) ref (fst x)"
        using list_order_insert_ref by (metis append.assoc insert_ops_appendD)
    qed
    moreover have "ops = (cs @ [(fst x, Some ref)]) @ ds"
      using calculation x_split
      by (metis append_eq_Cons_conv append_eq_append_conv2 append_self_conv2 prod.collapse)
    ultimately show "list_order ops ref (fst x)"
      using list_order_append snoc.prems(1) by blast
  next
    case False
    then obtain rest y where snoc_y: "xs = rest @ [y]"
      using append_butlast_last_id by metis
    obtain yi yr xi xr where yx_pairs: "y = (yi, yr) \<and> x = (xi, xr)"
      by force
    then have "xr = Some yi"
      using insert_seq_last_ref snoc.prems(2) snoc_y by fastforce
    have "yi < xi"
      using insert_ops_sorted_oids snoc_y yx_pairs snoc.prems(3)
      by (metis (no_types, lifting) append_eq_append_conv2)
    have "(yi, yr) \<in> set ops" and "(xi, Some yi) \<in> set ops"
      using snoc.prems(4) snoc_y yx_pairs \<open>xr = Some yi\<close> by auto
    then obtain as bs cs where ops_split: "ops = as @ [(yi, yr)] @ bs @ [(xi, Some yi)] @ cs"
      using insert_ops_split_2 \<open>yi < xi\<close> snoc.prems(1) by blast
    have "list_order ops ref yi"
      by (simp add: IH snoc_y yx_pairs)
    moreover have "list_order (as @ [(yi, yr)] @ bs @ [(xi, Some yi)]) yi xi"
    proof -
      have "insert_ops ((as @ [(yi, yr)] @ bs @ [(xi, Some yi)]) @ cs)"
        using ops_split snoc.prems(1) by auto
      hence "insert_ops ((as @ [(yi, yr)] @ bs) @ [(xi, Some yi)])"
        using insert_ops_appendD by fastforce
      moreover have "yi \<in> set (interp_ins ops)"
        using \<open>list_order ops ref yi\<close> list_order_memb2 by auto
      hence "yi \<in> set (interp_ins (as @ [(yi, yr)] @ bs))"
        using interp_ins_append_non_memb ops_split snoc.prems(1) by force
      ultimately show ?thesis
        using list_order_insert_ref by force
    qed
    hence "list_order ops yi xi"
      by (metis append_assoc list_order_append ops_split snoc.prems(1))
    ultimately show "list_order ops ref (fst x)"
      using list_order_trans snoc.prems(1) yx_pairs by auto
  qed
  ultimately show "\<forall>i \<in> set (map fst (xs @ [x])). list_order ops ref i"
    by auto
qed

lemma insert_seq_no_start:
  assumes "insert_ops ops"
    and "insert_seq (Some ref) xs" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
    and "ref \<notin> set (interp_ins ops)"
  shows "\<forall>i \<in> set (map fst xs). i \<notin> set (interp_ins ops)"
  using assms proof(induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  have IH: "\<forall>i \<in> set (map fst xs). i \<notin> set (interp_ins ops)"
    using snoc.IH snoc.prems insert_seq_rem_last insert_ops_appendD
    by (metis append_is_Nil_conv le_sup_iff list.map_disc_iff set_append split_list_first)
  obtain as bs where "ops = as @ x # bs"
    using snoc.prems(4) by (metis split_list last_in_set snoc_eq_iff_butlast subset_code(1))
  have "fst x \<notin> set (interp_ins ops)"
  proof(cases "xs = []")
    case True
    then obtain xi where "x = (xi, Some ref)"
      using insert_seq_hd snoc.prems(2) by force
    moreover have "ref \<notin> set (interp_ins as)"
      using interp_ins_monotonic snoc.prems(1) snoc.prems(5) \<open>ops = as @ x # bs\<close> by blast
    ultimately have "xi \<notin> set (interp_ins (as @ [x] @ bs))"
      using snoc.prems(1) by (simp add: interp_ins_ref_nonex \<open>ops = as @ x # bs\<close>)
    then show "fst x \<notin> set (interp_ins ops)"
      by (simp add: \<open>ops = as @ x # bs\<close> \<open>x = (xi, Some ref)\<close>)
  next
    case xs_nonempty: False
    then obtain y where "xs = (butlast xs) @ [y]"
      by (metis append_butlast_last_id)
    moreover from this obtain yi yr xi xr where "y = (yi, yr) \<and> x = (xi, xr)"
      by fastforce
    moreover from this have "xr = Some yi"
      using insert_seq.cases snoc.prems(2) calculation by fastforce
    moreover have "yi \<notin> set (interp_ins ops)"
      using IH calculation 
      by (metis Nil_is_map_conv fst_conv last_in_set last_map snoc_eq_iff_butlast)
    hence "yi \<notin> set (interp_ins as)"
      using \<open>ops = as @ x # bs\<close> interp_ins_monotonic snoc.prems(1) by blast
    ultimately have "xi \<notin> set (interp_ins (as @ [x] @ bs))"
      using interp_ins_ref_nonex snoc.prems(1) \<open>ops = as @ x # bs\<close> by fastforce
    then show "fst x \<notin> set (interp_ins ops)"
      by (simp add: \<open>ops = as @ x # bs\<close> \<open>y = (yi, yr) \<and> x = (xi, xr)\<close>)
  qed
  then show "\<forall>i \<in> set (map fst (xs @ [x])). i \<notin> set (interp_ins ops)"
    using IH by auto
qed


subsection\<open>The proof of no interleaving\<close>

lemma no_interleaving_ordered:
  assumes "insert_ops ops"
    and "insert_seq start xs" and "insert_ops xs"
    and "insert_seq start ys" and "insert_ops ys"
    and "set xs \<subseteq> set ops" and "set ys \<subseteq> set ops"
    and "distinct (map fst xs @ map fst ys)"
    and "fst (hd xs) < fst (hd ys)"
    and "\<And>r. start = Some r \<Longrightarrow> r \<in> set (interp_ins ops)"
  shows "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order ops y x) \<and>
         (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst xs). list_order ops r x) \<and>
                                 (\<forall>y \<in> set (map fst ys). list_order ops r y))"
  using assms proof(induction ops arbitrary: xs ys rule: List.rev_induct, simp)
  case (snoc a ops)
  then have "insert_ops ops"
    using insert_ops_rem_last by auto
  consider (a_in_xs) "a \<in> set xs" | (a_in_ys) "a \<in> set ys" | (neither) "a \<notin> set xs \<and> a \<notin> set ys"
    by blast
  then show ?case
  proof(cases)
    case a_in_xs
    then have "a \<notin> set ys"
      using snoc.prems(8) by auto
    hence "set ys \<subseteq> set ops"
      using snoc.prems(7) DiffE by auto
    from a_in_xs have "a = last xs"
      using insert_ops_subset_last snoc.prems by blast
    have IH: "(\<forall>x \<in> set (map fst (butlast xs)). \<forall>y \<in> set (map fst ys).  list_order ops y x) \<and>
              (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst (butlast xs)). list_order ops r x) \<and>
                                      (\<forall>y \<in> set (map fst          ys).  list_order ops r y))"
    proof(cases "xs = [a]")
      case True
      moreover have "\<forall>r. start = Some r \<longrightarrow> (\<forall>y \<in> set (map fst ys). list_order ops r y)"
        using insert_seq_after_start \<open>insert_ops ops\<close> \<open>set ys \<subseteq> set ops\<close> snoc.prems
        by (metis append_Nil2 calculation insert_seq_hd interp_ins_append_non_memb list.sel(1))
      ultimately show ?thesis by auto
    next
      case xs_longer: False
      from \<open>a = last xs\<close> have "set (butlast xs) \<subseteq> set ops"
        using snoc.prems by (simp add: distinct_fst subset_butlast)
      moreover have "insert_seq start (butlast xs)"
        using insert_seq_butlast insert_seq_nonempty xs_longer \<open>a = last xs\<close> snoc.prems(2) by blast
      moreover have "insert_ops (butlast xs)"
        using snoc.prems(2) snoc.prems(3) insert_ops_appendD
        by (metis append_butlast_last_id insert_seq_nonempty)
      moreover have "distinct (map fst (butlast xs) @ map fst ys)"
        using distinct_append_butlast1 snoc.prems(8) by blast
      moreover have "set ys \<subseteq> set ops"
        using \<open>a \<notin> set ys\<close> \<open>set ys \<subseteq> set ops\<close> by blast
      moreover have "hd (butlast xs) = hd xs"
        by (metis append_butlast_last_id calculation(2) hd_append2 insert_seq_nonempty snoc.prems(2))
      hence "fst (hd (butlast xs)) < fst (hd ys)"
        by (simp add: snoc.prems(9))
      moreover have "\<And>r. start = Some r \<Longrightarrow> r \<in> set (interp_ins ops)"
      proof -
        fix r
        assume "start = Some r"
        then obtain xid where "hd xs = (xid, Some r)"
          using insert_seq_hd snoc.prems(2) by auto
        hence "r < xid"
          by (metis hd_in_set insert_ops_memb_ref_older insert_seq_nonempty snoc.prems(2) snoc.prems(3))
        moreover have "xid < fst a"
        proof -
          have "xs = (butlast xs) @ [a]"
            using snoc.prems(2) insert_seq_nonempty \<open>a = last xs\<close> by fastforce
          moreover have "(xid, Some r) \<in> set (butlast xs)"
            using \<open>hd xs = (xid, Some r)\<close> insert_seq_nonempty list.set_sel(1) snoc.prems(2)
            by (metis \<open>hd (butlast xs) = hd xs\<close> \<open>insert_seq start (butlast xs)\<close>)
          hence "xid \<in> set (map fst (butlast xs))"
            by (metis in_set_zipE zip_map_fst_snd)
          ultimately show ?thesis
            using snoc.prems(3) last_op_greatest by (metis prod.collapse)
        qed
        ultimately have "r \<noteq> fst a"
          using dual_order.asym by blast
        thus "r \<in> set (interp_ins ops)"
          using snoc.prems(1) snoc.prems(10) interp_ins_maybe_grow2 \<open>start = Some r\<close> by blast
      qed
      ultimately show ?thesis
        using \<open>insert_ops ops\<close> snoc.IH snoc.prems(4) snoc.prems(5) by blast
    qed
    moreover have x_exists: "\<forall>x \<in> set (map fst (butlast xs)). x \<in> set (interp_ins ops)"
    proof(cases start)
      case None
      moreover have "set (butlast xs) \<subseteq> set ops"
        using \<open>a = last xs\<close> distinct_map snoc.prems(6) snoc.prems(8) subset_butlast by fastforce
      ultimately show ?thesis
        using insert_seq_start_none \<open>insert_ops ops\<close> snoc.prems 
        by (metis append_butlast_last_id butlast.simps(2) empty_iff empty_set
            insert_ops_rem_last insert_seq_butlast insert_seq_nonempty list.simps(8))
    next
      case (Some a)
      then show ?thesis
        using IH list_order_memb2 by blast
    qed
    moreover have "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y (fst a)"
    proof(cases "xs = [a]")
      case xs_a: True
      have "ys \<noteq> [] \<Longrightarrow> False"
      proof -
        assume "ys \<noteq> []"
        then obtain yi where yi_def: "ys = (yi, start) # (tl ys)"
          by (metis hd_Cons_tl insert_seq_hd snoc.prems(4))
        hence "(yi, start) \<in> set ops"
          by (metis \<open>set ys \<subseteq> set ops\<close> list.set_intros(1) subsetCE)
        hence "yi \<in> set (map fst ops)"
          by force
        hence "yi < fst a"
          using snoc.prems(1) last_op_greatest by (metis prod.collapse)
        moreover have "fst a < yi"
          by (metis yi_def xs_a fst_conv list.sel(1) snoc.prems(9))
        ultimately show False
          using less_not_sym by blast
      qed
      then show "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y (fst a)"
        using insert_seq_nonempty snoc.prems(4) by blast
    next
      case xs_longer: False
      hence butlast_split: "butlast xs = (butlast (butlast xs)) @ [last (butlast xs)]"
        using \<open>a = last xs\<close> insert_seq_butlast insert_seq_nonempty snoc.prems(2) by fastforce
      hence ref_exists: "fst (last (butlast xs)) \<in> set (interp_ins ops)"
        using x_exists by (metis last_in_set last_map map_is_Nil_conv snoc_eq_iff_butlast)
      moreover from butlast_split have "xs = (butlast (butlast xs)) @ [last (butlast xs), a]"
        by (metis \<open>a = last xs\<close> append.assoc append_butlast_last_id butlast.simps(2)
            insert_seq_nonempty last_ConsL last_ConsR list.simps(3) snoc.prems(2))
      hence "snd a = Some (fst (last (butlast xs)))"
        using snoc.prems(2) insert_seq_last_ref by (metis prod.collapse)
      hence "list_order (ops @ [a]) (fst (last (butlast xs))) (fst a)"
        using list_order_insert_ref ref_exists snoc.prems(1) by (metis prod.collapse)
      moreover have "\<forall>y \<in> set (map fst ys). list_order ops y (fst (last (butlast xs)))"
        by (metis IH butlast_split last_in_set last_map map_is_Nil_conv snoc_eq_iff_butlast)
      hence "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y (fst (last (butlast xs)))"
        using list_order_append snoc.prems(1) by blast
      ultimately show "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y (fst a)"
        using list_order_trans snoc.prems(1) by blast
    qed
    moreover have map_fst_xs: "map fst xs = map fst (butlast xs) @ map fst [last xs]"
      by (metis append_butlast_last_id insert_seq_nonempty map_append snoc.prems(2))
    hence "set (map fst xs) = set (map fst (butlast xs)) \<union> {fst a}"
      by (simp add: \<open>a = last xs\<close>)
    moreover have "\<forall>r. start = Some r \<longrightarrow> list_order (ops @ [a]) r (fst a)"
      using snoc.prems by (cases start, auto simp add: insert_seq_after_start \<open>a = last xs\<close> map_fst_xs)
    ultimately show "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y x) \<and>
          (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst xs). list_order (ops @ [a]) r x) \<and>
                                  (\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) r y))"
      using snoc.prems(1) by (simp add: list_order_append)
  next
    case a_in_ys
    then have "a \<notin> set xs"
      using snoc.prems(8) by auto
    hence "set xs \<subseteq> set ops"
      using snoc.prems(6) DiffE by auto
    from a_in_ys have "a = last ys"
      using insert_ops_subset_last snoc.prems by blast
    have IH: "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst (butlast ys)).  list_order ops y x) \<and>
              (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst          xs).  list_order ops r x) \<and>
                                      (\<forall>y \<in> set (map fst (butlast ys)). list_order ops r y))"
    proof(cases "ys = [a]")
      case True
      moreover have "\<forall>r. start = Some r \<longrightarrow> (\<forall>y \<in> set (map fst xs). list_order ops r y)"
        using insert_seq_after_start \<open>insert_ops ops\<close> \<open>set xs \<subseteq> set ops\<close> snoc.prems
        by (metis append_Nil2 calculation insert_seq_hd interp_ins_append_non_memb list.sel(1))
      ultimately show ?thesis by auto
    next
      case ys_longer: False
      from \<open>a = last ys\<close> have "set (butlast ys) \<subseteq> set ops"
        using snoc.prems by (simp add: distinct_fst subset_butlast)
      moreover have "insert_seq start (butlast ys)"
        using insert_seq_butlast insert_seq_nonempty ys_longer \<open>a = last ys\<close> snoc.prems(4) by blast
      moreover have "insert_ops (butlast ys)"
        using snoc.prems(4) snoc.prems(5) insert_ops_appendD
        by (metis append_butlast_last_id insert_seq_nonempty)
      moreover have "distinct (map fst xs @ map fst (butlast ys))"
        using distinct_append_butlast2 snoc.prems(8) by blast
      moreover have "set xs \<subseteq> set ops"
        using \<open>a \<notin> set xs\<close> \<open>set xs \<subseteq> set ops\<close> by blast
      moreover have "hd (butlast ys) = hd ys"
        by (metis append_butlast_last_id calculation(2) hd_append2 insert_seq_nonempty snoc.prems(4))
      hence "fst (hd xs) < fst (hd (butlast ys))"
        by (simp add: snoc.prems(9))
      moreover have "\<And>r. start = Some r \<Longrightarrow> r \<in> set (interp_ins ops)"
      proof -
        fix r
        assume "start = Some r"
        then obtain yid where "hd ys = (yid, Some r)"
          using insert_seq_hd snoc.prems(4) by auto
        hence "r < yid"
          by (metis hd_in_set insert_ops_memb_ref_older insert_seq_nonempty snoc.prems(4) snoc.prems(5))
        moreover have "yid < fst a"
        proof -
          have "ys = (butlast ys) @ [a]"
            using snoc.prems(4) insert_seq_nonempty \<open>a = last ys\<close> by fastforce
          moreover have "(yid, Some r) \<in> set (butlast ys)"
            using \<open>hd ys = (yid, Some r)\<close> insert_seq_nonempty list.set_sel(1) snoc.prems(2)
            by (metis \<open>hd (butlast ys) = hd ys\<close> \<open>insert_seq start (butlast ys)\<close>)
          hence "yid \<in> set (map fst (butlast ys))"
            by (metis in_set_zipE zip_map_fst_snd)
          ultimately show ?thesis
            using snoc.prems(5) last_op_greatest by (metis prod.collapse)
        qed
        ultimately have "r \<noteq> fst a"
          using dual_order.asym by blast
        thus "r \<in> set (interp_ins ops)"
          using snoc.prems(1) snoc.prems(10) interp_ins_maybe_grow2 \<open>start = Some r\<close> by blast
      qed
      ultimately show ?thesis
        using \<open>insert_ops ops\<close> snoc.IH snoc.prems(2) snoc.prems(3) by blast
    qed
    moreover have "\<forall>x \<in> set (map fst xs). list_order (ops @ [a]) (fst a) x"
    proof(cases "ys = [a]")
      case ys_a: True
      then show "\<forall>x \<in> set (map fst xs). list_order (ops @ [a]) (fst a) x"
      proof(cases start)
        case None
        then show ?thesis
          using insert_seq_start_none list_order_insert_none snoc.prems
          by (metis \<open>insert_ops ops\<close> \<open>set xs \<subseteq> set ops\<close> fst_conv insert_seq_hd list.sel(1) ys_a)
      next
        case (Some r)
        moreover from this have "\<forall>x \<in> set (map fst xs). list_order ops r x"
          using IH by blast
        ultimately show ?thesis
          using snoc.prems(1) snoc.prems(4) list_order_insert_between
          by (metis fst_conv insert_seq_hd list.sel(1) ys_a)
      qed
    next
      case ys_longer: False
      hence butlast_split: "butlast ys = (butlast (butlast ys)) @ [last (butlast ys)]"
        using \<open>a = last ys\<close> insert_seq_butlast insert_seq_nonempty snoc.prems(4) by fastforce
      moreover from this have "ys = (butlast (butlast ys)) @ [last (butlast ys), a]"
        by (metis \<open>a = last ys\<close> append.assoc append_butlast_last_id butlast.simps(2)
            insert_seq_nonempty last_ConsL last_ConsR list.simps(3) snoc.prems(4))
      hence "snd a = Some (fst (last (butlast ys)))"
        using snoc.prems(4) insert_seq_last_ref by (metis prod.collapse)
      moreover have "\<forall>x \<in> set (map fst xs). list_order ops (fst (last (butlast ys))) x"
        by (metis IH butlast_split last_in_set last_map map_is_Nil_conv snoc_eq_iff_butlast)
      ultimately show "\<forall>x \<in> set (map fst xs). list_order (ops @ [a]) (fst a) x"
        using list_order_insert_between snoc.prems(1) by (metis prod.collapse)
    qed
    moreover have map_fst_xs: "map fst ys = map fst (butlast ys) @ map fst [last ys]"
      by (metis append_butlast_last_id insert_seq_nonempty map_append snoc.prems(4))
    hence "set (map fst ys) = set (map fst (butlast ys)) \<union> {fst a}"
      by (simp add: \<open>a = last ys\<close>)
    moreover have "\<forall>r. start = Some r \<longrightarrow> list_order (ops @ [a]) r (fst a)"
      using snoc.prems by (cases start, auto simp add: insert_seq_after_start \<open>a = last ys\<close> map_fst_xs)
    ultimately show "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y x) \<and>
          (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst xs). list_order (ops @ [a]) r x) \<and>
                                  (\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) r y))"
      using snoc.prems(1) by (simp add: list_order_append)
  next
    case neither
    hence "set xs \<subseteq> set ops" and "set ys \<subseteq> set ops"
      using snoc.prems(6) snoc.prems(7) DiffE by auto
    have "(\<forall>r. start = Some r \<longrightarrow> r \<in> set (interp_ins ops)) \<or> (xs = [] \<and> ys = [])"
    proof(cases xs)
      case Nil
      then show ?thesis using insert_seq_nonempty snoc.prems(2) by blast
    next
      case xs_nonempty: (Cons x xsa)
      have "\<And>r. start = Some r \<Longrightarrow> r \<in> set (interp_ins ops)"
      proof -
        fix r
        assume "start = Some r"
        then obtain xi where "x = (xi, Some r)"
          using insert_seq_hd xs_nonempty snoc.prems(2) by fastforce
        hence "(xi, Some r) \<in> set ops"
          using \<open>set xs \<subseteq> set ops\<close> xs_nonempty by auto
        hence "r < xi"
          using \<open>insert_ops ops\<close> insert_ops_memb_ref_older by blast
        moreover have "xi \<in> set (map fst ops)"
          using \<open>(xi, Some r) \<in> set ops\<close> by force
        hence "xi < fst a"
          using last_op_greatest snoc.prems(1) by (metis prod.collapse)
        ultimately have "fst a \<noteq> r"
          using order.asym by blast
        then show "r \<in> set (interp_ins ops)"
          using snoc.prems(1) snoc.prems(10) interp_ins_maybe_grow2 \<open>start = Some r\<close> by blast
      qed
      then show ?thesis by blast
    qed
    hence "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order ops y x) \<and>
           (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst xs). list_order ops r x) \<and>
                                   (\<forall>y \<in> set (map fst ys). list_order ops r y))"
      using snoc.prems snoc.IH \<open>set xs \<subseteq> set ops\<close> \<open>set ys \<subseteq> set ops\<close> by blast
    then show "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y x) \<and>
          (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst xs). list_order (ops @ [a]) r x) \<and>
                                  (\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) r y))"
      using snoc.prems(1) by (simp add: list_order_append)
  qed
qed

text\<open>Consider an execution that contains two distinct insertion sequences,
\isa{xs} and \isa{ys}, that both begin at the same initial position \isa{start}.
We prove that, provided the starting element exists, the two insertion sequences
are not interleaved. That is, in the final list order, either all insertions by
\isa{xs} appear before all insertions by \isa{ys}, or vice versa.\<close>

theorem no_interleaving:
  assumes "insert_ops ops"
    and "insert_seq start xs" and "insert_ops xs"
    and "insert_seq start ys" and "insert_ops ys"
    and "set xs \<subseteq> set ops" and "set ys \<subseteq> set ops"
    and "distinct (map fst xs @ map fst ys)"
    and "start = None \<or> (\<exists>r. start = Some r \<and> r \<in> set (interp_ins ops))"
  shows "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order ops x y) \<or>
         (\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order ops y x)"
proof(cases "fst (hd xs) < fst (hd ys)")
  case True
  moreover have "\<And>r. start = Some r \<Longrightarrow> r \<in> set (interp_ins ops)"
    using assms(9) by blast
  ultimately have "\<forall>x\<in>set (map fst xs). \<forall>y\<in>set (map fst ys). list_order ops y x"
    using assms no_interleaving_ordered by blast
  then show ?thesis by blast
next
  case False
  hence "fst (hd ys) < fst (hd xs)"
    using assms(2) assms(4) assms(8) insert_seq_nonempty distinct_fst_append
    by (metis (no_types, lifting) hd_in_set hd_map list.map_disc_iff map_append neqE)
  moreover have "distinct (map fst ys @ map fst xs)"
    using assms(8) distinct_append_swap by blast
  moreover have "\<And>r. start = Some r \<Longrightarrow> r \<in> set (interp_ins ops)"
    using assms(9) by blast
  ultimately have "\<forall>x\<in>set (map fst ys). \<forall>y\<in>set (map fst xs). list_order ops y x"
    using assms no_interleaving_ordered by blast
  then show ?thesis by blast
qed

text\<open>For completeness, we also prove what happens if there are two insertion
sequences, \isa{xs} and \isa{ys}, but their initial position \isa{start} does
not exist. In that case, none of the insertions in \isa{xs} or \isa{ys} take
effect.\<close>

theorem missing_start_no_insertion:
  assumes "insert_ops ops"
    and "insert_seq (Some start) xs" and "insert_ops xs"
    and "insert_seq (Some start) ys" and "insert_ops ys"
    and "set xs \<subseteq> set ops" and "set ys \<subseteq> set ops"
    and "start \<notin> set (interp_ins ops)"
  shows "\<forall>x \<in> set (map fst xs) \<union> set (map fst ys). x \<notin> set (interp_ins ops)"
  using assms insert_seq_no_start by (metis UnE)

end
