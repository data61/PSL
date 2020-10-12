(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedSet, algorithms for iterators, min, max, to_sorted_list

*)

section \<open>\isaheader{Generic Algorithms for Sets}\<close>
theory SetGA
imports "../spec/SetSpec" SetIteratorCollectionsGA
begin
text_raw \<open>\label{thy:SetGA}\<close>

subsection \<open>Generic Set Algorithms\<close>

locale g_set_xx_defs_loc = 
  s1: StdSetDefs ops1 + s2: StdSetDefs ops2
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('x,'s2,'more2) set_ops_scheme"
begin
  definition "g_copy s \<equiv> s1.iterate s s2.ins_dj (s2.empty ())"
  definition "g_filter P s1 \<equiv> s1.iterate s1 
    (\<lambda>x \<sigma>. if P x then s2.ins_dj x \<sigma> else \<sigma>) 
    (s2.empty ())"

  definition "g_union s1 s2 \<equiv> s1.iterate s1 s2.ins s2"
  definition "g_diff s1 s2 \<equiv> s2.iterate s2 s1.delete s1"

  definition g_union_list where
    "g_union_list l =
      foldl (\<lambda>s s'. g_union s' s) (s2.empty ()) l"

  definition "g_union_dj s1 s2 \<equiv> s1.iterate s1 s2.ins_dj s2"

  definition "g_disjoint_witness s1 s2 \<equiv>
    s1.sel s1 (\<lambda>x. s2.memb x s2)"

  definition "g_disjoint s1 s2 \<equiv>
    s1.ball s1 (\<lambda>x. \<not>s2.memb x s2)"
end

locale g_set_xx_loc = g_set_xx_defs_loc ops1 ops2 +
  s1: StdSet ops1 + s2: StdSet ops2
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('x,'s2,'more2) set_ops_scheme"
begin
  lemma g_copy_alt: 
    "g_copy s = iterate_to_set s2.empty s2.ins_dj (s1.iteratei s)"
    unfolding iterate_to_set_alt_def g_copy_def ..

  lemma g_copy_impl: "set_copy s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_copy" 
  proof -

    have LIS: 
      "set_ins_dj s2.\<alpha> s2.invar s2.ins_dj" 
      "set_empty s2.\<alpha> s2.invar s2.empty"
      by unfold_locales

    from iterate_to_set_correct[OF LIS s1.iteratei_correct]
    show ?thesis
      apply unfold_locales
      unfolding g_copy_alt
      by simp_all
  qed

  lemma g_filter_impl: "set_filter s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_filter"
  proof
    fix s P
    assume "s1.invar s"
    hence "s2.\<alpha> (g_filter P s) = {e \<in> s1.\<alpha> s. P e} \<and>
      s2.invar (g_filter P s)" (is "?G1 \<and> ?G2")
      unfolding g_filter_def
      apply (rule_tac I="\<lambda>it \<sigma>. s2.invar \<sigma> \<and> s2.\<alpha> \<sigma> = {e \<in> it. P e}" 
        in s1.iterate_rule_insert_P)
      by (auto simp add: s2.empty_correct s2.ins_dj_correct)
    thus ?G1 ?G2 by auto
  qed

  lemma g_union_alt: 
    "g_union s1 s2 = iterate_add_to_set s2 s2.ins (s1.iteratei s1)"
    unfolding iterate_add_to_set_def g_union_def ..

  lemma g_diff_alt:
    "g_diff s1 s2 = iterate_diff_set s1 s1.delete (s2.iteratei s2)"
    unfolding g_diff_def iterate_diff_set_def ..

  lemma g_union_impl:
    "set_union s1.\<alpha> s1.invar s2.\<alpha> s2.invar s2.\<alpha> s2.invar g_union"
  proof -
    have LIS: "set_ins s2.\<alpha> s2.invar s2.ins" by unfold_locales
    from iterate_add_to_set_correct[OF LIS _ s1.iteratei_correct]
    show ?thesis
      apply unfold_locales
      unfolding g_union_alt
      by simp_all
  qed

  lemma g_diff_impl:
    "set_diff s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_diff"
  proof -
    have LIS: "set_delete s1.\<alpha> s1.invar s1.delete" by unfold_locales
    from iterate_diff_correct[OF LIS _ s2.iteratei_correct]
    show ?thesis
      apply unfold_locales
      unfolding g_diff_alt
      by simp_all
  qed

  lemma g_union_list_impl:
    shows "set_union_list s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_union_list"
  proof
    fix l
    note correct = s2.empty_correct set_union.union_correct[OF g_union_impl]

    assume "\<forall>s1\<in>set l. s1.invar s1"
    hence aux: "\<And>s. s2.invar s \<Longrightarrow>
           s2.\<alpha> (foldl (\<lambda>s s'. g_union s' s) s l) 
           = \<Union>{s1.\<alpha> s1 |s1. s1 \<in> set l} \<union> s2.\<alpha> s \<and>
           s2.invar (foldl (\<lambda>s s'. g_union s' s) s l)"
      by (induct l) (auto simp add: correct)

    from aux [of "s2.empty ()"]
    show "s2.\<alpha> (g_union_list l) = \<Union>{s1.\<alpha> s1 |s1. s1 \<in> set l}"
         "s2.invar (g_union_list l)"
      unfolding g_union_list_def
      by (simp_all add: correct)
  qed

  lemma g_union_dj_impl:
    "set_union_dj s1.\<alpha> s1.invar s2.\<alpha> s2.invar s2.\<alpha> s2.invar g_union_dj"
  proof
    fix s1 s2
    assume I: 
      "s1.invar s1" 
      "s2.invar s2"
    assume DJ: "s1.\<alpha> s1 \<inter> s2.\<alpha> s2 = {}"

    have "s2.\<alpha> (g_union_dj s1 s2) 
      = s1.\<alpha> s1 \<union> s2.\<alpha> s2
      \<and> s2.invar (g_union_dj s1 s2)" (is "?G1 \<and> ?G2")
      unfolding g_union_dj_def

      apply (rule_tac I="\<lambda>it \<sigma>. s2.invar \<sigma> \<and> s2.\<alpha> \<sigma> = it \<union> s2.\<alpha> s2" 
        in s1.iterate_rule_insert_P)
      using DJ
      apply (simp_all add: I)
      apply (subgoal_tac "x\<notin>s2.\<alpha> \<sigma>")
      apply (simp add: s2.ins_dj_correct I)
      apply auto
      done
    thus ?G1 ?G2 by auto
  qed

  lemma g_disjoint_witness_impl: 
    "set_disjoint_witness s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_disjoint_witness"
  proof -
    show ?thesis
      apply unfold_locales
      unfolding g_disjoint_witness_def
      by (auto dest: s1.sel'_noneD s1.sel'_someD simp: s2.memb_correct)
  qed

  lemma g_disjoint_impl: 
    "set_disjoint s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_disjoint"
  proof -
    show ?thesis
      apply unfold_locales
      unfolding g_disjoint_def
      by (auto simp: s2.memb_correct s1.ball_correct)
  qed
end

sublocale g_set_xx_loc < 
  set_copy s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_copy by (rule g_copy_impl)

sublocale g_set_xx_loc < 
  set_filter s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_filter by (rule g_filter_impl)

sublocale g_set_xx_loc < 
  set_union s1.\<alpha> s1.invar s2.\<alpha> s2.invar s2.\<alpha> s2.invar g_union 
  by (rule g_union_impl)

sublocale g_set_xx_loc < 
  set_union_dj s1.\<alpha> s1.invar s2.\<alpha> s2.invar s2.\<alpha> s2.invar g_union_dj 
  by (rule g_union_dj_impl)

sublocale g_set_xx_loc < 
  set_diff s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_diff 
  by (rule g_diff_impl)

sublocale g_set_xx_loc < 
  set_disjoint_witness s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_disjoint_witness
  by (rule g_disjoint_witness_impl)

sublocale g_set_xx_loc < 
  set_disjoint s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_disjoint by (rule g_disjoint_impl)




(*sublocale StdBasicSetDefs < g_set_xx: g_set_xx_defs_loc ops ops .
sublocale StdBasicSet < g_set_xx: g_set_xx_loc ops ops
  by unfold_locales
*)

locale g_set_xxx_defs_loc =
  s1: StdSetDefs ops1 +
  s2: StdSetDefs ops2 +
  s3: StdSetDefs ops3
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('x,'s2,'more2) set_ops_scheme"
  and ops3 :: "('x,'s3,'more3) set_ops_scheme"
begin
  definition "g_inter s1 s2 \<equiv>
    s1.iterate s1 (\<lambda>x s. if s2.memb x s2 then s3.ins_dj x s else s) 
      (s3.empty ())"
end

locale g_set_xxx_loc = g_set_xxx_defs_loc ops1 ops2 ops3 +
  s1: StdSet ops1 +
  s2: StdSet ops2 +
  s3: StdSet ops3
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('x,'s2,'more2) set_ops_scheme"
  and ops3 :: "('x,'s3,'more3) set_ops_scheme"
begin
  lemma g_inter_impl: "set_inter s1.\<alpha> s1.invar s2.\<alpha> s2.invar s3.\<alpha> s3.invar
    g_inter"
  proof
    fix s1 s2
    assume I: 
      "s1.invar s1" 
      "s2.invar s2"
    have "s3.\<alpha> (g_inter s1 s2) = s1.\<alpha> s1 \<inter> s2.\<alpha> s2 \<and> s3.invar (g_inter s1 s2)"
      unfolding g_inter_def
      apply (rule_tac I="\<lambda>it \<sigma>. s3.\<alpha> \<sigma> = it \<inter> s2.\<alpha> s2 \<and> s3.invar \<sigma>" 
        in s1.iterate_rule_insert_P) 
      apply (simp_all add: I s3.empty_correct s3.ins_dj_correct s2.memb_correct)
      done
    thus "s3.\<alpha> (g_inter s1 s2) = s1.\<alpha> s1 \<inter> s2.\<alpha> s2" 
      and "s3.invar (g_inter s1 s2)" by auto
  qed
end    

sublocale g_set_xxx_loc 
  < set_inter s1.\<alpha> s1.invar s2.\<alpha> s2.invar s3.\<alpha> s3.invar g_inter
  by (rule g_inter_impl)


(*sublocale StdBasicSetDefs < g_set_xxx: g_set_xxx_defs_loc ops ops ops .
sublocale StdBasicSet < g_set_xxx: g_set_xxx_loc ops ops ops
  by unfold_locales
*)

locale g_set_xy_defs_loc = 
  s1: StdSet ops1 + s2: StdSet ops2
  for ops1 :: "('x1,'s1,'more1) set_ops_scheme"
  and ops2 :: "('x2,'s2,'more2) set_ops_scheme"
begin
  definition "g_image_filter f s \<equiv> 
    s1.iterate s 
      (\<lambda>x res. case f x of Some v \<Rightarrow> s2.ins v res | _ \<Rightarrow> res) 
      (s2.empty ())"

  definition "g_image f s \<equiv> 
    s1.iterate s (\<lambda>x res. s2.ins (f x) res) (s2.empty ())"

  definition "g_inj_image_filter f s \<equiv> 
    s1.iterate s 
      (\<lambda>x res. case f x of Some v \<Rightarrow> s2.ins_dj v res | _ \<Rightarrow> res) 
      (s2.empty ())"

  definition "g_inj_image f s \<equiv> 
    s1.iterate s (\<lambda>x res. s2.ins_dj (f x) res) (s2.empty ())"

end

locale g_set_xy_loc = g_set_xy_defs_loc ops1 ops2 +
  s1: StdSet ops1 + s2: StdSet ops2
  for ops1 :: "('x1,'s1,'more1) set_ops_scheme"
  and ops2 :: "('x2,'s2,'more2) set_ops_scheme"
begin
  lemma g_image_filter_impl: 
    "set_image_filter s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_image_filter"
  proof
    fix f s
    assume I: "s1.invar s"
    have A: "g_image_filter f s == 
         iterate_to_set s2.empty s2.ins 
           (set_iterator_image_filter f (s1.iteratei s))"
      unfolding g_image_filter_def 
        iterate_to_set_alt_def set_iterator_image_filter_def
      by simp
    
    have ins: "set_ins s2.\<alpha> s2.invar s2.ins"
      and emp: "set_empty s2.\<alpha> s2.invar s2.empty" by unfold_locales

    from iterate_image_filter_to_set_correct[OF ins emp s1.iteratei_correct]
    show "s2.\<alpha> (g_image_filter f s) =
          {b. \<exists>a\<in>s1.\<alpha> s. f a = Some b}"
         "s2.invar (g_image_filter f s)"
      unfolding A using I by auto
  qed

  lemma g_image_alt: "g_image f s = g_image_filter (Some o f) s"
    unfolding g_image_def g_image_filter_def
    by auto

  lemma g_image_impl: "set_image s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_image" 
  proof -
    interpret set_image_filter s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_image_filter 
      by (rule g_image_filter_impl)

    show ?thesis
      apply unfold_locales
      unfolding g_image_alt
      by (auto simp add: image_filter_correct)
  qed

  lemma g_inj_image_filter_impl: 
    "set_inj_image_filter s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_inj_image_filter"
  proof
    fix f::"'x1 \<rightharpoonup> 'x2" and s
    assume I: "s1.invar s" and INJ: "inj_on f (s1.\<alpha> s \<inter> dom f)"
    have A: "g_inj_image_filter f s == 
         iterate_to_set s2.empty s2.ins_dj 
           (set_iterator_image_filter f (s1.iteratei s))"
      unfolding g_inj_image_filter_def 
        iterate_to_set_alt_def set_iterator_image_filter_def
      by simp
    
    have ins_dj: "set_ins_dj s2.\<alpha> s2.invar s2.ins_dj"
      and emp: "set_empty s2.\<alpha> s2.invar s2.empty" by unfold_locales


    from set_iterator_image_filter_correct[OF s1.iteratei_correct[OF I] INJ]
    have iti_s1_filter: "set_iterator 
      (set_iterator_image_filter f (s1.iteratei s))
      {y. \<exists>x. x \<in> s1.\<alpha> s \<and> f x = Some y}"
      by simp

    from iterate_to_set_correct[OF ins_dj emp, OF iti_s1_filter]
    show "s2.\<alpha> (g_inj_image_filter f s) =
          {b. \<exists>a\<in>s1.\<alpha> s. f a = Some b}"
         "s2.invar (g_inj_image_filter f s)"
      unfolding A by auto
  qed


  lemma g_inj_image_alt: "g_inj_image f s = g_inj_image_filter (Some o f) s"
    unfolding g_inj_image_def g_inj_image_filter_def
    by auto

  lemma g_inj_image_impl: 
    "set_inj_image s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_inj_image" 
  proof -
    interpret set_inj_image_filter 
      s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_inj_image_filter 
      by (rule g_inj_image_filter_impl)

    have AUX: "\<And>S f. inj_on f S \<Longrightarrow> inj_on (Some \<circ> f) (S \<inter> dom (Some \<circ> f))"
      by (auto intro!: inj_onI dest: inj_onD)
      
    show ?thesis
      apply unfold_locales
      unfolding g_inj_image_alt
      by (auto simp add: inj_image_filter_correct AUX)

  qed

end

sublocale g_set_xy_loc < set_image_filter s1.\<alpha> s1.invar s2.\<alpha> s2.invar 
  g_image_filter by (rule g_image_filter_impl)

sublocale g_set_xy_loc < set_image s1.\<alpha> s1.invar s2.\<alpha> s2.invar 
  g_image by (rule g_image_impl)

sublocale g_set_xy_loc < set_inj_image s1.\<alpha> s1.invar s2.\<alpha> s2.invar 
  g_inj_image by (rule g_inj_image_impl)

locale g_set_xyy_defs_loc = 
  s0: StdSetDefs ops0 + 
  g_set_xx_defs_loc ops1 ops2
  for ops0 :: "('x0,'s0,'more0) set_ops_scheme"
  and ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('x,'s2,'more2) set_ops_scheme"
begin
  definition g_Union_image
    :: "('x0 \<Rightarrow> 's1) \<Rightarrow> 's0 \<Rightarrow> 's2"
    where "g_Union_image f S 
    == s0.iterate S (\<lambda>x res. g_union (f x) res) (s2.empty ())"
end

locale g_set_xyy_loc = g_set_xyy_defs_loc ops0 ops1 ops2 +
  s0: StdSet ops0 + 
  g_set_xx_loc ops1 ops2
  for ops0 :: "('x0,'s0,'more0) set_ops_scheme"
  and ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('x,'s2,'more2) set_ops_scheme"
begin

  lemma g_Union_image_impl:
    "set_Union_image s0.\<alpha> s0.invar s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_Union_image"
  proof -
    {
      fix s f
      have "\<lbrakk>s0.invar s; \<And>x. x \<in> s0.\<alpha> s \<Longrightarrow> s1.invar (f x)\<rbrakk> \<Longrightarrow> 
        s2.\<alpha> (g_Union_image f s) = \<Union>(s1.\<alpha> ` f ` s0.\<alpha> s) 
        \<and> s2.invar (g_Union_image f s)"
        apply (unfold g_Union_image_def)
        apply (rule_tac I="\<lambda>it res. s2.invar res 
          \<and> s2.\<alpha> res = \<Union>(s1.\<alpha>`f`(s0.\<alpha> s - it))" in s0.iterate_rule_P)
        apply (fastforce simp add: s2.empty_correct union_correct)+
        done
    }
    thus ?thesis
      apply unfold_locales
      apply auto
      done
  qed
end

sublocale g_set_xyy_loc < 
  set_Union_image s0.\<alpha> s0.invar s1.\<alpha> s1.invar s2.\<alpha> s2.invar g_Union_image
  by (rule g_Union_image_impl)

subsection \<open>Default Set Operations\<close>

record ('x,'s) set_basic_ops = 
  bset_op_\<alpha> :: "'s \<Rightarrow> 'x set"
  bset_op_invar :: "'s \<Rightarrow> bool"
  bset_op_empty :: "unit \<Rightarrow> 's"
  bset_op_memb :: "'x \<Rightarrow> 's \<Rightarrow> bool"
  bset_op_ins :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  bset_op_ins_dj :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  bset_op_delete :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  bset_op_list_it :: "('x,'s) set_list_it"

record ('x,'s) oset_basic_ops = "('x::linorder,'s) set_basic_ops" +
  bset_op_ordered_list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator"
  bset_op_rev_list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator"

locale StdBasicSetDefs = 
  poly_set_iteratei_defs "bset_op_list_it ops"
  for ops :: "('x,'s,'more) set_basic_ops_scheme"
begin
  abbreviation \<alpha> where "\<alpha> == bset_op_\<alpha> ops"
  abbreviation invar where "invar == bset_op_invar ops"
  abbreviation empty where "empty == bset_op_empty ops"
  abbreviation memb where "memb == bset_op_memb ops"
  abbreviation ins where "ins == bset_op_ins ops"
  abbreviation ins_dj where "ins_dj == bset_op_ins_dj ops"
  abbreviation delete where "delete == bset_op_delete ops"
  abbreviation list_it where "list_it \<equiv> bset_op_list_it ops"
end

locale StdBasicOSetDefs = StdBasicSetDefs ops
  + poly_set_iterateoi_defs "bset_op_ordered_list_it ops"
  + poly_set_rev_iterateoi_defs "bset_op_rev_list_it ops"
  for ops :: "('x::linorder,'s,'more) oset_basic_ops_scheme"
begin
  abbreviation "ordered_list_it \<equiv> bset_op_ordered_list_it ops"
  abbreviation "rev_list_it \<equiv> bset_op_rev_list_it ops"
end

locale StdBasicSet = StdBasicSetDefs ops +
  set \<alpha> invar +
  set_empty \<alpha> invar empty + 
  set_memb \<alpha> invar memb + 
  set_ins \<alpha> invar ins + 
  set_ins_dj \<alpha> invar ins_dj +
  set_delete \<alpha> invar delete + 
  poly_set_iteratei \<alpha> invar list_it
  for ops :: "('x,'s,'more) set_basic_ops_scheme"
begin

  lemmas correct[simp] = 
    empty_correct
    memb_correct
    ins_correct
    ins_dj_correct
    delete_correct

end

locale StdBasicOSet =
  StdBasicOSetDefs ops +
  StdBasicSet ops +
  poly_set_iterateoi \<alpha> invar ordered_list_it +
  poly_set_rev_iterateoi \<alpha> invar rev_list_it
  for ops :: "('x::linorder,'s,'more) oset_basic_ops_scheme"
begin
end

context StdBasicSetDefs
begin
  definition "g_sng x \<equiv> ins x (empty ())"
  definition "g_isEmpty s \<equiv> iteratei s (\<lambda>c. c) (\<lambda>_ _. False) True"
  definition "g_sel' s P \<equiv> iteratei s ((=) None) 
    (\<lambda>x _. if P x then Some x else None) None"

  definition "g_ball s P \<equiv> iteratei s (\<lambda>c. c) (\<lambda>x \<sigma>. P x) True"
  definition "g_bex s P \<equiv> iteratei s (\<lambda>c. \<not>c) (\<lambda>x \<sigma>. P x) False"
  definition "g_size s \<equiv> iteratei s (\<lambda>_. True) (\<lambda>x n . Suc n) 0"
  definition "g_size_abort m s \<equiv> iteratei s (\<lambda>\<sigma>. \<sigma> < m) (\<lambda>x. Suc) 0"
  definition "g_isSng s \<equiv> (iteratei s (\<lambda>\<sigma>. \<sigma> < 2) (\<lambda>x. Suc) 0 = 1)"

  definition "g_union s1 s2 \<equiv> iterate s1 ins s2"
  definition "g_diff s1 s2 \<equiv> iterate s2 delete s1"

  definition "g_subset s1 s2 \<equiv> g_ball s1 (\<lambda>x. memb x s2)"

  definition "g_equal s1 s2 \<equiv> g_subset s1 s2 \<and> g_subset s2 s1"

  definition "g_to_list s \<equiv> iterate s (#) []"

  fun g_from_list_aux where
    "g_from_list_aux accs [] = accs" |
    "g_from_list_aux accs (x#l) = g_from_list_aux (ins x accs) l"
    \<comment> \<open>Tail recursive version\<close>

  definition "g_from_list l == g_from_list_aux (empty ()) l"

  definition "g_inter s1 s2 \<equiv>
    iterate s1 (\<lambda>x s. if memb x s2 then ins_dj x s else s) 
      (empty ())"

  definition "g_union_dj s1 s2 \<equiv> iterate s1 ins_dj s2"
  definition "g_filter P s \<equiv> iterate s 
    (\<lambda>x \<sigma>. if P x then ins_dj x \<sigma> else \<sigma>) 
    (empty ())"

  definition "g_disjoint_witness s1 s2 \<equiv> g_sel' s1 (\<lambda>x. memb x s2)"
  definition "g_disjoint s1 s2 \<equiv> g_ball s1 (\<lambda>x. \<not>memb x s2)"

  definition dflt_ops
    where [icf_rec_def]: "dflt_ops \<equiv> \<lparr>
      set_op_\<alpha> = \<alpha>, 
      set_op_invar = invar, 
      set_op_empty = empty, 
      set_op_memb = memb, 
      set_op_ins = ins, 
      set_op_ins_dj = ins_dj, 
      set_op_delete = delete, 
      set_op_list_it = list_it, 
      set_op_sng = g_sng ,
      set_op_isEmpty = g_isEmpty ,
      set_op_isSng = g_isSng ,
      set_op_ball = g_ball ,
      set_op_bex = g_bex ,
      set_op_size = g_size ,
      set_op_size_abort = g_size_abort ,
      set_op_union = g_union ,
      set_op_union_dj = g_union_dj ,
      set_op_diff = g_diff ,
      set_op_filter = g_filter ,
      set_op_inter = g_inter ,
      set_op_subset = g_subset ,
      set_op_equal = g_equal ,
      set_op_disjoint = g_disjoint ,
      set_op_disjoint_witness = g_disjoint_witness ,
      set_op_sel = g_sel' ,
      set_op_to_list = g_to_list ,
      set_op_from_list = g_from_list
    \<rparr>"

  local_setup \<open>Locale_Code.lc_decl_del @{term dflt_ops}\<close>
end

context StdBasicSet
begin
  lemma g_sng_impl: "set_sng \<alpha> invar g_sng"
    apply unfold_locales 
    unfolding g_sng_def
    apply (auto simp: ins_correct empty_correct)
    done

  lemma g_ins_dj_impl: "set_ins_dj \<alpha> invar ins"
    by unfold_locales (auto simp: ins_correct)

  lemma g_isEmpty_impl: "set_isEmpty \<alpha> invar g_isEmpty"
  proof 
    fix s assume I: "invar s"
    have A: "g_isEmpty s = iterate_is_empty (iteratei s)"
      unfolding g_isEmpty_def iterate_is_empty_def ..
    from iterate_is_empty_correct[OF iteratei_correct[OF I]]
    show "g_isEmpty s \<longleftrightarrow> \<alpha> s = {}" unfolding A .
  qed

  lemma g_sel'_impl: "set_sel' \<alpha> invar g_sel'"
  proof -
    have A: "\<And>s P. g_sel' s P = iterate_sel_no_map (iteratei s) P"
      unfolding g_sel'_def iterate_sel_no_map_alt_def 
      apply (rule arg_cong[where f="iteratei", THEN cong, THEN cong, THEN cong])
      by auto

    show ?thesis
      unfolding set_sel'_def A
      using iterate_sel_no_map_correct[OF iteratei_correct]
      apply (simp add: Bex_def Ball_def)
      apply (metis option.exhaust)
      done
  qed
   
  lemma g_ball_alt: "g_ball s P = iterate_ball (iteratei s) P"
    unfolding g_ball_def iterate_ball_def by (simp add: id_def)
  lemma g_bex_alt: "g_bex s P = iterate_bex (iteratei s) P"
    unfolding g_bex_def iterate_bex_def ..

  lemma g_ball_impl: "set_ball \<alpha> invar g_ball"
    apply unfold_locales
    unfolding g_ball_alt
    apply (rule iterate_ball_correct)
    by (rule iteratei_correct)

  lemma g_bex_impl: "set_bex \<alpha> invar g_bex"
    apply unfold_locales
    unfolding g_bex_alt
    apply (rule iterate_bex_correct)
    by (rule iteratei_correct)

  lemma g_size_alt: "g_size s = iterate_size (iteratei s)"
    unfolding g_size_def iterate_size_def ..
  lemma g_size_abort_alt: "g_size_abort m s = iterate_size_abort (iteratei s) m"
    unfolding g_size_abort_def iterate_size_abort_def ..

  lemma g_size_impl: "set_size \<alpha> invar g_size"
    apply unfold_locales
    unfolding g_size_alt
    apply (rule conjunct1[OF iterate_size_correct])
    by (rule iteratei_correct)

  lemma g_size_abort_impl: "set_size_abort \<alpha> invar g_size_abort"
    apply unfold_locales
    unfolding g_size_abort_alt
    apply (rule conjunct1[OF iterate_size_abort_correct])
    by (rule iteratei_correct)

  lemma g_isSng_alt: "g_isSng s = iterate_is_sng (iteratei s)"
    unfolding g_isSng_def iterate_is_sng_def iterate_size_abort_def ..

  lemma g_isSng_impl: "set_isSng \<alpha> invar g_isSng"
    apply unfold_locales
    unfolding g_isSng_alt
    apply (drule iterate_is_sng_correct[OF iteratei_correct])
    apply (simp add: card_Suc_eq)
    done

  lemma g_union_impl: "set_union \<alpha> invar \<alpha> invar \<alpha> invar g_union"
    unfolding g_union_def[abs_def]
    apply unfold_locales
    apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = it \<union> \<alpha> s2" 
      in iterate_rule_insert_P, simp_all)+
    done

  lemma g_diff_impl: "set_diff \<alpha> invar \<alpha> invar g_diff"
    unfolding g_diff_def[abs_def]
    apply (unfold_locales)
    apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = \<alpha> s1 - it" 
      in iterate_rule_insert_P, auto)+
    done

  lemma g_subset_impl: "set_subset \<alpha> invar \<alpha> invar g_subset"
  proof -
    interpret set_ball \<alpha> invar g_ball by (rule g_ball_impl)

    show ?thesis 
      apply unfold_locales
      unfolding g_subset_def
      by (auto simp add: ball_correct memb_correct)
  qed

  lemma g_equal_impl: "set_equal \<alpha> invar \<alpha> invar g_equal"
  proof -
    interpret set_subset \<alpha> invar \<alpha> invar g_subset by (rule g_subset_impl)

    show ?thesis 
      apply unfold_locales
      unfolding g_equal_def
      by (auto simp add: subset_correct)
  qed

  lemma g_to_list_impl: "set_to_list \<alpha> invar g_to_list"
  proof 
    fix s 
    assume I: "invar s"
    have A: "g_to_list s = iterate_to_list (iteratei s)"
      unfolding g_to_list_def iterate_to_list_def ..
    
    from iterate_to_list_correct [OF iteratei_correct[OF I]]
    show "set (g_to_list s) = \<alpha> s" and "distinct (g_to_list s)"
      unfolding A
      by auto
  qed

  lemma g_from_list_impl: "list_to_set \<alpha> invar g_from_list"
  proof -
    { \<comment> \<open>Show a generalized lemma\<close>
      fix l accs
      have "invar accs \<Longrightarrow> \<alpha> (g_from_list_aux accs l) = set l \<union> \<alpha> accs 
            \<and> invar (g_from_list_aux accs l)"
        by (induct l arbitrary: accs)
           (auto simp add: ins_correct)
    } thus ?thesis
      apply (unfold_locales)
      apply (unfold g_from_list_def)
      apply (auto simp add: empty_correct)
      done
  qed

  lemma g_inter_impl: "set_inter \<alpha> invar \<alpha> invar \<alpha> invar g_inter"
    unfolding g_inter_def[abs_def]
    apply unfold_locales
    apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = it \<inter> \<alpha> s2" 
      in iterate_rule_insert_P, auto) []
    apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = it \<inter> \<alpha> s2" 
      in iterate_rule_insert_P, auto)
    done

  lemma g_union_dj_impl: "set_union_dj \<alpha> invar \<alpha> invar \<alpha> invar g_union_dj"
    unfolding g_union_dj_def[abs_def]
    apply unfold_locales
    apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = it \<union> \<alpha> s2" 
      in iterate_rule_insert_P)
    apply simp
    apply simp
    apply (subgoal_tac "x\<notin>\<alpha> \<sigma>")
    apply simp
    apply blast
    apply simp
    apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = it \<union> \<alpha> s2" 
      in iterate_rule_insert_P)
    apply simp
    apply simp
    apply (subgoal_tac "x\<notin>\<alpha> \<sigma>")
    apply simp
    apply blast
    apply simp
    done

  lemma g_filter_impl: "set_filter \<alpha> invar \<alpha> invar g_filter"
    unfolding g_filter_def[abs_def]
    apply (unfold_locales)
    apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = it \<inter> Collect P" 
      in iterate_rule_insert_P, auto)
    apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = it \<inter> Collect P" 
      in iterate_rule_insert_P, auto)
    done

  lemma g_disjoint_witness_impl: "set_disjoint_witness 
    \<alpha> invar \<alpha> invar g_disjoint_witness"
  proof -
    interpret set_sel' \<alpha> invar g_sel' by (rule g_sel'_impl)
    show ?thesis
      unfolding g_disjoint_witness_def[abs_def]
      apply unfold_locales
      by (auto dest: sel'_noneD sel'_someD simp: memb_correct)
  qed

  lemma g_disjoint_impl: "set_disjoint 
    \<alpha> invar \<alpha> invar g_disjoint"
  proof -
    interpret set_ball \<alpha> invar g_ball by (rule g_ball_impl)
    show ?thesis
      apply unfold_locales
      unfolding g_disjoint_def
      by (auto simp: memb_correct ball_correct)
  qed

end

context StdBasicSet
begin
  lemma dflt_ops_impl: "StdSet dflt_ops"
    apply (rule StdSet_intro)
    apply icf_locales
    apply (simp_all add: icf_rec_unf)
    apply (rule g_sng_impl g_isEmpty_impl g_isSng_impl g_ball_impl 
      g_bex_impl g_size_impl g_size_abort_impl g_union_impl g_union_dj_impl
      g_diff_impl g_filter_impl g_inter_impl
      g_subset_impl g_equal_impl g_disjoint_impl
      g_disjoint_witness_impl g_sel'_impl g_to_list_impl
      g_from_list_impl
    )+
    done
end

context StdBasicOSetDefs
begin
  definition "g_min s P \<equiv> iterateoi s (\<lambda>x. x = None) 
    (\<lambda>x _. if P x then Some x else None) None"
  definition "g_max s P \<equiv> rev_iterateoi s (\<lambda>x. x = None)
    (\<lambda>x _. if P x then Some x else None) None"

  definition "g_to_sorted_list s \<equiv> rev_iterateo s (#) []"
  definition "g_to_rev_list s \<equiv> iterateo s (#) []"

  definition dflt_oops :: "('x::linorder,'s) oset_ops" 
    where [icf_rec_def]:
    "dflt_oops \<equiv> set_ops.extend 
      dflt_ops
      \<lparr> 
        set_op_ordered_list_it = ordered_list_it,
        set_op_rev_list_it = rev_list_it,
        set_op_min = g_min,
        set_op_max = g_max,
        set_op_to_sorted_list = g_to_sorted_list,
        set_op_to_rev_list = g_to_rev_list
      \<rparr>"
  local_setup \<open>Locale_Code.lc_decl_del @{term dflt_oops}\<close>

end

context StdBasicOSet
begin
  lemma g_min_impl: "set_min \<alpha> invar g_min"
  proof 
    fix s P

    assume I: "invar s"
  
    from iterateoi_correct[OF I]
    have iti': "set_iterator_linord (iterateoi s) (\<alpha> s)" by simp
    note sel_correct = iterate_sel_no_map_linord_correct[OF iti', of P]

    have A: "g_min s P = iterate_sel_no_map (iterateoi s) P"
      unfolding g_min_def iterate_sel_no_map_def iterate_sel_def by simp
  
    { fix x
      assume "x\<in>\<alpha> s" "P x"
      with sel_correct 
      show "g_min s P \<in> Some ` {x\<in>\<alpha> s. P x}" and "the (g_min s P) \<le> x"
        unfolding A by auto
    }

    { assume "{x\<in>\<alpha> s. P x} = {}"        
       with sel_correct show "g_min s P = None"
        unfolding A by auto
    }
  qed

  lemma g_max_impl: "set_max \<alpha> invar g_max"
  proof 
    fix s P

    assume I: "invar s"
  
    from rev_iterateoi_correct[OF I]
    have iti': "set_iterator_rev_linord (rev_iterateoi s) (\<alpha> s)" by simp
    note sel_correct = iterate_sel_no_map_rev_linord_correct[OF iti', of P]

    have A: "g_max s P = iterate_sel_no_map (rev_iterateoi s) P"
      unfolding g_max_def iterate_sel_no_map_def iterate_sel_def by simp
  
    { fix x
      assume "x\<in>\<alpha> s" "P x"
      with sel_correct 
      show "g_max s P \<in> Some ` {x\<in>\<alpha> s. P x}" and "the (g_max s P) \<ge> x"
        unfolding A by auto
    }

    { assume "{x\<in>\<alpha> s. P x} = {}"        
       with sel_correct show "g_max s P = None"
        unfolding A by auto
    }
  qed

  lemma g_to_sorted_list_impl: "set_to_sorted_list \<alpha> invar g_to_sorted_list"
  proof 
    fix s
    assume I: "invar s"
    note iti = rev_iterateoi_correct[OF I]
    from iterate_to_list_rev_linord_correct[OF iti]
    show "sorted (g_to_sorted_list s)" 
         "distinct (g_to_sorted_list s)"
         "set (g_to_sorted_list s) = \<alpha> s" 
      unfolding g_to_sorted_list_def iterate_to_list_def by simp_all
  qed

  lemma g_to_rev_list_impl: "set_to_rev_list \<alpha> invar g_to_rev_list"
  proof 
    fix s
    assume I: "invar s"
    note iti = iterateoi_correct[OF I]
    from iterate_to_list_linord_correct[OF iti]
    show "sorted (rev (g_to_rev_list s))" 
         "distinct (g_to_rev_list s)"
         "set (g_to_rev_list s) = \<alpha> s" 
      unfolding g_to_rev_list_def iterate_to_list_def 
      by (simp_all)
  qed

  lemma dflt_oops_impl: "StdOSet dflt_oops"
  proof -
    interpret aux: StdSet dflt_ops by (rule dflt_ops_impl)

    show ?thesis
      apply (rule StdOSet_intro)
      apply icf_locales
      apply (simp_all add: icf_rec_unf)
      apply (rule g_min_impl)
      apply (rule g_max_impl)
      apply (rule g_to_sorted_list_impl)
      apply (rule g_to_rev_list_impl)
      done
  qed

end

subsection "More Generic Set Algorithms"
text \<open>
  These algorithms do not have a function specification in a locale, but
  their specification is done  ad-hoc in the correctness lemma.
\<close>

subsubsection "Image and Filter of Cartesian Product"

locale image_filter_cp_defs_loc =
  s1: StdSetDefs ops1 +
  s2: StdSetDefs ops2 +
  s3: StdSetDefs ops3
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('y,'s2,'more2) set_ops_scheme"
  and ops3 :: "('z,'s3,'more3) set_ops_scheme"
begin

  definition "image_filter_cartesian_product f s1 s2 ==
    s1.iterate s1 (\<lambda>x res.
      s2.iterate s2 (\<lambda>y res.
        case (f (x, y)) of 
          None \<Rightarrow> res
        | Some z \<Rightarrow> (s3.ins z res)
      ) res
    ) (s3.empty ())"

  lemma image_filter_cartesian_product_alt:
    "image_filter_cartesian_product f s1 s2 ==
     iterate_to_set s3.empty s3.ins (set_iterator_image_filter f (
       set_iterator_product (s1.iteratei s1) (\<lambda>_. s2.iteratei s2)))"
    unfolding image_filter_cartesian_product_def iterate_to_set_alt_def
      set_iterator_image_filter_def set_iterator_product_def 
    by simp

  definition image_filter_cp where
    "image_filter_cp f P s1 s2 \<equiv>
     image_filter_cartesian_product 
      (\<lambda>xy. if P xy then Some (f xy) else None) s1 s2"

end

locale image_filter_cp_loc = image_filter_cp_defs_loc ops1 ops2 ops3 +
  s1: StdSet ops1 +
  s2: StdSet ops2 +
  s3: StdSet ops3
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('y,'s2,'more2) set_ops_scheme"
  and ops3 :: "('z,'s3,'more3) set_ops_scheme"
begin

  lemma image_filter_cartesian_product_correct:
    fixes f :: "'x \<times> 'y \<rightharpoonup> 'z"
    assumes I[simp, intro!]: "s1.invar s1" "s2.invar s2"
    shows "s3.\<alpha> (image_filter_cartesian_product f s1 s2) 
     = { z | x y z. f (x,y) = Some z \<and> x\<in>s1.\<alpha> s1 \<and> y\<in>s2.\<alpha> s2 }" (is ?T1)
    "s3.invar (image_filter_cartesian_product f s1 s2)" (is ?T2)
  proof -
    from set_iterator_product_correct 
      [OF s1.iteratei_correct[OF I(1)] s2.iteratei_correct[OF I(2)]]
      have it_s12: "set_iterator 
        (set_iterator_product (s1.iteratei s1) (\<lambda>_. s2.iteratei s2))
        (s1.\<alpha> s1 \<times> s2.\<alpha> s2)" 
        by simp

      have LIS: 
        "set_ins s3.\<alpha> s3.invar s3.ins" 
        "set_empty s3.\<alpha> s3.invar s3.empty"
        by unfold_locales
  
      from iterate_image_filter_to_set_correct[OF LIS it_s12, of f]
      show ?T1 ?T2
        unfolding image_filter_cartesian_product_alt by auto
  qed

  lemma image_filter_cp_correct:
    assumes I: "s1.invar s1" "s2.invar s2"
    shows 
    "s3.\<alpha> (image_filter_cp f P s1 s2) 
     = { f (x, y) | x y. P (x, y) \<and> x\<in>s1.\<alpha> s1 \<and> y\<in>s2.\<alpha> s2 }" (is ?T1)
    "s3.invar (image_filter_cp f P s1 s2)" (is ?T2)
  proof -
    from image_filter_cartesian_product_correct [OF I]
    show "?T1" "?T2"
      unfolding image_filter_cp_def
      by auto
  qed

end

locale inj_image_filter_cp_defs_loc =
  s1: StdSetDefs ops1 +
  s2: StdSetDefs ops2 +
  s3: StdSetDefs ops3
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('y,'s2,'more2) set_ops_scheme"
  and ops3 :: "('z,'s3,'more3) set_ops_scheme"
begin

  definition "inj_image_filter_cartesian_product f s1 s2 ==
    s1.iterate s1 (\<lambda>x res.
      s2.iterate s2 (\<lambda>y res.
        case (f (x, y)) of 
          None \<Rightarrow> res
        | Some z \<Rightarrow> (s3.ins_dj z res)
      ) res
    ) (s3.empty ())"

  lemma inj_image_filter_cartesian_product_alt:
    "inj_image_filter_cartesian_product f s1 s2 ==
     iterate_to_set s3.empty s3.ins_dj (set_iterator_image_filter f (
       set_iterator_product (s1.iteratei s1) (\<lambda>_. s2.iteratei s2)))"
    unfolding inj_image_filter_cartesian_product_def iterate_to_set_alt_def
      set_iterator_image_filter_def set_iterator_product_def 
    by simp

  definition inj_image_filter_cp where
    "inj_image_filter_cp f P s1 s2 \<equiv>
     inj_image_filter_cartesian_product 
      (\<lambda>xy. if P xy then Some (f xy) else None) s1 s2"

end

locale inj_image_filter_cp_loc = inj_image_filter_cp_defs_loc ops1 ops2 ops3 +
  s1: StdSet ops1 +
  s2: StdSet ops2 +
  s3: StdSet ops3
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('y,'s2,'more2) set_ops_scheme"
  and ops3 :: "('z,'s3,'more3) set_ops_scheme"
begin

  lemma inj_image_filter_cartesian_product_correct:
    fixes f :: "'x \<times> 'y \<rightharpoonup> 'z"
    assumes I[simp, intro!]: "s1.invar s1" "s2.invar s2"
    assumes INJ: "inj_on f (s1.\<alpha> s1 \<times> s2.\<alpha> s2 \<inter> dom f)"
    shows "s3.\<alpha> (inj_image_filter_cartesian_product f s1 s2) 
     = { z | x y z. f (x,y) = Some z \<and> x\<in>s1.\<alpha> s1 \<and> y\<in>s2.\<alpha> s2 }" (is ?T1)
    "s3.invar (inj_image_filter_cartesian_product f s1 s2)" (is ?T2)
  proof -
    from set_iterator_product_correct 
      [OF s1.iteratei_correct[OF I(1)] s2.iteratei_correct[OF I(2)]]
      have it_s12: "set_iterator 
        (set_iterator_product (s1.iteratei s1) (\<lambda>_. s2.iteratei s2))
        (s1.\<alpha> s1 \<times> s2.\<alpha> s2)" 
        by simp

      have LIS: 
        "set_ins_dj s3.\<alpha> s3.invar s3.ins_dj" 
        "set_empty s3.\<alpha> s3.invar s3.empty"
        by unfold_locales
  
      from iterate_inj_image_filter_to_set_correct[OF LIS it_s12 INJ]
      show ?T1 ?T2
        unfolding inj_image_filter_cartesian_product_alt by auto
  qed

  lemma inj_image_filter_cp_correct:
    assumes I: "s1.invar s1" "s2.invar s2"
    assumes INJ: "inj_on f {x\<in>s1.\<alpha> s1 \<times> s2.\<alpha> s2. P x}"
    shows 
    "s3.\<alpha> (inj_image_filter_cp f P s1 s2) 
     = { f (x, y) | x y. P (x, y) \<and> x\<in>s1.\<alpha> s1 \<and> y\<in>s2.\<alpha> s2 }" (is ?T1)
    "s3.invar (inj_image_filter_cp f P s1 s2)" (is ?T2)
  proof -
    let ?f = "\<lambda>xy. if P xy then Some (f xy) else None"
    from INJ have INJ': "inj_on ?f (s1.\<alpha> s1 \<times> s2.\<alpha> s2 \<inter> dom ?f)"
      by (force intro!: inj_onI dest: inj_onD split: if_split_asm)

    from inj_image_filter_cartesian_product_correct [OF I INJ']
    show "?T1" "?T2"
      unfolding inj_image_filter_cp_def
      by auto
  qed

end


subsubsection "Cartesian Product"

locale cart_defs_loc = inj_image_filter_cp_defs_loc ops1 ops2 ops3
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('y,'s2,'more2) set_ops_scheme"
  and ops3 :: "('x\<times>'y,'s3,'more3) set_ops_scheme"
begin

  definition "cart s1 s2 \<equiv>
    s1.iterate s1 
      (\<lambda>x. s2.iterate s2 (\<lambda>y res. s3.ins_dj (x,y) res)) 
      (s3.empty ())"

  lemma cart_alt: "cart s1 s2 == 
    inj_image_filter_cartesian_product Some s1 s2"
    unfolding cart_def inj_image_filter_cartesian_product_def
    by simp

end

locale cart_loc = cart_defs_loc ops1 ops2 ops3 
  + inj_image_filter_cp_loc ops1 ops2 ops3
  for ops1 :: "('x,'s1,'more1) set_ops_scheme"
  and ops2 :: "('y,'s2,'more2) set_ops_scheme"
  and ops3 :: "('x\<times>'y,'s3,'more3) set_ops_scheme"
begin

  lemma cart_correct:
    assumes I[simp, intro!]: "s1.invar s1" "s2.invar s2"
    shows "s3.\<alpha> (cart s1 s2) 
           = s1.\<alpha> s1 \<times> s2.\<alpha> s2" (is ?T1)
    "s3.invar (cart s1 s2)" (is ?T2)
    unfolding cart_alt
    by (auto simp add: 
      inj_image_filter_cartesian_product_correct[OF I, where f=Some])

end


subsection \<open>Generic Algorithms outside basic-set\<close>
text \<open>
  In this section, we present some generic algorithms that are not
  formulated in terms of basic-set. They are useful for setting up 
  some data structures.
\<close>

subsection \<open>Image (by image-filter)\<close>
definition "iflt_image iflt f s == iflt (\<lambda>x. Some (f x)) s"

lemma iflt_image_correct:
  assumes "set_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt"
  shows "set_image \<alpha>1 invar1 \<alpha>2 invar2 (iflt_image iflt)"
proof -
  interpret set_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold iflt_image_def)
    apply (auto simp add: image_filter_correct)
    done
qed

subsection\<open>Injective Image-Filter (by image-filter)\<close>

definition [code_unfold]: "iflt_inj_image = iflt_image"

lemma iflt_inj_image_correct:
  assumes "set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt"
  shows "set_inj_image \<alpha>1 invar1 \<alpha>2 invar2 (iflt_inj_image iflt)"
proof -
  interpret set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt by fact

  show ?thesis
    apply (unfold_locales)
    apply (unfold iflt_image_def iflt_inj_image_def)
    apply (subst inj_image_filter_correct)
    apply (auto simp add: dom_const intro: inj_onI dest: inj_onD)
    apply (subst inj_image_filter_correct)
    apply (auto simp add: dom_const intro: inj_onI dest: inj_onD)
    done
qed


subsection\<open>Filter (by image-filter)\<close>
definition "iflt_filter iflt P s == iflt (\<lambda>x. if P x then Some x else None) s"

lemma iflt_filter_correct:
  fixes \<alpha>1 :: "'s1 \<Rightarrow> 'a set"
  fixes \<alpha>2 :: "'s2 \<Rightarrow> 'a set"
  assumes "set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt"
  shows "set_filter \<alpha>1 invar1 \<alpha>2 invar2 (iflt_filter iflt)"
proof (rule set_filter.intro)
  fix s P
  assume invar_s: "invar1 s"
  interpret S: set_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 iflt by fact

  let ?f' = "\<lambda>x::'a. if P x then Some x else None"
  have inj_f': "inj_on ?f' (\<alpha>1 s \<inter> dom ?f')"
    by (simp add: inj_on_def Ball_def domIff)
  note correct' = S.inj_image_filter_correct [OF invar_s inj_f',
    folded iflt_filter_def]

  show "invar2 (iflt_filter iflt P s)"
       "\<alpha>2 (iflt_filter iflt P s) = {e \<in> \<alpha>1 s. P e}"
    by (auto simp add: correct')
qed

end
