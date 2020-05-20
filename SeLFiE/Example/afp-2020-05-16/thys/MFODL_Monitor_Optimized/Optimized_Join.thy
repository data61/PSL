(*<*)
theory Optimized_Join
  imports "Generic_Join.Generic_Join_Correctness"
begin
(*>*)

section \<open>Optimized relational join\<close>

subsection \<open>Binary join\<close>

definition join_mask :: "nat \<Rightarrow> nat set \<Rightarrow> bool list" where
  "join_mask n X = map (\<lambda>i. i \<in> X) [0..<n]"

fun proj_tuple :: "bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a tuple" where
  "proj_tuple [] [] = []"
| "proj_tuple (True # bs) (a # as) = a # proj_tuple bs as"
| "proj_tuple (False # bs) (a # as) = None # proj_tuple bs as"
| "proj_tuple (b # bs) [] = []"
| "proj_tuple [] (a # as) = []"

lemma proj_tuple_replicate: "(\<And>i. i \<in> set bs \<Longrightarrow> \<not>i) \<Longrightarrow> length bs = length as \<Longrightarrow>
  proj_tuple bs as = replicate (length bs) None"
  by (induction bs as rule: proj_tuple.induct) fastforce+

lemma proj_tuple_join_mask_empty: "length as = n \<Longrightarrow>
  proj_tuple (join_mask n {}) as = replicate n None"
  using proj_tuple_replicate[of "join_mask n {}"] by (auto simp add: join_mask_def)

lemma proj_tuple_alt: "proj_tuple bs as = map2 (\<lambda>b a. if b then a else None) bs as"
  by (induction bs as rule: proj_tuple.induct) auto

lemma map2_map: "map2 f (map g [0..<length as]) as = map (\<lambda>i. f (g i) (as ! i)) [0..<length as]"
  by (rule nth_equalityI) auto

lemma proj_tuple_join_mask_restrict: "length as = n \<Longrightarrow>
  proj_tuple (join_mask n X) as = restrict X as"
  by (auto simp add: restrict_def proj_tuple_alt join_mask_def map2_map)

lemma wf_tuple_proj_idle:
  assumes wf: "wf_tuple n X as"
  shows "proj_tuple (join_mask n X) as = as"
  using proj_tuple_join_mask_restrict[of as n X, unfolded restrict_idle[OF wf]] wf
  by (auto simp add: wf_tuple_def)

lemma wf_tuple_change_base:
  assumes wf: "wf_tuple n X as"
  and mask: "join_mask n X = join_mask n Y"
  shows "wf_tuple n Y as"
  using wf mask by (auto simp add: wf_tuple_def join_mask_def)

definition proj_tuple_in_join :: "bool \<Rightarrow> bool list \<Rightarrow> 'a tuple \<Rightarrow> 'a table \<Rightarrow> bool" where
  "proj_tuple_in_join pos bs as t = (if pos then proj_tuple bs as \<in> t else proj_tuple bs as \<notin> t)"

abbreviation "join_cond pos t \<equiv> (\<lambda>as. if pos then as \<in> t else as \<notin> t)"

abbreviation "join_filter_cond pos t \<equiv> (\<lambda>as _. join_cond pos t as)"

lemma proj_tuple_in_join_mask_idle:
  assumes wf: "wf_tuple n X as"
  shows "proj_tuple_in_join pos (join_mask n X) as t \<longleftrightarrow> join_cond pos t as"
  using wf_tuple_proj_idle[OF wf] by (auto simp add: proj_tuple_in_join_def)

lemma join_sub:
  assumes "L \<subseteq> R" "table n L t1" "table n R t2"
  shows "join t2 pos t1 = {as \<in> t2. proj_tuple_in_join pos (join_mask n L) as t1}"
  using assms proj_tuple_join_mask_restrict[of _ n L] join_restrict[of t2 n R t1 L pos]
    wf_tuple_length restrict_idle
  by (auto simp add: table_def proj_tuple_in_join_def sup.absorb1) fastforce+

lemma join_sub':
  assumes "R \<subseteq> L" "table n L t1" "table n R t2"
  shows "join t2 True t1 = {as \<in> t1. proj_tuple_in_join True (join_mask n R) as t2}"
  using assms proj_tuple_join_mask_restrict[of _ n R] join_restrict[of t2 n R t1 L True]
    wf_tuple_length restrict_idle
  by (auto simp add: table_def proj_tuple_in_join_def sup.absorb1 Un_absorb1) fastforce+

lemma join_eq:
  assumes tab: "table n R t1" "table n R t2"
  shows "join t2 pos t1 = (if pos then t2 \<inter> t1 else t2 - t1)"
  using join_sub[OF _ tab, of pos] tab(2) proj_tuple_in_join_mask_idle[of n R _ pos t1]
  by (auto simp add: table_def)

lemma join_no_cols:
  assumes tab: "table n {} t1" "table n R t2"
  shows "join t2 pos t1 = (if (pos \<longleftrightarrow> replicate n None \<in> t1) then t2 else {})"
  using join_sub[OF _ tab, of pos] tab(2)
  by (auto simp add: table_def proj_tuple_in_join_def wf_tuple_length proj_tuple_join_mask_empty)

lemma join_empty_left: "join {} pos t = {}"
  by (auto simp add: join_def)

lemma join_empty_right: "join t pos {} = (if pos then {} else t)"
  by (auto simp add: join_def)

fun bin_join :: "nat \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> bool \<Rightarrow> nat set \<Rightarrow> 'a table \<Rightarrow> 'a table" where
  "bin_join n A t pos A' t' =
    (if t = {} then {}
    else if t' = {} then (if pos then {} else t)
    else if A' = {} then (if (pos \<longleftrightarrow> replicate n None \<in> t') then t else {})
    else if A' = A then (if pos then t \<inter> t' else t - t')
    else if A' \<subseteq> A then {as \<in> t. proj_tuple_in_join pos (join_mask n A') as t'}
    else if A \<subseteq> A' \<and> pos then {as \<in> t'. proj_tuple_in_join pos (join_mask n A) as t}
    else join t pos t')"

lemma bin_join_table:
  assumes tab: "table n A t" "table n A' t'"
  shows "bin_join n A t pos A' t' = join t pos t'"
  using assms join_empty_left[of pos t'] join_empty_right[of t pos]
    join_no_cols[OF _ assms(1), of t' pos] join_eq[of n A t' t pos] join_sub[OF _ assms(2,1)]
    join_sub'[OF _ assms(2,1)]
  by auto+

subsection \<open>Multi-way join\<close>

fun mmulti_join' :: "(nat set list \<Rightarrow> nat set list \<Rightarrow> 'a table list \<Rightarrow> 'a table)" where
  "mmulti_join' A_pos A_neg L = (
    let Q = set (zip A_pos L) in
    let Q_neg = set (zip A_neg (drop (length A_pos) L)) in
    New_max_getIJ_wrapperGenericJoin Q Q_neg)"

lemma mmulti_join'_correct:
  assumes "A_pos \<noteq> []"
      and "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) L"
  shows "z \<in> mmulti_join' A_pos A_neg L \<longleftrightarrow> wf_tuple n (\<Union>A\<in>set A_pos. A) z \<and>
    list_all2 (\<lambda>A X. restrict A z \<in> X) A_pos (take (length A_pos) L) \<and>
    list_all2 (\<lambda>A X. restrict A z \<notin> X) A_neg (drop (length A_pos) L)"
proof -
  define Q where "Q = set (zip A_pos L)"
  have Q_alt: "Q = set (zip A_pos (take (length A_pos) L))"
    unfolding Q_def by (fastforce simp: in_set_zip)
  define Q_neg where "Q_neg = set (zip A_neg (drop (length A_pos) L))"
  let ?r = "mmulti_join' A_pos A_neg L"
  have "?r = New_max_getIJ_wrapperGenericJoin Q Q_neg"
    unfolding Q_def Q_neg_def by (simp del: New_max.wrapperGenericJoin.simps)
  moreover have "card Q \<ge> 1"
    unfolding Q_def using assms(1,2)
    by (auto simp: Suc_le_eq card_gt_0_iff zip_eq_Nil_iff)
  moreover have "\<forall>(A, X)\<in>(Q \<union> Q_neg). table n A X \<and> wf_set n A"
    unfolding Q_alt Q_neg_def using assms(2) by (simp add: zip_append1 list_all2_iff)
  ultimately have "z \<in> ?r \<longleftrightarrow> wf_tuple n (\<Union>(A, X)\<in>Q. A) z \<and>
      (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X)"
    using New_max.wrapper_correctness case_prod_beta' by blast
  moreover have "(\<Union>A\<in>set A_pos. A) = (\<Union>(A, X)\<in>Q. A)" proof -
    from assms(2) have "length A_pos \<le> length L" by (auto dest!: list_all2_lengthD)
    then show ?thesis
      unfolding Q_alt
      by (auto elim: in_set_impl_in_set_zip1[rotated, where ys="take (length A_pos) L"]
          dest: set_zip_leftD)
  qed
  moreover have "\<And>z. (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<longleftrightarrow>
    list_all2 (\<lambda>A X. restrict A z \<in> X) A_pos (take (length A_pos) L)"
    unfolding Q_alt using assms(2) by (auto simp add: list_all2_iff)
  moreover have "\<And>z. (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X) \<longleftrightarrow>
    list_all2 (\<lambda>A X. restrict A z \<notin> X) A_neg (drop (length A_pos) L)"
    unfolding Q_neg_def using assms(2) by (auto simp add: list_all2_iff)
  ultimately show ?thesis
    unfolding Q_def Q_neg_def using assms(2) by simp
qed

lemmas restrict_nested = New_max.restrict_nested

lemma list_all2_opt_True:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ((A_zs @ A_x # A_xs @ A_y # A_ys) @ A_neg)
    ((zs @ x # xs @ y # ys) @ L_neg)"
    "length A_xs = length xs" "length A_ys = length ys" "length A_zs = length zs"
  shows "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
    ((A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) @ A_neg) ((zs @ join x True y # xs @ ys) @ L_neg)"
proof -
  have assms_dest: "table n A_x x" "table n A_y y" "wf_set n A_x" "wf_set n A_y"
    using assms
    by (auto simp del: mmulti_join'.simps simp add: list_all2_append1 dest: list_all2_lengthD)
  then have tabs: "table n (A_x \<union> A_y) (join x True y)" "wf_set n (A_x \<union> A_y)"
    using join_table[of n A_x x A_y y True "A_x \<union> A_y", OF assms_dest(1,2)] assms_dest(3,4)
    by (auto simp add: wf_set_def)
  then show "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
    ((A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) @ A_neg) ((zs @ join x True y # xs @ ys) @ L_neg)"
    using assms
    by (auto simp del: mmulti_join'.simps simp add: list_all2_append1 list_all2_append2
        list_all2_Cons1 list_all2_Cons2 dest: list_all2_lengthD) fastforce
qed

lemma mmulti_join'_opt_True:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) ((A_zs @ A_x # A_xs @ A_y # A_ys) @ A_neg)
    ((zs @ x # xs @ y # ys) @ L_neg)"
    "length A_xs = length xs" "length A_ys = length ys" "length A_zs = length zs"
  shows "mmulti_join' (A_zs @ A_x # A_xs @ A_y # A_ys) A_neg ((zs @ x # xs @ y # ys) @ L_neg) =
    mmulti_join' (A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) A_neg
    ((zs @ join x True y # xs @ ys) @ L_neg)"
proof -
  have assms_dest: "table n A_x x" "table n A_y y" "wf_set n A_x" "wf_set n A_y"
    using assms
    by (auto simp del: mmulti_join'.simps simp add: list_all2_append1 dest: list_all2_lengthD)
  then have tabs: "table n (A_x \<union> A_y) (join x True y)" "wf_set n (A_x \<union> A_y)"
    using join_table[of n A_x x A_y y True "A_x \<union> A_y", OF assms_dest(1,2)] assms_dest(3,4)
    by (auto simp add: wf_set_def)
  then have list_all2': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
    ((A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) @ A_neg) ((zs @ join x True y # xs @ ys) @ L_neg)"
    using assms
    by (auto simp del: mmulti_join'.simps simp add: list_all2_append1 list_all2_append2
        list_all2_Cons1 list_all2_Cons2 dest: list_all2_lengthD) fastforce
  have res: "\<And>z Z. wf_tuple n Z z \<Longrightarrow> A_x \<union> A_y \<subseteq> Z \<Longrightarrow>
    restrict (A_x \<union> A_y) z \<in> join x True y \<longleftrightarrow> restrict A_x z \<in> x \<and> restrict A_y z \<in> y"
    using join_restrict[of x n A_x y A_y True] wf_tuple_restrict_simple[of n _ _ "A_x \<union> A_y"]
      assms_dest(1,2)
    by (auto simp add: table_def restrict_nested Int_absorb2)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix z
    assume "z \<in> mmulti_join' (A_zs @ A_x # A_xs @ A_y # A_ys) A_neg
      ((zs @ x # xs @ y # ys) @ L_neg)"
    then have z_in_dest: "wf_tuple n (\<Union>(set (A_zs @ A_x # A_xs @ A_y # A_ys))) z"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_zs zs"
      "restrict A_x z \<in> x"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_ys ys"
      "restrict A_y z \<in> y"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_xs xs"
      "list_all2 (\<lambda>A. (\<notin>) (restrict A z)) A_neg L_neg"
      using mmulti_join'_correct[OF _ assms(1), of z]
      by (auto simp del: mmulti_join'.simps simp add: assms list_all2_append1
          dest: list_all2_lengthD)
    then show "z \<in> mmulti_join' (A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) A_neg
      ((zs @ join x True y # xs @ ys) @ L_neg)"
      using mmulti_join'_correct[OF _ list_all2', of z] res[OF z_in_dest(1)]
      by (auto simp add: assms list_all2_appendI le_supI2 Un_assoc simp del: mmulti_join'.simps
          dest: list_all2_lengthD)
  next
    fix z
    assume "z \<in> mmulti_join' (A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) A_neg
      ((zs @ join x True y # xs @ ys) @ L_neg)"
    then have z_in_dest: "wf_tuple n (\<Union>(set (A_zs @ A_x # A_xs @ A_y # A_ys))) z"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_zs zs"
      "restrict (A_x \<union> A_y) z \<in> join x True y"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_ys ys"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_xs xs"
      "list_all2 (\<lambda>A. (\<notin>) (restrict A z)) A_neg L_neg"
      using mmulti_join'_correct[OF _ list_all2', of z]
      by (auto simp del: mmulti_join'.simps simp add: assms list_all2_append Un_assoc
          dest: list_all2_lengthD)
    then show "z \<in> mmulti_join' (A_zs @ A_x # A_xs @ A_y # A_ys) A_neg
      ((zs @ x # xs @ y # ys) @ L_neg)"
      using mmulti_join'_correct[OF _ assms(1), of z] res[OF z_in_dest(1)]
      by (auto simp add: assms list_all2_appendI le_supI2 Un_assoc simp del: mmulti_join'.simps
          dest: list_all2_lengthD)
  qed
qed

lemma list_all2_opt_False:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
    ((A_zs @ A_x # A_xs) @ (A_ws @ A_y # A_ys)) ((zs @ x # xs) @ (ws @ y # ys))"
    "length A_ws = length ws" "length A_xs = length xs"
    "length A_ys = length ys" "length A_zs = length zs"
    "A_y \<subseteq> A_x"
  shows "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
    ((A_zs @ A_x # A_xs) @ (A_ws @ A_ys)) ((zs @ join x False y # xs) @ (ws @ ys))"
proof -
  have assms_dest: "table n A_x x" "table n A_y y" "wf_set n A_x" "wf_set n A_y"
    using assms
    by (auto simp del: mmulti_join'.simps simp add: list_all2_append dest: list_all2_lengthD)
  have tabs: "table n A_x (join x False y)"
    using join_table[of n A_x x A_y y False A_x, OF assms_dest(1,2) assms(6)] assms(6) by auto
  then show "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
    ((A_zs @ A_x # A_xs) @ (A_ws @ A_ys)) ((zs @ join x False y # xs) @ (ws @ ys))"
    using assms assms_dest(3)
    by (auto simp del: mmulti_join'.simps simp add: list_all2_append1 list_all2_append2
        list_all2_Cons1 list_all2_Cons2 dest: list_all2_lengthD) fastforce
qed

lemma mmulti_join'_opt_False:
  assumes "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
    ((A_zs @ A_x # A_xs) @ (A_ws @ A_y # A_ys)) ((zs @ x # xs) @ (ws @ y # ys))"
    "length A_ws = length ws" "length A_xs = length xs"
    "length A_ys = length ys" "length A_zs = length zs"
    "A_y \<subseteq> A_x"
  shows "mmulti_join' (A_zs @ A_x # A_xs) (A_ws @ A_y # A_ys) ((zs @ x # xs) @ (ws @ y # ys)) =
    mmulti_join' (A_zs @ A_x # A_xs) (A_ws @ A_ys) ((zs @ join x False y # xs) @ (ws @ ys))"
proof -
  have assms_dest: "table n A_x x" "table n A_y y" "wf_set n A_x" "wf_set n A_y"
    using assms
    by (auto simp del: mmulti_join'.simps simp add: list_all2_append dest: list_all2_lengthD)
  have tabs: "table n A_x (join x False y)"
    using join_table[of n A_x x A_y y False A_x, OF assms_dest(1,2) assms(6)] assms(6) by auto
  then have list_all2': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
    ((A_zs @ A_x # A_xs) @ (A_ws @ A_ys)) ((zs @ join x False y # xs) @ (ws @ ys))"
    using assms assms_dest(3)
    by (auto simp del: mmulti_join'.simps simp add: list_all2_append1 list_all2_append2
        list_all2_Cons1 list_all2_Cons2 dest: list_all2_lengthD) fastforce
  have res: "\<And>z. restrict A_x z \<in> join x False y \<longleftrightarrow> restrict A_x z \<in> x \<and> restrict A_y z \<notin> y"
    using join_restrict[of x n A_x y A_y False, OF _ _ assms(6)] assms_dest(1,2) assms(6)
    by (auto simp add: table_def restrict_nested Int_absorb2 Un_absorb2)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix z
    assume "z \<in> mmulti_join' (A_zs @ A_x # A_xs) (A_ws @ A_y # A_ys)
      ((zs @ x # xs) @ ws @ y # ys)"
    then have z_in_dest: "wf_tuple n (\<Union>(set (A_zs @ A_x # A_xs))) z"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_zs zs"
      "restrict A_x z \<in> x"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_xs xs"
      "list_all2 (\<lambda>A. (\<notin>) (restrict A z)) A_ws ws"
      "restrict A_y z \<notin> y"
      "list_all2 (\<lambda>A. (\<notin>) (restrict A z)) A_ys ys"
      using mmulti_join'_correct[OF _ assms(1), of z]
      by (auto simp del: mmulti_join'.simps simp add: assms list_all2_append1
          dest: list_all2_lengthD)
    then show "z \<in> mmulti_join' (A_zs @ A_x # A_xs) (A_ws @ A_ys)
      ((zs @ join x False y # xs) @ ws @ ys)"
      using mmulti_join'_correct[OF _ list_all2', of z] res
      by (auto simp add: assms list_all2_appendI Un_assoc simp del: mmulti_join'.simps
          dest: list_all2_lengthD)
  next
    fix z
    assume "z \<in> mmulti_join' (A_zs @ A_x # A_xs) (A_ws @ A_ys)
      ((zs @ join x False y # xs) @ ws @ ys)"
    then have z_in_dest: "wf_tuple n (\<Union>(set (A_zs @ A_x # A_xs))) z"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_zs zs"
      "restrict A_x z \<in> join x False y"
      "list_all2 (\<lambda>A. (\<in>) (restrict A z)) A_xs xs"
      "list_all2 (\<lambda>A. (\<notin>) (restrict A z)) A_ws ws"
      "list_all2 (\<lambda>A. (\<notin>) (restrict A z)) A_ys ys"
      using mmulti_join'_correct[OF _ list_all2', of z]
      by (auto simp del: mmulti_join'.simps simp add: assms list_all2_append1
          dest: list_all2_lengthD)
    then show "z \<in> mmulti_join' (A_zs @ A_x # A_xs) (A_ws @ A_y # A_ys)
      ((zs @ x # xs) @ ws @ y # ys)"
      using mmulti_join'_correct[OF _ assms(1), of z] res
      by (auto simp add: assms list_all2_appendI Un_assoc simp del: mmulti_join'.simps
          dest: list_all2_lengthD)
  qed
qed

fun find_sub_in :: "'a set \<Rightarrow> 'a set list \<Rightarrow> bool \<Rightarrow>
  ('a set list \<times> 'a set \<times> 'a set list) option" where
  "find_sub_in X [] b = None"
| "find_sub_in X (x # xs) b = (if (x \<subseteq> X \<or> (b \<and> X \<subseteq> x)) then Some ([], x, xs)
    else (case find_sub_in X xs b of None \<Rightarrow> None | Some (ys, z, zs) \<Rightarrow> Some (x # ys, z, zs)))"

lemma find_sub_in_sound: "find_sub_in X xs b = Some (ys, z, zs) \<Longrightarrow>
  xs = ys @ z # zs \<and> (z \<subseteq> X \<or> (b \<and> X \<subseteq> z))"
  by (induction X xs b arbitrary: ys z zs rule: find_sub_in.induct)
     (fastforce split: if_splits option.splits)+

fun find_sub_True :: "'a set list \<Rightarrow>
  ('a set list \<times> 'a set \<times> 'a set list \<times> 'a set \<times> 'a set list) option" where
  "find_sub_True [] = None"
| "find_sub_True (x # xs) = (case find_sub_in x xs True of None \<Rightarrow>
    (case find_sub_True xs of None \<Rightarrow> None
    | Some (ys, w, ws, z, zs) \<Rightarrow> Some (x # ys, w, ws, z, zs))
  | Some (ys, z, zs) \<Rightarrow> Some ([], x, ys, z, zs))"

lemma find_sub_True_sound: "find_sub_True xs = Some (ys, w, ws, z, zs) \<Longrightarrow>
  xs = ys @ w # ws @ z # zs \<and> (z \<subseteq> w \<or> w \<subseteq> z)"
  using find_sub_in_sound
  by (induction xs arbitrary: ys w ws z zs rule: find_sub_True.induct)
     (fastforce split: option.splits)+

fun find_sub_False :: "'a set list \<Rightarrow> 'a set list \<Rightarrow>
  (('a set list \<times> 'a set \<times> 'a set list) \<times> ('a set list \<times> 'a set \<times> 'a set list)) option" where
  "find_sub_False [] ns = None"
| "find_sub_False (x # xs) ns = (case find_sub_in x ns False of None \<Rightarrow>
    (case find_sub_False xs ns of None \<Rightarrow> None
    | Some ((rs, w, ws), (ys, z, zs)) \<Rightarrow> Some ((x # rs, w, ws), (ys, z, zs)))
  | Some (ys, z, zs) \<Rightarrow> Some (([], x, xs), (ys, z, zs)))"

lemma find_sub_False_sound: "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs)) \<Longrightarrow>
  xs = rs @ w # ws \<and> ns = ys @ z # zs \<and> (z \<subseteq> w)"
  using find_sub_in_sound
  by (induction xs ns arbitrary: rs w ws ys z zs rule: find_sub_False.induct)
     (fastforce split: option.splits)+

fun proj_list_3 :: "'a list \<Rightarrow> ('b list \<times> 'b \<times> 'b list) \<Rightarrow> ('a list \<times> 'a \<times> 'a list)" where
  "proj_list_3 xs (ys, z, zs) = (take (length ys) xs, xs ! (length ys),
    take (length zs) (drop (length ys + 1) xs))"

lemma proj_list_3_same:
  assumes "proj_list_3 xs (ys, z, zs) = (ys', z', zs')"
    "length xs = length ys + 1 + length zs"
  shows "xs = ys' @ z' # zs'"
  using assms by (auto simp add: id_take_nth_drop)

lemma proj_list_3_length:
  assumes "proj_list_3 xs (ys, z, zs) = (ys', z', zs')"
    "length xs = length ys + 1 + length zs"
  shows "length ys = length ys'" "length zs = length zs'"
  using assms by auto

fun proj_list_5 :: "'a list \<Rightarrow>
  ('b list \<times> 'b \<times> 'b list \<times> 'b \<times> 'b list) \<Rightarrow>
  ('a list \<times> 'a \<times> 'a list \<times> 'a \<times> 'a list)" where
  "proj_list_5 xs (ys, w, ws, z, zs) = (take (length ys) xs, xs ! (length ys),
    take (length ws) (drop (length ys + 1) xs), xs ! (length ys + 1 + length ws),
    drop (length ys + 1 + length ws + 1) xs)"

lemma proj_list_5_same:
  assumes "proj_list_5 xs (ys, w, ws, z, zs) = (ys', w', ws', z', zs')"
    "length xs = length ys + 1 + length ws + 1 + length zs"
  shows "xs = ys' @ w' # ws' @ z' # zs'"
proof -
  have "xs ! length ys # take (length ws) (drop (Suc (length ys)) xs) = take (Suc (length ws)) (drop (length ys) xs)"
    using assms(2) by (simp add: list_eq_iff_nth_eq nth_Cons split: nat.split)
  moreover have "take (Suc (length ws)) (drop (length ys) xs) @ drop (Suc (length ys + length ws)) xs =
      drop (length ys) xs"
    unfolding Suc_eq_plus1 add.assoc[of _ _ 1] add.commute[of _ "length ws + 1"]
      drop_drop[symmetric, of "length ws + 1"] append_take_drop_id ..
  ultimately show ?thesis
    using assms by (auto simp: Cons_nth_drop_Suc append_Cons[symmetric])
qed

lemma proj_list_5_length:
  assumes "proj_list_5 xs (ys, w, ws, z, zs) = (ys', w', ws', z', zs')"
    "length xs = length ys + 1 + length ws + 1 + length zs"
  shows "length ys = length ys'" "length ws = length ws'"
    "length zs = length zs'"
  using assms by auto

fun dominate_True :: "nat set list \<Rightarrow> 'a table list \<Rightarrow>
  ((nat set list \<times> nat set \<times> nat set list \<times> nat set \<times> nat set list) \<times>
  ('a table list \<times> 'a table \<times> 'a table list \<times> 'a table \<times> 'a table list)) option" where
  "dominate_True A_pos L_pos = (case find_sub_True A_pos of None \<Rightarrow> None
  | Some split \<Rightarrow> Some (split, proj_list_5 L_pos split))"

lemma find_sub_True_proj_list_5_same:
  assumes "find_sub_True xs = Some (ys, w, ws, z, zs)" "length xs = length xs'"
    "proj_list_5 xs' (ys, w, ws, z, zs) = (ys', w', ws', z', zs')"
  shows "xs' = ys' @ w' # ws' @ z' # zs'"
proof -
  have len: "length xs' = length ys + 1 + length ws + 1 + length zs"
    using find_sub_True_sound[OF assms(1)] by (auto simp add: assms(2)[symmetric])
  show ?thesis
    using proj_list_5_same[OF assms(3) len] .
qed

lemma find_sub_True_proj_list_5_length:
  assumes "find_sub_True xs = Some (ys, w, ws, z, zs)" "length xs = length xs'"
    "proj_list_5 xs' (ys, w, ws, z, zs) = (ys', w', ws', z', zs')"
  shows "length ys = length ys'" "length ws = length ws'"
    "length zs = length zs'"
  using find_sub_True_sound[OF assms(1)] proj_list_5_length[OF assms(3)] assms(2) by auto

lemma dominate_True_sound:
  assumes "dominate_True A_pos L_pos = Some ((A_zs, A_x, A_xs, A_y, A_ys), (zs, x, xs, y, ys))"
    "length A_pos = length L_pos"
  shows "A_pos = A_zs @ A_x # A_xs @ A_y # A_ys" "L_pos = zs @ x # xs @ y # ys"
    "length A_xs = length xs" "length A_ys = length ys" "length A_zs = length zs"
  using assms find_sub_True_sound find_sub_True_proj_list_5_same find_sub_True_proj_list_5_length
  by (auto simp del: proj_list_5.simps split: option.splits) fast+

fun dominate_False :: "nat set list \<Rightarrow> 'a table list \<Rightarrow> nat set list \<Rightarrow> 'a table list \<Rightarrow>
  (((nat set list \<times> nat set \<times> nat set list) \<times> nat set list \<times> nat set \<times> nat set list) \<times>
  (('a table list \<times> 'a table \<times> 'a table list) \<times>
  'a table list \<times> 'a table \<times> 'a table list)) option" where
  "dominate_False A_pos L_pos A_neg L_neg = (case find_sub_False A_pos A_neg of None \<Rightarrow> None
  | Some (pos_split, neg_split) \<Rightarrow>
    Some ((pos_split, neg_split), (proj_list_3 L_pos pos_split, proj_list_3 L_neg neg_split)))"

lemma find_sub_False_proj_list_3_same_left:
  assumes "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs))"
    "length xs = length xs'" "proj_list_3 xs' (rs, w, ws) = (rs', w', ws')"
  shows "xs' = rs' @ w' # ws'"
proof -
  have len: "length xs' = length rs + 1 + length ws"
    using find_sub_False_sound[OF assms(1)] by (auto simp add: assms(2)[symmetric])
  show ?thesis
    using proj_list_3_same[OF assms(3) len] .
qed

lemma find_sub_False_proj_list_3_length_left:
  assumes "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs))"
    "length xs = length xs'" "proj_list_3 xs' (rs, w, ws) = (rs', w', ws')"
  shows "length rs = length rs'" "length ws = length ws'"
  using find_sub_False_sound[OF assms(1)] proj_list_3_length[OF assms(3)] assms(2) by auto

lemma find_sub_False_proj_list_3_same_right:
  assumes "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs))"
    "length ns = length ns'" "proj_list_3 ns' (ys, z, zs) = (ys', z', zs')"
  shows "ns' = ys' @ z' # zs'"
proof -
  have len: "length ns' = length ys + 1 + length zs"
    using find_sub_False_sound[OF assms(1)] by (auto simp add: assms(2)[symmetric])
  show ?thesis
    using proj_list_3_same[OF assms(3) len] .
qed

lemma find_sub_False_proj_list_3_length_right:
  assumes "find_sub_False xs ns = Some ((rs, w, ws), (ys, z, zs))"
    "length ns = length ns'" "proj_list_3 ns' (ys, z, zs) = (ys', z', zs')"
  shows "length ys = length ys'" "length zs = length zs'"
  using find_sub_False_sound[OF assms(1)] proj_list_3_length[OF assms(3)] assms(2) by auto

lemma dominate_False_sound:
  assumes "dominate_False A_pos L_pos A_neg L_neg =
    Some (((A_zs, A_x, A_xs), A_ws, A_y, A_ys), ((zs, x, xs), ws, y, ys))"
    "length A_pos = length L_pos" "length A_neg = length L_neg"
  shows "A_pos = (A_zs @ A_x # A_xs)" "A_neg = A_ws @ A_y # A_ys"
    "L_pos = (zs @ x # xs)" "L_neg = ws @ y # ys"
    "length A_ws = length ws" "length A_xs = length xs"
    "length A_ys = length ys" "length A_zs = length zs"
    "A_y \<subseteq> A_x"
  using assms find_sub_False_proj_list_3_same_left find_sub_False_proj_list_3_same_right
    find_sub_False_proj_list_3_length_left find_sub_False_proj_list_3_length_right
    find_sub_False_sound
  by (auto simp del: proj_list_3.simps split: option.splits) fast+

function mmulti_join :: "(nat \<Rightarrow> nat set list \<Rightarrow> nat set list \<Rightarrow> 'a table list \<Rightarrow> 'a table)" where
  "mmulti_join n A_pos A_neg L = (if length A_pos + length A_neg \<noteq> length L then {} else
    let L_pos = take (length A_pos) L; L_neg = drop (length A_pos) L in
    (case dominate_True A_pos L_pos of None \<Rightarrow>
      (case dominate_False A_pos L_pos A_neg L_neg of None \<Rightarrow> mmulti_join' A_pos A_neg L
      | Some (((A_zs, A_x, A_xs), A_ws, A_y, A_ys), ((zs, x, xs), ws, y, ys)) \<Rightarrow>
        mmulti_join n (A_zs @ A_x # A_xs) (A_ws @ A_ys)
        ((zs @ bin_join n A_x x False A_y y # xs) @ (ws @ ys)))
    | Some ((A_zs, A_x, A_xs, A_y, A_ys), (zs, x, xs, y, ys)) \<Rightarrow>
      mmulti_join n (A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) A_neg
      ((zs @ bin_join n A_x x True A_y y # xs @ ys) @ L_neg)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(n, A_pos, A_neg, L). length A_pos + length A_neg)")
    (use find_sub_True_sound find_sub_False_sound in \<open>fastforce split: option.splits\<close>)+

lemma mmulti_join_link:
  assumes "A_pos \<noteq> []"
      and "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) L"
    shows "mmulti_join n A_pos A_neg L = mmulti_join' A_pos A_neg L"
  using assms
proof (induction A_pos A_neg L rule: mmulti_join.induct)
  case (1 n A_pos A_neg L)
  define L_pos where "L_pos = take (length A_pos) L"
  define L_neg where "L_neg = drop (length A_pos) L"
  have L_def: "L = L_pos @ L_neg"
    using L_pos_def L_neg_def by auto
  have lens_match: "length A_pos = length L_pos" "length A_neg = length L_neg"
    using L_pos_def L_neg_def 1(4)[unfolded L_def] by (auto dest: list_all2_lengthD)
  then have lens_sum: "length A_pos + length A_neg = length L"
    by (auto simp add: L_def)
  show ?case
  proof (cases "dominate_True A_pos L_pos")
    case None
    note dom_True = None
    show ?thesis
    proof (cases "dominate_False A_pos L_pos A_neg L_neg")
      case None
      show ?thesis
        by (subst mmulti_join.simps)
           (simp del: dominate_True.simps dominate_False.simps mmulti_join.simps
            mmulti_join'.simps add: Let_def dom_True L_pos_def[symmetric] None
            L_neg_def[symmetric] lens_sum split: option.splits)
    next
      case (Some a)
      then obtain A_zs A_x A_xs A_ws A_y A_ys zs x xs ws y ys where
        dom_False: "dominate_False A_pos L_pos A_neg L_neg =
        Some (((A_zs, A_x, A_xs), A_ws, A_y, A_ys), ((zs, x, xs), ws, y, ys))"
        by (cases a) auto
      note list_all2 = 1(4)[unfolded L_def dominate_False_sound[OF dom_False lens_match]]
      have lens: "length A_ws = length ws" "length A_xs = length xs"
        "length A_ys = length ys" "length A_zs = length zs"
        using dominate_False_sound[OF dom_False lens_match] by auto
      have sub: "A_y \<subseteq> A_x"
        using dominate_False_sound[OF dom_False lens_match] by auto
      have list_all2': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
        ((A_zs @ A_x # A_xs) @ (A_ws @ A_ys)) ((zs @ join x False y # xs) @ (ws @ ys))"
        using list_all2_opt_False[OF list_all2 lens sub] .
      have tabs: "table n A_x x" "table n A_y y"
        using list_all2 by (auto simp add: lens list_all2_append)
      have bin_join_conv: "join x False y = bin_join n A_x x False A_y y"
        using bin_join_table[OF tabs, symmetric] .
      have mmulti: "mmulti_join n A_pos A_neg L = mmulti_join n (A_zs @ A_x # A_xs) (A_ws @ A_ys)
        ((zs @ bin_join n A_x x False A_y y # xs) @ (ws @ ys))"
        by (subst mmulti_join.simps)
           (simp del: dominate_True.simps dominate_False.simps mmulti_join.simps
            add: Let_def dom_True L_pos_def[symmetric] L_neg_def[symmetric] dom_False lens_sum)
      show ?thesis
        unfolding mmulti
        unfolding L_def dominate_False_sound[OF dom_False lens_match]
        by (rule 1(1)[OF _ L_pos_def L_neg_def dom_True dom_False,
            OF _ _ _ _ _ _ _ _ _ _ _ _ _ list_all2'[unfolded bin_join_conv],
            unfolded mmulti_join'_opt_False[OF list_all2 lens sub, symmetric,
            unfolded bin_join_conv]])
           (auto simp add: lens_sum)
    qed
  next
    case (Some a)
    then obtain A_zs A_x A_xs A_y A_ys zs x xs y ys where dom_True: "dominate_True A_pos L_pos =
      Some ((A_zs, A_x, A_xs, A_y, A_ys), (zs, x, xs, y, ys))"
      by (cases a) auto
    note list_all2 = 1(4)[unfolded L_def dominate_True_sound[OF dom_True lens_match(1)]]
    have lens: "length A_xs = length xs" "length A_ys = length ys" "length A_zs = length zs"
      using dominate_True_sound[OF dom_True lens_match(1)] by auto
    have list_all2': "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A)
      ((A_zs @ (A_x \<union> A_y) # A_xs @ A_ys) @ A_neg) ((zs @ join x True y # xs @ ys) @ L_neg)"
      using list_all2_opt_True[OF list_all2 lens] .
    have tabs: "table n A_x x" "table n A_y y"
        using list_all2 by (auto simp add: lens list_all2_append)
    have bin_join_conv: "join x True y = bin_join n A_x x True A_y y"
      using bin_join_table[OF tabs, symmetric] .
    have mmulti: "mmulti_join n A_pos A_neg L = mmulti_join n (A_zs @ (A_x \<union> A_y) # A_xs @ A_ys)
      A_neg ((zs @ bin_join n A_x x True A_y y # xs @ ys) @ L_neg)"
      by (subst mmulti_join.simps)
         (simp del: dominate_True.simps dominate_False.simps mmulti_join.simps
          add: Let_def dom_True L_pos_def[symmetric] L_neg_def lens_sum)
    show ?thesis
      unfolding mmulti
      unfolding L_def dominate_True_sound[OF dom_True lens_match(1)]
      by (rule 1(2)[OF _ L_pos_def L_neg_def dom_True,
          OF _ _ _ _ _ _ _ _ _ _ _ list_all2'[unfolded bin_join_conv],
          unfolded mmulti_join'_opt_True[OF list_all2 lens, symmetric,
          unfolded bin_join_conv]])
         (auto simp add: lens_sum)
  qed
qed

lemma mmulti_join_correct:
  assumes "A_pos \<noteq> []"
      and "list_all2 (\<lambda>A X. table n A X \<and> wf_set n A) (A_pos @ A_neg) L"
  shows "z \<in> mmulti_join n A_pos A_neg L \<longleftrightarrow> wf_tuple n (\<Union>A\<in>set A_pos. A) z \<and>
    list_all2 (\<lambda>A X. restrict A z \<in> X) A_pos (take (length A_pos) L) \<and>
    list_all2 (\<lambda>A X. restrict A z \<notin> X) A_neg (drop (length A_pos) L)"
  unfolding mmulti_join_link[OF assms] using mmulti_join'_correct[OF assms] .

end
