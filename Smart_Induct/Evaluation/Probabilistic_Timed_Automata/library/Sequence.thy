(* Author: Julian Brunner *)
(* This is originally a part of the CAVA model checker *)
theory Sequence
imports
  Basic
  "HOL-Library.Stream"
begin

  (* list basics *)

  declare upt_Suc[simp del]
  declare last.simps[simp del]
  declare butlast.simps[simp del]
  declare Cons_nth_drop_Suc[simp]

  lemma list_pred_cases:
    assumes "list_all P xs"
    obtains (nil) "xs = []" | (cons) y ys where "xs = y # ys" "P y" "list_all P ys"
    using assms by (cases xs) (auto)

  lemma fold_const: "fold const xs a = last (a # xs)"
    by (induct xs arbitrary: a) (auto simp: last.simps)

  lemma take_Suc: "take (Suc n) xs = (if xs = [] then [] else hd xs # take n (tl xs))"
    by (simp add: take_Suc)

  (* stream basics *)

  declare stream.map_id[simp]
  declare stream.set_map[simp]
  declare stream.set_sel(1)[intro!, simp]
  declare stream.pred_map[iff]
  declare stream.rel_map[iff]
  declare shift_simps[simp del]
  declare stake_sdrop[simp]
  declare stake_siterate[simp del]
  declare sdrop_snth[simp]

  lemma stream_pred_cases:
    assumes "pred_stream P xs"
    obtains (scons) y ys where "xs = y ## ys" "P y" "pred_stream P ys"
    using assms by (cases xs) (auto)

  lemma stream_rel_coinduct[case_names stream_rel, coinduct pred: stream_all2]:
    assumes "R u v"
    assumes "\<And> a u b v. R (a ## u) (b ## v) \<Longrightarrow> P a b \<and> R u v"
    shows "stream_all2 P u v"
    using assms by (coinduct) (metis stream.collapse)
  lemma stream_rel_coinduct_shift[case_names stream_rel, consumes 1]:
    assumes "R u v"
    assumes "\<And> u v. R u v \<Longrightarrow>
      \<exists> u\<^sub>1 u\<^sub>2 v\<^sub>1 v\<^sub>2. u = u\<^sub>1 @- u\<^sub>2 \<and> v = v\<^sub>1 @- v\<^sub>2 \<and> u\<^sub>1 \<noteq> [] \<and> v\<^sub>1 \<noteq> [] \<and> list_all2 P u\<^sub>1 v\<^sub>1 \<and> R u\<^sub>2 v\<^sub>2"
    shows "stream_all2 P u v"
  proof -
    have "\<exists> u\<^sub>1 u\<^sub>2 v\<^sub>1 v\<^sub>2. u = u\<^sub>1 @- u\<^sub>2 \<and> v = v\<^sub>1 @- v\<^sub>2 \<and> list_all2 P u\<^sub>1 v\<^sub>1 \<and> R u\<^sub>2 v\<^sub>2"
      using assms(1) by force
    then show ?thesis using assms(2) by (coinduct) (force elim: list.rel_cases)
  qed

  lemma stream_pred_coinduct[case_names stream_pred, coinduct pred: pred_stream]:
    assumes "R w"
    assumes "\<And> a w. R (a ## w) \<Longrightarrow> P a \<and> R w"
    shows "pred_stream P w"
    using assms unfolding stream.pred_rel eq_onp_def by (coinduction arbitrary: w) (auto)
  lemma stream_pred_coinduct_shift[case_names stream_pred, consumes 1]:
    assumes "R w"
    assumes "\<And> w. R w \<Longrightarrow> \<exists> u v. w = u @- v \<and> u \<noteq> [] \<and> list_all P u \<and> R v"
    shows "pred_stream P w"
  proof -
    have "\<exists> u v. w = u @- v \<and> list_all P u \<and> R v"
      using assms(1) by (metis list_all_simps(2) shift.simps(1))
    then show ?thesis using assms(2) by (coinduct) (force elim: list_pred_cases)
  qed
  lemma stream_pred_flat_coinduct[case_names stream_pred, consumes 1]:
    assumes "R ws"
    assumes "\<And> w ws. R (w ## ws) \<Longrightarrow> w \<noteq> [] \<and> list_all P w \<and> R ws"
    shows "pred_stream P (flat ws)"
    using assms
    by (coinduction arbitrary: ws rule: stream_pred_coinduct_shift) (metis stream.exhaust flat_Stream)

  lemmas stream_eq_coinduct[case_names stream_eq, coinduct pred: HOL.eq] =
    stream_rel_coinduct[where ?P = HOL.eq, unfolded stream.rel_eq]
  lemmas stream_eq_coinduct_shift[case_names stream_eq, consumes 1] =
    stream_rel_coinduct_shift[where ?P = HOL.eq, unfolded stream.rel_eq list.rel_eq]

  lemma sset_subset_stream_pred: "sset w \<subseteq> A \<longleftrightarrow> pred_stream (\<lambda> a. a \<in> A) w"
    unfolding stream.pred_set by auto
  lemma stream_pred_snth: "pred_stream P w \<longleftrightarrow> (\<forall> i. P (w !! i))"
    unfolding stream.pred_set sset_range by simp

  lemma stream_pred_shift[iff]: "pred_stream P (u @- v) \<longleftrightarrow> list_all P u \<and> pred_stream P v"
    by (induct u) (auto)
  lemma stream_rel_shift[iff]:
    assumes "length u\<^sub>1 = length v\<^sub>1"
    shows "stream_all2 P (u\<^sub>1 @- u\<^sub>2) (v\<^sub>1 @- v\<^sub>2) \<longleftrightarrow> list_all2 P u\<^sub>1 v\<^sub>1 \<and> stream_all2 P u\<^sub>2 v\<^sub>2"
    using assms by (induct rule: list_induct2) (auto)

  lemma eq_scons: "w = a ## v \<longleftrightarrow> a = shd w \<and> v = stl w" by auto
  lemma scons_eq: "a ## v = w \<longleftrightarrow> shd w = a \<and> stl w = v" by auto
  lemma eq_shift: "w = u @- v \<longleftrightarrow> stake (length u) w = u \<and> sdrop (length u) w = v"
    by (induct u arbitrary: w) (force+)
  lemma shift_eq: "u @- v = w \<longleftrightarrow> u = stake (length u) w \<and> v = sdrop (length u) w"
    by (induct u arbitrary: w) (force+)
  lemma scons_eq_shift: "a ## w = u @- v \<longleftrightarrow> ([] = u \<and> a ## w = v) \<or> (\<exists> u'. a # u' = u \<and> w = u' @- v)"
    by (cases u) (auto)
  lemma shift_eq_scons: "u @- v = a ## w \<longleftrightarrow> (u = [] \<and> v = a ## w) \<or> (\<exists> u'. u = a # u' \<and> u' @- v = w)"
    by (cases u) (auto)

  lemma stream_all2_sset1:
    assumes "stream_all2 P xs ys"
    shows "\<forall> x \<in> sset xs. \<exists> y \<in> sset ys. P x y"
  proof -
    have "pred_stream (\<lambda> x. \<exists> y \<in> S. P x y) xs" if "sset ys \<subseteq> S" for S
      using assms that by (coinduction arbitrary: xs ys) (force elim: stream.rel_cases)
    then show ?thesis unfolding stream.pred_set by auto
  qed
  lemma stream_all2_sset2:
    assumes "stream_all2 P xs ys"
    shows "\<forall> y \<in> sset ys. \<exists> x \<in> sset xs. P x y"
  proof -
    have "pred_stream (\<lambda> y. \<exists> x \<in> S. P x y) ys" if "sset xs \<subseteq> S" for S
      using assms that by (coinduction arbitrary: xs ys) (force elim: stream.rel_cases)
    then show ?thesis unfolding stream.pred_set by auto
  qed

  lemma smap_eq_scons[iff]: "smap f xs = y ## ys \<longleftrightarrow> f (shd xs) = y \<and> smap f (stl xs) = ys"
    using smap_ctr by metis
  lemma scons_eq_smap[iff]: "y ## ys = smap f xs \<longleftrightarrow> y = f (shd xs) \<and> ys = smap f (stl xs)"
    using smap_ctr by metis
  lemma smap_eq_shift[iff]:
    "smap f w = u @- v \<longleftrightarrow> (\<exists> w\<^sub>1 w\<^sub>2. w = w\<^sub>1 @- w\<^sub>2 \<and> map f w\<^sub>1 = u \<and> smap f w\<^sub>2 = v)"
    using sdrop_smap eq_shift stake_sdrop stake_smap by metis
  lemma shift_eq_smap[iff]:
    "u @- v = smap f w \<longleftrightarrow> (\<exists> w\<^sub>1 w\<^sub>2. w = w\<^sub>1 @- w\<^sub>2 \<and> u = map f w\<^sub>1 \<and> v = smap f w\<^sub>2)"
    using sdrop_smap eq_shift stake_sdrop stake_smap by metis

  lemma siterate_eq_scons[iff]: "siterate f s = a ## w \<longleftrightarrow> s = a \<and> siterate f (f s) = w"
    using siterate.ctr stream.inject by metis
  lemma scons_eq_siterate[iff]: "a ## w = siterate f s \<longleftrightarrow> a = s \<and> w = siterate f (f s)"
    using siterate.ctr stream.inject by metis

  lemma eqI_snth:
    assumes "\<And> i. u !! i = v !! i"
    shows "u = v"
    using assms by (coinduction arbitrary: u v) (metis stream.sel snth.simps)

  lemma set_sset_stake[intro!, simp]: "set (stake n xs) \<subseteq> sset xs"
    by (metis sset_shift stake_sdrop sup_ge1)
  lemma sset_sdrop[intro!, simp]: "sset (sdrop n xs) \<subseteq> sset xs"
    by (metis sset_shift stake_sdrop sup_ge2)

  lemma set_stake_snth: "x \<in> set (stake n xs) \<longleftrightarrow> (\<exists> i < n. xs !! i = x)"
    unfolding in_set_conv_nth by auto

  lemma split_stream_first:
    assumes "x \<in> sset xs"
    obtains ys zs
    where "xs = ys @- x ## zs" "x \<notin> set ys"
  proof
    let ?n = "LEAST n. xs !! n = x"
    have 1: "xs !! ?n = x" using assms unfolding sset_range by (auto intro: LeastI)
    have 2: "xs !! n \<noteq> x" if "n < ?n" for n using that by (metis (full_types) not_less_Least)
    show "xs = stake ?n xs @- x ## sdrop (Suc ?n) xs" using 1 by (metis id_stake_snth_sdrop)
    show "x \<notin> set (stake ?n xs)" using 2 by (meson set_stake_snth)
  qed

  (* scans *)

  fun scan :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b list" where
    "scan f [] a = []" | "scan f (x # xs) a = f x a # scan f xs (f x a)"

  lemma scan_append[simp]: "scan f (xs @ ys) a = scan f xs a @ scan f ys (fold f xs a)"
    by (induct xs arbitrary: a) (auto)

  lemma scan_eq_nil[iff]: "scan f xs a = [] \<longleftrightarrow> xs = []" by (cases xs) (auto)
  lemma scan_eq_cons[iff]:
    "scan f xs a = b # w \<longleftrightarrow> (\<exists> y ys. xs = y # ys \<and> f y a = b \<and> scan f ys (f y a) = w)"
    by (cases xs) (auto)
  lemma scan_eq_append[iff]:
    "scan f xs a = u @ v \<longleftrightarrow> (\<exists> ys zs. xs = ys @ zs \<and> scan f ys a = u \<and> scan f zs (fold f ys a) = v)"
    by (induct u arbitrary: xs a) (auto, metis append_Cons fold_simps(2), blast)

  lemma scan_length[simp]: "length (scan f xs a) = length xs"
    by (induct xs arbitrary: a) (auto)
  lemma scan_last: "last (a # scan f xs a) = fold f xs a"
    by (induct xs arbitrary: a) (auto simp: last.simps)

  lemma scan_const[simp]: "scan const xs a = xs"
    by (induct xs arbitrary: a) (auto)
  lemma scan_nth[simp]:
    assumes "i < length (scan f xs a)"
    shows "scan f xs a ! i = fold f (take (Suc i) xs) a"
    using assms by (cases xs, simp, induct i arbitrary: xs a, auto simp: take_Suc neq_Nil_conv)
  lemma scan_map[simp]: "scan f (map g xs) a = scan (f \<circ> g) xs a"
    by (induct xs arbitrary: a) (auto)
  lemma scan_take[simp]: "take k (scan f xs a) = scan f (take k xs) a"
    by (induct k arbitrary: xs a) (auto simp: take_Suc neq_Nil_conv)
  lemma scan_drop[simp]: "drop k (scan f xs a) = scan f (drop k xs) (fold f (take k xs) a)"
    by (induct k arbitrary: xs a) (auto simp: take_Suc neq_Nil_conv)

  primcorec sscan :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a stream \<Rightarrow> 'b \<Rightarrow> 'b stream" where
    "sscan f xs a = f (shd xs) a ## sscan f (stl xs) (f (shd xs) a)"

  lemma sscan_scons[simp]: "sscan f (x ## xs) a = f x a ## sscan f xs (f x a)"
    by (simp add: stream.expand)
  lemma sscan_shift[simp]: "sscan f (xs @- ys) a = scan f xs a @- sscan f ys (fold f xs a)"
    by (induct xs arbitrary: a) (auto)

  lemma sscan_eq_scons[iff]:
    "sscan f xs a = b ## w \<longleftrightarrow> f (shd xs) a = b \<and> sscan f (stl xs) (f (shd xs) a) = w"
    using sscan.ctr stream.inject by metis
  lemma scons_eq_sscan[iff]:
    "b ## w = sscan f xs a \<longleftrightarrow> b = f (shd xs) a \<and> w = sscan f (stl xs) (f (shd xs) a)"
    using sscan.ctr stream.inject by metis

  lemma sscan_const[simp]: "sscan const xs a = xs"
    by (coinduction arbitrary: xs a) (auto)
  lemma sscan_snth[simp]: "sscan f xs a !! i = fold f (stake (Suc i) xs) a"
    by (induct i arbitrary: xs a) (auto)
  lemma sscan_scons_snth[simp]: "(a ## sscan f xs a) !! i = fold f (stake i xs) a"
    by (induct i arbitrary: xs a) (auto)
  lemma sscan_smap[simp]: "sscan f (smap g xs) a = sscan (f \<circ> g) xs a"
    by (coinduction arbitrary: xs a) (auto)
  lemma sscan_stake[simp]: "stake k (sscan f xs a) = scan f (stake k xs) a"
    by (induct k arbitrary: a xs) (auto)
  lemma sscan_sdrop[simp]: "sdrop k (sscan f xs a) = sscan f (sdrop k xs) (fold f (stake k xs) a)"
    by (induct k arbitrary: a xs) (auto)

  (* sdistinct *)

  coinductive sdistinct :: "'a stream \<Rightarrow> bool" where
    scons[intro!]: "x \<notin> sset xs \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (x ## xs)"

  lemma sdistinct_scons_elim[elim!]:
    assumes "sdistinct (x ## xs)"
    obtains "x \<notin> sset xs" "sdistinct xs"
    using assms by (auto elim: sdistinct.cases)

  lemma sdistinct_coinduct[case_names sdistinct, coinduct pred: sdistinct]:
    assumes "P xs"
    assumes "\<And> x xs. P (x ## xs) \<Longrightarrow> x \<notin> sset xs \<and> P xs"
    shows "sdistinct xs"
    using stream.collapse sdistinct.coinduct assms by metis

  lemma sdistinct_shift[intro!]:
    assumes "distinct xs" "sdistinct ys" "set xs \<inter> sset ys = {}"
    shows "sdistinct (xs @- ys)"
    using assms by (induct xs) (auto)
  lemma sdistinct_shift_elim[elim!]:
    assumes "sdistinct (xs @- ys)"
    obtains "distinct xs" "sdistinct ys" "set xs \<inter> sset ys = {}"
    using assms by (induct xs) (auto)

  lemma sdistinct_infinite_sset:
    assumes "sdistinct w"
    shows "infinite (sset w)"
    using assms by (coinduction arbitrary: w) (force elim: sdistinct.cases)

  lemma not_sdistinct_decomp:
    assumes "\<not> sdistinct w"
    obtains u v a w'
    where "w = u @- a ## v @- a ## w'"
  proof (rule ccontr)
    assume 1: "\<not> thesis"
    assume 2: "w = u @- a ## v @- a ## w' \<Longrightarrow> thesis" for u a v w'
    have 3: "\<forall> u v a w'. w \<noteq> u @- a ## v @- a ## w'" using 1 2 by auto
    have 4: "sdistinct w" using 3 by (coinduct) (metis id_stake_snth_sdrop imageE shift.simps sset_range)
    show False using assms 4 by auto
  qed

  (* sorted streams *)

  coinductive (in order) sascending :: "'a stream \<Rightarrow> bool" where
    "a \<le> b \<Longrightarrow> sascending (b ## w) \<Longrightarrow> sascending (a ## b ## w)"

  coinductive (in order) sdescending :: "'a stream \<Rightarrow> bool" where
    "a \<ge> b \<Longrightarrow> sdescending (b ## w) \<Longrightarrow> sdescending (a ## b ## w)"

  lemma sdescending_coinduct[case_names sdescending, coinduct pred: sdescending]:
    assumes "P w"
    assumes "\<And> a b w. P (a ## b ## w) \<Longrightarrow> a \<ge> b \<and> P (b ## w)"
    shows "sdescending w"
    using stream.collapse sdescending.coinduct assms by (metis (no_types))

  lemma sdescending_sdrop:
    assumes "sdescending w"
    shows "sdescending (sdrop k w)"
    using assms by (induct k) (auto, metis sdescending.cases sdrop_stl stream.sel(2))

  lemma sdescending_snth_antimono:
    assumes "sdescending w"
    shows "antimono (snth w)"
  unfolding antimono_iff_le_Suc
  proof
    fix k
    have "sdescending (sdrop k w)" using sdescending_sdrop assms by this
    then obtain a b v where 2: "sdrop k w = a ## b ## v" "a \<ge> b" by rule
    then show "w !! k \<ge> w !! Suc k" by (metis sdrop_simps stream.sel)
  qed

  lemma sdescending_stuck:
    fixes w :: "'a :: wellorder stream"
    assumes "sdescending w"
    obtains k
    where "sdrop k w = sconst (w !! k)"
  using assms
  proof (induct "w !! 0" arbitrary: w thesis rule: less_induct)
    case less
    show ?case
    proof (cases "w = sconst (w !! 0)")
      case True
      show ?thesis using less(2)[of 0] True by simp
    next
      case False
      obtain k where 1: "w !! k \<noteq> w !! 0"
        using False by (metis empty_iff eqI_snth insert_iff snth_sset sset_sconst)
      have 2: "antimono (snth w)" using sdescending_snth_antimono less(3) by this
      have 3: "w !! k \<le> w !! 0" using 1 2 by (blast dest: antimonoD)
      have 4: "sdrop k w !! 0 < w !! 0" using 1 3 by auto
      have 5: "sdescending (sdrop k w)" using sdescending_sdrop less(3) by this
      obtain l where 5: "sdrop l (sdrop k w) = sconst (sdrop k w !! l)"
        using less(1)[OF 4 _ 5] by this
      show ?thesis using less(2) 5 by simp
    qed
  qed

end
