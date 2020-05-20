section \<open>Zipping Sequences\<close>

theory Sequence_Zip
imports "Sequence_LTL"
begin

  subsection \<open>Zipping Lists\<close>

  notation zip (infixr "||" 51)

  lemmas [simp] = zip_map_fst_snd

  lemma split_zip[no_atp]: "(\<And> x. PROP P x) \<equiv> (\<And> y z. length y = length z \<Longrightarrow> PROP P (y || z))"
  proof
    fix y z
    assume 1: "\<And> x. PROP P x"
    show "PROP P (y || z)" using 1 by this
  next
    fix x :: "('a \<times> 'b) list"
    assume 1: "\<And> y z. length y = length z \<Longrightarrow> PROP P (y || z)"
    have 2: "length (map fst x) = length (map snd x)" by simp
    have 3: "PROP P (map fst x || map snd x)" using 1 2 by this
    show "PROP P x" using 3 by simp
  qed
  lemma split_zip_all[no_atp]: "(\<forall> x. P x) \<longleftrightarrow> (\<forall> y z. length y = length z \<longrightarrow> P (y || z))"
    by (fastforce iff: split_zip)
  lemma split_zip_ex[no_atp]: "(\<exists> x. P x) \<longleftrightarrow> (\<exists> y z. length y = length z \<and> P (y || z))"
    by (fastforce iff: split_zip)

  lemma zip_eq[iff]:
    assumes "length u = length v" "length r = length s"
    shows "u || v = r || s \<longleftrightarrow> u = r \<and> v = s"
    using assms zip_eq_conv by metis

  lemma list_rel_pred_zip: "list_all2 P xs ys \<longleftrightarrow> length xs = length ys \<and> list_all (case_prod P) (xs || ys)"
    unfolding list_all2_conv_all_nth list_all_length by auto

  lemma list_choice_zip: "list_all (\<lambda> x. \<exists> y. P x y) xs \<longleftrightarrow>
    (\<exists> ys. length ys = length xs \<and> list_all (case_prod P) (xs || ys))"
    unfolding list_choice list_rel_pred_zip by metis
  lemma list_choice_pair: "list_all (\<lambda> xy. case_prod (\<lambda> x y. \<exists> z. P x y z) xy) (xs || ys) \<longleftrightarrow>
    (\<exists> zs. length zs = min (length xs) (length ys) \<and> list_all (\<lambda> (x, y, z). P x y z) (xs || ys || zs))"
  proof -
    have 1: "list_all (\<lambda> (xy, z). case xy of (x, y) \<Rightarrow> P x y z) ((xs || ys) || zs) \<longleftrightarrow>
      list_all (\<lambda> (x, y, z). P x y z) (xs || ys || zs)" for zs
      unfolding zip_assoc list.pred_map by (auto intro!: list.pred_cong)
    have 2: "(\<lambda> (x, y). \<exists> z. P x y z) = (\<lambda> xy. \<exists> z. case xy of (x, y) \<Rightarrow> P x y z)" by auto
    show ?thesis unfolding list_choice_zip 1 2 by force
  qed

  lemma list_rel_zip[iff]:
    assumes "length u = length v" "length r = length s"
    shows "list_all2 (rel_prod A B) (u || v) (r || s) \<longleftrightarrow> list_all2 A u r \<and> list_all2 B v s"
  proof safe
    assume [transfer_rule]: "list_all2 (rel_prod A B) (u || v) (r || s)"
    have "list_all2 A (map fst (u || v)) (map fst (r || s))" by transfer_prover
    then show "list_all2 A u r" using assms by simp
    have "list_all2 B (map snd (u || v)) (map snd (r || s))" by transfer_prover
    then show "list_all2 B v s" using assms by simp
  next
    assume [transfer_rule]: "list_all2 A u r" "list_all2 B v s"
    show "list_all2 (rel_prod A B) (u || v) (r || s)" by transfer_prover
  qed

  lemma zip_last[simp]:
    assumes "xs || ys \<noteq> []" "length xs = length ys"
    shows "last (xs || ys) = (last xs, last ys)"
  proof -
    have 1: "xs \<noteq> []" "ys \<noteq> []" using assms(1) by auto
    have "last (xs || ys) = (xs || ys) ! (length (xs || ys) - 1)" using last_conv_nth assms by blast
    also have "\<dots> = (xs ! (length (xs || ys) - 1), ys ! (length (xs || ys) - 1))" using assms 1 by simp
    also have "\<dots> = (xs ! (length xs - 1), ys ! (length ys - 1))" using assms(2) by simp
    also have "\<dots> = (last xs, last ys)" using last_conv_nth 1 by metis
    finally show ?thesis by this
  qed

  subsection \<open>Zipping Streams\<close>

  notation szip (infixr "|||" 51)

  lemmas [simp] = szip_unfold

  lemma smap_szip_same: "smap f (xs ||| xs) = smap (\<lambda> x. f (x, x)) xs" by (coinduction arbitrary: xs) (auto)

  lemma szip_smap[simp]: "smap fst zs ||| smap snd zs = zs" by (coinduction arbitrary: zs) (auto)
  lemma szip_smap_fst[simp]: "smap fst (xs ||| ys) = xs" by (coinduction arbitrary: xs ys) (auto)
  lemma szip_smap_snd[simp]: "smap snd (xs ||| ys) = ys" by (coinduction arbitrary: xs ys) (auto)

  lemma szip_smap_both: "smap f xs ||| smap g ys = smap (map_prod f g) (xs ||| ys)" by (coinduction arbitrary: xs ys) (auto)
  lemma szip_smap_left: "smap f xs ||| ys = smap (apfst f) (xs ||| ys)" by (coinduction arbitrary: xs ys) (auto)
  lemma szip_smap_right: "xs ||| smap f ys = smap (apsnd f) (xs ||| ys)" by (coinduction arbitrary: xs ys) (auto)
  lemmas szip_smap_fold = szip_smap_both szip_smap_left szip_smap_right

  lemma szip_sconst_smap_fst: "sconst a ||| xs = smap (Pair a) xs"
    by (coinduction arbitrary: xs) (auto)
  lemma szip_sconst_smap_snd: "xs ||| sconst a = smap (prod.swap \<circ> Pair a) xs"
    by (coinduction arbitrary: xs) (auto)

  lemma split_szip[no_atp]: "(\<And> x. PROP P x) \<equiv> (\<And> y z. PROP P (y ||| z))"
  proof
    fix y z
    assume 1: "\<And> x. PROP P x"
    show "PROP P (y ||| z)" using 1 by this
  next
    fix x
    assume 1: "\<And> y z. PROP P (y ||| z)"
    have 2: "PROP P (smap fst x ||| smap snd x)" using 1 by this
    show "PROP P x" using 2 by simp
  qed
  lemma split_szip_all[no_atp]: "(\<forall> x. P x) \<longleftrightarrow> (\<forall> y z. P (y ||| z))" by (fastforce iff: split_szip)
  lemma split_szip_ex[no_atp]: "(\<exists> x. P x) \<longleftrightarrow> (\<exists> y z. P (y ||| z))" by (fastforce iff: split_szip)

  lemma szip_eq[iff]: "u ||| v = r ||| s \<longleftrightarrow> u = r \<and> v = s"
    using szip_smap_fst szip_smap_snd by metis

  lemma stream_rel_szip[iff]:
    "stream_all2 (rel_prod A B) (u ||| v) (r ||| s) \<longleftrightarrow> stream_all2 A u r \<and> stream_all2 B v s"
  proof safe
    assume [transfer_rule]: "stream_all2 (rel_prod A B) (u ||| v) (r ||| s)"
    have "stream_all2 A (smap fst (u ||| v)) (smap fst (r ||| s))" by transfer_prover
    then show "stream_all2 A u r" by simp
    have "stream_all2 B (smap snd (u ||| v)) (smap snd (r ||| s))" by transfer_prover
    then show "stream_all2 B v s" by simp
  next
    assume [transfer_rule]: "stream_all2 A u r" "stream_all2 B v s"
    show "stream_all2 (rel_prod A B) (u ||| v) (r ||| s)" by transfer_prover
  qed

  lemma szip_shift[simp]:
    assumes "length u = length s"
    shows "u @- v ||| s @- t = (u || s) @- (v ||| t)"
    using assms by (simp add: eq_shift stake_shift sdrop_shift)

  lemma szip_sset_fst[simp]: "fst ` sset (u ||| v) = sset u" by (metis stream.set_map szip_smap_fst)
  lemma szip_sset_snd[simp]: "snd ` sset (u ||| v) = sset v" by (metis stream.set_map szip_smap_snd)
  lemma szip_sset_elim[elim]:
    assumes "(a, b) \<in> sset (u ||| v)"
    obtains "a \<in> sset u" "b \<in> sset v"
    using assms by (metis image_eqI fst_conv snd_conv szip_sset_fst szip_sset_snd)
  lemma szip_sset[simp]: "sset (u ||| v) \<subseteq> sset u \<times> sset v" by auto

  lemma sset_szip_finite[iff]: "finite (sset (u ||| v)) \<longleftrightarrow> finite (sset u) \<and> finite (sset v)"
  proof safe
    assume 1: "finite (sset (u ||| v))"
    have 2: "finite (fst ` sset (u ||| v))" using 1 by blast
    have 3: "finite (snd ` sset (u ||| v))" using 1 by blast
    show "finite (sset u)" using 2 by simp
    show "finite (sset v)" using 3 by simp
  next
    assume 1: "finite (sset u)" "finite (sset v)"
    have "sset (u ||| v) \<subseteq> sset u \<times> sset v" by simp
    also have "finite \<dots>" using 1 by simp
    finally show "finite (sset (u ||| v))" by this
  qed

  lemma infs_szip_fst[iff]: "infs (P \<circ> fst) (u ||| v) \<longleftrightarrow> infs P u"
  proof -
    have "infs (P \<circ> fst) (u ||| v) \<longleftrightarrow> infs P (smap fst (u ||| v))"
      by (simp add: comp_def del: szip_smap_fst)
    also have "\<dots> \<longleftrightarrow> infs P u" by simp
    finally show ?thesis by this
  qed
  lemma infs_szip_snd[iff]: "infs (P \<circ> snd) (u ||| v) \<longleftrightarrow> infs P v"
  proof -
    have "infs (P \<circ> snd) (u ||| v) \<longleftrightarrow> infs P (smap snd (u ||| v))"
      by (simp add: comp_def del: szip_smap_snd)
    also have "\<dots> \<longleftrightarrow> infs P v" by simp
    finally show ?thesis by this
  qed

end