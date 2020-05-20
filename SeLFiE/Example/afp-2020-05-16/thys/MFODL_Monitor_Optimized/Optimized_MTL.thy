(*<*)
theory Optimized_MTL
  imports Monitor
begin
(*>*)

section \<open>Efficient implementation of temporal operators\<close>

subsection \<open>Optimized queue data structure\<close>

lemma less_enat_iff: "a < enat i \<longleftrightarrow> (\<exists>j. a = enat j \<and> j < i)"
  by (cases a) auto

type_synonym 'a queue_t = "'a list \<times> 'a list"

definition queue_invariant :: "'a queue_t \<Rightarrow> bool" where
  "queue_invariant q = (case q of ([], []) \<Rightarrow> True | (fs, l # ls) \<Rightarrow> True | _ \<Rightarrow> False)"

typedef 'a queue = "{q :: 'a queue_t. queue_invariant q}"
  by (auto simp: queue_invariant_def split: list.splits)

setup_lifting type_definition_queue

lift_definition linearize :: "'a queue \<Rightarrow> 'a list" is "(\<lambda>q. case q of (fs, ls) \<Rightarrow> fs @ rev ls)" .

lift_definition empty_queue :: "'a queue" is "([], [])"
  by (auto simp: queue_invariant_def split: list.splits)

lemma empty_queue_rep: "linearize empty_queue = []"
  by transfer (simp add: empty_queue_def linearize_def)

lift_definition is_empty :: "'a queue \<Rightarrow> bool" is "\<lambda>q. (case q of ([], []) \<Rightarrow> True | _ \<Rightarrow> False)" .

lemma linearize_t_Nil: "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = [] \<longleftrightarrow> q = ([], [])"
  by (auto split: prod.splits)

lemma is_empty_alt: "is_empty q \<longleftrightarrow> linearize q = []"
  by transfer (auto simp: linearize_t_Nil list.case_eq_if)

fun prepend_queue_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "prepend_queue_t a ([], []) = ([], [a])"
| "prepend_queue_t a (fs, l # ls) = (a # fs, l # ls)"
| "prepend_queue_t a (f # fs, []) = undefined"

lift_definition prepend_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is prepend_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim: prepend_queue_t.elims)

lemma prepend_queue_rep: "linearize (prepend_queue a q) = a # linearize q"
  by transfer
    (auto simp add: queue_invariant_def linearize_def elim: prepend_queue_t.elims split: prod.splits)

lift_definition append_queue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is
  "(\<lambda>a q. case q of (fs, ls) \<Rightarrow> (fs, a # ls))"
  by (auto simp: queue_invariant_def split: list.splits)

lemma append_queue_rep: "linearize (append_queue a q) = linearize q @ [a]"
  by transfer (auto simp add: linearize_def split: prod.splits)

fun safe_last_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_last_t ([], []) = (None, ([], []))"
| "safe_last_t (fs, l # ls) = (Some l, (fs, l # ls))"
| "safe_last_t (f # fs, []) = undefined"

lift_definition safe_last :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_last_t
  by (auto simp: queue_invariant_def split: prod.splits list.splits)

lemma safe_last_rep: "safe_last q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = last (linearize q))"
  by transfer (auto simp: queue_invariant_def split: list.splits elim: safe_last_t.elims)

fun safe_hd_t :: "'a queue_t \<Rightarrow> 'a option \<times> 'a queue_t" where
  "safe_hd_t ([], []) = (None, ([], []))"
| "safe_hd_t ([], [l]) = (Some l, ([], [l]))"
| "safe_hd_t ([], l # ls) = (let fs = rev ls in (Some (hd fs), (fs, [l])))"
| "safe_hd_t (f # fs, l # ls) = (Some f, (f # fs, l # ls))"
| "safe_hd_t (f # fs, []) = undefined"

lift_definition(code_dt) safe_hd :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" is safe_hd_t
proof -
  fix q :: "'a queue_t"
  assume "queue_invariant q"
  then show "pred_prod \<top> queue_invariant (safe_hd_t q)"
    by (cases q rule: safe_hd_t.cases) (auto simp: queue_invariant_def Let_def split: list.split)
qed

lemma safe_hd_rep: "safe_hd q = (\<alpha>, q') \<Longrightarrow> linearize q = linearize q' \<and>
  (case \<alpha> of None \<Rightarrow> linearize q = [] | Some a \<Rightarrow> linearize q \<noteq> [] \<and> a = hd (linearize q))"
  by transfer
    (auto simp add: queue_invariant_def Let_def hd_append split: list.splits elim: safe_hd_t.elims)

fun replace_hd_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "replace_hd_t a ([], []) = ([], [])"
| "replace_hd_t a ([], [l]) = ([], [a])"
| "replace_hd_t a ([], l # ls) = (let fs = rev ls in (a # tl fs, [l]))"
| "replace_hd_t a (f # fs, l # ls) = (a # fs, l # ls)"
| "replace_hd_t a (f # fs, []) = undefined"

lift_definition replace_hd :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is replace_hd_t
  by (auto simp: queue_invariant_def split: list.splits elim: replace_hd_t.elims)

lemma tl_append: "xs \<noteq> [] \<Longrightarrow> tl xs @ ys = tl (xs @ ys)"
  by simp

lemma replace_hd_rep: "linearize q = f # fs \<Longrightarrow> linearize (replace_hd a q) = a # fs"
proof (transfer fixing: f fs a)
  fix q
  assume "queue_invariant q" and "(case q of (fs, ls) \<Rightarrow> fs @ rev ls) = f # fs"
  then show "(case replace_hd_t a q of (fs, ls) \<Rightarrow> fs @ rev ls) = a # fs"
    by (cases "(a, q)" rule: replace_hd_t.cases) (auto simp: queue_invariant_def tl_append)
qed

fun replace_last_t :: "'a \<Rightarrow> 'a queue_t \<Rightarrow> 'a queue_t" where
  "replace_last_t a ([], []) = ([], [])"
| "replace_last_t a (fs, l # ls) = (fs, a # ls)"
| "replace_last_t a (fs, []) = undefined"

lift_definition replace_last :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" is replace_last_t
  by (auto simp: queue_invariant_def split: list.splits elim: replace_last_t.elims)

lemma replace_last_rep: "linearize q = fs @ [f] \<Longrightarrow> linearize (replace_last a q) = fs @ [a]"
  by transfer (auto simp: queue_invariant_def split: list.splits prod.splits elim!: replace_last_t.elims)

fun tl_queue_t :: "'a queue_t \<Rightarrow> 'a queue_t" where
  "tl_queue_t ([], []) = ([], [])"
| "tl_queue_t ([], [l]) = ([], [])"
| "tl_queue_t ([], l # ls) = (tl (rev ls), [l])"
| "tl_queue_t (a # as, fs) = (as, fs)"

lift_definition tl_queue :: "'a queue \<Rightarrow> 'a queue" is tl_queue_t
  by (auto simp: queue_invariant_def split: list.splits elim!: tl_queue_t.elims)

lemma tl_queue_rep: "\<not>is_empty q \<Longrightarrow> linearize (tl_queue q) = tl (linearize q)"
  by transfer (auto simp: tl_append split: prod.splits list.splits elim!: tl_queue_t.elims)

lemma length_tl_queue_rep: "\<not>is_empty q \<Longrightarrow>
  length (linearize (tl_queue q)) < length (linearize q)"
  by transfer (auto split: prod.splits list.splits elim: tl_queue_t.elims)

lemma length_tl_queue_safe_hd:
  assumes "safe_hd q = (Some a, q')"
  shows "length (linearize (tl_queue q')) < length (linearize q)"
  using safe_hd_rep[OF assms]
  by (auto simp add: length_tl_queue_rep is_empty_alt)

function dropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "dropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a then dropWhile_queue f (tl_queue q') else q')"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma dropWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  dropWhile P xs = (if P (hd xs) then dropWhile P (tl xs) else xs)"
  by (cases xs) auto

lemma dropWhile_queue_rep: "linearize (dropWhile_queue f q) = dropWhile f (linearize q)"
  by (induction f q rule: dropWhile_queue.induct)
     (auto simp add: tl_queue_rep dropWhile_hd_tl is_empty_alt
      split: prod.splits option.splits dest: safe_hd_rep)

function takeWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "takeWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> q'
  | (Some a, q') \<Rightarrow> if f a
    then prepend_queue a (takeWhile_queue f (tl_queue q'))
    else empty_queue)"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takeWhile_hd_tl: "xs \<noteq> [] \<Longrightarrow>
  takeWhile P xs = (if P (hd xs) then hd xs # takeWhile P (tl xs) else [])"
  by (cases xs) auto

lemma takeWhile_queue_rep: "linearize (takeWhile_queue f q) = takeWhile f (linearize q)"
  by (induction f q rule: takeWhile_queue.induct)
     (auto simp add: prepend_queue_rep tl_queue_rep empty_queue_rep takeWhile_hd_tl is_empty_alt
      split: prod.splits option.splits dest: safe_hd_rep)

function takedropWhile_queue :: "('a \<Rightarrow> bool) \<Rightarrow> 'a queue \<Rightarrow> 'a queue \<times> 'a list" where
  "takedropWhile_queue f q = (case safe_hd q of (None, q') \<Rightarrow> (q', [])
  | (Some a, q') \<Rightarrow> if f a
    then (case takedropWhile_queue f (tl_queue q') of (q'', as) \<Rightarrow> (q'', a # as))
    else (q', []))"
  by pat_completeness auto
termination
  using length_tl_queue_safe_hd[OF sym]
  by (relation "measure (\<lambda>(f, q). length (linearize q))") (fastforce split: prod.splits)+

lemma takedropWhile_queue_fst: "fst (takedropWhile_queue f q) = dropWhile_queue f q"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits) (auto simp add: case_prod_unfold split: option.splits)
qed

lemma takedropWhile_queue_snd: "snd (takedropWhile_queue f q) = takeWhile f (linearize q)"
proof (induction f q rule: takedropWhile_queue.induct)
  case (1 f q)
  then show ?case
    by (simp split: prod.splits)
      (auto simp add: case_prod_unfold tl_queue_rep takeWhile_hd_tl is_empty_alt
        split: option.splits dest: safe_hd_rep)
qed

subsection \<open>Optimized data structure for Since\<close>

type_synonym 'a mmsaux = "ts \<times> ts \<times> bool list \<times> bool list \<times>
  (ts \<times> 'a table) queue \<times> (ts \<times> 'a table) queue \<times>
  (('a tuple, ts) mapping) \<times> (('a tuple, ts) mapping)"

fun time_mmsaux :: "'a mmsaux \<Rightarrow> ts" where
  "time_mmsaux aux = (case aux of (nt, _) \<Rightarrow> nt)"

definition ts_tuple_rel :: "(ts \<times> 'a table) set \<Rightarrow> (ts \<times> 'a tuple) set" where
  "ts_tuple_rel ys = {(t, as). \<exists>X. as \<in> X \<and> (t, X) \<in> ys}"

lemma finite_fst_ts_tuple_rel: "finite (fst ` {tas \<in> ts_tuple_rel (set xs). P tas})"
proof -
  have "fst ` {tas \<in> ts_tuple_rel (set xs). P tas} \<subseteq> fst ` ts_tuple_rel (set xs)"
    by auto
  moreover have "\<dots> \<subseteq> set (map fst xs)"
    by (force simp add: ts_tuple_rel_def)
  finally show ?thesis
    using finite_subset by blast
qed

lemma ts_tuple_rel_ext_Cons: "tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_ext_Cons': "tas \<in> ts_tuple_rel (set tass) \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_intro: "as \<in> X \<Longrightarrow> (t, X) \<in> ys \<Longrightarrow> (t, as) \<in> ts_tuple_rel ys"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_dest: "(t, as) \<in> ts_tuple_rel ys \<Longrightarrow> \<exists>X. (t, X) \<in> ys \<and> as \<in> X"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_Un: "ts_tuple_rel (ys \<union> zs) = ts_tuple_rel ys \<union> ts_tuple_rel zs"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_ext: "tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, Y \<union> X) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
  then obtain as where tas_def: "tas = (nt, as)" "as \<in> X"
    by (cases tas) (auto simp add: ts_tuple_rel_def)
  then have "as \<in> Y \<union> X"
    by auto
  then show "tas \<in> ts_tuple_rel (set ((nt, Y \<union> X) # tass))"
    unfolding tas_def(1)
    by (rule ts_tuple_rel_intro) auto
qed

lemma ts_tuple_rel_ext': "tas \<in> ts_tuple_rel (set ((nt, X) # tass)) \<Longrightarrow>
  tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
proof -
  assume assm: "tas \<in> ts_tuple_rel (set ((nt, X) # tass))"
  then have "tas \<in> ts_tuple_rel {(nt, X)} \<union> ts_tuple_rel (set tass)"
    using ts_tuple_rel_Un by force
  then show "tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
  proof
    assume "tas \<in> ts_tuple_rel {(nt, X)}"
    then show ?thesis
      by (auto simp: Un_commute dest!: ts_tuple_rel_ext)
  next
    assume "tas \<in> ts_tuple_rel (set tass)"
    then have "tas \<in> ts_tuple_rel (set ((nt, X \<union> Y) # tass))"
      by (rule ts_tuple_rel_ext_Cons')
    then show ?thesis by simp
  qed
qed

lemma ts_tuple_rel_mono: "ys \<subseteq> zs \<Longrightarrow> ts_tuple_rel ys \<subseteq> ts_tuple_rel zs"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_filter: "ts_tuple_rel (set (filter (\<lambda>(t, X). P t) xs)) =
  {(t, X) \<in> ts_tuple_rel (set xs). P t}"
  by (auto simp add: ts_tuple_rel_def)

lemma ts_tuple_rel_set_filter: "x \<in> ts_tuple_rel (set (filter P xs)) \<Longrightarrow>
  x \<in> ts_tuple_rel (set xs)"
  by (auto simp add: ts_tuple_rel_def)

definition valid_tuple :: "(('a tuple, ts) mapping) \<Rightarrow> (ts \<times> 'a tuple) \<Rightarrow> bool" where
  "valid_tuple tuple_since = (\<lambda>(t, as). case Mapping.lookup tuple_since as of None \<Rightarrow> False
  | Some t' \<Rightarrow> t \<ge> t')"

definition safe_max :: "'a :: linorder set \<Rightarrow> 'a option" where
  "safe_max X = (if X = {} then None else Some (Max X))"

lemma safe_max_empty: "safe_max X = None \<longleftrightarrow> X = {}"
  by (simp add: safe_max_def)

lemma safe_max_empty_dest: "safe_max X = None \<Longrightarrow> X = {}"
  by (simp add: safe_max_def split: if_splits)

lemma safe_max_Some_intro: "x \<in> X \<Longrightarrow> \<exists>y. safe_max X = Some y"
  using safe_max_empty by auto

lemma safe_max_Some_dest_in: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> x \<in> X"
  using Max_in by (auto simp add: safe_max_def split: if_splits)

lemma safe_max_Some_dest_le: "finite X \<Longrightarrow> safe_max X = Some x \<Longrightarrow> y \<in> X \<Longrightarrow> y \<le> x"
  using Max_ge by (auto simp add: safe_max_def split: if_splits)

fun valid_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a Monitor.msaux \<Rightarrow> bool" where
  "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<longleftrightarrow>
    (args_L args) \<subseteq> (args_R args) \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    (\<forall>(t, X) \<in> set ys. table (args_n args) (args_R args) X) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_in) \<and>
    table (args_n args) (args_R args) (Mapping.keys tuple_since) \<and>
    (\<forall>as \<in> \<Union>(snd ` (set (linearize data_prev))). wf_tuple (args_n args) (args_R args) as) \<and>
    cur = nt \<and>
    ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since tas} \<and>
    sorted (map fst (linearize data_prev)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt \<and> nt - t < left (args_ivl args)) \<and>
    sorted (map fst (linearize data_in)) \<and>
    (\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt \<and> nt - t \<ge> left (args_ivl args)) \<and>
    (\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since tas \<and> as = snd tas})) \<and>
    (\<forall>as \<in> Mapping.keys tuple_since. case Mapping.lookup tuple_since as of Some t \<Rightarrow> t \<le> nt)"

lemma Mapping_lookup_filter_keys: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  Mapping.lookup (Mapping.filter f m) k = Mapping.lookup m k"
  by (metis default_def insert_subset keys_default keys_filter lookup_default lookup_default_filter)

lemma Mapping_filter_keys: "(\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys (Mapping.filter f m). P (Mapping.lookup (Mapping.filter f m) k))"
  using Mapping_lookup_filter_keys Mapping.keys_filter by fastforce

lemma Mapping_filter_keys_le: "(\<And>x. P x \<Longrightarrow> P' x) \<Longrightarrow>
  (\<forall>k \<in> Mapping.keys m. P (Mapping.lookup m k)) \<Longrightarrow> (\<forall>k \<in> Mapping.keys m. P' (Mapping.lookup m k))"
  by auto

lemma Mapping_keys_dest: "x \<in> Mapping.keys f \<Longrightarrow> \<exists>y. Mapping.lookup f x = Some y"
  by (simp add: domD keys_dom_lookup)

lemma Mapping_keys_intro: "Mapping.lookup f x \<noteq> None \<Longrightarrow> x \<in> Mapping.keys f"
  by (simp add: domIff keys_dom_lookup)

lemma valid_mmsaux_tuple_in_keys: "valid_mmsaux args cur
  (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) ys \<Longrightarrow>
  Mapping.keys tuple_in = snd ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
  valid_tuple tuple_since tas}"
  by (auto intro!: Mapping_keys_intro safe_max_Some_intro
      dest!: Mapping_keys_dest safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])+

fun init_mmsaux :: "args \<Rightarrow> 'a mmsaux" where
  "init_mmsaux args = (0, 0, join_mask (args_n args) (args_L args),
  join_mask (args_n args) (args_R args), empty_queue, empty_queue, Mapping.empty, Mapping.empty)"

lemma valid_init_mmsaux: "L \<subseteq> R \<Longrightarrow> valid_mmsaux (init_args I n L R b) 0
  (init_mmsaux (init_args I n L R b)) []"
  by (auto simp add: init_args_def empty_queue_rep ts_tuple_rel_def join_mask_def
      Mapping.lookup_empty safe_max_def table_def)

abbreviation "filter_cond X' ts t' \<equiv> (\<lambda>as _. \<not> (as \<in> X' \<and> Mapping.lookup ts as = Some t'))"

lemma dropWhile_filter:
  "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>(t, X). enat (nt - t) > c) xs = filter (\<lambda>(t, X). enat (nt - t) \<le> c) xs"
  by (induction xs) (auto 0 3 intro!: filter_id_conv[THEN iffD2, symmetric] elim: order.trans[rotated])

lemma dropWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>(t, X). nt - t \<ge> c) xs = filter (\<lambda>(t, X). nt - t < c) xs"
  by (induction xs) (auto 0 3 intro!: filter_id_conv[THEN iffD2, symmetric] elim: order.trans[rotated])

lemma dropWhile_filter'':
  "sorted xs \<Longrightarrow> \<forall>t \<in> set xs. t \<le> nt \<Longrightarrow>
  dropWhile (\<lambda>t. enat (nt - t) > c) xs = filter (\<lambda>t. enat (nt - t) \<le> c) xs"
  by (induction xs) (auto 0 3 intro!: filter_id_conv[THEN iffD2, symmetric] elim: order.trans[rotated])

lemma takeWhile_filter:
  "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>(t, X). enat (nt - t) > c) xs = filter (\<lambda>(t, X). enat (nt - t) > c) xs"
  by (induction xs) (auto 0 3 simp: less_enat_iff intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma takeWhile_filter':
  fixes nt :: nat
  shows "sorted (map fst xs) \<Longrightarrow> \<forall>t \<in> fst ` set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>(t, X). nt - t \<ge> c) xs = filter (\<lambda>(t, X). nt - t \<ge> c) xs"
  by (induction xs) (auto 0 3 simp: less_enat_iff intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma takeWhile_filter'':
  "sorted xs \<Longrightarrow> \<forall>t \<in> set xs. t \<le> nt \<Longrightarrow>
  takeWhile (\<lambda>t. enat (nt - t) > c) xs = filter (\<lambda>t. enat (nt - t) > c) xs"
  by (induction xs) (auto 0 3 simp: less_enat_iff intro!: filter_empty_conv[THEN iffD2, symmetric])

lemma fold_Mapping_filter_None: "Mapping.lookup ts as = None \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter
  (filter_cond X ts t) ts) ds ts) as = None"
  by (induction ds arbitrary: ts) (auto simp add: Mapping.lookup_filter)

lemma Mapping_lookup_filter_Some_P: "Mapping.lookup (Mapping.filter P m) k = Some v \<Longrightarrow> P k v"
  by (auto simp add: Mapping.lookup_filter split: option.splits if_splits)

lemma Mapping_lookup_filter_None: "(\<And>v. \<not>P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = None"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_Some: "(\<And>v. P k v) \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma Mapping_lookup_filter_not_None: "Mapping.lookup (Mapping.filter P m) k \<noteq> None \<Longrightarrow>
  Mapping.lookup (Mapping.filter P m) k = Mapping.lookup m k"
  by (auto simp add: Mapping.lookup_filter split: option.splits)

lemma fold_Mapping_filter_Some_None: "Mapping.lookup ts as = Some t \<Longrightarrow>
  as \<in> X \<Longrightarrow> (t, X) \<in> set ds \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond X ts t) ts) ds ts) as = None"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using fold_Mapping_filter_None[of "Mapping.filter (filter_cond X' ts t') ts" as ds]
        Mapping_lookup_filter_not_None[of "filter_cond X' ts t'" ts as]
        fold_Mapping_filter_None[OF Mapping_lookup_filter_None, of _ as ds ts]
      by (cases "Mapping.lookup (Mapping.filter (filter_cond X' ts t') ts) as = None") auto
  qed
qed simp

lemma fold_Mapping_filter_Some_Some: "Mapping.lookup ts as = Some t \<Longrightarrow>
  (\<And>X. (t, X) \<in> set ds \<Longrightarrow> as \<notin> X) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) ts. Mapping.filter (filter_cond X ts t) ts) ds ts) as = Some t"
proof (induction ds arbitrary: ts)
  case (Cons a ds)
  then show ?case
  proof (cases a)
    case (Pair t' X')
    with Cons show ?thesis
      using Mapping_lookup_filter_Some[of "filter_cond X' ts t'" as ts] by auto
  qed
qed simp

fun shift_end :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "shift_end args nt (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let I = args_ivl args;
    data_prev' = dropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_prev;
    (data_in, discard) = takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in;
    tuple_in = fold (\<lambda>(t, X) tuple_in. Mapping.filter
      (filter_cond X tuple_in t) tuple_in) discard tuple_in in
    (t, gc, maskL, maskR, data_prev', data_in, tuple_in, tuple_since))"

lemma valid_shift_end_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args cur (shift_end args nt
    (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (filter (\<lambda>(t, rel). enat (nt - t) \<le> right (args_ivl args)) auxlist)"
proof -
  define I where "I = args_ivl args"
  define data_in' where "data_in' \<equiv>
    fst (takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in)"
  define data_prev' where "data_prev' \<equiv>
    dropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_prev"
  define discard where "discard \<equiv>
    snd (takedropWhile_queue (\<lambda>(t, X). enat (nt - t) > right I) data_in)"
  define tuple_in' where "tuple_in' \<equiv> fold (\<lambda>(t, X) tuple_in. Mapping.filter
    (\<lambda>as _. \<not>(as \<in> X \<and> Mapping.lookup tuple_in as = Some t)) tuple_in) discard tuple_in"
  have tuple_in_Some_None: "\<And>as t X. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    as \<in> X \<Longrightarrow> (t, X) \<in> set discard \<Longrightarrow> Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_Some_None unfolding tuple_in'_def by fastforce
  have tuple_in_Some_Some: "\<And>as t. Mapping.lookup tuple_in as = Some t \<Longrightarrow>
    (\<And>X. (t, X) \<in> set discard \<Longrightarrow> as \<notin> X) \<Longrightarrow> Mapping.lookup tuple_in' as = Some t"
    using fold_Mapping_filter_Some_Some unfolding tuple_in'_def by fastforce
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    using fold_Mapping_filter_None unfolding tuple_in'_def by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_Some_None tuple_in_Some_Some tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    using valid_before nt_mono by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    using valid_before nt_mono by auto
  have lin_data_in': "linearize data_in' =
    filter (\<lambda>(t, X). enat (nt - t) \<le> right I) (linearize data_in)"
    unfolding data_in'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F1] ..
  then have set_lin_data_in': "set (linearize data_in') \<subseteq> set (linearize data_in)"
    by auto
  have "sorted (map fst (linearize data_in))"
    using valid_before by auto
  then have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using sorted_filter by auto
  have discard_alt: "discard = filter (\<lambda>(t, X). enat (nt - t) > right I) (linearize data_in)"
    unfolding discard_def[unfolded takedropWhile_queue_snd] takeWhile_filter[OF F1] ..
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). enat (nt - t) \<le> right I) (linearize data_prev)"
    unfolding data_prev'_def[unfolded takedropWhile_queue_fst] dropWhile_queue_rep
      dropWhile_filter[OF F2] ..
  have "sorted (map fst (linearize data_prev))"
    using valid_before by auto
  then have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter by auto
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')). valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before by (auto dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using ts_tuple_rel_mono[OF set_lin_data_in'] by auto
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "\<exists>X. (t, X) \<in> set discard \<and> as \<in> X")
        case True
        then obtain X where X_def: "(t, X) \<in> set discard" "as \<in> X"
          by auto
        have "enat (nt - t) > right I"
          using X_def(1) unfolding discard_alt by simp
        moreover have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        ultimately have "{tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas} = {}"
          unfolding lin_data_in' using ts_tuple_rel_set_filter
          by (auto simp add: ts_tuple_rel_def)
             (meson diff_le_mono2 enat_ord_simps(2) leD le_less_trans)
        then show ?thesis
          unfolding tuple_in_Some_None[OF Some X_def(2,1)]
          using iffD2[OF safe_max_empty, symmetric] by blast
      next
        case False
        then have lookup_Some: "Mapping.lookup tuple_in' as = Some t"
          using tuple_in_Some_Some[OF Some] by auto
        have t_as: "(t, as) \<in> ts_tuple_rel (set (linearize data_in))"
          "valid_tuple tuple_since (t, as)"
          using valid_before Some by (auto dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then obtain X where X_def: "as \<in> X" "(t, X) \<in> set (linearize data_in)"
          by (auto simp add: ts_tuple_rel_def)
        have "(t, X) \<in> set (linearize data_in')"
          using X_def False unfolding discard_alt lin_data_in' by auto
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}"
          using t_as(2) X_def(1) by (auto simp add: ts_tuple_rel_def image_iff)
        have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel, OF _ t_in_fst]
            ts_tuple_rel_mono[OF set_lin_data_in'] by fastforce
        then show ?thesis
          unfolding lookup_Some using t_in_fst by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_in: "table (args_n args) (args_R args) (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before by (auto simp add: table_def)
  have "ts_tuple_rel (set auxlist) =
    {as \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since as}"
    using valid_before by auto
  then have "ts_tuple_rel (set (filter (\<lambda>(t, rel). enat (nt - t) \<le> right I) auxlist)) =
    {as \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since as}"
    unfolding lin_data_prev' lin_data_in' ts_tuple_rel_Un ts_tuple_rel_filter by auto
  then show ?thesis
    using data_prev'_def data_in'_def tuple_in'_def discard_def valid_before nt_mono
      sorted_lin_data_prev' sorted_lin_data_in' lin_data_prev' lin_data_in' lookup_tuple_in'
      table_in unfolding I_def
    by (auto simp only: valid_mmsaux.simps shift_end.simps Let_def split: prod.splits) auto
      (* takes long *)
qed

lemma valid_shift_end_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args cur (shift_end args nt aux)
  (filter (\<lambda>(t, rel). enat (nt - t) \<le> right (args_ivl args)) auxlist)"
  using valid_shift_end_mmsaux_unfolded by (cases aux) fast

setup_lifting type_definition_mapping

lift_definition upd_set :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m f X a. if a \<in> X then Some (f a) else m a" .

lemma Mapping_lookup_upd_set: "Mapping.lookup (upd_set m f X) a =
  (if a \<in> X then Some (f a) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set.rep_eq)

lemma Mapping_upd_set_keys: "Mapping.keys (upd_set m f X) = Mapping.keys m \<union> X"
  by (auto simp add: Mapping_lookup_upd_set dest!: Mapping_keys_dest intro: Mapping_keys_intro)

lift_definition upd_keys_on :: "('a, 'b) mapping \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow>
  ('a, 'b) mapping" is
  "\<lambda>m f X a. case Mapping.lookup m a of Some b \<Rightarrow> Some (if a \<in> X then f a b else b)
  | None \<Rightarrow> None" .

lemma Mapping_lookup_upd_keys_on: "Mapping.lookup (upd_keys_on m f X) a =
  (case Mapping.lookup m a of Some b \<Rightarrow> Some (if a \<in> X then f a b else b) | None \<Rightarrow> None)"
  by (simp add: Mapping.lookup.rep_eq upd_keys_on.rep_eq)

lemma Mapping_upd_keys_sub: "Mapping.keys (upd_keys_on m f X) = Mapping.keys m"
  by (auto simp add: Mapping_lookup_upd_keys_on dest!: Mapping_keys_dest intro: Mapping_keys_intro
      split: option.splits)

lemma fold_append_queue_rep: "linearize (fold (\<lambda>x q. append_queue x q) xs q) = linearize q @ xs"
  by (induction xs arbitrary: q) (auto simp add: append_queue_rep)

lemma Max_Un_absorb:
  assumes "finite X" "X \<noteq> {}" "finite Y" "(\<And>x y. y \<in> Y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<le> x)"
  shows "Max (X \<union> Y) = Max X"
proof -
  have Max_X_in_X: "Max X \<in> X"
    using Max_in[OF assms(1,2)] .
  have Max_X_in_XY: "Max X \<in> X \<union> Y"
    using Max_in[OF assms(1,2)] by auto
  have fin: "finite (X \<union> Y)"
    using assms(1,3) by auto
  have Y_le_Max_X: "\<And>y. y \<in> Y \<Longrightarrow> y \<le> Max X"
    using assms(4)[OF _ Max_X_in_X] .
  have XY_le_Max_X: "\<And>y. y \<in> X \<union> Y \<Longrightarrow> y \<le> Max X"
    using Max_ge[OF assms(1)] Y_le_Max_X by auto
  show ?thesis
    using Max_eqI[OF fin XY_le_Max_X Max_X_in_XY] by auto
qed

lemma Mapping_lookup_fold_upd_set_idle: "{(t, X) \<in> set xs. as \<in> Z X t} = {} \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as = Mapping.lookup m as"
proof (induction xs arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain x1 x2 where "x = (x1, x2)" by (cases x)
  have "Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs (upd_set m (\<lambda>_. x1) (Z x2 x1))) as =
    Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as"
    using Cons by auto
  also have "Mapping.lookup (upd_set m (\<lambda>_. x1) (Z x2 x1)) as = Mapping.lookup m as"
    using Cons.prems by (auto simp: \<open>x = (x1, x2)\<close> Mapping_lookup_upd_set)
  finally show ?case by (simp add: \<open>x = (x1, x2)\<close>)
qed

lemma Mapping_lookup_fold_upd_set_max: "{(t, X) \<in> set xs. as \<in> Z X t} \<noteq> {} \<Longrightarrow>
  sorted (map fst xs) \<Longrightarrow>
  Mapping.lookup (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z X t)) xs m) as =
  Some (Max (fst ` {(t, X) \<in> set xs. as \<in> Z X t}))"
proof (induction xs arbitrary: m)
  case (Cons x xs)
  obtain t X where tX_def: "x = (t, X)"
    by (cases x) auto
  have set_fst_eq: "(fst ` {(t, X). (t, X) \<in> set (x # xs) \<and> as \<in> Z X t}) =
    ((fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t}) \<union>
    (if as \<in> Z X t then {t} else {}))"
    using image_iff by (fastforce simp add: tX_def split: if_splits)
  show ?case
  proof (cases "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<noteq> {}")
    case True
    have "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} \<subseteq> set xs"
      by auto
    then have fin: "finite (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      by (simp add: finite_subset)
    have "Max (insert t (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})) =
      Max (fst ` {(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t})"
      using Max_Un_absorb[OF fin, of "{t}"] True Cons(3) tX_def by auto
    then show ?thesis
      using Cons True unfolding set_fst_eq by auto
  next
    case False
    then have empty: "{(t, X). (t, X) \<in> set xs \<and> as \<in> Z X t} = {}"
      by auto
    then have "as \<in> Z X t"
      using Cons(2) set_fst_eq by fastforce
    then show ?thesis
      using Mapping_lookup_fold_upd_set_idle[OF empty] unfolding set_fst_eq empty
      by (auto simp add: Mapping_lookup_upd_set tX_def)
  qed
qed simp

fun add_new_ts_mmsaux' :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux' args nt (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let I = args_ivl args;
    (data_prev, move) = takedropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev;
    data_in = fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in) move data_in;
    tuple_in = fold (\<lambda>(t, X) tuple_in. upd_set tuple_in (\<lambda>_. t)
      {as \<in> X. valid_tuple tuple_since (t, as)}) move tuple_in in
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))"

lemma Mapping_keys_fold_upd_set: "k \<in> Mapping.keys (fold (\<lambda>(t, X) m. upd_set m (\<lambda>_. t) (Z t X))
  xs m) \<Longrightarrow> k \<in> Mapping.keys m \<or> (\<exists>(t, X) \<in> set xs. k \<in> Z t X)"
  by (induction xs arbitrary: m) (fastforce simp add: Mapping_upd_set_keys)+

lemma valid_add_new_ts_mmsaux'_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and nt_mono: "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux' args nt
    (ot, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)) auxlist"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define data_prev' where "data_prev' \<equiv> dropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev"
  define move where "move \<equiv> takeWhile (\<lambda>(t, X). nt - t \<ge> left I) (linearize data_prev)"
  define data_in' where "data_in' \<equiv> fold (\<lambda>(t, X) data_in. append_queue (t, X) data_in)
    move data_in"
  define tuple_in' where "tuple_in' \<equiv> fold (\<lambda>(t, X) tuple_in. upd_set tuple_in (\<lambda>_. t)
      {as \<in> X. valid_tuple tuple_since (t, as)}) move tuple_in"
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in \<or>
    (\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)})"
    using Mapping_keys_fold_upd_set[of _ "\<lambda>t X. {as \<in> X. valid_tuple tuple_since (t, as)}"]
    by (auto simp add: tuple_in'_def)
  have F1: "sorted (map fst (linearize data_in))" "\<forall>t \<in> fst ` set (linearize data_in). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_in). t \<le> ot \<and> ot - t \<ge> left I"
    using valid_before nt_mono unfolding I_def by auto
  have F2: "sorted (map fst (linearize data_prev))" "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> nt"
    "\<forall>t \<in> fst ` set (linearize data_prev). t \<le> ot \<and> ot - t < left I"
    using valid_before nt_mono unfolding I_def by auto
  have lin_data_prev': "linearize data_prev' =
    filter (\<lambda>(t, X). nt - t < left I) (linearize data_prev)"
    unfolding data_prev'_def dropWhile_queue_rep dropWhile_filter'[OF F2(1,2)] ..
  have move_filter: "move = filter (\<lambda>(t, X). nt - t \<ge> left I) (linearize data_prev)"
    unfolding move_def takeWhile_filter'[OF F2(1,2)] ..
  then have sorted_move: "sorted (map fst move)"
    using sorted_filter F2 by auto
  have "\<forall>t\<in>fst ` set move. t \<le> ot \<and> ot - t < left I"
    using move_filter F2(3) set_filter by auto
  then have fst_set_before: "\<forall>t\<in>fst ` set (linearize data_in). \<forall>t'\<in>fst ` set move. t \<le> t'"
    using F1(3) by fastforce
  then have fst_ts_tuple_rel_before: "\<forall>t\<in>fst ` ts_tuple_rel (set (linearize data_in)).
    \<forall>t'\<in>fst ` ts_tuple_rel (set move). t \<le> t'"
    by (fastforce simp add: ts_tuple_rel_def)
  have sorted_lin_data_prev': "sorted (map fst (linearize data_prev'))"
    unfolding lin_data_prev' using sorted_filter F2 by auto
  have lin_data_in': "linearize data_in' = linearize data_in @ move"
    unfolding data_in'_def using fold_append_queue_rep by fastforce
  have sorted_lin_data_in': "sorted (map fst (linearize data_in'))"
    unfolding lin_data_in' using F1(1) sorted_move fst_set_before by (simp add: sorted_append)
  have set_lin_prev'_in': "set (linearize data_prev') \<union> set (linearize data_in') =
    set (linearize data_prev) \<union> set (linearize data_in)"
    using lin_data_prev' lin_data_in' move_filter by auto
  have ts_tuple_rel': "ts_tuple_rel (set auxlist) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev') \<union> set (linearize data_in')).
    valid_tuple tuple_since tas}"
    unfolding set_lin_prev'_in' using valid_before by auto
  have lookup': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in')).
    valid_tuple tuple_since tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since tas \<and> as = snd tas})"
    proof (cases "{(t, X) \<in> set move. as \<in> X \<and> valid_tuple tuple_since (t, as)} = {}")
      case True
      have move_absorb: "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        {tas \<in> ts_tuple_rel (set (linearize data_in @ move)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        using True by (auto simp add: ts_tuple_rel_def)
      have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        using valid_before by auto
      then have "Mapping.lookup tuple_in as =
        safe_max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding lin_data_in' move_absorb .
      then show ?thesis
        using Mapping_lookup_fold_upd_set_idle[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}"] True
        unfolding tuple_in'_def by auto
    next
      case False
      have split: "fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas} \<union>
        fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
        unfolding lin_data_in' set_append ts_tuple_rel_Un by auto
      have max_eq: "Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}) =
        Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since tas \<and> as = snd tas})"
        unfolding split using False fst_ts_tuple_rel_before
        by (fastforce simp add: ts_tuple_rel_def
            intro!: Max_Un_absorb[OF finite_fst_ts_tuple_rel _ finite_fst_ts_tuple_rel, symmetric])
      have "fst ` {(t, X). (t, X) \<in> set move \<and> as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}} =
        fst ` {tas \<in> ts_tuple_rel (set move). valid_tuple tuple_since tas \<and> as = snd tas}"
        by (auto simp add: ts_tuple_rel_def image_iff)
      then have "Mapping.lookup tuple_in' as = Some (Max (fst ` {tas \<in> ts_tuple_rel (set move).
        valid_tuple tuple_since tas \<and> as = snd tas}))"
        using Mapping_lookup_fold_upd_set_max[of "move" as
          "\<lambda>X t. {as \<in> X. valid_tuple tuple_since (t, as)}", OF _ sorted_move] False
        unfolding tuple_in'_def by (auto simp add: ts_tuple_rel_def)
      then show ?thesis
        unfolding max_eq using False
        by (auto simp add: safe_max_def lin_data_in' ts_tuple_rel_def)
    qed
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
  proof -
    {
      fix as
      assume assm: "as \<in> Mapping.keys tuple_in'"
      have "wf_tuple n R as"
        using tuple_in'_keys[OF assm]
      proof (rule disjE)
        assume "as \<in> Mapping.keys tuple_in"
        then show "wf_tuple n R as"
          using valid_before by (auto simp add: table_def n_def R_def)
      next
        assume "\<exists>(t, X)\<in>set move. as \<in> {as \<in> X. valid_tuple tuple_since (t, as)}"
        then obtain t X where tX_def: "(t, X) \<in> set move" "as \<in> X"
          by auto
        then have "as \<in> \<Union>(snd ` set (linearize data_prev))"
          unfolding move_def using set_takeWhileD by force
        then show "wf_tuple n R as"
          using valid_before by (auto simp add: n_def R_def)
      qed
    }
    then show ?thesis
      by (auto simp add: table_def)
  qed
  have data_prev'_move: "(data_prev', move) =
    takedropWhile_queue (\<lambda>(t, X). nt - t \<ge> left I) data_prev"
    using takedropWhile_queue_fst takedropWhile_queue_snd data_prev'_def move_def
    by (metis surjective_pairing)
  moreover have "valid_mmsaux args nt (nt, gc, maskL, maskR, data_prev', data_in',
    tuple_in', tuple_since) auxlist"
    using lin_data_prev' sorted_lin_data_prev' lin_data_in' move_filter sorted_lin_data_in'
      nt_mono valid_before ts_tuple_rel' lookup' table_in' unfolding I_def
    by (auto simp only: valid_mmsaux.simps Let_def n_def R_def split: option.splits) auto
      (* takes long *)
  ultimately show ?thesis
    by (auto simp only: add_new_ts_mmsaux'.simps Let_def data_in'_def tuple_in'_def I_def
        split: prod.splits)
qed

lemma valid_add_new_ts_mmsaux': "valid_mmsaux args cur aux auxlist \<Longrightarrow> nt \<ge> cur \<Longrightarrow>
  valid_mmsaux args nt (add_new_ts_mmsaux' args nt aux) auxlist"
  using valid_add_new_ts_mmsaux'_unfolded by (cases aux) fast

definition add_new_ts_mmsaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_ts_mmsaux args nt aux = add_new_ts_mmsaux' args nt (shift_end args nt aux)"

lemma valid_add_new_ts_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmsaux args nt (add_new_ts_mmsaux args nt aux)
    (filter (\<lambda>(t, rel). enat (nt - t) \<le> right (args_ivl args)) auxlist)"
  using valid_add_new_ts_mmsaux'[OF valid_shift_end_mmsaux[OF assms] assms(2)]
  unfolding add_new_ts_mmsaux_def .

fun join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let pos = args_pos args in
    (if maskL = maskR then
      (let tuple_in = Mapping.filter (join_filter_cond pos X) tuple_in;
      tuple_since = Mapping.filter (join_filter_cond pos X) tuple_since in
      (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    else if (\<forall>i \<in> set maskL. \<not>i) then
      (let nones = replicate (length maskL) None;
      take_all = (pos \<longleftrightarrow> nones \<in> X);
      tuple_in = (if take_all then tuple_in else Mapping.empty);
      tuple_since = (if take_all then tuple_since else Mapping.empty) in
      (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    else
      (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
      tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
      (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))))"

fun join_mmsaux_abs :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "join_mmsaux_abs args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let pos = args_pos args in
    (let tuple_in = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in;
    tuple_since = Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since in
    (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)))"

lemma Mapping_filter_cong:
  assumes cong: "(\<And>k v. k \<in> Mapping.keys m \<Longrightarrow> f k v = f' k v)"
  shows "Mapping.filter f m = Mapping.filter f' m"
proof -
  have "\<And>k. Mapping.lookup (Mapping.filter f m) k = Mapping.lookup (Mapping.filter f' m) k"
    using cong
    by (fastforce simp add: Mapping.lookup_filter intro: Mapping_keys_intro split: option.splits)
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma join_mmsaux_abs_eq:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_left: "table (args_n args) (args_L args) X"
  shows "join_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    join_mmsaux_abs args X (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since)"
proof (cases "maskL = maskR")
  case True
  define n where "n = args_n args"
  define L where "L = args_L args"
  define pos where "pos = args_pos args"
  have keys_wf_in: "\<And>as. as \<in> Mapping.keys tuple_in \<Longrightarrow> wf_tuple n L as"
    using wf_tuple_change_base valid_before True by (fastforce simp add: table_def n_def L_def)
  have cong_in: "\<And>as n. as \<in> Mapping.keys tuple_in \<Longrightarrow>
    proj_tuple_in_join pos maskL as X \<longleftrightarrow> join_cond pos X as"
    using proj_tuple_in_join_mask_idle[OF keys_wf_in] valid_before
    by (auto simp only: valid_mmsaux.simps n_def L_def pos_def)
  have keys_wf_since: "\<And>as. as \<in> Mapping.keys tuple_since \<Longrightarrow> wf_tuple n L as"
    using wf_tuple_change_base valid_before True by (fastforce simp add: table_def n_def L_def)
  have cong_since: "\<And>as n. as \<in> Mapping.keys tuple_since \<Longrightarrow>
    proj_tuple_in_join pos maskL as X \<longleftrightarrow> join_cond pos X as"
    using proj_tuple_in_join_mask_idle[OF keys_wf_since] valid_before
    by (auto simp only: valid_mmsaux.simps n_def L_def pos_def)
  show ?thesis
    using True Mapping_filter_cong[OF cong_in, of tuple_in "\<lambda>k _. k"]
      Mapping_filter_cong[OF cong_since, of tuple_since "\<lambda>k _. k"]
    by (auto simp add: pos_def)
next
  case False
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  from False show ?thesis
  proof (cases "\<forall>i \<in> set maskL. \<not>i")
    case True
    have length_maskL: "length maskL = n"
      using valid_before by (auto simp add: join_mask_def n_def)
    have proj_rep: "\<And>as. wf_tuple n R as \<Longrightarrow> proj_tuple maskL as = replicate (length maskL) None"
      using True proj_tuple_replicate by (force simp add: length_maskL wf_tuple_def)
    have keys_wf_in: "\<And>as. as \<in> Mapping.keys tuple_in \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def n_def R_def)
    have keys_wf_since: "\<And>as. as \<in> Mapping.keys tuple_since \<Longrightarrow> wf_tuple n R as"
      using valid_before by (auto simp add: table_def n_def R_def)
    have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_in) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_in else Mapping.empty) as"
      using proj_rep[OF keys_wf_in]
      by (auto simp add: Mapping.lookup_filter Mapping.lookup_empty proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    moreover have "\<And>as. Mapping.lookup (Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X)
      tuple_since) as = Mapping.lookup (if (pos \<longleftrightarrow> replicate (length maskL) None \<in> X)
      then tuple_since else Mapping.empty) as"
      using proj_rep[OF keys_wf_since]
      by (auto simp add: Mapping.lookup_filter Mapping.lookup_empty proj_tuple_in_join_def
          Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using False True by (auto simp add: mapping_eqI Let_def pos_def)
  qed (auto simp add: Let_def)
qed

lemma valid_join_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_left': "table (args_n args) (args_L args) X"
  shows "valid_mmsaux args cur
    (join_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  note table_left = table_left'[unfolded n_def[symmetric] L_def[symmetric]]
  define tuple_in' where "tuple_in' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_in"
  define tuple_since' where "tuple_since' \<equiv>
    Mapping.filter (\<lambda>as _. proj_tuple_in_join pos maskL as X) tuple_since"
  have tuple_in_None_None: "\<And>as. Mapping.lookup tuple_in as = None \<Longrightarrow>
    Mapping.lookup tuple_in' as = None"
    unfolding tuple_in'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_in'_keys: "\<And>as. as \<in> Mapping.keys tuple_in' \<Longrightarrow> as \<in> Mapping.keys tuple_in"
    using tuple_in_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  have ts_tuple_rel': "ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
    then obtain t as Z where tas_def: "tas = (t, as)" "as \<in> join Z pos X" "(t, Z) \<in> set auxlist"
      "(t, join Z pos X) \<in> set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist)"
      by (fastforce simp add: ts_tuple_rel_def)
    from tas_def(3) have table_Z: "table n R Z"
      using valid_before by (auto simp add: n_def R_def)
    have proj: "as \<in> Z" "proj_tuple_in_join pos maskL as X"
      using tas_def(2) join_sub[OF _ table_left table_Z] valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    then have "(t, as) \<in> ts_tuple_rel (set (auxlist))"
      using tas_def(3) by (auto simp add: ts_tuple_rel_def)
    then have tas_in: "(t, as) \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in))" "valid_tuple tuple_since (t, as)"
      using valid_before by auto
    then obtain t' where t'_def: "Mapping.lookup tuple_since as = Some t'" "t \<ge> t'"
      by (auto simp add: valid_tuple_def split: option.splits)
    then have valid_tuple_since': "valid_tuple tuple_since' (t, as)"
      using proj(2)
      by (auto simp add: tuple_since'_def Mapping_lookup_filter_Some valid_tuple_def)
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
      valid_tuple tuple_since' tas}"
      using tas_in valid_tuple_since' unfolding tas_def(1)[symmetric] by auto
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel
      (set (linearize data_prev) \<union> set (linearize data_in)). valid_tuple tuple_since' tas}"
    then obtain t as where tas_def: "tas = (t, as)" "valid_tuple tuple_since' (t, as)"
      by (auto simp add: ts_tuple_rel_def)
    from tas_def(2) have "valid_tuple tuple_since (t, as)"
      unfolding tuple_since'_def using Mapping_lookup_filter_not_None
      by (force simp add: valid_tuple_def split: option.splits)
    then have "(t, as) \<in> ts_tuple_rel (set auxlist)"
      using valid_before assm tas_def(1) by auto
    then obtain Z where Z_def: "as \<in> Z" "(t, Z) \<in> set auxlist"
      by (auto simp add: ts_tuple_rel_def)
    then have table_Z: "table n R Z"
      using valid_before by (auto simp add: n_def R_def)
    from tas_def(2) have "proj_tuple_in_join pos maskL as X"
      unfolding tuple_since'_def using Mapping_lookup_filter_Some_P
      by (fastforce simp add: valid_tuple_def split: option.splits)
    then have as_in_join: "as \<in> join Z pos X"
      using join_sub[OF _ table_left table_Z] Z_def(1) valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    then show "tas \<in> ts_tuple_rel (set (map (\<lambda>(t, rel). (t, join rel pos X)) auxlist))"
      using Z_def unfolding tas_def(1) by (auto simp add: ts_tuple_rel_def)
  qed
  have lookup_tuple_in': "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
  proof -
    fix as
    show "Mapping.lookup tuple_in' as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof (cases "Mapping.lookup tuple_in as")
      case None
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas} = {}"
        using valid_before by (auto dest!: safe_max_empty_dest)
      then have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas} = {}"
        using Mapping_lookup_filter_not_None
        by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
      then show ?thesis
        unfolding tuple_in_None_None[OF None] using iffD2[OF safe_max_empty, symmetric] by blast
    next
      case (Some t)
      show ?thesis
      proof (cases "proj_tuple_in_join pos maskL as X")
        case True
        then have lookup_tuple_in': "Mapping.lookup tuple_in' as = Some t"
          using Some unfolding tuple_in'_def by (simp add: Mapping_lookup_filter_Some)
        have "(t, as) \<in> ts_tuple_rel (set (linearize data_in))" "valid_tuple tuple_since (t, as)"
          using valid_before Some by (auto dest: safe_max_Some_dest_in[OF finite_fst_ts_tuple_rel])
        then have t_in_fst: "t \<in> fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using True by (auto simp add: image_iff valid_tuple_def tuple_since'_def
            Mapping_lookup_filter_Some split: option.splits)
        have "\<And>t'. valid_tuple tuple_since' (t', as) \<Longrightarrow> valid_tuple tuple_since (t', as)"
          using Mapping_lookup_filter_not_None
          by (fastforce simp add: valid_tuple_def tuple_since'_def split: option.splits)
        then have "\<And>t'. (t', as) \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
          valid_tuple tuple_since' (t', as) \<Longrightarrow> t' \<le> t"
          using valid_before Some safe_max_Some_dest_le[OF finite_fst_ts_tuple_rel]
          by (fastforce simp add: image_iff)
        then have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since' tas \<and> as = snd tas}) = t"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of "linearize data_in"],
            OF _ t_in_fst] by fastforce
        then show ?thesis
          unfolding lookup_tuple_in' using t_in_fst by (auto simp add: safe_max_def)
      next
        case False
        then have lookup_tuple': "Mapping.lookup tuple_in' as = None"
          "Mapping.lookup tuple_since' as = None"
          unfolding tuple_in'_def tuple_since'_def
          by (auto simp add: Mapping_lookup_filter_None)
        then have "\<And>tas. \<not>(valid_tuple tuple_since' tas \<and> as = snd tas)"
          by (auto simp add: valid_tuple_def split: option.splits)
        then show ?thesis
          unfolding lookup_tuple' by (auto simp add: safe_max_def)
      qed
    qed
  qed
  have table_join': "\<And>t ys. (t, ys) \<in> set auxlist \<Longrightarrow> table n R (join ys pos X)"
  proof -
    fix t ys
    assume "(t, ys) \<in> set auxlist"
    then have table_ys: "table n R ys"
      using valid_before
      by (auto simp add: n_def L_def R_def pos_def)
    show "table n R (join ys pos X)"
      using join_table[OF table_ys table_left, of pos R] valid_before
      by (auto simp add: n_def L_def R_def pos_def)
  qed
  have table_in': "table n R (Mapping.keys tuple_in')"
    using tuple_in'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using tuple_since'_keys valid_before
    by (auto simp add: n_def L_def R_def pos_def table_def)
  show ?thesis
    unfolding join_mmsaux_abs_eq[OF valid_before table_left']
    using valid_before ts_tuple_rel' lookup_tuple_in' tuple_in'_def tuple_since'_def table_join'
      Mapping_filter_keys[of tuple_since "\<lambda>as. case as of Some t \<Rightarrow> t \<le> nt"]
      table_in' table_since' by (auto simp add: n_def L_def R_def pos_def table_def Let_def)
qed

lemma valid_join_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  table (args_n args) (args_L args) X \<Longrightarrow> valid_mmsaux args cur
  (join_mmsaux args X aux) (map (\<lambda>(t, rel). (t, join rel (args_pos args) X)) auxlist)"
  using valid_join_mmsaux_unfolded by (cases aux) fast

fun gc_mmsaux :: "'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_mmsaux (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let all_tuples = \<Union>(snd ` (set (linearize data_prev) \<union> set (linearize data_in)));
    tuple_since' = Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since in
    (nt, nt, maskL, maskR, data_prev, data_in, tuple_in, tuple_since'))"

lemma valid_gc_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur (nt, gc, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since) ys"
  shows "valid_mmsaux args cur (gc_mmsaux (nt, gc, maskL, maskR, data_prev, data_in,
    tuple_in, tuple_since)) ys"
proof -
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define all_tuples where "all_tuples \<equiv> \<Union>(snd ` (set (linearize data_prev) \<union>
    set (linearize data_in)))"
  define tuple_since' where "tuple_since' \<equiv> Mapping.filter (\<lambda>as _. as \<in> all_tuples) tuple_since"
  have tuple_since_None_None: "\<And>as. Mapping.lookup tuple_since as = None \<Longrightarrow>
    Mapping.lookup tuple_since' as = None"
    unfolding tuple_since'_def using Mapping_lookup_filter_not_None by fastforce
  have tuple_since'_keys: "\<And>as. as \<in> Mapping.keys tuple_since' \<Longrightarrow> as \<in> Mapping.keys tuple_since"
    using tuple_since_None_None
    by (fastforce intro: Mapping_keys_intro dest: Mapping_keys_dest)
  then have table_since': "table n R (Mapping.keys tuple_since')"
    using valid_before by (auto simp add: table_def n_def R_def)
  have data_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in)) \<Longrightarrow> valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
  proof -
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
    set (linearize data_in))"
    define t where "t \<equiv> fst tas"
    define as where "as \<equiv> snd tas"
    have "as \<in> all_tuples"
      using assm by (force simp add: as_def all_tuples_def ts_tuple_rel_def)
    then have "Mapping.lookup tuple_since' as = Mapping.lookup tuple_since as"
      by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits)
    then show "valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
      by (auto simp add: valid_tuple_def as_def split: option.splits) metis
  qed
  then have data_in_cong: "\<And>tas. tas \<in> ts_tuple_rel (set (linearize data_in)) \<Longrightarrow>
    valid_tuple tuple_since' tas = valid_tuple tuple_since tas"
    by (auto simp add: ts_tuple_rel_Un)
  have "ts_tuple_rel (set ys) =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in)).
    valid_tuple tuple_since' tas}"
    using data_cong valid_before by auto
  moreover have "(\<forall>as. Mapping.lookup tuple_in as = safe_max (fst `
    {tas \<in> ts_tuple_rel (set (linearize data_in)). valid_tuple tuple_since' tas \<and> as = snd tas}))"
    using valid_before by auto (meson data_in_cong)
  moreover have "(\<forall>as \<in> Mapping.keys tuple_since'. case Mapping.lookup tuple_since' as of
    Some t \<Rightarrow> t \<le> nt)"
    using Mapping.keys_filter valid_before
    by (auto simp add: tuple_since'_def Mapping.lookup_filter split: option.splits
        intro!: Mapping_keys_intro dest: Mapping_keys_dest)
  ultimately show ?thesis
    using all_tuples_def tuple_since'_def valid_before table_since'
    by (auto simp add: n_def R_def)
qed

lemma valid_gc_mmsaux: "valid_mmsaux args cur aux ys \<Longrightarrow> valid_mmsaux args cur (gc_mmsaux aux) ys"
  using valid_gc_mmsaux_unfolded by (cases aux) fast

fun gc_join_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "gc_join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (if enat (t - gc) > right (args_ivl args) then join_mmsaux args X (gc_mmsaux (t, gc, maskL, maskR,
      data_prev, data_in, tuple_in, tuple_since))
    else join_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))"

lemma gc_join_mmsaux_alt: "gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 (gc_mmsaux aux) \<or>
  gc_join_mmsaux args rel1 aux = join_mmsaux args rel1 aux"
  by (cases aux) (auto simp only: gc_join_mmsaux.simps split: if_splits)

lemma valid_gc_join_mmsaux:
  assumes "valid_mmsaux args cur aux auxlist" "table (args_n args) (args_L args) rel1"
  shows "valid_mmsaux args cur (gc_join_mmsaux args rel1 aux)
    (map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
  using gc_join_mmsaux_alt[of args rel1 aux]
  using valid_join_mmsaux[OF valid_gc_mmsaux[OF assms(1)] assms(2)]
    valid_join_mmsaux[OF assms]
  by auto

fun add_new_table_mmsaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a mmsaux \<Rightarrow> 'a mmsaux" where
  "add_new_table_mmsaux args X (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    (let tuple_since = upd_set tuple_since (\<lambda>_. t) (X - Mapping.keys tuple_since) in
    (if 0 \<ge> left (args_ivl args) then (t, gc, maskL, maskR, data_prev, append_queue (t, X) data_in,
      upd_set tuple_in (\<lambda>_. t) X, tuple_since)
    else (t, gc, maskL, maskR, append_queue (t, X) data_prev, data_in, tuple_in, tuple_since)))"

lemma valid_add_new_table_mmsaux_unfolded:
  assumes valid_before: "valid_mmsaux args cur
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X
    (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since))
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
proof -
  have cur_nt: "cur = nt"
    using valid_before by auto
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  define tuple_in' where "tuple_in' \<equiv> upd_set tuple_in (\<lambda>_. nt) X"
  define tuple_since' where "tuple_since' \<equiv> upd_set tuple_since (\<lambda>_. nt)
    (X - Mapping.keys tuple_since)"
  define data_prev' where "data_prev' \<equiv> append_queue (nt, X) data_prev"
  define data_in' where "data_in' \<equiv> append_queue (nt, X) data_in"
  define auxlist' where "auxlist' \<equiv> (case auxlist of
    [] => [(nt, X)]
    | ((t, y) # ts) \<Rightarrow> if t = nt then (t, y \<union> X) # ts else (nt, X) # auxlist)"
  have table_in': "table n R (Mapping.keys tuple_in')"
    using table_X valid_before
    by (auto simp add: table_def tuple_in'_def Mapping_upd_set_keys n_def R_def)
  have table_since': "table n R (Mapping.keys tuple_since')"
    using table_X valid_before
    by (auto simp add: table_def tuple_since'_def Mapping_upd_set_keys n_def R_def)
  have tuple_since'_keys: "Mapping.keys tuple_since \<subseteq> Mapping.keys tuple_since'"
    using Mapping_upd_set_keys by (fastforce simp add: tuple_since'_def)
  have lin_data_prev': "linearize data_prev' = linearize data_prev @ [(nt, X)]"
    unfolding data_prev'_def append_queue_rep ..
  have wf_data_prev': "\<And>as. as \<in> \<Union>(snd ` (set (linearize data_prev'))) \<Longrightarrow> wf_tuple n R as"
    unfolding lin_data_prev' using table_X valid_before
    by (auto simp add: table_def n_def R_def)
  have lin_data_in': "linearize data_in' = linearize data_in @ [(nt, X)]"
    unfolding data_in'_def append_queue_rep ..
  have table_auxlist': "\<forall>(t, X) \<in> set auxlist'. table n R X"
    using table_X table_Un valid_before
    by (auto simp add: auxlist'_def n_def R_def split: list.splits if_splits)
  have lookup_tuple_since': "\<forall>as \<in> Mapping.keys tuple_since'.
    case Mapping.lookup tuple_since' as of Some t \<Rightarrow> t \<le> nt"
    unfolding tuple_since'_def using valid_before Mapping_lookup_upd_set[of tuple_since]
    by (auto dest: Mapping_keys_dest intro!: Mapping_keys_intro split: if_splits option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    ts_tuple_rel (set auxlist) \<union> ts_tuple_rel {(nt, X)}"
    unfolding auxlist'_def
    using ts_tuple_rel_ext ts_tuple_rel_ext' ts_tuple_rel_ext_Cons ts_tuple_rel_ext_Cons'
    by (fastforce simp: ts_tuple_rel_def split: list.splits if_splits)
  have valid_tuple_nt_X: "\<And>tas. tas \<in> ts_tuple_rel {(nt, X)} \<Longrightarrow> valid_tuple tuple_since' tas"
    using valid_before by (auto simp add: ts_tuple_rel_def valid_tuple_def tuple_since'_def
        Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
  have valid_tuple_mono: "\<And>tas. valid_tuple tuple_since tas \<Longrightarrow> valid_tuple tuple_since' tas"
    by (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
        intro: Mapping_keys_intro split: option.splits)
  have ts_tuple_rel_auxlist': "ts_tuple_rel (set auxlist') =
    {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union> set (linearize data_in) \<union> {(nt, X)}).
    valid_tuple tuple_since' tas}"
  proof (rule set_eqI, rule iffI)
    fix tas
    assume assm: "tas \<in> ts_tuple_rel (set auxlist')"
    show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
      using assm[unfolded ts_tuple_rel_auxlist' ts_tuple_rel_Un]
    proof (rule UnE)
      assume assm: "tas \<in> ts_tuple_rel (set auxlist)"
      then have "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)). valid_tuple tuple_since tas}"
        using valid_before by auto
      then show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm by (auto simp only: ts_tuple_rel_Un intro: valid_tuple_mono)
    next
      assume assm: "tas \<in> ts_tuple_rel {(nt, X)}"
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
        using assm valid_before by (auto simp add: ts_tuple_rel_Un tuple_since'_def
            valid_tuple_def Mapping_lookup_upd_set ts_tuple_rel_def dest: Mapping_keys_dest
            split: option.splits if_splits)
    qed
  next
    fix tas
    assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in) \<union> {(nt, X)}). valid_tuple tuple_since' tas}"
    then have "tas \<in> (ts_tuple_rel (set (linearize data_prev) \<union>
      set (linearize data_in)) - ts_tuple_rel {(nt, X)}) \<union> ts_tuple_rel {(nt, X)}"
      by (auto simp only: ts_tuple_rel_Un)
    then show "tas \<in> ts_tuple_rel (set auxlist')"
    proof (rule UnE)
      assume assm': "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in)) - ts_tuple_rel {(nt, X)}"
      then have tas_in: "tas \<in> ts_tuple_rel (set (linearize data_prev) \<union>
        set (linearize data_in))"
        by (auto simp only: ts_tuple_rel_def)
      obtain t as where tas_def: "tas = (t, as)"
        by (cases tas) auto
      have "t \<in> fst ` (set (linearize data_prev) \<union> set (linearize data_in))"
        using assm' unfolding tas_def by (force simp add: ts_tuple_rel_def)
      then have t_le_nt: "t \<le> nt"
        using valid_before by auto
      have valid_tas: "valid_tuple tuple_since' tas"
        using assm by auto
      have "valid_tuple tuple_since tas"
      proof (cases "as \<in> Mapping.keys tuple_since")
        case True
        then show ?thesis
          using valid_tas tas_def by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set split: option.splits if_splits)
      next
        case False
        then have "t = nt" "as \<in> X"
          using valid_tas t_le_nt unfolding tas_def
          by (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
              intro: Mapping_keys_intro split: option.splits if_splits)
        then have "False"
          using assm' unfolding tas_def ts_tuple_rel_def by (auto simp only: ts_tuple_rel_def)
        then show ?thesis
          by simp
      qed
      then show "tas \<in> ts_tuple_rel (set auxlist')"
        using tas_in valid_before by (auto simp add: ts_tuple_rel_auxlist')
    qed (auto simp only: ts_tuple_rel_auxlist')
  qed
  show ?thesis
  proof (cases "0 \<ge> left I")
    case True
    then have add_def: "add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since) = (nt, gc, maskL, maskR, data_prev, data_in',
      tuple_in', tuple_since')"
      using data_in'_def tuple_in'_def tuple_since'_def unfolding I_def by auto
    have left_I: "left I = 0"
      using True by auto
    have "\<forall>t \<in> fst ` set (linearize data_in'). t \<le> nt \<and> nt - t \<ge> left I"
      using valid_before True by (auto simp add: lin_data_in')
    moreover have "\<And>as. Mapping.lookup tuple_in' as = safe_max (fst `
      {tas \<in> ts_tuple_rel (set (linearize data_in')).
      valid_tuple tuple_since' tas \<and> as = snd tas})"
    proof -
      fix as
      show "Mapping.lookup tuple_in' as = safe_max (fst `
        {tas \<in> ts_tuple_rel (set (linearize data_in')).
        valid_tuple tuple_since' tas \<and> as = snd tas})"
      proof (cases "as \<in> X")
        case True
        have "valid_tuple tuple_since' (nt, as)"
          using True valid_before by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set dest: Mapping_keys_dest split: option.splits)
        moreover have "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          using True by (auto simp add: ts_tuple_rel_def)
        ultimately have nt_in: "nt \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas}"
        proof -
          assume a1: "valid_tuple tuple_since' (nt, as)"
          assume "(nt, as) \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in)))"
          then have "\<exists>p. nt = fst p \<and> p \<in> ts_tuple_rel (insert (nt, X)
            (set (linearize data_in))) \<and> valid_tuple tuple_since' p \<and> as = snd p"
            using a1 by simp
          then show "nt \<in> fst ` {p \<in> ts_tuple_rel (insert (nt, X) (set (linearize data_in))).
            valid_tuple tuple_since' p \<and> as = snd p}"
            by blast
        qed
        moreover have "\<And>t. t \<in> fst ` {tas \<in> ts_tuple_rel (insert (nt, X)
          (set (linearize data_in))). valid_tuple tuple_since' tas \<and> as = snd tas} \<Longrightarrow> t \<le> nt"
          using valid_before by (auto split: option.splits)
            (metis (no_types, lifting) eq_imp_le fst_conv insertE ts_tuple_rel_dest)
        ultimately have "Max (fst ` {tas \<in> ts_tuple_rel (set (linearize data_in)
          \<union> set [(nt, X)]). valid_tuple tuple_since' tas \<and> as = snd tas}) = nt"
          using Max_eqI[OF finite_fst_ts_tuple_rel[of "linearize data_in'"],
              unfolded lin_data_in' set_append] by auto
        then show ?thesis
          using nt_in True
          by (auto simp add: tuple_in'_def Mapping_lookup_upd_set safe_max_def lin_data_in')
      next
        case False
        have "{tas \<in> ts_tuple_rel (set (linearize data_in)).
          valid_tuple tuple_since tas \<and> as = snd tas} =
          {tas \<in> ts_tuple_rel (set (linearize data_in')).
          valid_tuple tuple_since' tas \<and> as = snd tas}"
          using False by (fastforce simp add: lin_data_in' ts_tuple_rel_def valid_tuple_def
              tuple_since'_def Mapping_lookup_upd_set intro: Mapping_keys_intro
              split: option.splits if_splits)
        then show ?thesis
          using valid_before False by (auto simp add: tuple_in'_def Mapping_lookup_upd_set)
      qed
    qed
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_in)"]
        lookup_tuple_since' ts_tuple_rel_auxlist' table_in' table_since'
      unfolding add_def auxlist'_def[symmetric] cur_nt I_def
      by (auto simp only: valid_mmsaux.simps lin_data_in' n_def R_def) auto
  next
    case False
    then have add_def: "add_new_table_mmsaux args X (nt, gc, maskL, maskR, data_prev, data_in,
      tuple_in, tuple_since) = (nt, gc, maskL, maskR, data_prev', data_in,
      tuple_in, tuple_since')"
      using data_prev'_def tuple_since'_def unfolding I_def by auto
    have left_I: "left I > 0"
      using False by auto
    have "\<forall>t \<in> fst ` set (linearize data_prev'). t \<le> nt \<and> nt - t < left I"
      using valid_before False by (auto simp add: lin_data_prev' I_def)
    moreover have "\<And>as. {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since tas \<and> as = snd tas} =
      {tas \<in> ts_tuple_rel (set (linearize data_in)).
      valid_tuple tuple_since' tas \<and> as = snd tas}"
    proof (rule set_eqI, rule iffI)
      fix as tas
      assume assm: "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since' tas \<and> as = snd tas}"
      then obtain t Z where Z_def: "tas = (t, as)" "as \<in> Z" "(t, Z) \<in> set (linearize data_in)"
        "valid_tuple tuple_since' (t, as)"
        by (auto simp add: ts_tuple_rel_def)
      show "tas \<in> {tas \<in> ts_tuple_rel (set (linearize data_in)).
        valid_tuple tuple_since tas \<and> as = snd tas}"
      using assm
      proof (cases "as \<in> Mapping.keys tuple_since")
        case False
        then have "t \<ge> nt"
          using Z_def(4) by (auto simp add: valid_tuple_def tuple_since'_def
              Mapping_lookup_upd_set intro: Mapping_keys_intro split: option.splits if_splits)
        then show ?thesis
          using Z_def(3) valid_before left_I unfolding I_def by auto
      qed (auto simp add: valid_tuple_def tuple_since'_def Mapping_lookup_upd_set
           dest: Mapping_keys_dest split: option.splits)
    qed (auto simp add: Mapping_lookup_upd_set valid_tuple_def tuple_since'_def
         intro: Mapping_keys_intro split: option.splits)
    ultimately show ?thesis
      using assms table_auxlist' sorted_append[of "map fst (linearize data_prev)"]
        False lookup_tuple_since' ts_tuple_rel_auxlist' table_in' table_since' wf_data_prev'
        valid_before
      unfolding add_def auxlist'_def[symmetric] cur_nt I_def
      by (auto simp only: valid_mmsaux.simps lin_data_prev' n_def R_def) fastforce+
        (* takes long *)
  qed
qed

lemma valid_add_new_table_mmsaux:
  assumes valid_before: "valid_mmsaux args cur aux auxlist"
  and table_X: "table (args_n args) (args_R args) X"
  shows "valid_mmsaux args cur (add_new_table_mmsaux args X aux)
    (case auxlist of
      [] => [(cur, X)]
    | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> X) # ts else (cur, X) # auxlist)"
  using valid_add_new_table_mmsaux_unfolded assms
  by (cases aux) fast

lemma foldr_ts_tuple_rel:
  "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {} \<longleftrightarrow>
  (\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t)"
proof (rule iffI)
  assume assm: "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {}"
  then obtain t X where tX_def: "P t" "as \<in> X" "(t, X) \<in> set auxlist"
    by (auto elim!: in_foldr_UnE)
  then show "\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t"
    by (auto simp add: ts_tuple_rel_def)
next
  assume assm: "\<exists>t. (t, as) \<in> ts_tuple_rel (set auxlist) \<and> P t"
  then obtain t X where tX_def: "P t" "as \<in> X" "(t, X) \<in> set auxlist"
    by (auto simp add: ts_tuple_rel_def)
  show "as \<in> foldr (\<union>) (concat (map (\<lambda>(t, rel). if P t then [rel] else []) auxlist)) {}"
    using in_foldr_UnI[OF tX_def(2)] tX_def assm by (induction auxlist) force+
qed

lemma image_snd: "(a, b) \<in> X \<Longrightarrow> b \<in> snd ` X"
  by force

fun result_mmsaux :: "args \<Rightarrow> 'a mmsaux \<Rightarrow> 'a table" where
  "result_mmsaux args (nt, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    Mapping.keys tuple_in"

lemma valid_result_mmsaux_unfolded:
  assumes "valid_mmsaux args cur
    (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) auxlist"
  shows "result_mmsaux args (t, gc, maskL, maskR, data_prev, data_in, tuple_in, tuple_since) =
    foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, left (args_ivl args) \<le> cur - t] {}"
  using valid_mmsaux_tuple_in_keys[OF assms] assms
  by (auto simp add: image_Un ts_tuple_rel_Un foldr_ts_tuple_rel image_snd)
     (fastforce intro: ts_tuple_rel_intro dest: ts_tuple_rel_dest)+

lemma valid_result_mmsaux: "valid_mmsaux args cur aux auxlist \<Longrightarrow>
  result_mmsaux args aux = foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, left (args_ivl args) \<le> cur - t] {}"
  using valid_result_mmsaux_unfolded by (cases aux) fast

interpretation default_msaux: msaux valid_mmsaux init_mmsaux add_new_ts_mmsaux gc_join_mmsaux
  add_new_table_mmsaux result_mmsaux
  using valid_init_mmsaux valid_add_new_ts_mmsaux valid_gc_join_mmsaux valid_add_new_table_mmsaux
    valid_result_mmsaux
  by unfold_locales assumption+

subsection \<open>Optimized data structure for Until\<close>

type_synonym tp = nat

type_synonym 'a mmuaux = "tp \<times> ts queue \<times> nat \<times> bool list \<times> bool list \<times>
  ('a tuple, tp) mapping \<times> (tp, ('a tuple, ts + tp) mapping) mapping \<times> 'a table list \<times> nat"

definition tstp_lt :: "ts + tp \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> bool" where
  "tstp_lt tstp ts tp = case_sum (\<lambda>ts'. ts' \<le> ts) (\<lambda>tp'. tp' < tp) tstp"

definition tstp_le :: "ts + tp \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> bool" where
  "tstp_le tstp ts tp = case_sum (\<lambda>ts'. ts' \<le> ts) (\<lambda>tp'. tp' \<le> tp) tstp"

definition ts_tp_lt :: "ts \<Rightarrow> tp \<Rightarrow> ts + tp \<Rightarrow> bool" where
  "ts_tp_lt ts tp tstp = case_sum (\<lambda>ts'. ts \<le> ts') (\<lambda>tp'. tp < tp') tstp"

definition ts_tp_lt' :: "ts \<Rightarrow> tp \<Rightarrow> ts + tp \<Rightarrow> bool" where
  "ts_tp_lt' ts tp tstp = case_sum (\<lambda>ts'. ts < ts') (\<lambda>tp'. tp \<le> tp') tstp"

definition ts_tp_le :: "ts \<Rightarrow> tp \<Rightarrow> ts + tp \<Rightarrow> bool" where
  "ts_tp_le ts tp tstp = case_sum (\<lambda>ts'. ts \<le> ts') (\<lambda>tp'. tp \<le> tp') tstp"

fun max_tstp :: "ts + tp \<Rightarrow> ts + tp \<Rightarrow> ts + tp" where
  "max_tstp (Inl ts) (Inl ts') = Inl (max ts ts')"
| "max_tstp (Inr tp) (Inr tp') = Inr (max tp tp')"
| "max_tstp (Inl ts) _ = Inl ts"
| "max_tstp _ (Inl ts) = Inl ts"

lemma max_tstp_idem: "max_tstp (max_tstp x y) y = max_tstp x y"
  by (cases x; cases y) auto

lemma max_tstp_idem': "max_tstp x (max_tstp x y) = max_tstp x y"
  by (cases x; cases y) auto

lemma max_tstp_d_d: "max_tstp d d = d"
  by (cases d) auto

lemma max_cases: "(max a b = a \<Longrightarrow> P) \<Longrightarrow> (max a b = b \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis max_def)

lemma max_tstpE: "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow> (max_tstp tstp tstp' = tstp \<Longrightarrow> P) \<Longrightarrow>
  (max_tstp tstp tstp' = tstp' \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases tstp; cases tstp') (auto elim: max_cases)

lemma max_tstp_intro: "tstp_lt tstp ts tp \<Longrightarrow> tstp_lt tstp' ts tp \<Longrightarrow> isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  tstp_lt (max_tstp tstp tstp') ts tp"
  by (auto simp add: tstp_lt_def split: sum.splits)

lemma max_tstp_intro': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_le ts' tp' tstp \<Longrightarrow> ts_tp_le ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto simp add: ts_tp_le_def tstp_le_def split: sum.splits)

lemma max_tstp_intro'': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_le ts' tp' tstp' \<Longrightarrow> ts_tp_le ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto simp add: ts_tp_le_def tstp_le_def split: sum.splits)

lemma max_tstp_intro''': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_lt' ts' tp' tstp \<Longrightarrow> ts_tp_lt' ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto simp add: ts_tp_lt'_def tstp_le_def split: sum.splits)

lemma max_tstp_intro'''': "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow>
  ts_tp_lt' ts' tp' tstp' \<Longrightarrow> ts_tp_lt' ts' tp' (max_tstp tstp tstp')"
  by (cases tstp; cases tstp') (auto simp add: ts_tp_lt'_def tstp_le_def split: sum.splits)

lemma max_tstp_isl: "isl tstp \<longleftrightarrow> isl tstp' \<Longrightarrow> isl (max_tstp tstp tstp') \<longleftrightarrow> isl tstp"
  by (cases tstp; cases tstp') auto

definition filter_a1_map :: "bool \<Rightarrow> tp \<Rightarrow> ('a tuple, tp) mapping \<Rightarrow> 'a table" where
  "filter_a1_map pos tp a1_map =
    {xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow>
    (pos \<longrightarrow> tp' \<le> tp) \<and> (\<not>pos \<longrightarrow> tp \<le> tp')}"

definition filter_a2_map :: "\<I> \<Rightarrow> ts \<Rightarrow> tp \<Rightarrow> (tp, ('a tuple, ts + tp) mapping) mapping \<Rightarrow>
  'a table" where
  "filter_a2_map I ts tp a2_map = {xs. \<exists>tp' \<le> tp. (case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
    (case Mapping.lookup m xs of Some tstp \<Rightarrow> ts_tp_lt' ts tp tstp | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)}"

fun triple_eq_pair :: "('a \<times> 'b \<times> 'c) \<Rightarrow> ('a \<times> 'd) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'd \<Rightarrow> 'c) \<Rightarrow> bool" where
  "triple_eq_pair (t, a1, a2) (ts', tp') f g \<longleftrightarrow> t = ts' \<and> a1 = f tp' \<and> a2 = g ts' tp'"

fun valid_mmuaux' :: "args \<Rightarrow> ts \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a muaux \<Rightarrow> bool" where
  "valid_mmuaux' args cur dt (tp, tss, len, maskL, maskR, a1_map, a2_map,
    done, done_length) auxlist \<longleftrightarrow>
    args_L args \<subseteq> args_R args \<and>
    maskL = join_mask (args_n args) (args_L args) \<and>
    maskR = join_mask (args_n args) (args_R args) \<and>
    len \<le> tp \<and>
    length (linearize tss) = len \<and> sorted (linearize tss) \<and>
    (\<forall>t \<in> set (linearize tss). t \<le> cur \<and> enat cur \<le> enat t + right (args_ivl args)) \<and>
    table (args_n args) (args_L args) (Mapping.keys a1_map) \<and>
    Mapping.keys a2_map = {tp - len..tp} \<and>
    (\<forall>xs \<in> Mapping.keys a1_map. case Mapping.lookup a1_map xs of Some tp' \<Rightarrow> tp' < tp) \<and>
    (\<forall>tp' \<in> Mapping.keys a2_map. case Mapping.lookup a2_map tp' of Some m \<Rightarrow>
      table (args_n args) (args_R args) (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp (cur - (left (args_ivl args) - 1)) tp \<and> (isl tstp \<longleftrightarrow> left (args_ivl args) > 0))) \<and>
    length done = done_length \<and> length done + len = length auxlist \<and>
    rev done = map proj_thd (take (length done) auxlist) \<and>
    (\<forall>x \<in> set (take (length done) auxlist). check_before (args_ivl args) dt x) \<and>
    sorted (map fst auxlist) \<and>
    list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map (args_pos args) tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map (args_ivl args) ts' tp' a2_map)) (drop (length done) auxlist)
      (zip (linearize tss) [tp - len..<tp])"

definition valid_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a muaux \<Rightarrow>
  bool" where
  "valid_mmuaux args cur = valid_mmuaux' args cur cur"

fun eval_step_mmuaux :: "'a mmuaux \<Rightarrow> 'a mmuaux" where
  "eval_step_mmuaux (tp, tss, len, maskL, maskR, a1_map, a2_map,
    done, done_length) = (case safe_hd tss of (Some ts, tss') \<Rightarrow>
      (case Mapping.lookup a2_map (tp - len) of Some m \<Rightarrow>
        let m = Mapping.filter (\<lambda>_ tstp. ts_tp_lt' ts (tp - len) tstp) m;
        T = Mapping.keys m;
        a2_map = Mapping.update (tp - len + 1)
          (case Mapping.lookup a2_map (tp - len + 1) of Some m' \<Rightarrow>
          Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m m') a2_map;
        a2_map = Mapping.delete (tp - len) a2_map in
        (tp, tl_queue tss', len - 1, maskL, maskR, a1_map, a2_map,
        T # done, done_length + 1)))"

lemma Mapping_update_keys: "Mapping.keys (Mapping.update a b m) = Mapping.keys m \<union> {a}"
  by transfer auto

lemma drop_is_Cons_take: "drop n xs = y # ys \<Longrightarrow> take (Suc n) xs = take n xs @ [y]"
proof (induction xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases n) simp_all
qed

lemma list_all2_weaken: "list_all2 f xs ys \<Longrightarrow>
  (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> f x y \<Longrightarrow> f' x y) \<Longrightarrow> list_all2 f' xs ys"
  by (induction xs ys rule: list_all2_induct) auto

lemma Mapping_lookup_delete: "Mapping.lookup (Mapping.delete k m) k' =
  (if k = k' then None else Mapping.lookup m k')"
  by transfer auto

lemma Mapping_lookup_update: "Mapping.lookup (Mapping.update k v m) k' =
  (if k = k' then Some v else Mapping.lookup m k')"
  by transfer auto

lemma hd_le_set: "sorted xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> x \<in> set xs \<Longrightarrow> hd xs \<le> x"
  by (metis eq_iff list.sel(1) set_ConsD sorted.elims(2))

lemma Mapping_lookup_combineE: "Mapping.lookup (Mapping.combine f m m') k = Some v \<Longrightarrow>
  (Mapping.lookup m k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (Mapping.lookup m' k = Some v \<Longrightarrow> P) \<Longrightarrow>
  (\<And>v' v''. Mapping.lookup m k = Some v' \<Longrightarrow> Mapping.lookup m' k = Some v'' \<Longrightarrow>
  f v' v'' = v \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding Mapping.lookup_combine
  by (auto simp add: combine_options_def split: option.splits)

lemma Mapping_keys_filterI: "Mapping.lookup m k = Some v \<Longrightarrow> f k v \<Longrightarrow>
  k \<in> Mapping.keys (Mapping.filter f m)"
  by transfer (auto split: option.splits if_splits)

lemma Mapping_keys_filterD: "k \<in> Mapping.keys (Mapping.filter f m) \<Longrightarrow>
  \<exists>v. Mapping.lookup m k = Some v \<and> f k v"
  by transfer (auto split: option.splits if_splits)

fun lin_ts_mmuaux :: "'a mmuaux \<Rightarrow> ts list" where
  "lin_ts_mmuaux (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    linearize tss"

lemma valid_eval_step_mmuaux':
  assumes "valid_mmuaux' args cur dt aux auxlist"
    "lin_ts_mmuaux aux = ts # tss''" "enat ts + right (args_ivl args) < dt"
  shows "valid_mmuaux' args cur dt (eval_step_mmuaux aux) auxlist \<and>
    lin_ts_mmuaux (eval_step_mmuaux aux) = tss''"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where aux_def:
    "aux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases aux) auto
  then obtain tss' where safe_hd_eq: "safe_hd tss = (Some ts, tss')"
    using assms(2) safe_hd_rep case_optionE
    by (cases "safe_hd tss") fastforce
  note valid_before = assms(1)[unfolded aux_def]
  have lin_tss_not_Nil: "linearize tss \<noteq> []"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have ts_hd: "ts = hd (linearize tss)"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have lin_tss': "linearize tss' = linearize tss"
    using safe_hd_rep[OF safe_hd_eq] by auto
  have tss'_not_empty: "\<not>is_empty tss'"
    using is_empty_alt[of tss'] lin_tss_not_Nil unfolding lin_tss' by auto
  have len_pos: "len > 0"
    using lin_tss_not_Nil valid_before by auto
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using valid_before by auto
  have len_tp: "len \<le> tp"
    using valid_before by auto
  have tp_minus_keys: "tp - len \<in> Mapping.keys a2_map"
    using a2_map_keys by auto
  have tp_minus_keys': "tp - len + 1 \<in> Mapping.keys a2_map"
    using a2_map_keys len_pos len_tp by auto
  obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
    using tp_minus_keys by (auto dest: Mapping_keys_dest)
  have "table n R (Mapping.keys m)"
    "(\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp (cur - (left I - 1)) tp \<and> (isl tstp \<longleftrightarrow> left I > 0))"
    using tp_minus_keys m_def valid_before
    unfolding valid_mmuaux'.simps n_def I_def R_def by fastforce+
  then have m_inst: "table n R (Mapping.keys m)"
    "\<And>xs tstp. Mapping.lookup m xs = Some tstp \<Longrightarrow>
    tstp_lt tstp (cur - (left I - 1)) tp \<and> (isl tstp \<longleftrightarrow> left I > 0)"
    using Mapping_keys_intro by fastforce+
  have m_inst_isl: "\<And>xs tstp. Mapping.lookup m xs = Some tstp \<Longrightarrow> isl tstp \<longleftrightarrow> left I > 0"
    using m_inst(2) by fastforce
  obtain m' where m'_def: "Mapping.lookup a2_map (tp - len + 1) = Some m'"
    using tp_minus_keys' by (auto dest: Mapping_keys_dest)
  have "table n R (Mapping.keys m')"
    "(\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
    tstp_lt tstp (cur - (left I - 1)) tp \<and> (isl tstp \<longleftrightarrow> left I > 0))"
    using tp_minus_keys' m'_def valid_before
    unfolding valid_mmuaux'.simps I_def n_def R_def by fastforce+
  then have m'_inst: "table n R (Mapping.keys m')"
    "\<And>xs tstp. Mapping.lookup m' xs = Some tstp \<Longrightarrow>
    tstp_lt tstp (cur - (left I - 1)) tp \<and> (isl tstp \<longleftrightarrow> left I > 0)"
    using Mapping_keys_intro by fastforce+
  have m'_inst_isl: "\<And>xs tstp. Mapping.lookup m' xs = Some tstp \<Longrightarrow> isl tstp \<longleftrightarrow> left I > 0"
    using m'_inst(2) by fastforce
  define m_upd where "m_upd = Mapping.filter (\<lambda>_ tstp. ts_tp_lt' ts (tp - len) tstp) m"
  define T where "T = Mapping.keys m_upd"
  define mc where "mc = Mapping.combine (\<lambda>tstp tstp'. max_tstp tstp tstp') m_upd m'"
  define a2_map' where "a2_map' = Mapping.update (tp - len + 1) mc a2_map"
  define a2_map'' where "a2_map'' = Mapping.delete (tp - len) a2_map'"
  have m_upd_lookup: "\<And>xs tstp. Mapping.lookup m_upd xs = Some tstp \<Longrightarrow>
    tstp_lt tstp (cur - (left I - 1)) tp \<and> (isl tstp \<longleftrightarrow> left I > 0)"
    unfolding m_upd_def Mapping.lookup_filter
    using m_inst(2) by (auto split: option.splits if_splits)
  have mc_lookup: "\<And>xs tstp. Mapping.lookup mc xs = Some tstp \<Longrightarrow>
    tstp_lt tstp (cur - (left I - 1)) tp \<and> (isl tstp \<longleftrightarrow> left I > 0)"
    unfolding mc_def Mapping.lookup_combine
    using m_upd_lookup m'_inst(2)
    by (auto simp add: combine_options_def max_tstp_isl intro: max_tstp_intro split: option.splits)
  have mc_keys: "Mapping.keys mc \<subseteq> Mapping.keys m \<union> Mapping.keys m'"
    unfolding mc_def Mapping.keys_combine m_upd_def
    using Mapping.keys_filter by fastforce
  have tp_len_assoc: "tp - len + 1 = tp - (len - 1)"
    using len_pos len_tp by auto
  have a2_map''_keys: "Mapping.keys a2_map'' = {tp - (len - 1)..tp}"
    unfolding a2_map''_def a2_map'_def Mapping.keys_delete Mapping_update_keys a2_map_keys
    using tp_len_assoc by auto
  have lin_tss_Cons: "linearize tss = ts # linearize (tl_queue tss')"
    using lin_tss_not_Nil
    by (auto simp add: tl_queue_rep[OF tss'_not_empty] lin_tss' ts_hd)
  have tp_len_tp_unfold: "[tp - len..<tp] = (tp - len) # [tp - (len - 1)..<tp]"
    unfolding tp_len_assoc[symmetric]
    using len_pos len_tp Suc_diff_le upt_conv_Cons by auto
  have id: "\<And>x. x \<in> {tp - (len - 1) + 1..tp} \<Longrightarrow>
    Mapping.lookup a2_map'' x = Mapping.lookup a2_map x"
    unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update tp_len_assoc
    using len_tp by auto
  have list_all2: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map))
    (drop (length done) auxlist) (zip (linearize tss) [tp - len..<tp])"
    using valid_before unfolding I_def pos_def by auto
  obtain hd_aux tl_aux where aux_split: "drop (length done) auxlist = hd_aux # tl_aux"
    "case hd_aux of (t, a1, a2) \<Rightarrow> (t, a1, a2) =
    (ts, filter_a1_map pos (tp - len) a1_map, filter_a2_map I ts (tp - len) a2_map)"
    and list_all2': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)) tl_aux
      (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])"
    using list_all2[unfolded lin_tss_Cons tp_len_tp_unfold zip_Cons_Cons list_all2_Cons2] by auto
  have lookup''_tp_minus: "Mapping.lookup a2_map'' (tp - (len - 1)) = Some mc"
    unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update
      tp_len_assoc[symmetric]
    using len_tp by auto
  have filter_a2_map_cong: "\<And>ts' tp'. ts' \<in> set (linearize tss) \<Longrightarrow>
    tp' \<in> {tp - (len - 1)..<tp} \<Longrightarrow> filter_a2_map I ts' tp' a2_map =
    filter_a2_map I ts' tp' a2_map''"
  proof (rule set_eqI, rule iffI)
    fix ts' tp' xs
    assume assms: "ts' \<in> set (linearize tss)"
      "tp' \<in> {tp - (len - 1)..<tp}" "xs \<in> filter_a2_map I ts' tp' a2_map"
    obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp'" "Mapping.lookup a2_map tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt' ts' tp' tstp"
      using assms(3)[unfolded filter_a2_map_def]
      by (fastforce split: option.splits)
    have ts_le_ts': "ts \<le> ts'"
      using hd_le_set[OF _ lin_tss_not_Nil assms(1)] valid_before
      unfolding ts_hd by auto
    have tp_bef_in: "tp_bef \<in> {tp - len..tp}"
      using defs(2) valid_before by (auto intro!: Mapping_keys_intro)
    have tp_minus_le: "tp - (len - 1) \<le> tp'"
      using assms(2) by auto
    show "xs \<in> filter_a2_map I ts' tp' a2_map''"
    proof (cases "tp_bef \<le> tp - (len - 1)")
      case True
      show ?thesis
      proof (cases "tp_bef = tp - len")
        case True
        have m_bef_m: "m_bef = m"
          using defs(2) m_def
          unfolding True by auto
        have "Mapping.lookup m_upd xs = Some tstp"
          using defs(3,4) assms(2) ts_le_ts' unfolding m_bef_m m_upd_def
          by (auto simp add: Mapping.lookup_filter ts_tp_lt'_def intro: Mapping_keys_intro
              split: sum.splits)
        then have "case Mapping.lookup mc xs of None \<Rightarrow> False | Some tstp \<Rightarrow>
          ts_tp_lt' ts' tp' tstp"
          unfolding mc_def Mapping.lookup_combine
          using m'_inst(2) m_upd_lookup
          by (auto simp add: combine_options_def defs(4) intro!: max_tstp_intro'''
              dest: Mapping_keys_dest split: option.splits)
        then show ?thesis
          using lookup''_tp_minus tp_minus_le defs
          unfolding m_bef_m filter_a2_map_def by (auto split: option.splits)
      next
        case False
        then have "tp_bef = tp - (len - 1)"
          using True tp_bef_in by auto
        then have m_bef_m: "m_bef = m'"
          using defs(2) m'_def
          unfolding tp_len_assoc by auto
        have "case Mapping.lookup mc xs of None \<Rightarrow> False | Some tstp \<Rightarrow>
          ts_tp_lt' ts' tp' tstp"
          unfolding mc_def Mapping.lookup_combine
          using m'_inst(2) m_upd_lookup defs(3)[unfolded m_bef_m]
          by (auto simp add: combine_options_def defs(4) intro!: max_tstp_intro''''
              dest: Mapping_keys_dest split: option.splits)
        then show ?thesis
          using lookup''_tp_minus tp_minus_le defs
          unfolding m_bef_m filter_a2_map_def by (auto split: option.splits)
      qed
    next
      case False
      then have "Mapping.lookup a2_map'' tp_bef = Mapping.lookup a2_map tp_bef"
        using id tp_bef_in len_tp by auto
      then show ?thesis
        unfolding filter_a2_map_def
        using defs by auto
    qed
  next
    fix ts' tp' xs
    assume assms: "ts' \<in> set (linearize tss)" "tp' \<in> {tp - (len - 1)..<tp}"
      "xs \<in> filter_a2_map I ts' tp' a2_map''"
    obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp'"
      "Mapping.lookup a2_map'' tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt' ts' tp' tstp"
      using assms(3)[unfolded filter_a2_map_def]
      by (fastforce split: option.splits)
    have ts_le_ts': "ts \<le> ts'"
      using hd_le_set[OF _ lin_tss_not_Nil assms(1)] valid_before
      unfolding ts_hd by auto
    have tp_bef_in: "tp_bef \<in> {tp - (len - 1)..tp}"
      using defs(2) a2_map''_keys by (auto intro!: Mapping_keys_intro)
    have tp_minus_le: "tp - len \<le> tp'" "tp - (len - 1) \<le> tp'"
      using assms(2) by auto
    show "xs \<in> filter_a2_map I ts' tp' a2_map"
    proof (cases "tp_bef = tp - (len - 1)")
      case True
      have m_beg_mc: "m_bef = mc"
        using defs(2)
        unfolding True a2_map''_def a2_map'_def tp_len_assoc Mapping_lookup_delete
          Mapping.lookup_update
        by (auto split: if_splits)
      show ?thesis
        using defs(3)[unfolded m_beg_mc mc_def]
      proof (rule Mapping_lookup_combineE)
        assume lassm: "Mapping.lookup m_upd xs = Some tstp"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map"
          unfolding m_upd_def Mapping.lookup_filter
          using m_def tp_minus_le(1) defs
          by (auto simp add: filter_a2_map_def split: option.splits if_splits)
      next
        assume lassm: "Mapping.lookup m' xs = Some tstp"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map"
          using m'_def defs(4) tp_minus_le defs
          unfolding filter_a2_map_def tp_len_assoc
          by auto
      next
        fix v' v''
        assume lassms: "Mapping.lookup m_upd xs = Some v'" "Mapping.lookup m' xs = Some v''"
          "max_tstp v' v'' = tstp"
        show "xs \<in> filter_a2_map I ts' tp' a2_map"
        proof (rule max_tstpE)
          show "isl v' = isl v''"
            using lassms(1,2) m_upd_lookup m'_inst(2)
            by auto
        next
          assume "max_tstp v' v'' = v'"
          then show "xs \<in> filter_a2_map I ts' tp' a2_map"
            using lassms(1,3) m_def defs tp_minus_le(1)
            unfolding tp_len_assoc m_upd_def Mapping.lookup_filter
            by (auto simp add: filter_a2_map_def split: option.splits if_splits)
        next
          assume "max_tstp v' v'' = v''"
          then show "xs \<in> filter_a2_map I ts' tp' a2_map"
            using lassms(2,3) m'_def defs tp_minus_le(2)
            unfolding tp_len_assoc
            by (auto simp add: filter_a2_map_def)
        qed
      qed
    next
      case False
      then have "Mapping.lookup a2_map'' tp_bef = Mapping.lookup a2_map tp_bef"
        using id tp_bef_in by auto
      then show ?thesis
        unfolding filter_a2_map_def
        using defs by auto (metis option.simps(5))
    qed
  qed
  have set_tl_tss': "set (linearize (tl_queue tss')) \<subseteq> set (linearize tss)"
    unfolding tl_queue_rep[OF tss'_not_empty] lin_tss_Cons by auto
  have list_all2'': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'')) tl_aux
      (zip (linearize (tl_queue tss')) [tp - (len - 1)..<tp])"
    using filter_a2_map_cong set_tl_tss'
    by (intro list_all2_weaken[OF list_all2']) (auto elim!: in_set_zipE split: prod.splits)
  have lookup'': "\<forall>tp' \<in> Mapping.keys a2_map''. case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
    table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp (cur - (left I - 1)) tp \<and> isl tstp = (0 < left I))"
  proof (rule ballI)
    fix tp'
    assume assm: "tp' \<in> Mapping.keys a2_map''"
    then obtain f where f_def: "Mapping.lookup a2_map'' tp' = Some f"
      by (auto dest: Mapping_keys_dest)
    have tp'_in: "tp' \<in> {tp - (len - 1)..tp}"
      using assm unfolding a2_map''_keys .
    then have tp'_in_keys: "tp' \<in> Mapping.keys a2_map"
      using valid_before by auto
    have "table n R (Mapping.keys f) \<and>
      (\<forall>xs \<in> Mapping.keys f. case Mapping.lookup f xs of Some tstp \<Rightarrow>
      tstp_lt tstp (cur - (left I - 1)) tp \<and> isl tstp = (0 < left I))"
    proof (cases "tp' = tp - (len - 1)")
      case True
      then have f_mc: "f = mc"
        using f_def
        unfolding a2_map''_def a2_map'_def Mapping_lookup_delete Mapping_lookup_update tp_len_assoc
        by (auto split: if_splits)
      have "table n R (Mapping.keys f)"
        unfolding f_mc
        using mc_keys m_def m'_def m_inst m'_inst
        by (auto simp add: table_def)
      moreover have "\<forall>xs \<in> Mapping.keys f. case Mapping.lookup f xs of Some tstp \<Rightarrow>
        tstp_lt tstp (cur - (left I - 1)) tp \<and> isl tstp = (0 < left I)"
        using assm Mapping.keys_filter m_inst(2) m_inst_isl m'_inst(2) m'_inst_isl max_tstp_isl
        unfolding f_mc mc_def Mapping.lookup_combine
        by (auto simp add: combine_options_def m_upd_def Mapping.lookup_filter
            intro!: max_tstp_intro Mapping_keys_intro dest!: Mapping_keys_dest
            split: option.splits)
      ultimately show ?thesis
        by auto
    next
      case False
      have "Mapping.lookup a2_map tp' = Some f"
        using tp'_in id[of tp'] f_def False by auto
      then show ?thesis
        using tp'_in_keys valid_before
        unfolding valid_mmuaux'.simps I_def n_def R_def by fastforce
    qed
    then show "case Mapping.lookup a2_map'' tp' of Some m \<Rightarrow>
      table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp (cur - (left I - 1)) tp \<and> isl tstp = (0 < left I))"
      using f_def by auto
  qed
  have tl_aux_def: "tl_aux = drop (length done + 1) auxlist"
    using aux_split(1) by (metis Suc_eq_plus1 add_Suc drop0 drop_Suc_Cons drop_drop)
  have T_eq: "T = filter_a2_map I ts (tp - len) a2_map"
  proof (rule set_eqI, rule iffI)
    fix xs
    assume "xs \<in> filter_a2_map I ts (tp - len) a2_map"
    then obtain tp_bef m_bef tstp where defs: "tp_bef \<le> tp - len"
      "Mapping.lookup a2_map tp_bef = Some m_bef"
      "Mapping.lookup m_bef xs = Some tstp" "ts_tp_lt' ts (tp - len) tstp"
      by (fastforce simp add: filter_a2_map_def split: option.splits)
    then have tp_bef_minus: "tp_bef = tp - len"
      using valid_before Mapping_keys_intro by force
    have m_bef_m: "m_bef = m"
      using defs(2) m_def
      unfolding tp_bef_minus by auto
    show "xs \<in> T"
      using defs
      unfolding T_def m_upd_def m_bef_m
      by (auto intro: Mapping_keys_filterI Mapping_keys_intro)
  next
    fix xs
    assume "xs \<in> T"
    then show "xs \<in> filter_a2_map I ts (tp - len) a2_map"
      using m_def Mapping.keys_filter
      unfolding T_def m_upd_def filter_a2_map_def
      by (auto simp add: filter_a2_map_def dest!: Mapping_keys_filterD split: if_splits)
  qed
  have min_auxlist_done: "min (length auxlist) (length done) = length done"
    using valid_before by auto
  then have "\<forall>x \<in> set (take (length done) auxlist). check_before I dt x"
    "rev done = map proj_thd (take (length done) auxlist)"
    using valid_before unfolding I_def by auto
  then have list_all': "(\<forall>x \<in> set (take (length (T # done)) auxlist). check_before I dt x)"
    "rev (T # done) = map proj_thd (take (length (T # done)) auxlist)"
    using drop_is_Cons_take[OF aux_split(1)] aux_split(2) assms(3)
    by (auto simp add: T_eq I_def)
  have eval_step_mmuaux_eq: "eval_step_mmuaux (tp, tss, len, maskL, maskR, a1_map, a2_map,
    done, done_length) = (tp, tl_queue tss', len - 1,  maskL, maskR, a1_map, a2_map'',
    T # done, done_length + 1)"
    using safe_hd_eq m_def m'_def m_upd_def T_def mc_def a2_map'_def a2_map''_def
    by (auto simp add: Let_def)
  have "lin_ts_mmuaux (eval_step_mmuaux aux) = tss''"
    using lin_tss_Cons assms(2) unfolding aux_def eval_step_mmuaux_eq by auto
  then show ?thesis
    using valid_before a2_map''_keys sorted_tl list_all' lookup'' list_all2''
    unfolding eval_step_mmuaux_eq valid_mmuaux'.simps tl_aux_def aux_def I_def n_def R_def pos_def
    using lin_tss_not_Nil safe_hd_eq len_pos
    by (auto simp add: list.set_sel(2) lin_tss' tl_queue_rep[OF tss'_not_empty] min_auxlist_done)
qed

lemma done_empty_valid_mmuaux'_intro:
  assumes "valid_mmuaux' args cur dt
    (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) auxlist"
  shows "valid_mmuaux' args cur dt'
    (tp, tss, len, maskL, maskR, a1_map, a2_map, [], 0)
    (drop (length done) auxlist)"
  using assms sorted_drop by (auto simp add: drop_map[symmetric])

lemma valid_mmuaux'_mono:
  assumes "valid_mmuaux' args cur dt aux auxlist" "dt \<le> dt'"
  shows "valid_mmuaux' args cur dt' aux auxlist"
  using assms less_le_trans by (cases aux) fastforce

lemma valid_foldl_eval_step_mmuaux':
  assumes valid_before: "valid_mmuaux' args cur dt aux auxlist"
    "lin_ts_mmuaux aux = tss @ tss'"
    "\<And>ts. ts \<in> set (take (length tss) (lin_ts_mmuaux aux)) \<Longrightarrow> enat ts + right (args_ivl args) < dt"
  shows "valid_mmuaux' args cur dt (foldl (\<lambda>aux _. eval_step_mmuaux aux) aux tss) auxlist \<and>
    lin_ts_mmuaux (foldl (\<lambda>aux _. eval_step_mmuaux aux) aux tss) = tss'"
  using assms
proof (induction tss arbitrary: aux)
  case (Cons ts tss)
  have app_ass: "lin_ts_mmuaux aux = ts # (tss @ tss')"
    using Cons(3) by auto
  have "enat ts + right (args_ivl args) < dt"
    using Cons by auto
  then have valid_step: "valid_mmuaux' args cur dt (eval_step_mmuaux aux) auxlist"
    "lin_ts_mmuaux (eval_step_mmuaux aux) = tss @ tss'"
    using valid_eval_step_mmuaux'[OF Cons(2) app_ass] by auto
  show ?case
    using Cons(1)[OF valid_step] valid_step Cons(4) app_ass by auto
qed auto

lemma sorted_dropWhile_filter: "sorted xs \<Longrightarrow> dropWhile (\<lambda>t. enat t + right I < enat nt) xs =
  filter (\<lambda>t. \<not>enat t + right I < enat nt) xs"
proof (induction xs)
  case (Cons x xs)
  then show ?case
  proof (cases "enat x + right I < enat nt")
    case False
    then have neg: "enat x + right I \<ge> enat nt"
      by auto
    have "\<And>z. z \<in> set xs \<Longrightarrow> \<not>enat z + right I < enat nt"
    proof -
      fix z
      assume "z \<in> set xs"
      then have "enat z + right I \<ge> enat x + right I"
        using Cons by auto
      with neg have "enat z + right I \<ge> enat nt"
        using dual_order.trans by blast
      then show "\<not>enat z + right I < enat nt"
        by auto
    qed
    with False show ?thesis
      using filter_empty_conv by auto
  qed auto
qed auto

fun shift_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a mmuaux" where
  "shift_mmuaux args nt (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    (let tss_list = linearize (takeWhile_queue (\<lambda>t. enat t + right (args_ivl args) < enat nt) tss) in
    foldl (\<lambda>aux _. eval_step_mmuaux aux) (tp, tss, len, maskL, maskR,
      a1_map, a2_map, done, done_length) tss_list)"

lemma valid_shift_mmuaux':
  assumes "valid_mmuaux' args cur cur aux auxlist" "nt \<ge> cur"
  shows "valid_mmuaux' args cur nt (shift_mmuaux args nt aux) auxlist \<and>
    (\<forall>ts \<in> set (lin_ts_mmuaux (shift_mmuaux args nt aux)). \<not>enat ts + right (args_ivl args) < nt)"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,2) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where aux_def:
    "aux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases aux) auto
  note valid_before = valid_folded[unfolded aux_def]
  define tss_list where "tss_list =
    linearize (takeWhile_queue (\<lambda>t. enat t + right I < enat nt) tss)"
  have tss_list_takeWhile: "tss_list = takeWhile (\<lambda>t. enat t + right I < enat nt) (linearize tss)"
    using tss_list_def unfolding takeWhile_queue_rep .
  then obtain tss_list' where tss_list'_def: "linearize tss = tss_list @ tss_list'"
    "tss_list' = dropWhile (\<lambda>t. enat t + right I < enat nt) (linearize tss)"
    by auto
  obtain tp' len' tss' maskL' maskR' a1_map' a2_map' "done'" done_length' where
    foldl_aux_def: "(tp', tss', len', maskL', maskR', a1_map', a2_map',
      done', done_length') = foldl (\<lambda>aux _. eval_step_mmuaux aux) aux tss_list"
    by (cases "foldl (\<lambda>aux _. eval_step_mmuaux aux) aux tss_list") auto
  have lin_tss_aux: "lin_ts_mmuaux aux = linearize tss"
    unfolding aux_def by auto
  have "take (length tss_list) (lin_ts_mmuaux aux) = tss_list"
    unfolding lin_tss_aux using tss_list'_def(1) by auto
  then have valid_foldl: "valid_mmuaux' args cur nt
    (foldl (\<lambda>aux _. eval_step_mmuaux aux) aux tss_list) auxlist"
    "lin_ts_mmuaux (foldl (\<lambda>aux _. eval_step_mmuaux aux) aux tss_list) = tss_list'"
    using valid_foldl_eval_step_mmuaux'[OF valid_before[folded aux_def], unfolded lin_tss_aux,
      OF tss_list'_def(1)] tss_list_takeWhile set_takeWhileD
    unfolding lin_tss_aux I_def by fastforce+
  have shift_mmuaux_eq: "shift_mmuaux args nt aux = foldl (\<lambda>aux _. eval_step_mmuaux aux) aux tss_list"
    using tss_list_def unfolding aux_def I_def by auto
  have "\<And>ts. ts \<in> set tss_list' \<Longrightarrow> \<not>enat ts + right (args_ivl args) < nt"
    using sorted_dropWhile_filter tss_list'_def(2) valid_before unfolding I_def by auto
  then show ?thesis
    using valid_foldl(1)[unfolded shift_mmuaux_eq[symmetric]]
    unfolding valid_foldl(2)[unfolded shift_mmuaux_eq[symmetric]] by auto
qed

lift_definition upd_set' :: "('a, 'b) mapping \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping" is
  "\<lambda>m d f X a. (if a \<in> X then (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d)
    else Mapping.lookup m a)" .

lemma upd_set'_lookup: "Mapping.lookup (upd_set' m d f X) a = (if a \<in> X then
  (case Mapping.lookup m a of Some b \<Rightarrow> Some (f b) | None \<Rightarrow> Some d) else Mapping.lookup m a)"
  by (simp add: Mapping.lookup.rep_eq upd_set'.rep_eq)

lemma upd_set'_keys: "Mapping.keys (upd_set' m d f X) = Mapping.keys m \<union> X"
  by (auto simp add: upd_set'_lookup intro!: Mapping_keys_intro
      dest!: Mapping_keys_dest split: option.splits)

lift_definition upd_nested :: "('a, ('b, 'c) mapping) mapping \<Rightarrow>
  'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a, ('b, 'c) mapping) mapping" is
  "\<lambda>m d f X a. case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None" .

lemma upd_nested_lookup: "Mapping.lookup (upd_nested m d f X) a =
  (case Mapping.lookup m a of Some m' \<Rightarrow> Some (upd_set' m' d f {b. (a, b) \<in> X})
  | None \<Rightarrow> if a \<in> fst ` X then Some (upd_set' Mapping.empty d f {b. (a, b) \<in> X}) else None)"
  by (simp add: Mapping.lookup.abs_eq upd_nested.abs_eq)

lemma upd_nested_keys: "Mapping.keys (upd_nested m d f X) = Mapping.keys m \<union> fst ` X"
  by (auto simp add: upd_nested_lookup Domain.DomainI fst_eq_Domain intro!: Mapping_keys_intro
      dest!: Mapping_keys_dest split: option.splits)

fun add_new_mmuaux :: "args \<Rightarrow> 'a table \<Rightarrow> 'a table \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a mmuaux" where
  "add_new_mmuaux args rel1 rel2 nt aux =
    (let (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    shift_mmuaux args nt aux;
    I = args_ivl args; pos = args_pos args;
    new_tstp = (if left I = 0 then Inr tp else Inl (nt - (left I - 1)));
    tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
      (if \<not>pos then {(tp - len, as)} else {})
      | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
      else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if left I = 0 then {tp} \<times> rel2 else {});
    a2_map = Mapping.update (tp + 1) Mapping.empty
      (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp);
    a1_map = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
      (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1);
    tss = append_queue nt tss in
    (tp + 1, tss, len + 1, maskL, maskR, a1_map, a2_map, done, done_length))"

lemma fst_case: "(\<lambda>x. fst (case x of (t, a1, a2) \<Rightarrow> (t, y t a1 a2, z t a1 a2))) = fst"
  by auto

lemma list_all2_in_setE: "list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> (\<And>y. y \<in> set ys \<Longrightarrow> P x y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fastforce simp: list_all2_iff set_zip in_set_conv_nth)

lemma list_all2_zip: "list_all2 (\<lambda>x y. triple_eq_pair x y f g) xs (zip ys zs) \<Longrightarrow>
  (\<And>y. y \<in> set ys \<Longrightarrow> Q y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> Q (fst x)"
  by (auto simp: in_set_zip elim!: list_all2_in_setE triple_eq_pair.elims)

lemma list_appendE: "xs = ys @ zs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
  (x \<in> set ys \<Longrightarrow> P) \<Longrightarrow> (x \<in> set zs \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma take_takeWhile: "n \<le> length ys \<Longrightarrow>
  (\<And>y. y \<in> set (take n ys) \<Longrightarrow> P y) \<Longrightarrow>
  (\<And>y. y \<in> set (drop n ys) \<Longrightarrow> \<not>P y) \<Longrightarrow>
  take n ys = takeWhile P ys"
proof (induction ys arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases n) simp_all
qed

lemma valid_add_new_mmuaux:
  assumes valid_before: "valid_mmuaux args cur aux auxlist"
    and tabs: "table (args_n args) (args_L args) rel1" "table (args_n args) (args_R args) rel2"
    and nt_mono: "nt \<ge> cur"
  shows "valid_mmuaux args nt (add_new_mmuaux args rel1 rel2 nt aux)
    (update_until args rel1 rel2 nt auxlist)"
proof -
  define I where "I = args_ivl args"
  define n where "n = args_n args"
  define L where "L = args_L args"
  define R where "R = args_R args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,4) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where shift_aux_def:
    "shift_mmuaux args nt aux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases "shift_mmuaux args nt aux") auto
  have valid_shift_aux: "valid_mmuaux' args cur nt (tp, tss, len, maskL, maskR,
    a1_map, a2_map, done, done_length) auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> \<not>enat ts + right (args_ivl args) < enat nt"
    using valid_shift_mmuaux'[OF assms(1)[unfolded valid_mmuaux_def] assms(4)]
    unfolding shift_aux_def by auto
  define new_tstp where "new_tstp = (if left I = 0 then Inr tp else Inl (nt - (left I - 1)))"
  have new_tstp_lt_isl: "tstp_lt new_tstp (nt - (left I - 1)) (tp + 1)"
    "isl new_tstp \<longleftrightarrow> left I > 0"
    by (auto simp add: new_tstp_def tstp_lt_def)
  define tmp where "tmp = \<Union>((\<lambda>as. case Mapping.lookup a1_map (proj_tuple maskL as) of None \<Rightarrow>
    (if \<not>pos then {(tp - len, as)} else {})
    | Some tp' \<Rightarrow> if pos then {(max (tp - len) tp', as)}
    else {(max (tp - len) (tp' + 1), as)}) ` rel2) \<union> (if left I = 0 then {tp} \<times> rel2 else {})"
  have a1_map_lookup: "\<And>as tp'. Mapping.lookup a1_map as = Some tp' \<Longrightarrow> tp' < tp"
    using valid_shift_aux(1) Mapping_keys_intro by force
  then have fst_tmp: "\<And>tp'. tp' \<in> fst ` tmp \<Longrightarrow> tp - len \<le> tp' \<and> tp' < tp + 1"
    unfolding tmp_def by (auto simp add: less_SucI split: option.splits if_splits)
  have snd_tmp: "\<And>tp'. table n R (snd ` tmp)"
    using tabs(2) unfolding tmp_def n_def R_def
    by (auto simp add: table_def split: if_splits option.splits)
  define a2_map' where "a2_map' = Mapping.update (tp + 1) Mapping.empty
    (upd_nested a2_map new_tstp (max_tstp new_tstp) tmp)"
  define a1_map' where "a1_map' = (if pos then Mapping.filter (\<lambda>as _. as \<in> rel1)
    (upd_set a1_map (\<lambda>_. tp) (rel1 - Mapping.keys a1_map)) else upd_set a1_map (\<lambda>_. tp) rel1)"
  define tss' where "tss' = append_queue nt tss"
  have add_new_mmuaux_eq: "add_new_mmuaux args rel1 rel2 nt aux = (tp + 1, tss', len + 1,
    maskL, maskR, a1_map', a2_map', done, done_length)"
    using shift_aux_def new_tstp_def tmp_def a2_map'_def a1_map'_def tss'_def
    unfolding I_def pos_def
    by (auto simp only: add_new_mmuaux.simps Let_def)
  have update_until_eq: "update_until args rel1 rel2 nt auxlist =
    (map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem (nt - t) I then a2 \<union> join rel2 pos a1 else a2)) auxlist) @
    [(nt, rel1, if left I = 0 then rel2 else empty_table)]"
    unfolding update_until_def I_def pos_def by simp
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have auxlist_split: "auxlist = take (length done) auxlist @ drop (length done) auxlist"
    using len_done_auxlist by auto
  have lin_tss': "linearize tss' = linearize tss @ [nt]"
    unfolding tss'_def append_queue_rep by (rule refl)
  have len_lin_tss': "length (linearize tss') = len + 1"
    unfolding lin_tss' using valid_shift_aux by auto
  have tmp: "sorted (linearize tss)" "\<And>t. t \<in> set (linearize tss) \<Longrightarrow> t \<le> cur"
    using valid_shift_aux by auto
  have sorted_lin_tss': "sorted (linearize tss')"
    unfolding lin_tss' using tmp(1) le_trans[OF _ assms(4), OF tmp(2)]
    by (simp add: sorted_append)
  have in_lin_tss: "\<And>t. t \<in> set (linearize tss) \<Longrightarrow>
    t \<le> cur \<and> enat cur \<le> enat t + right I"
    using valid_shift_aux(1) unfolding I_def by auto
  then have set_lin_tss': "\<forall>t \<in> set (linearize tss'). t \<le> nt \<and> enat nt \<le> enat t + right I"
    unfolding lin_tss' I_def using le_trans[OF _ assms(4)] valid_shift_aux(2)
    by (auto simp add: not_less)
  have a1_map'_keys: "Mapping.keys a1_map' \<subseteq> Mapping.keys a1_map \<union> rel1"
    unfolding a1_map'_def using Mapping.keys_filter Mapping_upd_set_keys
    by (auto simp add: Mapping_upd_set_keys split: if_splits dest: Mapping_keys_filterD)
  then have tab_a1_map'_keys: "table n L (Mapping.keys a1_map')"
    using valid_shift_aux(1) tabs(1) by (auto simp add: table_def n_def L_def)
  have a2_map_keys: "Mapping.keys a2_map = {tp - len..tp}"
    using valid_shift_aux by auto
  have a2_map'_keys: "Mapping.keys a2_map' = {tp - len..tp + 1}"
    unfolding a2_map'_def Mapping.keys_update upd_nested_keys a2_map_keys using fst_tmp
    by fastforce
  then have a2_map'_keys': "Mapping.keys a2_map' = {tp + 1 - (len + 1)..tp + 1}"
    by auto
  have len_upd_until: "length done + (len + 1) = length (update_until args rel1 rel2 nt auxlist)"
    using valid_shift_aux unfolding update_until_eq by auto
  have set_take_auxlist: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have list_all2_triple: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map)
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)) (drop (length done) auxlist)
    (zip (linearize tss) [tp - len..<tp])"
    using valid_shift_aux unfolding I_def pos_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux(2)[OF list_all2_zip[OF list_all2_triple,
      of "\<lambda>y. y \<in> set (linearize tss)"]]
    unfolding I_def by auto
  have length_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using take_takeWhile[OF length_done_auxlist set_take_auxlist set_drop_auxlist] .
  have "length done = length (takeWhile (check_before I nt) auxlist)"
    by (metis (no_types) add_diff_cancel_right' auxlist_split diff_diff_cancel
        length_append length_done_auxlist length_drop take_auxlist_takeWhile)
  then have set_take_auxlist': "\<And>x. x \<in> set (take (length done)
    (update_until args rel1 rel2 nt auxlist)) \<Longrightarrow> check_before I nt x"
    by (metis I_def length_map map_proj_thd_update_until set_takeWhileD takeWhile_eq_take)
  have rev_done: "rev done = map proj_thd (take (length done) auxlist)"
    using valid_shift_aux by auto
  moreover have "\<dots> = map proj_thd (takeWhile (check_before I nt)
    (update_until args rel1 rel2 nt auxlist))"
    by (simp add: take_auxlist_takeWhile map_proj_thd_update_until I_def)
  finally have rev_done': "rev done = map proj_thd (take (length done)
    (update_until args rel1 rel2 nt auxlist))"
    by (metis length_map length_rev takeWhile_eq_take)
  have map_fst_auxlist_take: "\<And>t. t \<in> set (map fst (take (length done) auxlist)) \<Longrightarrow> t \<le> nt"
    using set_take_auxlist
    by auto (meson add_increasing2 enat_ord_simps(1) le_cases not_less zero_le)
  have map_fst_auxlist_drop: "\<And>t. t \<in> set (map fst (drop (length done) auxlist)) \<Longrightarrow> t \<le> nt"
    using in_lin_tss[OF list_all2_zip[OF list_all2_triple, of "\<lambda>y. y \<in> set (linearize tss)"]]
      assms(4) dual_order.trans by auto blast
  have set_drop_auxlist_cong: "\<And>x t a1 a2. x \<in> set (drop (length done) auxlist) \<Longrightarrow>
    x = (t, a1, a2) \<Longrightarrow> mem (nt - t) I \<longleftrightarrow> left I \<le> nt - t"
  proof -
    fix x t a1 a2
    assume "x \<in> set (drop (length done) auxlist)" "x = (t, a1, a2)"
    then have "enat t + right I \<ge> enat nt"
      using set_drop_auxlist not_less
      by auto blast
    then have "right I \<ge> enat (nt - t)"
      by (cases "right I") auto
    then show "mem (nt - t) I \<longleftrightarrow> left I \<le> nt - t"
      by auto
  qed
  have sorted_fst_auxlist: "sorted (map fst auxlist)"
    using valid_shift_aux by auto
  have set_map_fst_auxlist: "\<And>t. t \<in> set (map fst auxlist) \<Longrightarrow> t \<le> nt"
    using arg_cong[OF auxlist_split, of "map fst", unfolded map_append] map_fst_auxlist_take
      map_fst_auxlist_drop by auto
  have lookup_a1_map_keys: "\<And>xs tp'. Mapping.lookup a1_map xs = Some tp' \<Longrightarrow> tp' < tp"
    using valid_shift_aux Mapping_keys_intro by force
  have lookup_a1_map_keys': "\<forall>xs \<in> Mapping.keys a1_map'.
    case Mapping.lookup a1_map' xs of Some tp' \<Rightarrow> tp' < tp + 1"
    using lookup_a1_map_keys unfolding a1_map'_def
    by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set Mapping_upd_set_keys
        split: option.splits dest: Mapping_keys_dest) fastforce+
  have sorted_upd_until: "sorted (map fst (update_until args rel1 rel2 nt auxlist))"
    using sorted_fst_auxlist set_map_fst_auxlist
    unfolding update_until_eq
    by (auto simp add: sorted_append comp_def fst_case)
  have lookup_a2_map: "\<And>tp' m. Mapping.lookup a2_map tp' = Some m \<Longrightarrow>
    table n R (Mapping.keys m) \<and> (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp (cur - (left I - 1)) tp \<and> (isl tstp \<longleftrightarrow> left I > 0))"
    using valid_shift_aux(1) Mapping_keys_intro unfolding I_def n_def R_def by force
  then have lookup_a2_map': "\<And>tp' m xs tstp. Mapping.lookup a2_map tp' = Some m \<Longrightarrow>
    Mapping.lookup m xs = Some tstp \<Longrightarrow> tstp_lt tstp (nt - (left I - 1)) tp \<and>
    isl tstp = (0 < left I)"
    using Mapping_keys_intro assms(4) by (force simp add: tstp_lt_def split: sum.splits)
  have lookup_a2_map'_keys: "\<forall>tp' \<in> Mapping.keys a2_map'.
    case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> table n R (Mapping.keys m) \<and>
    (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
    tstp_lt tstp (nt - (left I - 1)) (tp + 1) \<and> isl tstp = (0 < left I))"
  proof (rule ballI)
    fix tp'
    assume tp'_assm: "tp' \<in> Mapping.keys a2_map'"
    then obtain m' where m'_def: "Mapping.lookup a2_map' tp' = Some m'"
      by (auto dest: Mapping_keys_dest)
    have "table n R (Mapping.keys m') \<and>
      (\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
      tstp_lt tstp (nt - (left I - 1)) (tp + 1) \<and> isl tstp = (0 < left I))"
    proof (cases "tp' = tp + 1")
      case True
      show ?thesis
        using m'_def unfolding a2_map'_def True Mapping.lookup_update
        by (auto simp add: table_def)
    next
      case False
      then have tp'_in: "tp' \<in> Mapping.keys a2_map"
        using tp'_assm unfolding a2_map_keys a2_map'_keys by auto
      then obtain m where m_def: "Mapping.lookup a2_map tp' = Some m"
        by (auto dest: Mapping_keys_dest)
      have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp}"
        using m_def m'_def unfolding a2_map'_def Mapping.lookup_update_neq[OF False[symmetric]]
          upd_nested_lookup
        by auto
      have "table n R (Mapping.keys m')"
        using lookup_a2_map[OF m_def] snd_tmp unfolding m'_alt upd_set'_keys
        by (auto simp add: table_def)
      moreover have "\<forall>xs \<in> Mapping.keys m'. case Mapping.lookup m' xs of Some tstp \<Rightarrow>
        tstp_lt tstp (nt - (left I - 1)) (tp + 1) \<and> isl tstp = (0 < left I)"
      proof (rule ballI)
        fix xs
        assume xs_assm: "xs \<in> Mapping.keys m'"
        then obtain tstp where tstp_def: "Mapping.lookup m' xs = Some tstp"
          by (auto dest: Mapping_keys_dest)
        have "tstp_lt tstp (nt - (left I - 1)) (tp + 1) \<and> isl tstp = (0 < left I)"
        proof (cases "Mapping.lookup m xs")
          case None
          then show ?thesis
            using tstp_def[unfolded m'_alt upd_set'_lookup] new_tstp_lt_isl
            by (auto split: if_splits)
        next
          case (Some tstp')
          show ?thesis
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using tstp_def[unfolded m'_alt upd_set'_lookup] Some
              by auto
            show ?thesis
              using lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
              by (auto simp add: tstp_lt_def tstp_eq split: sum.splits)
          next
            case False
            then show ?thesis
              using tstp_def[unfolded m'_alt upd_set'_lookup] lookup_a2_map'[OF m_def Some] Some
              by (auto simp add: tstp_lt_def split: sum.splits)
          qed
        qed
        then show "case Mapping.lookup m' xs of Some tstp \<Rightarrow>
          tstp_lt tstp (nt - (left I - 1)) (tp + 1) \<and> isl tstp = (0 < left I)"
          using tstp_def by auto
      qed
      ultimately show ?thesis
        by auto
    qed
    then show "case Mapping.lookup a2_map' tp' of Some m \<Rightarrow> table n R (Mapping.keys m) \<and>
      (\<forall>xs \<in> Mapping.keys m. case Mapping.lookup m xs of Some tstp \<Rightarrow>
      tstp_lt tstp (nt - (left I - 1)) (tp + 1) \<and> isl tstp = (0 < left I))"
      using m'_def by auto
  qed
  have tp_upt_Suc: "[tp + 1 - (len + 1)..<tp + 1] = [tp - len..<tp] @ [tp]"
    using upt_Suc by auto
  have map_eq: "map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem (nt - t) I then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist) =
    map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if left I \<le> nt - t then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist)"
    using set_drop_auxlist_cong by auto
  have "drop (length done) (update_until args rel1 rel2 nt auxlist) =
    map (\<lambda>x. case x of (t, a1, a2) \<Rightarrow> (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if mem (nt - t) I then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist) @
    [(nt, rel1, if left I = 0 then rel2 else empty_table)]"
    unfolding update_until_eq using len_done_auxlist drop_map by auto
  note drop_update_until = this[unfolded map_eq]
  have list_all2_old: "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map')
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'))
    (map (\<lambda>(t, a1, a2). (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if left I \<le> nt - t then a2 \<union> join rel2 pos a1 else a2)) (drop (length done) auxlist))
    (zip (linearize tss) [tp - len..<tp])"
    unfolding list_all2_map1
    using list_all2_triple
  proof (rule list.rel_mono_strong)
    fix tri pair
    assume tri_pair_in: "tri \<in> set (drop (length done) auxlist)"
      "pair \<in> set (zip (linearize tss) [tp - len..<tp])"
    obtain t a1 a2 where tri_def: "tri = (t, a1, a2)"
      by (cases tri) auto
    obtain ts' tp' where pair_def: "pair = (ts', tp')"
      by (cases pair) auto
    assume "triple_eq_pair tri pair (\<lambda>tp'. filter_a1_map pos tp' a1_map)
      (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map)"
    then have eqs: "t = ts'" "a1 = filter_a1_map pos tp' a1_map"
      "a2 = filter_a2_map I ts' tp' a2_map"
      unfolding tri_def pair_def by auto
    have tp'_ge: "tp' \<ge> tp - len"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    have tp'_lt_tp: "tp' < tp"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    have ts'_in_lin_tss: "ts' \<in> set (linearize tss)"
      using tri_pair_in(2) unfolding pair_def
      by (auto elim: in_set_zipE)
    then have ts'_nt: "ts' \<le> nt"
      using valid_shift_aux(1) assms(4) by auto
    then have t_nt: "t \<le> nt"
      unfolding eqs(1) .
    have "table n L (Mapping.keys a1_map)"
      using valid_shift_aux unfolding n_def L_def by auto
    then have a1_tab: "table n L a1"
      unfolding eqs(2) filter_a1_map_def by (auto simp add: table_def)
    note tabR = tabs(2)[unfolded n_def[symmetric] R_def[symmetric]]
    have join_rel2_assms: "L \<subseteq> R" "maskL = join_mask n L"
      using valid_shift_aux unfolding n_def L_def R_def by auto
    have join_rel2_eq: "join rel2 pos a1 = {xs \<in> rel2. proj_tuple_in_join pos maskL xs a1}"
      using join_sub[OF join_rel2_assms(1) a1_tab tabR] join_rel2_assms(2) by auto
    have filter_sub_a2: "\<And>xs m' tp'' tstp. tp'' \<le> tp' \<Longrightarrow>
      Mapping.lookup a2_map' tp'' = Some m' \<Longrightarrow> Mapping.lookup m' xs = Some tstp \<Longrightarrow>
      ts_tp_lt' ts' tp' tstp \<Longrightarrow> (tstp = new_tstp \<Longrightarrow> False) \<Longrightarrow>
      xs \<in> filter_a2_map I ts' tp' a2_map' \<Longrightarrow> xs \<in> a2"
    proof -
      fix xs m' tp'' tstp
      assume m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt' ts' tp' tstp"
      have tp''_neq: "tp + 1 \<noteq> tp''"
        using le_less_trans[OF m'_def(1) tp'_lt_tp] by auto
      assume new_tstp_False: "tstp = new_tstp \<Longrightarrow> False"
      show "xs \<in> a2"
      proof (cases "Mapping.lookup a2_map tp''")
        case None
        then have m'_alt: "m' = upd_set' Mapping.empty new_tstp (max_tstp new_tstp)
          {b. (tp'', b) \<in> tmp}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] by (auto split: option.splits if_splits)
        then show ?thesis
          using new_tstp_False m'_def(3)[unfolded m'_alt upd_set'_lookup Mapping.lookup_empty]
          by (auto split: if_splits)
      next
        case (Some m)
        then have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] by (auto split: option.splits if_splits)
        note lookup_m = Some
        show ?thesis
        proof (cases "Mapping.lookup m xs")
          case None
          then show ?thesis
            using new_tstp_False m'_def(3)[unfolded m'_alt upd_set'_lookup]
            by (auto split: if_splits)
        next
          case (Some tstp')
          have tstp_ok: "tstp = tstp' \<Longrightarrow> xs \<in> a2"
            using eqs(3) lookup_m Some m'_def unfolding filter_a2_map_def by auto
          show ?thesis
          proof (cases "xs \<in> {b. (tp'', b) \<in> tmp}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using m'_def(3)[unfolded m'_alt upd_set'_lookup Some] by auto
            show ?thesis
              using lookup_a2_map'[OF lookup_m Some] new_tstp_lt_isl(2)
                tstp_eq new_tstp_False tstp_ok
              by (auto intro: max_tstpE[of new_tstp tstp'])
          next
            case False
            then have "tstp = tstp'"
              using m'_def(3)[unfolded m'_alt upd_set'_lookup Some] by auto
            then show ?thesis
              using tstp_ok by auto
          qed
        qed
      qed
    qed
    have a2_sub_filter: "a2 \<subseteq> filter_a2_map I ts' tp' a2_map'"
    proof (rule subsetI)
      fix xs
      assume xs_in: "xs \<in> a2"
      then obtain tp'' m tstp where m_def: "tp'' \<le> tp'" "Mapping.lookup a2_map tp'' = Some m"
        "Mapping.lookup m xs = Some tstp" "ts_tp_lt' ts' tp' tstp"
        using eqs(3)[unfolded filter_a2_map_def] by (auto split: option.splits)
      have tp''_in: "tp'' \<in> {tp - len..tp}"
        using m_def(2) a2_map_keys by (auto intro!: Mapping_keys_intro)
      then obtain m' where m'_def: "Mapping.lookup a2_map' tp'' = Some m'"
        using a2_map'_keys
        by (metis Mapping_keys_dest One_nat_def add_Suc_right add_diff_cancel_right'
            atLeastatMost_subset_iff diff_zero le_eq_less_or_eq le_less_Suc_eq subsetD)
      have tp''_neq: "tp + 1 \<noteq> tp''"
        using m_def(1) tp'_lt_tp by auto
      have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp}"
        using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq] m_def(2)
          upd_nested_lookup] by (auto split: option.splits if_splits)
      show "xs \<in> filter_a2_map I ts' tp' a2_map'"
      proof (cases "xs \<in> {b. (tp'', b) \<in> tmp}")
        case True
        then have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp)"
          unfolding m'_alt upd_set'_lookup m_def(3) by auto
        moreover have "ts_tp_lt' ts' tp' (max_tstp new_tstp tstp)"
          using new_tstp_lt_isl(2) lookup_a2_map'[OF m_def(2,3)]
          by (auto intro: max_tstp_intro''''[OF _ m_def(4)])
        ultimately show ?thesis
          unfolding filter_a2_map_def using m_def(1) m'_def m_def(4) by auto
      next
        case False
        then have "Mapping.lookup m' xs = Some tstp"
          unfolding m'_alt upd_set'_lookup m_def(3) by auto
        then show ?thesis
          unfolding filter_a2_map_def using m_def(1) m'_def m_def by auto
      qed
    qed
    have "pos \<Longrightarrow> filter_a1_map pos tp' a1_map' = join a1 True rel1"
    proof -
      assume pos: pos
      note tabL = tabs(1)[unfolded n_def[symmetric] L_def[symmetric]]
      have join_eq: "join a1 True rel1 = a1 \<inter> rel1"
        using join_eq[OF tabL a1_tab] by auto
      show "filter_a1_map pos tp' a1_map' = join a1 True rel1"
        using eqs(2) pos tp'_lt_tp unfolding filter_a1_map_def a1_map'_def join_eq
        by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set split: if_splits option.splits
            intro: Mapping_keys_intro dest: Mapping_keys_dest Mapping_keys_filterD)
    qed
    moreover have "\<not>pos \<Longrightarrow> filter_a1_map pos tp' a1_map' = a1 \<union> rel1"
      using eqs(2) tp'_lt_tp unfolding filter_a1_map_def a1_map'_def
      by (auto simp add: Mapping.lookup_filter Mapping_lookup_upd_set intro: Mapping_keys_intro
          dest: Mapping_keys_filterD Mapping_keys_dest split: option.splits)
    moreover have "left I \<le> nt - t \<Longrightarrow> filter_a2_map I ts' tp' a2_map' = a2 \<union> join rel2 pos a1"
    proof (rule set_eqI, rule iffI)
      fix xs
      assume in_int: "left I \<le> nt - t"
      assume xs_in: "xs \<in> filter_a2_map I ts' tp' a2_map'"
      then obtain m' tp'' tstp where m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt' ts' tp' tstp"
        unfolding filter_a2_map_def by (fastforce split: option.splits)
      show "xs \<in> a2 \<union> join rel2 pos a1"
      proof (cases "tstp = new_tstp")
        case True
        note tstp_new_tstp = True
        have tp''_neq: "tp + 1 \<noteq> tp''"
          using m'_def(1) tp'_lt_tp by auto
        have tp''_in: "tp'' \<in> {tp - len..tp}"
          using m'_def(1,2) tp'_lt_tp a2_map'_keys
          by (auto intro!: Mapping_keys_intro)
        obtain m where m_def: "Mapping.lookup a2_map tp'' = Some m"
          "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp'', b) \<in> tmp}"
          using m'_def(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp''_neq]
            upd_nested_lookup] tp''_in a2_map_keys
          by (fastforce dest: Mapping_keys_dest split: option.splits if_splits)
        show ?thesis
        proof (cases "Mapping.lookup m xs = Some new_tstp")
          case True
          then show ?thesis
            using eqs(3) m'_def(1) m_def(1) m'_def tstp_new_tstp
            unfolding filter_a2_map_def by auto
        next
          case False
          then have xs_in_snd_tmp: "xs \<in> {b. (tp'', b) \<in> tmp}"
            using m'_def(3)[unfolded m_def(2) upd_set'_lookup True]
            by (auto split: if_splits)
          then have xs_in_rel2: "xs \<in> rel2"
            unfolding tmp_def
            by (auto split: if_splits option.splits)
          show ?thesis
          proof (cases pos)
            case True
            obtain tp''' where tp'''_def: "Mapping.lookup a1_map (proj_tuple maskL xs) = Some tp'''"
              "if pos then tp'' = max (tp - len) tp''' else tp'' = max (tp - len) (tp''' + 1)"
              using xs_in_snd_tmp m'_def(1) tp'_lt_tp True
              unfolding tmp_def by (auto split: option.splits if_splits)
            have "proj_tuple maskL xs \<in> a1"
              using eqs(2)[unfolded filter_a1_map_def] True m'_def(1) tp'''_def
              by (auto intro: Mapping_keys_intro)
            then show ?thesis
              using True xs_in_rel2 unfolding proj_tuple_in_join_def join_rel2_eq by auto
          next
            case False
            show ?thesis
            proof (cases "Mapping.lookup a1_map (proj_tuple maskL xs)")
              case None
              then show ?thesis
                using xs_in_rel2 False eqs(2)[unfolded filter_a1_map_def]
                unfolding proj_tuple_in_join_def join_rel2_eq
                by (auto dest: Mapping_keys_dest)
            next
              case (Some tp''')
              then have "tp'' = max (tp - len) (tp''' + 1)"
                using xs_in_snd_tmp m'_def(1) tp'_lt_tp False
                unfolding tmp_def by (auto split: option.splits if_splits)
              then have "tp''' < tp'"
                using m'_def(1) by auto
              then have "proj_tuple maskL xs \<notin> a1"
                using eqs(2)[unfolded filter_a1_map_def] True m'_def(1) Some False
                by (auto intro: Mapping_keys_intro)
              then show ?thesis
                using xs_in_rel2 False unfolding proj_tuple_in_join_def join_rel2_eq by auto
            qed
          qed
        qed
      next
        case False
        then show ?thesis
          using filter_sub_a2[OF m'_def _ xs_in] by auto
      qed
    next
      fix xs
      assume in_int: "left I \<le> nt - t"
      assume xs_in: "xs \<in> a2 \<union> join rel2 pos a1"
      then have "xs \<in> a2 \<union> (join rel2 pos a1 - a2)"
        by auto
      then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
      proof (rule UnE)
        assume "xs \<in> a2"
        then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
          using a2_sub_filter by auto
      next
        assume "xs \<in> join rel2 pos a1 - a2"
        then have xs_props: "xs \<in> rel2" "xs \<notin> a2" "proj_tuple_in_join pos maskL xs a1"
          unfolding join_rel2_eq by auto
        have ts_tp_lt'_new_tstp: "ts_tp_lt' ts' tp' new_tstp"
          using tp'_lt_tp in_int t_nt eqs(1) unfolding new_tstp_def
          by (auto simp add: ts_tp_lt'_def)
        show "xs \<in> filter_a2_map I ts' tp' a2_map'"
        proof (cases pos)
          case True
          then obtain tp''' where tp'''_def: "tp''' \<le> tp'"
            "Mapping.lookup a1_map (proj_tuple maskL xs) = Some tp'''"
            using eqs(2)[unfolded filter_a1_map_def] xs_props(3)[unfolded proj_tuple_in_join_def]
            by (auto dest: Mapping_keys_dest)
          define wtp where "wtp \<equiv> max (tp - len) tp'''"
          have wtp_xs_in: "(wtp, xs) \<in> tmp"
            unfolding wtp_def using tp'''_def tmp_def xs_props(1) True by fastforce
          have wtp_le: "wtp \<le> tp'"
            using tp'''_def(1) tp'_ge unfolding wtp_def by auto
          have wtp_in: "wtp \<in> {tp - len..tp}"
            using tp'''_def(1) tp'_lt_tp unfolding wtp_def by auto
          have wtp_neq: "tp + 1 \<noteq> wtp"
            using wtp_in by auto
          obtain m where m_def: "Mapping.lookup a2_map wtp = Some m"
            using wtp_in a2_map_keys Mapping_keys_dest by fastforce
          obtain m' where m'_def: "Mapping.lookup a2_map' wtp = Some m'"
            using wtp_in a2_map'_keys Mapping_keys_dest by fastforce
          have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (wtp, b) \<in> tmp}"
            using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF wtp_neq]
              upd_nested_lookup m_def] by auto
          show ?thesis
          proof (cases "Mapping.lookup m xs")
            case None
            have "Mapping.lookup m' xs = Some new_tstp"
              using wtp_xs_in unfolding m'_alt upd_set'_lookup None by auto
            then show ?thesis
              unfolding filter_a2_map_def using wtp_le m'_def ts_tp_lt'_new_tstp by auto
          next
            case (Some tstp')
            have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
              using wtp_xs_in unfolding m'_alt upd_set'_lookup Some by auto
            moreover have "ts_tp_lt' ts' tp' (max_tstp new_tstp tstp')"
              using max_tstp_intro''' ts_tp_lt'_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
              by auto
            ultimately show ?thesis
              using lookup_a2_map'[OF m_def Some] wtp_le m'_def
              unfolding filter_a2_map_def by auto
          qed
        next
          case False
          show ?thesis
          proof (cases "Mapping.lookup a1_map (proj_tuple maskL xs)")
            case None
            then have in_tmp: "(tp - len, xs) \<in> tmp"
              using tmp_def False xs_props(1) by fastforce
            obtain m where m_def: "Mapping.lookup a2_map (tp - len) = Some m"
              using a2_map_keys by (fastforce dest: Mapping_keys_dest)
            obtain m' where m'_def: "Mapping.lookup a2_map' (tp - len) = Some m'"
              using a2_map'_keys by (fastforce dest: Mapping_keys_dest)
            have tp_neq: "tp + 1 \<noteq> tp - len"
              by auto
            have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp - len, b) \<in> tmp}"
              using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp_neq]
                upd_nested_lookup m_def] by auto
            show ?thesis
            proof (cases "Mapping.lookup m xs")
              case None
              have "Mapping.lookup m' xs = Some new_tstp"
                unfolding m'_alt upd_set'_lookup None using in_tmp by auto
              then show ?thesis
                unfolding filter_a2_map_def using tp'_ge m'_def ts_tp_lt'_new_tstp by auto
            next
              case (Some tstp')
              have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
                unfolding m'_alt upd_set'_lookup Some using in_tmp by auto
              moreover have "ts_tp_lt' ts' tp' (max_tstp new_tstp tstp')"
                using max_tstp_intro''' ts_tp_lt'_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
                by auto
              ultimately show ?thesis
                unfolding filter_a2_map_def using tp'_ge m'_def by auto
            qed
          next
            case (Some tp''')
            then have tp'_gt: "tp' > tp'''"
              using xs_props(3)[unfolded proj_tuple_in_join_def] eqs(2)[unfolded filter_a1_map_def]
                False by (auto intro: Mapping_keys_intro)
            define wtp where "wtp \<equiv> max (tp - len) (tp''' + 1)"
            have wtp_xs_in: "(wtp, xs) \<in> tmp"
              unfolding wtp_def tmp_def using xs_props(1) Some False by fastforce
            have wtp_le: "wtp \<le> tp'"
              using tp'_ge tp'_gt unfolding wtp_def by auto
            have wtp_in: "wtp \<in> {tp - len..tp}"
              using tp'_lt_tp tp'_gt unfolding wtp_def by auto
            have wtp_neq: "tp + 1 \<noteq> wtp"
              using wtp_in by auto
            obtain m where m_def: "Mapping.lookup a2_map wtp = Some m"
              using wtp_in a2_map_keys Mapping_keys_dest by fastforce
            obtain m' where m'_def: "Mapping.lookup a2_map' wtp = Some m'"
              using wtp_in a2_map'_keys Mapping_keys_dest by fastforce
            have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (wtp, b) \<in> tmp}"
              using m'_def[unfolded a2_map'_def Mapping.lookup_update_neq[OF wtp_neq]
                upd_nested_lookup m_def] by auto
            show ?thesis
            proof (cases "Mapping.lookup m xs")
              case None
              have "Mapping.lookup m' xs = Some new_tstp"
                using wtp_xs_in unfolding m'_alt upd_set'_lookup None by auto
              then show ?thesis
                unfolding filter_a2_map_def using wtp_le m'_def ts_tp_lt'_new_tstp by auto
            next
              case (Some tstp')
              have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
                using wtp_xs_in unfolding m'_alt upd_set'_lookup Some by auto
              moreover have "ts_tp_lt' ts' tp' (max_tstp new_tstp tstp')"
                using max_tstp_intro''' ts_tp_lt'_new_tstp lookup_a2_map'[OF m_def Some] new_tstp_lt_isl
                by auto
              ultimately show ?thesis
                using lookup_a2_map'[OF m_def Some] wtp_le m'_def
                unfolding filter_a2_map_def by auto
            qed
          qed
        qed
      qed
    qed
    moreover have "nt - t < left I \<Longrightarrow> filter_a2_map I ts' tp' a2_map' = a2"
    proof (rule set_eqI, rule iffI)
      fix xs
      assume out: "nt - t < left I"
      assume xs_in: "xs \<in> filter_a2_map I ts' tp' a2_map'"
      then obtain m' tp'' tstp where m'_def: "tp'' \<le> tp'" "Mapping.lookup a2_map' tp'' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt' ts' tp' tstp"
        unfolding filter_a2_map_def by (fastforce split: option.splits)
      have new_tstp_False: "tstp = new_tstp \<Longrightarrow> False"
        using m'_def t_nt out tp'_lt_tp unfolding eqs(1)
        by (auto simp add: ts_tp_lt'_def new_tstp_def)
      show "xs \<in> a2"
        using filter_sub_a2[OF m'_def new_tstp_False xs_in] .
    next
      fix xs
      assume "xs \<in> a2"
      then show "xs \<in> filter_a2_map I ts' tp' a2_map'"
        using a2_sub_filter by auto
    qed
    ultimately show "triple_eq_pair (case tri of (t, a1, a2) \<Rightarrow>
      (t, if pos then join a1 True rel1 else a1 \<union> rel1,
      if left I \<le> nt - t then a2 \<union> join rel2 pos a1 else a2))
      pair (\<lambda>tp'. filter_a1_map pos tp' a1_map') (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map')"
      using eqs unfolding tri_def pair_def by auto
  qed
  have filter_a1_map_rel1: "filter_a1_map pos tp a1_map' = rel1"
    unfolding filter_a1_map_def a1_map'_def using leD lookup_a1_map_keys
    by (force simp add: a1_map_lookup less_imp_le_nat Mapping.lookup_filter
        Mapping_lookup_upd_set keys_is_none_rep dest: Mapping_keys_filterD
        intro: Mapping_keys_intro split: option.splits)
  have filter_a1_map_rel2: "filter_a2_map I nt tp a2_map' =
    (if left I = 0 then rel2 else empty_table)"
  proof (cases "left I = 0")
    case True
    note left_I_zero = True
    have "\<And>tp' m' xs tstp. tp' \<le> tp \<Longrightarrow> Mapping.lookup a2_map' tp' = Some m' \<Longrightarrow>
      Mapping.lookup m' xs = Some tstp \<Longrightarrow> ts_tp_lt' nt tp tstp \<Longrightarrow> xs \<in> rel2"
    proof -
      fix tp' m' xs tstp
      assume lassms: "tp' \<le> tp" "Mapping.lookup a2_map' tp' = Some m'"
        "Mapping.lookup m' xs = Some tstp" "ts_tp_lt' nt tp tstp"
      have tp'_neq: "tp + 1 \<noteq> tp'"
        using lassms(1) by auto
      have tp'_in: "tp' \<in> {tp - len..tp}"
        using lassms(1,2) a2_map'_keys tp'_neq by (auto intro!: Mapping_keys_intro)
      obtain m where m_def: "Mapping.lookup a2_map tp' = Some m"
        "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp}"
        using lassms(2)[unfolded a2_map'_def Mapping.lookup_update_neq[OF tp'_neq]
          upd_nested_lookup] tp'_in a2_map_keys
        by (fastforce dest: Mapping_keys_dest intro: Mapping_keys_intro split: option.splits)
      have "xs \<in> {b. (tp', b) \<in> tmp}"
      proof (rule ccontr)
        assume "xs \<notin> {b. (tp', b) \<in> tmp}"
        then have Some: "Mapping.lookup m xs = Some tstp"
          using lassms(3)[unfolded m_def(2) upd_set'_lookup] by auto
        show "False"
          using lookup_a2_map'[OF m_def(1) Some] lassms(4)
          by (auto simp add: tstp_lt_def ts_tp_lt'_def split: sum.splits)
      qed
      then show "xs \<in> rel2"
        unfolding tmp_def by (auto split: option.splits if_splits)
    qed
    moreover have "\<And>xs. xs \<in> rel2 \<Longrightarrow> \<exists>m' tstp. Mapping.lookup a2_map' tp = Some m' \<and>
      Mapping.lookup m' xs = Some tstp \<and> ts_tp_lt' nt tp tstp"
    proof -
      fix xs
      assume lassms: "xs \<in> rel2"
      obtain m' where m'_def: "Mapping.lookup a2_map' tp = Some m'"
        using a2_map'_keys by (fastforce dest: Mapping_keys_dest)
      have tp_neq: "tp + 1 \<noteq> tp"
        by auto
      obtain m where m_def: "Mapping.lookup a2_map tp = Some m"
        "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp, b) \<in> tmp}"
        using m'_def a2_map_keys unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq]
          upd_nested_lookup
        by (auto dest: Mapping_keys_dest split: option.splits if_splits)
           (metis Mapping_keys_dest atLeastAtMost_iff diff_le_self le_eq_less_or_eq
            option.simps(3))
      have xs_in_tmp: "xs \<in> {b. (tp, b) \<in> tmp}"
        using lassms left_I_zero unfolding tmp_def by auto
      show "\<exists>m' tstp. Mapping.lookup a2_map' tp = Some m' \<and>
        Mapping.lookup m' xs = Some tstp \<and> ts_tp_lt' nt tp tstp"
      proof (cases "Mapping.lookup m xs")
        case None
        moreover have "Mapping.lookup m' xs = Some new_tstp"
          using xs_in_tmp unfolding m_def(2) upd_set'_lookup None by auto
        moreover have "ts_tp_lt' nt tp new_tstp"
          using left_I_zero new_tstp_def by (auto simp add: ts_tp_lt'_def)
        ultimately show ?thesis
          using xs_in_tmp m_def
          unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup by auto
      next
        case (Some tstp')
        moreover have "Mapping.lookup m' xs = Some (max_tstp new_tstp tstp')"
          using xs_in_tmp unfolding m_def(2) upd_set'_lookup Some by auto
        moreover have "ts_tp_lt' nt tp (max_tstp new_tstp tstp')"
          using max_tstpE[of new_tstp tstp'] lookup_a2_map'[OF m_def(1) Some] new_tstp_lt_isl left_I_zero
          by (auto simp add: sum.discI(1) new_tstp_def ts_tp_lt'_def tstp_lt_def split: sum.splits)
        ultimately show ?thesis
          using xs_in_tmp m_def
          unfolding a2_map'_def Mapping.lookup_update_neq[OF tp_neq] upd_nested_lookup by auto
      qed
    qed
    ultimately show ?thesis
      using True by (fastforce simp add: filter_a2_map_def split: option.splits)
  next
    case False
    note left_I_pos = False
    have "\<And>tp' m xs tstp. tp' \<le> tp \<Longrightarrow> Mapping.lookup a2_map' tp' = Some m \<Longrightarrow>
      Mapping.lookup m xs = Some tstp \<Longrightarrow> \<not>(ts_tp_lt' nt tp tstp)"
    proof -
      fix tp' m' xs tstp
      assume lassms: "tp' \<le> tp" "Mapping.lookup a2_map' tp' = Some m'"
        "Mapping.lookup m' xs = Some tstp"
      from lassms(1) have tp'_neq_Suc_tp: "tp + 1 \<noteq> tp'"
        by auto
      show "\<not>(ts_tp_lt' nt tp tstp)"
      proof (cases "Mapping.lookup a2_map tp'")
        case None
        then have tp'_in_tmp: "tp' \<in> fst ` tmp" and
          m'_alt: "m' = upd_set' Mapping.empty new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp}"
          using lassms(2) unfolding a2_map'_def Mapping.lookup_update_neq[OF tp'_neq_Suc_tp]
            upd_nested_lookup by (auto split: if_splits)
        then have "tstp = new_tstp"
          using lassms(3)[unfolded m'_alt upd_set'_lookup]
          by (auto simp add: Mapping.lookup_empty split: if_splits)
        then show ?thesis
          using False by (auto simp add: ts_tp_lt'_def new_tstp_def split: if_splits sum.splits)
      next
        case (Some m)
        then have m'_alt: "m' = upd_set' m new_tstp (max_tstp new_tstp) {b. (tp', b) \<in> tmp}"
          using lassms(2) unfolding a2_map'_def Mapping.lookup_update_neq[OF tp'_neq_Suc_tp]
            upd_nested_lookup by auto
        note lookup_a2_map_tp' = Some
        show ?thesis
        proof (cases "Mapping.lookup m xs")
          case None
          then have "tstp = new_tstp"
            using lassms(3) unfolding m'_alt upd_set'_lookup by (auto split: if_splits)
          then show ?thesis
            using False by (auto simp add: ts_tp_lt'_def new_tstp_def split: if_splits sum.splits)
        next
          case (Some tstp')
          show ?thesis
          proof (cases "xs \<in> {b. (tp', b) \<in> tmp}")
            case True
            then have tstp_eq: "tstp = max_tstp new_tstp tstp'"
              using lassms(3)
              unfolding m'_alt upd_set'_lookup Some by auto
            show ?thesis
              using max_tstpE[of new_tstp tstp'] lookup_a2_map'[OF lookup_a2_map_tp' Some] new_tstp_lt_isl left_I_pos
              by (auto simp add: tstp_eq tstp_lt_def ts_tp_lt'_def split: sum.splits)
          next
            case False
            then show ?thesis
              using lassms(3) lookup_a2_map'[OF lookup_a2_map_tp' Some]
              unfolding m'_alt upd_set'_lookup Some
              by (auto simp add: ts_tp_lt'_def tstp_lt_def split: sum.splits)
          qed
        qed
      qed
    qed
    then show ?thesis
      using False by (auto simp add: filter_a2_map_def empty_table_def split: option.splits)
  qed
  have zip_dist: "zip (linearize tss @ [nt]) ([tp - len..<tp] @ [tp]) =
    zip (linearize tss) [tp - len..<tp] @ [(nt, tp)]"
    using valid_shift_aux(1) by auto
  have list_all2': "list_all2 (\<lambda>x y. triple_eq_pair x y (\<lambda>tp'. filter_a1_map pos tp' a1_map')
    (\<lambda>ts' tp'. filter_a2_map I ts' tp' a2_map'))
    (drop (length done) (update_until args rel1 rel2 nt auxlist))
    (zip (linearize tss') [tp + 1 - (len + 1)..<tp + 1])"
    unfolding lin_tss' tp_upt_Suc drop_update_until zip_dist
    using filter_a1_map_rel1 filter_a1_map_rel2 list_all2_appendI[OF list_all2_old]
    by auto
  show ?thesis
    using valid_shift_aux len_lin_tss' sorted_lin_tss' set_lin_tss' tab_a1_map'_keys a2_map'_keys'
      len_upd_until sorted_upd_until lookup_a1_map_keys' rev_done' set_take_auxlist'
      lookup_a2_map'_keys list_all2'
    unfolding valid_mmuaux_def add_new_mmuaux_eq valid_mmuaux'.simps
      I_def n_def L_def R_def pos_def by auto
qed

lemma list_all2_check_before: "list_all2 (\<lambda>x y. triple_eq_pair x y f g) xs (zip ys zs) \<Longrightarrow>
  (\<And>y. y \<in> set ys \<Longrightarrow> \<not>enat y + right I < nt) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<not>check_before I nt x"
  by (auto simp: in_set_zip elim!: list_all2_in_setE triple_eq_pair.elims)

fun eval_mmuaux :: "args \<Rightarrow> ts \<Rightarrow> 'a mmuaux \<Rightarrow> 'a table list \<times> 'a mmuaux" where
  "eval_mmuaux args nt aux =
    (let (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    shift_mmuaux args nt aux in
    (rev done, (tp, tss, len, maskL, maskR, a1_map, a2_map, [], 0)))"

lemma valid_eval_mmuaux:
  assumes "valid_mmuaux args cur aux auxlist" "nt \<ge> cur"
    "eval_mmuaux args nt aux = (res, aux')" "eval_until (args_ivl args) nt auxlist = (res', auxlist')"
  shows "res = res' \<and> valid_mmuaux args cur aux' auxlist'"
proof -
  define I where "I = args_ivl args"
  define pos where "pos = args_pos args"
  have valid_folded: "valid_mmuaux' args cur nt aux auxlist"
    using assms(1,2) valid_mmuaux'_mono unfolding valid_mmuaux_def by blast
  obtain tp len tss maskL maskR a1_map a2_map "done" done_length where shift_aux_def:
    "shift_mmuaux args nt aux = (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length)"
    by (cases "shift_mmuaux args nt aux") auto
  have valid_shift_aux: "valid_mmuaux' args cur nt (tp, tss, len, maskL, maskR,
    a1_map, a2_map, done, done_length) auxlist"
    "\<And>ts. ts \<in> set (linearize tss) \<Longrightarrow> \<not>enat ts + right (args_ivl args) < enat nt"
    using valid_shift_mmuaux'[OF assms(1)[unfolded valid_mmuaux_def] assms(2)]
    unfolding shift_aux_def by auto
  have len_done_auxlist: "length done \<le> length auxlist"
    using valid_shift_aux by auto
  have list_all: "\<And>x. x \<in> set (take (length done) auxlist) \<Longrightarrow> check_before I nt x"
    using valid_shift_aux unfolding I_def by auto
  have set_drop_auxlist: "\<And>x. x \<in> set (drop (length done) auxlist) \<Longrightarrow> \<not>check_before I nt x"
    using valid_shift_aux[unfolded valid_mmuaux'.simps]
      list_all2_check_before[OF _ valid_shift_aux(2)] unfolding I_def by fast
  have take_auxlist_takeWhile: "take (length done) auxlist = takeWhile (check_before I nt) auxlist"
    using len_done_auxlist list_all set_drop_auxlist
    by (rule take_takeWhile) assumption+
  have rev_done: "rev done = map proj_thd (take (length done) auxlist)"
    using valid_shift_aux by auto
  then have res'_def: "res' = rev done"
    using eval_until_res[OF assms(4)] unfolding take_auxlist_takeWhile I_def by auto
  then have auxlist'_def: "auxlist' = drop (length done) auxlist"
    using eval_until_auxlist'[OF assms(4)] by auto
  have eval_mmuaux_eq: "eval_mmuaux args nt aux = (rev done, (tp, tss, len, maskL, maskR,
    a1_map, a2_map, [], 0))"
    using shift_aux_def by auto
  show ?thesis
    using assms(3) done_empty_valid_mmuaux'_intro[OF valid_shift_aux(1)]
    unfolding shift_aux_def eval_mmuaux_eq pos_def auxlist'_def res'_def valid_mmuaux_def by auto
qed

definition init_mmuaux :: "args \<Rightarrow> 'a mmuaux" where
  "init_mmuaux args = (0, empty_queue, 0,
  join_mask (args_n args) (args_L args), join_mask (args_n args) (args_R args),
  Mapping.empty, Mapping.update 0 Mapping.empty Mapping.empty, [], 0)"

lemma valid_init_mmuaux: "L \<subseteq> R \<Longrightarrow> valid_mmuaux (init_args I n L R b) 0
  (init_mmuaux (init_args I n L R b)) []"
  unfolding init_mmuaux_def valid_mmuaux_def
  by (auto simp add: init_args_def empty_queue_rep table_def Mapping.lookup_update)

fun length_mmuaux :: "args \<Rightarrow> 'a mmuaux \<Rightarrow> nat" where
  "length_mmuaux args (tp, tss, len, maskL, maskR, a1_map, a2_map, done, done_length) =
    len + done_length"

lemma valid_length_mmuaux:
  assumes "valid_mmuaux args cur aux auxlist"
  shows "length_mmuaux args aux = length auxlist"
  using assms by (cases aux) (auto simp add: valid_mmuaux_def dest: list_all2_lengthD)

end