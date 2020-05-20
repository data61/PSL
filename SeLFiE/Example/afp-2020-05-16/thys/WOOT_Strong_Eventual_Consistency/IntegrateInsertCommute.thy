subsection \<open>Termination Proof for @{term integrate_insert}\label{sec:integrate_term}\<close>

theory IntegrateInsertCommute
  imports IntegrateAlgorithm Consistency CreateConsistent
begin

text \<open>In the following we show that @{term integrate_insert} terminates. Note that, this does not
  yet imply that the return value will not be an error state.\<close>

lemma substr_simp [simp]: "substr s l u = nths s {k. l < Suc k \<and> Suc k < u}"
proof (cases "l \<le> length s")
  case True
  have "set (nths (take l s) {k. l < Suc k \<and> Suc k < u}) = {}" 
    by (simp add:set_nths)
  hence "nths (take l s) {k. l < Suc k \<and> Suc k < u} = []" by blast
  moreover have "{j. Suc (j + l) < u} = {..<(u-Suc l)}" by auto
  moreover have "min (length s) l = l" using True by auto
  ultimately
    have "nths (take l s @ drop l s) {k. l < Suc k \<and> Suc k < u} = substr s l u"
    by (simp add:nths_append del:append_take_drop_id)
  then show ?thesis by simp
next
  case False
  hence "set (nths s {k. l < Suc k \<and> Suc k < u}) = {}"
    by (simp add:set_nths)
  hence "nths s {k. l < Suc k \<and> Suc k < u} = []" by blast
  thus ?thesis using False by simp
qed

declare substr.simps [simp del]

text \<open>Instead of simplifying @{term substr} with its definition we use @{thm [source] substr_simp}
  as a simplification rule. The right hand side of @{thm [source] substr_simp} is a better
  representation within proofs. However, we cannot directly define @{term substr} using the right
  hand side as it is not constructible term for Isabelle.\<close>

lemma int_ins_loop_term_1:
  assumes "isOK (mapM (concurrent w l u) t)"
  assumes "x \<in> set (concat (projr (mapM (concurrent w l u) t)))"
  shows "x \<in> (InString \<circ> I) ` (set t)"
  using assms
  by (induction t, simp, simp add: bind_simp del:idx.simps set_concat, blast)

lemma fromSingleton_simp: "(fromSingleton xs = Inr x) = ([x] = xs)"
  by (cases xs rule: fromSingleton.cases, auto)

lemma filt_simp: "([b] = filter p [0..<n]) =
   (p b \<and> b < n \<and> (\<forall>y < n. p y \<longrightarrow> b = y))" 
  apply (induction n, simp, simp) 
  by (metis atLeast_upt cancel_comm_monoid_add_class.diff_cancel 
      filter_empty_conv lessThan_iff less_Suc_eq neq0_conv zero_less_diff)

lemma substr_eff: 
  assumes "x \<in> (InString \<circ> I) ` set (substr w l u)"
  assumes "isOK (idx w x)"
  shows "l < (projr (idx w x)) \<and> (projr (idx w x)) < u"
proof -
  obtain i where i_def: "idx w x = Inr i" using assms(2) by blast
  then have "l < i \<and> i < u" using assms(1) 
    apply (simp add: set_nths image_iff fromSingleton_simp filt_simp)
    apply (simp add:ext_ids_def) 
    by (metis (no_types, lifting) Suc_mono length_map less_SucI list_update_id
        list_update_same_conv map_update nth_Cons_Suc nth_append)
  thus ?thesis using i_def by auto
qed

lemma find_zip:
  assumes "find (cond \<circ> snd) (zip (p#v) (v@[s])) = Some (x,y)" 
  assumes "v \<noteq> []"
  shows
    "cond y"
    "x \<in> set v \<or> y \<in> set v"
    "x = p \<or> (x \<in> set v \<and> \<not>(cond x))"
    "y = s \<or> (y \<in> set v)"
proof -
  obtain i where i_def:
    "i < Suc (length v)"
    "(zip (p#v) (v@[s])) ! i = (x,y)"
    "cond y"
    "\<forall>j. j < i \<longrightarrow> \<not>(cond ((v@[s])!j))"
    using assms apply (simp add:find_Some_iff) by force
  show "cond y" using i_def by auto
  show "x \<in> set v \<or> y \<in> set v" using assms(2) i_def(1,2)
    by (metis fst_conv in_set_conv_nth length_0_conv length_Cons length_append_singleton
        less_Suc_eq less_Suc_eq_0_disj nth_Cons_Suc nth_append nth_zip snd_conv)
  show "x = p \<or> (x \<in> set v \<and> (\<not>(cond x)))"
    apply (cases i)
    using i_def(2) apply auto[1]
    by (metis Suc_less_eq fst_conv i_def(1,2,4) length_Cons
        length_append_singleton lessI nth_Cons_Suc nth_append nth_mem nth_zip)
  show "y = s \<or> y \<in> set v"
    by (metis diff_is_0_eq' i_def(1,2) in_set_conv_nth length_Cons
        length_append_singleton less_Suc_eq_le nth_Cons_0 nth_append nth_zip snd_conv)
qed

fun int_ins_measure'
  where
    "int_ins_measure' (m,w,p,s) = (
      do {
        l \<leftarrow> idx w p;
        u \<leftarrow> idx w s;
        assert (l < u);
        return (u - l)
      })"

fun int_ins_measure
  where
    "int_ins_measure (m,w,p,s) = case_sum (\<lambda>e. 0) id (int_ins_measure' (m,w,p,s))"

text \<open>We show that during the iteration of @{term integrate_insert}, the arguments are decreasing
  with respect to @{term int_ins_measure}. Note, this means that the distance between the
  W-characters with identifiers @{term p} (resp. @{term s}) is decreasing.\<close>

lemma int_ins_loop_term:
  assumes "idx w p = Inr l"
  assumes "idx w s = Inr u"
  assumes "mapM (concurrent w l u) (substr w l u) = Inr d" 
  assumes "concat d \<noteq> []"
  assumes "find ((\<lambda>x.\<lbrakk>I m\<rbrakk> < x \<or> x = s) \<circ> snd) 
    (zip (p#concat d) (concat d@[s])) = Some r"
  shows "int_ins_measure (m, w, r) < u - l"
proof -
  have a: "\<And>x y. x \<in> set (concat d) \<Longrightarrow> idx w x = Inr y \<Longrightarrow> l < y \<and> y < u"
    using int_ins_loop_term_1 substr_eff assms(3) by (metis isOK_I sum.sel(2))
  hence b: "l < u" using assms
    by (metis concat.simps(1) diff_is_0_eq less_imp_le_nat
        mapM.simps(1) not_less_eq substr.simps sum.sel(2) take0)
  obtain p' s' where ps_def: "r = (p', s')" by (cases r, simp+)
  show ?thesis
  proof (cases "int_ins_measure' (m, w, r)")
    case (Inl a)
    then show ?thesis using b by (simp add:ps_def)
  next
    case (Inr b)
    then obtain l' u' where ps'_def: "idx w p' = Inr l'" "idx w s' = Inr u'"
      using ps_def apply (simp add:bind_simp del:idx.simps) by blast
    then have "l' \<ge> l \<and> l' < u \<and> u' > l \<and> u' \<le> u \<and> (l' > l \<or> u' < u)"
      using a b ps_def find_zip(2,3,4) assms(1,2,4,5)
      by (metis (no_types, lifting) Inr_inject order.order_iff_strict)
    thus ?thesis using ps_def ps'_def apply (simp add:bind_simp del:idx.simps)
      by (cases "l' < u'", simp del:idx.simps, linarith, simp del:idx.simps)
  qed
qed

lemma assert_ok_simp [simp]: "(assert p = Inr z) = p" by (cases p, simp+)

termination integrate_insert
  apply (relation "measure int_ins_measure", simp)
  using int_ins_loop_term by (simp del:idx.simps, blast)

subsection \<open>Integrate Commutes\<close>

locale integrate_insert_commute =
  fixes M :: "('a :: linorder, 's) message set"
  fixes a :: "'a extended \<Rightarrow> 'a position"
  fixes s :: "('a, 's) woot_character list"
  assumes associated_string_assm: "is_associated_string M s"
  assumes a_conditions_assm: "a_conditions (insert_messages M) a"
begin

lemma dist_ext_ids: "distinct (ext_ids s)"
  using associated_string_assm a_conditions_assm
  apply (simp add:is_associated_string_def sorted_wrt_map)
  by (metis (mono_tags) irreflp_def le_less not_le sorted_wrt_irrefl_distinct)

lemma I_inj_on_S:
  "l < length s \<and> u < length s \<and> I(s ! l) = I(s ! u) \<Longrightarrow> l = u"
  using dist_ext_ids apply (simp add:ext_ids_def)
  using nth_eq_iff_index_eq by fastforce

lemma idx_find: 
  assumes "x < length (ext_ids s)"
  assumes "ext_ids s ! x = i"
  shows "idx s i = Inr x"
  using assms dist_ext_ids nth_eq_iff_index_eq
  by (simp add:filt_simp fromSingleton_simp, blast)

lemma obtain_idx:
  assumes "x \<in> set (ext_ids s)" 
  shows "\<exists>i. idx s x = Inr i" 
  using idx_find assms by (metis in_set_conv_nth)

lemma sorted_a:
  assumes "idx s x = Inr l"
  assumes "idx s y = Inr u"
  shows "(l \<le> u) = (a x \<le> a y)"
proof -
  have "sorted_wrt (<) (map a (ext_ids s))" 
    using associated_string_assm a_conditions_assm is_associated_string_def by blast
  then show ?thesis
  using assms apply (simp add:filt_simp fromSingleton_simp)
  by (metis leD leI le_less length_map nth_map sorted_wrt_nth_less)
qed

lemma sorted_a_le: "idx s x = Inr l \<Longrightarrow> idx s y = Inr u \<Longrightarrow> (l < u) = (a x < a y)"
  by (meson sorted_a not_le)

lemma idx_intro_ext: "i < length (ext_ids s) \<Longrightarrow> idx s (ext_ids s ! i) = Inr i"
  using dist_ext_ids by (simp add:fromSingleton_simp filt_simp  nth_eq_iff_index_eq)

lemma idx_intro:
  assumes "i < length s"
  shows "idx s \<lbrakk>I (s ! i)\<rbrakk> = Inr (Suc i)"
proof -
  have "ext_ids s  ! (Suc i) = \<lbrakk>I (s ! i)\<rbrakk> \<and> Suc i < length (ext_ids s)"
    using assms by (simp add:ext_ids_def nth_append)
  thus ?thesis using idx_intro_ext by force
qed

end

locale integrate_insert_commute_insert = integrate_insert_commute +
  fixes m
  assumes consistent_assm: "consistent (M \<union> {Insert m})"
  assumes insert_assm: "Insert m \<notin> M"
  assumes a_conditions_assm_2: 
    "a_conditions (insert_messages (M \<union> {Insert m})) a"
begin

definition invariant where 
  "invariant pm sm = (pm \<in> set (ext_ids s) \<and> sm \<in> set (ext_ids s) \<and>
   subset (a pm, a sm) (a (P m), a (S m)) \<and> 
   elem (a \<lbrakk>I m\<rbrakk>) (a pm, a sm))"

fun is_concurrent where 
  "is_concurrent pm sm x = (x \<in> set s \<and> 
   subset (a pm, a sm) (a (P x), a (S x)) \<and> 
   elem (a \<lbrakk>I x\<rbrakk>) (a pm, a sm))"

lemma no_id_collision: "I m \<notin> I ` insert_messages M"
proof -
  have "inj_on I (insert_messages (M \<union> {Insert m}))"
    using consistent_def consistent_assm by fastforce
  hence "I m \<in> I ` insert_messages M \<longrightarrow> Insert m \<in> M"
    by (simp add: image_iff inj_on_eq_iff insert_messages_def)
  thus ?thesis using insert_assm by blast
qed
      
lemma not_deleted: "to_woot_char m = to_woot_character M m"
proof -
  have "Delete (DeleteMessage (I m)) \<notin> M"
  proof
    assume "Delete (DeleteMessage (I m)) \<in> M"
    hence "deps (Delete (DeleteMessage (I m))) \<subseteq> I ` insert_messages M"
      using consistent_assm associated_string_assm
      apply (simp add:consistent_def is_associated_string_def)
      using image_subset_iff by fastforce
    thus "False" using no_id_collision by simp
  qed
  thus "to_woot_char m = to_woot_character M m"
    by (cases m, simp add:to_woot_character_def delete_maybe_def)
qed

lemma invariant_imp_sorted:
  assumes "Suc l < length (ext_ids s)"
  assumes "a(ext_ids s ! l) < a \<lbrakk>I m\<rbrakk> \<and> a \<lbrakk>I m\<rbrakk> < a(ext_ids s ! (l+1))"
  shows "sorted_wrt (<) (map a (ext_ids ((take l s)@to_woot_char m#drop l s)))"
proof -
  have "l \<le> length s" using assms(1) by (simp add:ext_ids_def)
  hence "ext_ids (take l s@to_woot_char m#drop l s) = 
        (take (Suc l) (ext_ids s))@\<lbrakk>I m\<rbrakk>#(drop (Suc l) (ext_ids s))"
    by (cases m, simp add:ext_ids_def take_map drop_map)
  thus ?thesis
    using assms associated_string_assm is_associated_string_def a_conditions_assm
    apply (simp flip:take_map drop_map)
    by (rule insort, simp+, blast)
qed

lemma no_self_dep: "\<not> depends_on (insert_messages M \<union> {m}) m m"
proof -
  have "wfP (depends_on (insert_messages M \<union> {m}))"
    using consistent_assm
    apply (simp add:consistent_def)
    by (metis Un_insert_right insert_insert_message sup_bot.right_neutral)
  thus ?thesis 
    by (metis mem_Collect_eq wfP_eq_minimal)
qed

lemma pred_succ_order:
  "m' \<in> (insert_messages M \<union> {m}) \<Longrightarrow> a(P m') < a \<lbrakk>I m'\<rbrakk> \<and> a(S m') > a \<lbrakk>I m'\<rbrakk>"
  by (metis elem.simps is_interval.simps psi_elem a_conditions_def 
      a_conditions_assm_2 insert_insert_message)

lemma find_dep:
  assumes "Insert m' \<in> (M \<union> {Insert m})"
  assumes "i \<in> deps (Insert m')"
  shows "\<lbrakk>i\<rbrakk> \<in> set (ext_ids s)"
proof -
  have "i \<in> I ` insert_messages M"
  proof (cases "m' = m")
    case True
    hence "i \<in> I ` insert_messages (M \<union> {Insert m})"
      using assms consistent_assm
      by (simp add:consistent_def, blast)
    moreover have "i \<noteq> I m" using assms True no_self_dep by auto
    ultimately show ?thesis
      by (metis (no_types, lifting) UnE image_Un image_empty image_insert 
          insert_insert_message singletonD)
  next
    case False
    hence "Insert m' \<in> M" using assms by simp
    then show "i \<in> I ` insert_messages M"
      using assms is_associated_string_def associated_string_assm consistent_def
      by (metis (no_types, hide_lams) Union_iff contra_subsetD image_iff)
  qed
  hence "i \<in> I ` (set s)"
    using associated_string_assm by (simp add:is_associated_string_def)
  thus "\<lbrakk>i\<rbrakk> \<in> set (ext_ids s)"
    by (simp add:ext_ids_def image_iff) 
qed

lemma find_pred:
  "m' \<in> (insert_messages M \<union> {m}) \<Longrightarrow> P m' \<in> set (ext_ids s)"
  using find_dep by (cases "P m'", (simp add:ext_ids_def insert_messages_def pred_is_dep)+)

lemma find_succ:
  "m' \<in> (insert_messages M \<union> {m}) \<Longrightarrow> S m' \<in> set (ext_ids s)"
  using find_dep by (cases "S m'", (simp add:ext_ids_def insert_messages_def succ_is_dep)+)

fun is_certified_associated_string' where
  "is_certified_associated_string' (Inr v) = (
    set v = to_woot_character (M \<union> {Insert m}) ` 
      (insert_messages (M \<union> {Insert m})) \<and>
    sorted_wrt (<) (map a (ext_ids v)))" |
  "is_certified_associated_string' (Inl _) = False" 

lemma integrate_insert_final_step:
  assumes "invariant pm sm"
  assumes "idx s pm = Inr l"
  assumes "idx s sm = Inr (Suc l)" 
  shows "is_certified_associated_string' (Inr (take l s@(to_woot_char m)#drop l s))"
proof -
  define t where "t = (take l s@(to_woot_char m)#drop l s)"
  hence "set t = set s \<union> {to_woot_char m}"
    by (metis Un_insert_right append_take_drop_id list.simps(15) 
        set_append sup_bot.right_neutral)
  hence 
    "set t = to_woot_character M ` insert_messages M \<union> {to_woot_character M m}"
    using not_deleted by (metis associated_string_assm is_associated_string_def)
  hence 
    "set t = to_woot_character (M \<union> {Insert m}) ` insert_messages (M \<union> {Insert m})"
    apply (simp add: to_woot_character_insert_no_eff) 
    using insert_insert_message by fastforce
  moreover have "sorted_wrt (<) (map a (ext_ids t))" using assms invariant_imp_sorted
    by (simp add:invariant_def fromSingleton_simp filt_simp t_def)
  ultimately show ?thesis 
    using t_def associated_string_assm by (simp add:is_associated_string_def)
qed

lemma concurrent_eff:
  assumes "idx s pm = Inr l"
  assumes "idx s sm = Inr u"
  obtains d where "mapM (concurrent s l u) (substr s l u) = Inr d \<and> 
    set (concat d) = InString ` I ` {x. is_concurrent pm sm x}"
proof -
  define t where "t = substr s l u"
  have "set t \<subseteq> set s \<Longrightarrow> (isOK (mapM (concurrent s l u) t) \<and>
    set (concat (projr (mapM (concurrent s l u) t))) = 
    InString ` I ` {x. x \<in> set t \<and> a (P x) \<le> a pm \<and> a (S x) \<ge> a sm})"
  proof (induction t)
    case Nil
    then show ?case by simp
  next
    case (Cons th tt)
    hence "th \<in> to_woot_character M ` insert_messages M" 
      using associated_string_assm by (simp add: is_associated_string_def)
    then obtain th' where th'_def: 
      "th' \<in> insert_messages M \<and> P th' = P th \<and> S th' = S th"
      by (metis image_iff to_woot_character_keeps_P to_woot_character_keeps_S)
    obtain l' where l'_def: "idx s (P th) = Inr l'"
      using th'_def find_pred obtain_idx by fastforce
    obtain u' where u'_def: "idx s (S th) = Inr u'"
      using th'_def find_succ obtain_idx by fastforce
    have "{x. x = \<lbrakk>I th\<rbrakk> \<and> l' \<le> l \<and> u \<le> u'} = 
      InString ` I ` {x. x = th \<and> a (P x) \<le> a pm \<and> a sm \<le> a (S x)}"
      using sorted_a l'_def u'_def assms 
      by (rule_tac set_eqI, simp add:image_iff, blast)
    then show ?case 
      using Cons 
      by (simp add:bind_simp l'_def u'_def 
          concurrent.simps[where w=th] del:idx.simps, auto)
  qed
  moreover have 
    "\<And>x. (x \<in> set (substr s l u)) = (x \<in> set s \<and> a pm < a \<lbrakk>I x\<rbrakk> \<and> a \<lbrakk>I x\<rbrakk> < a sm)"
    apply (simp add:set_nths in_set_conv_nth)
    using sorted_a_le idx_intro assms by blast
  ultimately have "
    isOK (mapM (concurrent s l u) (substr s l u)) \<and> 
    set (concat (projr (mapM (concurrent s l u) (substr s l u)))) = 
      InString ` I ` {x. is_concurrent pm sm x}"
    by (simp only:t_def, fastforce)
  thus ?thesis using that by auto
qed

lemma concurrent_eff_2:
  assumes "invariant pm sm" 
  assumes "is_concurrent pm sm x"
  shows "preserve_order \<lbrakk>I x\<rbrakk> \<lbrakk>I m\<rbrakk> (a \<lbrakk>I x\<rbrakk>) (a \<lbrakk>I m\<rbrakk>)"
proof -
  have "x \<in> to_woot_character M ` insert_messages M" 
    using assms(2) associated_string_assm is_associated_string_def 
      is_concurrent.elims(2) by blast
  then obtain x' where x'_def: "I x = I x' \<and> P x = P x' \<and> S x = S x' \<and> x' \<in> insert_messages M"
    using to_woot_character_keeps_P to_woot_character_keeps_S 
      to_woot_character_keeps_i by fastforce
  have "elem (a \<lbrakk>I x\<rbrakk>) (a (P m), a (S m))"
    using assms by (simp add: invariant_def, auto) 
  moreover have "elem (a \<lbrakk>I m\<rbrakk>) (a (P x), a (S x))" 
    using assms by (simp add: invariant_def, auto)
  moreover have "a_conditions (insert_messages M \<union> {m}) a"
    by (metis insert_insert_message a_conditions_assm_2)
  ultimately have "preserve_order (I x) (I m) (a \<lbrakk>I x\<rbrakk>) (a \<lbrakk>I m\<rbrakk>)" 
    by (simp add: a_conditions_def psi_preserve_order x'_def)
  thus ?thesis by (simp add: preserve_order_def)
qed

lemma concurrent_eff_3:
  assumes "idx s pm = Inr l"
  assumes "idx s sm = Inr u"
  assumes "Suc l < u"
  shows "{x. is_concurrent pm sm x} \<noteq> {}"
proof -
  define H where
    "H = {x. x \<in> insert_messages M \<and> a pm < a \<lbrakk>I x\<rbrakk> \<and> a \<lbrakk>I x\<rbrakk> < a sm}"
  have "wfP (depends_on (insert_messages M))"
    using associated_string_assm by (simp add: consistent_def is_associated_string_def)
  moreover have f:"H \<subseteq> insert_messages M" using H_def by blast
  hence "depends_on H \<le> depends_on (insert_messages M)" by auto
  ultimately have "wfP (depends_on H)" using wf_subset [to_pred] by blast
  moreover
  have u: "l < length s" using assms(2) assms(3) 
    by (simp add:fromSingleton_simp filt_simp, simp add:ext_ids_def)
  hence v:"a pm < a \<lbrakk>I(s ! l)\<rbrakk> \<and> a \<lbrakk>I(s ! l)\<rbrakk> < a sm" 
    using sorted_a_le assms u idx_intro by blast
  have "I (s ! l) \<in> I ` insert_messages M"
    by (metis image_eqI associated_string_assm is_associated_string_def nth_mem 
        to_woot_character_keeps_i_lifted u)
  hence "\<exists>x. x \<in> H" using v H_def by auto
  ultimately obtain z where z_def: "z \<in> H" "\<And> y. depends_on H y z \<Longrightarrow> y \<notin> H"
    by (metis wfP_eq_minimal)
  have a:"\<And>x. x \<in> deps (Insert z) \<Longrightarrow> \<not>(a pm < a \<lbrakk>x\<rbrakk> \<and> a \<lbrakk>x\<rbrakk> < a sm)"
  proof -
    fix x
    assume a:"x \<in> deps (Insert z)"
    hence "x \<in> I ` insert_messages M" 
      using insert_messages_def associated_string_assm 
      apply (simp add:consistent_def is_associated_string_def)
      using H_def z_def(1) by blast
    then obtain x' where x'_def: "x' \<in> insert_messages M \<and> x = I x'" by blast
    hence "x' \<notin> H" using z_def 
      using a depends_on.simps by blast
    thus "\<not>(a pm < a \<lbrakk>x\<rbrakk> \<and> a \<lbrakk>x\<rbrakk> < a sm)" using H_def x'_def by blast
  qed
  have "ext_ids s ! 0 = \<turnstile> \<and> 0 < length (ext_ids s)" by (simp add:ext_ids_def)
  hence b:"\<not>(a pm < a \<turnstile>)"
    by (metis not_less_zero  sorted_a_le assms(1) idx_intro_ext)
  have "ext_ids s ! (Suc (length s)) = \<stileturn> \<and> Suc (length s) < length (ext_ids s)"
    by (simp add:nth_append ext_ids_def)
  moreover have "\<not>(Suc (length s) < u)" using assms(2)
    by (simp add:fromSingleton_simp filt_simp, simp add:ext_ids_def)
  ultimately have c:"\<not>(a \<stileturn> < a sm)" by (metis sorted_a_le assms(2) idx_intro_ext)
  have d:"a (P z) \<le> a pm"
    using a b c pred_is_dep pred_succ_order H_def z_def(1) by (cases "P z", fastforce+)
  have e:"a (S z) \<ge> a sm"
    using a b c succ_is_dep pred_succ_order H_def z_def(1) by (cases "S z", fastforce+)
  have "to_woot_character M z \<in> set s" 
    using f associated_string_assm is_associated_string_def z_def(1) by fastforce
  hence "is_concurrent pm sm (to_woot_character M z)"
    using H_def z_def(1) d e by simp
  thus ?thesis by blast
qed

lemma integrate_insert_result_helper:
  "invariant pm sm \<Longrightarrow> m' = m \<Longrightarrow> s' = s \<Longrightarrow> 
  is_certified_associated_string' (integrate_insert m' s' pm sm)"
proof (induction m' s' pm sm rule:integrate_insert.induct)
  case (1 m' s' pm sm)
  obtain l where l_def: "idx s pm = Inr l" 
    using "1"(2) invariant_def obtain_idx by blast
  obtain u where u_def: "idx s sm = Inr u"
    using "1"(2) invariant_def obtain_idx by blast
  show ?case
  proof (cases "Suc l = u")
    case True
    then show ?thesis
      apply (simp add:l_def u_def 1 del:idx.simps is_certified_associated_string'.simps)
      using "1"(2) l_def u_def integrate_insert_final_step by blast
  next
    case False
    have "a pm < a sm" using invariant_def "1"(2) by auto
    hence a:"l < u" using sorted_a_le  l_def u_def by blast
    obtain d where d_def: "mapM (concurrent s l u) (substr s l u) = Inr d \<and>  
      set (concat d) = InString ` I ` {x. is_concurrent pm sm x}" 
      by (metis concurrent_eff l_def u_def)
    have b:"concat d \<noteq> []" 
      by (metis Suc_lessI concurrent_eff_3 False l_def u_def 
          a d_def empty_set image_is_empty)
    have c:"\<And>x. x \<in> set (concat d) \<Longrightarrow> 
      preserve_order x \<lbrakk>I m\<rbrakk> (a x) (a \<lbrakk>I m\<rbrakk>) \<and> x \<in> set (ext_ids s) \<and>
       a pm < a x \<and> a x < a sm"
      using 1(2) d_def concurrent_eff_2 
      by (simp del:set_concat add:ext_ids_def, blast)
    obtain pm' sm' where ps'_def: "find ((\<lambda>x.\<lbrakk>I m\<rbrakk> < x \<or> x = sm) \<circ> snd)
         (zip (pm # concat d) (concat d @ [sm])) = Some (pm',sm')"
      (is "?lhs = ?rhs")
      apply (cases "?lhs")
      apply (simp add:find_None_iff) 
       apply (metis in_set_conv_decomp in_set_impl_in_set_zip2 length_Cons 
              length_append_singleton) 
      by fastforce
    have d:"pm' = pm \<or> pm' \<in> set (concat d)" using ps'_def b
      by (metis (full_types) find_zip(3))
    hence "pm' \<in> set (ext_ids s)" using c 1(2) invariant_def by auto
    hence "pm' \<in> InString ` I ` insert_messages M \<or> pm' = \<turnstile> \<or> pm' = \<stileturn>"
      apply (simp add:ext_ids_def)
      by (metis image_image associated_string_assm is_associated_string_def 
          to_woot_character_keeps_i_lifted)
    hence "pm' \<noteq> \<lbrakk>I m\<rbrakk>" using no_id_collision by blast
    hence "(pm' = pm \<or> pm' < \<lbrakk>I m\<rbrakk>) \<and> (sm' = sm \<or> sm' > \<lbrakk>I m\<rbrakk> \<and> sm' \<in> set (concat d))" 
      by (metis (mono_tags, lifting) ps'_def b find_zip(1) find_zip(3) find_zip(4) less_linear)
    hence e:"invariant pm' sm'"
      using 1(2) c d apply (simp add:invariant_def del:set_concat) 
      by (meson dual_order.strict_trans leD leI preserve_order_def)
    show ?thesis apply (subst integrate_insert.simps)
      using a b e ps'_def 1 d_def False l_def u_def
      by (simp add:1 del:idx.simps integrate_insert.simps)
  qed
qed

lemma integrate_insert_result:
  "is_certified_associated_string' (integrate_insert m s (P m) (S m))"
proof -
  have "invariant (P m) (S m)" 
    using find_pred find_succ pred_succ_order by (simp add:invariant_def)
  thus ?thesis using integrate_insert_result_helper by blast
qed
end

lemma integrate_insert_result:
  assumes "consistent (M \<union> {Insert m})"
  assumes "Insert m \<notin> M"
  assumes "is_associated_string M s"
  shows "is_certified_associated_string (M \<union> {Insert m}) (integrate_insert m s (P m) (S m))"
proof -
  obtain t where t_def: "(integrate_insert m s (P m) (S m)) = Inr t \<and>
    set t = to_woot_character (M \<union> {Insert m}) ` (insert_messages (M \<union> {Insert m}))"
  proof -
    fix tt
    assume a:"(\<And>t. (integrate_insert m s (P m) (S m)) = Inr t \<and>
          set t = to_woot_character (M \<union> {Insert m}) ` insert_messages (M \<union> {Insert m}) \<Longrightarrow>
          tt)"
    obtain a where a_def: "a_conditions (insert_messages (M \<union> {Insert m})) a"
      using consistent_def assms by blast
    moreover have "a_conditions (insert_messages M) a"
      using assms a_subset is_associated_string_def a_def by blast
    ultimately interpret integrate_insert_commute_insert "M" "a" "s" "m"
      using assms by (simp add: integrate_insert_commute_insert_def integrate_insert_commute_def (*
                *) integrate_insert_commute_insert_axioms.intro)
    show tt using a integrate_insert_result
      apply (cases "integrate_insert m s (P m) (S m)") by auto 
  qed
  have b:"\<And>a. a_conditions (insert_messages (M \<union> {Insert m})) a \<Longrightarrow> 
    sorted_wrt (<) (map a (ext_ids t))"
  proof -
    fix a
    assume c:"a_conditions (insert_messages (M \<union> {Insert m})) a"
    moreover have "a_conditions (insert_messages M) a"
      using assms a_subset is_associated_string_def c by blast
    ultimately interpret integrate_insert_commute_insert "M" "a" "s" "m"
      using assms by (simp add: integrate_insert_commute_insert_def integrate_insert_commute_def (*
                *) integrate_insert_commute_insert_axioms.intro)
    show "sorted_wrt (<) (map a (ext_ids t))" 
      using integrate_insert_result t_def by simp
  qed
  show "?thesis" using b t_def assms(1) by (simp add:is_associated_string_def)
qed 

locale integrate_insert_commute_delete = integrate_insert_commute +
  fixes m
  assumes consistent_assm: "consistent (M \<union> {Delete m})"
begin

fun delete :: "('a, 's) woot_character \<Rightarrow> ('a, 's) woot_character"
  where "delete (InsertMessage p i u _) = InsertMessage p i u None"

definition delete_only_m :: "('a, 's) woot_character \<Rightarrow> ('a, 's) woot_character"
  where "delete_only_m x = (if DeleteMessage (I x) = m then delete x else x)"

lemma set_s: "set s = to_woot_character M ` insert_messages M"
  using associated_string_assm by (simp add:is_associated_string_def)

lemma delete_only_m_effect:
  "delete_only_m (to_woot_character M x) = to_woot_character (M \<union> {Delete m}) x"
  apply (cases x, simp add:to_woot_character_def delete_maybe_def)
  by (metis delete_only_m_def insert_message.sel(2) delete.simps)

lemma integrate_delete_result:
  "is_certified_associated_string (M \<union> {Delete m}) (integrate_delete m s)"
proof (cases m)
  case (DeleteMessage i)
  have "deps (Delete m) \<subseteq> I ` insert_messages (M \<union> {Delete m})"
    using consistent_assm by (simp add:consistent_def DeleteMessage)
  hence "i \<in> I ` insert_messages (M \<union> {Delete m})" using DeleteMessage by auto
  hence "i \<in> I ` set s" using set_s by (simp add:insert_messages_def)
  then obtain k where k_def: "I (s ! k) = i \<and> k < length s" 
    by (metis imageE in_set_conv_nth)
  hence "ext_ids s ! (Suc k) = \<lbrakk>i\<rbrakk> \<and> Suc k < length (ext_ids s)" 
    by (simp add:ext_ids_def nth_append)
  hence g:"idx s \<lbrakk>i\<rbrakk> = Inr (Suc k)" apply (simp add:fromSingleton_simp filt_simp)
     using dist_ext_ids nth_eq_iff_index_eq by fastforce
  moreover define t where "t = List.list_update s k (delete (s ! k))"
  ultimately have a: "integrate_delete m s = Inr t"
    using k_def DeleteMessage by (cases "s ! k", simp)
  have "\<And>j. j < length s \<Longrightarrow> (DeleteMessage (I(s ! j)) = m) = (j = k)" 
    apply (simp add: DeleteMessage) using I_inj_on_S k_def by blast
  hence "List.list_update s k (delete (s ! k)) = map delete_only_m s"
    by (rule_tac nth_equalityI, (simp add:k_def delete_only_m_def)+)
  hence "set t = delete_only_m ` set s" using t_def by auto
  also have "... = to_woot_character (M \<union> {Delete m}) ` (insert_messages M)"
    using set_s delete_only_m_effect image_cong by (metis (no_types, lifting) image_image)
  finally have b:
    "set t = to_woot_character (M \<union> {Delete m}) ` (insert_messages (M \<union> {Delete m}))"
    by (simp add: insert_messages_def)
  have "ext_ids s = ext_ids t"
    apply (cases "s ! k", simp add:t_def ext_ids_def) 
    by (metis (no_types, lifting) insert_message.sel(2) list_update_id map_update)
  moreover have "\<And>a. a_conditions (insert_messages M) a \<Longrightarrow> sorted_wrt (<) (map a (ext_ids s))"
    using associated_string_assm is_associated_string_def by blast
  ultimately have c: "\<And>a. a_conditions (insert_messages (M \<union> {Delete m})) a
                  \<Longrightarrow> sorted_wrt (<) (map a (ext_ids t))" 
    by (simp add:insert_messages_def)
  show ?thesis
    apply (simp add:a is_associated_string_def b c)
    using consistent_assm by fastforce
qed
end

lemma integrate_delete_result:
  assumes "consistent (M \<union> {Delete m})"
  assumes "is_associated_string M s"
  shows "is_certified_associated_string (M \<union> {Delete m}) (integrate_delete m s)"
proof -
  obtain a where a_def: "a_conditions (insert_messages (M \<union> {Delete m})) a" 
    using consistent_def assms by blast
  moreover have "a_conditions (insert_messages M) a"
    using assms a_subset is_associated_string_def a_def by blast
  ultimately interpret integrate_insert_commute_delete "M" "a" "s" "m"
    using assms by (simp add: integrate_insert_commute_def integrate_insert_commute_delete.intro
            integrate_insert_commute_delete_axioms.intro)
  show "?thesis" using integrate_delete_result by blast
qed

fun is_delete :: "(('a, 's) message) \<Rightarrow> bool" 
  where 
    "is_delete (Insert m) = False" |
    "is_delete (Delete m) = True"

proposition integrate_insert_commute:
  assumes "consistent (M \<union> {m})"
  assumes "is_delete m \<or> m \<notin> M"
  assumes "is_associated_string M s"
  shows "is_certified_associated_string (M \<union> {m}) (integrate s m)"
  using assms integrate_insert_result integrate_delete_result by (cases m, fastforce+)

end