(*<*)
theory Monitor_Impl
  imports Monitor
    Optimized_MTL
    Event_Data
    "HOL-Library.Code_Target_Nat"
    Containers.Containers
begin
(*>*)

section \<open>Instantiation of the generic algorithm and code setup\<close>

lemma [code_unfold del, symmetric, code_post del]: "card \<equiv> Cardinality.card'" by simp
declare [[code drop: card]] Set_Impl.card_code[code]

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance ..
end

derive ccompare Formula.trm
derive (eq) ceq Formula.trm
derive (rbt) set_impl Formula.trm
derive (eq) ceq Monitor.mregex
derive ccompare Monitor.mregex
derive (rbt) set_impl Monitor.mregex
derive (rbt) mapping_impl Monitor.mregex
derive (no) cenum Monitor.mregex
derive (rbt) set_impl event_data
derive (rbt) mapping_impl event_data

definition add_new_mmuaux' :: "args \<Rightarrow> event_data table \<Rightarrow> event_data table \<Rightarrow> ts \<Rightarrow> event_data mmuaux \<Rightarrow>
  event_data mmuaux" where
  "add_new_mmuaux' = add_new_mmuaux"

interpretation muaux valid_mmuaux init_mmuaux add_new_mmuaux' length_mmuaux eval_mmuaux
  using valid_init_mmuaux valid_add_new_mmuaux valid_length_mmuaux valid_eval_mmuaux
  unfolding add_new_mmuaux'_def
  by unfold_locales assumption+

global_interpretation verimon_maux: maux "\<lambda>_ cur (t, aux) auxlist. t = cur \<and> aux = auxlist" "\<lambda>_. (0, [])"
  "\<lambda>args nt (t, auxlist). (nt, filter (\<lambda>(t, rel). enat (nt - t) \<le> right (args_ivl args)) auxlist)"
  "\<lambda>args rel1 (t, auxlist). (t, map (\<lambda>(t, rel). (t, join rel (args_pos args) rel1)) auxlist)"
  "\<lambda>args rel2 (cur, auxlist). (cur, (case auxlist of
    [] => [(cur, rel2)]
  | ((t, y) # ts) \<Rightarrow> if t = cur then (t, y \<union> rel2) # ts else (cur, rel2) # auxlist))"
  "\<lambda>args (cur, auxlist). foldr (\<union>) [rel. (t, rel) \<leftarrow> auxlist, left (args_ivl args) \<le> cur - t] {}"
  "\<lambda>_ cur (t, aux) auxlist. t = cur \<and> aux = auxlist" "\<lambda>_. (0, [])"
  "\<lambda>args rel1 rel2 nt (t, auxlist). (nt, update_until args rel1 rel2 nt auxlist)"
  "\<lambda>_ (_, auxlist). length auxlist"
  "\<lambda>args nt (t, auxlist). (let (res, auxlist') = eval_until (args_ivl args) nt auxlist in (res, (t, auxlist')))"
  by unfold_locales auto

global_interpretation default_maux: maux valid_mmsaux "init_mmsaux :: _ \<Rightarrow> event_data mmsaux" add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux result_mmsaux
  valid_mmuaux "init_mmuaux :: _ \<Rightarrow> event_data mmuaux" add_new_mmuaux' length_mmuaux eval_mmuaux
  defines minit0 = "maux.minit0 (init_mmsaux :: _ \<Rightarrow> event_data mmsaux) (init_mmuaux :: _ \<Rightarrow> event_data mmuaux) :: _ \<Rightarrow> Formula.formula \<Rightarrow> _"
  and minit = "maux.minit (init_mmsaux :: _ \<Rightarrow> event_data mmsaux) (init_mmuaux :: _ \<Rightarrow> event_data mmuaux) :: Formula.formula \<Rightarrow> _"
  and minit_safe = "maux.minit_safe (init_mmsaux :: _ \<Rightarrow> event_data mmsaux) (init_mmuaux :: _ \<Rightarrow> event_data mmuaux) :: Formula.formula \<Rightarrow> _"
  and update_since = "maux.update_since add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> event_data table)"
  and meval = "maux.meval add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux' (eval_mmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and mstep = "maux.mstep add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux' (eval_mmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and msteps0_stateless = "maux.msteps0_stateless add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux' (eval_mmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and msteps_stateless = "maux.msteps_stateless add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) add_new_mmuaux' (eval_mmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  and monitor = "maux.monitor init_mmsaux add_new_ts_mmsaux gc_join_mmsaux add_new_table_mmsaux (result_mmsaux :: _ \<Rightarrow> event_data mmsaux \<Rightarrow> _) init_mmuaux add_new_mmuaux' (eval_mmuaux :: _ \<Rightarrow> _ \<Rightarrow> event_data mmuaux \<Rightarrow> _)"
  by unfold_locales

lemma image_these: "f ` Option.these X = Option.these (map_option f ` X)"
  by (force simp: in_these_eq Bex_def image_iff map_option_case split: option.splits)

thm default_maux.meval.simps(2)

lemma meval_MPred: "meval n t db (MPred e ts) =
  (case Mapping.lookup db e of None \<Rightarrow> [{}] | Some Xs \<Rightarrow> map (\<lambda>X. \<Union>v \<in> X.
  (set_option (map_option (\<lambda>f. Table.tabulate f 0 n) (match ts v)))) Xs, MPred e ts)"
  by (force split: option.splits simp: Option.these_def image_iff)

lemmas meval_code[code] = default_maux.meval.simps(1) meval_MPred default_maux.meval.simps(3-)

definition mk_db :: "(Formula.name \<times> event_data list set) list \<Rightarrow> _" where
  "mk_db t = Monitor.mk_db (\<Union>n \<in> set (map fst t). (\<lambda>v. (n, v)) ` the (map_of t n))"

definition rbt_fold :: "_ \<Rightarrow> event_data tuple set_rbt \<Rightarrow> _ \<Rightarrow> _" where
  "rbt_fold = RBT_Set2.fold"

definition rbt_empty :: "event_data list set_rbt" where
  "rbt_empty = RBT_Set2.empty"

definition rbt_insert :: "_ \<Rightarrow> _ \<Rightarrow> event_data list set_rbt" where
  "rbt_insert = RBT_Set2.insert"

lemma saturate_commute:
  assumes "\<And>s. r \<in> g s" "\<And>s. g (insert r s) = g s" "\<And>s. r \<in> s \<Longrightarrow> h s = g s"
  and terminates: "mono g" "\<And>X. X \<subseteq> C \<Longrightarrow> g X \<subseteq> C" "finite C"
shows "saturate g {} = saturate h {r}"
proof (cases "g {} = {r}")
  case True
  with assms have "g {r} = {r}" "h {r} = {r}" by auto
  with True show ?thesis
    by (subst (1 2) saturate_code; subst saturate_code) (simp add: Let_def)
next
  case False
  then show ?thesis
    unfolding saturate_def while_def
    using while_option_finite_subset_Some[OF terminates] assms(1-3)
    by (subst while_option_commute_invariant[of "\<lambda>S. S = {} \<or> r \<in> S" "\<lambda>S. g S \<noteq> S" g "\<lambda>S. h S \<noteq> S" "insert r" h "{}", symmetric])
      (auto 4 4 dest: while_option_stop[of "\<lambda>S. g S \<noteq> S" g "{}"])
qed

definition "RPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (RPD ` S))"

lemma RPDs_aux_code[code]:
  "RPDs_aux S = (let S' = S \<union> Set.bind S RPD in if S' \<subseteq> S then S else RPDs_aux S')"
  unfolding RPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare RPDs_code[code del]
lemma RPDs_code[code]: "RPDs r = RPDs_aux {r}"
  unfolding RPDs_aux_def RPDs_code
  by (rule saturate_commute[where C="RPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff RPDs_refl RPDs_trans finite_RPDs)

definition "LPDs_aux = saturate (\<lambda>S. S \<union> \<Union> (LPD ` S))"

lemma LPDs_aux_code[code]:
  "LPDs_aux S = (let S' = S \<union> Set.bind S LPD in if S' \<subseteq> S then S else LPDs_aux S')"
  unfolding LPDs_aux_def bind_UNION
  by (subst saturate_code) auto

declare LPDs_code[code del]
lemma LPDs_code[code]: "LPDs r = LPDs_aux {r}"
  unfolding LPDs_aux_def LPDs_code
  by (rule saturate_commute[where C="LPDs r"])
     (auto 0 3 simp: mono_def subset_singleton_iff LPDs_refl LPDs_trans finite_LPDs)

lemma is_empty_table_unfold [code_unfold]:
  "X = empty_table \<longleftrightarrow> Set.is_empty X"
  "empty_table = X \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set X empty_table \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set empty_table X \<longleftrightarrow> Set.is_empty X"
  "set_eq X empty_table \<longleftrightarrow> Set.is_empty X"
  "set_eq empty_table X \<longleftrightarrow> Set.is_empty X"
  "X = (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "(set_empty impl) = X \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set X (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "Cardinality.eq_set (set_empty impl) X \<longleftrightarrow> Set.is_empty X"
  "set_eq X (set_empty impl) \<longleftrightarrow> Set.is_empty X"
  "set_eq (set_empty impl) X \<longleftrightarrow> Set.is_empty X"
  unfolding set_eq_def set_empty_def empty_table_def Set.is_empty_def Cardinality.eq_set_def by auto

lemma tabulate_rbt_code[code]: "Monitor.mrtabulate (xs :: mregex list) f =
  (case ID CCOMPARE(mregex) of None \<Rightarrow> Code.abort (STR ''tabulate RBT_Mapping: ccompare = None'') (\<lambda>_. Monitor.mrtabulate (xs :: mregex list) f)
  | _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.bulkload (List.map_filter (\<lambda>k. let fk = f k in if fk = empty_table then None else Some (k, fk)) xs)))"
  unfolding mrtabulate.abs_eq RBT_Mapping_def
  by (auto split: option.splits)

lemma combine_Mapping[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.combine f (RBT_Mapping t) (RBT_Mapping u) = 
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''combine RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.combine f (RBT_Mapping t) (RBT_Mapping u))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.join (\<lambda>_. f) t u))"
  by (auto simp add: Mapping.combine.abs_eq Mapping_inject lookup_join split: option.split)

lemma upd_set_empty[simp]: "upd_set m f {} = m"
  by transfer auto

lemma upd_set_insert[simp]: "upd_set m f (insert x A) = Mapping.update x (f x) (upd_set m f A)"
  by (rule mapping_eqI) (auto simp: Mapping_lookup_upd_set Mapping.lookup_update')

lemma upd_set_fold:
  assumes "finite A"
  shows "upd_set m f A = Finite_Set.fold (\<lambda>a. Mapping.update a (f a)) m A"
proof -
  interpret comp_fun_idem "\<lambda>a. Mapping.update a (f a)"
    by unfold_locales (transfer; auto simp: fun_eq_iff)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) auto
qed

lift_definition upd_cfi :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>f a m. Mapping.update a (f a) m"
  by unfold_locales (transfer; auto simp: fun_eq_iff)+

lemma upd_set_code[code]:
  "upd_set m f A = (if finite A then set_fold_cfi (upd_cfi f) m A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. upd_set m f A))"
  by (transfer fixing: m) (auto simp: upd_set_fold)

lemma lexordp_eq_code[code]: "lexordp_eq xs ys \<longleftrightarrow> (case xs of [] \<Rightarrow> True
  | x # xs \<Rightarrow> (case ys of [] \<Rightarrow> False
    | y # ys \<Rightarrow> if x < y then True else if x > y then False else lexordp_eq xs ys))"
  by (subst lexordp_eq.simps) (auto split: list.split)

definition "filter_set m X t = Mapping.filter (filter_cond X m t) m"

declare [[code drop: shift_end]]
declare shift_end.simps[folded filter_set_def, code]

lemma upd_set'_empty[simp]: "upd_set' m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup)

lemma upd_set'_insert: "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_set' m d f (insert x A) =
  (let m' = (upd_set' m d f A) in case Mapping.lookup m' x of None \<Rightarrow> Mapping.update x d m'
  | Some v \<Rightarrow> Mapping.update x (f v) m')"
  by (rule mapping_eqI) (auto simp: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux1: "upd_set' Mapping.empty d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' Mapping.empty d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: Let_def upd_set'_lookup Mapping.lookup_update'
      Mapping.lookup_empty split: option.splits)

lemma upd_set'_aux2: "Mapping.lookup m k = None \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k d (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux3: "Mapping.lookup m k = Some v \<Longrightarrow> upd_set' m d f {b. b = k \<or> (a, b) \<in> A} =
  Mapping.update k (f v) (upd_set' m d f {b. (a, b) \<in> A})"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' split: option.splits)

lemma upd_set'_aux4: "k \<notin> fst ` A \<Longrightarrow> upd_set' Mapping.empty d f {b. (k, b) \<in> A} = Mapping.empty"
  by (rule mapping_eqI) (auto simp add: upd_set'_lookup Mapping.lookup_update' Domain.DomainI fst_eq_Domain
      split: option.splits)

lemma upd_nested_empty[simp]: "upd_nested m d f {} = m"
  by (rule mapping_eqI) (auto simp add: upd_nested_lookup split: option.splits)

definition upd_nested_step :: "'c \<Rightarrow> ('c \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a, ('b, 'c) mapping) mapping \<Rightarrow>
  ('a, ('b, 'c) mapping) mapping" where
  "upd_nested_step d f x m = (case x of (k, k') \<Rightarrow>
    (case Mapping.lookup m k of Some m' \<Rightarrow>
      (case Mapping.lookup m' k' of Some v \<Rightarrow> Mapping.update k (Mapping.update k' (f v) m') m
      | None \<Rightarrow> Mapping.update k (Mapping.update k' d m') m)
    | None \<Rightarrow> Mapping.update k (Mapping.update k' d Mapping.empty) m))"

lemma upd_nested_insert:
  "d = f d \<Longrightarrow> (\<And>x. f (f x) = f x) \<Longrightarrow> upd_nested m d f (insert x A) =
  upd_nested_step d f x (upd_nested m d f A)"
  unfolding upd_nested_step_def
  using upd_set'_aux1[of d f _ _ A] upd_set'_aux2[of _ _ d f _ A] upd_set'_aux3[of _ _ _ d f _ A]
    upd_set'_aux4[of _ A d f]
  by (auto simp add: Let_def upd_nested_lookup upd_set'_lookup Mapping.lookup_update'
      Mapping.lookup_empty split: option.splits prod.splits if_splits intro!: mapping_eqI)

definition upd_nested_max_tstp where
  "upd_nested_max_tstp m d X = upd_nested m d (max_tstp d) X"

lemma upd_nested_max_tstp_fold:
  assumes "finite X"
  shows "upd_nested_max_tstp m d X = Finite_Set.fold (upd_nested_step d (max_tstp d)) m X"
proof -
  interpret comp_fun_idem "upd_nested_step d (max_tstp d)"
    by (unfold_locales; rule ext)
      (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update' Mapping.lookup_empty
       update_update max_tstp_d_d max_tstp_idem' split: option.splits)
  note upd_nested_insert' = upd_nested_insert[of d "max_tstp d",
    OF max_tstp_d_d[symmetric] max_tstp_idem']
  show ?thesis
    using assms
    by (induct X arbitrary: m rule: finite.induct)
       (auto simp add: upd_nested_max_tstp_def upd_nested_insert')
qed

lift_definition upd_nested_max_tstp_cfi ::
  "ts + tp \<Rightarrow> ('a \<times> 'b, ('a, ('b, ts + tp) mapping) mapping) comp_fun_idem"
  is "\<lambda>d. upd_nested_step d (max_tstp d)"
  by (unfold_locales; rule ext)
    (auto simp add: comp_def upd_nested_step_def Mapping.lookup_update' Mapping.lookup_empty
      update_update max_tstp_d_d max_tstp_idem' split: option.splits)

lemma upd_nested_max_tstp_code[code]:
  "upd_nested_max_tstp m d X = (if finite X then set_fold_cfi (upd_nested_max_tstp_cfi d) m X
    else Code.abort (STR ''upd_nested_max_tstp: infinite'') (\<lambda>_. upd_nested_max_tstp m d X))"
  by transfer (auto simp add: upd_nested_max_tstp_fold)

declare [[code drop: add_new_mmuaux']]
declare add_new_mmuaux'_def[unfolded add_new_mmuaux.simps, folded upd_nested_max_tstp_def, code]

lemma filter_set_empty[simp]: "filter_set m {} t = m"
  unfolding filter_set_def
  by transfer (auto simp: fun_eq_iff split: option.splits)

lemma filter_set_insert[simp]: "filter_set m (insert x A) t = (let m' = filter_set m A t in
  case Mapping.lookup m' x of Some u \<Rightarrow> if t = u then Mapping.delete x m' else m' | _ \<Rightarrow> m')"
  unfolding filter_set_def
  by transfer (auto simp: fun_eq_iff Let_def Map_To_Mapping.map_apply_def split: option.splits)

lemma filter_set_fold:
  assumes "finite A"
  shows "filter_set m A t = Finite_Set.fold (\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m) m A"
proof -
  interpret comp_fun_idem "\<lambda>a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
    by unfold_locales
      (transfer; auto simp: fun_eq_iff Map_To_Mapping.map_apply_def split: option.splits)+
  from assms show ?thesis
    by (induct A arbitrary: m rule: finite.induct) (auto simp: Let_def)
qed

lift_definition filter_cfi :: "'b \<Rightarrow> ('a, ('a, 'b) mapping) comp_fun_idem"
  is "\<lambda>t a m.
    case Mapping.lookup m a of Some u \<Rightarrow> if t = u then Mapping.delete a m else m | _ \<Rightarrow> m"
  by unfold_locales
    (transfer; auto simp: fun_eq_iff Map_To_Mapping.map_apply_def split: option.splits)+

lemma filter_set_code[code]:
  "filter_set m A t = (if finite A then set_fold_cfi (filter_cfi t) m A else Code.abort (STR ''upd_set: infinite'') (\<lambda>_. filter_set m A t))"
  by (transfer fixing: m) (auto simp: filter_set_fold)

lemma filter_Mapping[code]:
  fixes t :: "('a :: ccompare, 'b) mapping_rbt" shows
  "Mapping.filter P (RBT_Mapping t) = 
  (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''filter RBT_Mapping: ccompare = None'') (\<lambda>_. Mapping.filter P (RBT_Mapping t))
                     | Some _ \<Rightarrow> RBT_Mapping (RBT_Mapping2.filter (case_prod P) t))"
  by (auto simp add: Mapping.filter.abs_eq Mapping_inject split: option.split)

definition "filter_join pos X m = Mapping.filter (join_filter_cond pos X) m"

declare [[code drop: join_mmsaux]]
declare join_mmsaux.simps[folded filter_join_def, code]

lemma filter_join_False_empty: "filter_join False {} m = m"
  unfolding filter_join_def
  by transfer (auto split: option.splits)

lemma filter_join_False_insert: "filter_join False (insert a A) m =
  filter_join False A (Mapping.delete a m)"
proof -
  {
    fix x
    have "Mapping.lookup (filter_join False (insert a A) m) x =
      Mapping.lookup (filter_join False A (Mapping.delete a m)) x"
      by (auto simp add: filter_join_def Mapping.lookup_filter Mapping_lookup_delete
          split: option.splits)
  }
  then show ?thesis
    by (simp add: mapping_eqI)
qed

lemma filter_join_False:
  assumes "finite A"
  shows "filter_join False A m = Finite_Set.fold Mapping.delete m A"
proof -
  interpret comp_fun_idem "Mapping.delete"
    by (unfold_locales; transfer) (fastforce simp add: comp_def)+
  from assms show ?thesis
    by (induction A arbitrary: m rule: finite.induct)
       (auto simp add: filter_join_False_empty filter_join_False_insert fold_fun_left_comm)
qed

lift_definition filter_not_in_cfi :: "('a, ('a, 'b) mapping) comp_fun_idem" is "Mapping.delete"
  by (unfold_locales; transfer) (fastforce simp add: comp_def)+

lemma filter_join_code[code]:
  "filter_join pos A m =
    (if \<not>pos \<and> finite A \<and> card A < Mapping.size m then set_fold_cfi filter_not_in_cfi m A
    else Mapping.filter (join_filter_cond pos A) m)"
  unfolding filter_join_def
  by (transfer fixing: m) (use filter_join_False in \<open>auto simp add: filter_join_def\<close>)

definition set_minus :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "set_minus X Y = X - Y"

lift_definition remove_cfi :: "('a, 'a set) comp_fun_idem"
  is "\<lambda>b a. a - {b}"
  by unfold_locales auto

lemma set_minus_finite:
  assumes fin: "finite Y"
  shows "set_minus X Y = Finite_Set.fold (\<lambda>a X. X - {a}) X Y"
proof -
  interpret comp_fun_idem "\<lambda>a X. X - {a}"
    by unfold_locales auto
  from assms show ?thesis
    by (induction Y arbitrary: X rule: finite.induct) (auto simp add: set_minus_def)
qed

lemma set_minus_code[code]: "set_minus X Y =
  (if finite Y \<and> card Y < card X then set_fold_cfi remove_cfi X Y else X - Y)"
  by transfer (use set_minus_finite in \<open>auto simp add: set_minus_def\<close>)

declare [[code drop: bin_join]]
declare bin_join.simps[folded set_minus_def, code]

definition remove_Union where
  "remove_Union A X B = A - (\<Union>x \<in> X. B x)"

lemma remove_Union_finite: 
  assumes "finite X"
  shows "remove_Union A X B = Finite_Set.fold (\<lambda>x A. A - B x) A X"
proof -
  interpret comp_fun_idem "\<lambda>x A. A - B x"
    by unfold_locales auto
  from assms show ?thesis
    by (induct X arbitrary: A rule: finite_induct) (auto simp: remove_Union_def)
qed

lift_definition remove_Union_cfi :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a, 'b set) comp_fun_idem" is "\<lambda>B x A. A - B x"
  by unfold_locales auto

lemma remove_Union_code[code]: "remove_Union A X B =
  (if finite X then set_fold_cfi (remove_Union_cfi B) A X else A - (\<Union>x \<in> X. B x))"
  by (transfer fixing: A X B) (use remove_Union_finite[of X A B] in \<open>auto simp add: remove_Union_def\<close>)

lemma tabulate_remdups: "Mapping.tabulate xs f = Mapping.tabulate (remdups xs) f"
  by (transfer fixing: xs f) (auto simp: map_of_map_restrict)

lift_definition clearjunk :: "(char list \<times> event_data list set) list \<Rightarrow> (char list, event_data list set list) alist" is
  "\<lambda>t. List.map_filter (\<lambda>(p, X). if X = {} then None else Some (p, [X])) (AList.clearjunk t)"
  unfolding map_filter_def o_def list.map_comp
  by (subst map_cong[OF refl, of _ _ fst]) (auto simp: map_filter_def distinct_map_fst_filter split: if_splits)

lemma map_filter_snd_map_filter: "List.map_filter (\<lambda>(a, b). if P b then None else Some (f a b)) xs =
    map (\<lambda>(a, b). f a b) (filter (\<lambda>x. \<not> P (snd x)) xs)"
  by (simp add: map_filter_def prod.case_eq_if)

lemma mk_db_code_alist:
  "mk_db t = Assoc_List_Mapping (clearjunk t)"
  unfolding mk_db_def Assoc_List_Mapping_def
  by (transfer' fixing: t)
    (auto simp: map_filter_snd_map_filter fun_eq_iff map_of_map image_iff map_of_clearjunk
      map_of_filter_apply dest: weak_map_of_SomeI intro!: bexI[rotated, OF map_of_SomeD]
      split: if_splits option.splits)

lemma mk_db_code[code]:
  "mk_db t = Mapping.of_alist (List.map_filter (\<lambda>(p, X). if X = {} then None else Some (p, [X])) (AList.clearjunk t))"
  unfolding mk_db_def
  by (transfer' fixing: t) (auto simp: map_filter_snd_map_filter fun_eq_iff map_of_map image_iff
      map_of_clearjunk map_of_filter_apply dest: weak_map_of_SomeI intro!: bexI[rotated, OF map_of_SomeD]
      split: if_splits option.splits)

declare [[code drop: New_max_getIJ_genericJoin New_max_getIJ_wrapperGenericJoin]]
declare New_max.genericJoin.simps[folded remove_Union_def, code]
declare New_max.wrapperGenericJoin.simps[folded remove_Union_def, code]

(*<*)
end
(*>*)
