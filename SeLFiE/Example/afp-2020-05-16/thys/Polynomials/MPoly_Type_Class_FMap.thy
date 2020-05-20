(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Executable Representation of Polynomial Mappings as Association Lists\<close>

theory MPoly_Type_Class_FMap
  imports
    MPoly_Type_Class_Ordered
    Poly_Mapping_Finite_Map
begin

text \<open>In this theory, (type class) multivariate polynomials of type
  @{typ "('a, 'b) poly_mapping"} are represented as association lists.\<close>

text \<open>It is important to note that theory \<open>MPoly_Type_Class_OAlist\<close>, which represents polynomials as
  @{emph \<open>ordered\<close>} associative lists, is much better suited for doing actual computations. This
  theory is only included for being able to compare the two representations in terms of efficiency.\<close>

subsection \<open>Power Products\<close>

lemma compute_lcs_pp[code]:
  "lcs (Pm_fmap xs) (Pm_fmap ys) =
  Pm_fmap (fmmap_keys (\<lambda>k v. Orderings.max (lookup0 xs k) (lookup0 ys k)) (xs ++\<^sub>f ys))"
  by (rule poly_mapping_eqI)
    (auto simp add: fmlookup_default_fmmap_keys fmlookup_dom_iff fmdom'_notI
      lcs_poly_mapping.rep_eq fmdom'_notD)

lemma compute_deg_pp[code]:
  "deg_pm (Pm_fmap xs) = sum (the o fmlookup xs) (fmdom' xs)"
proof -
  have "deg_pm (Pm_fmap xs) = sum (lookup (Pm_fmap xs)) (keys (Pm_fmap xs))"
    by (rule deg_pm_superset) auto
  also have "\<dots> = sum (the o fmlookup xs) (fmdom' xs)"
    by (rule sum.mono_neutral_cong_left)
       (auto simp: fmlookup_dom'_iff fmdom'I in_keys_iff fmlookup_default_def
             split: option.splits)
  finally show ?thesis .
qed

definition adds_pp_add_linorder :: "('b \<Rightarrow>\<^sub>0 'a::add_linorder) \<Rightarrow> _ \<Rightarrow> bool"
  where [code_abbrev]: "adds_pp_add_linorder = (adds)"

lemma compute_adds_pp[code]:
  "adds_pp_add_linorder (Pm_fmap xs) (Pm_fmap ys) =
    (fmpred (\<lambda>k v. lookup0 xs k \<le> lookup0 ys k) (xs ++\<^sub>f ys))"
  for xs ys::"('a, 'b::add_linorder_min) fmap"
  unfolding adds_pp_add_linorder_def
  unfolding adds_poly_mapping
  using fmdom_notI
  by (force simp: fmlookup_dom_iff le_fun_def
      split: option.splits if_splits)


text\<open>Computing @{term lex} as below is certainly not the most efficient way, but it works.\<close>

lemma lex_pm_iff: "lex_pm s t = (\<forall>x. lookup s x \<le> lookup t x \<or> (\<exists>y<x. lookup s y \<noteq> lookup t y))"
proof -
  have "lex_pm s t = (\<not> lex_pm_strict t s)" by (simp add: lex_pm_strict_alt)
  also have "\<dots> = (\<forall>x. lookup s x \<le> lookup t x \<or> (\<exists>y<x. lookup s y \<noteq> lookup t y))"
    by (simp add: lex_pm_strict_def less_poly_mapping_def less_fun_def) (metis leD leI)
  finally show ?thesis .
qed

lemma compute_lex_pp[code]:
  "(lex_pm (Pm_fmap xs) (Pm_fmap (ys::(_, _::ordered_comm_monoid_add) fmap))) =
    (let zs = xs ++\<^sub>f ys in
      fmpred (\<lambda>x v.
        lookup0 xs x \<le> lookup0 ys x \<or>
        \<not> fmpred (\<lambda>y w. y \<ge> x \<or> lookup0 xs y = lookup0 ys y) zs) zs
    )"
  unfolding Let_def lex_pm_iff fmpred_iff Pm_fmap.rep_eq fmlookup_add fmlookup_dom_iff
  apply (intro iffI)
   apply (metis fmdom'_notD fmlookup_default_if(2) fmlookup_dom'_iff leD)
  apply (metis eq_iff not_le fmdom'_notD fmlookup_default_if(2) fmlookup_dom'_iff)
  done

lemma compute_dord_pp[code]:
  "(dord_pm ord (Pm_fmap xs) (Pm_fmap (ys::('a::wellorder , 'b::ordered_comm_monoid_add) fmap))) =
    (let dx = deg_pm (Pm_fmap xs) in let dy = deg_pm (Pm_fmap ys) in
      dx < dy \<or> (dx = dy \<and> ord (Pm_fmap xs) (Pm_fmap ys))
    )"
  by (auto simp: Let_def deg_pm.rep_eq dord_fun_def dord_pm.rep_eq)
    (simp_all add: Pm_fmap.abs_eq)


subsubsection \<open>Computations\<close>

experiment begin

abbreviation "X \<equiv> 0::nat"
abbreviation "Y \<equiv> 1::nat"
abbreviation "Z \<equiv> 2::nat"

lemma
  "sparse\<^sub>0 [(X, 2::nat), (Z, 7)] + sparse\<^sub>0 [(Y, 3), (Z, 2)] = sparse\<^sub>0 [(X, 2), (Z, 9), (Y, 3)]"
  "dense\<^sub>0 [2, 0, 7::nat] + dense\<^sub>0 [0, 3, 2] = dense\<^sub>0 [2, 3, 9]"
  by eval+

lemma
  "sparse\<^sub>0 [(X, 2::nat), (Z, 7)] - sparse\<^sub>0 [(X, 2), (Z, 2)] = sparse\<^sub>0 [(Z, 5)]"
  by eval

lemma
  "lcs (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 7)]) (sparse\<^sub>0 [(Y, 3), (Z, 2)]) = sparse\<^sub>0 [(X, 2), (Y, 3), (Z, 7)]"
  by eval

lemma
  "(sparse\<^sub>0 [(X, 2::nat), (Z, 1)]) adds (sparse\<^sub>0 [(X, 3), (Y, 2), (Z, 1)])"
  by eval

lemma
  "lookup (sparse\<^sub>0 [(X, 2::nat), (Z, 3)]) X = 2"
  by eval

lemma
  "deg_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3), (X, 1)]) = 6"
  by eval

lemma
  "lex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)])"
by eval

lemma
  "lex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)])"
  by eval

lemma
  "\<not> (dlex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 3)]) (sparse\<^sub>0 [(X, 4)]))"
  by eval

lemma
  "dlex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 2)]) (sparse\<^sub>0 [(X, 5)])"
  by eval

lemma
  "\<not> (drlex_pm (sparse\<^sub>0 [(X, 2::nat), (Y, 1), (Z, 2)]) (sparse\<^sub>0 [(X, 5)]))"
  by eval

end


subsection \<open>Implementation of Multivariate Polynomials as Association Lists\<close>

subsubsection \<open>Unordered Power-Products\<close>

lemma compute_monomial [code]:
  "monomial c t = (if c = 0 then 0 else sparse\<^sub>0 [(t, c)])"
  by (auto intro!: poly_mapping_eqI simp: sparse\<^sub>0_def fmlookup_default_def lookup_single)

lemma compute_one_poly_mapping [code]: "1 = sparse\<^sub>0 [(0, 1)]"
  by (metis compute_monomial single_one zero_neq_one)

lemma compute_except_poly_mapping [code]:
  "except (Pm_fmap xs) S = Pm_fmap (fmfilter (\<lambda>k. k \<notin> S) xs)"
  by (auto simp: fmlookup_default_def lookup_except split: option.splits intro!: poly_mapping_eqI)

lemma lookup0_fmap_of_list_simps:
  "lookup0 (fmap_of_list ((x, y)#xs)) i = (if x = i then y else lookup0 (fmap_of_list xs) i)"
  "lookup0 (fmap_of_list []) i = 0"
  by (auto simp: fmlookup_default_def fmlookup_of_list split: if_splits option.splits)

lemma if_poly_mapping_eq_iff:
  "(if x = y then a else b) =
    (if (\<forall>i\<in>keys x \<union> keys y. lookup x i = lookup y i) then a else b)"
  by simp (metis UnI1 UnI2 in_keys_iff poly_mapping_eqI)

lemma keys_add_eq: "keys (a + b) = keys a \<union> keys b - {x \<in> keys a \<inter> keys b. lookup a x + lookup b x = 0}"
  by (auto simp: in_keys_iff lookup_add add_eq_0_iff)

context term_powerprod
begin

context includes fmap.lifting begin

lift_definition shift_keys::"'a \<Rightarrow> ('t, 'b) fmap \<Rightarrow> ('t, 'b) fmap"
  is "\<lambda>t m x. if t adds\<^sub>p x then m (x \<ominus> t) else None"
proof -
  fix t and f::"'t \<Rightarrow> 'b option"
  assume "finite (dom f)"
  have "dom (\<lambda>x. if t adds\<^sub>p x then f (x \<ominus> t) else None) \<subseteq> (\<oplus>) t ` dom f"
    by (auto simp: adds_pp_alt domI term_simps split: if_splits)
  also have "finite \<dots>"
    using \<open>finite (dom f)\<close> by simp
  finally (finite_subset) show "finite (dom (\<lambda>x. if t adds\<^sub>p x then f (x \<ominus> t) else None))" .
qed

definition "shift_map_keys t f m = fmmap f (shift_keys t m)"

lemma compute_shift_map_keys[code]:
  "shift_map_keys t f (fmap_of_list xs) = fmap_of_list (map (\<lambda>(k, v). (t \<oplus> k, f v)) xs)"
  unfolding shift_map_keys_def
  apply transfer
  subgoal for f t xs
  proof -
    show ?thesis
      apply (rule ext)
      subgoal for x
        apply (cases "t adds\<^sub>p x")
        subgoal by (induction xs) (auto simp: adds_pp_alt term_simps)
        subgoal by (induction xs) (auto simp: adds_pp_alt term_simps)
        done
      done
  qed
  done

end

lemmas [simp] = compute_zero_pp[symmetric]

lemma compute_monom_mult_poly_mapping [code]:
  "monom_mult c t (Pm_fmap xs) = Pm_fmap (if c = 0 then fmempty else shift_map_keys t ((*) c) xs)"
proof (cases "c = 0")
  case True
  hence "monom_mult c t (Pm_fmap xs) = 0" using monom_mult_zero_left by simp
  thus ?thesis using True
    by simp
next
  case False
  thus ?thesis
    by (auto simp: simp: fmlookup_default_def shift_map_keys_def lookup_monom_mult
        adds_def group_eq_aux shift_keys.rep_eq
        intro!: poly_mapping_eqI split: option.splits)
qed

lemma compute_mult_scalar_poly_mapping [code]:
  "Pm_fmap (fmap_of_list xs) \<odot> q = (case xs of ((t, c) # ys) \<Rightarrow>
    (monom_mult c t q + except (Pm_fmap (fmap_of_list ys)) {t} \<odot> q) | _ \<Rightarrow>
    Pm_fmap fmempty)"
proof (split list.splits, simp, intro conjI impI allI, goal_cases)
  case (1 t c ys)
  have "Pm_fmap (fmupd t c (fmap_of_list ys)) = sparse\<^sub>0 [(t, c)] + except (sparse\<^sub>0 ys) {t}"
    by (auto simp: sparse\<^sub>0_def fmlookup_default_def lookup_add lookup_except
        split: option.splits intro!: poly_mapping_eqI)
  also have "sparse\<^sub>0 [(t, c)] = monomial c t"
    by (auto simp: sparse\<^sub>0_def lookup_single fmlookup_default_def intro!: poly_mapping_eqI)
  finally show ?case
    by (simp add: algebra_simps mult_scalar_monomial sparse\<^sub>0_def)
qed

end (* term_powerprod *)

subsubsection \<open>restore constructor view\<close>

named_theorems mpoly_simps

definition "monomial1 pp = monomial 1 pp"

lemma monomial1_Nil[mpoly_simps]: "monomial1 0 = 1"
  by (simp add: monomial1_def)

lemma monomial_mp: "monomial c (pp::'a\<Rightarrow>\<^sub>0nat) = Const\<^sub>0 c * monomial1 pp"
  for c::"'b::comm_semiring_1"
  by (auto intro!: poly_mapping_eqI simp: monomial1_def Const\<^sub>0_def mult_single)

lemma monomial1_add: "(monomial1 (a + b)::('a::monoid_add\<Rightarrow>\<^sub>0'b::comm_semiring_1)) = monomial1 a * monomial1 b"
  by (auto simp: monomial1_def mult_single)

lemma monomial1_monomial: "monomial1 (monomial n v) = (Var\<^sub>0 v::_\<Rightarrow>\<^sub>0('b::comm_semiring_1))^n"
  by (auto intro!: poly_mapping_eqI simp: monomial1_def Var\<^sub>0_power lookup_single when_def)

lemma Ball_True: "(\<forall>x\<in>X. True) \<longleftrightarrow> True" by auto
lemma Collect_False: "{x. False} = {}" by simp

lemma Pm_fmap_sum: "Pm_fmap f = (\<Sum>x \<in> fmdom' f. monomial (lookup0 f x) x)"
  including fmap.lifting
  by (auto intro!: poly_mapping_eqI sum.neutral
      simp: fmlookup_default_def lookup_sum lookup_single when_def fmdom'I
      split: option.splits)

lemma MPoly_numeral: "MPoly (numeral x) = numeral x"
  by (metis monom.abs_eq monom_numeral single_numeral)

lemma MPoly_power: "MPoly (x ^ n) = MPoly x ^ n"
  by (induction n) (auto simp: one_mpoly_def times_mpoly.abs_eq[symmetric])

lemmas [mpoly_simps] = Pm_fmap_sum
  add.assoc[symmetric] mult.assoc[symmetric]
  add_0 add_0_right mult_1 mult_1_right mult_zero_left mult_zero_right power_0 power_one_right
  fmdom'_fmap_of_list
  list.map fst_conv
  sum.insert_remove finite_insert finite.emptyI
  lookup0_fmap_of_list_simps
  num.simps rel_simps
  if_True if_False
  insert_Diff_if insert_iff empty_Diff empty_iff
  simp_thms
  sum.empty
  if_poly_mapping_eq_iff
  keys_zero keys_one
  keys_add_eq
  keys_single
  Un_insert_left Un_empty_left
  Int_insert_left Int_empty_left
  Collect_False
  lookup_add lookup_single lookup_zero lookup_one
  Set.ball_simps
  when_simps
  monomial_mp
  monomial1_add
  monomial1_monomial
  Const\<^sub>0_one Const\<^sub>0_zero Const\<^sub>0_numeral Const\<^sub>0_minus
  set_simps

text \<open>A simproc for postprocessing with \<open>mpoly_simps\<close> and not polluting \<open>[code_post]\<close>:\<close>

ML \<open>val mpoly_simproc = Simplifier.make_simproc @{context} "multivariate polynomials"
      {lhss = [@{term "Pm_fmap mpp::(_ \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 _"}],
       proc = (K (fn ctxt => fn ct =>
          SOME (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps
            (Named_Theorems.get ctxt (\<^named_theorems>\<open>mpoly_simps\<close>))) ct)))}\<close>

(* The simproc slows down computations *a lot*, so it is deactivated by default. *)

(* setup \<open>Code_Preproc.map_post (fn ctxt => ctxt addsimprocs [mpoly_simproc])\<close> *)


subsubsection \<open>Ordered Power-Products\<close>

lemma foldl_assoc:
  assumes "\<And>x y z. f (f x y) z = f x (f y z)"
  shows "foldl f (f a b) xs = f a (foldl f b xs)"
proof (induct xs arbitrary: a b)
  fix a b
  show "foldl f (f a b) [] = f a (foldl f b [])" by simp
next
  fix a b x xs
  assume "\<And>a b. foldl f (f a b) xs = f a (foldl f b xs)"
  from assms[of a b x] this[of a "f b x"]
    show "foldl f (f a b) (x # xs) = f a (foldl f b (x # xs))" unfolding foldl_Cons by simp
qed

context ordered_term
begin

definition list_max::"'t list \<Rightarrow> 't" where
  "list_max xs \<equiv> foldl ord_term_lin.max min_term xs"

lemma list_max_Cons: "list_max (x # xs) = ord_term_lin.max x (list_max xs)"
  unfolding list_max_def foldl_Cons
proof -
  have "foldl ord_term_lin.max (ord_term_lin.max x min_term) xs =
          ord_term_lin.max x (foldl ord_term_lin.max min_term xs)"
    by (rule foldl_assoc, rule ord_term_lin.max.assoc)
  from this ord_term_lin.max.commute[of min_term x]
    show "foldl ord_term_lin.max (ord_term_lin.max min_term x) xs =
            ord_term_lin.max x (foldl ord_term_lin.max min_term xs)" by simp
qed

lemma list_max_empty: "list_max [] = min_term"
  unfolding list_max_def by simp

lemma list_max_in_list:
  assumes "xs \<noteq> []"
  shows "list_max xs \<in> set xs"
  using assms
proof (induct xs, simp)
  fix x xs
  assume IH: "xs \<noteq> [] \<Longrightarrow> list_max xs \<in> set xs"
  show "list_max (x # xs) \<in> set (x # xs)"
  proof (cases "xs = []")
    case True
    hence "list_max (x # xs) = ord_term_lin.max min_term x" unfolding list_max_def by simp
    also have "\<dots> = x" unfolding ord_term_lin.max_def by (simp add: min_term_min)
    finally show ?thesis by simp
  next
    assume "xs \<noteq> []"
    show ?thesis
    proof (cases "x \<preceq>\<^sub>t list_max xs")
      case True
      hence "list_max (x # xs) = list_max xs"
        unfolding list_max_Cons ord_term_lin.max_def by simp
      thus ?thesis using IH[OF \<open>xs \<noteq> []\<close>] by simp
    next
      case False
      hence "list_max (x # xs) = x" unfolding list_max_Cons ord_term_lin.max_def by simp
      thus ?thesis by simp
    qed
  qed
qed

lemma list_max_maximum:
  assumes "a \<in> set xs"
  shows "a \<preceq>\<^sub>t (list_max xs)"
  using assms
proof (induct xs)
  assume "a \<in> set []"
  thus "a \<preceq>\<^sub>t list_max []" by simp
next
  fix x xs
  assume IH: "a \<in> set xs \<Longrightarrow> a \<preceq>\<^sub>t list_max xs" and a_in: "a \<in> set (x # xs)"
  from a_in have "a = x \<or> a \<in> set xs" by simp
  thus "a \<preceq>\<^sub>t list_max (x # xs)" unfolding list_max_Cons
  proof
    assume "a = x"
    thus "a \<preceq>\<^sub>t ord_term_lin.max x (list_max xs)" by simp
  next
    assume "a \<in> set xs"
    from IH[OF this] show "a \<preceq>\<^sub>t ord_term_lin.max x (list_max xs)"
      by (simp add: ord_term_lin.le_max_iff_disj)
  qed
qed

lemma list_max_nonempty:
  assumes "xs \<noteq> []"
  shows "list_max xs = ord_term_lin.Max (set xs)"
proof -
  have fin: "finite (set xs)" by simp
  have "ord_term_lin.Max (set xs) = list_max xs"
  proof (rule ord_term_lin.Max_eqI[OF fin, of "list_max xs"])
    fix y
    assume "y \<in> set xs"
    from list_max_maximum[OF this] show "y \<preceq>\<^sub>t list_max xs" .
  next
    from list_max_in_list[OF assms] show "list_max xs \<in> set xs" .
  qed
  thus ?thesis by simp
qed

lemma in_set_clearjunk_iff_map_of_eq_Some:
  "(a, b) \<in> set (AList.clearjunk xs) \<longleftrightarrow> map_of xs a = Some b"
  by (metis Some_eq_map_of_iff distinct_clearjunk map_of_clearjunk)

lemma Pm_fmap_of_list_eq_zero_iff:
  "Pm_fmap (fmap_of_list xs) = 0 \<longleftrightarrow> [(k, v)\<leftarrow>AList.clearjunk xs . v \<noteq> 0] = []"
  by (auto simp: poly_mapping_eq_iff fmlookup_default_def fun_eq_iff
    in_set_clearjunk_iff_map_of_eq_Some filter_empty_conv fmlookup_of_list split: option.splits)

lemma fmdom'_clearjunk0: "fmdom' (clearjunk0 xs) = fmdom' xs - {x. fmlookup xs x = Some 0}"
  by (metis (no_types, lifting) clearjunk0_def fmdom'_drop_set fmfilter_alt_defs(2) fmfilter_cong' mem_Collect_eq)

lemma compute_lt_poly_mapping[code]:
  "lt (Pm_fmap (fmap_of_list xs)) = list_max (map fst [(k, v) \<leftarrow> AList.clearjunk xs. v \<noteq> 0])"
proof -
  have "keys (Pm_fmap (fmap_of_list xs)) = fst ` {x \<in> set (AList.clearjunk xs). case x of (k, v) \<Rightarrow> v \<noteq> 0}"
    by (auto simp: compute_keys_pp fmdom'_clearjunk0 fmap_of_list.rep_eq
        in_set_clearjunk_iff_map_of_eq_Some fmdom'I image_iff fmlookup_dom'_iff)
  then show ?thesis
    unfolding lt_def
    by (auto simp: Pm_fmap_of_list_eq_zero_iff list_max_empty list_max_nonempty)
qed

lemma compute_higher_poly_mapping [code]:
  "higher (Pm_fmap xs) t = Pm_fmap (fmfilter (\<lambda>k. t \<prec>\<^sub>t k) xs)"
  unfolding higher_def compute_except_poly_mapping
  by (metis mem_Collect_eq ord_term_lin.leD ord_term_lin.leI)

lemma compute_lower_poly_mapping [code]:
  "lower (Pm_fmap xs) t = Pm_fmap (fmfilter (\<lambda>k. k \<prec>\<^sub>t t) xs)"
  unfolding lower_def compute_except_poly_mapping
  by (metis mem_Collect_eq ord_term_lin.leD ord_term_lin.leI)

end (* ordered_term *)

lifting_update poly_mapping.lifting
lifting_forget poly_mapping.lifting

subsection \<open>Computations\<close>

subsubsection \<open>Scalar Polynomials\<close>

type_synonym 'a mpoly_tc = "(nat \<Rightarrow>\<^sub>0 nat)\<Rightarrow>\<^sub>0'a"

definition "shift_map_keys_punit = term_powerprod.shift_map_keys to_pair_unit fst"

lemma compute_shift_map_keys_punit [code]:
  "shift_map_keys_punit t f (fmap_of_list xs) = fmap_of_list (map (\<lambda>(k, v). (t + k, f v)) xs)"
  by (simp add: punit.compute_shift_map_keys shift_map_keys_punit_def)

global_interpretation punit: term_powerprod to_pair_unit fst
  rewrites "punit.adds_term = (adds)"
  and "punit.pp_of_term = (\<lambda>x. x)"
  and "punit.component_of_term = (\<lambda>_. ())"
  defines monom_mult_punit = punit.monom_mult
  and mult_scalar_punit = punit.mult_scalar
  apply (fact MPoly_Type_Class.punit.term_powerprod_axioms)
  apply (fact MPoly_Type_Class.punit_adds_term)
  apply (fact MPoly_Type_Class.punit_pp_of_term)
  apply (fact MPoly_Type_Class.punit_component_of_term)
  done

lemma compute_monom_mult_punit [code]:
  "monom_mult_punit c t (Pm_fmap xs) = Pm_fmap (if c = 0 then fmempty else shift_map_keys_punit t ((*) c) xs)"
  by (simp add: monom_mult_punit_def punit.compute_monom_mult_poly_mapping shift_map_keys_punit_def)

lemma compute_mult_scalar_punit [code]:
  "Pm_fmap (fmap_of_list xs) * q = (case xs of ((t, c) # ys) \<Rightarrow>
    (monom_mult_punit c t q + except (Pm_fmap (fmap_of_list ys)) {t} * q) | _ \<Rightarrow>
    Pm_fmap fmempty)"
  by (simp only: punit_mult_scalar[symmetric] punit.compute_mult_scalar_poly_mapping monom_mult_punit_def)

locale trivariate\<^sub>0_rat
begin

abbreviation X::"rat mpoly_tc" where "X \<equiv> Var\<^sub>0 (0::nat)"
abbreviation Y::"rat mpoly_tc" where "Y \<equiv> Var\<^sub>0 (1::nat)"
abbreviation Z::"rat mpoly_tc" where "Z \<equiv> Var\<^sub>0 (2::nat)"

end

locale trivariate
begin

abbreviation "X \<equiv> Var 0"
abbreviation "Y \<equiv> Var 1"
abbreviation "Z \<equiv> Var 2"

end

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "keys (X\<^sup>2 * Z ^ 3 + 2 * Y ^ 3 * Z\<^sup>2) =
    {monomial 2 0 + monomial 3 2, monomial 3 1 + monomial 2 2}"
  by eval

lemma
  "keys (X\<^sup>2 * Z ^ 3 + 2 * Y ^ 3 * Z\<^sup>2) =
    {monomial 2 0 + monomial 3 2, monomial 3 1 + monomial 2 2}"
  by eval

lemma
  "- 1 * X\<^sup>2 * Z ^ 7 + - 2 * Y ^ 3 * Z\<^sup>2 = - X\<^sup>2 * Z ^ 7 + - 2 * Y ^ 3 * Z\<^sup>2"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 + X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2 = X\<^sup>2 * Z ^ 7 + X\<^sup>2 * Z ^ 4"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 - X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2 =
    X\<^sup>2 * Z ^ 7 - X\<^sup>2 * Z ^ 4"
  by eval

lemma
  "lookup (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 + 2) (sparse\<^sub>0 [(0, 2), (2, 7)]) = 1"
  by eval

lemma
  "X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2 \<noteq>
   X\<^sup>2 * Z ^ 4 + - 2 * Y ^ 3 * Z\<^sup>2"
  by eval


lemma
  "0 * X^2 * Z^7 + 0 * Y^3*Z\<^sup>2 = 0"
  by eval

lemma
  "monom_mult_punit 3 (sparse\<^sub>0 [(1, 2::nat)]) (X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) =
    3 * Y\<^sup>2 * Z * X\<^sup>2 + 6 * Y ^ 5 * Z\<^sup>2"
  by eval

lemma
  "monomial (-4) (sparse\<^sub>0 [(0, 2::nat)]) = - 4 * X\<^sup>2"
  by eval

lemma "monomial (0::rat) (sparse\<^sub>0 [(0::nat, 2::nat)]) = 0"
  by eval

lemma
  "(X\<^sup>2 * Z + 2 * Y ^ 3 * Z\<^sup>2) * (X\<^sup>2 * Z ^ 3 + - 2 * Y ^ 3 * Z\<^sup>2) =
    X ^ 4 * Z ^ 4 + - 2 * X\<^sup>2 * Z ^ 3 * Y ^ 3 +
 - 4 * Y ^ 6 * Z ^ 4 + 2 * Y ^ 3 * Z ^ 5 * X\<^sup>2"
  by eval

end

subsubsection \<open>Vector-Polynomials\<close>

type_synonym 'a vmpoly_tc = "((nat \<Rightarrow>\<^sub>0 nat) \<times> nat) \<Rightarrow>\<^sub>0 'a"

definition "shift_map_keys_pprod = pprod.shift_map_keys"

global_interpretation pprod: term_powerprod "\<lambda>x. x" "\<lambda>x. x"
  rewrites "pprod.pp_of_term = fst"
  and "pprod.component_of_term = snd"
  defines splus_pprod = pprod.splus
  and monom_mult_pprod = pprod.monom_mult
  and mult_scalar_pprod = pprod.mult_scalar
  and adds_term_pprod = pprod.adds_term
  apply (fact MPoly_Type_Class.pprod.term_powerprod_axioms)
  apply (fact MPoly_Type_Class.pprod_pp_of_term)
  apply (fact MPoly_Type_Class.pprod_component_of_term)
  done

lemma compute_adds_term_pprod [code_unfold]:
  "adds_term_pprod u v = (snd u = snd v \<and> adds_pp_add_linorder (fst u) (fst v))"
  by (simp add: adds_term_pprod_def pprod.adds_term_def adds_pp_add_linorder_def)

lemma compute_splus_pprod [code]: "splus_pprod t (s, i) = (t + s, i)"
  by (simp add: splus_pprod_def pprod.splus_def)

lemma compute_shift_map_keys_pprod [code]:
  "shift_map_keys_pprod t f (fmap_of_list xs) = fmap_of_list (map (\<lambda>(k, v). (splus_pprod t k, f v)) xs)"
  by (simp add: pprod.compute_shift_map_keys shift_map_keys_pprod_def splus_pprod_def)

lemma compute_monom_mult_pprod [code]:
  "monom_mult_pprod c t (Pm_fmap xs) = Pm_fmap (if c = 0 then fmempty else shift_map_keys_pprod t ((*) c) xs)"
  by (simp add: monom_mult_pprod_def pprod.compute_monom_mult_poly_mapping shift_map_keys_pprod_def)

lemma compute_mult_scalar_pprod [code]:
  "mult_scalar_pprod (Pm_fmap (fmap_of_list xs)) q = (case xs of ((t, c) # ys) \<Rightarrow>
    (monom_mult_pprod c t q + mult_scalar_pprod (except (Pm_fmap (fmap_of_list ys)) {t}) q) | _ \<Rightarrow>
    Pm_fmap fmempty)"
  by (simp only: mult_scalar_pprod_def pprod.compute_mult_scalar_poly_mapping monom_mult_pprod_def)

definition Vec\<^sub>0 :: "nat \<Rightarrow> (('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 nat) \<times> nat) \<Rightarrow>\<^sub>0 'b::semiring_1" where
  "Vec\<^sub>0 i p = mult_scalar_pprod p (Poly_Mapping.single (0, i) 1)"

experiment begin interpretation trivariate\<^sub>0_rat .

lemma
  "keys (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3) + Vec\<^sub>0 1 (2 * Y ^ 3 * Z\<^sup>2)) =
    {(sparse\<^sub>0 [(0, 2), (2, 3)], 0), (sparse\<^sub>0 [(1, 3), (2, 2)], 1)}"
  by eval

lemma
  "keys (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 3) + Vec\<^sub>0 2 (2 * Y ^ 3 * Z\<^sup>2)) =
    {(sparse\<^sub>0 [(0, 2), (2, 3)], 0), (sparse\<^sub>0 [(1, 3), (2, 2)], 2)}"
  by eval

lemma
  "Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 7 + 2 * Y ^ 3 * Z\<^sup>2) + Vec\<^sub>0 3 (X\<^sup>2 * Z ^ 4) + Vec\<^sub>0 1 (- 2 * Y ^ 3 * Z\<^sup>2) =
    Vec\<^sub>0 1 (X\<^sup>2 * Z ^ 7) + Vec\<^sub>0 3 (X\<^sup>2 * Z ^ 4)"
  by eval

lemma
  "lookup (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 7) + Vec\<^sub>0 1 (2 * Y ^ 3 * Z\<^sup>2 + 2)) (sparse\<^sub>0 [(0, 2), (2, 7)], 0) = 1"
  by eval

lemma
  "lookup (Vec\<^sub>0 0 (X\<^sup>2 * Z ^ 7) + Vec\<^sub>0 1 (2 * Y ^ 3 * Z\<^sup>2 + 2)) (sparse\<^sub>0 [(0, 2), (2, 7)], 1) = 0"
  by eval

lemma
  "Vec\<^sub>0 0 (0 * X^2 * Z^7) + Vec\<^sub>0 1 (0 * Y^3*Z\<^sup>2) = 0"
  by eval

lemma
  "monom_mult_pprod 3 (sparse\<^sub>0 [(1, 2::nat)]) (Vec\<^sub>0 0 (X\<^sup>2 * Z) + Vec\<^sub>0 1 (2 * Y ^ 3 * Z\<^sup>2)) =
    Vec\<^sub>0 0 (3 * Y\<^sup>2 * Z * X\<^sup>2) + Vec\<^sub>0 1 (6 * Y ^ 5 * Z\<^sup>2)"
  by eval

end

subsection \<open>Code setup for type MPoly\<close>

text \<open>postprocessing from \<open>Var\<^sub>0, Const\<^sub>0\<close> to \<open>Var, Const\<close>.\<close>

lemmas [code_post] =
  plus_mpoly.abs_eq[symmetric]
  times_mpoly.abs_eq[symmetric]
  MPoly_numeral
  MPoly_power
  one_mpoly_def[symmetric]
  Var.abs_eq[symmetric]
  Const.abs_eq[symmetric]

instantiation mpoly::("{equal, zero}")equal begin

lift_definition equal_mpoly:: "'a mpoly \<Rightarrow> 'a mpoly \<Rightarrow> bool" is HOL.equal .

instance proof standard qed (transfer, rule equal_eq)

end

experiment begin interpretation trivariate .

lemmas [mpoly_simps] = plus_mpoly.abs_eq

lemma "content_primitive (4 * X * Y^2 * Z^3 + 6 * X\<^sup>2 * Y^4 + 8 * X\<^sup>2 * Y^5) =
    (2::int, 2 * X * Y\<^sup>2 * Z ^ 3 + 3 * X\<^sup>2 * Y ^ 4 + 4 * X\<^sup>2 * Y ^ 5)"
  by eval

end

end (* theory *)
