theory Abstract_Rigorous_Numerics
imports
  "HOL-Library.Parallel"
  Transfer_Euclidean_Space_Vector
  "../Refinement/Enclosure_Operations"
  "../Refinement/Refine_Vector_List"
  "../Refinement/Refine_Hyperplane"
  "../Refinement/Refine_Interval"
  "../Refinement/Refine_Invar"
  "../Refinement/Refine_Unions"
  "../Refinement/Refine_Info"
begin

section \<open>misc\<close>

lemma length_listset: "xi \<in> listset xs \<Longrightarrow> length xi = length xs"
  by (induction xs arbitrary: xi) (auto simp: set_Cons_def)

lemma Nil_mem_listset[simp]: "[] \<in> listset list \<longleftrightarrow> list = []"
  by (induction list) (auto simp: set_Cons_def)

lemma sing_mem_listset_iff[simp]: "[b] \<in> listset ys \<longleftrightarrow> (\<exists>z. ys = [z] \<and> b \<in> z)"
  \<comment> \<open>TODO: generalize to Cons?\<close>
  by (cases ys) (auto simp: set_Cons_def)


no_notation (in autoref_syn) funcset (infixr "\<rightarrow>" 60)

definition cfuncset where "cfuncset l u X = funcset {l .. u} X \<inter> Collect (continuous_on {l .. u})"
lemma cfuncset_iff: "f \<in> cfuncset l u X \<longleftrightarrow> (\<forall>i\<in>{l .. u}. f i \<in> X) \<and> continuous_on {l .. u} f"
  unfolding cfuncset_def by auto

lemma cfuncset_continuous_onD: "f \<in> cfuncset 0 h X \<Longrightarrow> continuous_on {0..h} f"
  by (simp add: cfuncset_iff)


section \<open>Implementations\<close>

subsection \<open>locale for sets\<close>

definition "product_listset xs ys = (\<lambda>(x, y). x @ y) ` ((xs::real list set) \<times> (ys::real list set))"

abbreviation "rl_rel \<equiv> \<langle>rnv_rel\<rangle>list_rel"

abbreviation "slp_rel \<equiv> \<langle>Id::floatarith rel\<rangle>list_rel"
abbreviation "fas_rel \<equiv> \<langle>Id::floatarith rel\<rangle>list_rel"

type_synonym 'b reduce_argument = "'b list \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> bool" \<comment> \<open>is this too special?\<close>

record 'b numeric_options =
  precision :: nat
  adaptive_atol :: real
  adaptive_rtol :: real
  method_id :: nat
  start_stepsize :: real
  iterations :: nat
  halve_stepsizes :: nat
  widening_mod :: nat
  rk2_param :: real
  default_reduce :: "'b reduce_argument"
  printing_fun :: "bool \<Rightarrow> 'b list \<Rightarrow> unit"
  tracing_fun :: "string \<Rightarrow> 'b list option \<Rightarrow> unit"

record 'b reach_options =
  max_tdev_thres :: "real"
  pre_split_reduce :: "'b reduce_argument"
  pre_inter_granularity :: "real"
  post_inter_granularity :: "real"
  pre_collect_granularity :: real
  max_intersection_step :: real

definition "reach_options_rel TYPE('b) = (UNIV::('b reach_options \<times> unit) set)"
lemma sv_reach_options_rel[relator_props]: "single_valued (reach_options_rel TYPE('a))"
  by (auto simp: reach_options_rel_def single_valued_def)

definition "reduce_argument_rel TYPE('b) = (UNIV::('b reduce_argument \<times> unit) set)"
lemma sv_reduce_argument_rel[relator_props]: "single_valued (reduce_argument_rel TYPE('a))"
  by (auto simp: reduce_argument_rel_def single_valued_def)


definition [refine_vcg_def, simp]: "max_tdev_thres_spec (ro::unit) = SPEC (\<lambda>x::real. True)"
definition [refine_vcg_def, simp]: "max_intersection_step_spec (ro::unit) = SPEC (\<lambda>x::real. True)"
definition [refine_vcg_def, simp]: "pre_inter_granularity_spec (ro::unit) = SPEC (\<lambda>x::real. True)"
definition [refine_vcg_def, simp]: "post_inter_granularity_spec (ro::unit) = SPEC (\<lambda>x::real. True)"
definition [refine_vcg_def, simp]: "pre_collect_granularity_spec (ro::unit) = SPEC (\<lambda>x::real. True)"

lemma reach_optns_autoref[autoref_rules]:
  includes autoref_syntax
  shows
    "(\<lambda>x. RETURN (max_tdev_thres x), max_tdev_thres_spec) \<in> reach_options_rel TYPE('b) \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(\<lambda>x. RETURN (pre_inter_granularity x), pre_inter_granularity_spec) \<in> reach_options_rel TYPE('b)  \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(\<lambda>x. RETURN (post_inter_granularity x), post_inter_granularity_spec) \<in> reach_options_rel TYPE('b) \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(\<lambda>x. RETURN (pre_collect_granularity x), pre_collect_granularity_spec) \<in> reach_options_rel TYPE('b)  \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(\<lambda>x. RETURN (max_intersection_step x), max_intersection_step_spec) \<in> reach_options_rel TYPE('b)  \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
  by (auto simp: nres_rel_def)


record 'b approximate_set_ops =
  appr_of_ivl::"real list \<Rightarrow> real list \<Rightarrow> 'b list"
  product_appr::"'b list \<Rightarrow> 'b list \<Rightarrow> 'b list"
  msum_appr::"'b list \<Rightarrow> 'b list \<Rightarrow> 'b list"
  inf_of_appr::"'b numeric_options \<Rightarrow> 'b list \<Rightarrow> real list"
  sup_of_appr::"'b numeric_options \<Rightarrow> 'b list \<Rightarrow> real list"
  split_appr::"nat \<Rightarrow> 'b list \<Rightarrow> 'b list \<times> 'b list"
  appr_inf_inner::"'b numeric_options \<Rightarrow> 'b list \<Rightarrow> real list \<Rightarrow> real"
  appr_sup_inner::"'b numeric_options \<Rightarrow> 'b list \<Rightarrow> real list \<Rightarrow> real"
  inter_appr_plane::"'b numeric_options \<Rightarrow> 'b list \<Rightarrow> real list sctn \<Rightarrow> 'b list dres"
  reduce_appr::"'b numeric_options \<Rightarrow> 'b reduce_argument \<Rightarrow> 'b list \<Rightarrow> 'b list"
  width_appr::"'b numeric_options \<Rightarrow> 'b list \<Rightarrow> real"
  approx_slp_dres::"'b numeric_options \<Rightarrow> nat \<Rightarrow> slp \<Rightarrow> 'b list \<Rightarrow> 'b list option dres"
  approx_euclarithform::"'b numeric_options \<Rightarrow> form \<Rightarrow> 'b list \<Rightarrow> bool dres"
  approx_isFDERIV::"'b numeric_options \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> floatarith list \<Rightarrow> 'b list \<Rightarrow> bool dres"

primrec concat_appr where
  "concat_appr ops [] = []"
| "concat_appr ops (x#xs) = product_appr ops x (concat_appr ops xs)"


unbundle autoref_syntax

locale approximate_sets =
  fixes ops :: "'b approximate_set_ops"
    and set_of_appr::"'b list \<Rightarrow> real list set"
    and appr_rell :: "('b list \<times> real list set) set"
    and optns :: "'b numeric_options"
  assumes appr_rell_internal: "appr_rell \<equiv> br set_of_appr top"
  assumes transfer_operations_rl:
    "SIDE_PRECOND (list_all2 (\<le>) xrs yrs) \<Longrightarrow>
      (xri, xrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
      (yri, yrs) \<in> \<langle>rnv_rel\<rangle>list_rel \<Longrightarrow>
      (appr_of_ivl ops xri yri, lv_ivl $ xrs $ yrs) \<in> appr_rell"
    "(product_appr ops, product_listset) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
    "(msum_appr ops, (\<lambda>xs ys. {List.map2 (+) x y |x y. x \<in> xs \<and> y \<in> ys})) \<in> appr_rell \<rightarrow> appr_rell \<rightarrow> appr_rell"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (inf_of_appr ops optns xi), Inf_specs d x) \<in> \<langle>rl_rel\<rangle>nres_rel"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (sup_of_appr ops optns xi), Sup_specs d x) \<in> \<langle>rl_rel\<rangle>nres_rel"
    "(ni, n) \<in> nat_rel \<Longrightarrow> (xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow>
      (RETURN (split_appr ops ni xi), split_spec_params d n x) \<in> \<langle>appr_rell \<times>\<^sub>r appr_rell\<rangle>nres_rel"
    "(RETURN o2 appr_inf_inner ops optns, Inf_inners) \<in> appr_rell \<rightarrow> rl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(RETURN o2 appr_sup_inner ops optns, Sup_inners) \<in> appr_rell \<rightarrow> rl_rel \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow> length (normal si) = d \<Longrightarrow> d > 0 \<Longrightarrow> (si, s) \<in> \<langle>rl_rel\<rangle>sctn_rel \<Longrightarrow>
      (nres_of (inter_appr_plane ops optns xi si), inter_sctn_specs d x s) \<in> \<langle>appr_rell\<rangle>nres_rel"
    "(xi, x) \<in> appr_rell \<Longrightarrow> length xi = d \<Longrightarrow> (rai, ra) \<in> reduce_argument_rel TYPE('b) \<Longrightarrow>
      (RETURN (reduce_appr ops optns rai xi), reduce_specs d ra x) \<in> \<langle>appr_rell\<rangle>nres_rel"
    "(RETURN o width_appr ops optns, width_spec) \<in> appr_rell \<rightarrow> \<langle>rnv_rel\<rangle>nres_rel"
    "(nres_of o3 approx_slp_dres ops optns, approx_slp_spec fas) \<in> nat_rel \<rightarrow> slp_rel \<rightarrow> appr_rell \<rightarrow> \<langle>\<langle>appr_rell\<rangle>option_rel\<rangle>nres_rel"
assumes approx_euclarithform[unfolded comps, autoref_rules]:
  "(nres_of o2 approx_euclarithform ops optns, approx_form_spec) \<in> Id \<rightarrow> appr_rell \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
assumes approx_isFDERIV[unfolded comps, autoref_rules]:
  "(\<lambda>N xs fas vs. nres_of (approx_isFDERIV ops optns N xs fas vs), isFDERIV_spec) \<in>
  nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel \<rightarrow>  appr_rell \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
assumes set_of_appr_nonempty[simp]: "set_of_appr X \<noteq> {}"
assumes length_set_of_appr: "xrs \<in> set_of_appr xs \<Longrightarrow> length xrs = length xs"
assumes set_of_appr_project: "xrs \<in> set_of_appr xs \<Longrightarrow> (\<And>i. i \<in> set is \<Longrightarrow> i < length xs) \<Longrightarrow>
    map ((!) xrs) is \<in> set_of_appr (map ((!) xs) is)"
assumes set_of_apprs_ex_Cons: "xrs \<in> set_of_appr xs \<Longrightarrow> \<exists>r. r#xrs \<in> set_of_appr (b#xs)"
assumes set_of_apprs_Nil[simp]: "xrs \<in> set_of_appr [] \<longleftrightarrow> xrs = []"
begin

abbreviation "reach_optns_rel \<equiv> reach_options_rel TYPE('b)"

definition "appr_rel = appr_rell O \<langle>lv_rel\<rangle>set_rel"
lemmas [autoref_rel_intf] = REL_INTFI[of appr_rel i_appr]

definition [simp]: "op_concat_listset xs = concat ` listset xs"

lemma [autoref_op_pat_def]: "concat ` listset xs \<equiv> OP op_concat_listset $ xs"
  by simp

lemma list_all2_replicate [simp]: "list_all2 (\<le>) xs xs" for xs::"'a::order list"
  by (auto simp: list_all2_iff in_set_zip)

lemma length_appr_of_ivl[simp]:
  "length (appr_of_ivl ops xs ys) = length xs"
  if "list_all2 (\<le>) xs ys"
  using transfer_operations_rl(1)[of xs ys xs ys] that
    apply (simp add: appr_rell_internal br_def lv_ivl_def)
  apply (auto simp: appr_rell_internal br_def list_all2_lengthD dest!: length_set_of_appr)
  using length_set_of_appr by fastforce

definition [simp]: "op_atLeastAtMost_appr = atLeastAtMost"
lemma [autoref_op_pat]: "atLeastAtMost \<equiv> OP op_atLeastAtMost_appr"
  by simp

definition card_info::"_ set \<Rightarrow> nat nres" where [refine_vcg_def]: "card_info x = SPEC top" \<comment> \<open>\<open>op_set_wcard\<close>\<close>

definition [simp]: "set_of_coll X = X"

definition [simp]: "ivl_to_set X = X"

definition "ivls_of_sets X = do {
    XS \<leftarrow> (sets_of_coll (X:::clw_rel appr_rel) ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN (op_empty_coll:::clw_rel lvivl_rel))
      (\<lambda>X. do {
        (i, s) \<leftarrow> op_ivl_rep_of_set X;
        RETURN (mk_coll (op_atLeastAtMost_ivl i s:::\<langle>lv_rel\<rangle>ivl_rel))
      })
      (\<lambda>a b. RETURN (a \<union> b))
  }"
sublocale autoref_op_pat_def ivls_of_sets .

definition "ivl_rep_of_set_coll X = do { Xs \<leftarrow> sets_of_coll (X:::clw_rel appr_rel); op_ivl_rep_of_sets Xs}"
sublocale autoref_op_pat_def ivl_rep_of_set_coll .

definition [simp]: "sets_of_ivls X = X"
sublocale autoref_op_pat_def sets_of_ivls .

definition "op_intersects X sctn = (do {
    ii \<leftarrow> Inf_inner X (normal sctn);
    si \<leftarrow> Sup_inner X (normal sctn);
    RETURN (ii \<le> pstn sctn \<and> si \<ge> pstn sctn)
  })"
sublocale autoref_op_pat_def op_intersects .

definition "sbelow_sctns_coll XS sctns = do {
    XS \<leftarrow> (sets_of_coll XS ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True) (\<lambda>X. sbelow_sctns X sctns) (\<lambda>a b. RETURN (a \<and> b))
  }"
sublocale autoref_op_pat_def sbelow_sctns_coll .

definition "below_sctn_coll XS sctn = do {
    XS \<leftarrow> (sets_of_coll XS ::: \<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True) (\<lambda>X. below_sctn X sctn) (\<lambda>a b. RETURN (a \<and> b))
  }"
sublocale autoref_op_pat_def below_sctn_coll .


definition "intersects_clw X sctn = (do {
    XS \<leftarrow> sets_of_coll (X:::clw_rel appr_rel);
    FORWEAK XS (RETURN False) (\<lambda>X. op_intersects X sctn) (\<lambda>a b. RETURN (a \<or> b))
  })"
sublocale autoref_op_pat_def intersects_clw .

definition "op_subset X ivl = do {
    (i', s') \<leftarrow> ((ivl_rep ((ivl))));
    (i, s) \<leftarrow> (op_ivl_rep_of_set ((X::'a::executable_euclidean_space set)));
    RETURN (((i' \<le> i):::bool_rel) \<and> ((s \<le> s'):::bool_rel))
  }"
sublocale autoref_op_pat_def op_subset .

definition [simp]: "subset_spec_coll X ivl = do {
    XS \<leftarrow> (sets_of_coll X:::\<langle>\<langle>appr_rel\<rangle>list_wset_rel\<rangle>nres_rel);
    FORWEAK XS (RETURN True)
      (\<lambda>X. op_subset X ivl)
      (\<lambda>x y. RETURN (x \<and> y))
  }"
sublocale autoref_op_pat_def subset_spec_coll .

definition "op_project_set X b y = inter_sctn_spec X (Sctn b y)"
sublocale autoref_op_pat_def op_project_set .

definition [simp]: "project_set_clw X b y = do {
    XS \<leftarrow> (sets_of_coll (X:::clw_rel appr_rel));
    FORWEAK XS (RETURN op_empty_coll) (\<lambda>X. do {
      P \<leftarrow> op_project_set X b y;
      RETURN (mk_coll P)
    }) (\<lambda>X Y. RETURN (Y \<union> X))
  }"
sublocale autoref_op_pat_def project_set_clw .

definition "subset_spec_ivls X Y = do {
    Ys \<leftarrow> sets_of_coll Y; FORWEAK Ys (RETURN False) (\<lambda>Y. op_subset X Y) (\<lambda>a b. RETURN (a \<or> b))
  }"
sublocale autoref_op_pat_def subset_spec_ivls .

definition "subset_spec_ivls_clw M X Y = do {
    X \<leftarrow> split_along_ivls M X Y;
    X \<leftarrow> sets_of_coll (sets_of_ivls X);
    FORWEAK X (RETURN True) (\<lambda>X. subset_spec_ivls X Y) (\<lambda>a b. RETURN (a \<and> b))
  }"
sublocale autoref_op_pat_def subset_spec_ivls_clw .

definition [simp]: "REMDUPS x = x"
sublocale autoref_op_pat_def REMDUPS .

definition "split_along_ivls2 M X Y = do {
    Xs \<leftarrow> sets_of_coll X;
    Rs \<leftarrow>FORWEAK Xs (RETURN op_empty_coll) (\<lambda>X. do {
      (I, N) \<leftarrow> split_intersecting Y (mk_coll X);
      split_along_ivls M (mk_coll X) I
    }) (\<lambda>x y. RETURN (y \<union> x));
    RETURN (REMDUPS Rs)
  }"
sublocale autoref_op_pat_def split_along_ivls2 .

definition [simp]: "op_list_of_eucl_image X = list_of_eucl ` X"
lemma [autoref_op_pat_def]: "list_of_eucl ` X \<equiv> OP op_list_of_eucl_image $ X" by simp

definition [simp]: "op_eucl_of_list_image X = (eucl_of_list ` X::'a::executable_euclidean_space set)"
lemma [autoref_op_pat_def]: "eucl_of_list ` X \<equiv> OP op_eucl_of_list_image $ X" by simp

definition [simp]: "op_take_image n X = take n ` X"
lemma [autoref_op_pat_def]: "take n ` X \<equiv> OP op_take_image $ n $ X" by simp

definition [simp]: "op_drop_image n X = drop n ` X"
lemma [autoref_op_pat_def]: "drop n ` X \<equiv> OP op_drop_image $ n $ X" by simp

definition "approx_slp_appr fas slp X = do {
    cfp \<leftarrow> approx_slp_spec fas DIM('a::executable_euclidean_space) slp X;
    (case cfp of
      Some cfp \<Rightarrow> do {
        RETURN ((eucl_of_list ` cfp::'a set):::appr_rel)
      }
      | None \<Rightarrow> do {
        SUCCEED
      }
    )
  }"
sublocale autoref_op_pat_def approx_slp_appr .

definition "mig_set D (X::'a::executable_euclidean_space set) = do {
    (i, s) \<leftarrow> op_ivl_rep_of_set (X:::appr_rel);
    let migc = mig_componentwise i s;
    ASSUME (D = DIM('a));
    let norm_fas = ([Norm (map floatarith.Var [0..<D])]:::\<langle>Id\<rangle>list_rel);
    let env = (list_of_eucl ` ({migc .. migc}:::appr_rel):::appr_rell);
    (n::real set) \<leftarrow> approx_slp_appr  norm_fas (slp_of_fas norm_fas) env;
    (ni::real) \<leftarrow> Inf_spec (n:::appr_rel);
    RETURN (rnv_of_lv ni::real)
  }"
sublocale autoref_op_pat_def mig_set .

lemma appr_rel_br: "appr_rel = br (\<lambda>xs. eucl_of_list ` (set_of_appr xs)::'a set) (\<lambda>xs. length xs = DIM('a::executable_euclidean_space))"
  unfolding appr_rel_def lv_rel_def set_rel_br
  unfolding appr_rell_internal br_chain o_def
  using length_set_of_appr
  by (auto dest!: brD intro: brI)

definition print_set::"bool \<Rightarrow> 'a set \<Rightarrow> unit" where "print_set _ _ = ()"

definition trace_set::"string\<Rightarrow>'a set option\<Rightarrow>unit" where "trace_set _ _ = ()"

definition print_msg::"string \<Rightarrow> unit" where "print_msg _ = ()"

abbreviation "CHECKs \<equiv> \<lambda>s. CHECK (\<lambda>_. print_msg s)"

definition "ncc (X::'a::executable_euclidean_space set) \<longleftrightarrow> X \<noteq> {} \<and> compact X \<and> convex X"

definition "ncc_precond TYPE('a::executable_euclidean_space) \<longleftrightarrow> (\<forall>(Xi, X::'a set) \<in> appr_rel. ncc X)"

end

lemma prod_relI': "\<lbrakk>(a,fst ab')\<in>R1; (b,snd ab')\<in>R2\<rbrakk> \<Longrightarrow> ((a,b),ab')\<in>\<langle>R1,R2\<rangle>prod_rel"
  by  (auto simp: prod_rel_def)

lemma lv_relivl_relI:
  "((xs', ys'), {eucl_of_list xs..eucl_of_list ys::'a::executable_euclidean_space}) \<in> \<langle>lv_rel\<rangle>ivl_rel"
  if [simp]: "xs' = xs" "ys' = ys" "DIM('a) = length xs" "length ys = length xs"
  by (force simp: ivl_rel_def set_of_ivl_def
      intro!:  brI lv_relI prod_relI[of _ "eucl_of_list xs" _ _ "eucl_of_list ys"])


end