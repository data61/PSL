section \<open>Relations and Refinement\<close>

theory Refine
imports
  "Automatic_Refinement.Automatic_Refinement"
  (* TODO Peter: list_set_rel is defined in Refine_Monadic.Refine_Foreach,
    but it should probably be somewhere in Automatic_Refinement as it has nothing to do
    with the nondeterminism monad *)
  "Refine_Monadic.Refine_Foreach"
  "Sequence_LTL"
  "Maps"
begin

  (* TODO Peter:
    - there is some infrastructure for converting between predicates and sets using
      the constants rel2p and p2rel
    - however, HOL already has the pred_set_conv attributes
    - with some additional setup connecting the refinement framework relators to their
      lifting/transfer counterparts, the attribute to_set can be used to instantly convert
      lifting/transfer rules to set-based relation format
    - examples can be found throughout this theory (look for the to_set attribute)
  *)
  subsection \<open>Predicate to Set Conversion Setup\<close>

  (* TODO Peter: it would be nice if there were corresponding constants for all the relation predicates
    in Transfer.thy (left_total, left_unique, right_total, right_unique, bi_total, bi_unique *)
  lemma right_unique_pred_set_conv[pred_set_conv]: "right_unique = single_valuedp"
    unfolding right_unique_def single_valuedp_def by auto
  lemma bi_unique_pred_set_conv[pred_set_conv]: "bi_unique (\<lambda> x y. (x, y) \<in> R) \<longleftrightarrow> bijective R"
    unfolding bi_unique_def bijective_def by blast

  text \<open>useful for unfolding equality constants in theorems about predicates\<close>
  lemma pred_Id: "HOL.eq = (\<lambda> x y. (x, y) \<in> Id)" by simp
  lemma pred_bool_Id: "HOL.eq = (\<lambda> x y. (x, y) \<in> (Id :: bool rel))" by simp
  lemma pred_nat_Id: "HOL.eq = (\<lambda> x y. (x, y) \<in> (Id :: nat rel))" by simp
  lemma pred_set_Id: "HOL.eq = (\<lambda> x y. (x, y) \<in> (Id :: 'a set rel))" by simp
  lemma pred_list_Id: "HOL.eq = (\<lambda> x y. (x, y) \<in> (Id :: 'a list rel))" by simp
  lemma pred_stream_Id: "HOL.eq = (\<lambda> x y. (x, y) \<in> (Id :: 'a stream rel))" by simp

  lemma eq_onp_Id_on_eq[pred_set_conv]: "eq_onp (\<lambda> a. a \<in> A) = (\<lambda> x y. (x, y) \<in> Id_on A)"
    unfolding eq_onp_def by auto
  lemma rel_fun_fun_rel_eq[pred_set_conv]:
    "rel_fun (\<lambda> x y. (x, y) \<in> A) (\<lambda> x y. (x, y) \<in> B) = (\<lambda> f g. (f, g) \<in> A \<rightarrow> B)"
    by (force simp: rel_fun_def fun_rel_def)
  lemma rel_prod_prod_rel_eq[pred_set_conv]:
    "rel_prod (\<lambda> x y. (x, y) \<in> A) (\<lambda> x y. (x, y) \<in> B) = (\<lambda> f g. (f, g) \<in> A \<times>\<^sub>r B)"
    by (force simp: prod_rel_def elim: rel_prod.cases)
  lemma rel_sum_sum_rel_eq[pred_set_conv]:
    "rel_sum (\<lambda> x y. (x, y) \<in> A) (\<lambda> x y. (x, y) \<in> B) = (\<lambda> f g. (f, g) \<in> \<langle>A, B\<rangle> sum_rel)"
    by (force simp: sum_rel_def elim: rel_sum.cases)
  lemma rel_set_set_rel_eq[pred_set_conv]:
    "rel_set (\<lambda> x y. (x, y) \<in> A) = (\<lambda> f g. (f, g) \<in> \<langle>A\<rangle> set_rel)"
    unfolding rel_set_def set_rel_def by simp
  lemma rel_option_option_rel_eq[pred_set_conv]:
    "rel_option (\<lambda> x y. (x, y) \<in> A) = (\<lambda> f g. (f, g) \<in> \<langle>A\<rangle> option_rel)"
    by (force simp: option_rel_def elim: option.rel_cases)

  (* TODO Peter: pred_set_conv examples *)
  thm image_transfer image_transfer[to_set]
  thm fun_upd_transfer fun_upd_transfer[to_set]

  subsection \<open>Relation Composition\<close>

  lemma relcomp_trans_1[trans]:
    assumes "(f, g) \<in> A\<^sub>1"
    assumes "(g, h) \<in> A\<^sub>2"
    shows "(f, h) \<in> A\<^sub>1 O A\<^sub>2"
    using relcompI assms by this
  lemma relcomp_trans_2[trans]:
    assumes "(f, g) \<in> A\<^sub>1 \<rightarrow> B\<^sub>1"
    assumes "(g, h) \<in> A\<^sub>2 \<rightarrow> B\<^sub>2"
    shows "(f, h) \<in> A\<^sub>1 O A\<^sub>2 \<rightarrow> B\<^sub>1 O B\<^sub>2"
  proof -
    note assms(1)
    also note assms(2)
    also note
      fun_rel_comp_dist
    finally show ?thesis by this
  qed
  lemma relcomp_trans_3[trans]:
    assumes "(f, g) \<in> A\<^sub>1 \<rightarrow> B\<^sub>1 \<rightarrow> C\<^sub>1"
    assumes "(g, h) \<in> A\<^sub>2 \<rightarrow> B\<^sub>2 \<rightarrow> C\<^sub>2"
    shows "(f, h) \<in> A\<^sub>1 O A\<^sub>2 \<rightarrow> B\<^sub>1 O B\<^sub>2 \<rightarrow> C\<^sub>1 O C\<^sub>2"
  proof -
    note assms(1)
    also note assms(2)
    also note
      fun_rel_mono[OF order_refl
      fun_rel_comp_dist]
    finally show ?thesis by this
  qed
  lemma relcomp_trans_4[trans]:
    assumes "(f, g) \<in> A\<^sub>1 \<rightarrow> B\<^sub>1 \<rightarrow> C\<^sub>1 \<rightarrow> D\<^sub>1"
    assumes "(g, h) \<in> A\<^sub>2 \<rightarrow> B\<^sub>2 \<rightarrow> C\<^sub>2 \<rightarrow> D\<^sub>2"
    shows "(f, h) \<in> A\<^sub>1 O A\<^sub>2 \<rightarrow> B\<^sub>1 O B\<^sub>2 \<rightarrow> C\<^sub>1 O C\<^sub>2 \<rightarrow> D\<^sub>1 O D\<^sub>2"
  proof -
    note assms(1)
    also note assms(2)
    also note
      fun_rel_mono[OF order_refl
      fun_rel_mono[OF order_refl
      fun_rel_comp_dist]]
    finally show ?thesis by this
  qed
  lemma relcomp_trans_5[trans]:
    assumes "(f, g) \<in> A\<^sub>1 \<rightarrow> B\<^sub>1 \<rightarrow> C\<^sub>1 \<rightarrow> D\<^sub>1 \<rightarrow> E\<^sub>1"
    assumes "(g, h) \<in> A\<^sub>2 \<rightarrow> B\<^sub>2 \<rightarrow> C\<^sub>2 \<rightarrow> D\<^sub>2 \<rightarrow> E\<^sub>2"
    shows "(f, h) \<in> A\<^sub>1 O A\<^sub>2 \<rightarrow> B\<^sub>1 O B\<^sub>2 \<rightarrow> C\<^sub>1 O C\<^sub>2 \<rightarrow> D\<^sub>1 O D\<^sub>2 \<rightarrow> E\<^sub>1 O E\<^sub>2"
  proof -
    note assms(1)
    also note assms(2)
    also note
      fun_rel_mono[OF order_refl
      fun_rel_mono[OF order_refl
      fun_rel_mono[OF order_refl
      fun_rel_comp_dist]]]
    finally show ?thesis by this
  qed

  subsection \<open>Relation Basics\<close>

  (* TODO Peter: these were copied from Sepref_HOL_Bindings, they should probably be part of
    $AFP/Automatic_Refinement *)
  lemma inv_fun_rel_eq[simp]: "(A\<rightarrow>B)\<inverse> = A\<inverse>\<rightarrow>B\<inverse>"
    by (auto dest: fun_relD)
  lemma inv_option_rel_eq[simp]: "(\<langle>K\<rangle>option_rel)\<inverse> = \<langle>K\<inverse>\<rangle>option_rel"
    by (auto simp: option_rel_def)
  lemma inv_prod_rel_eq[simp]: "(P \<times>\<^sub>r Q)\<inverse> = P\<inverse> \<times>\<^sub>r Q\<inverse>"
    by (auto)
  lemma inv_sum_rel_eq[simp]: "(\<langle>P,Q\<rangle>sum_rel)\<inverse> = \<langle>P\<inverse>,Q\<inverse>\<rangle>sum_rel"
    by (auto simp: sum_rel_def)
  lemma set_rel_converse[simp]: "(\<langle>A\<rangle> set_rel)\<inverse> = \<langle>A\<inverse>\<rangle> set_rel" unfolding set_rel_def by auto

  lemma build_rel_domain[simp]: "Domain (br \<alpha> I) = Collect I" unfolding build_rel_def by auto
  lemma build_rel_range[simp]: "Range (br \<alpha> I) = \<alpha> ` Collect I" unfolding build_rel_def by auto
  lemma build_rel_image[simp]: "br \<alpha> I `` A = \<alpha> ` (A \<inter> Collect I)" unfolding build_rel_def by auto

  lemma prod_rel_domain[simp]: "Domain (A \<times>\<^sub>r B) = Domain A \<times> Domain B" unfolding prod_rel_def by auto
  lemma prod_rel_range[simp]: "Range (A \<times>\<^sub>r B) = Range A \<times> Range B" unfolding prod_rel_def by auto

  lemma member_Id_on[iff]: "(x, y) \<in> Id_on A \<longleftrightarrow> x = y \<and> y \<in> A" unfolding Id_on_def by auto
  lemma bijective_Id_on[intro!, simp]: "bijective (Id_on A)" unfolding bijective_def by auto
  lemma relcomp_Id_on[simp]: "Id_on A O Id_on B = Id_on (A \<inter> B)" by auto

  lemma prod_rel_Id_on[simp]: "Id_on A \<times>\<^sub>r Id_on B = Id_on (A \<times> B)" by auto
  lemma set_rel_Id_on[simp]: "\<langle>Id_on S\<rangle> set_rel = Id_on (Pow S)" unfolding set_rel_def by auto

  subsection \<open>Parametricity\<close>

  lemmas basic_param[param] =
    option.rel_transfer[unfolded pred_bool_Id, to_set]
    All_transfer[unfolded pred_bool_Id, to_set]
    Ex_transfer[unfolded pred_bool_Id, to_set]
    Union_transfer[to_set]
    image_transfer[to_set]
    Image_parametric[to_set]

  lemma Sigma_param[param]: "(Sigma, Sigma) \<in> \<langle>A\<rangle> set_rel \<rightarrow> (A \<rightarrow> \<langle>B\<rangle> set_rel) \<rightarrow> \<langle>A \<times>\<^sub>r B\<rangle> set_rel"
    unfolding Sigma_def by parametricity
  (* TODO: Lifting_Set.filter_transfer is too weak *)
  lemma set_filter_param[param]:
    "(Set.filter, Set.filter) \<in> (A \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle> set_rel \<rightarrow> \<langle>A\<rangle> set_rel"
    unfolding Set.filter_def fun_rel_def set_rel_def by blast
  lemma is_singleton_param[param]:
    assumes "bijective A"
    shows "(is_singleton, is_singleton) \<in> \<langle>A\<rangle> set_rel \<rightarrow> bool_rel"
    using assms unfolding is_singleton_def set_rel_def bijective_def by auto blast+
  lemma the_elem_param[param]:
    assumes "is_singleton S" "is_singleton T"
    assumes "(S, T) \<in> \<langle>A\<rangle> set_rel"
    shows "(the_elem S, the_elem T) \<in> A"
    using assms unfolding set_rel_def is_singleton_def by auto

  subsection \<open>Lists\<close>

  lemma list_all2_list_rel_conv[pred_set_conv]:
    "list_all2 (\<lambda> x y. (x, y) \<in> R) = (\<lambda> x y. (x, y) \<in> \<langle>R\<rangle> list_rel)"
    unfolding list_rel_def by simp

  lemmas list_rel_single_valued[iff] = list_rel_sv_iff

  lemmas list_rel_simps[simp] =
    list.rel_eq_onp[to_set]
    list.rel_conversep[to_set, symmetric]
    list.rel_compp[to_set]

  lemmas list_rel_param[param] =
    list.set_transfer[to_set]
    list.pred_transfer[unfolded pred_bool_Id, to_set, folded pred_list_listsp]
    list.rel_transfer[unfolded pred_bool_Id, to_set]

  (* TODO Peter: param_set is too restrictive *)
  thm param_set list.set_transfer[to_set]

  lemmas scan_param[param] = scan.transfer[to_set]
  lemma bind_param[param]: "(List.bind, List.bind) \<in> \<langle>A\<rangle> list_rel \<rightarrow> (A \<rightarrow> \<langle>B\<rangle> list_rel) \<rightarrow> \<langle>B\<rangle> list_rel"
    unfolding List.bind_def by parametricity

  lemma set_id_param[param]: "(set, id) \<in> \<langle>A\<rangle> list_set_rel \<rightarrow> \<langle>A\<rangle> set_rel"
    unfolding list_set_rel_def relcomp_unfold in_br_conv by auto parametricity

  subsection \<open>Streams\<close>

  definition stream_rel :: "('a \<times> 'b) set \<Rightarrow> ('a stream \<times> 'b stream) set" where
    [to_relAPP]: "stream_rel R \<equiv> {(x, y). stream_all2 (\<lambda> x y. (x, y) \<in> R) x y}"

  lemma stream_all2_stream_rel_conv[pred_set_conv]:
    "stream_all2 (\<lambda> x y. (x, y) \<in> R) = (\<lambda> x y. (x, y) \<in> \<langle>R\<rangle> stream_rel)"
    unfolding stream_rel_def by simp

  lemmas stream_rel_coinduct'[case_names stream_rel, coinduct set: stream_rel] =
    stream_rel_coinduct[to_set]

  lemmas stream_rel_intros = stream.rel_intros[to_set]
  lemmas stream_rel_cases = stream.rel_cases[to_set]
  lemmas stream_rel_inject[iff] = stream.rel_inject[to_set]

  (* TODO: why is stream.right_unique_rel not generated as an iff rule? *)
  lemma stream_rel_single_valued[iff]: "single_valued (\<langle>A\<rangle> stream_rel) \<longleftrightarrow> single_valued A"
  proof
    show "single_valued A" if "single_valued (\<langle>A\<rangle> stream_rel)"
    proof (intro single_valuedI)
      fix x y z
      assume "(x, y) \<in> A" "(x, z) \<in> A"
      then have "(sconst x, sconst y) \<in> \<langle>A\<rangle> stream_rel" "(sconst x, sconst z) \<in> \<langle>A\<rangle> stream_rel"
        unfolding stream_rel_sconst[to_set] by this
      then have "sconst y = sconst z" using single_valuedD that by metis
      then show "y = z" by simp
    qed
    show "single_valued A \<Longrightarrow> single_valued (\<langle>A\<rangle> stream_rel)"
      using stream.right_unique_rel[to_set, to_set] by this
  qed

  lemmas stream_rel_simps[simp] =
    stream.rel_eq[unfolded pred_Id, THEN IdD, to_set]
    stream.rel_eq_onp[to_set]
    stream.rel_conversep[to_set]
    stream.rel_compp[to_set]

  lemmas stream_rel_param[param] =
    stream.ctr_transfer[to_set]
    stream.sel_transfer[to_set]
    stream.pred_transfer[unfolded pred_bool_Id, to_set, folded pred_stream_streamsp]
    stream.rel_transfer[unfolded pred_bool_Id, to_set]
    stream.map_transfer[to_set]
    stream.set_transfer[to_set]
    stream.case_transfer[to_set]
    stream.corec_transfer[unfolded pred_bool_Id, to_set]

  (* TODO: why is this not generated by the datatype package when stream.Domainp_rel is? *)
  lemma stream_Rangep_rel: "Rangep (stream_all2 R) = pred_stream (Rangep R)"
  proof -
    have 1: "pred_stream (Rangep R) v" if "stream_all2 R u v" for u v
      using that by (coinduction arbitrary: u v) (auto elim: stream.rel_cases)
    have 2: "stream_all2 R (smap (\<lambda> y. SOME x. R x y) v) v" if "pred_stream (Rangep R) v" for v
      using that by (coinduction arbitrary: v) (auto intro: someI)
    show ?thesis using 1 2 by blast
  qed

  lemmas stream_rel_domain[simp] = stream.Domainp_rel[to_set]
  lemmas stream_rel_range[simp] = stream_Rangep_rel[to_set]

  lemma stream_param[param]:
    assumes"(HOL.eq, HOL.eq) \<in> R \<rightarrow> R \<rightarrow> bool_rel"
    shows "(HOL.eq, HOL.eq) \<in> \<langle>R\<rangle> stream_rel \<rightarrow> \<langle>R\<rangle> stream_rel \<rightarrow> bool_rel"
  proof -
    have "(stream_all2 HOL.eq, stream_all2 HOL.eq) \<in> \<langle>R\<rangle> stream_rel \<rightarrow> \<langle>R\<rangle> stream_rel \<rightarrow> bool_rel"
      using assms by parametricity
    then show ?thesis unfolding stream.rel_eq by this
  qed

  lemmas szip_param[param] = szip_transfer[to_set]
  lemmas siterate_param[param] = siterate_transfer[to_set]
  lemmas sscan_param[param] = sscan.transfer[to_set]

  lemma streams_param[param]: "(streams, streams) \<in> \<langle>A\<rangle> set_rel \<rightarrow> \<langle>\<langle>A\<rangle> stream_rel\<rangle> set_rel"
  proof (intro fun_relI set_relI)
    fix S T
    assume 1: "(S, T) \<in> \<langle>A\<rangle> set_rel"
    obtain f where 2: "\<And> x. x \<in> S \<Longrightarrow> f x \<in> T \<and> (x, f x) \<in> A"
      using 1 unfolding set_rel_def by auto metis
    have 3: "f ` S \<subseteq> T" "(id, f) \<in> Id_on S \<rightarrow> A" using 2 by auto
    obtain g where 4: "\<And> y. y \<in> T \<Longrightarrow> g y \<in> S \<and> (g y, y) \<in> A"
      using 1 unfolding set_rel_def by auto metis
    have 5: "g ` T \<subseteq> S" "(g, id) \<in> Id_on T \<rightarrow> A" using 4 by auto
    show "\<exists> v \<in> streams T. (u, v) \<in> \<langle>A\<rangle> stream_rel" if "u \<in> streams S" for u
    proof
      show "smap f u \<in> streams T" using smap_streams 3 that by blast
      have "(smap id u, smap f u) \<in> \<langle>A\<rangle> stream_rel" using 3 that by parametricity auto
      then show "(u, smap f u) \<in> \<langle>A\<rangle> stream_rel" by simp
    qed
    show "\<exists> u \<in> streams S. (u, v) \<in> \<langle>A\<rangle> stream_rel" if "v \<in> streams T" for v
    proof
      show "smap g v \<in> streams S" using smap_streams 5 that by blast
      have "(smap g v, smap id v) \<in> \<langle>A\<rangle> stream_rel" using 5 that by parametricity auto
      then show "(smap g v, v) \<in> \<langle>A\<rangle> stream_rel" by simp
    qed
  qed

  lemma holds_param[param]: "(holds, holds) \<in> (A \<rightarrow> bool_rel) \<rightarrow> (\<langle>A\<rangle> stream_rel \<rightarrow> bool_rel)"
    unfolding holds.simps by parametricity
  lemma HLD_param[param]:
    assumes "single_valued A" "single_valued (A\<inverse>)"
    shows "(HLD, HLD) \<in> \<langle>A\<rangle> set_rel \<rightarrow> \<langle>A\<rangle> stream_rel \<rightarrow> bool_rel"
    using assms unfolding HLD_def by parametricity
  lemma ev_param[param]: "(ev, ev) \<in> (\<langle>A\<rangle> stream_rel \<rightarrow> bool_rel) \<rightarrow> (\<langle>A\<rangle> stream_rel \<rightarrow> bool_rel)"
  proof safe
    fix P Q u v
    assume 1: "(P, Q) \<in> \<langle>A\<rangle> stream_rel \<rightarrow> bool_rel" "(u, v) \<in> \<langle>A\<rangle> stream_rel"
    note 2 = 1[param_fo] stream_rel_param(3)[param_fo]
    show "ev Q v" if "ev P u" using that 2 by (induct arbitrary: v) (blast+)
    show "ev P u" if "ev Q v" using that 2 by (induct arbitrary: u) (blast+)
  qed
  lemma alw_param[param]: "(alw, alw) \<in> (\<langle>A\<rangle> stream_rel \<rightarrow> bool_rel) \<rightarrow> (\<langle>A\<rangle> stream_rel \<rightarrow> bool_rel)"
  proof safe
    fix P Q u v
    assume 1: "(P, Q) \<in> \<langle>A\<rangle> stream_rel \<rightarrow> bool_rel" "(u, v) \<in> \<langle>A\<rangle> stream_rel"
    note 2 = 1[param_fo] stream_rel_param(3)[param_fo]
    show "alw Q v" if "alw P u" using that 2 by (coinduction arbitrary: u v) (auto, blast)
    show "alw P u" if "alw Q v" using that 2 by (coinduction arbitrary: u v) (auto, blast)
  qed

  subsection \<open>Functional Relations\<close>

  lemma br_set_rel: "\<langle>br f P\<rangle> set_rel = br (image f) (\<lambda> A. Ball A P)"
    using br_set_rel_alt by (auto simp: build_rel_def)

  lemma br_list_rel: "\<langle>br f P\<rangle> list_rel = br (map f) (list_all P)"
  proof safe
    fix u v
    show "(u, v) \<in> br (map f) (list_all P)" if "(u, v) \<in> \<langle>br f P\<rangle> list_rel"
      using that unfolding build_rel_def by induct auto
    show "(u, v) \<in> \<langle>br f P\<rangle> list_rel" if "(u, v) \<in> br (map f) (list_all P)"
      using that unfolding build_rel_def by (induct u arbitrary: v) (auto)
  qed

  lemma br_list_set_rel: "\<langle>br f P\<rangle> list_set_rel = br (set \<circ> map f) (\<lambda> s. list_all P s \<and> distinct (map f s))"
    unfolding list_set_rel_def br_list_rel
    unfolding br_chain
    by rule

  lemma br_fun_rel1: "Id \<rightarrow> br f P = br (comp f) (All \<circ> comp P)"
    unfolding fun_rel_def Ball_def by (auto simp: build_rel_def)

  (* notes *)

  (* TODO Peter: the way \<circ>\<circ> and \<circ>\<circ>\<circ> are declared, a lot of unexpected abbreviation folding takes place *)
  term "set \<circ> map f \<circ> map g \<circ> map h"
  (* in large expressions, this can introduce unneccessary paretheses and in general, makes
    things very hard to read *)
  (* it is even possible for other abbreviations to be torn apart by this *)
  term "set \<circ> sort"
  (* I think that there were even cases where eta-expanded terms were torn apart, but I
    do not have an example at the moment *)

  (* the following abbreviations work better, a term can only be abbreviated by comp_n if
    it contains the constant comp at least n times, thus they should only be folded back if
    the original term really had the right degree of "point-free-ness" *)
  (*
  abbreviation comp_2 (infixl "\<circ>\<circ>" 55) where "f \<circ>\<circ> g \<equiv> comp (comp f) g"
  abbreviation comp_3 (infixl "\<circ>\<circ>\<circ>" 55) where "f \<circ>\<circ>\<circ> g \<equiv> comp (comp (comp f)) g"
  abbreviation comp_4 (infixl "\<circ>\<circ>\<circ>\<circ>" 55) where "f \<circ>\<circ>\<circ>\<circ> g \<equiv> comp (comp (comp (comp f))) g"
  abbreviation comp_5 (infixl "\<circ>\<circ>\<circ>\<circ>\<circ>" 55) where "f \<circ>\<circ>\<circ>\<circ>\<circ> g \<equiv> comp (comp (comp (comp (comp f)))) g"
  *)
  (* since the root of the right hand side term is not a lambda abstraction, this
    abbreviation should also not be able to introduce any parentheses *)

end
