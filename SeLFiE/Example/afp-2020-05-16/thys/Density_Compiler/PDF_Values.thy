(*
  Theory: PDF_Values.thy
  Author: Manuel Eberl

  Defines the values and types in the PDF language and the corresponding stock measure spaces.
  Additionally, some functions and lemmas for lifting functions on the HOL types (int, real, \<dots>)
  to PDF values are provided.
*)

section \<open>Source Language Values\<close>

theory PDF_Values
imports Density_Predicates
begin

subsection \<open>Values and stock measures\<close>

datatype pdf_type =  UNIT | BOOL | INTEG | REAL | PRODUCT pdf_type pdf_type

datatype val = UnitVal
  | BoolVal (extract_bool: bool)
  | IntVal (extract_int: int)
  | RealVal (extract_real: real)
  | PairVal (extract_fst: val) (extract_snd: val)  ("<|_, _|>"  [0, 61] 1000)
where
  "extract_bool UnitVal = False"
| "extract_bool (IntVal i) = False"
| "extract_bool (RealVal r) = False"
| "extract_bool (PairVal x y) = False"
| "extract_int UnitVal = 0"
| "extract_int (BoolVal b) = 0"
| "extract_int (RealVal r) = 0"
| "extract_int (PairVal x y) = 0"
| "extract_real UnitVal = 0"
| "extract_real (BoolVal b) = 0"
| "extract_real (IntVal i) = 0"
| "extract_real (PairVal x y) = 0"

primrec extract_pair' where
  "extract_pair' f s <| x, y |> = (f x, s y)"

definition map_int_pair where
  "map_int_pair f g x = (case x of <| IntVal a, IntVal b |> \<Rightarrow> f a b | _ \<Rightarrow> g x)"

definition map_real_pair where
  "map_real_pair f g x = (case x of <| RealVal a, RealVal b |> \<Rightarrow> f a b | _ \<Rightarrow> g x)"

abbreviation "TRUE \<equiv> BoolVal True"
abbreviation "FALSE \<equiv> BoolVal False"

type_synonym vname = "nat"
type_synonym state = "vname \<Rightarrow> val"

lemma map_int_pair[simp]: "map_int_pair f g <| IntVal i, IntVal j |> = f i j"
  by (simp add: map_int_pair_def)

lemma map_int_pair_REAL[simp]: "map_int_pair f g <| RealVal i, RealVal j |> = g <| RealVal i, RealVal j |>"
  by (simp add: map_int_pair_def)

lemma map_real_pair[simp]: "map_real_pair f g <| RealVal i, RealVal j |> = f i j"
  by (simp add: map_real_pair_def)

abbreviation "extract_pair \<equiv> extract_pair' id id"
abbreviation "extract_real_pair \<equiv> extract_pair' extract_real extract_real"
abbreviation "extract_int_pair \<equiv> extract_pair' extract_int extract_int"

definition "RealPairVal \<equiv> \<lambda>(x,y). <|RealVal x, RealVal y|>"

definition "IntPairVal \<equiv> \<lambda>(x,y). <|IntVal x, IntVal y|>"

lemma inj_RealPairVal: "inj RealPairVal" by (auto simp: RealPairVal_def intro!: injI)
lemma inj_IntPairVal: "inj IntPairVal" by (auto simp: IntPairVal_def intro!: injI)

fun val_type :: "val \<Rightarrow> pdf_type" where
  "val_type (BoolVal b) = BOOL"
| "val_type (IntVal i) = INTEG"
| "val_type UnitVal = UNIT"
| "val_type (RealVal r) = REAL"
| "val_type (<|v1 , v2|>) = (PRODUCT (val_type v1) (val_type v2))"

lemma val_type_eq_REAL: "val_type x = REAL \<longleftrightarrow> x \<in> RealVal`UNIV"
  by (cases x) auto

lemma val_type_eq_INTEG: "val_type x = INTEG \<longleftrightarrow> x \<in> IntVal`UNIV"
  by (cases x) auto

definition "type_universe t = {v. val_type v = t}"

lemma type_universe_nonempty[simp]: "type_universe t \<noteq> {}"
  by (induction t) (auto intro: val_type.simps simp: type_universe_def)

lemma val_in_type_universe[simp]:
    "v \<in> type_universe (val_type v)"
  by (simp add: type_universe_def)

lemma BoolVal_in_type_universe[simp]: "BoolVal v \<in> type_universe BOOL"
  by (simp add: type_universe_def)

lemma IntVal_in_type_universe[simp]: "IntVal v \<in> type_universe INTEG"
  by (simp add: type_universe_def)

lemma type_universe_type[simp]:
    "w \<in> type_universe t \<longleftrightarrow> val_type w = t"
  by (simp add: type_universe_def)

lemma type_universe_REAL: "type_universe REAL = RealVal ` UNIV"
  apply (auto simp add: set_eq_iff image_iff)
  apply (case_tac x)
  apply auto
  done

lemma type_universe_eq_imp_type_eq:
  assumes "type_universe t1 = type_universe t2"
  shows "t1 = t2"
proof-
  from type_universe_nonempty obtain v where A: "v \<in> type_universe t1" by blast
  hence "t1 = val_type v" by simp
  also from A and assms have "v \<in> type_universe t2" by simp
  hence "val_type v = t2" by simp
  finally show ?thesis .
qed

lemma type_universe_eq_iff[simp]: "type_universe t1 = type_universe t2 \<longleftrightarrow> t1 = t2"
  by (blast intro: type_universe_eq_imp_type_eq)

primrec stock_measure :: "pdf_type \<Rightarrow> val measure" where
  "stock_measure UNIT = count_space {UnitVal}"
| "stock_measure INTEG = count_space (range IntVal)"
| "stock_measure BOOL = count_space (range BoolVal)"
| "stock_measure REAL = embed_measure lborel RealVal"
| "stock_measure (PRODUCT t1 t2) =
       embed_measure (stock_measure t1 \<Otimes>\<^sub>M stock_measure t2) (\<lambda>(a, b). <|a, b|>)"

declare [[coercion stock_measure]]

lemma sigma_finite_stock_measure[simp]: "sigma_finite_measure (stock_measure t)"
  by (induction t)
     (auto intro!: sigma_finite_measure_count_space_countable sigma_finite_pair_measure
                   sigma_finite_embed_measure injI sigma_finite_lborel)

lemma val_case_stock_measurable:
  assumes "t = UNIT \<Longrightarrow> c \<in> space M"
  assumes "\<And>b. t = BOOL \<Longrightarrow> g b \<in> space M"
  assumes "\<And>i. t = INTEG \<Longrightarrow> h i \<in> space M"
  assumes "t = REAL \<Longrightarrow> j \<in> measurable borel M"
  assumes *: "\<And>t1 t2. t = PRODUCT t1 t2 \<Longrightarrow> case_prod k \<in> measurable (stock_measure t1 \<Otimes>\<^sub>M stock_measure t2) M"
  shows "(\<lambda>x. case x of UnitVal \<Rightarrow> c | BoolVal b \<Rightarrow> g b | IntVal i \<Rightarrow> h i | RealVal r \<Rightarrow> j r
                | PairVal y z \<Rightarrow> k y z) \<in> measurable t M"
proof (cases t)
  case (PRODUCT t1 t2) with *[of t1 t2] show ?thesis
    by (auto intro!: measurable_embed_measure1 simp: split_beta')
qed (auto intro!: measurable_embed_measure1 assms)

lemma space_stock_measure[simp]: "space (stock_measure t) = type_universe t"
  by (induction t)
     (auto simp add: type_universe_def space_pair_measure space_embed_measure
           simp del: type_universe_type elim: val_type.elims)

lemma type_universe_stock_measure[measurable]: "type_universe t \<in> sets (stock_measure t)"
  using sets.top[of "stock_measure t"] by simp

lemma inj_RealVal[simp]: "inj RealVal" by (auto intro!: inj_onI)
lemma inj_IntVal[simp]: "inj IntVal" by (auto intro!: inj_onI)
lemma inj_BoolVal[simp]: "inj BoolVal" by (auto intro!: inj_onI)
lemma inj_PairVal[simp]: "inj (\<lambda>(x, y). <| x ,  y |>)" by (auto intro: injI)

lemma measurable_PairVal[measurable]:
  fixes t1 t2 :: pdf_type
  shows "case_prod PairVal \<in> measurable (t1 \<Otimes>\<^sub>M t2) (PRODUCT t1 t2)"
  using measurable_embed_measure2[measurable] by simp

lemma measurable_RealVal[measurable]: "RealVal \<in> measurable borel REAL"
  using measurable_embed_measure2[measurable] by simp

lemma nn_integral_BoolVal:
  assumes "\<And>x. f (BoolVal x) \<ge> 0"
  shows "(\<integral>\<^sup>+x. f x \<partial>BOOL) = f (BoolVal True) + f (BoolVal False)"
proof-
  have A: "range BoolVal = {BoolVal True, BoolVal False}" by auto
  from assms show ?thesis
    by (subst stock_measure.simps, subst A, subst nn_integral_count_space_finite)
       (simp_all add: max_def A)
qed

lemma nn_integral_RealVal:
  "f \<in> borel_measurable REAL \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>REAL) = (\<integral>\<^sup>+x. f (RealVal x) \<partial>lborel)"
  unfolding stock_measure.simps using measurable_embed_measure2[measurable]
  by (subst embed_measure_eq_distr, simp_all add: nn_integral_distr)

lemma nn_integral_IntVal: "(\<integral>\<^sup>+x. f x \<partial>INTEG) = (\<integral>\<^sup>+x. f (IntVal x) \<partial>count_space UNIV)"
  using measurable_embed_measure1[measurable (raw)]
  unfolding stock_measure.simps embed_measure_count_space[OF inj_IntVal, symmetric]
  by (subst embed_measure_eq_distr[OF inj_IntVal], simp add: nn_integral_distr space_embed_measure)

lemma nn_integral_PairVal:
  "f \<in> borel_measurable (PRODUCT t1 t2) \<Longrightarrow>
    (\<integral>\<^sup>+x. f x \<partial>PRODUCT t1 t2) = (\<integral>\<^sup>+x. f (PairVal (fst x) (snd x)) \<partial>(t1 \<Otimes>\<^sub>M t2))"
  unfolding stock_measure.simps
  by (subst nn_integral_embed_measure) (simp_all add: split_beta' inj_on_def)

lemma BOOL_E: "\<lbrakk>val_type v = BOOL; \<And>b. v = BoolVal b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases v) auto

lemma PROD_E: "\<lbrakk>val_type v = PRODUCT t1 t2 ;
     \<And>a b. val_type a = t1 \<Longrightarrow> val_type b = t2 \<Longrightarrow> v = <| a, b |> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases v) auto

lemma REAL_E: "\<lbrakk>val_type v = REAL; \<And>b. v = RealVal b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases v) auto

lemma INTEG_E: "\<lbrakk>val_type v = INTEG; \<And>i. v = IntVal i \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases v) auto

lemma measurable_extract_pair'[measurable (raw)]:
  fixes t1 t2 :: pdf_type
  assumes [measurable]: "f \<in> measurable t1 M"
  assumes [measurable]: "g \<in> measurable t2 N"
  assumes h: "h \<in> measurable K (PRODUCT t1 t2)"
  shows "(\<lambda>x. extract_pair' f g (h x)) \<in> measurable K (M \<Otimes>\<^sub>M N)"
  by (rule measurable_compose[OF h[unfolded stock_measure.simps] measurable_embed_measure1])
     (simp add: split_beta')

lemma measurable_extract_pair[measurable]: "extract_pair \<in> measurable (PRODUCT t1 t2) (t1 \<Otimes>\<^sub>M t2)"
  by measurable

lemma measurable_extract_real[measurable]: "extract_real \<in> measurable REAL borel"
  apply simp
  apply measurable
  apply (rule measurable_embed_measure1)
  apply simp
  done

lemma measurable_extract_int[measurable]: "extract_int \<in> measurable INTEG (count_space UNIV)"
  by simp measurable

lemma measurable_extract_int_pair[measurable]:
  "extract_int_pair \<in> measurable (PRODUCT INTEG INTEG) (count_space UNIV \<Otimes>\<^sub>M count_space UNIV)"
  by measurable

lemma measurable_extract_real_pair[measurable]:
  "extract_real_pair \<in> measurable (PRODUCT REAL REAL) (borel \<Otimes>\<^sub>M borel)"
  by measurable

lemma measurable_extract_real_pair'[measurable]:
  "extract_real_pair \<in> measurable (PRODUCT REAL REAL) borel"
  by (subst borel_prod[symmetric]) measurable

lemma measurable_extract_bool[measurable]: "extract_bool \<in> measurable BOOL (count_space UNIV)"
  by simp

lemma map_int_pair_measurable[measurable]:
  assumes f: "case_prod f \<in> measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV) M"
  shows "map_int_pair f g \<in> measurable (PRODUCT INTEG INTEG) M"
proof (subst measurable_cong)
  fix w assume "w \<in> space (PRODUCT INTEG INTEG)"
  then show "map_int_pair f g w = (case_prod f o extract_int_pair) w"
    by (auto simp: space_embed_measure space_pair_measure)
next
  show "(\<lambda>(x, y). f x y) \<circ> extract_int_pair \<in> measurable (stock_measure (PRODUCT INTEG INTEG)) M"
    using measurable_extract_int_pair f by (rule measurable)
qed

lemma map_int_pair_measurable_REAL[measurable]:
  assumes "g \<in> measurable (PRODUCT REAL REAL) M"
  shows "map_int_pair f g \<in> measurable (PRODUCT REAL REAL) M"
proof (subst measurable_cong)
  fix w assume "w \<in> space (PRODUCT REAL REAL)"
  then show "map_int_pair f g w = g w"
    by (auto simp: space_embed_measure space_pair_measure map_int_pair_def)
qed fact

lemma map_real_pair_measurable[measurable]:
  assumes f: "case_prod f \<in> measurable (borel \<Otimes>\<^sub>M borel) M"
  shows "map_real_pair f g \<in> measurable (PRODUCT REAL REAL) M"
proof (subst measurable_cong)
  fix w assume "w \<in> space (PRODUCT REAL REAL)"
  then show "map_real_pair f g w = (case_prod f o extract_real_pair) w"
    by (auto simp: space_embed_measure space_pair_measure)
next
  show "(\<lambda>(x, y). f x y) \<circ> extract_real_pair \<in> measurable (stock_measure (PRODUCT REAL REAL)) M"
    using measurable_extract_real_pair f by (rule measurable)
qed

lemma count_space_IntVal_prod[simp]: "INTEG \<Otimes>\<^sub>M INTEG = count_space (range IntVal \<times> range IntVal)"
  by (auto intro!: pair_measure_countable)

lemma count_space_BoolVal_prod[simp]: "BOOL \<Otimes>\<^sub>M BOOL = count_space (range BoolVal \<times> range BoolVal)"
  by (auto intro!: pair_measure_countable)

lemma measurable_stock_measure_val_type:
  assumes "f \<in> measurable M (stock_measure t)" "x \<in> space M"
  shows "val_type (f x) = t"
  using assms by (auto dest!: measurable_space)

lemma singleton_in_stock_measure[simp]: "val_type v = t \<Longrightarrow> {v} \<in> sets t"
proof (induction v arbitrary: t)
  case (PairVal v1 v2)
  have A: "{<|v1, v2|>} = (\<lambda>(v1,v2). <|v1,v2|>) ` ({v1}\<times>{v2})" by simp
  from pair_measureI[OF PairVal.IH, OF refl refl] PairVal.prems[symmetric] show ?case
    by (simp only: val_type.simps stock_measure.simps A in_sets_embed_measure)
qed (auto simp: sets_embed_measure)

lemma emeasure_stock_measure_singleton_finite[simp]:
    "emeasure (stock_measure (val_type v)) {v} \<noteq> \<infinity>"
proof (induction v)
  case (RealVal r)
  have A: "{RealVal r} = RealVal ` {r}" by simp
  have "RealVal ` {r} \<in> sets (embed_measure lborel RealVal)"
      by (rule in_sets_embed_measure) simp
  thus ?case by (simp only: A val_type.simps stock_measure.simps emeasure_embed_measure
                            inj_RealVal inj_vimage_image_eq) simp
next
  case (PairVal v1 v2)
    let ?M = "\<lambda>x. stock_measure (val_type x)"
    interpret sigma_finite_measure "stock_measure (val_type v2)"
      by (rule sigma_finite_stock_measure)
    have A: "{<|v1, v2|>} = (\<lambda>(v1,v2). <|v1,v2|>) ` ({v1}\<times>{v2})" by simp
    have B: "{v1}\<times>{v2} \<in> ?M v1 \<Otimes>\<^sub>M ?M v2"
      by (intro pair_measureI singleton_in_stock_measure) simp_all
    hence "emeasure (?M (<|v1,v2|>)) {<|v1,v2|>} = emeasure (?M v1) {v1} * emeasure (?M v2) {v2}"
      by (simp only: stock_measure.simps val_type.simps A emeasure_embed_measure_image inj_PairVal
                     inj_vimage_image_eq emeasure_pair_measure_Times singleton_in_stock_measure B)
    with PairVal.IH show ?case by (simp add: ennreal_mult_eq_top_iff)
qed simp_all


subsection \<open>Measures on states\<close>

definition state_measure :: "vname set \<Rightarrow> (vname \<Rightarrow> pdf_type) \<Rightarrow> state measure" where
  "state_measure V \<Gamma> \<equiv> \<Pi>\<^sub>M y\<in>V. \<Gamma> y"

lemma state_measure_nonempty[simp]: "space (state_measure V \<Gamma>) \<noteq> {}"
  by (simp add: state_measure_def space_PiM PiE_eq_empty_iff)

lemma space_state_measure: "space (state_measure V \<Gamma>) = (\<Pi>\<^sub>E y\<in>V. type_universe (\<Gamma> y))"
  by (simp add: state_measure_def space_PiM PiE_eq_empty_iff)

lemma state_measure_var_type:
    "\<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow> x \<in> V \<Longrightarrow> val_type (\<sigma> x) = \<Gamma> x"
  by (auto simp: state_measure_def space_PiM dest!: PiE_mem)

lemma merge_in_state_measure:
  "x \<in> space (state_measure A \<Gamma>) \<Longrightarrow> y \<in> space (state_measure B \<Gamma>) \<Longrightarrow>
      merge A B (x, y) \<in> space (state_measure (A\<union>B) \<Gamma>)" unfolding state_measure_def
  by (rule measurable_space, rule measurable_merge) (simp add: space_pair_measure)

lemma measurable_merge_stock[measurable (raw)]:
  "f \<in> N \<rightarrow>\<^sub>M state_measure V \<Gamma> \<Longrightarrow> g \<in> N \<rightarrow>\<^sub>M state_measure V' \<Gamma> \<Longrightarrow>
    (\<lambda>x. merge V V' (f x, g x)) \<in> N \<rightarrow>\<^sub>M state_measure (V \<union> V') \<Gamma>"
  by (auto simp: state_measure_def)

lemma comp_in_state_measure:
    assumes "\<sigma> \<in> space (state_measure V \<Gamma>)"
    shows "\<sigma> \<circ> f \<in> space (state_measure (f -` V) (\<Gamma> \<circ> f))"
  using assms by (auto simp: state_measure_def space_PiM)

lemma sigma_finite_state_measure[intro]:
    "finite V \<Longrightarrow> sigma_finite_measure (state_measure V \<Gamma>)" unfolding state_measure_def
  by (auto intro!: product_sigma_finite.sigma_finite simp: product_sigma_finite_def)


subsection \<open>Equalities of measure embeddings\<close>

lemma embed_measure_RealPairVal:
   "stock_measure (PRODUCT REAL REAL) = embed_measure lborel RealPairVal"
proof-
  have [simp]: "(\<lambda>(x, y). <| x ,  y |>) \<circ> (\<lambda>(x, y). (RealVal x, RealVal y)) = RealPairVal"
    unfolding RealPairVal_def by auto
  have "stock_measure (PRODUCT REAL REAL) =
            embed_measure (embed_measure lborel (\<lambda>(x, y). (RealVal x, RealVal y))) (case_prod PairVal)"
    by (auto simp: embed_measure_prod sigma_finite_lborel lborel_prod)
  also have "... = embed_measure lborel RealPairVal"
    by (subst embed_measure_comp) (auto intro!: injI)
  finally show ?thesis .
qed

lemma embed_measure_IntPairVal:
  "stock_measure (PRODUCT INTEG INTEG) = count_space (range IntPairVal)"
proof-
  have [simp]: "(\<lambda>(x, y). <| x ,  y |>) ` (range IntVal \<times> range IntVal) = range IntPairVal"
    by (auto simp: IntPairVal_def)
  show ?thesis
    using count_space_IntVal_prod by (auto simp: embed_measure_prod embed_measure_count_space)
qed

subsection \<open>Monadic operations on values\<close>

definition "return_val x = return (stock_measure (val_type x)) x"

lemma sets_return_val[measurable_cong]: "sets (return_val x) = sets (stock_measure (val_type x))"
    by (simp add: return_val_def)

lemma measurable_return_val[simp]:
    "return_val \<in> measurable (stock_measure t) (subprob_algebra (stock_measure t))"
  unfolding return_val_def[abs_def]
  apply (subst measurable_cong)
  apply (subst type_universe_type[THEN iffD1])
  apply simp
  apply (rule refl)
  apply (rule return_measurable)
  done

lemma bind_return_val:
  assumes "space M \<noteq> {}" "f \<in> measurable M (stock_measure t')"
  shows "M \<bind> (\<lambda>x. return_val (f x)) = distr M (stock_measure t') f"
  using assms
  by (subst bind_return_distr[symmetric])
     (auto simp: return_val_def intro!: bind_cong dest: measurable_stock_measure_val_type)

lemma bind_return_val':
  assumes "val_type x = t" "f \<in> measurable (stock_measure t) (stock_measure t')"
  shows "return_val x \<bind> (\<lambda>x. return_val (f x)) = return_val (f x)"
proof-
  have "return_val x \<bind> (\<lambda>x. return_val (f x)) = return (stock_measure t') (f x)"
    apply (subst bind_return_val, unfold return_val_def, simp)
    apply (insert assms, simp cong: measurable_cong_sets) []
    apply (subst distr_return, simp_all add: assms type_universe_def
                                        del: type_universe_type)
    done
  also from assms(2) have "f x \<in> space (stock_measure t')"
    by (rule measurable_space)
       (simp add: assms(1) type_universe_def del: type_universe_type)
  hence "return (stock_measure t') (f x) = return_val (f x)"
    by (simp add: return_val_def)
  finally show ?thesis .
qed

lemma bind_return_val'':
  assumes "f \<in> measurable (stock_measure (val_type x)) (subprob_algebra M)"
  shows "return_val x \<bind> f = f x"
unfolding return_val_def by (subst bind_return[OF assms]) simp_all

lemma bind_assoc_return_val:
  assumes sets_M: "sets M = sets (stock_measure t)"
  assumes Mf: "f \<in> measurable (stock_measure t) (stock_measure t')"
  assumes Mg: "g \<in> measurable (stock_measure t') (stock_measure t'')"
  shows "(M \<bind> (\<lambda>x. return_val (f x))) \<bind> (\<lambda>x. return_val (g x)) =
             M \<bind> (\<lambda>x. return_val (g (f x)))"
proof-
  have "(M \<bind> (\<lambda>x. return_val (f x))) \<bind> (\<lambda>x. return_val (g x)) =
           M \<bind> (\<lambda>x. return_val (f x) \<bind> (\<lambda>x. return_val (g x)))"
    apply (subst bind_assoc)
    apply (rule measurable_compose[OF _ measurable_return_val])
    apply (subst measurable_cong_sets[OF sets_M refl], rule Mf)
    apply (rule measurable_compose[OF Mg measurable_return_val], rule refl)
    done
  also have "... = M \<bind> (\<lambda>x. return_val (g (f x)))"
    apply (intro bind_cong refl)
    apply (subst (asm) sets_eq_imp_space_eq[OF sets_M])
    apply (drule measurable_space[OF Mf])
    apply (subst bind_return_val'[where t = t' and t' = t''])
    apply (simp_all add: Mg)
    done
  finally show ?thesis .
qed

lemma bind_return_val_distr:
  assumes sets_M: "sets M = sets (stock_measure t)"
  assumes Mf: "f \<in> measurable (stock_measure t) (stock_measure t')"
  shows "M \<bind> return_val \<circ> f = distr M (stock_measure t') f"
proof-
  have "M \<bind> return_val \<circ> f = M \<bind> return (stock_measure t') \<circ> f"
    apply (intro bind_cong refl)
    apply (subst (asm) sets_eq_imp_space_eq[OF sets_M])
    apply (drule measurable_space[OF Mf])
    apply (simp add: return_val_def o_def)
    done
  also have "... = distr M (stock_measure t') f"
    apply (rule bind_return_distr)
    apply (simp add: sets_eq_imp_space_eq[OF sets_M])
    apply (subst measurable_cong_sets[OF sets_M refl], rule Mf)
    done
  finally show ?thesis .
qed


subsection \<open>Lifting of functions\<close>

definition lift_RealVal where
  "lift_RealVal f \<equiv> \<lambda> RealVal v \<Rightarrow> RealVal (f v) | _ \<Rightarrow> RealVal (f 0)"
definition lift_IntVal where
  "lift_IntVal f \<equiv> \<lambda> IntVal v \<Rightarrow> IntVal (f v) | _ \<Rightarrow> IntVal (f 0)"
definition lift_RealIntVal where
  "lift_RealIntVal f g \<equiv> \<lambda> IntVal v \<Rightarrow> IntVal (f v) | RealVal v \<Rightarrow> RealVal (g v)"

definition lift_RealIntVal2 where
  "lift_RealIntVal2 f g \<equiv>
    map_int_pair (\<lambda>a b. IntVal (f a b))
    (map_real_pair (\<lambda>a b. RealVal (g a b))
      id)"

definition  lift_Comp where
  "lift_Comp f g \<equiv> map_int_pair (\<lambda>a b. BoolVal (f a b))
    (map_real_pair (\<lambda>a b. BoolVal (g a b))
      (\<lambda>_. FALSE))"

lemma lift_RealVal_eq: "lift_RealVal f (RealVal x) = RealVal (f x)"
  by (simp add: lift_RealVal_def)

lemma lift_RealIntVal_Real:
  "x \<in> space (stock_measure REAL) \<Longrightarrow> lift_RealIntVal f g x = lift_RealVal g x"
  by (auto simp: space_embed_measure lift_RealIntVal_def lift_RealVal_def)

lemma lift_RealIntVal_Int:
  "x \<in> space (stock_measure INTEG) \<Longrightarrow> lift_RealIntVal f g x = lift_IntVal f x"
  by (auto simp: space_embed_measure lift_RealIntVal_def lift_IntVal_def)

declare stock_measure.simps[simp del]

lemma measurable_lift_RealVal[measurable]:
  assumes [measurable]: "f \<in> borel_measurable borel"
  shows "lift_RealVal f \<in> measurable REAL REAL"
  unfolding lift_RealVal_def
  by (auto intro!: val_case_stock_measurable)

lemma measurable_lift_IntVal[simp]: "lift_IntVal f \<in> range IntVal \<rightarrow> range IntVal"
  by (auto simp: lift_IntVal_def)

lemma measurable_lift_IntVal'[measurable]: "lift_IntVal f \<in> measurable INTEG INTEG"
  unfolding lift_IntVal_def
  by (auto intro!: val_case_stock_measurable)

lemma split_apply: "(case x of (a, b) \<Rightarrow> f a b) y = (case x of (a, b) \<Rightarrow> f a b y)"
  by (cases x) simp

lemma measurable_lift_Comp_RealVal[measurable]:
  assumes [measurable]: "Measurable.pred (borel \<Otimes>\<^sub>M borel) (case_prod g)"
  shows "lift_Comp f g \<in> measurable (PRODUCT REAL REAL) BOOL"
  unfolding lift_Comp_def by measurable

lemma measurable_lift_Comp_IntVal[simp]:
  "lift_Comp f g \<in> measurable (PRODUCT INTEG INTEG) BOOL"
  unfolding lift_Comp_def
  by (auto intro!: val_case_stock_measurable)

lemma measurable_lift_RealIntVal_IntVal[simp]: "lift_RealIntVal f g \<in> range IntVal \<rightarrow> range IntVal"
  by (auto simp: embed_measure_count_space lift_RealIntVal_def)

lemma measurable_lift_RealIntVal_IntVal'[measurable]:
   "lift_RealIntVal f g \<in> measurable INTEG INTEG"
  by (auto simp: lift_RealIntVal_def intro!: val_case_stock_measurable)

lemma measurable_lift_RealIntVal_RealVal[measurable]:
  assumes [measurable]: "g \<in> borel_measurable borel"
  shows "lift_RealIntVal f g \<in> measurable REAL REAL"
  unfolding lift_RealIntVal_def
  by (auto intro!: val_case_stock_measurable)

lemma measurable_lift_RealIntVal2_IntVal[measurable]:
  "lift_RealIntVal2 f g \<in> measurable (PRODUCT INTEG INTEG) INTEG"
  unfolding lift_RealIntVal2_def
  by (auto intro!: val_case_stock_measurable)

lemma measurable_lift_RealIntVal2_RealVal[measurable]:
  assumes [measurable]: "case_prod g \<in> borel_measurable (borel \<Otimes>\<^sub>M borel)"
  shows "lift_RealIntVal2 f g \<in> measurable (PRODUCT REAL REAL) REAL"
  unfolding lift_RealIntVal2_def by measurable

lemma distr_lift_RealVal:
  fixes f
  assumes Mf[measurable]: "f \<in> borel_measurable borel"
  assumes pdens: "has_subprob_density M (stock_measure REAL) \<delta>"
  assumes dens': "\<And>M \<delta>. has_subprob_density M lborel \<delta> \<Longrightarrow> has_density (distr M borel f) lborel (g \<delta>)"
  defines "N \<equiv> distr M (stock_measure REAL) (lift_RealVal f)"
  shows "has_density N (stock_measure REAL) (g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real)"
proof (rule has_densityI)
  from assms(2) have dens: "has_density M (stock_measure REAL) \<delta>"
    unfolding has_subprob_density_def by simp
  from dens have sets_M[measurable_cong]: "sets M = sets REAL" by (auto dest: has_densityD)

  note measurable_embed_measure1[measurable del]

  have "N = distr M (stock_measure REAL) (lift_RealVal f)" by (simp add: N_def)
  also have "\<dots> = distr M (stock_measure REAL) (RealVal \<circ> f \<circ> extract_real)"
    using sets_eq_imp_space_eq[OF sets_M]
    by (intro distr_cong) (auto simp: lift_RealVal_def stock_measure.simps space_embed_measure)
  also have "... = distr (distr (distr M lborel extract_real) borel f) (stock_measure REAL) RealVal"
    by (subst distr_distr)
       (simp_all add: distr_distr[OF _ measurable_comp[OF _ Mf]] comp_assoc)
  also have dens'': "has_density (distr (distr M lborel extract_real) borel f) lborel (g (\<delta> \<circ> RealVal))"
    by (intro dens' has_subprob_density_embed_measure'') (insert pdens, simp_all add: extract_real_def stock_measure.simps)
  hence "distr (distr M lborel extract_real) borel f = density lborel (g (\<delta> \<circ> RealVal))"
    by (rule has_densityD)
  also have "distr ... (stock_measure REAL) RealVal = embed_measure ... RealVal" (is "_ = ?M")
    by (subst embed_measure_eq_distr[OF inj_RealVal], intro distr_cong)
       (simp_all add: sets_embed_measure stock_measure.simps)
  also have "... = density (embed_measure lborel RealVal) (g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real)"
    using dens''[unfolded o_def]
    apply (subst density_embed_measure', simp, simp add: extract_real_def)
    apply (erule has_densityD, simp add: o_def)
    done
  finally show "N = density (stock_measure REAL) (g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real)"
    by (simp add: stock_measure.simps)

  from dens''[unfolded o_def, THEN has_densityD(1)]  measurable_extract_real
  show "g (\<lambda>x. \<delta> (RealVal x)) \<circ> extract_real \<in> borel_measurable (stock_measure REAL)"
    by (intro measurable_comp) auto
qed (subst space_stock_measure, simp)

lemma distr_lift_IntVal:
  fixes f
  assumes pdens: "has_density M (stock_measure INTEG) \<delta>"
  assumes dens': "\<And>M \<delta>. has_density M (count_space UNIV) \<delta> \<Longrightarrow>
                            has_density (distr M (count_space UNIV) f) (count_space UNIV) (g \<delta>)"
  defines "N \<equiv> distr M (stock_measure INTEG) (lift_IntVal f)"
  shows "has_density N (stock_measure INTEG) (g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int)"
proof (rule has_densityI)
  let ?R = "count_space UNIV" and ?S = "count_space (range IntVal)"
  have Mf: "f \<in> measurable ?R ?R" by simp
  from assms(1) have dens: "has_density M (stock_measure INTEG) \<delta>"
    unfolding has_subprob_density_def by simp
  from dens have sets_M[measurable_cong]: "sets M = sets INTEG" by (auto dest!: has_densityD(2))

  have "N = distr M (stock_measure INTEG) (lift_IntVal f)" by (simp add: N_def)
  also have "\<dots> = distr M (stock_measure INTEG) (IntVal \<circ> f \<circ> extract_int)"
    using sets_eq_imp_space_eq[OF sets_M]
    by (intro distr_cong) (auto simp: space_embed_measure lift_IntVal_def stock_measure.simps)
  also have "\<dots> = distr (distr (distr M ?R extract_int) ?R f) (stock_measure INTEG) IntVal"
    by (subst distr_distr) (simp_all add: distr_distr[OF _ measurable_comp[OF _ Mf]] comp_assoc)
  also have dens'': "has_density (distr (distr M ?R extract_int) ?R f) ?R (g (\<delta> \<circ> IntVal))"
    by (intro dens' has_density_embed_measure'')
       (insert dens, simp_all add: extract_int_def embed_measure_count_space stock_measure.simps)
  hence "distr (distr M ?R extract_int) ?R f = density ?R (g (\<delta> \<circ> IntVal))"
    by (rule has_densityD)
  also have "distr ... (stock_measure INTEG) IntVal = embed_measure ... IntVal" (is "_ = ?M")
    by (subst embed_measure_eq_distr[OF inj_IntVal], intro distr_cong)
       (auto simp: sets_embed_measure subset_image_iff stock_measure.simps)
  also have "... = density (embed_measure ?R IntVal) (g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int)"
    using dens''[unfolded o_def]
    apply (subst density_embed_measure', simp, simp add: extract_int_def)
    apply (erule has_densityD, simp add: o_def)
    done
  finally show "N = density (stock_measure INTEG) (g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int)"
    by (simp add: embed_measure_count_space stock_measure.simps)

  from dens''[unfolded o_def]
    show "g (\<lambda>x. \<delta> (IntVal x)) \<circ> extract_int \<in> borel_measurable (stock_measure INTEG)"
    by (simp add: embed_measure_count_space stock_measure.simps)
qed (subst space_stock_measure, simp)

lemma distr_lift_RealPairVal:
  fixes f f' g
  assumes Mf[measurable]: "case_prod f \<in> borel_measurable borel"
  assumes pdens: "has_subprob_density M (stock_measure (PRODUCT REAL REAL)) \<delta>"
  assumes dens': "\<And>M \<delta>. has_subprob_density M lborel \<delta> \<Longrightarrow> has_density (distr M borel (case_prod f)) lborel (g \<delta>)"
  defines "N \<equiv> distr M (stock_measure REAL) (lift_RealIntVal2 f' f)"
  shows "has_density N (stock_measure REAL) (g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real)"
proof (rule has_densityI)
  from assms(2) have dens: "has_density M (stock_measure (PRODUCT REAL REAL)) \<delta>"
    unfolding has_subprob_density_def by simp
  have sets_M[measurable_cong]: "sets M = sets (stock_measure (PRODUCT REAL REAL))"
    by (auto simp: has_subprob_densityD[OF pdens])

  have "N = distr M (stock_measure REAL) (lift_RealIntVal2 f' f)" by (simp add: N_def)
  also have "... = distr M (stock_measure REAL) (RealVal \<circ> case_prod f \<circ> extract_real_pair)"
    using sets_eq_imp_space_eq[OF sets_M]
    by (intro distr_cong) (auto simp: lift_RealIntVal2_def space_embed_measure space_pair_measure stock_measure.simps)
  also have "... = distr (distr (distr M lborel extract_real_pair) borel (case_prod f)) REAL RealVal"
    by (subst distr_distr) (simp_all add: distr_distr[OF _ measurable_comp[OF _ Mf]] comp_assoc)
  also have dens'': "has_density (distr (distr M lborel extract_real_pair) borel (case_prod f)) lborel
                      (g (\<delta> \<circ> RealPairVal))" using inj_RealPairVal embed_measure_RealPairVal
    by (intro dens' has_subprob_density_embed_measure'')
       (insert pdens, simp_all add: RealPairVal_def split: prod.split)
  hence "distr (distr M lborel extract_real_pair) borel (case_prod f) =
             density lborel (g (\<delta> \<circ> RealPairVal))" by (rule has_densityD)
  also have "distr ... (stock_measure REAL) RealVal = embed_measure ... RealVal" (is "_ = ?M")
    by (subst embed_measure_eq_distr[OF inj_RealVal], intro distr_cong)
       (simp_all add: sets_embed_measure stock_measure.simps)
  also have "... = density (embed_measure lborel RealVal) (g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real)"
    using dens''[unfolded o_def]
    by (subst density_embed_measure', simp, simp add: extract_real_def)
       (erule has_densityD, simp add: o_def)
  finally show "N = density (stock_measure REAL) (g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real)"
    by (simp add: stock_measure.simps)

  from dens''[unfolded o_def]
    show "g (\<lambda>x. \<delta> (RealPairVal x)) \<circ> extract_real \<in> borel_measurable (stock_measure REAL)"
    by (intro measurable_comp)
       (rule measurable_extract_real, subst measurable_lborel2[symmetric], erule has_densityD)
qed (subst space_stock_measure, simp)

lemma distr_lift_IntPairVal:
  fixes f f'
  assumes pdens: "has_density M (stock_measure (PRODUCT INTEG INTEG)) \<delta>"
  assumes dens': "\<And>M \<delta>. has_density M (count_space UNIV) \<delta> \<Longrightarrow>
                            has_density (distr M (count_space UNIV) (case_prod f))
                                        (count_space UNIV) (g \<delta>)"
  defines "N \<equiv> distr M (stock_measure INTEG) (lift_RealIntVal2 f f')"
  shows "has_density N (stock_measure INTEG) (g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int)"
proof (rule has_densityI)
  let ?R = "count_space UNIV" and ?S = "count_space (range IntVal)"
  and ?T = "count_space (range IntPairVal)" and ?tp = "PRODUCT INTEG INTEG"
  have Mf: "f \<in> measurable ?R ?R" by simp
  have MIV: "IntVal \<in> measurable ?R ?S" by simp
  from assms(1) have dens: "has_density M (stock_measure ?tp) \<delta>"
    unfolding has_subprob_density_def by simp
  from dens have "M = density (stock_measure ?tp) \<delta>" by (rule has_densityD)
  hence sets_M: "sets M = sets ?T" by (subst embed_measure_IntPairVal[symmetric]) auto
  hence [simp]: "space M = space ?T" by (rule sets_eq_imp_space_eq)
  from sets_M have [simp]: "measurable M = measurable (count_space (range IntPairVal))"
    by (intro ext measurable_cong_sets) simp_all

  have "N = distr M (stock_measure INTEG) (lift_RealIntVal2 f f')" by (simp add: N_def)

  also have "... = distr M (stock_measure INTEG) (IntVal \<circ> case_prod f \<circ> extract_int_pair)"
    by (intro distr_cong) (auto simp: lift_RealIntVal2_def space_embed_measure space_pair_measure IntPairVal_def)
  also have "... = distr (distr (distr M (count_space UNIV) extract_int_pair)
                        (count_space UNIV) (case_prod f)) (stock_measure INTEG) IntVal"
    apply (subst distr_distr[of _ ?R, symmetric], simp, simp)
    apply (subst distr_distr[symmetric], subst stock_measure.simps, rule MIV,
           simp_all add: assms(1) cong: distr_cong)
    done
  also have dens'': "has_density (distr (distr M (count_space UNIV) extract_int_pair) ?R (case_prod f)) ?R
                      (g (\<delta> \<circ> IntPairVal))" using inj_IntPairVal embed_measure_IntPairVal
    by (intro dens' has_density_embed_measure'')
       (insert dens, simp_all add: extract_int_def embed_measure_count_space IntPairVal_def split: prod.split)
  hence "distr (distr M (count_space UNIV) extract_int_pair) ?R (case_prod f) =
             density ?R (g (\<delta> \<circ> IntPairVal))" by (rule has_densityD)
  also have "distr ... (stock_measure INTEG) IntVal = embed_measure ... IntVal" (is "_ = ?M")
    by (subst embed_measure_eq_distr[OF inj_IntVal], intro distr_cong)
       (auto simp: sets_embed_measure subset_image_iff stock_measure.simps)
  also have "... = density (embed_measure ?R IntVal) (g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int)"
    using dens''[unfolded o_def]
    by (subst density_embed_measure', simp, simp add: extract_int_def)
       (erule has_densityD, simp add: o_def)
  finally show "N = density (stock_measure INTEG) (g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int)"
    by (simp add: embed_measure_count_space stock_measure.simps)

  from dens''[unfolded o_def]
    show "g (\<lambda>x. \<delta> (IntPairVal x)) \<circ> extract_int \<in> borel_measurable (stock_measure INTEG)"
    by (simp add: embed_measure_count_space stock_measure.simps)
qed (subst space_stock_measure, simp)

end
