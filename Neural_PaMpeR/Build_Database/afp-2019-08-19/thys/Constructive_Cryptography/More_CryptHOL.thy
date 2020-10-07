(* Author: Andreas Lochbihler, ETH Zurich *)

theory More_CryptHOL imports
  CryptHOL.CryptHOL
begin

(* Misc *)

lemma is_empty_image [simp]: "Set.is_empty (f ` A) = Set.is_empty A"
  by(auto simp add: Set.is_empty_def)

lemma inj_on_map_sum [simp]:
  "\<lbrakk> inj_on f A; inj_on g B \<rbrakk> \<Longrightarrow> inj_on (map_sum f g) (A <+> B)"
proof(rule inj_onI, goal_cases)
  case (1 x y)
  then show ?case by(cases x; cases y; auto simp add: inj_on_def)
qed

lemma inv_into_map_sum:
  "inv_into (A <+> B) (map_sum f g) x = map_sum (inv_into A f) (inv_into B g) x"
  if "x \<in> f ` A <+> g ` B" "inj_on f A" "inj_on g B"
  using that by(cases rule: PlusE[consumes 1])(auto simp add: inv_into_f_eq f_inv_into_f)

lemma Pair_fst_Unity: "(fst x, ()) = x"
  by(cases x) simp

fun rsuml :: "('a + 'b) + 'c \<Rightarrow> 'a + ('b + 'c)" where
  "rsuml (Inl (Inl a)) = Inl a"
| "rsuml (Inl (Inr b)) = Inr (Inl b)"
| "rsuml (Inr c) = Inr (Inr c)"

fun lsumr :: "'a + ('b + 'c) \<Rightarrow> ('a + 'b) + 'c" where
  "lsumr (Inl a) = Inl (Inl a)"
| "lsumr (Inr (Inl b)) = Inl (Inr b)"
| "lsumr (Inr (Inr c)) = Inr c"

lemma rsuml_lsumr [simp]: "rsuml (lsumr x) = x"
  by(cases x rule: lsumr.cases) simp_all

lemma lsumr_rsuml [simp]: "lsumr (rsuml x) = x"
  by(cases x rule: rsuml.cases) simp_all

definition rprodl :: "('a \<times> 'b) \<times> 'c \<Rightarrow> 'a \<times> ('b \<times> 'c)" where "rprodl = (\<lambda>((a, b), c). (a, (b, c)))"

lemma rprodl_simps [simp]: "rprodl ((a, b), c) = (a, (b, c))"
  by(simp add: rprodl_def)

lemma rprodl_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_prod (rel_prod A B) C ===> rel_prod A (rel_prod B C)) rprodl rprodl"
  unfolding rprodl_def by transfer_prover

definition lprodr :: "'a \<times> ('b \<times> 'c) \<Rightarrow> ('a \<times> 'b) \<times> 'c" where "lprodr = (\<lambda>(a, b, c). ((a, b), c))"

lemma lprodr_simps [simp]: "lprodr (a, b, c) = ((a, b), c)"
  by(simp add: lprodr_def)

lemma lprodr_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_prod A (rel_prod B C) ===> rel_prod (rel_prod A B) C) lprodr lprodr"
  unfolding lprodr_def by transfer_prover

lemma lprodr_inverse [simp]: "rprodl (lprodr x) = x"
  by(cases x) auto

lemma rprodl_inverse [simp]: "lprodr (rprodl x) = x"
  by(cases x) auto


lemma rel_fun_comp:
  "\<And>f g h. rel_fun A B (f \<circ> g) h = rel_fun A (\<lambda>x. B (f x)) g h"
  "\<And>f g h. rel_fun A B f (g \<circ> h) = rel_fun A (\<lambda>x y. B x (g y)) f h"
  by(auto simp add: rel_fun_def)

lemma rel_fun_map_fun1: "rel_fun (BNF_Def.Grp UNIV h)\<inverse>\<inverse> A f g \<Longrightarrow> rel_fun (=) A (map_fun h id f) g"
  by(auto simp add: rel_fun_def Grp_def)

lemma rel_fun_map_fun2: "rel_fun (eq_on (range h)) A f g \<Longrightarrow> rel_fun (BNF_Def.Grp UNIV h)\<inverse>\<inverse> A f (map_fun h id g)"
  by(auto simp add: rel_fun_def Grp_def eq_onp_def)

lemma map_fun2_id: "map_fun f g x = g \<circ> map_fun f id x"
  by(simp add: map_fun_def o_assoc)

lemma rel_fun_refl_eq_onp:
  "(\<And>z. z \<in> f ` X \<Longrightarrow> A z z) \<Longrightarrow> rel_fun (eq_on X) A f f"
  by(auto simp add: rel_fun_def eq_onp_def)

lemma map_fun_id2_in: "map_fun g h f = map_fun g id (h \<circ> f)"
  by(simp add: map_fun_def)

lemma Domainp_rel_fun_le: "Domainp (rel_fun A B) \<le> pred_fun (Domainp A) (Domainp B)"
  by(auto dest: rel_funD)

lemma eq_onE: "\<lbrakk> eq_on X a b; \<lbrakk> b \<in> X; a = b \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis" by auto

lemma Domainp_eq_on [simp]: "Domainp (eq_on X) = (\<lambda>x. x \<in> X)"
  by auto

declare eq_on_def [simp del]

lemma pred_prod_mono' [mono]:
  "pred_prod A B xy \<longrightarrow> pred_prod A' B' xy"
  if "\<And>x. A x \<longrightarrow> A' x" "\<And>y. B y \<longrightarrow> B' y"
  using that by(cases xy) auto

fun rel_witness_prod :: "('a \<times> 'b) \<times> ('c \<times> 'd) \<Rightarrow> (('a \<times> 'c) \<times> ('b \<times> 'd))" where
  "rel_witness_prod ((a, b), (c, d)) = ((a, c), (b, d))"

consts relcompp_witness :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'c \<Rightarrow> 'b"
specification (relcompp_witness)
  relcompp_witness1: "(A OO B) (fst xy) (snd xy) \<Longrightarrow> A (fst xy) (relcompp_witness A B xy)"
  relcompp_witness2: "(A OO B) (fst xy) (snd xy) \<Longrightarrow> B (relcompp_witness A B xy) (snd xy)"
  apply(fold all_conj_distrib)
  apply(rule choice allI)+
  by(auto intro: choice allI)

lemmas relcompp_witness[of _ _ "(x, y)" for x y, simplified] = relcompp_witness1 relcompp_witness2

hide_fact (open) relcompp_witness1 relcompp_witness2

lemma relcompp_witness_eq [simp]: "relcompp_witness (=) (=) (x, x) = x"
  using relcompp_witness(1)[of "(=)" "(=)" x x] by(simp add: eq_OO)

fun rel_witness_option :: "'a option \<times> 'b option \<Rightarrow> ('a \<times> 'b) option" where
  "rel_witness_option (Some x, Some y) = Some (x, y)"
| "rel_witness_option (None, None) = None"
| "rel_witness_option _ = None" \<comment> \<open>Just to make the definition complete\<close>

lemma rel_witness_option:
  shows set_rel_witness_option: "\<lbrakk> rel_option A x y; (a, b) \<in> set_option (rel_witness_option (x, y)) \<rbrakk> \<Longrightarrow> A a b"
    and map1_rel_witness_option: "rel_option A x y \<Longrightarrow> map_option fst (rel_witness_option (x, y)) = x"
    and map2_rel_witness_option: "rel_option A x y \<Longrightarrow> map_option snd (rel_witness_option (x, y)) = y"
  by(cases "(x, y)" rule: rel_witness_option.cases; simp; fail)+

lemma rel_witness_option1:
  assumes "rel_option A x y"
  shows "rel_option (\<lambda>a (a', b). a = a' \<and> A a' b) x (rel_witness_option (x, y))"
  using map1_rel_witness_option[OF assms, symmetric]
  unfolding option.rel_eq[symmetric] option.rel_map
  by(rule option.rel_mono_strong)(auto intro: set_rel_witness_option[OF assms])

lemma rel_witness_option2:
  assumes "rel_option A x y"
  shows "rel_option (\<lambda>(a, b') b. b = b' \<and> A a b') (rel_witness_option (x, y)) y"
  using map2_rel_witness_option[OF assms]
  unfolding option.rel_eq[symmetric] option.rel_map
  by(rule option.rel_mono_strong)(auto intro: set_rel_witness_option[OF assms])


definition rel_witness_fun :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'd) \<times> ('c \<Rightarrow> 'e) \<Rightarrow> ('b \<Rightarrow> 'd \<times> 'e)" where
  "rel_witness_fun A A' = (\<lambda>(f, g) b. (f (THE a. A a b), g (THE c. A' b c)))"

lemma
  assumes fg: "rel_fun (A OO A') B f g"
    and A: "left_unique A" "right_total A"
    and A': "right_unique A'" "left_total A'"
  shows rel_witness_fun1: "rel_fun A (\<lambda>x (x', y). x = x' \<and> B x' y) f (rel_witness_fun A A' (f, g))"
    and rel_witness_fun2: "rel_fun A' (\<lambda>(x, y') y. y = y' \<and> B x y') (rel_witness_fun A A' (f, g)) g"
proof (goal_cases)
  case 1
  have "A x y \<Longrightarrow> f x = f (THE a. A a y) \<and> B (f (THE a. A a y)) (g (The (A' y)))" for x y 
    by(rule left_totalE[OF A'(2)]; erule meta_allE[of _ y]; erule exE; frule (1) fg[THEN rel_funD, OF relcomppI])
      (auto intro!: arg_cong[where f=f] arg_cong[where f=g] rel_funI the_equality the_equality[symmetric] dest: left_uniqueD[OF A(1)] right_uniqueD[OF A'(1)] elim!: arg_cong2[where f=B, THEN iffD2, rotated -1])

  with 1 show ?case by(clarsimp simp add: rel_fun_def rel_witness_fun_def)
next
  case 2
  have "A' x y \<Longrightarrow> g y = g (The (A' x)) \<and> B (f (THE a. A a x)) (g (The (A' x)))" for x y
    by(rule right_totalE[OF A(2), of x]; frule (1) fg[THEN rel_funD, OF relcomppI])
      (auto intro!: arg_cong[where f=f] arg_cong[where f=g] rel_funI the_equality the_equality[symmetric] dest: left_uniqueD[OF A(1)] right_uniqueD[OF A'(1)] elim!: arg_cong2[where f=B, THEN iffD2, rotated -1])

  with 2 show ?case by(clarsimp simp add: rel_fun_def rel_witness_fun_def)    
qed

lemma rel_witness_fun_eq [simp]: "rel_witness_fun (=) (=) (f, g) = (\<lambda>x. (f x, g x))"
  by(simp add: rel_witness_fun_def)


consts rel_witness_pmf :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a pmf \<times> 'b pmf \<Rightarrow> ('a \<times> 'b) pmf"
specification (rel_witness_pmf)
  set_rel_witness_pmf': "rel_pmf A (fst xy) (snd xy) \<Longrightarrow> set_pmf (rel_witness_pmf A xy) \<subseteq> {(a, b). A a b}"
  map1_rel_witness_pmf': "rel_pmf A (fst xy) (snd xy) \<Longrightarrow> map_pmf fst (rel_witness_pmf A xy) = fst xy"
  map2_rel_witness_pmf': "rel_pmf A (fst xy) (snd xy) \<Longrightarrow> map_pmf snd (rel_witness_pmf A xy) = snd xy"
  apply(fold all_conj_distrib imp_conjR)
  apply(rule choice allI)+
  apply(unfold pmf.in_rel)
  by blast

lemmas set_rel_witness_pmf = set_rel_witness_pmf'[of _ "(x, y)" for x y, simplified]
lemmas map1_rel_witness_pmf = map1_rel_witness_pmf'[of _ "(x, y)" for x y, simplified]
lemmas map2_rel_witness_pmf = map2_rel_witness_pmf'[of _ "(x, y)" for x y, simplified]
lemmas rel_witness_pmf = set_rel_witness_pmf map1_rel_witness_pmf map2_rel_witness_pmf

lemma rel_witness_pmf1:
  assumes "rel_pmf A p q" 
  shows "rel_pmf (\<lambda>a (a', b). a = a' \<and> A a' b) p (rel_witness_pmf A (p, q))"
  using map1_rel_witness_pmf[OF assms, symmetric]
  unfolding pmf.rel_eq[symmetric] pmf.rel_map
  by(rule pmf.rel_mono_strong)(auto dest: set_rel_witness_pmf[OF assms, THEN subsetD])

lemma rel_witness_pmf2:
  assumes "rel_pmf A p q" 
  shows "rel_pmf (\<lambda>(a, b') b. b = b' \<and> A a b') (rel_witness_pmf A (p, q)) q"
  using map2_rel_witness_pmf[OF assms]
  unfolding pmf.rel_eq[symmetric] pmf.rel_map
  by(rule pmf.rel_mono_strong)(auto dest: set_rel_witness_pmf[OF assms, THEN subsetD])

definition rel_witness_spmf :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a spmf \<times> 'b spmf \<Rightarrow> ('a \<times> 'b) spmf" where
  "rel_witness_spmf A = map_pmf rel_witness_option \<circ> rel_witness_pmf (rel_option A)"

lemma assumes "rel_spmf A p q"
  shows rel_witness_spmf1: "rel_spmf (\<lambda>a (a', b). a = a' \<and> A a' b) p (rel_witness_spmf A (p, q))"
    and rel_witness_spmf2: "rel_spmf (\<lambda>(a, b') b. b = b' \<and> A a b') (rel_witness_spmf A (p, q)) q"
  by(auto simp add: pmf.rel_map rel_witness_spmf_def intro: pmf.rel_mono_strong[OF rel_witness_pmf1[OF assms]] rel_witness_option1 pmf.rel_mono_strong[OF rel_witness_pmf2[OF assms]] rel_witness_option2)


primrec (transfer) enforce_option :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "enforce_option P (Some x) = (if P x then Some x else None)"
| "enforce_option P None = None"

lemma set_enforce_option [simp]: "set_option (enforce_option P x) = {a \<in> set_option x. P a}"
  by(cases x) auto

lemma enforce_map_option: "enforce_option P (map_option f x) = map_option f (enforce_option (P \<circ> f) x)"
  by(cases x) auto

lemma enforce_bind_option [simp]:
  "enforce_option P (Option.bind x f) = Option.bind x (enforce_option P \<circ> f)"
  by(cases x) auto

lemma enforce_option_alt_def:
  "enforce_option P x = Option.bind x (\<lambda>a. Option.bind (assert_option (P a)) (\<lambda>_ :: unit. Some a))"
  by(cases x) simp_all

lemma enforce_option_eq_None_iff [simp]:
  "enforce_option P x = None \<longleftrightarrow> (\<forall>a. x = Some a \<longrightarrow> \<not> P a)"
  by(cases x) auto

lemma enforce_option_eq_Some_iff [simp]:
  "enforce_option P x = Some y \<longleftrightarrow> x = Some y \<and> P y"
  by(cases x) auto

lemma Some_eq_enforce_option_iff [simp]:
  "Some y = enforce_option P x \<longleftrightarrow> x = Some y \<and> P y"
  by(cases x) auto

lemma enforce_option_top [simp]: "enforce_option \<top> = id"
  by(rule ext; rename_tac x; case_tac x; simp)

lemma enforce_option_K_True [simp]: "enforce_option (\<lambda>_. True) x = x"
  by(cases x) simp_all

lemma enforce_option_bot [simp]: "enforce_option \<bottom> = (\<lambda>_. None)"
  by(simp add: fun_eq_iff)

lemma enforce_option_K_False [simp]: "enforce_option (\<lambda>_. False) x = None"
  by simp

lemma enforce_pred_id_option: "pred_option P x \<Longrightarrow> enforce_option P x = x"
  by(cases x) auto

lemma rel_fun_refl: "\<lbrakk> A \<le> (=); (=) \<le> B \<rbrakk> \<Longrightarrow> (=) \<le> rel_fun A B"
  by(subst fun.rel_eq[symmetric])(rule fun_mono)

lemma rel_fun_mono_strong:
  "\<lbrakk> rel_fun A B f g; A' \<le> A; \<And>x y. \<lbrakk> x \<in> f ` {x. Domainp A' x}; y \<in> g ` {x. Rangep A' x}; B x y \<rbrakk> \<Longrightarrow> B' x y \<rbrakk> \<Longrightarrow> rel_fun A' B' f g"
  by(auto simp add: rel_fun_def) fastforce

lemma rel_fun_refl_strong: 
  assumes "A \<le> (=)" "\<And>x. x \<in> f ` {x. Domainp A x} \<Longrightarrow> B x x"
  shows "rel_fun A B f f"
proof -
  have "rel_fun (=) (=) f f" by(simp add: rel_fun_eq)
  then show ?thesis using assms(1)
    by(rule rel_fun_mono_strong) (auto intro: assms(2))
qed

lemma Grp_iff: "BNF_Def.Grp B g x y \<longleftrightarrow> y = g x \<and> x \<in> B" by(simp add: Grp_def)

lemma Rangep_Grp: "Rangep (BNF_Def.Grp A f) = (\<lambda>x. x \<in> f ` A)"
  by(auto simp add: fun_eq_iff Grp_iff)

lemma Domainp_Grp: "Domainp (BNF_Def.Grp A f) = (\<lambda>x. x \<in> A)"
  by(auto simp add: Grp_iff fun_eq_iff)

lemma rel_fun_Grp:
  "rel_fun (BNF_Def.Grp UNIV h)\<inverse>\<inverse> (BNF_Def.Grp A g) = BNF_Def.Grp {f. f ` range h \<subseteq> A} (map_fun h g)"
  by(auto simp add: rel_fun_def fun_eq_iff Grp_iff)

lemma wf_strict_prefix: "wfP strict_prefix"
proof -
  from wf have "wf (inv_image {(x, y). x < y} length)" by(rule wf_inv_image)
  moreover have "{(x, y). strict_prefix x y} \<subseteq> inv_image {(x, y). x < y} length" by(auto intro: prefix_length_less)
  ultimately show ?thesis unfolding wfP_def by(rule wf_subset)
qed

lemma strict_prefix_setD:
  "strict_prefix xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  by(auto simp add: strict_prefix_def prefix_def)


(* SPMF *)

lemma weight_assert_spmf [simp]: "weight_spmf (assert_spmf b) = indicator {True} b"
  by(simp split: split_indicator)

definition enforce_spmf :: "('a \<Rightarrow> bool) \<Rightarrow> 'a spmf \<Rightarrow> 'a spmf" where
  "enforce_spmf P = map_pmf (enforce_option P)"

lemma enforce_spmf_parametric [transfer_rule]: includes lifting_syntax shows
  "((A ===> (=)) ===> rel_spmf A ===> rel_spmf A) enforce_spmf enforce_spmf"
  unfolding enforce_spmf_def by transfer_prover

lemma enforce_return_spmf [simp]:
  "enforce_spmf P (return_spmf x) = (if P x then return_spmf x else return_pmf None)"
  by(simp add: enforce_spmf_def)

lemma enforce_return_pmf_None [simp]:
  "enforce_spmf P (return_pmf None) = return_pmf None"
  by(simp add: enforce_spmf_def)

lemma enforce_map_spmf:
  "enforce_spmf P (map_spmf f p) = map_spmf f (enforce_spmf (P \<circ> f) p)"
  by(simp add: enforce_spmf_def pmf.map_comp o_def enforce_map_option)

lemma enforce_bind_spmf [simp]:
  "enforce_spmf P (bind_spmf p f) = bind_spmf p (enforce_spmf P \<circ> f)"
  by(auto simp add: enforce_spmf_def bind_spmf_def map_bind_pmf intro!: bind_pmf_cong split: option.split)

lemma set_enforce_spmf [simp]: "set_spmf (enforce_spmf P p) = {a \<in> set_spmf p. P a}"
  by(auto simp add: enforce_spmf_def in_set_spmf)

lemma enforce_spmf_alt_def:
  "enforce_spmf P p = bind_spmf p (\<lambda>a. bind_spmf (assert_spmf (P a)) (\<lambda>_ :: unit. return_spmf a))"
  by(auto simp add: enforce_spmf_def assert_spmf_def map_pmf_def bind_spmf_def bind_return_pmf intro!: bind_pmf_cong split: option.split)

lemma bind_enforce_spmf [simp]:
  "bind_spmf (enforce_spmf P p) f = bind_spmf p (\<lambda>x. if P x then f x else return_pmf None)"
  by(auto simp add: enforce_spmf_alt_def assert_spmf_def intro!: bind_spmf_cong)

lemma weight_enforce_spmf:
  "weight_spmf (enforce_spmf P p) = weight_spmf p - measure (measure_spmf p) {x. \<not> P x}" (is "?lhs = ?rhs")
proof -
  have "?lhs = LINT x|measure_spmf p. indicator {x. P x} x"
    by(auto simp add: enforce_spmf_alt_def weight_bind_spmf o_def simp del: Bochner_Integration.integral_indicator intro!: Bochner_Integration.integral_cong split: split_indicator)
  also have "\<dots> = ?rhs"
    by(subst measure_spmf.finite_measure_Diff[symmetric])(auto simp add: space_measure_spmf intro!: arg_cong2[where f=measure])
  finally show ?thesis .
qed

lemma lossless_enforce_spmf [simp]:
  "lossless_spmf (enforce_spmf P p) \<longleftrightarrow> lossless_spmf p \<and> set_spmf p \<subseteq> {x. P x}"
  by(auto simp add: enforce_spmf_alt_def)

lemma enforce_spmf_top [simp]: "enforce_spmf \<top> = id"
  by(simp add: enforce_spmf_def)

lemma enforce_spmf_K_True [simp]: "enforce_spmf (\<lambda>_. True) p = p"
  using enforce_spmf_top[THEN fun_cong, of p] by(simp add: top_fun_def)

lemma enforce_spmf_bot [simp]: "enforce_spmf \<bottom> = (\<lambda>_. return_pmf None)"
  by(simp add: enforce_spmf_def fun_eq_iff)

lemma enforce_spmf_K_False [simp]: "enforce_spmf (\<lambda>_. False) p = return_pmf None"
  using enforce_spmf_bot[THEN fun_cong, of p] by(simp add: bot_fun_def)

lemma enforce_pred_id_spmf: "enforce_spmf P p = p" if "pred_spmf P p"
proof -
  have "enforce_spmf P p = map_pmf id p" using that
    by(auto simp add: enforce_spmf_def enforce_pred_id_option simp del: map_pmf_id intro!: pmf.map_cong_pred[OF refl] elim!: pmf_pred_mono_strong)
  then show ?thesis by simp
qed

lemma map_the_spmf_of_pmf [simp]: "map_pmf the (spmf_of_pmf p) = p"
  by(simp add: spmf_of_pmf_def pmf.map_comp o_def)

lemma bind_bind_conv_pair_spmf:
  "bind_spmf p (\<lambda>x. bind_spmf q (f x)) = bind_spmf (pair_spmf p q) (\<lambda>(x, y). f x y)"
  by(simp add: pair_spmf_alt_def)

lemma cond_pmf_of_set:
  assumes fin: "finite A" and nonempty: "A \<inter> B \<noteq> {}"
  shows "cond_pmf (pmf_of_set A) B = pmf_of_set (A \<inter> B)" (is "?lhs = ?rhs")
proof(rule pmf_eqI)
  from nonempty have A: "A \<noteq> {}" by auto
  show "pmf ?lhs x = pmf ?rhs x" for x
    by(subst pmf_cond; clarsimp simp add: fin A nonempty measure_pmf_of_set split: split_indicator)
qed

lemma cond_spmf_spmf_of_set:
  "cond_spmf (spmf_of_set A) B = spmf_of_set (A \<inter> B)" if "finite A"
  by(rule spmf_eqI)(auto simp add: spmf_of_set measure_spmf_of_set that split: split_indicator)

lemma pair_pmf_of_set:
  assumes A: "finite A" "A \<noteq> {}"
    and B: "finite B" "B \<noteq> {}"
  shows "pair_pmf (pmf_of_set A) (pmf_of_set B) = pmf_of_set (A \<times> B)"
  by(rule pmf_eqI)(clarsimp simp add: pmf_pair assms split: split_indicator)

lemma pair_spmf_of_set:
  "pair_spmf (spmf_of_set A) (spmf_of_set B) = spmf_of_set (A \<times> B)"
  by(rule spmf_eqI)(clarsimp simp add: spmf_of_set card_cartesian_product split: split_indicator)

(*lemma cond_bind_pmf:
  assumes *: "\<And>x. x \<in> set_pmf p \<Longrightarrow> set_pmf (f x) \<inter> A \<noteq> {}"
  shows "cond_pmf (bind_pmf p f) A = bind_pmf p (\<lambda>x. cond_pmf (f x) A)"
  apply(rule pmf_eqI)
  apply(subst pmf_cond)
  subgoal using * set_pmf_not_empty[of p] by auto
  apply clarsimp
  oops*)

lemma emeasure_cond_pmf:
  fixes p A
  defines "q \<equiv> cond_pmf p A"
  assumes "set_pmf p \<inter> A \<noteq> {}"
  shows "emeasure (measure_pmf q) B = emeasure (measure_pmf p) (A \<inter> B) / emeasure (measure_pmf p) A"
proof -
  note [transfer_rule] = cond_pmf.transfer[OF assms(2), folded q_def]
  interpret pmf_as_measure .
  show ?thesis by transfer simp
qed

lemma measure_cond_pmf:
  "measure (measure_pmf (cond_pmf p A)) B = measure (measure_pmf p) (A \<inter> B) / measure (measure_pmf p) A"
  if "set_pmf p \<inter> A \<noteq> {}"
  using emeasure_cond_pmf[OF that, of B] that 
  by(auto simp add: measure_pmf.emeasure_eq_measure measure_pmf_posI divide_ennreal)

lemma emeasure_measure_pmf_zero_iff: "emeasure (measure_pmf p) s = 0 \<longleftrightarrow> set_pmf p \<inter> s = {}" (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> (AE x in measure_pmf p. x \<notin> s)"
    by(subst AE_iff_measurable)(auto)
  also have "\<dots> = ?rhs" by(auto simp add: AE_measure_pmf_iff)
  finally show ?thesis .
qed

lemma emeasure_cond_spmf:
  "emeasure (measure_spmf (cond_spmf p A)) B = emeasure (measure_spmf p) (A \<inter> B) / emeasure (measure_spmf p) A"
  apply(clarsimp simp add: cond_spmf_def emeasure_measure_spmf_conv_measure_pmf emeasure_measure_pmf_zero_iff set_pmf_Int_Some split!: if_split)
   apply blast
  apply(subst (asm) emeasure_cond_pmf)
  by(auto simp add: set_pmf_Int_Some image_Int)

lemma measure_cond_spmf:
  "measure (measure_spmf (cond_spmf p A)) B = measure (measure_spmf p) (A \<inter> B) / measure (measure_spmf p) A"
  apply(clarsimp simp add: cond_spmf_def measure_measure_spmf_conv_measure_pmf measure_pmf_zero_iff set_pmf_Int_Some split!: if_split)
  apply(subst (asm) measure_cond_pmf)
  by(auto simp add: image_Int set_pmf_Int_Some)


lemma lossless_cond_spmf [simp]: "lossless_spmf (cond_spmf p A) \<longleftrightarrow> set_spmf p \<inter> A \<noteq> {}"
  by(clarsimp simp add: cond_spmf_def lossless_iff_set_pmf_None set_pmf_Int_Some)

lemma measure_spmf_eq_density: "measure_spmf p = density (count_space UNIV) (spmf p)"
  by(rule measure_eqI)(simp_all add: emeasure_density nn_integral_spmf[symmetric] nn_integral_count_space_indicator)

lemma integral_measure_spmf:
  fixes f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes A: "finite A"
  shows "(\<And>a. a \<in> set_spmf M \<Longrightarrow> f a \<noteq> 0 \<Longrightarrow> a \<in> A) \<Longrightarrow> (LINT x|measure_spmf M. f x) = (\<Sum>a\<in>A. spmf M a *\<^sub>R f a)"
  unfolding measure_spmf_eq_density
  apply (simp add: integral_density)
  apply (subst lebesgue_integral_count_space_finite_support)
  by (auto intro!: finite_subset[OF _ \<open>finite A\<close>] sum.mono_neutral_left simp: spmf_eq_0_set_spmf)


lemma image_set_spmf_eq:
  "f ` set_spmf p = g ` set_spmf q" if "ASSUMPTION (map_spmf f p = map_spmf g q)"
  using that[unfolded ASSUMPTION_def, THEN arg_cong[where f=set_spmf]] by simp

lemma map_spmf_const: "map_spmf (\<lambda>_. x) p = scale_spmf (weight_spmf p) (return_spmf x)"
  by(simp add: map_spmf_conv_bind_spmf bind_spmf_const)

lemma cond_return_pmf [simp]: "cond_pmf (return_pmf x) A = return_pmf x" if "x \<in> A"
  using that by(intro pmf_eqI)(auto simp add: pmf_cond split: split_indicator)

lemma cond_return_spmf [simp]: "cond_spmf (return_spmf x) A = (if x \<in> A then return_spmf x else return_pmf None)"
  by(simp add: cond_spmf_def)

lemma measure_range_Some_eq_weight:
  "measure (measure_pmf p) (range Some) = weight_spmf p"
  by (simp add: measure_measure_spmf_conv_measure_pmf space_measure_spmf)

lemma restrict_spmf_eq_return_pmf_None [simp]:
  "restrict_spmf p A = return_pmf None \<longleftrightarrow> set_spmf p \<inter> A = {}"
  by(auto 4 3 simp add: restrict_spmf_def map_pmf_eq_return_pmf_iff bind_UNION in_set_spmf bind_eq_None_conv option.the_def dest: bspec split: if_split_asm option.split_asm)

lemma integrable_scale_measure [simp]:
  "\<lbrakk> integrable M f; r < \<top> \<rbrakk> \<Longrightarrow> integrable (scale_measure r M) f" 
  for f :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  by(auto simp add: integrable_iff_bounded nn_integral_scale_measure ennreal_mult_less_top)

lemma integral_scale_measure:
  assumes "integrable M f" "r < \<top>"
  shows "integral\<^sup>L (scale_measure r M) f = enn2real r * integral\<^sup>L M f"
  using assms
  apply(subst (1 2) real_lebesgue_integral_def)
    apply(simp_all add: nn_integral_scale_measure ennreal_enn2real_if)
  by(auto simp add: ennreal_mult_less_top ennreal_less_top_iff ennreal_mult_eq_top_iff enn2real_mult right_diff_distrib elim!: integrableE)

definition mk_lossless :: "'a spmf \<Rightarrow> 'a spmf" where
  "mk_lossless p = scale_spmf (inverse (weight_spmf p)) p"

lemma mk_lossless_idem [simp]: "mk_lossless (mk_lossless p) = mk_lossless p"
  by(simp add: mk_lossless_def weight_scale_spmf min_def max_def inverse_eq_divide) 

lemma mk_lossless_return [simp]: "mk_lossless (return_pmf x) = return_pmf x"
  by(cases x)(simp_all add: mk_lossless_def)

lemma mk_lossless_map [simp]: "mk_lossless (map_spmf f p) = map_spmf f (mk_lossless p)"
  by(simp add: mk_lossless_def map_scale_spmf)

lemma spmf_mk_lossless [simp]: "spmf (mk_lossless p) x = spmf p x / weight_spmf p"
  by(simp add: mk_lossless_def spmf_scale_spmf inverse_eq_divide max_def)

lemma set_spmf_mk_lossless [simp]: "set_spmf (mk_lossless p) = set_spmf p"
  by(simp add: mk_lossless_def set_scale_spmf measure_spmf_zero_iff zero_less_measure_iff)

lemma mk_lossless_lossless [simp]: "lossless_spmf p \<Longrightarrow> mk_lossless p = p"
  by(simp add: mk_lossless_def lossless_weight_spmfD)

lemma mk_lossless_eq_return_pmf_None [simp]: "mk_lossless p = return_pmf None \<longleftrightarrow> p = return_pmf None"
proof -
  have aux: "weight_spmf p = 0 \<Longrightarrow> spmf p i = 0" for i
    by(rule antisym, rule order_trans[OF spmf_le_weight]) (auto intro!: order_trans[OF spmf_le_weight])

  have[simp]: " spmf (scale_spmf (inverse (weight_spmf p)) p) = spmf (return_pmf None) \<Longrightarrow> spmf p i = 0" for i
    by(drule fun_cong[where x=i]) (auto simp add: aux spmf_scale_spmf max_def)

  show ?thesis by(auto simp add: mk_lossless_def intro: spmf_eqI)
qed

lemma return_pmf_None_eq_mk_lossless [simp]: "return_pmf None = mk_lossless p \<longleftrightarrow> p = return_pmf None"
  by(metis mk_lossless_eq_return_pmf_None)

lemma mk_lossless_spmf_of_set [simp]: "mk_lossless (spmf_of_set A) = spmf_of_set A"
  by(simp add: spmf_of_set_def del: spmf_of_pmf_pmf_of_set)

lemma weight_mk_lossless: "weight_spmf (mk_lossless p) = (if p = return_pmf None then 0 else 1)"
  by(simp add: mk_lossless_def weight_scale_spmf min_def max_def inverse_eq_divide weight_spmf_eq_0)

lemma mk_lossless_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_spmf A ===> rel_spmf A) mk_lossless mk_lossless"
  by(simp add: mk_lossless_def rel_fun_def rel_spmf_weightD rel_spmf_scaleI)

lemma rel_spmf_mk_losslessI:
  "rel_spmf A p q \<Longrightarrow> rel_spmf A (mk_lossless p) (mk_lossless q)"
  by(rule mk_lossless_parametric[THEN rel_funD])

lemma rel_spmf_restrict_spmfI:
  "rel_spmf (\<lambda>x y. (x \<in> A \<and> y \<in> B \<and> R x y) \<or> x \<notin> A \<and> y \<notin> B) p q
   \<Longrightarrow> rel_spmf R (restrict_spmf p A) (restrict_spmf q B)"
  by(auto simp add: restrict_spmf_def pmf.rel_map elim!: option.rel_cases pmf.rel_mono_strong)

lemma cond_spmf_alt: "cond_spmf p A = mk_lossless (restrict_spmf p A)"
proof(cases "set_spmf p \<inter> A = {}")
  case True
  then show ?thesis by(simp add: cond_spmf_def measure_spmf_zero_iff)
next
  case False
  show ?thesis
    by(rule spmf_eqI)(simp add: False cond_spmf_def pmf_cond set_pmf_Int_Some image_iff measure_measure_spmf_conv_measure_pmf[symmetric] spmf_scale_spmf max_def inverse_eq_divide)
qed

lemma cond_spmf_bind:
  "cond_spmf (bind_spmf p f) A = mk_lossless (p \<bind> (\<lambda>x. f x \<upharpoonleft> A))"
  by(simp add: cond_spmf_alt restrict_bind_spmf scale_bind_spmf)

lemma cond_spmf_UNIV [simp]: "cond_spmf p UNIV = mk_lossless p"
  by(clarsimp simp add: cond_spmf_alt)

lemma cond_pmf_singleton:
  "cond_pmf p A = return_pmf x" if "set_pmf p \<inter> A = {x}"
proof -
  have[simp]: "set_pmf p \<inter> A = {x} \<Longrightarrow> x \<in> A \<Longrightarrow> measure_pmf.prob p A = pmf p x"
    by(auto simp add: measure_pmf_single[symmetric] AE_measure_pmf_iff intro!: measure_pmf.finite_measure_eq_AE)

  have "pmf (cond_pmf p A) i = pmf (return_pmf x) i" for i
    using that by(auto simp add: pmf_cond measure_pmf_zero_iff pmf_eq_0_set_pmf split: split_indicator)

  then show ?thesis by(rule pmf_eqI)
qed


definition cond_spmf_fst :: "('a \<times> 'b) spmf \<Rightarrow> 'a \<Rightarrow> 'b spmf" where
  "cond_spmf_fst p a = map_spmf snd (cond_spmf p ({a} \<times> UNIV))"

lemma cond_spmf_fst_return_spmf [simp]:
  "cond_spmf_fst (return_spmf (x, y)) x = return_spmf y"
  by(simp add: cond_spmf_fst_def)

lemma cond_spmf_fst_map_Pair [simp]: "cond_spmf_fst (map_spmf (Pair x) p) x = mk_lossless p"
  by(clarsimp simp add: cond_spmf_fst_def spmf.map_comp o_def)

lemma cond_spmf_fst_map_Pair' [simp]: "cond_spmf_fst (map_spmf (\<lambda>y. (x, f y)) p) x = map_spmf f (mk_lossless p)"
  by(subst spmf.map_comp[where f="Pair x", symmetric, unfolded o_def]) simp

lemma cond_spmf_fst_eq_return_None [simp]: "cond_spmf_fst p x = return_pmf None \<longleftrightarrow> x \<notin> fst ` set_spmf p"
  by(auto 4 4 simp add: cond_spmf_fst_def map_pmf_eq_return_pmf_iff in_set_spmf[symmetric] dest: bspec[where x="Some _"] intro: ccontr rev_image_eqI)

lemma cond_spmf_fst_map_Pair1:
  "cond_spmf_fst (map_spmf (\<lambda>x. (f x, g x)) p) (f x) = return_spmf (g (inv_into (set_spmf p) f (f x)))"
  if "x \<in> set_spmf p" "inj_on f (set_spmf p)"
proof -
  let ?foo="\<lambda>y. map_option (\<lambda>x. (f x, g x)) -` Some ` ({f y} \<times> UNIV)"
  have[simp]: "y \<in> set_spmf p \<Longrightarrow> f x = f y \<Longrightarrow> set_pmf p \<inter> (?foo y) \<noteq> {}" for y
    by(auto simp add: vimage_def image_def in_set_spmf)

  have[simp]: "y \<in> set_spmf p \<Longrightarrow> f x = f y \<Longrightarrow>  map_spmf snd (map_spmf (\<lambda>x. (f x, g x)) (cond_pmf p (?foo y))) = return_spmf (g x)" for y
    using that by(subst cond_pmf_singleton[where x="Some x"]) (auto simp add: in_set_spmf elim: inj_onD)

  show ?thesis
    using that
    by(auto simp add: cond_spmf_fst_def cond_spmf_def)
      (erule notE, subst cond_map_pmf, simp_all)
qed

lemma lossless_cond_spmf_fst [simp]: "lossless_spmf (cond_spmf_fst p x) \<longleftrightarrow> x \<in> fst ` set_spmf p"
  by(auto simp add: cond_spmf_fst_def intro: rev_image_eqI)

lemma cond_spmf_fst_inverse:
  "bind_spmf (map_spmf fst p) (\<lambda>x. map_spmf (Pair x) (cond_spmf_fst p x)) = p"
  (is "?lhs = ?rhs")
proof(rule spmf_eqI)
  fix i :: "'a \<times> 'b"
  have *: "({x} \<times> UNIV \<inter> (Pair x \<circ> snd) -` {i}) = (if x = fst i then {i} else {})" for x by(cases i)auto
  have "spmf ?lhs i = LINT x|measure_spmf (map_spmf fst p). spmf (map_spmf (Pair x \<circ> snd) (cond_spmf p ({x} \<times> UNIV))) i"
    by(auto simp add: spmf_bind spmf.map_comp[symmetric] cond_spmf_fst_def intro!: integral_cong_AE)
  also have "\<dots> = LINT x|measure_spmf (map_spmf fst p). measure (measure_spmf (cond_spmf p ({x} \<times> UNIV))) ((Pair x \<circ> snd) -` {i})"
    by(rule integral_cong_AE)(auto simp add: spmf_map)
  also have "\<dots> = LINT x|measure_spmf (map_spmf fst p). measure (measure_spmf p) ({x} \<times> UNIV \<inter> (Pair x \<circ> snd) -` {i}) /
       measure (measure_spmf p) ({x} \<times> UNIV)"
    by(rule integral_cong_AE; clarsimp simp add: measure_cond_spmf)
  also have "\<dots> = spmf (map_spmf fst p) (fst i) * spmf p i / measure (measure_spmf p) ({fst i} \<times> UNIV)"
    by(simp add: * if_distrib[where f="measure (measure_spmf _)"] cong: if_cong)
      (subst integral_measure_spmf[where A="{fst i}"]; auto split: if_split_asm simp add: spmf_conv_measure_spmf)
  also have "\<dots> = spmf p i"
    by(clarsimp simp add: spmf_map vimage_fst)(metis (no_types, lifting) Int_insert_left_if1 in_set_spmf_iff_spmf insertI1 insert_UNIV insert_absorb insert_not_empty measure_spmf_zero_iff mem_Sigma_iff prod.collapse)
  finally show "spmf ?lhs i = spmf ?rhs i" .
qed

(* Generat *)

fun rel_witness_generat :: "('a, 'c, 'e) generat \<times> ('b, 'd, 'f) generat \<Rightarrow> ('a \<times> 'b, 'c \<times> 'd, 'e \<times> 'f) generat" where
  "rel_witness_generat (Pure x, Pure y) = Pure (x, y)"
| "rel_witness_generat (IO out c, IO out' c') = IO (out, out') (c, c')"

lemma rel_witness_generat: 
  assumes "rel_generat A C R x y"
  shows pures_rel_witness_generat: "generat_pures (rel_witness_generat (x, y)) \<subseteq> {(a, b). A a b}"
    and outs_rel_witness_generat: "generat_outs (rel_witness_generat (x, y)) \<subseteq> {(c, d). C c d}"
    and conts_rel_witness_generat: "generat_conts (rel_witness_generat (x, y)) \<subseteq> {(e, f). R e f}"
    and map1_rel_witness_generat: "map_generat fst fst fst (rel_witness_generat (x, y)) = x"
    and map2_rel_witness_generat: "map_generat snd snd snd (rel_witness_generat (x, y)) = y"
  using assms by(cases; simp; fail)+

lemmas set_rel_witness_generat = pures_rel_witness_generat outs_rel_witness_generat conts_rel_witness_generat

lemma rel_witness_generat1:
  assumes "rel_generat A C R x y"
  shows "rel_generat (\<lambda>a (a', b). a = a' \<and> A a' b) (\<lambda>c (c', d). c = c' \<and> C c' d) (\<lambda>r (r', s). r = r' \<and> R r' s) x (rel_witness_generat (x, y))"
  using map1_rel_witness_generat[OF assms, symmetric]
  unfolding generat.rel_eq[symmetric] generat.rel_map
  by(rule generat.rel_mono_strong)(auto dest: set_rel_witness_generat[OF assms, THEN subsetD])

lemma rel_witness_generat2:
  assumes "rel_generat A C R x y"
  shows "rel_generat (\<lambda>(a, b') b. b = b' \<and> A a b') (\<lambda>(c, d') d. d = d' \<and> C c d') (\<lambda>(r, s') s. s = s' \<and> R r s') (rel_witness_generat (x, y)) y"
  using map2_rel_witness_generat[OF assms]
  unfolding generat.rel_eq[symmetric] generat.rel_map
  by(rule generat.rel_mono_strong)(auto dest: set_rel_witness_generat[OF assms, THEN subsetD])


(* Generative_Probabilistic_Value *)

lemma rel_gpv''_map_gpv1:
  "rel_gpv'' A C R (map_gpv f g gpv) gpv' = rel_gpv'' (\<lambda>a. A (f a)) (\<lambda>c. C (g c)) R gpv gpv'" (is "?lhs = ?rhs")
proof
  show ?rhs if ?lhs using that
    apply(coinduction arbitrary: gpv gpv')
    apply(drule rel_gpv''D)
    apply(simp add: gpv.map_sel spmf_rel_map)
    apply(erule rel_spmf_mono)
    by(auto simp add: generat.rel_map rel_fun_comp elim!: generat.rel_mono_strong rel_fun_mono)
  show ?lhs if ?rhs using that
    apply(coinduction arbitrary: gpv gpv')
    apply(drule rel_gpv''D)
    apply(simp add: gpv.map_sel spmf_rel_map)
    apply(erule rel_spmf_mono)
    by(auto simp add: generat.rel_map rel_fun_comp elim!: generat.rel_mono_strong rel_fun_mono)
qed

lemma rel_gpv''_map_gpv2:
  "rel_gpv'' A C R gpv (map_gpv f g gpv') = rel_gpv'' (\<lambda>a b. A a (f b)) (\<lambda>c d. C c (g d)) R gpv gpv'"
  using rel_gpv''_map_gpv1[of "conversep A" "conversep C" "conversep R" f g gpv' gpv]
  apply(rewrite in "\<hole> = _" conversep_iff[symmetric])
  apply(rewrite in "_ = \<hole>" conversep_iff[symmetric])
  apply(simp only: rel_gpv''_conversep)
  apply(simp only: rel_gpv''_conversep[symmetric])
  apply(simp only: conversep_iff[abs_def])
  done

lemmas rel_gpv''_map_gpv = rel_gpv''_map_gpv1[abs_def] rel_gpv''_map_gpv2

lemma rel_gpv''_map_gpv' [simp]:
  shows "\<And>f g h gpv. NO_MATCH id f \<or> NO_MATCH id g 
    \<Longrightarrow> rel_gpv'' A C R (map_gpv' f g h gpv) = rel_gpv'' (\<lambda>a. A (f a)) (\<lambda>c. C (g c)) R (map_gpv' id id h gpv)"
    and "\<And>f g h gpv gpv'. NO_MATCH id f \<or> NO_MATCH id g 
    \<Longrightarrow> rel_gpv'' A C R gpv (map_gpv' f g h gpv') = rel_gpv'' (\<lambda>a b. A a (f b)) (\<lambda>c d. C c (g d)) R gpv (map_gpv' id id h gpv')"
proof (goal_cases)
  case (1 f g h gpv)
  then show ?case using map_gpv'_comp[of f g id id id h gpv, symmetric] by(simp add: rel_gpv''_map_gpv[unfolded map_gpv_conv_map_gpv'])
next
  case (2 f g h gpv gpv')
  then show ?case using map_gpv'_comp[of f g id id id h gpv', symmetric] by(simp add: rel_gpv''_map_gpv[unfolded map_gpv_conv_map_gpv'])
qed

lemmas rel_gpv_map_gpv' = rel_gpv''_map_gpv'[where R="(=)", folded rel_gpv_conv_rel_gpv'']

definition rel_witness_gpv :: "('a \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> ('g \<Rightarrow> 'f \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c) gpv \<times> ('d, 'e, 'f) gpv \<Rightarrow> ('a \<times> 'd, 'b \<times> 'e, 'g) gpv" where
  "rel_witness_gpv A C R R' = corec_gpv (
     map_spmf (map_generat id id (\<lambda>(rpv, rpv'). (Inr \<circ> rel_witness_fun R R' (rpv, rpv'))) \<circ> rel_witness_generat) \<circ>
     rel_witness_spmf (rel_generat A C (rel_fun (R OO R') (rel_gpv'' A C (R OO R')))) \<circ> map_prod the_gpv the_gpv)"

lemma rel_witness_gpv_sel [simp]:
  "the_gpv (rel_witness_gpv A C R R' (gpv, gpv')) = 
    map_spmf (map_generat id id (\<lambda>(rpv, rpv'). (rel_witness_gpv A C R R' \<circ> rel_witness_fun R R' (rpv, rpv'))) \<circ> rel_witness_generat)
     (rel_witness_spmf (rel_generat A C (rel_fun (R OO R') (rel_gpv'' A C (R OO R')))) (the_gpv gpv, the_gpv gpv'))"
  unfolding rel_witness_gpv_def
  by(auto simp add: spmf.map_comp generat.map_comp o_def intro!: map_spmf_cong generat.map_cong)

lemma assumes "rel_gpv'' A C (R OO R') gpv gpv'"
  and R: "left_unique R" "right_total R"
  and R': "right_unique R'" "left_total R'"
shows rel_witness_gpv1: "rel_gpv'' (\<lambda>a (a', b). a = a' \<and> A a' b) (\<lambda>c (c', d). c = c' \<and> C c' d) R gpv (rel_witness_gpv A C R R' (gpv, gpv'))" (is "?thesis1")
  and rel_witness_gpv2: "rel_gpv'' (\<lambda>(a, b') b. b = b' \<and> A a b') (\<lambda>(c, d') d. d = d' \<and> C c d') R' (rel_witness_gpv A C R R' (gpv, gpv')) gpv'" (is "?thesis2")
proof -
  show ?thesis1 using assms(1)
  proof(coinduction arbitrary: gpv gpv')
    case rel_gpv''
    from this[THEN rel_gpv''D] show ?case
      by(auto simp add: spmf_rel_map generat.rel_map rel_fun_comp elim!: rel_fun_mono[OF rel_witness_fun1[OF _ R R']]
          rel_spmf_mono[OF rel_witness_spmf1] generat.rel_mono[THEN predicate2D, rotated -1, OF rel_witness_generat1])
  qed
  show ?thesis2 using assms(1)
  proof(coinduction arbitrary: gpv gpv')
    case rel_gpv''
    from this[THEN rel_gpv''D] show ?case
      by(simp add: spmf_rel_map) 
        (erule rel_spmf_mono[OF rel_witness_spmf2]
          , auto simp add: generat.rel_map rel_fun_comp elim!: rel_fun_mono[OF rel_witness_fun2[OF _ R R']]
          generat.rel_mono[THEN predicate2D, rotated -1, OF rel_witness_generat2])
  qed
qed

lemma rel_gpv''_neg_distr:
  assumes R: "left_unique R" "right_total R"
    and R': "right_unique R'" "left_total R'"
  shows "rel_gpv'' (A OO A') (C OO C') (R OO R') \<le> rel_gpv'' A C R OO rel_gpv'' A' C' R'"
proof(rule predicate2I relcomppI)+
  fix gpv gpv''
  assume *: "rel_gpv'' (A OO A') (C OO C') (R OO R') gpv gpv''"
  let ?gpv' = "map_gpv (relcompp_witness A A') (relcompp_witness C C') (rel_witness_gpv (A OO A') (C OO C') R R' (gpv, gpv''))"
  show "rel_gpv'' A C R gpv ?gpv'" using rel_witness_gpv1[OF * R R'] unfolding rel_gpv''_map_gpv
    by(rule rel_gpv''_mono[THEN predicate2D, rotated -1]; clarify del: relcomppE elim!: relcompp_witness)
  show "rel_gpv'' A' C' R' ?gpv' gpv''" using rel_witness_gpv2[OF * R R'] unfolding rel_gpv''_map_gpv
    by(rule rel_gpv''_mono[THEN predicate2D, rotated -1]; clarify del: relcomppE elim!: relcompp_witness)
qed

lemma rel_gpv''_mono' [mono]:
  assumes "\<And>x y. A x y \<longrightarrow> A' x y"
    and "\<And>x y. C x y \<longrightarrow> C' x y"
    and "\<And>x y. R' x y \<longrightarrow> R x y"
  shows "rel_gpv'' A C R gpv gpv' \<longrightarrow> rel_gpv'' A' C' R' gpv gpv'"
  using rel_gpv''_mono[of A A' C C' R' R] assms by(blast)

context includes \<I>.lifting begin

lift_definition \<I>_uniform :: "'out set \<Rightarrow> 'in set \<Rightarrow> ('out, 'in) \<I>" is "\<lambda>A B x. if x \<in> A then B else {}" .

lemma outs_\<I>_uniform [simp]: "outs_\<I> (\<I>_uniform A B) = (if B = {} then {} else A)"
  by transfer simp

lemma responses_\<I>_uniform [simp]: "responses_\<I> (\<I>_uniform A B) x = (if x \<in> A then B else {})"
  by transfer simp

lemma \<I>_uniform_UNIV [simp]: "\<I>_uniform UNIV UNIV = \<I>_full" (* TODO: make \<I>_full an abbreviation *)
  by transfer simp

lifting_update \<I>.lifting
lifting_forget \<I>.lifting

end 

lemma \<I>_eqI: "\<lbrakk> outs_\<I> \<I> = outs_\<I> \<I>'; \<And>x. x \<in> outs_\<I> \<I>' \<Longrightarrow> responses_\<I> \<I> x = responses_\<I> \<I>' x \<rbrakk> \<Longrightarrow> \<I> = \<I>'"
  including \<I>.lifting by transfer auto

instantiation \<I> :: (type, type) order begin

definition less_eq_\<I> :: "('a, 'b) \<I> \<Rightarrow> ('a, 'b) \<I> \<Rightarrow> bool"
  where le_\<I>_def: "less_eq_\<I> \<I> \<I>' \<longleftrightarrow> outs_\<I> \<I> \<subseteq> outs_\<I> \<I>' \<and> (\<forall>x\<in>outs_\<I> \<I>. responses_\<I> \<I>' x \<subseteq> responses_\<I> \<I> x)"

definition less_\<I> :: "('a, 'b) \<I> \<Rightarrow> ('a, 'b) \<I> \<Rightarrow> bool"
  where "less_\<I> = mk_less (\<le>)"

instance
proof
  show "\<I> < \<I>' \<longleftrightarrow> \<I> \<le> \<I>' \<and> \<not> \<I>' \<le> \<I>" for \<I> \<I>' :: "('a, 'b) \<I>" by(simp add: less_\<I>_def mk_less_def)
  show "\<I> \<le> \<I>" for \<I> :: "('a, 'b) \<I>" by(simp add: le_\<I>_def)
  show "\<I> \<le> \<I>''" if "\<I> \<le> \<I>'" "\<I>' \<le> \<I>''" for \<I> \<I>' \<I>'' :: "('a, 'b) \<I>" using that
    by(fastforce simp add: le_\<I>_def)
  show "\<I> = \<I>'" if "\<I> \<le> \<I>'" "\<I>' \<le> \<I>" for \<I> \<I>' :: "('a, 'b) \<I>" using that
    by(auto simp add: le_\<I>_def intro!: \<I>_eqI)
qed
end

instantiation \<I> :: (type, type) order_bot begin
definition bot_\<I> :: "('a, 'b) \<I>" where "bot_\<I> = \<I>_uniform {} UNIV"
instance by standard(auto simp add: bot_\<I>_def le_\<I>_def)
end

lemma outs_\<I>_bot [simp]: "outs_\<I> bot = {}"
  by(simp add: bot_\<I>_def)

lemma respones_\<I>_bot [simp]: "responses_\<I> bot x = {}"
  by(simp add: bot_\<I>_def)

lemma outs_\<I>_mono: "\<I> \<le> \<I>' \<Longrightarrow> outs_\<I> \<I> \<subseteq> outs_\<I> \<I>'"
  by(simp add: le_\<I>_def)

lemma responses_\<I>_mono: "\<lbrakk> \<I> \<le> \<I>'; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> responses_\<I> \<I>' x \<subseteq> responses_\<I> \<I> x"
  by(simp add: le_\<I>_def)

lemma \<I>_uniform_empty [simp]: "\<I>_uniform {} A = bot" 
  unfolding bot_\<I>_def including \<I>.lifting by transfer simp

lemma WT_gpv_\<I>_mono: "\<lbrakk> \<I> \<turnstile>g gpv \<surd>; \<I> \<le> \<I>' \<rbrakk> \<Longrightarrow> \<I>' \<turnstile>g gpv \<surd>"
  by(erule WT_gpv_mono; rule outs_\<I>_mono responses_\<I>_mono)

lemma results_gpv_mono:
  assumes le: "\<I>' \<le> \<I>" and WT: "\<I>' \<turnstile>g gpv \<surd>"
  shows "results_gpv \<I> gpv \<subseteq> results_gpv \<I>' gpv"
proof(rule subsetI, goal_cases)
  case (1 x)
  show ?case using 1 WT by(induction)(auto 4 3 intro: results_gpv.intros responses_\<I>_mono[OF le, THEN subsetD] intro: WT_gpvD)
qed

lemma \<I>_uniform_mono:
  "\<I>_uniform A B \<le> \<I>_uniform C D" if "A \<subseteq> C" "D \<subseteq> B" "D = {} \<longrightarrow> B = {}"
  unfolding le_\<I>_def using that by auto

context begin
qualified inductive outsp_gpv :: "('out, 'in) \<I> \<Rightarrow> 'out \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
  for \<I> x where
    IO: "IO x c \<in> set_spmf (the_gpv gpv) \<Longrightarrow> outsp_gpv \<I> x gpv"
  | Cont: "\<lbrakk> IO out rpv \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out; outsp_gpv \<I> x (rpv input) \<rbrakk>
  \<Longrightarrow> outsp_gpv \<I> x gpv"

definition outs_gpv :: "('out, 'in) \<I> \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> 'out set"
  where "outs_gpv \<I> gpv \<equiv> {x. outsp_gpv \<I> x gpv}"

lemma outsp_gpv_outs_gpv_eq [pred_set_conv]: "outsp_gpv \<I> x = (\<lambda>gpv. x \<in> outs_gpv \<I> gpv)"
  by(simp add: outs_gpv_def)

context begin
local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "outs_gpv")\<close>

lemmas intros [intro?] = outsp_gpv.intros[to_set]
  and IO = IO[to_set]
  and Cont = Cont[to_set]
  and induct [consumes 1, case_names IO Cont, induct set: outs_gpv] = outsp_gpv.induct[to_set]
  and cases [consumes 1, case_names IO Cont, cases set: outs_gpv] = outsp_gpv.cases[to_set]
  and simps = outsp_gpv.simps[to_set]
end

inductive_simps outs_gpv_GPV [to_set, simp]: "outsp_gpv \<I> x (GPV gpv)"

end

lemma outs_gpv_Done [iff]: "outs_gpv \<I> (Done x) = {}"
  by(auto simp add: Done.ctr)

lemma outs_gpv_Fail [iff]: "outs_gpv \<I> Fail = {}"
  by(auto simp add: Fail_def)

lemma outs_gpv_Pause [simp]:
  "outs_gpv \<I> (Pause out c) = insert out (\<Union>input\<in>responses_\<I> \<I> out. outs_gpv \<I> (c input))"
  by(auto simp add: Pause.ctr)

lemma outs_gpv_lift_spmf [iff]: "outs_gpv \<I> (lift_spmf p) = {}"
  by(auto simp add: lift_spmf.ctr)

lemma outs_gpv_assert_gpv [simp]: "outs_gpv \<I> (assert_gpv b) = {}"
  by(cases b)auto

lemma outs_gpv_bind_gpv [simp]:
  "outs_gpv \<I> (gpv \<bind> f) = outs_gpv \<I> gpv \<union> (\<Union>x\<in>results_gpv \<I> gpv. outs_gpv \<I> (f x))"
  (is "?lhs = ?rhs")
proof(intro Set.set_eqI iffI)
  fix x
  assume "x \<in> ?lhs"
  then show "x \<in> ?rhs"
  proof(induction gpv'\<equiv>"gpv \<bind> f" arbitrary: gpv)
    case IO thus ?case
    proof(clarsimp split: if_split_asm elim!: is_PureE not_is_PureE, goal_cases)
      case (1 generat)
      then show ?case by(cases generat)(auto intro: results_gpv.Pure outs_gpv.intros)
    qed
  next
    case (Cont out rpv input)
    thus ?case
    proof(clarsimp split: if_split_asm, goal_cases)
      case (1 generat)
      then show ?case by(cases generat)(auto 4 3 split: if_split_asm intro: results_gpv.intros outs_gpv.intros)
    qed
  qed
next
  fix x
  assume "x \<in> ?rhs"
  then consider (out) "x \<in> outs_gpv \<I> gpv" | (result) y where "y \<in> results_gpv \<I> gpv" "x \<in> outs_gpv \<I> (f y)" by auto
  then show "x \<in> ?lhs"
  proof cases
    case out then show ?thesis
      by(induction) (auto 4 4 intro: outs_gpv.IO  outs_gpv.Cont rev_bexI) 
  next
    case result then show ?thesis
      by induction ((erule outs_gpv.cases | rule outs_gpv.Cont), 
          auto 4 4 intro: outs_gpv.intros rev_bexI elim: outs_gpv.cases)+
  qed
qed

lemma outs_gpv_\<I>_full: "outs_gpv \<I>_full = outs'_gpv"
proof(intro ext Set.set_eqI iffI)
  show "x \<in> outs'_gpv gpv" if "x \<in> outs_gpv \<I>_full gpv" for x gpv
    using that by induction(auto intro: outs'_gpvI)
  show "x \<in> outs_gpv \<I>_full gpv" if "x \<in> outs'_gpv gpv" for x gpv
    using that by induction(auto intro: outs_gpv.intros elim!: generat.set_cases)
qed

lemma outs'_bind_gpv [simp]:
  "outs'_gpv (bind_gpv gpv f) = outs'_gpv gpv \<union> (\<Union>x\<in>results'_gpv gpv. outs'_gpv (f x))"
  unfolding outs_gpv_\<I>_full[symmetric] results_gpv_\<I>_full[symmetric] by simp

lemma outs_gpv_map_gpv_id [simp]: "outs_gpv \<I> (map_gpv f id gpv) = outs_gpv \<I> gpv"
  by(auto simp add: map_gpv_conv_bind id_def)

lemma outs_gpv_map_gpv_id' [simp]: "outs_gpv \<I> (map_gpv f (\<lambda>x. x) gpv) = outs_gpv \<I> gpv"
  by(auto simp add: map_gpv_conv_bind id_def)

lemma outs'_gpv_bind_option [simp]:
  "outs'_gpv (monad.bind_option Fail x f) = (\<Union>y\<in>set_option x. outs'_gpv (f y))"
  by(cases x) simp_all

lemma WT_gpv_outs_gpv:
  assumes "\<I> \<turnstile>g gpv \<surd>"
  shows "outs_gpv \<I> gpv \<subseteq> outs_\<I> \<I>"
proof
  show "x \<in> outs_\<I> \<I>" if "x \<in> outs_gpv \<I> gpv" for x using that assms
    by(induction)(blast intro: WT_gpv_OutD WT_gpv_ContD)+
qed

context includes \<I>.lifting begin

lift_definition map_\<I> :: "('out' \<Rightarrow> 'out) \<Rightarrow> ('in \<Rightarrow> 'in') \<Rightarrow> ('out, 'in) \<I> \<Rightarrow> ('out', 'in') \<I>"
  is "\<lambda>f g resp x. g ` resp (f x)" .

lemma outs_\<I>_map_\<I> [simp]:
  "outs_\<I> (map_\<I> f g \<I>) = f -` outs_\<I> \<I>"
  by transfer simp

lemma responses_\<I>_map_\<I> [simp]:
  "responses_\<I> (map_\<I> f g \<I>) x = g ` responses_\<I> \<I> (f x)"
  by transfer simp

lemma map_\<I>_\<I>_uniform [simp]:
  "map_\<I> f g (\<I>_uniform A B) = \<I>_uniform (f -` A) (g ` B)"
  by transfer(auto simp add: fun_eq_iff)

lemma map_\<I>_id [simp]: "map_\<I> id id \<I> = \<I>"
  by transfer simp

lemma map_\<I>_id0: "map_\<I> id id = id"
  by(simp add: fun_eq_iff)

lemma map_\<I>_comp [simp]: "map_\<I> f g (map_\<I> f' g' \<I>) = map_\<I> (f' \<circ> f) (g \<circ> g') \<I>"
  by transfer auto

lemma map_\<I>_cong: "map_\<I> f g \<I> = map_\<I> f' g' \<I>'"
  if "\<I> = \<I>'" and f: "f = f'" and "\<And>x y. \<lbrakk> x \<in> outs_\<I> \<I>'; y \<in> responses_\<I> \<I>' x \<rbrakk> \<Longrightarrow> g y = g' y"
  unfolding that(1,2) using that(3-)
  by transfer(auto simp add: fun_eq_iff intro!: image_cong)

lifting_update \<I>.lifting
lifting_forget \<I>.lifting
end

functor map_\<I> by(simp_all add: fun_eq_iff)

lemma WT_gpv_map_gpv': "\<I> \<turnstile>g map_gpv' f g h gpv \<surd>" if "map_\<I> g h \<I> \<turnstile>g gpv \<surd>"
  using that by(coinduction arbitrary: gpv)(auto 4 4 dest: WT_gpvD)

lemma WT_gpv_map_gpv: "\<I> \<turnstile>g map_gpv f g gpv \<surd>" if "map_\<I> g id \<I> \<turnstile>g gpv \<surd>"
  unfolding map_gpv_conv_map_gpv' using that by(rule WT_gpv_map_gpv')

lemma results_gpv_map_gpv' [simp]:
  "results_gpv \<I> (map_gpv' f g h gpv) = f ` (results_gpv (map_\<I> g h \<I>) gpv)"
proof(intro Set.set_eqI iffI; (elim imageE; hypsubst)?)
  show "x \<in> f ` results_gpv (map_\<I> g h \<I>) gpv" if "x \<in> results_gpv \<I> (map_gpv' f g h gpv)" for x using that
    by(induction gpv'\<equiv>"map_gpv' f g h gpv" arbitrary: gpv)(fastforce intro: results_gpv.intros rev_image_eqI)+
  show "f x \<in> results_gpv \<I> (map_gpv' f g h gpv)" if "x \<in> results_gpv (map_\<I> g h \<I>) gpv" for x using that
    by(induction)(fastforce intro: results_gpv.intros)+
qed

lemma map_\<I>_plus_\<I> [simp]: 
  "map_\<I> (map_sum f1 f2) (map_sum g1 g2) (\<I>1 \<oplus>\<^sub>\<I> \<I>2) = map_\<I> f1 g1 \<I>1 \<oplus>\<^sub>\<I> map_\<I> f2 g2 \<I>2"
proof(rule \<I>_eqI[OF Set.set_eqI], goal_cases)
  case (1 x)
  then show ?case by(cases x) auto
qed (auto simp add: image_image)

lemma le_plus_\<I>_iff [simp]:
  "\<I>1 \<oplus>\<^sub>\<I> \<I>2 \<le> \<I>1' \<oplus>\<^sub>\<I> \<I>2' \<longleftrightarrow> \<I>1 \<le> \<I>1' \<and> \<I>2 \<le> \<I>2'"
  by(auto 4 4 simp add: le_\<I>_def dest: bspec[where x="Inl _"] bspec[where x="Inr _"])



inductive pred_gpv' :: "('a \<Rightarrow> bool) \<Rightarrow> ('out \<Rightarrow> bool) \<Rightarrow> 'in set \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool" for P Q X gpv where
  "pred_gpv' P Q X gpv" 
if "\<And>x. x \<in> results_gpv (\<I>_uniform UNIV X) gpv \<Longrightarrow> P x" "\<And>out. out \<in> outs_gpv (\<I>_uniform UNIV X) gpv \<Longrightarrow> Q out"

lemma pred_gpv_conv_pred_gpv': "pred_gpv P Q = pred_gpv' P Q UNIV"
  by(auto simp add: fun_eq_iff pred_gpv_def pred_gpv'.simps results_gpv_\<I>_full outs_gpv_\<I>_full)

lemma rel_gpv''_Grp: includes lifting_syntax shows
  "rel_gpv'' (BNF_Def.Grp A f) (BNF_Def.Grp B g) (BNF_Def.Grp UNIV h)\<inverse>\<inverse> = 
   BNF_Def.Grp {x. results_gpv (\<I>_uniform UNIV (range h)) x \<subseteq> A \<and> outs_gpv (\<I>_uniform UNIV (range h)) x \<subseteq> B} (map_gpv' f g h)"
  (is "?lhs = ?rhs")
proof(intro ext GrpI iffI CollectI conjI subsetI)
  let ?\<I> = "\<I>_uniform UNIV (range h)"
  fix gpv gpv'
  assume *: "?lhs gpv gpv'"
  then show "map_gpv' f g h gpv = gpv'"
    by(coinduction arbitrary: gpv gpv')
      (drule rel_gpv''D
        , auto 4 5 simp add: spmf_rel_map generat.rel_map elim!: rel_spmf_mono generat.rel_mono_strong GrpE intro!: GrpI dest: rel_funD)
  show "x \<in> A" if "x \<in> results_gpv ?\<I> gpv" for x using that *
  proof(induction arbitrary: gpv')
    case (Pure gpv)
    have "pred_spmf (Domainp (rel_generat (BNF_Def.Grp A f) (BNF_Def.Grp B g) ((BNF_Def.Grp UNIV h)\<inverse>\<inverse> ===> rel_gpv'' (BNF_Def.Grp A f) (BNF_Def.Grp B g) (BNF_Def.Grp UNIV h)\<inverse>\<inverse>))) (the_gpv gpv)"
      using Pure.prems[THEN rel_gpv''D] unfolding spmf_Domainp_rel[symmetric] by(rule DomainPI)
    with Pure.hyps show ?case by(simp add: generat.Domainp_rel pred_spmf_def pred_generat_def Domainp_Grp)
  next
    case (IO out c gpv input)
    have "pred_spmf (Domainp (rel_generat (BNF_Def.Grp A f) (BNF_Def.Grp B g) ((BNF_Def.Grp UNIV h)\<inverse>\<inverse> ===> rel_gpv'' (BNF_Def.Grp A f) (BNF_Def.Grp B g) (BNF_Def.Grp UNIV h)\<inverse>\<inverse>))) (the_gpv gpv)"
      using IO.prems[THEN rel_gpv''D] unfolding spmf_Domainp_rel[symmetric] by(rule DomainPI)
    with IO.hyps show ?case 
      by(auto simp add: generat.Domainp_rel pred_spmf_def pred_generat_def Grp_iff dest: rel_funD intro: IO.IH dest!: bspec)
  qed
  show "x \<in> B" if "x \<in> outs_gpv ?\<I> gpv" for x using that *
  proof(induction arbitrary: gpv')
    case (IO c gpv)
    have "pred_spmf (Domainp (rel_generat (BNF_Def.Grp A f) (BNF_Def.Grp B g) ((BNF_Def.Grp UNIV h)\<inverse>\<inverse> ===> rel_gpv'' (BNF_Def.Grp A f) (BNF_Def.Grp B g) (BNF_Def.Grp UNIV h)\<inverse>\<inverse>))) (the_gpv gpv)"
      using IO.prems[THEN rel_gpv''D] unfolding spmf_Domainp_rel[symmetric] by(rule DomainPI)
    with IO.hyps show ?case by(simp add: generat.Domainp_rel pred_spmf_def pred_generat_def Domainp_Grp)
  next
    case (Cont out rpv gpv input)
    have "pred_spmf (Domainp (rel_generat (BNF_Def.Grp A f) (BNF_Def.Grp B g) ((BNF_Def.Grp UNIV h)\<inverse>\<inverse> ===> rel_gpv'' (BNF_Def.Grp A f) (BNF_Def.Grp B g) (BNF_Def.Grp UNIV h)\<inverse>\<inverse>))) (the_gpv gpv)"
      using Cont.prems[THEN rel_gpv''D] unfolding spmf_Domainp_rel[symmetric] by(rule DomainPI)
    with Cont.hyps show ?case 
      by(auto simp add: generat.Domainp_rel pred_spmf_def pred_generat_def Grp_iff dest: rel_funD intro: Cont.IH dest!: bspec)
  qed
next
  fix gpv gpv'
  assume "?rhs gpv gpv'"
  then have gpv': "gpv' = map_gpv' f g h gpv"
    and *: "results_gpv (\<I>_uniform UNIV (range h)) gpv \<subseteq> A" "outs_gpv (\<I>_uniform UNIV (range h)) gpv \<subseteq> B" by(auto simp add: Grp_iff)
  show "?lhs gpv gpv'" using * unfolding gpv'
    by(coinduction arbitrary: gpv)
      (fastforce simp add: spmf_rel_map generat.rel_map Grp_iff intro!: rel_spmf_reflI generat.rel_refl_strong rel_funI elim!: generat.set_cases intro: results_gpv.intros outs_gpv.intros)
qed

lemma rel_gpv''_map_gpv'1:
  "rel_gpv'' A C (BNF_Def.Grp UNIV h)\<inverse>\<inverse> gpv gpv' \<Longrightarrow> rel_gpv'' A C (=) (map_gpv' id id h gpv) gpv'"
  apply(coinduction arbitrary: gpv gpv')
  apply(drule rel_gpv''D)
  apply(simp add: spmf_rel_map)
  apply(erule rel_spmf_mono)
  apply(simp add: generat.rel_map)
  apply(erule generat.rel_mono_strong; simp?)
  apply(subst map_fun2_id)
  by(auto simp add: rel_fun_comp intro!: rel_fun_map_fun1 elim: rel_fun_mono)

lemma rel_gpv''_map_gpv'2:
  "rel_gpv'' A C (eq_on (range h)) gpv gpv' \<Longrightarrow> rel_gpv'' A C (BNF_Def.Grp UNIV h)\<inverse>\<inverse> gpv (map_gpv' id id h gpv')"
  apply(coinduction arbitrary: gpv gpv')
  apply(drule rel_gpv''D)
  apply(simp add: spmf_rel_map)
  apply(erule rel_spmf_mono_strong)
  apply(simp add: generat.rel_map)
  apply(erule generat.rel_mono_strong; simp?)
  apply(subst map_fun_id2_in)
  apply(rule rel_fun_map_fun2)
  by (auto simp add: rel_fun_comp  elim: rel_fun_mono)

context
  fixes A :: "'a \<Rightarrow> 'd \<Rightarrow> bool"
    and C :: "'c \<Rightarrow> 'g \<Rightarrow> bool"
    and R :: "'b \<Rightarrow> 'e \<Rightarrow> bool"
begin

private lemma f11:" Pure x \<in> set_spmf (the_gpv gpv) \<Longrightarrow>
   Domainp (rel_generat A C (rel_fun R (rel_gpv'' A C R))) (Pure x) \<Longrightarrow> Domainp A x"
  by (auto simp add: pred_generat_def elim:bspec dest: generat.Domainp_rel[THEN fun_cong, THEN iffD1, OF Domainp_iff[THEN iffD2], OF exI])

private lemma f21: "IO out c \<in> set_spmf (the_gpv gpv) \<Longrightarrow> 
  rel_generat A C (rel_fun R (rel_gpv'' A C R)) (IO out c) ba \<Longrightarrow> Domainp C out"
  by (auto simp add: pred_generat_def elim:bspec dest: generat.Domainp_rel[THEN fun_cong, THEN iffD1, OF Domainp_iff[THEN iffD2], OF exI])

private lemma f12:
  assumes "IO out c \<in> set_spmf (the_gpv gpv)"
    and "input \<in> responses_\<I> (\<I>_uniform UNIV {x. Domainp R x}) out"
    and "x \<in> results_gpv (\<I>_uniform UNIV {x. Domainp R x}) (c input)"
    and "Domainp (rel_gpv'' A C R) gpv"
  shows "Domainp (rel_gpv'' A C R) (c input)"
proof -
  obtain b1 where o1:"rel_gpv'' A C R gpv b1" using assms(4) by clarsimp
  obtain b2 where o2:"rel_generat A C (rel_fun R (rel_gpv'' A C R)) (IO out c) b2"
    using assms(1) o1[THEN rel_gpv''D, THEN spmf_Domainp_rel[THEN fun_cong, THEN iffD1, OF Domainp_iff[THEN iffD2], OF exI]]
    unfolding pred_spmf_def by - (drule (1) bspec, auto)

  have "Ball (generat_conts (IO out c)) (Domainp (rel_fun R (rel_gpv'' A C R)))"
    using o2[THEN generat.Domainp_rel[THEN fun_cong, THEN iffD1, OF Domainp_iff[THEN iffD2], OF exI]]
    unfolding pred_generat_def by simp

  with assms(2) show ?thesis 
    apply -
    apply(drule bspec)
     apply simp
    apply clarify
    apply(drule Domainp_rel_fun_le[THEN predicate1D, OF Domainp_iff[THEN iffD2], OF exI])
    by simp  
qed

private lemma f22:
  assumes "IO out' rpv \<in> set_spmf (the_gpv gpv)"
    and "input \<in> responses_\<I> (\<I>_uniform UNIV {x. Domainp R x}) out'"
    and "out \<in> outs_gpv (\<I>_uniform UNIV {x. Domainp R x}) (rpv input)"
    and "Domainp (rel_gpv'' A C R) gpv"
  shows "Domainp (rel_gpv'' A C R) (rpv input)"
proof -
  obtain b1 where o1:"rel_gpv'' A C R gpv b1" using assms(4) by auto
  obtain b2 where o2:"rel_generat A C (rel_fun R (rel_gpv'' A C R)) (IO out' rpv) b2"
    using assms(1) o1[THEN rel_gpv''D, THEN spmf_Domainp_rel[THEN fun_cong, THEN iffD1, OF Domainp_iff[THEN iffD2], OF exI]]
    unfolding pred_spmf_def by - (drule (1) bspec, auto)

  have "Ball (generat_conts (IO out' rpv)) (Domainp (rel_fun R (rel_gpv'' A C R)))"
    using o2[THEN generat.Domainp_rel[THEN fun_cong, THEN iffD1, OF Domainp_iff[THEN iffD2], OF exI]]
    unfolding pred_generat_def by simp

  with assms(2) show ?thesis 
    apply -
    apply(drule bspec)
     apply simp
    apply clarify
    apply(drule Domainp_rel_fun_le[THEN predicate1D, OF Domainp_iff[THEN iffD2], OF exI])
    by simp 
qed

lemma Domainp_rel_gpv''_le:
  "Domainp (rel_gpv'' A C R) \<le> pred_gpv' (Domainp A) (Domainp C) {x. Domainp R x}"
proof(rule predicate1I pred_gpv'.intros)+

  show "Domainp A x" if "x \<in> results_gpv (\<I>_uniform UNIV {x. Domainp R x}) gpv" "Domainp (rel_gpv'' A C R) gpv" for x gpv using that
  proof(induction)
    case (Pure gpv)
    then show ?case 
      by (clarify) (drule rel_gpv''D
          , auto simp add: f11 pred_spmf_def dest: spmf_Domainp_rel[THEN fun_cong, THEN iffD1, OF Domainp_iff[THEN iffD2], OF exI])
  qed (simp add: f12) 
  show "Domainp C out" if "out \<in> outs_gpv (\<I>_uniform UNIV {x. Domainp R x}) gpv" "Domainp (rel_gpv'' A C R) gpv" for out gpv using that
  proof( induction)
    case (IO c gpv)
    then show ?case
      by (clarify) (drule rel_gpv''D
          , auto simp add: f21 pred_spmf_def dest!: bspec spmf_Domainp_rel[THEN fun_cong, THEN iffD1, OF Domainp_iff[THEN iffD2], OF exI])
  qed (simp add: f22)
qed

end


lemma map_gpv'_id12: "map_gpv' f g h gpv = map_gpv' id id h (map_gpv f g gpv)"
  unfolding map_gpv_conv_map_gpv' map_gpv'_comp by simp

lemma rel_gpv''_refl: "\<lbrakk> (=) \<le> A; (=) \<le> C; R \<le> (=) \<rbrakk> \<Longrightarrow> (=) \<le> rel_gpv'' A C R"
  by(subst rel_gpv''_eq[symmetric])(rule rel_gpv''_mono)


context
  fixes A A' :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
    and C C' :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
    and R R' :: "'e \<Rightarrow> 'f \<Rightarrow> bool"
   
begin

private abbreviation foo where 
  "foo \<equiv> (\<lambda> fx fy gpvx gpvy g1 g2. 
            \<forall>x y. x \<in> fx (\<I>_uniform UNIV (Collect (Domainp R'))) gpvx \<longrightarrow>
                  y \<in> fy (\<I>_uniform UNIV (Collect (Rangep R'))) gpvy \<longrightarrow> g1 x y \<longrightarrow> g2 x y)"

private lemma f1: "foo results_gpv results_gpv gpv gpv' A A' \<Longrightarrow>
       x \<in> set_spmf (the_gpv gpv) \<Longrightarrow> y \<in> set_spmf (the_gpv gpv') \<Longrightarrow>
       a \<in> generat_conts x \<Longrightarrow> b \<in> generat_conts y \<Longrightarrow>  R' a' \<alpha> \<Longrightarrow> R' \<beta> b' \<Longrightarrow> 
    foo results_gpv results_gpv (a a') (b b') A A'"
  by (fastforce elim: generat.set_cases intro: results_gpv.IO)

private lemma f2: "foo outs_gpv outs_gpv gpv gpv' C C' \<Longrightarrow>
       x \<in> set_spmf (the_gpv gpv) \<Longrightarrow> y \<in> set_spmf (the_gpv gpv') \<Longrightarrow>
       a \<in> generat_conts x \<Longrightarrow> b \<in> generat_conts y \<Longrightarrow> R' a' \<alpha> \<Longrightarrow> R' \<beta> b' \<Longrightarrow> 
    foo outs_gpv outs_gpv (a a') (b b') C C'"
  by (fastforce elim: generat.set_cases intro: outs_gpv.Cont)

lemma rel_gpv''_mono_strong:
  "\<lbrakk> rel_gpv'' A C R gpv gpv'; 
     \<And>x y. \<lbrakk> x \<in> results_gpv (\<I>_uniform UNIV {x. Domainp R' x}) gpv; y \<in> results_gpv (\<I>_uniform UNIV {x. Rangep R' x}) gpv'; A x y \<rbrakk> \<Longrightarrow> A' x y;
     \<And>x y. \<lbrakk> x \<in> outs_gpv (\<I>_uniform UNIV {x. Domainp R' x}) gpv; y \<in> outs_gpv (\<I>_uniform UNIV {x. Rangep R' x}) gpv'; C x y \<rbrakk> \<Longrightarrow> C' x y;
     R' \<le> R \<rbrakk>
  \<Longrightarrow> rel_gpv'' A' C' R' gpv gpv'"
  apply(coinduction arbitrary: gpv gpv')
  apply(drule rel_gpv''D)
  apply(erule rel_spmf_mono_strong)
  apply(erule generat.rel_mono_strong)
    apply(erule generat.set_cases)+
    apply(erule allE, rotate_tac -1)
    apply(erule allE)
    apply(erule impE)
     apply(rule results_gpv.Pure)
     apply simp
    apply(erule impE)
     apply(rule results_gpv.Pure)
     apply simp
    apply simp
   apply(erule generat.set_cases)+
   apply(rotate_tac 1)
   apply(erule allE, rotate_tac -1)
   apply(erule allE)
   apply(erule impE)
    apply(rule outs_gpv.IO)
    apply simp
   apply(erule impE)
    apply(rule outs_gpv.IO)
    apply simp
   apply simp
  apply(erule (1) rel_fun_mono_strong)
  by (fastforce simp add: f1[simplified] f2[simplified])

end

lemma rel_gpv''_refl_strong:
  assumes "\<And>x. x \<in> results_gpv (\<I>_uniform UNIV {x. Domainp R x}) gpv \<Longrightarrow> A x x"
    and "\<And>x. x \<in> outs_gpv (\<I>_uniform UNIV {x. Domainp R x}) gpv \<Longrightarrow> C x x"
    and "R \<le> (=)"
  shows "rel_gpv'' A C R gpv gpv"
proof -
  have "rel_gpv'' (=) (=) (=) gpv gpv" unfolding rel_gpv''_eq by simp
  then show ?thesis using _ _ assms(3) by(rule rel_gpv''_mono_strong)(auto intro: assms(1-2))
qed

lemma rel_gpv''_refl_eq_on:
  "\<lbrakk> \<And>x. x \<in> results_gpv (\<I>_uniform UNIV X) gpv \<Longrightarrow> A x x; \<And>out. out \<in> outs_gpv (\<I>_uniform UNIV X) gpv \<Longrightarrow> B out out \<rbrakk>
  \<Longrightarrow> rel_gpv'' A B (eq_on X) gpv gpv"
  by(rule rel_gpv''_refl_strong) (auto elim: eq_onE)

lemma pred_gpv'_mono' [mono]:
  "pred_gpv' A C R gpv \<longrightarrow> pred_gpv' A' C' R gpv"
  if "\<And>x. A x \<longrightarrow> A' x" "\<And>x. C x \<longrightarrow> C' x"
  using that unfolding pred_gpv'.simps
  by auto



primcorec enforce_\<I>_gpv :: "('out, 'in) \<I> \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out, 'in) gpv" where
  "enforce_\<I>_gpv \<I> gpv = GPV 
    (map_spmf (map_generat id id ((\<circ>) (enforce_\<I>_gpv \<I>))) 
     (map_spmf (\<lambda>generat. case generat of Pure x \<Rightarrow> Pure x | IO out rpv \<Rightarrow> IO out (\<lambda>input. if input \<in> responses_\<I> \<I> out then rpv input else Fail))
        (enforce_spmf (pred_generat \<top> (\<lambda>x. x \<in> outs_\<I> \<I>) \<top>) (the_gpv gpv))))"

lemma enforce_\<I>_gpv_Done [simp]: "enforce_\<I>_gpv \<I> (Done x) = Done x"
  by(rule gpv.expand) simp

lemma enforce_\<I>_gpv_Fail [simp]: "enforce_\<I>_gpv \<I> Fail = Fail"
  by(rule gpv.expand) simp

lemma enforce_\<I>_gpv_Pause [simp]:
  "enforce_\<I>_gpv \<I> (Pause out rpv) =
   (if out \<in> outs_\<I> \<I> then Pause out (\<lambda>input. if input \<in> responses_\<I> \<I> out then enforce_\<I>_gpv \<I> (rpv input) else Fail) else Fail)"
  by(rule gpv.expand)(simp add: fun_eq_iff)

lemma enforce_\<I>_gpv_lift_spmf [simp]: "enforce_\<I>_gpv \<I> (lift_spmf p) = lift_spmf p"
  by(rule gpv.expand)(simp add: enforce_map_spmf spmf.map_comp o_def)

lemma enforce_\<I>_gpv_bind_gpv [simp]:
  "enforce_\<I>_gpv \<I> (bind_gpv gpv f) = bind_gpv (enforce_\<I>_gpv \<I> gpv) (enforce_\<I>_gpv \<I> \<circ> f)"
  by(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
    (auto 4 3 simp add: bind_gpv.sel spmf_rel_map bind_map_spmf o_def pred_generat_def elim!: generat.set_cases intro!: generat.rel_refl_strong rel_spmf_bind_reflI rel_spmf_reflI rel_funI split!: if_splits generat.split_asm)

lemma enforce_\<I>_gpv_parametric':
  includes lifting_syntax 
  notes [transfer_rule] = corec_gpv_parametric' the_gpv_parametric' Fail_parametric'
  assumes [transfer_rule]: "bi_unique C" "bi_unique R"
  shows "(rel_\<I> C R ===> rel_gpv'' A C R ===> rel_gpv'' A C R) enforce_\<I>_gpv enforce_\<I>_gpv"
  unfolding enforce_\<I>_gpv_def top_fun_def by(transfer_prover)

lemma enforce_\<I>_gpv_parametric [transfer_rule]: includes lifting_syntax shows
  "bi_unique C \<Longrightarrow> (rel_\<I> C (=) ===> rel_gpv A C ===> rel_gpv A C) enforce_\<I>_gpv enforce_\<I>_gpv"
  unfolding rel_gpv_conv_rel_gpv'' by(rule enforce_\<I>_gpv_parametric'[OF _ bi_unique_eq])

lemma WT_enforce_\<I>_gpv [simp]: "\<I> \<turnstile>g enforce_\<I>_gpv \<I> gpv \<surd>"
  by(coinduction arbitrary: gpv)(auto split: generat.split_asm)

lemma WT_gpv_parametric': includes lifting_syntax shows
  "bi_unique C \<Longrightarrow> (rel_\<I> C R ===> rel_gpv'' A C R ===> (=)) WT_gpv WT_gpv"
proof(rule rel_funI iffI)+
  note [transfer_rule] = the_gpv_parametric'
  show *: "\<I> \<turnstile>g gpv \<surd>" if [transfer_rule]: "rel_\<I> C R \<I> \<I>'" "bi_unique C" 
    and *: "\<I>' \<turnstile>g gpv' \<surd>" "rel_gpv'' A C R gpv gpv'" for \<I> \<I>' gpv gpv' A C R
    using *
  proof(coinduction arbitrary: gpv gpv')
    case (WT_gpv out c gpv gpv')
    note [transfer_rule] = WT_gpv(2)
    have "rel_set (rel_generat A C (R ===> rel_gpv'' A C R)) (set_spmf (the_gpv gpv)) (set_spmf (the_gpv gpv'))" 
      by transfer_prover
    from rel_setD1[OF this WT_gpv(3)] obtain out' c'
      where [transfer_rule]: "C out out'" "(R ===> rel_gpv'' A C R) c c'"
        and out': "IO out' c' \<in> set_spmf (the_gpv gpv')"
      by(auto elim: generat.rel_cases)
    have "out \<in> outs_\<I> \<I> \<longleftrightarrow> out' \<in> outs_\<I> \<I>'" by transfer_prover
    with WT_gpvD(1)[OF WT_gpv(1) out'] have ?out by simp
    moreover have ?cont
    proof(standard; goal_cases cont)
      case (cont input)
      have "rel_set R (responses_\<I> \<I> out) (responses_\<I> \<I>' out')" by transfer_prover
      from rel_setD1[OF this cont] obtain input' where [transfer_rule]: "R input input'"
        and input': "input' \<in> responses_\<I> \<I>' out'" by blast
      have "rel_gpv'' A C R (c input) (c' input')" by transfer_prover
      with WT_gpvD(2)[OF WT_gpv(1) out' input'] show ?case by auto
    qed
    ultimately show ?case ..
  qed

  show "\<I>' \<turnstile>g gpv' \<surd>" if "rel_\<I> C R \<I> \<I>'" "bi_unique C" "\<I> \<turnstile>g gpv \<surd>" "rel_gpv'' A C R gpv gpv'" 
    for \<I> \<I>' gpv gpv'
    using *[of "conversep C" "conversep R" \<I>' \<I> gpv "conversep A" gpv'] that
    by(simp add: rel_gpv''_conversep)
qed

lemma WT_gpv_map_gpv_id [simp]: "\<I> \<turnstile>g map_gpv f id gpv \<surd> \<longleftrightarrow> \<I> \<turnstile>g gpv \<surd>"
  using WT_gpv_parametric'[of "BNF_Def.Grp UNIV id" "(=)" "BNF_Def.Grp UNIV f", folded rel_gpv_conv_rel_gpv'']
  unfolding gpv.rel_Grp unfolding eq_alt[symmetric] relator_eq
  by(auto simp add: rel_fun_def Grp_def bi_unique_eq)

locale raw_converter_invariant =
  fixes \<I> :: "('call, 'ret) \<I>"
    and \<I>' :: "('call', 'ret') \<I>"
    and callee :: "'s \<Rightarrow> 'call \<Rightarrow> ('ret \<times> 's, 'call', 'ret') gpv"
    and I :: "'s \<Rightarrow> bool"
  assumes results_callee: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> results_gpv \<I>' (callee s x) \<subseteq> responses_\<I> \<I> x \<times> {s. I s}"
    and WT_callee: "\<And>x s. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> \<I>' \<turnstile>g callee s x \<surd>"
begin

context begin
private lemma aux:
  "set_spmf (inline1 callee gpv s) \<subseteq> {Inr (out, callee', rpv') | out callee' rpv'.
    \<exists>call\<in>outs_\<I> \<I>. \<exists>s. I s \<and> (\<forall>x \<in> responses_\<I> \<I>' out. callee' x \<in> sub_gpvs \<I>' (callee s call))} \<union>
     {Inl (x, s') | x s'. x \<in> results_gpv \<I> gpv \<and> I s'}"
  (is "?concl (inline1 callee) gpv s" is "_ \<subseteq> ?rhs1 \<union> ?rhs2 gpv")
  if "\<I> \<turnstile>g gpv \<surd>" "I s"
  using that
proof(induction arbitrary: gpv s rule: inline1_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step inline1')
  { fix out c
    assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" 
    from step.prems(1) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
    { fix x s'
      assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
      then have "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
      with out step.prems(2) have "x \<in> responses_\<I> \<I> out" "I s'" by(auto dest: results_callee)
      from step.prems(1) IO this(1) have "\<I> \<turnstile>g c x \<surd>" by(rule WT_gpvD)
      hence "?concl inline1' (c x) s'" using \<open>I s'\<close> by(rule step.IH)
      also have "\<dots> \<subseteq> ?rhs1 \<union> ?rhs2 gpv" using \<open>x \<in> _\<close> IO by(auto intro: results_gpv.intros)
      also note calculation
    } moreover {
      fix out' c'
      assume "IO out' c' \<in> set_spmf (the_gpv (callee s out))"
      hence "\<forall>x\<in>responses_\<I> \<I>' out'. c' x \<in> sub_gpvs \<I>' (callee s out)"
        by(auto intro: sub_gpvs.base)
      then have "\<exists>call\<in>outs_\<I> \<I>. \<exists>s. I s \<and> (\<forall>x\<in>responses_\<I> \<I>' out'. c' x \<in> sub_gpvs \<I>' (callee s call))"
        using out step.prems(2) by blast
    } moreover note calculation }
    then show ?case using step.prems
      by(auto 4 3 del: subsetI simp add: bind_UNION intro!: UN_least split: generat.split intro: results_gpv.intros)
  qed

lemma inline1_in_sub_gpvs_callee:
  assumes "Inr (out, callee', rpv') \<in> set_spmf (inline1 callee gpv s)"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and s: "I s"
  shows "\<exists>call\<in>outs_\<I> \<I>. \<exists>s. I s \<and> (\<forall>x \<in> responses_\<I> \<I>' out. callee' x \<in> sub_gpvs \<I>' (callee s call))"
  using aux[OF WT s] assms(1) by fastforce

lemma inline1_Inl_results_gpv:
  assumes "Inl (x, s') \<in> set_spmf (inline1 callee gpv s)"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and s: "I s"
  shows "x \<in> results_gpv \<I> gpv \<and> I s'"
  using aux[OF WT s] assms(1) by fastforce
end

lemma inline1_in_sub_gpvs:
  assumes "Inr (out, callee', rpv') \<in> set_spmf (inline1 callee gpv s)"
    and "(x, s') \<in> results_gpv \<I>' (callee' input)"
    and "input \<in> responses_\<I> \<I>' out"
    and "\<I> \<turnstile>g gpv \<surd>"
    and "I s"
  shows "rpv' x \<in> sub_gpvs \<I> gpv \<and> I s'"
proof -
  from \<open>\<I> \<turnstile>g gpv \<surd>\<close> \<open>I s\<close>
  have "set_spmf (inline1 callee gpv s) \<subseteq> {Inr (out, callee', rpv') | out callee' rpv'.
    \<forall>input \<in> responses_\<I> \<I>' out. \<forall>(x, s')\<in>results_gpv \<I>' (callee' input). I s' \<and> rpv' x \<in> sub_gpvs \<I> gpv}
    \<union> {Inl (x, s') | x s'. I s'}" (is "?concl (inline1 callee) gpv s" is "_ \<subseteq> ?rhs gpv s")
  proof(induction arbitrary: gpv s rule: inline1_fixp_induct)
    case adm show ?case by(intro cont_intro ccpo_class.admissible_leI)
    case bottom show ?case by simp
    case (step inline1')
    { fix out c
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" 
      from step.prems(1) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
      { fix x s'
        assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
        then have "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
        with out step.prems(2) have "x \<in> responses_\<I> \<I> out" "I s'" by(auto dest: results_callee)
        from step.prems(1) IO this(1) have "\<I> \<turnstile>g c x \<surd>" by(rule WT_gpvD)
        hence "?concl inline1' (c x) s'" using \<open>I s'\<close> by(rule step.IH)
        also have "\<dots> \<subseteq> ?rhs gpv s'" using IO Pure \<open>I s\<close>
          by(fastforce intro: sub_gpvs.cont dest: WT_gpv_OutD[OF step.prems(1)] results_callee[THEN subsetD, OF _ _ results_gpv.Pure])
        finally have "set_spmf (inline1' (c x) s') \<subseteq> \<dots>" .
      } moreover {
        fix out' c' input x s'
        assume "IO out' c' \<in> set_spmf (the_gpv (callee s out))"
          and "input \<in> responses_\<I> \<I>' out'" and "(x, s') \<in> results_gpv \<I>' (c' input)"
        then have "c x \<in> sub_gpvs \<I> gpv" "I s'" using IO \<open>I s\<close>
          by(auto intro!: sub_gpvs.base dest: WT_gpv_OutD[OF step.prems(1)] results_callee[THEN subsetD, OF _ _ results_gpv.IO])
      } moreover note calculation }
      then show ?case using step.prems(2)
        by(auto simp add: bind_UNION intro!: UN_least split: generat.split del: subsetI)
    qed
    with assms show ?thesis by fastforce
  qed

lemma WT_gpv_inline1:
  assumes "Inr (out, rpv, rpv') \<in> set_spmf (inline1 callee gpv s)"
    and "\<I> \<turnstile>g gpv \<surd>"
    and "I s"
  shows "out \<in> outs_\<I> \<I>'" (is "?thesis1")
    and "input \<in> responses_\<I> \<I>' out \<Longrightarrow> \<I>' \<turnstile>g rpv input \<surd>" (is "PROP ?thesis2")
    and "\<lbrakk> input \<in> responses_\<I> \<I>' out; (x, s') \<in> results_gpv \<I>' (rpv input) \<rbrakk> \<Longrightarrow> \<I> \<turnstile>g rpv' x \<surd> \<and> I s'" (is "PROP ?thesis3")
proof -
  from \<open>\<I> \<turnstile>g gpv \<surd>\<close> \<open>I s\<close>
  have "set_spmf (inline1 callee gpv s) \<subseteq> {Inr (out, rpv, rpv') | out rpv rpv'. out \<in> outs_\<I> \<I>'} \<union> {Inl (x, s')| x s'. I s'}"
  proof(induction arbitrary: gpv s rule: inline1_fixp_induct)
    { case adm show ?case by(intro cont_intro ccpo_class.admissible_leI) }
    { case bottom show ?case by simp }
    case (step inline1')
    { fix out c
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" 
      from step.prems(1) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
      { fix x s'
        assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
        then have *: "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
        with out step.prems(2) have "x \<in> responses_\<I> \<I> out" "I s'" by(auto dest: results_callee)
        from step.prems(1) IO this(1) have "\<I> \<turnstile>g c x \<surd>" by(rule WT_gpvD)
        note this \<open>I s'\<close>
      } moreover {
        fix out' c'
        from out step.prems(2) have "\<I>' \<turnstile>g callee s out \<surd>" by(rule WT_callee)
        moreover assume "IO out' c' \<in> set_spmf (the_gpv (callee s out))"
        ultimately have "out' \<in> outs_\<I> \<I>'" by(rule WT_gpvD) 
      } moreover note calculation }
      then show ?case using step.prems(2)
        by(auto del: subsetI simp add: bind_UNION intro!: UN_least split: generat.split intro!: step.IH[THEN order_trans])
    qed
    then show ?thesis1 using assms by auto

    assume "input \<in> responses_\<I> \<I>' out"
    with inline1_in_sub_gpvs_callee[OF \<open>Inr _ \<in> _\<close> \<open>\<I> \<turnstile>g gpv \<surd>\<close> \<open>I s\<close>]
    obtain out' s where "out' \<in> outs_\<I> \<I>" 
      and *: "rpv input \<in> sub_gpvs \<I>' (callee s out')" and "I s" by blast
    from \<open>out' \<in> _\<close> \<open>I s\<close> have "\<I>' \<turnstile>g callee s out' \<surd>" by(rule WT_callee)
    then show "\<I>' \<turnstile>g rpv input \<surd>" using * by(rule WT_sub_gpvsD)

    assume "(x, s') \<in> results_gpv \<I>' (rpv input)"
    with \<open>Inr _ \<in> _\<close> have "rpv' x \<in> sub_gpvs \<I> gpv \<and> I s'"
      using \<open>input \<in> _\<close> \<open>\<I> \<turnstile>g gpv \<surd>\<close> assms(3) \<open>I s\<close> by-(rule inline1_in_sub_gpvs)
    with \<open>\<I> \<turnstile>g gpv \<surd>\<close> show "\<I> \<turnstile>g rpv' x \<surd> \<and> I s'" by(blast intro: WT_sub_gpvsD)
  qed

lemma WT_gpv_inline_invar:
  assumes "\<I> \<turnstile>g gpv \<surd>"
    and "I s"
  shows "\<I>' \<turnstile>g inline callee gpv s \<surd>"
  using assms
proof(coinduction arbitrary: gpv s rule: WT_gpv_coinduct_bind)
  case (WT_gpv out c gpv)
  from \<open>IO out c \<in> _\<close> obtain callee' rpv'
    where Inr: "Inr (out, callee', rpv') \<in> set_spmf (inline1 callee gpv s)"
      and c: "c = (\<lambda>input. callee' input \<bind> (\<lambda>(x, s). inline callee (rpv' x) s))"
    by(clarsimp simp add: inline_sel split: sum.split_asm)
  from Inr \<open>\<I> \<turnstile>g gpv \<surd>\<close> \<open>I s\<close> have ?out by(rule WT_gpv_inline1)
  moreover have "?cont TYPE('ret \<times> 's)" (is "\<forall>input\<in>_. _ \<or> _ \<or> ?case' input")
  proof(rule ballI disjI2)+
    fix input
    assume "input \<in> responses_\<I> \<I>' out"
    with Inr \<open>\<I> \<turnstile>g gpv \<surd> \<close> \<open>I s\<close> have "\<I>' \<turnstile>g callee' input \<surd>"
      and "\<And>x s'. (x, s') \<in> results_gpv \<I>' (callee' input) \<Longrightarrow> \<I> \<turnstile>g rpv' x \<surd> \<and> I s'"
      by(blast dest: WT_gpv_inline1)+
    then show "?case' input" by(subst c)(auto 4 5)
  qed
  ultimately show "?case TYPE('ret \<times> 's)" ..
qed

end

lemma WT_gpv_inline:
  assumes "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> results_gpv \<I>' (callee s x) \<subseteq> responses_\<I> \<I> x \<times> UNIV"
    and "\<And>x s. x \<in> outs_\<I> \<I> \<Longrightarrow> \<I>' \<turnstile>g callee s x \<surd>"
    and "\<I> \<turnstile>g gpv \<surd>"
  shows "\<I>' \<turnstile>g inline callee gpv s \<surd>"
proof -
  interpret raw_converter_invariant \<I> \<I>' callee "\<lambda>_. True" 
    using assms by(unfold_locales)auto
  show ?thesis by(rule WT_gpv_inline_invar)(use assms in auto)
qed

lemma results_gpv_sub_gvps: "gpv' \<in> sub_gpvs \<I> gpv \<Longrightarrow> results_gpv \<I> gpv' \<subseteq> results_gpv \<I> gpv"
  by(induction rule: sub_gpvs.induct)(auto intro: results_gpv.IO)

lemma in_results_gpv_sub_gvps: "\<lbrakk> x \<in> results_gpv \<I> gpv'; gpv' \<in> sub_gpvs \<I> gpv \<rbrakk> \<Longrightarrow> x \<in> results_gpv \<I> gpv"
  using results_gpv_sub_gvps[of gpv' \<I> gpv] by blast

context raw_converter_invariant begin
lemma results_gpv_inline_aux:
  assumes "(x, s') \<in> results_gpv \<I>' (inline_aux callee y)"
  shows "\<lbrakk> y = Inl (gpv, s); \<I> \<turnstile>g gpv \<surd>; I s \<rbrakk> \<Longrightarrow> x \<in> results_gpv \<I> gpv \<and> I s'"
    and "\<lbrakk> y = Inr (rpv, callee'); \<forall>(z, s') \<in> results_gpv \<I>' callee'. \<I> \<turnstile>g rpv z \<surd> \<and> I s' \<rbrakk>
    \<Longrightarrow> \<exists>(z, s'') \<in> results_gpv \<I>' callee'. x \<in> results_gpv \<I> (rpv z) \<and> I s'' \<and> I s'"
  using assms
proof(induction gvp'\<equiv>"inline_aux callee y" arbitrary: y gpv s rpv callee')
  case Pure case 1
  with Pure show ?case
    by(auto simp add: inline_aux.sel split: sum.split_asm dest: inline1_Inl_results_gpv)
next
  case Pure case 2
  with Pure show ?case
    by(clarsimp simp add: inline_aux.sel split: sum.split_asm)
      (fastforce split: generat.split_asm dest: inline1_Inl_results_gpv intro: results_gpv.Pure)+
next
  case (IO out c input) case 1
  with IO(1) obtain rpv rpv' where inline1: "Inr (out, rpv, rpv') \<in> set_spmf (inline1 callee gpv s)"
    and c: "c = (\<lambda>input. inline_aux callee (Inr (rpv', rpv input)))"
    by(auto simp add: inline_aux.sel split: sum.split_asm)
  from inline1[THEN inline1_in_sub_gpvs, OF _ \<open>input \<in> responses_\<I> \<I>' out\<close> _ \<open>I s\<close>] \<open>\<I> \<turnstile>g gpv \<surd>\<close>
  have "\<forall>(z, s')\<in>results_gpv \<I>' (rpv input). \<I> \<turnstile>g rpv' z \<surd> \<and> I s'"
    by(auto intro: WT_sub_gpvsD)
  from IO(5)[unfolded c, OF refl refl this] obtain input' s'' 
    where input': "(input', s'') \<in> results_gpv \<I>' (rpv input)" 
      and x: "x \<in> results_gpv \<I> (rpv' input')" and s'': "I s''" "I s'"
    by auto
  from inline1[THEN inline1_in_sub_gpvs, OF input' \<open>input \<in> responses_\<I> \<I>' out\<close> \<open>\<I> \<turnstile>g gpv \<surd>\<close> \<open>I s\<close>] s'' x
  show ?case by(auto intro: in_results_gpv_sub_gvps)
next
  case (IO out c input) case 2
  from IO(1) "2"(1) consider (Pure) input' s'' rpv' rpv''
    where "Pure (input', s'') \<in> set_spmf (the_gpv callee')" "Inr (out, rpv', rpv'') \<in> set_spmf (inline1 callee (rpv input') s'')"
      "c = (\<lambda>input. inline_aux callee (Inr (rpv'', rpv' input)))"
    | (Cont) rpv' where "IO out rpv' \<in> set_spmf (the_gpv callee')" "c = (\<lambda>input. inline_aux callee (Inr (rpv, rpv' input)))"
    by(auto simp add: inline_aux.sel split: sum.split_asm; rename_tac generat; case_tac generat; clarsimp)
  then show ?case
  proof cases
    case Pure
    have res: "(input', s'') \<in> results_gpv \<I>' callee'" using Pure(1) by(rule results_gpv.Pure)
    with 2 have WT: "\<I> \<turnstile>g rpv input' \<surd>" "I s''" by auto
    have "\<forall>(z, s')\<in>results_gpv \<I>' (rpv' input). \<I> \<turnstile>g rpv'' z \<surd> \<and> I s'"
      using inline1_in_sub_gpvs[OF Pure(2) _ \<open>input \<in> _\<close> WT] WT by(auto intro: WT_sub_gpvsD)
    from IO(5)[unfolded Pure(3), OF refl refl this] obtain z s'''
      where z: "(z, s''') \<in> results_gpv \<I>' (rpv' input)"
        and x: "x \<in> results_gpv \<I> (rpv'' z)" and s': "I s'''" "I s'" by auto
    have "x \<in> results_gpv \<I> (rpv input')" using x inline1_in_sub_gpvs[OF Pure(2) z \<open>input \<in> _\<close> WT]
      by(auto intro: in_results_gpv_sub_gvps)
    then show ?thesis using res WT s' by auto
  next
    case Cont
    have "\<forall>(z, s')\<in>results_gpv \<I>' (rpv' input). \<I> \<turnstile>g rpv z \<surd> \<and> I s'" 
      using Cont 2 \<open>input \<in> responses_\<I> \<I>' out\<close> by(auto intro: results_gpv.IO)
    from IO(5)[unfolded Cont, OF refl refl this] obtain z s'' 
      where "(z, s'') \<in> results_gpv \<I>' (rpv' input)" "x \<in> results_gpv \<I> (rpv z)" "I s''" "I s'" by auto
    then show ?thesis using Cont(1) \<open>input \<in> _\<close> by(auto intro: results_gpv.IO)
  qed
qed

lemma results_gpv_inline: 
  "\<lbrakk>(x, s') \<in> results_gpv \<I>' (inline callee gpv s); \<I> \<turnstile>g gpv \<surd>; I s\<rbrakk> \<Longrightarrow> x \<in> results_gpv \<I> gpv \<and> I s'"
  unfolding inline_def by(rule results_gpv_inline_aux(1)[OF _ refl])

end


lemma inline_map_gpv:
  "inline callee (map_gpv f g gpv) s = map_gpv (apfst f) id (inline (\<lambda>s x. callee s (g x)) gpv s)"
  unfolding apfst_def
  by(rule inline_parametric
      [where S="BNF_Def.Grp UNIV id" and C="BNF_Def.Grp UNIV g" and C'="BNF_Def.Grp UNIV id" and A="BNF_Def.Grp UNIV f",
        THEN rel_funD, THEN rel_funD, THEN rel_funD,
        unfolded gpv.rel_Grp prod.rel_Grp, simplified, folded eq_alt, unfolded Grp_def, simplified])
    (auto simp add: rel_fun_def relator_eq)



(* Computational_Model *)

lemma \<I>_full_le_plus_\<I>: "\<I>_full \<le> plus_\<I> \<I>1 \<I>2" if "\<I>_full \<le> \<I>1" "\<I>_full \<le> \<I>2"
  using that by(auto simp add: le_\<I>_def top_unique)

lemma plus_\<I>_mono: "plus_\<I> \<I>1 \<I>2 \<le> plus_\<I> \<I>1' \<I>2'" if "\<I>1 \<le> \<I>1'" "\<I>2 \<le> \<I>2'" 
  using that by(fastforce simp add: le_\<I>_def)

primcorec (transfer) left_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out + 'out', 'in + 'in') gpv" where
  "the_gpv (left_gpv gpv) = 
   map_spmf (map_generat id Inl (\<lambda>rpv input. case input of Inl input' \<Rightarrow> left_gpv (rpv input') | _ \<Rightarrow> Fail)) (the_gpv gpv)"

abbreviation left_rpv :: "('a, 'out, 'in) rpv \<Rightarrow> ('a, 'out + 'out', 'in + 'in') rpv" where
  "left_rpv rpv \<equiv> \<lambda>input. case input of Inl input' \<Rightarrow> left_gpv (rpv input') | _ \<Rightarrow> Fail"

primcorec (transfer) right_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out' + 'out, 'in' + 'in) gpv" where
  "the_gpv (right_gpv gpv) =
   map_spmf (map_generat id Inr (\<lambda>rpv input. case input of Inr input' \<Rightarrow> right_gpv (rpv input') | _ \<Rightarrow> Fail)) (the_gpv gpv)"

abbreviation right_rpv :: "('a, 'out, 'in) rpv \<Rightarrow> ('a, 'out' + 'out, 'in' + 'in) rpv" where
  "right_rpv rpv \<equiv> \<lambda>input. case input of Inr input' \<Rightarrow> right_gpv (rpv input') | _ \<Rightarrow> Fail"

context 
  includes lifting_syntax
  notes [transfer_rule] = corec_gpv_parametric' Fail_parametric' the_gpv_parametric'
begin

lemmas left_gpv_parametric = left_gpv.transfer

lemma left_gpv_parametric':
  "(rel_gpv'' A C R ===> rel_gpv'' A (rel_sum C C') (rel_sum R R')) left_gpv left_gpv"
  unfolding left_gpv_def by transfer_prover

lemmas right_gpv_parametric = right_gpv.transfer

lemma right_gpv_parametric':
  "(rel_gpv'' A C' R' ===> rel_gpv'' A (rel_sum C C') (rel_sum R R')) right_gpv right_gpv"
  unfolding right_gpv_def by transfer_prover

end

lemma left_gpv_Done [simp]: "left_gpv (Done x) = Done x"
  by(rule gpv.expand) simp

lemma right_gpv_Done [simp]: "right_gpv (Done x) = Done x"
  by(rule gpv.expand) simp

lemma left_gpv_Pause [simp]:
  "left_gpv (Pause x rpv) = Pause (Inl x) (\<lambda>input. case input of Inl input' \<Rightarrow> left_gpv (rpv input') | _ \<Rightarrow> Fail)"
  by(rule gpv.expand) simp

lemma right_gpv_Pause [simp]:
  "right_gpv (Pause x rpv) = Pause (Inr x) (\<lambda>input. case input of Inr input' \<Rightarrow> right_gpv (rpv input') | _ \<Rightarrow> Fail)"
  by(rule gpv.expand) simp

lemma left_gpv_map: "left_gpv (map_gpv f g gpv) = map_gpv f (map_sum g h) (left_gpv gpv)"
  using left_gpv.transfer[of "BNF_Def.Grp UNIV f" "BNF_Def.Grp UNIV g" "BNF_Def.Grp UNIV h"]
  unfolding sum.rel_Grp gpv.rel_Grp
  by(auto simp add: rel_fun_def Grp_def)

lemma right_gpv_map: "right_gpv (map_gpv f g gpv) = map_gpv f (map_sum h g) (right_gpv gpv)"
  using right_gpv.transfer[of "BNF_Def.Grp UNIV f" "BNF_Def.Grp UNIV g" "BNF_Def.Grp UNIV h"]
  unfolding sum.rel_Grp gpv.rel_Grp
  by(auto simp add: rel_fun_def Grp_def)

lemma results'_gpv_left_gpv [simp]: 
  "results'_gpv (left_gpv gpv :: ('a, 'out + 'out', 'in + 'in') gpv) = results'_gpv gpv" (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv'\<equiv>"left_gpv gpv :: ('a, 'out + 'out', 'in + 'in') gpv" arbitrary: gpv)
      (fastforce simp add: elim!: generat.set_cases intro: results'_gpvI split: sum.splits)+
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that
    by(induction)
      (auto 4 3 elim!: generat.set_cases intro: results'_gpv_Pure rev_image_eqI results'_gpv_Cont[where input="Inl _"])
qed

lemma results'_gpv_right_gpv [simp]: 
  "results'_gpv (right_gpv gpv :: ('a, 'out' + 'out, 'in' + 'in) gpv) = results'_gpv gpv" (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv'\<equiv>"right_gpv gpv :: ('a, 'out' + 'out, 'in' + 'in) gpv" arbitrary: gpv)
      (fastforce simp add: elim!: generat.set_cases intro: results'_gpvI split: sum.splits)+
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that
    by(induction)
      (auto 4 3 elim!: generat.set_cases intro: results'_gpv_Pure rev_image_eqI results'_gpv_Cont[where input="Inr _"])
qed

lemma left_gpv_Inl_transfer: "rel_gpv'' (=) (\<lambda>l r. l = Inl r) (\<lambda>l r. l = Inl r) (left_gpv gpv) gpv"
  by(coinduction arbitrary: gpv)
    (auto simp add: spmf_rel_map generat.rel_map del: rel_funI intro!: rel_spmf_reflI generat.rel_refl_strong rel_funI)

lemma right_gpv_Inr_transfer: "rel_gpv'' (=) (\<lambda>l r. l = Inr r) (\<lambda>l r. l = Inr r) (right_gpv gpv) gpv"
  by(coinduction arbitrary: gpv)
    (auto simp add: spmf_rel_map generat.rel_map del: rel_funI intro!: rel_spmf_reflI generat.rel_refl_strong rel_funI)

lemma exec_gpv_plus_oracle_left: "exec_gpv (plus_oracle oracle1 oracle2) (left_gpv gpv) s = exec_gpv oracle1 gpv s"
  unfolding spmf_rel_eq[symmetric] prod.rel_eq[symmetric]
  by(rule exec_gpv_parametric'[where A="(=)" and S="(=)" and CALL="\<lambda>l r. l = Inl r" and R="\<lambda>l r. l = Inl r", THEN rel_funD, THEN rel_funD, THEN rel_funD])
    (auto intro!: rel_funI simp add: spmf_rel_map apfst_def map_prod_def rel_prod_conv intro: rel_spmf_reflI left_gpv_Inl_transfer)

lemma exec_gpv_plus_oracle_right: "exec_gpv (plus_oracle oracle1 oracle2) (right_gpv gpv) s = exec_gpv oracle2 gpv s"
  unfolding spmf_rel_eq[symmetric] prod.rel_eq[symmetric]
  by(rule exec_gpv_parametric'[where A="(=)" and S="(=)" and CALL="\<lambda>l r. l = Inr r" and R="\<lambda>l r. l = Inr r", THEN rel_funD, THEN rel_funD, THEN rel_funD])
    (auto intro!: rel_funI simp add: spmf_rel_map apfst_def map_prod_def rel_prod_conv intro: rel_spmf_reflI right_gpv_Inr_transfer)

lemma left_gpv_bind_gpv: "left_gpv (bind_gpv gpv f) = bind_gpv (left_gpv gpv) (left_gpv \<circ> f)"
  by(coinduction arbitrary:gpv f rule: gpv.coinduct_strong)
    (auto 4 4 simp add: bind_map_spmf spmf_rel_map intro!: rel_spmf_reflI rel_spmf_bindI[of "(=)"] generat.rel_refl rel_funI split: sum.splits)

lemma inline1_left_gpv:
  "inline1 (\<lambda>s q. left_gpv (callee s q)) gpv s = 
   map_spmf (map_sum id (map_prod Inl (map_prod left_rpv id))) (inline1 callee gpv s)"
proof(induction arbitrary: gpv s rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf inline1.mono inline1.mono inline1_def inline1_def, unfolded lub_spmf_empty, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step inline1' inline1'')
  then show ?case
    by(auto simp add: map_spmf_bind_spmf o_def bind_map_spmf intro!: ext bind_spmf_cong split: generat.split)
qed

lemma left_gpv_inline: "left_gpv (inline callee gpv s) = inline (\<lambda>s q. left_gpv (callee s q)) gpv s"
  by(coinduction arbitrary: callee gpv s rule: gpv_coinduct_bind)
    (fastforce simp add: inline_sel spmf_rel_map inline1_left_gpv left_gpv_bind_gpv o_def split_def intro!: rel_spmf_reflI split: sum.split intro!: rel_funI gpv.rel_refl_strong)

lemma right_gpv_bind_gpv: "right_gpv (bind_gpv gpv f) = bind_gpv (right_gpv gpv) (right_gpv \<circ> f)"
  by(coinduction arbitrary:gpv f rule: gpv.coinduct_strong)
    (auto 4 4 simp add: bind_map_spmf spmf_rel_map intro!: rel_spmf_reflI rel_spmf_bindI[of "(=)"] generat.rel_refl rel_funI split: sum.splits)

lemma inline1_right_gpv:
  "inline1 (\<lambda>s q. right_gpv (callee s q)) gpv s = 
   map_spmf (map_sum id (map_prod Inr (map_prod right_rpv id))) (inline1 callee gpv s)"
proof(induction arbitrary: gpv s rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf inline1.mono inline1.mono inline1_def inline1_def, unfolded lub_spmf_empty, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step inline1' inline1'')
  then show ?case
    by(auto simp add: map_spmf_bind_spmf o_def bind_map_spmf intro!: ext bind_spmf_cong split: generat.split)
qed

lemma right_gpv_inline: "right_gpv (inline callee gpv s) = inline (\<lambda>s q. right_gpv (callee s q)) gpv s"
  by(coinduction arbitrary: callee gpv s rule: gpv_coinduct_bind)
    (fastforce simp add: inline_sel spmf_rel_map inline1_right_gpv right_gpv_bind_gpv o_def split_def intro!: rel_spmf_reflI split: sum.split intro!: rel_funI gpv.rel_refl_strong)

lemma WT_gpv_left_gpv: "\<I>1 \<turnstile>g gpv \<surd> \<Longrightarrow> \<I>1 \<oplus>\<^sub>\<I> \<I>2 \<turnstile>g left_gpv gpv \<surd>"
  by(coinduction arbitrary: gpv)(auto 4 4 dest: WT_gpvD)

lemma WT_gpv_right_gpv: "\<I>2 \<turnstile>g gpv \<surd> \<Longrightarrow> \<I>1 \<oplus>\<^sub>\<I> \<I>2 \<turnstile>g right_gpv gpv \<surd>"
  by(coinduction arbitrary: gpv)(auto 4 4 dest: WT_gpvD)

lemma results_gpv_left_gpv [simp]: "results_gpv (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (left_gpv gpv) = results_gpv \<I>1 gpv"
  (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv'\<equiv>"left_gpv gpv :: ('a, 'b + 'c, 'd + 'e) gpv" arbitrary: gpv rule: results_gpv.induct)
      (fastforce intro: results_gpv.intros)+
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that
    by(induction)(fastforce intro: results_gpv.intros)+
qed

lemma results_gpv_right_gpv [simp]: "results_gpv (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (right_gpv gpv) = results_gpv \<I>2 gpv"
  (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv'\<equiv>"right_gpv gpv :: ('a, 'b + 'c, 'd + 'e) gpv" arbitrary: gpv rule: results_gpv.induct)
      (fastforce intro: results_gpv.intros)+
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that
    by(induction)(fastforce intro: results_gpv.intros)+
qed

lemma left_gpv_Fail [simp]: "left_gpv Fail = Fail"
  by(rule gpv.expand) auto

lemma right_gpv_Fail [simp]: "right_gpv Fail = Fail"
  by(rule gpv.expand) auto

lemma rsuml_lsumr_left_gpv_left_gpv:"map_gpv' id rsuml lsumr (left_gpv (left_gpv gpv)) = left_gpv gpv"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split elim!: lsumr.elims intro: exI[where x=Fail])

lemma rsuml_lsumr_left_gpv_right_gpv: "map_gpv' id rsuml lsumr (left_gpv (right_gpv gpv)) = right_gpv (left_gpv gpv)"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split elim!: lsumr.elims intro: exI[where x=Fail])

lemma rsuml_lsumr_right_gpv: "map_gpv' id rsuml lsumr (right_gpv gpv) = right_gpv (right_gpv gpv)"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split elim!: lsumr.elims intro: exI[where x=Fail])

lemma map_gpv'_map_gpv_swap:
  "map_gpv' f g h (map_gpv f' id gpv) = map_gpv (f \<circ> f') id (map_gpv' id g h gpv)"
  by(simp add: map_gpv_conv_map_gpv' map_gpv'_comp)

lemma lsumr_rsuml_left_gpv: "map_gpv' id lsumr rsuml (left_gpv gpv) = left_gpv (left_gpv gpv)"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split intro: exI[where x=Fail])

lemma lsumr_rsuml_right_gpv_left_gpv:
  "map_gpv' id lsumr rsuml (right_gpv (left_gpv gpv)) = left_gpv (right_gpv gpv)"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split intro: exI[where x=Fail])

lemma lsumr_rsuml_right_gpv_right_gpv:
  "map_gpv' id lsumr rsuml (right_gpv (right_gpv gpv)) = right_gpv gpv"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split!: sum.split elim!: rsuml.elims intro: exI[where x=Fail])


lemma in_set_spmf_extend_state_oracle [simp]:
  "x \<in> set_spmf (extend_state_oracle oracle s y) \<longleftrightarrow>
   fst (snd x) = fst s \<and> (fst x, snd (snd x)) \<in> set_spmf (oracle (snd s) y)"
  by(auto 4 4 simp add: extend_state_oracle_def split_beta intro: rev_image_eqI prod.expand)

lemma extend_state_oracle_plus_oracle: 
  "extend_state_oracle (plus_oracle oracle1 oracle2) = plus_oracle (extend_state_oracle oracle1) (extend_state_oracle oracle2)"
proof ((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases s; cases q) (simp_all add: apfst_def spmf.map_comp o_def split_def)
qed

definition stateless_callee :: "('a \<Rightarrow> ('b, 'out, 'in) gpv) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's, 'out, 'in) gpv)" where
  "stateless_callee callee s = map_gpv (\<lambda>b. (b, s)) id \<circ> callee"

lemma stateless_callee_parametric': 
  includes lifting_syntax notes [transfer_rule] = map_gpv_parametric' shows
    "((A ===> rel_gpv'' B C R) ===> S ===> A ===> (rel_gpv'' (rel_prod B S) C R))
   stateless_callee stateless_callee"
  unfolding stateless_callee_def by transfer_prover

lemma id_oralce_alt_def: "id_oracle = stateless_callee (\<lambda>x. Pause x Done)"
  by(simp add: id_oracle_def fun_eq_iff stateless_callee_def)

context
  fixes left :: "'s1 \<Rightarrow> 'x1 \<Rightarrow> ('y1 \<times> 's1, 'call1, 'ret1) gpv"
    and right :: "'s2 \<Rightarrow> 'x2 \<Rightarrow> ('y2 \<times> 's2, 'call2, 'ret2) gpv"
begin

fun parallel_intercept :: "'s1 \<times> 's2 \<Rightarrow> 'x1 + 'x2 \<Rightarrow> (('y1 + 'y2) \<times> ('s1 \<times> 's2), 'call1 + 'call2, 'ret1 + 'ret2) gpv"
  where
    "parallel_intercept (s1, s2) (Inl a) = left_gpv (map_gpv (map_prod Inl (\<lambda>s1'. (s1', s2))) id (left s1 a))"
  | "parallel_intercept (s1, s2) (Inr b) = right_gpv (map_gpv (map_prod Inr (Pair s1)) id (right s2 b))"

end

(* GPV_Expectation *)

lemma expectation_gpv_\<I>_mono:
  defines "expectation_gpv' \<equiv> expectation_gpv"
  assumes le: "\<I> \<le> \<I>'"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
  shows "expectation_gpv fail \<I> f gpv \<le> expectation_gpv' fail \<I>' f gpv"
  using WT
proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case step [unfolded expectation_gpv'_def]: (step expectation_gpv')
  show ?case unfolding expectation_gpv'_def
    by(subst expectation_gpv.simps)
      (clarsimp intro!: add_mono nn_integral_mono_AE INF_mono split: generat.split
        , auto intro!: bexI step add_mono nn_integral_mono_AE INF_mono split: generat.split dest: WT_gpvD[OF step.prems] intro!: step dest: responses_\<I>_mono[OF le])
qed

lemma pgen_lossless_gpv_mono:
  assumes *: "pgen_lossless_gpv fail \<I> gpv"
    and le: "\<I> \<le> \<I>'"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and fail: "fail \<le> 1"
  shows "pgen_lossless_gpv fail \<I>' gpv"
  unfolding pgen_lossless_gpv_def
proof(rule antisym)
  from WT le have "\<I>' \<turnstile>g gpv \<surd>" by(rule WT_gpv_\<I>_mono)
  from expectation_gpv_const_le[OF this, of fail 1] fail
  show "expectation_gpv fail \<I>' (\<lambda>_. 1) gpv \<le> 1" by(simp add: max_def split: if_split_asm)
  from expectation_gpv_\<I>_mono[OF le WT, of fail "\<lambda>_. 1"] *
  show "expectation_gpv fail \<I>' (\<lambda>_. 1) gpv \<ge> 1" by(simp add: pgen_lossless_gpv_def)
qed

lemma plossless_gpv_mono:
  "\<lbrakk> plossless_gpv \<I> gpv; \<I> \<le> \<I>'; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> plossless_gpv \<I>' gpv"
  by(erule pgen_lossless_gpv_mono; simp)

lemma pfinite_gpv_mono:
  "\<lbrakk> pfinite_gpv \<I> gpv; \<I> \<le> \<I>'; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> pfinite_gpv \<I>' gpv"
  by(erule pgen_lossless_gpv_mono; simp)

lemma pgen_lossless_gpv_parametric': includes lifting_syntax shows
  "((=) ===> rel_\<I> C R ===> rel_gpv'' A C R ===> (=)) pgen_lossless_gpv pgen_lossless_gpv"
  unfolding pgen_lossless_gpv_def supply expectation_gpv_parametric'[transfer_rule] by transfer_prover

lemma pgen_lossless_gpv_parametric: includes lifting_syntax shows
  "((=) ===> rel_\<I> C (=) ===> rel_gpv A C ===> (=)) pgen_lossless_gpv pgen_lossless_gpv"
  using pgen_lossless_gpv_parametric'[of C "(=)" A] by(simp add: rel_gpv_conv_rel_gpv'')

lemma pgen_lossless_gpv_map_gpv_id [simp]:
  "pgen_lossless_gpv fail \<I> (map_gpv f id gpv) = pgen_lossless_gpv fail \<I> gpv"
  using pgen_lossless_gpv_parametric[of "BNF_Def.Grp UNIV id" "BNF_Def.Grp UNIV f"]
  unfolding gpv.rel_Grp
  by(auto simp add: eq_alt[symmetric] rel_\<I>_eq rel_fun_def Grp_iff)

context raw_converter_invariant begin

lemma expectation_gpv_le_inline:
  defines "expectation_gpv2 \<equiv> expectation_gpv 0 \<I>'"
  assumes callee: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> plossless_gpv \<I>' (callee s x)"
    and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
    and I: "I s"
  shows "expectation_gpv 0 \<I> f gpv \<le> expectation_gpv2 (\<lambda>(x, s). f x) (inline callee gpv s)"
  using WT_gpv I
proof(induction arbitrary: gpv s rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv')
  { fix out c
    assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
    with step.prems (1) have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpv_OutD)
    have "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) = \<integral>\<^sup>+ generat. (INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<partial>measure_spmf (the_gpv (callee s out))"
      using WT_callee[OF out, of s] callee[OF out, of s] \<open>I s\<close>
      by(clarsimp simp add: measure_spmf.emeasure_eq_measure plossless_iff_colossless_pfinite colossless_gpv_lossless_spmfD lossless_weight_spmfD)
    also have "\<dots> \<le> \<integral>\<^sup>+ generat. (case generat of Pure (x, s') \<Rightarrow>
            \<integral>\<^sup>+ xx. (case xx of Inl (x, _) \<Rightarrow> f x 
               | Inr (out', callee', rpv) \<Rightarrow> INF r':responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r, s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv r) s')) (callee' r'))
            \<partial>measure_spmf (inline1 callee (c x) s')
         | IO out' rpv \<Rightarrow> INF r':responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r'))
       \<partial>measure_spmf (the_gpv (callee s out))"
    proof(rule nn_integral_mono_AE; simp split!: generat.split)
      fix x s'
      assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
      hence "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
      with results_callee[OF out, of s] \<open>I s\<close> have x: "x \<in> responses_\<I> \<I> out" and "I s'" by blast+
      from x have "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> expectation_gpv' (c x)" by(rule INF_lower)
      also have "\<dots> \<le> expectation_gpv2 (\<lambda>(x, s). f x) (inline callee (c x) s')"
        by(rule step.IH)(rule WT_gpv_ContD[OF step.prems(1) IO x] step.prems \<open>I s'\<close>|assumption)+
      also have "\<dots> = \<integral>\<^sup>+ xx. (case xx of Inl (x, _) \<Rightarrow> f x 
               | Inr (out', callee', rpv) \<Rightarrow> INF r':responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r, s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv r) s')) (callee' r'))
            \<partial>measure_spmf (inline1 callee (c x) s')"
        unfolding expectation_gpv2_def
        by(subst expectation_gpv.simps)(auto simp add: inline_sel split_def o_def intro!: nn_integral_cong split: generat.split sum.split)
      finally show "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> \<dots>" .
    next
      fix out' rpv
      assume IO': "IO out' rpv \<in> set_spmf (the_gpv (callee s out))"
      have "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> (INF (r, s'):(\<Union>r'\<in>responses_\<I> \<I>' out'. results_gpv \<I>' (rpv r')). expectation_gpv' (c r))"
        using IO' results_callee[OF out, of s] \<open>I s\<close> by(intro INF_mono)(auto intro: results_gpv.IO)
      also have "\<dots> = (INF r':responses_\<I> \<I>' out'. INF (r, s'):results_gpv \<I>' (rpv r'). expectation_gpv' (c r))"
        by(simp add: INF_UNION)
      also have "\<dots> \<le> (INF r':responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r'))"
      proof(rule INF_mono, rule bexI)
        fix r'
        assume r': "r' \<in> responses_\<I> \<I>' out'"
        have "(INF (r, s'):results_gpv \<I>' (rpv r'). expectation_gpv' (c r)) \<le> (INF (r, s'):results_gpv \<I>' (rpv r'). expectation_gpv2 (\<lambda>(x, s). f x) (inline callee (c r) s'))"
          using IO IO' step.prems out results_callee[OF out, of s] r'
          by(auto intro!: INF_mono rev_bexI step.IH dest: WT_gpv_ContD intro: results_gpv.IO)
        also have "\<dots> \<le>  expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r')"
          unfolding expectation_gpv2_def using plossless_gpv_ContD[OF callee, OF out \<open>I s\<close> IO' r'] WT_callee[OF out \<open>I s\<close>] IO' r'
          by(intro plossless_INF_le_expectation_gpv)(auto intro: WT_gpv_ContD)
        finally show "(INF (r, s'):results_gpv \<I>' (rpv r'). expectation_gpv' (c r)) \<le> \<dots>" .
      qed
      finally show "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> \<dots>" .
    qed
    also note calculation }
  then show ?case unfolding expectation_gpv2_def
    apply(rewrite expectation_gpv.simps)
    apply(rewrite inline_sel)
    apply(simp add: o_def pmf_map_spmf_None)
    apply(rewrite sum.case_distrib[where h="case_generat _ _"])
    apply(simp cong del: sum.case_cong_weak)
    apply(simp add: split_beta o_def cong del: sum.case_cong_weak)
    apply(rewrite inline1.simps)
    apply(rewrite measure_spmf_bind)
    apply(rewrite nn_integral_bind[where B="measure_spmf _"])
      apply simp
     apply(simp add: space_subprob_algebra)
    apply(rule nn_integral_mono_AE)
    apply(clarsimp split!: generat.split)
     apply(simp add: measure_spmf_return_spmf nn_integral_return)
    apply(rewrite measure_spmf_bind)
    apply(simp add: nn_integral_bind[where B="measure_spmf _"] space_subprob_algebra)
    apply(subst generat.case_distrib[where h="measure_spmf"])
    apply(subst generat.case_distrib[where h="\<lambda>x. nn_integral x _"])
    apply(simp add: measure_spmf_return_spmf nn_integral_return split_def)
    done
qed

lemma plossless_inline:
  assumes lossless: "plossless_gpv \<I> gpv"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and callee: "\<And>s x. \<lbrakk> I s; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> plossless_gpv \<I>' (callee s x)"
    and I: "I s"
  shows "plossless_gpv \<I>' (inline callee gpv s)"
  unfolding pgen_lossless_gpv_def
proof(rule antisym)
  have WT': "\<I>' \<turnstile>g inline callee gpv s \<surd>" using WT I by(rule WT_gpv_inline_invar)
  from expectation_gpv_const_le[OF WT', of 0 1]
  show "expectation_gpv 0 \<I>' (\<lambda>_. 1) (inline callee gpv s) \<le> 1" by(simp add: max_def)

  have "1 = expectation_gpv 0 \<I> (\<lambda>_. 1) gpv" using lossless by(simp add: pgen_lossless_gpv_def)
  also have "\<dots> \<le> expectation_gpv 0 \<I>' (\<lambda>_. 1) (inline callee gpv s)"
    by(rule expectation_gpv_le_inline[unfolded split_def]; rule callee I WT)
  finally show "1 \<le> \<dots>" .
qed

end

lemma expectation_left_gpv [simp]:
  "expectation_gpv fail (\<I> \<oplus>\<^sub>\<I> \<I>') f (left_gpv gpv) = expectation_gpv fail \<I> f gpv"
proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions expectation_gpv.mono expectation_gpv.mono expectation_gpv_def expectation_gpv_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv' expectation_gpv'')
  show ?case
    by (auto simp add: pmf_map_spmf_None o_def case_map_generat image_comp
      split: generat.split intro!: nn_integral_cong_AE INF_cong step.IH)
qed

lemma expectation_right_gpv [simp]:
  "expectation_gpv fail (\<I> \<oplus>\<^sub>\<I> \<I>') f (right_gpv gpv) = expectation_gpv fail \<I>' f gpv"
proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions expectation_gpv.mono expectation_gpv.mono expectation_gpv_def expectation_gpv_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv' expectation_gpv'')
  show ?case
    by (auto simp add: pmf_map_spmf_None o_def case_map_generat image_comp
      split: generat.split intro!: nn_integral_cong_AE INF_cong step.IH)
qed

lemma pgen_lossless_left_gpv [simp]: "pgen_lossless_gpv fail (\<I> \<oplus>\<^sub>\<I> \<I>') (left_gpv gpv) = pgen_lossless_gpv fail \<I> gpv"
  by(simp add: pgen_lossless_gpv_def)

lemma pgen_lossless_right_gpv [simp]: "pgen_lossless_gpv fail (\<I> \<oplus>\<^sub>\<I> \<I>') (right_gpv gpv) = pgen_lossless_gpv fail \<I>' gpv"
  by(simp add: pgen_lossless_gpv_def)

lemma (in raw_converter_invariant) expectation_gpv_le_inline_invariant:
  defines "expectation_gpv2 \<equiv> expectation_gpv 0 \<I>'"
  assumes callee: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> plossless_gpv \<I>' (callee s x)"
    and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
    and I: "I s"
  shows "expectation_gpv 0 \<I> f gpv \<le> expectation_gpv2 (\<lambda>(x, s). f x) (inline callee gpv s)"
  using WT_gpv I
proof(induction arbitrary: gpv s rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv')
  { fix out c
    assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
    with step.prems(1) have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpv_OutD)
    have "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) = \<integral>\<^sup>+ generat. (INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<partial>measure_spmf (the_gpv (callee s out))"
      using WT_callee[OF out, of s] callee[OF out, of s] step.prems(2)
      by(clarsimp simp add: measure_spmf.emeasure_eq_measure plossless_iff_colossless_pfinite colossless_gpv_lossless_spmfD lossless_weight_spmfD)
    also have "\<dots> \<le> \<integral>\<^sup>+ generat. (case generat of Pure (x, s') \<Rightarrow>
            \<integral>\<^sup>+ xx. (case xx of Inl (x, _) \<Rightarrow> f x 
               | Inr (out', callee', rpv) \<Rightarrow> INF r':responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r, s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv r) s')) (callee' r'))
            \<partial>measure_spmf (inline1 callee (c x) s')
         | IO out' rpv \<Rightarrow> INF r':responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r'))
       \<partial>measure_spmf (the_gpv (callee s out))"
    proof(rule nn_integral_mono_AE; simp split!: generat.split)
      fix x s'
      assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
      hence "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
      with results_callee[OF out step.prems(2)] have x: "x \<in> responses_\<I> \<I> out" and s': "I s'" by blast+
      from this(1) have "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> expectation_gpv' (c x)" by(rule INF_lower)
      also have "\<dots> \<le> expectation_gpv2 (\<lambda>(x, s). f x) (inline callee (c x) s')"
        by(rule step.IH)(rule WT_gpv_ContD[OF step.prems(1) IO x] step.prems s'|assumption)+
      also have "\<dots> = \<integral>\<^sup>+ xx. (case xx of Inl (x, _) \<Rightarrow> f x 
               | Inr (out', callee', rpv) \<Rightarrow> INF r':responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r, s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv r) s')) (callee' r'))
            \<partial>measure_spmf (inline1 callee (c x) s')"
        unfolding expectation_gpv2_def
        by(subst expectation_gpv.simps)(auto simp add: inline_sel split_def o_def intro!: nn_integral_cong split: generat.split sum.split)
      finally show "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> \<dots>" .
    next
      fix out' rpv
      assume IO': "IO out' rpv \<in> set_spmf (the_gpv (callee s out))"
      have "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> (INF (r, s'):(\<Union>r'\<in>responses_\<I> \<I>' out'. results_gpv \<I>' (rpv r')). expectation_gpv' (c r))"
        using IO' results_callee[OF out step.prems(2)] by(intro INF_mono)(auto intro: results_gpv.IO)
      also have "\<dots> = (INF r':responses_\<I> \<I>' out'. INF (r, s'):results_gpv \<I>' (rpv r'). expectation_gpv' (c r))"
        by(simp add: INF_UNION)
      also have "\<dots> \<le> (INF r':responses_\<I> \<I>' out'. expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r'))"
      proof(rule INF_mono, rule bexI)
        fix r'
        assume r': "r' \<in> responses_\<I> \<I>' out'"
        have "(INF (r, s'):results_gpv \<I>' (rpv r'). expectation_gpv' (c r)) \<le> (INF (r, s'):results_gpv \<I>' (rpv r'). expectation_gpv2 (\<lambda>(x, s). f x) (inline callee (c r) s'))"
          using IO IO' step.prems out results_callee[OF out, of s] r'
          by(auto intro!: INF_mono rev_bexI step.IH dest: WT_gpv_ContD intro: results_gpv.IO)
        also have "\<dots> \<le>  expectation_gpv 0 \<I>' (\<lambda>(r', s'). expectation_gpv 0 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (rpv r')"
          unfolding expectation_gpv2_def using plossless_gpv_ContD[OF callee, OF out step.prems(2) IO' r'] WT_callee[OF out step.prems(2)] IO' r'
          by(intro plossless_INF_le_expectation_gpv)(auto intro: WT_gpv_ContD)
        finally show "(INF (r, s'):results_gpv \<I>' (rpv r'). expectation_gpv' (c r)) \<le> \<dots>" .
      qed
      finally show "(INF r:responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> \<dots>" .
    qed
    also note calculation }
  then show ?case unfolding expectation_gpv2_def
    apply(rewrite expectation_gpv.simps)
    apply(rewrite inline_sel)
    apply(simp add: o_def pmf_map_spmf_None)
    apply(rewrite sum.case_distrib[where h="case_generat _ _"])
    apply(simp cong del: sum.case_cong_weak)
    apply(simp add: split_beta o_def cong del: sum.case_cong_weak)
    apply(rewrite inline1.simps)
    apply(rewrite measure_spmf_bind)
    apply(rewrite nn_integral_bind[where B="measure_spmf _"])
      apply simp
     apply(simp add: space_subprob_algebra)
    apply(rule nn_integral_mono_AE)
    apply(clarsimp split!: generat.split)
     apply(simp add: measure_spmf_return_spmf nn_integral_return)
    apply(rewrite measure_spmf_bind)
    apply(simp add: nn_integral_bind[where B="measure_spmf _"] space_subprob_algebra)
    apply(subst generat.case_distrib[where h="measure_spmf"])
    apply(subst generat.case_distrib[where h="\<lambda>x. nn_integral x _"])
    apply(simp add: measure_spmf_return_spmf nn_integral_return split_def)
    done
qed

lemma (in raw_converter_invariant) plossless_inline_invariant:
  assumes lossless: "plossless_gpv \<I> gpv"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and callee: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> plossless_gpv \<I>' (callee s x)"
    and I: "I s"
  shows "plossless_gpv \<I>' (inline callee gpv s)"
  unfolding pgen_lossless_gpv_def
proof(rule antisym)
  have WT': "\<I>' \<turnstile>g inline callee gpv s \<surd>" using WT I by(rule WT_gpv_inline_invar)
  from expectation_gpv_const_le[OF WT', of 0 1]
  show "expectation_gpv 0 \<I>' (\<lambda>_. 1) (inline callee gpv s) \<le> 1" by(simp add: max_def)

  have "1 = expectation_gpv 0 \<I> (\<lambda>_. 1) gpv" using lossless by(simp add: pgen_lossless_gpv_def)
  also have "\<dots> \<le> expectation_gpv 0 \<I>' (\<lambda>_. 1) (inline callee gpv s)"
    by(rule expectation_gpv_le_inline[unfolded split_def]; rule callee WT WT_callee I)
  finally show "1 \<le> \<dots>" .
qed

context callee_invariant_on begin

lemma raw_converter_invariant: "raw_converter_invariant \<I> \<I>' (\<lambda>s x. lift_spmf (callee s x)) I"
  by(unfold_locales)(auto dest: callee_invariant WT_callee WT_calleeD)

lemma (in callee_invariant_on) plossless_exec_gpv:
  assumes lossless: "plossless_gpv \<I> gpv"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and callee: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> lossless_spmf (callee s x)"
    and I: "I s"
  shows "lossless_spmf (exec_gpv callee gpv s)"
proof -
  interpret raw_converter_invariant \<I> \<I>' "\<lambda>s x. lift_spmf (callee s x)" I for \<I>'
    by(rule raw_converter_invariant)
  have "plossless_gpv \<I>_full (inline (\<lambda>s x. lift_spmf (callee s x)) gpv s)"
    using lossless WT by(rule plossless_inline)(simp_all add: callee I)
  from this[THEN plossless_gpv_lossless_spmfD] show ?thesis
    unfolding exec_gpv_conv_inline1 by(simp add: inline_sel)
qed

end

definition extend_state_oracle2 :: "('call, 'ret, 's) callee \<Rightarrow> ('call, 'ret, 's \<times> 's') callee" ("_\<dagger>" [1000] 1000)
  where "extend_state_oracle2 callee = (\<lambda>(s, s') x. map_spmf (\<lambda>(y, s). (y, (s, s'))) (callee s x))"

lemma extend_state_oracle2_simps [simp]:
  "extend_state_oracle2 callee (s, s') x = map_spmf (\<lambda>(y, s). (y, (s, s'))) (callee s x)"
  by(simp add: extend_state_oracle2_def)

lemma extend_state_oracle2_parametric [transfer_rule]: includes lifting_syntax shows
  "((S ===> C ===> rel_spmf (rel_prod R S)) ===> rel_prod S S' ===> C ===> rel_spmf (rel_prod R (rel_prod S S')))
  extend_state_oracle2 extend_state_oracle2"
  unfolding extend_state_oracle2_def[abs_def] by transfer_prover

lemma callee_invariant_extend_state_oracle2_const [simp]:
  "callee_invariant oracle\<dagger> (\<lambda>(s, s'). I s')"
  by unfold_locales auto

lemma callee_invariant_extend_state_oracle2_const':
  "callee_invariant oracle\<dagger> (\<lambda>s. I (snd s))"
  by unfold_locales auto

lemma extend_state_oracle2_plus_oracle: 
  "extend_state_oracle2 (plus_oracle oracle1 oracle2) = plus_oracle (extend_state_oracle2 oracle1) (extend_state_oracle2 oracle2)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases s; cases q) (simp_all add: apfst_def spmf.map_comp o_def split_def)
qed

lemma parallel_oracle_conv_plus_oracle:
  "parallel_oracle oracle1 oracle2 = plus_oracle (oracle1\<dagger>) (\<dagger>oracle2)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases s; cases q) (auto simp add: spmf.map_comp apfst_def o_def split_def map_prod_def)
qed

lemma map_sum_parallel_oracle: includes lifting_syntax shows
  "(id ---> map_sum f g ---> map_spmf (map_prod (map_sum h k) id)) (parallel_oracle oracle1 oracle2)
  = parallel_oracle ((id ---> f ---> map_spmf (map_prod h id)) oracle1) ((id ---> g ---> map_spmf (map_prod k id)) oracle2)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases s; cases q) (simp_all add: spmf.map_comp o_def apfst_def prod.map_comp)
qed

lemma map_sum_plus_oracle: includes lifting_syntax shows
  "(id ---> map_sum f g ---> map_spmf (map_prod (map_sum h k) id)) (plus_oracle oracle1 oracle2)
  = plus_oracle ((id ---> f ---> map_spmf (map_prod h id)) oracle1) ((id ---> g ---> map_spmf (map_prod k id)) oracle2)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases q) (simp_all add: spmf.map_comp o_def apfst_def prod.map_comp)
qed

lemma map_rsuml_plus_oracle: includes lifting_syntax shows
  "(id ---> rsuml ---> (map_spmf (map_prod lsumr id))) (oracle1 \<oplus>\<^sub>O (oracle2 \<oplus>\<^sub>O oracle3)) =
   ((oracle1 \<oplus>\<^sub>O oracle2) \<oplus>\<^sub>O oracle3)"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case 
  proof(cases q)
    case (Inl ql)
    then show ?thesis by(cases ql)(simp_all add: spmf.map_comp o_def apfst_def prod.map_comp)
  qed (simp add: spmf.map_comp o_def apfst_def prod.map_comp id_def)
qed

lemma map_lsumr_plus_oracle: includes lifting_syntax shows
  "(id ---> lsumr ---> (map_spmf (map_prod rsuml id))) ((oracle1 \<oplus>\<^sub>O oracle2) \<oplus>\<^sub>O oracle3) =
   (oracle1 \<oplus>\<^sub>O (oracle2 \<oplus>\<^sub>O oracle3))"
proof((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case 
  proof(cases q)
    case (Inr qr)
    then show ?thesis by(cases qr)(simp_all add: spmf.map_comp o_def apfst_def prod.map_comp)
  qed (simp add: spmf.map_comp o_def apfst_def prod.map_comp id_def)
qed

context includes lifting_syntax begin

definition lift_state_oracle
  :: "(('s \<Rightarrow> 'a \<Rightarrow> (('b \<times> 't) \<times> 's) spmf) \<Rightarrow> ('s' \<Rightarrow> 'a \<Rightarrow> (('b \<times> 't) \<times> 's') spmf)) 
  \<Rightarrow> ('t \<times> 's \<Rightarrow> 'a \<Rightarrow> ('b \<times> 't \<times> 's) spmf) \<Rightarrow> ('t \<times> 's' \<Rightarrow> 'a \<Rightarrow> ('b \<times> 't \<times> 's') spmf)" where
  "lift_state_oracle F oracle = 
   (\<lambda>(t, s') a. map_spmf rprodl (F ((Pair t ---> id ---> map_spmf lprodr) oracle) s' a))"

lemma lift_state_oracle_simps [simp]:
  "lift_state_oracle F oracle (t, s') a = map_spmf rprodl (F ((Pair t ---> id ---> map_spmf lprodr) oracle) s' a)"
  by(simp add: lift_state_oracle_def)

lemma lift_state_oracle_parametric [transfer_rule]: includes lifting_syntax shows
  "(((S ===> A ===> rel_spmf (rel_prod (rel_prod B T) S)) ===> S' ===> A ===> rel_spmf (rel_prod (rel_prod B T) S'))
  ===> (rel_prod T S ===> A ===> rel_spmf (rel_prod B (rel_prod T S)))
  ===> rel_prod T S' ===> A ===> rel_spmf (rel_prod B (rel_prod T S')))
  lift_state_oracle lift_state_oracle"
  unfolding lift_state_oracle_def map_fun_def o_def by transfer_prover

lemma lift_state_oracle_extend_state_oracle:
  includes lifting_syntax
  assumes "\<And>B. Transfer.Rel (((=) ===> (=) ===> rel_spmf (rel_prod B (=))) ===> (=) ===> (=) ===> rel_spmf (rel_prod B (=))) G F"
    (* TODO: implement simproc to discharge parametricity assumptions like this one *)
  shows "lift_state_oracle F (extend_state_oracle oracle) = extend_state_oracle (G oracle)"
  unfolding lift_state_oracle_def extend_state_oracle_def
  apply(clarsimp simp add: fun_eq_iff map_fun_def o_def spmf.map_comp split_def rprodl_def)
  subgoal for t s a
    apply(rule sym)
    apply(fold spmf_rel_eq)
    apply(simp add: spmf_rel_map)
    apply(rule rel_spmf_mono)
     apply(rule assms[unfolded Rel_def, where B="\<lambda>x (y, z). x = y \<and> z = t", THEN rel_funD, THEN rel_funD, THEN rel_funD])
       apply(auto simp add: rel_fun_def spmf_rel_map intro!: rel_spmf_reflI)
    done
  done

lemma lift_state_oracle_compose: 
  "lift_state_oracle F (lift_state_oracle G oracle) = lift_state_oracle (F \<circ> G) oracle"
  by(simp add: lift_state_oracle_def map_fun_def o_def split_def spmf.map_comp)

lemma lift_state_oracle_id [simp]: "lift_state_oracle id = id"
  by(simp add: fun_eq_iff spmf.map_comp o_def)

lemma rprodl_extend_state_oracle: includes lifting_syntax shows
  "(rprodl ---> id ---> map_spmf (map_prod id lprodr)) (extend_state_oracle (extend_state_oracle oracle)) = 
  extend_state_oracle oracle"
  by(simp add: fun_eq_iff spmf.map_comp o_def split_def)

end

lemma interaction_bound_map_gpv':
  assumes "surj h"
  shows "interaction_bound consider (map_gpv' f g h gpv) = interaction_bound (consider \<circ> g) gpv"
proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF lattice_partial_function_definition lattice_partial_function_definition interaction_bound.mono interaction_bound.mono interaction_bound_def interaction_bound_def, case_names adm bottom step])
  case (step interaction_bound' interaction_bound'' gpv)
  have *: "IO out c \<in> set_spmf (the_gpv gpv) \<Longrightarrow>  x \<in> UNIV \<Longrightarrow> interaction_bound'' (c x) \<le> (\<Squnion>x. interaction_bound'' (c (h x)))" for out c x
    using assms[THEN surjD, of x] by (clarsimp intro!: SUP_upper)

  show ?case 
    by (auto simp add: * step.IH image_comp split: generat.split
      intro!: SUP_cong [OF refl] antisym SUP_upper SUP_least)
qed simp_all

lemma interaction_any_bounded_by_map_gpv':
  assumes "interaction_any_bounded_by gpv n"
    and "surj h"
  shows "interaction_any_bounded_by (map_gpv' f g h gpv) n"
  using assms by(simp add: interaction_bounded_by.simps interaction_bound_map_gpv' o_def)

lemma results'_gpv_map_gpv':
  assumes "surj h"
  shows "results'_gpv (map_gpv' f g h gpv) = f ` results'_gpv gpv" (is "?lhs = ?rhs")
proof -
  have *:"IO z c \<in> set_spmf (the_gpv gpv) \<Longrightarrow> x \<in> results'_gpv (c input) \<Longrightarrow>
     f x \<in> results'_gpv (map_gpv' f g h (c input)) \<Longrightarrow> f x \<in> results'_gpv (map_gpv' f g h gpv)" for x z gpv c input
    using surjD[OF assms, of input] by(fastforce intro: results'_gpvI elim!: generat.set_cases intro: rev_image_eqI simp add: map_fun_def o_def)

  show ?thesis 
  proof(intro Set.set_eqI iffI; (elim imageE; hypsubst)?)
    show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
      by(induction gpv'\<equiv>"map_gpv' f g h gpv" arbitrary: gpv)(fastforce elim!: generat.set_cases intro: results'_gpvI)+
    show "f x \<in> ?lhs" if "x \<in> results'_gpv gpv" for x using that
      by induction (fastforce intro: results'_gpvI elim!: generat.set_cases intro: rev_image_eqI simp add: map_fun_def o_def
          , clarsimp simp add: *  elim!: generat.set_cases)
  qed
qed

context fixes B :: "'b \<Rightarrow> 'c set" and x :: 'a begin

primcorec mk_lossless_gpv :: "('a, 'b, 'c) gpv \<Rightarrow> ('a, 'b, 'c) gpv" where
  "the_gpv (mk_lossless_gpv gpv) =
   map_spmf (\<lambda>generat. case generat of Pure x \<Rightarrow> Pure x 
      | IO out c \<Rightarrow> IO out (\<lambda>input. if input \<in> B out then mk_lossless_gpv (c input) else Done x))
    (the_gpv gpv)"

end

lemma WT_gpv_outs_gpvI:
  assumes "outs_gpv \<I> gpv \<subseteq> outs_\<I> \<I>"
  shows "\<I> \<turnstile>g gpv \<surd>"
  using assms by(coinduction arbitrary: gpv)(auto intro: outs_gpv.intros)

lemma WT_gpv_iff_outs_gpv:
  "\<I> \<turnstile>g gpv \<surd> \<longleftrightarrow> outs_gpv \<I> gpv \<subseteq> outs_\<I> \<I>"
  by(blast intro: WT_gpv_outs_gpvI dest: WT_gpv_outs_gpv)

lemma WT_gpv_mk_lossless_gpv:
  assumes "\<I> \<turnstile>g gpv \<surd>"
    and outs: "outs_\<I> \<I>' = outs_\<I> \<I>"
  shows "\<I>' \<turnstile>g mk_lossless_gpv (responses_\<I> \<I>) x gpv \<surd>"
  using assms(1)
  by(coinduction arbitrary: gpv)(auto 4 3 split: generat.split_asm simp add: outs dest: WT_gpvD)

lemma expectation_gpv_mk_lossless_gpv:
  fixes \<I> y
  defines "rhs \<equiv> expectation_gpv 0 \<I> (\<lambda>_. y)"
  assumes WT: "\<I>' \<turnstile>g gpv \<surd>"
    and outs: "outs_\<I> \<I> = outs_\<I> \<I>'"
  shows "expectation_gpv 0 \<I>' (\<lambda>_. y) gpv \<le> rhs (mk_lossless_gpv (responses_\<I> \<I>') x gpv)"
  using WT
proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case step [unfolded rhs_def]: (step expectation_gpv')
  show ?case using step.prems outs unfolding rhs_def
    apply(subst expectation_gpv.simps)
    apply(clarsimp intro!: nn_integral_mono_AE INF_mono split!: generat.split if_split)
    subgoal
      by(frule (1) WT_gpv_OutD)(auto simp add: in_outs_\<I>_iff_responses_\<I> intro!: bexI step.IH[unfolded rhs_def] dest: WT_gpv_ContD)
    apply(frule (1) WT_gpv_OutD; clarsimp simp add: in_outs_\<I>_iff_responses_\<I> ex_in_conv[symmetric])
    subgoal for out c input input'
      using step.hyps[of "c input'"] expectation_gpv_const_le[of \<I>' "c input'" 0 y]
      by- (drule (2) WT_gpv_ContD, fastforce intro: rev_bexI simp add: max_def)
    done
qed

lemma plossless_gpv_mk_lossless_gpv:
  assumes "plossless_gpv \<I> gpv"
    and "\<I> \<turnstile>g gpv \<surd>"
    and "outs_\<I> \<I> = outs_\<I> \<I>'"
  shows "plossless_gpv \<I>' (mk_lossless_gpv (responses_\<I> \<I>) x gpv)"
  using assms expectation_gpv_mk_lossless_gpv[OF assms(2), of \<I>' 1 x]
  unfolding pgen_lossless_gpv_def
  by -(rule antisym[OF expectation_gpv_const_le[THEN order_trans]]; simp add: WT_gpv_mk_lossless_gpv)

lemma (in callee_invariant_on) exec_gpv_mk_lossless_gpv:
  assumes "\<I> \<turnstile>g gpv \<surd>"
    and "I s"
  shows "exec_gpv callee (mk_lossless_gpv (responses_\<I> \<I>) x gpv) s = exec_gpv callee gpv s"
  using assms
proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step exec_gpv')
  show ?case using step.prems WT_gpv_OutD[OF step.prems(1)]
    by(clarsimp simp add: bind_map_spmf intro!: bind_spmf_cong[OF refl] split!: generat.split if_split)
      (force intro!: step.IH dest: WT_callee[THEN WT_calleeD] WT_gpv_OutD callee_invariant WT_gpv_ContD)+
qed

lemma in_results_gpv_restrict_gpvD:
  assumes "x \<in> results_gpv \<I> (restrict_gpv \<I>' gpv)"
  shows "x \<in> results_gpv \<I> gpv"
  using assms
  apply(induction gpv'\<equiv>"restrict_gpv \<I>' gpv" arbitrary: gpv)
   apply(clarsimp split: option.split_asm simp add: in_set_spmf[symmetric])
  subgoal for \<dots> y by(cases y)(auto intro: results_gpv.intros split: if_split_asm)
  apply(clarsimp split: option.split_asm simp add: in_set_spmf[symmetric])
  subgoal for \<dots> y by(cases y)(auto intro: results_gpv.intros split: if_split_asm)
  done

lemma results_gpv_restrict_gpv:
  "results_gpv \<I> (restrict_gpv \<I>' gpv) \<subseteq> results_gpv \<I> gpv"
  by(blast intro: in_results_gpv_restrict_gpvD)

lemma in_results'_gpv_restrict_gpvD:
  "x \<in> results'_gpv (restrict_gpv \<I>' gpv) \<Longrightarrow> x \<in> results'_gpv gpv"
  by(rule in_results_gpv_restrict_gpvD[where \<I> = "\<I>_full", unfolded results_gpv_\<I>_full])

lemma expectation_gpv_map_gpv' [simp]:
  "expectation_gpv fail \<I> f (map_gpv' g h k gpv) =
   expectation_gpv fail (map_\<I> h k \<I>) (f \<circ> g) gpv"
proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions expectation_gpv.mono expectation_gpv.mono expectation_gpv_def expectation_gpv_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step exp1 exp2)
  have "pmf (the_gpv (map_gpv' g h k gpv)) None = pmf (the_gpv gpv) None"
    by(simp add: pmf_map_spmf_None)
  then show ?case 
    by simp
      (auto simp add: nn_integral_measure_spmf step.IH image_comp
        split: generat.split intro!: nn_integral_cong)
qed

lemma plossless_gpv_map_gpv' [simp]:
  "pgen_lossless_gpv b \<I> (map_gpv' f g h gpv) \<longleftrightarrow> pgen_lossless_gpv b (map_\<I> g h \<I>) gpv"
  unfolding pgen_lossless_gpv_def by(simp add: o_def)

end