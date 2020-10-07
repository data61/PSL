(* Author: Andreas Lochbihler, ETH Zurich
   Author: Joshua Schneider, ETH Zurich *)

section \<open>Concrete \BNFCC{}s\<close>

theory Concrete_Examples imports
  Preliminaries
  "HOL-Library.Rewrite"
  "HOL-Library.Cardinality"
begin

context includes lifting_syntax
begin

subsection \<open>Function space\<close>

lemma rel_fun_mono: "(A ===> B) \<le> (A' ===> B')" if "A' \<le> A" "B \<le> B'"
  using that by(auto simp add: rel_fun_def)

lemma rel_fun_eq: "((=) ===> (=)) = (=)" by(fact fun.rel_eq)

lemma rel_fun_conversep: "(A\<inverse>\<inverse> ===> B\<inverse>\<inverse>) = (A ===> B)\<inverse>\<inverse>" by(auto simp add: rel_fun_def)

lemma map_fun_id0: "(id ---> id) = id" by(fact map_fun.id)

lemma map_fun_comp: "(f ---> g) \<circ> (f' ---> g') = ((f' \<circ> f) ---> (g \<circ> g'))" by(fact map_fun.comp)

lemma map_fun_parametric: "((A ===> A') ===> (B ===> B') ===> (A' ===> B) ===> (A ===> B')) (--->) (--->)"
  by(fact map_fun_parametric)

definition rel_fun_pos_distr_cond :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> 'a'' \<Rightarrow> bool) \<Rightarrow>
    ('b \<times> 'b' \<times> 'b'') itself \<Rightarrow> bool" where
  "rel_fun_pos_distr_cond A A' _ \<longleftrightarrow> (\<forall>(B :: 'b \<Rightarrow> 'b' \<Rightarrow> bool) (B' :: 'b' \<Rightarrow> 'b'' \<Rightarrow> bool).
    (A ===> B) OO (A' ===> B') \<le> (A OO A') ===> (B OO B'))"

definition rel_fun_neg_distr_cond :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> 'a'' \<Rightarrow> bool) \<Rightarrow>
    ('b \<times> 'b' \<times> 'b'') itself \<Rightarrow> bool" where
  "rel_fun_neg_distr_cond A A' _ \<longleftrightarrow> (\<forall>(B :: 'b \<Rightarrow> 'b' \<Rightarrow> bool) (B' :: 'b' \<Rightarrow> 'b'' \<Rightarrow> bool).
    (A OO A') ===> (B OO B') \<le> (A ===> B) OO (A' ===> B'))"

lemmas
  rel_fun_pos_distr = rel_fun_pos_distr_cond_def[THEN iffD1, rule_format] and
  rel_fun_neg_distr = rel_fun_neg_distr_cond_def[THEN iffD1, rule_format]

lemma rel_fun_pos_distr_iff [simp]: "rel_fun_pos_distr_cond A A' tytok = True"
  unfolding rel_fun_pos_distr_cond_def by (blast intro!: pos_fun_distr)

lemma rel_fun_neg_distr_imp: "\<lbrakk> left_unique A; right_total A; right_unique A'; left_total A' \<rbrakk> \<Longrightarrow>
  rel_fun_neg_distr_cond A A' tytok"
  unfolding rel_fun_neg_distr_cond_def by (fast elim!: neg_fun_distr1[THEN predicate2D])

lemma rel_fun_pos_distr_cond_eq: "rel_fun_pos_distr_cond (=) (=) tytok"
  by simp

lemma rel_fun_neg_distr_cond_eq: "rel_fun_neg_distr_cond (=) (=) tytok"
  by (blast intro: rel_fun_neg_distr_imp left_unique_eq right_unique_eq right_total_eq left_total_eq)

thm fun.set_map fun.map_cong0 fun.rel_mono_strong


subsection \<open>Covariant powerset\<close>

lemma rel_set_mono: "A \<le> A' \<Longrightarrow> rel_set A \<le> rel_set A'" by(fact rel_set_mono)

lemma rel_set_eq: "rel_set (=) = (=)" by(fact rel_set_eq)

lemma rel_set_conversep: "rel_set A\<inverse>\<inverse> = (rel_set A)\<inverse>\<inverse>" by(fact rel_set_conversep)

lemma map_set_id0: "image id = id" by(fact image_id)

lemma map_set_comp: "image f \<circ> image g = image (f \<circ> g)" by(simp add: fun_eq_iff image_image o_def)

lemma map_set_parametric: includes lifting_syntax shows
  "((A ===> B) ===> rel_set A ===> rel_set B) image image"
  by(fact image_transfer)

definition rel_set_pos_distr_cond :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> 'a'' \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_set_pos_distr_cond A A' \<longleftrightarrow> rel_set A OO rel_set A' \<le> rel_set (A OO A')"

definition rel_set_neg_distr_cond :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> 'a'' \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_set_neg_distr_cond A A' \<longleftrightarrow> rel_set (A OO A') \<le> rel_set A OO rel_set A'"

lemmas
  rel_set_pos_distr = rel_set_pos_distr_cond_def[THEN iffD1, rule_format] and
  rel_set_neg_distr = rel_set_neg_distr_cond_def[THEN iffD1, rule_format]

lemma rel_set_pos_distr_iff [simp]: "rel_set_pos_distr_cond A A' = True"
  unfolding rel_set_pos_distr_cond_def by(simp add: rel_set_OO)

lemma rel_set_neg_distr_iff [simp]: "rel_set_neg_distr_cond A A' = True"
  unfolding rel_set_neg_distr_cond_def by(simp add: rel_set_OO)

lemma rel_set_pos_distr_eq: "rel_set_pos_distr_cond (=) (=)"
  by simp

lemma rel_set_neg_distr_eq: "rel_set_neg_distr_cond (=) (=)"
  by simp


subsection \<open>Bounded sets\<close>

text \<open>
  We define bounded sets as a subtype, with an additional fixed parameter which controls the bound.
  Using the \BNFCC{} structure on the covariant powerset functor, it suffices to show the
  preconditions for the closedness of \BNFCC{} under subtypes.
\<close>

typedef ('a, 'k) bset = "{A :: 'a set. finite A \<and> card A \<le> CARD('k)}"
proof
  show "{} \<in> ?bset" by simp
qed

setup_lifting type_definition_bset

lemma bset_map_closed:
  fixes f A
  defines "B \<equiv> image f A"
  assumes "finite A \<and> card A \<le> CARD('k)"
  shows "finite B \<and> card B \<le> CARD('k)"
  using assms by(auto intro: card_image_le[THEN order_trans])

lift_definition map_bset :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'k) bset \<Rightarrow> ('b, 'k) bset" is image
  by(fact bset_map_closed)

lift_definition rel_bset :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'k) bset \<Rightarrow> ('b, 'k) bset \<Rightarrow> bool" is rel_set .

definition neg_distr_cond_bset :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'k itself \<Rightarrow> bool" where
  "neg_distr_cond_bset C C' _ \<longleftrightarrow> rel_bset (C OO C') \<le> rel_bset C OO (rel_bset C' :: (_, 'k) bset \<Rightarrow> _)"

lemma right_unique_rel_set_lemma:
  assumes "right_unique R" and "rel_set R X Y"
  obtains f where "Y = image f X" and "\<forall>x\<in>X. R x (f x)"
proof
  define f where "f x = (THE y. R x y)" for x
  { fix x assume "x \<in> X"
    with \<open>rel_set R X Y\<close> \<open>right_unique R\<close> have "R x (f x)"
      by (simp add: right_unique_def rel_set_def f_def) (metis theI)
    with assms \<open>x \<in> X\<close> have  "R x (f x)" "f x \<in> Y"
      by (fastforce simp add: right_unique_def rel_set_def)+ }
  moreover
  have "\<exists>x\<in>X. y = f x" if "y \<in> Y" for y using \<open>rel_set R X Y\<close> that
    by(auto simp add: f_def dest!: rel_setD2 dest: right_uniqueD[OF \<open>right_unique R\<close>]
        intro: the_equality[symmetric])
  ultimately show "\<forall>x\<in>X. R x (f x)" "Y = image f X"
    by (auto simp: inj_on_def image_iff)
qed

lemma left_unique_rel_set_lemma:
  assumes "left_unique R" and "rel_set R Y X"
  obtains f where "Y = image f X" and "\<forall>x\<in>X. R (f x) x"
proof
  define f where "f x = (THE y. R y x)" for x
  { fix x assume "x \<in> X"
    with \<open>rel_set R Y X\<close> \<open>left_unique R\<close> have "R (f x) x"
      by (simp add: left_unique_def rel_set_def f_def)  (metis theI)
    with assms \<open>x \<in> X\<close> have  "R (f x) x" "f x \<in> Y"
      by (fastforce simp add: left_unique_def rel_set_def)+ }
  moreover
  have "\<exists>x\<in>X. y = f x" if "y \<in> Y" for y using \<open>rel_set R Y X\<close> that
    by(auto simp add: f_def dest!: rel_setD1 dest: left_uniqueD[OF \<open>left_unique R\<close>]
        intro: the_equality[symmetric])
  ultimately show "\<forall>x\<in>X. R (f x) x" "Y = image f X"
    by (auto simp: inj_on_def image_iff)
qed

lemma neg_distr_cond_bset_right_unique:
  "right_unique C \<Longrightarrow> neg_distr_cond_bset C D tytok"
  unfolding neg_distr_cond_bset_def
  apply(rule predicate2I)
  apply transfer
  apply(auto 6 2 intro: card_image_le[THEN order_trans] elim: right_unique_rel_set_lemma
      simp add: rel_set_OO[symmetric])
  done

lemma neg_distr_cond_bset_left_unique:
  "left_unique D \<Longrightarrow> neg_distr_cond_bset C D tytok"
  unfolding neg_distr_cond_bset_def
  apply(rule predicate2I)
  apply transfer
  apply(auto 6 2 intro: card_image_le[THEN order_trans] elim: left_unique_rel_set_lemma
      simp add: rel_set_OO[symmetric])
  done

lemma neg_distr_cond_bset_eq: "neg_distr_cond_bset (=) (=) tytok"
  by (intro neg_distr_cond_bset_right_unique right_unique_eq)


subsection \<open>Contravariant powerset (sets as predicates)\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

definition map_pred :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a pred \<Rightarrow> 'b pred" where
  "map_pred f = (f ---> id)"

definition rel_pred :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a pred \<Rightarrow> 'b pred \<Rightarrow> bool" where
  "rel_pred R = (R ===> (\<longleftrightarrow>))"

lemma rel_pred_mono: "A' \<le> A \<Longrightarrow> rel_pred A \<le> rel_pred A'" unfolding rel_pred_def
  by(auto elim!: rel_fun_mono)

lemma rel_pred_eq: "rel_pred (=) = (=)"
  by(simp add: rel_pred_def rel_fun_eq)

lemma rel_pred_conversep: "rel_pred A\<inverse>\<inverse> = (rel_pred A)\<inverse>\<inverse>"
  using rel_fun_conversep[of _ "(=)"] by (simp add: rel_pred_def)

lemma map_pred_id0: "map_pred id = id"
  by (simp add: map_pred_def map_fun_id)

lemma map_pred_comp: "map_pred f \<circ> map_pred g = map_pred (g \<circ> f)"
  using map_fun_comp[where g=id and g'=id] by (simp add: map_pred_def)

lemma map_pred_parametric: "((A' ===> A) ===> rel_pred A ===> rel_pred A') map_pred map_pred"
  by (simp add: rel_fun_def rel_pred_def map_pred_def)

definition rel_pred_pos_distr_cond :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> 'a'' \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_pred_pos_distr_cond A B \<longleftrightarrow> rel_pred A OO rel_pred B \<le> rel_pred (A OO B)"

definition rel_pred_neg_distr_cond :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> 'a'' \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_pred_neg_distr_cond A B \<longleftrightarrow>  rel_pred (A OO B) \<le> rel_pred A OO rel_pred B"

lemmas
  rel_pred_pos_distr = rel_pred_pos_distr_cond_def[THEN iffD1, rule_format] and
  rel_pred_neg_distr = rel_pred_neg_distr_cond_def[THEN iffD1, rule_format]

lemma rel_pred_pos_distr_iff [simp]: "rel_pred_pos_distr_cond A B = True"
  unfolding rel_pred_pos_distr_cond_def by (auto simp add: rel_pred_def rel_fun_def)

lemma rel_pred_pos_distr_cond_eq: "rel_pred_pos_distr_cond (=) (=)"
  by simp

lemma neg_fun_distr3:
  assumes 1: "left_unique R" "right_total R"
    and 2: "right_unique S" "left_total S"
  shows "rel_fun (R OO R') (S OO S') \<le> rel_fun R S OO rel_fun R' S'"
  using functional_converse_relation[OF 1] functional_relation[OF 2]
  unfolding rel_fun_def OO_def
  apply clarify
  apply (subst all_comm)
  apply (subst all_conj_distrib[symmetric])
  apply (intro choice)
  by metis

text \<open>
  As there are no live variables, we can get a weaker condition than if we derived it
  from @{const rel_fun}'s condition!
\<close>

lemma rel_pred_neg_distr_imp:
  "right_unique B \<and> left_total B \<or> left_unique A \<and> right_total A \<Longrightarrow> rel_pred_neg_distr_cond A B"
  unfolding rel_pred_neg_distr_cond_def rel_pred_def
  apply(clarsimp simp add: vimage2p_def rel_pred_neg_distr_cond_def)
  apply(rewrite in "rel_fun _ \<hole>" in asm eq_OO[symmetric])
  apply(elim disjE)
   apply(drule neg_fun_distr2[THEN predicate2D, rotated -1];
      (simp add: left_unique_eq right_unique_eq left_total_eq right_total_eq)?)
  apply(drule neg_fun_distr3[THEN predicate2D, rotated -1];
      (simp add: left_unique_eq right_unique_eq left_total_eq right_total_eq)?)
  done

lemma rel_pred_neg_distr_cond_eq: "rel_pred_neg_distr_cond (=) (=)"
  by(blast intro: rel_pred_neg_distr_imp left_unique_eq right_total_eq)


lemma left_unique_rel_pred: "left_total A \<Longrightarrow> left_unique (rel_pred A)"
  unfolding rel_pred_def by (erule left_unique_fun) (rule left_unique_eq)

lemma right_unique_rel_pred: "right_total A \<Longrightarrow> right_unique (rel_pred A)"
  unfolding rel_pred_def by (erule right_unique_fun) (rule right_unique_eq)

lemma left_total_rel_pred: "left_unique A \<Longrightarrow> left_total (rel_pred A)"
  unfolding rel_pred_def by (erule left_total_fun) (rule left_total_eq)

lemma right_total_rel_pred: "right_unique A \<Longrightarrow> right_total (rel_pred A)"
  unfolding rel_pred_def by (erule right_total_fun) (rule right_total_eq)

end (* context includes lifting_syntax *)


subsection \<open>Filter\<close>

text \<open>
  Similarly to bounded sets, we exploit the definition of filters as a subtype in order to
  lift the \BNFCC{} operations. Here we use that the @{const is_filter} predicate is closed under
  zippings.
\<close>

lemma map_filter_closed:
  includes lifting_syntax
  assumes "is_filter F"
  shows "is_filter (((f ---> id) ---> id) F)"
proof -
  define F' where "F' = Abs_filter F"
  have "is_filter (((f ---> id) ---> id) (\<lambda>P. eventually P F'))"
    by (rule is_filter.intro)(auto elim!: eventually_rev_mp simp add: map_fun_def o_def)
  then show ?thesis using assms by(simp add: F'_def eventually_Abs_filter)
qed

definition rel_pred2_neg_distr_cond :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> 'a'' \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_pred2_neg_distr_cond A B \<longleftrightarrow>
  rel_pred (rel_pred (A OO B)) \<le> rel_pred (rel_pred A) OO rel_pred (rel_pred B)"

consts rel_pred2_witness :: "('a \<Rightarrow> 'a' \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> 'a'' \<Rightarrow> bool) \<Rightarrow>
  (('a \<Rightarrow> bool) \<Rightarrow> bool) \<times> (('a'' \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> ('a' \<Rightarrow> bool) \<Rightarrow> bool"

specification (rel_pred2_witness)
  rel_pred2_witness1: "\<And>K K' x y. \<lbrakk> rel_pred2_neg_distr_cond K K'; rel_pred (rel_pred (K OO K')) x y \<rbrakk> \<Longrightarrow>
    rel_pred (rel_pred K) x (rel_pred2_witness K K' (x, y))"
  rel_pred2_witness2: "\<And>K K' x y. \<lbrakk> rel_pred2_neg_distr_cond K K'; rel_pred (rel_pred (K OO K')) x y \<rbrakk> \<Longrightarrow>
    rel_pred (rel_pred K') (rel_pred2_witness K K' (x, y)) y"
  apply (rule exI[of _ "\<lambda>K K' (x, y). SOME z. rel_pred (rel_pred K) x z \<and> rel_pred (rel_pred K') z y"])
  apply (fold all_conj_distrib)
  apply (intro allI)
  apply (fold imp_conjR)
  apply (clarify)
  apply (rule relcomppE[of "rel_pred (rel_pred _)" "rel_pred (rel_pred _)", rotated])
   apply (rule someI[where P="\<lambda>z. rel_pred (rel_pred _) _ z \<and> rel_pred (rel_pred _) z _"])
   apply (erule (1) conjI)
  apply (auto simp add: rel_pred2_neg_distr_cond_def)
  done

lemmas rel_pred2_witness = rel_pred2_witness1 rel_pred2_witness2

context includes lifting_syntax
begin

definition rel_filter_neg_distr_cond' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_filter_neg_distr_cond' C C' \<longleftrightarrow> left_total C \<and> right_unique C \<or> right_total C' \<and> left_unique C'"

lemma rel_filter_neg_distr_cond'_stronger:
  assumes "rel_filter_neg_distr_cond' C C'"
  shows "rel_pred2_neg_distr_cond C C'"
  unfolding rel_pred2_neg_distr_cond_def
proof -
  have "rel_pred (rel_pred (C OO C')) \<le> rel_pred (rel_pred C OO rel_pred C')"
    by (auto intro!: rel_pred_mono rel_pred_pos_distr)
  also have "... \<le> rel_pred (rel_pred C) OO rel_pred (rel_pred C')"
    apply (rule rel_pred_neg_distr)
    apply (rule rel_pred_neg_distr_imp)
    apply (insert assms[unfolded rel_filter_neg_distr_cond'_def])
    by (blast dest: left_unique_rel_pred right_total_rel_pred right_unique_rel_pred left_total_rel_pred)
  finally show "rel_pred (rel_pred (C OO C')) \<le> ..." .
qed

lemma rel_filter_neg_distr_cond'_eq: "rel_filter_neg_distr_cond' (=) (=)"
  unfolding rel_filter_neg_distr_cond'_def by (simp add: left_total_eq right_unique_eq)

lemma is_filter_rel_witness:
  assumes F: "is_filter F" and G: "is_filter G"
    and FG: "rel_pred (rel_pred (C OO C')) F G"
    and cond: "rel_filter_neg_distr_cond' C C'"
  shows "is_filter (rel_pred2_witness C C' (F, G))"
proof
  let ?C = "rel_pred (rel_pred C)" and ?C' = "rel_pred (rel_pred C')"
  let ?wit = "rel_pred2_witness C C' (F, G)"
  have "rel_pred2_neg_distr_cond C C'"
    using cond by (rule rel_filter_neg_distr_cond'_stronger)
  with FG have wit1: "?C F ?wit" and wit2: "?C' ?wit G"
    by (rule rel_pred2_witness[rotated])+
  from wit1[unfolded rel_pred_def, THEN rel_funD, of "\<lambda>_. True" "\<lambda>_. True"] F
  show "?wit (\<lambda>_. True)" by (auto simp add: is_filter.True)

  fix P Q
  have *: "(?wit P \<longrightarrow> ?wit Q \<longrightarrow> ?wit (\<lambda>x. P x \<and> Q x)) \<and> (?wit P \<longrightarrow> (\<forall>x. P x \<longrightarrow> Q x) \<longrightarrow> ?wit Q)"
    using cond unfolding rel_filter_neg_distr_cond'_def
  proof(elim disjE conjE; use nothing in \<open>intro conjI strip\<close>)
    assume "left_total C" "right_unique C"
    hence "left_unique (C ===> (=))" "right_total (C ===> (=))"
      by(blast intro: left_unique_fun left_unique_eq right_total_fun right_total_eq)+
    from functional_converse_relation[OF this] obtain P' Q'
      where P' [transfer_rule]: "(C ===> (=)) P' P" and Q' [transfer_rule]: "(C ===> (=)) Q' Q"
      by fastforce
    have PQ: "(C ===> (=)) (\<lambda>x. P' x \<and> Q' x) (\<lambda>x. P x \<and> Q x)" by transfer_prover

    with wit1 P' Q' have P: "?wit P \<longleftrightarrow> F P'" and Q: "?wit Q \<longleftrightarrow> F Q'"
      and PQ: "?wit (\<lambda>x. P x \<and> Q x) \<longleftrightarrow> F (\<lambda>x. P' x \<and> Q' x)"
      by(auto dest: rel_funD simp add: rel_pred_def)

    show "?wit (\<lambda>x. P x \<and> Q x)" if "?wit P" "?wit Q" using that P Q PQ
      by(auto intro: is_filter.conj[OF F])

    assume "\<forall>x. P x \<longrightarrow> Q x"
    with P' Q' \<open>left_total C\<close> have "\<forall>x. P' x \<longrightarrow> Q' x" by(metis (full_types) apply_rsp' left_total_def)
    then show "?wit Q" if "?wit P" using P Q that by(simp add: is_filter.mono[OF F])
  next
    assume "right_total C'" "left_unique C'"
    hence "right_unique (C' ===> (=))" "left_total (C' ===> (=))"
      by(blast intro: right_unique_fun right_unique_eq left_total_fun left_total_eq)+
    from functional_relation[OF this] obtain P' Q'
      where P' [transfer_rule]: "(C' ===> (=)) P P'" and Q' [transfer_rule]: "(C' ===> (=)) Q Q'"
      by fastforce
    have PQ: "(C' ===> (=)) (\<lambda>x. P x \<and> Q x) (\<lambda>x. P' x \<and> Q' x)" by transfer_prover

    with wit2 P' Q' have P: "?wit P \<longleftrightarrow> G P'" and Q: "?wit Q \<longleftrightarrow> G Q'"
      and PQ: "?wit (\<lambda>x. P x \<and> Q x) \<longleftrightarrow> G (\<lambda>x. P' x \<and> Q' x)"
      by(auto dest: rel_funD simp add: rel_pred_def)
    show "?wit (\<lambda>x. P x \<and> Q x)" if "?wit P" "?wit Q" using that P Q PQ
      by(auto intro: is_filter.conj[OF G])

    assume "\<forall>x. P x \<longrightarrow> Q x"
    with P' Q' \<open>right_total C'\<close> have "\<forall>x. P' x \<longrightarrow> Q' x" by(metis (full_types) apply_rsp' right_total_def)
    then show "?wit Q" if "?wit P" using P Q that by(simp add: is_filter.mono[OF G])
  qed
  show "?wit (\<lambda>x. P x \<and> Q x)" if P: "?wit P" and Q: "?wit Q" using * that by simp
  show "?wit Q" if P: "?wit P" and imp: "\<forall>x. P x \<longrightarrow> Q x" using * that by simp
qed

end (* context includes lifting_syntax *)


text \<open>The following example shows that filters do not satisfy @{command lift_bnf}'s condition.\<close>

experiment begin
unbundle lifting_syntax

definition "raw_filtermap f = ((f ---> id) ---> id)"

lemma raw_filtermap_apply: "raw_filtermap f F = (\<lambda>P. F (\<lambda>x. P (f x)))"
  unfolding raw_filtermap_def
  by (simp add: map_fun_def comp_def)

lemma "filtermap f = Abs_filter \<circ> raw_filtermap f \<circ> Rep_filter"
  unfolding filtermap_def eventually_def
  by (simp add: fun_eq_iff raw_filtermap_apply)

definition Z where
  "Z = {{(False, False), (False, True)}, {(False, False), (True, False)},
    {(False, False), (False, True), (True, False), (True, True)}}"

abbreviation "Z' \<equiv> (\<lambda>P. Collect P \<in> Z)"

lemma "is_filter (raw_filtermap fst Z')"
  unfolding Z_def raw_filtermap_apply
  apply (rule is_filter.intro)
    apply (simp add: set_eq_iff; smt)+
  done

lemma "is_filter (raw_filtermap snd Z')"
  unfolding Z_def raw_filtermap_apply
  apply (rule is_filter.intro)
    apply (simp add: set_eq_iff; smt)+
  done

lemma "\<not> is_filter Z'"
  apply (rule)
  apply (drule is_filter.mono[of _ "\<lambda>x. x \<in> {(False, False), (False, True)}"
        "\<lambda>x. x \<in> {(False, False), (False, True), (True, False)}"])
    apply (auto 3 0 simp add: Z_def)
  done

end (* experiment *)


subsection \<open>Almost-everywhere equal sequences\<close>

inductive aeseq_eq :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool" for f g where
  "aeseq_eq f g" if "finite {n. f n \<noteq> g n}"

lemma equivp_aeseq_eq: "equivp aeseq_eq"
proof(rule equivpI)
  show "reflp aeseq_eq" by(simp add: reflp_def aeseq_eq.simps)
  show "symp aeseq_eq" by(simp add: symp_def aeseq_eq.simps eq_commute)
  have "finite {n. f n \<noteq> h n}" if "finite {n. f n \<noteq> g n}" "finite {n. g n \<noteq> h n}"
    for f g h :: "nat \<Rightarrow> 'b"
    using finite_subset[of "{n. f n \<noteq> h n}" "{n. f n \<noteq> g n} \<union> {n. g n \<noteq> h n}"] that
    by(fastforce intro: finite_subset)
  then show "transp aeseq_eq" by(auto simp add: transp_def aeseq_eq.simps)
qed

quotient_type 'a aeseq = "nat \<Rightarrow> 'a" / aeseq_eq by(rule equivp_aeseq_eq)

lift_definition map_aeseq :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a aeseq \<Rightarrow> 'b aeseq" is "(\<circ>)"
  by(auto simp add: aeseq_eq.simps elim: finite_subset[rotated])

lemma map_aeseq_id: "map_aeseq id x = x"
  by transfer(simp add: equivp_reflp[OF equivp_aeseq_eq])

lemma map_aeseq_comp: "map_aeseq f (map_aeseq g x) = map_aeseq (f \<circ> g) x"
  by transfer(simp add: o_assoc equivp_reflp[OF equivp_aeseq_eq])

lift_definition rel_aeseq :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a aeseq \<Rightarrow> 'b aeseq \<Rightarrow> bool" is
  "\<lambda>R f g. finite {n. \<not> R (f n) (g n)}"
proof(unfold aeseq_eq.simps)
  show "finite {n. \<not> R (f n) (g n)} \<longleftrightarrow> finite {n. \<not> R (f' n) (g' n)}"
    if ff': "finite {n. f n \<noteq> f' n}" and gg': "finite {n. g n \<noteq> g' n}"
    for R and f f' :: "nat \<Rightarrow> 'a" and g g' :: "nat \<Rightarrow> 'b"
  proof(rule iffI)
    assume "finite {n. \<not> R (f n) (g n)}"
    with ff' gg' have "finite ({n. \<not> R (f n) (g n)} \<union> {n. f n \<noteq> f' n} \<union> {n. g n \<noteq> g' n})" by simp
    then show "finite {n. \<not> R (f' n) (g' n)}" by(rule finite_subset[rotated]) auto
  next
    assume "finite {n. \<not> R (f' n) (g' n)}"
    with ff' gg' have "finite ({n. \<not> R (f' n) (g' n)} \<union> {n. f n \<noteq> f' n} \<union> {n. g n \<noteq> g' n})" by simp
    then show "finite {n. \<not> R (f n) (g n)}" by(rule finite_subset[rotated]) auto
  qed
qed

lemma rel_aeseq_mono: "R \<le> S \<Longrightarrow> rel_aeseq R \<le> rel_aeseq S"
  by(rule predicate2I; transfer; auto intro: finite_subset[rotated])

lemma rel_aeseq_eq: "rel_aeseq (=) = (=)"
  by(intro ext; transfer; simp add: aeseq_eq.simps)

lemma rel_aeseq_conversep: "rel_aeseq R\<inverse>\<inverse> = (rel_aeseq R)\<inverse>\<inverse>"
  by(simp add: fun_eq_iff; transfer; simp)

lemma map_aeseq_parametric: includes lifting_syntax shows
  "((A ===> B) ===> rel_aeseq A ===> rel_aeseq B) map_aeseq map_aeseq"
  by(intro rel_funI; transfer; auto elim: finite_subset[rotated] dest: rel_funD)

lemma rel_aeseq_distr: "rel_aeseq (R OO S) = rel_aeseq R OO rel_aeseq S"
  apply(intro ext)
  apply(transfer fixing: R S)
  apply(safe)
  subgoal for f h
    apply(rule relcomppI[where b="\<lambda>n. SOME z. R (f n) z \<and> S z (h n)"])
    apply(auto elim!: finite_subset[rotated] intro: someI2)
    done
  subgoal for f h g
    apply(rule finite_subset[where B="{n. \<not> R (f n) (g n)} \<union> {n. \<not> S (g n) (h n)}"])
    apply auto
    done
  done

end
