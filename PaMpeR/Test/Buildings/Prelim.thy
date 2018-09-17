section {* Preliminaries *}

text {*
  In this section, we establish some basic facts about natural numbers, logic, sets, functions and
  relations, lists, and orderings and posets, that are either not available in the HOL library or
  are in a form not suitable for our purposes.
*}

theory Prelim
imports Main

begin

subsection {* Natural numbers *}

lemma nat_cases_2Suc [case_names 0 1 SucSuc]:
  assumes      0: "n = 0 \<Longrightarrow> P"
  and          1: "n = 1 \<Longrightarrow> P"
  and     SucSuc: "\<And>m. n = Suc (Suc m) \<Longrightarrow> P"
  shows "P"
proof (cases n)
  case (Suc m) with 1 SucSuc show ?thesis by (cases m) auto
qed (simp add: 0)

lemma nat_even_induct [case_names _ 0 SucSuc]:
  assumes   even: "even n"
  and          0: "P 0"
  and     SucSuc: "\<And>m. even m \<Longrightarrow> P m \<Longrightarrow> P (Suc (Suc m))"
  shows   "P n"
proof-
  from assms obtain k where "n = 2*k" using evenE by auto
  moreover from assms have "P (2*k)" by (induct k) auto
  ultimately show ?thesis by fast
qed  

lemma nat_induct_step2 [case_names 0 1 SucSuc]:
  assumes      0: "P 0"
  and          1: "P 1"
  and     SucSuc: "\<And>m. P m \<Longrightarrow> P (Suc (Suc m))"
  shows   "P n"
proof (cases "even n")
  case True
  from this obtain k where "n = 2*k" using evenE by auto
  moreover have "P (2*k)" using 0 SucSuc by (induct k) auto
  ultimately show ?thesis by fast
next
  case False
  from this obtain k where "n = 2*k+1" using oddE by blast
  moreover have "P (2*k+1)" using 1 SucSuc by (induct k) auto
  ultimately show ?thesis by fast
qed


subsection {* Logic *}

lemma ex1_unique: "\<exists>!x. P x \<Longrightarrow> P a \<Longrightarrow> P b \<Longrightarrow> a=b"
  by blast

lemma not_the1:
  assumes "\<exists>!x. P x" "y \<noteq> (THE x. P x)"
  shows   "\<not> P y"
  using assms(2) the1_equality[OF assms(1)]
  by    auto

lemma two_cases [case_names both one other neither]:
  assumes both   : "P \<Longrightarrow> Q \<Longrightarrow> R"
  and     one    : "P \<Longrightarrow> \<not>Q \<Longrightarrow> R"
  and     other  : "\<not>P \<Longrightarrow> Q \<Longrightarrow> R"
  and     neither: "\<not>P \<Longrightarrow> \<not>Q \<Longrightarrow> R"
  shows   "R"
  using   assms
  by      fast


subsection {* Sets *}

lemma bex1_equality: "\<lbrakk> \<exists>!x\<in>A. P x; x\<in>A; P x; y\<in>A; P y \<rbrakk> \<Longrightarrow> x=y"
  by blast

lemma prod_ballI: "(\<And>a b. (a,b)\<in>A \<Longrightarrow> P a b) \<Longrightarrow> \<forall>(a,b)\<in>A. P a b"
  by fast

lemmas seteqI = set_eqI[OF iffI]

lemma set_decomp_subset:
  "\<lbrakk> U = A\<union>B; A\<subseteq>X; B\<subseteq>Y; X\<subseteq>U; X\<inter>Y = {} \<rbrakk> \<Longrightarrow> A = X"
  by auto

lemma insert_subset_equality: "\<lbrakk> a\<notin>A; a\<notin>B; insert a A = insert a B \<rbrakk> \<Longrightarrow> A=B"
  by auto

lemma insert_compare_element: "a\<notin>A \<Longrightarrow> insert b A = insert a A \<Longrightarrow> b=a"
  by auto

lemma card1:
  assumes "card A = 1"
  shows "\<exists>a. A = {a}"
proof-
  from assms obtain a where a: "a \<in> A" by fastforce
  with assms show ?thesis using card_ge_0_finite[of A] card_subset_eq[of A "{a}"] by auto
qed

lemma singleton_pow: "a\<in>A \<Longrightarrow> {a}\<in>Pow A"
  using Pow_mono Pow_top by fast

definition separated_by :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "separated_by w x y \<equiv> \<exists>A B. w={A,B} \<and> x\<in>A \<and> y\<in>B"

lemma separated_byI: "x\<in>A \<Longrightarrow> y\<in>B \<Longrightarrow> separated_by {A,B} x y"
  using separated_by_def by fastforce

lemma separated_by_disjoint: "\<lbrakk> separated_by {A,B} x y; A\<inter>B={}; x\<in>A \<rbrakk> \<Longrightarrow> y\<in>B"
  unfolding separated_by_def by fast

lemma separated_by_in_other: "separated_by {A,B} x y \<Longrightarrow> x\<notin>A \<Longrightarrow> x\<in>B \<and> y\<in>A"
  unfolding separated_by_def by auto

lemma separated_by_not_empty: "separated_by w x y \<Longrightarrow> w\<noteq>{}"
  unfolding separated_by_def by fast

lemma not_self_separated_by_disjoint: "A\<inter>B={} \<Longrightarrow> \<not> separated_by {A,B} x x"
  unfolding separated_by_def by auto

subsection {* Functions and relations *}

subsubsection {* Miscellaneous *}

lemma cong_let: "(let x = y in f x) = f y" by simp

lemma sym_sym: "sym (A\<times>A)" by (fast intro: symI)

lemma trans_sym: "trans (A\<times>A)" by (fast intro: transI)

lemma map_prod_sym: "sym A \<Longrightarrow> sym (map_prod f f ` A)"
  using symD[of A] map_prod_def by (fast intro: symI)

abbreviation restrict1 :: "('a\<Rightarrow>'a) \<Rightarrow> 'a set \<Rightarrow> ('a\<Rightarrow>'a)"
  where "restrict1 f A \<equiv> (\<lambda>a. if a\<in>A then f a else a)"

lemma restrict1_image: "B\<subseteq>A \<Longrightarrow> restrict1 f A ` B = f`B"
  by auto

subsubsection {* Equality of functions restricted to a set *}

definition "fun_eq_on f g A \<equiv> (\<forall>a\<in>A. f a = g a)"

lemma fun_eq_onI: "(\<And>a. a\<in>A \<Longrightarrow> f a = g a) \<Longrightarrow> fun_eq_on f g A"
  using fun_eq_on_def by fast

lemma fun_eq_onD: "fun_eq_on f g A \<Longrightarrow> a \<in> A \<Longrightarrow> f a = g a"
  using fun_eq_on_def by fast

lemma fun_eq_on_UNIV: "(fun_eq_on f g UNIV) = (f=g)"
  unfolding fun_eq_on_def by fast

lemma fun_eq_on_subset: "fun_eq_on f g A \<Longrightarrow> B\<subseteq>A \<Longrightarrow> fun_eq_on f g B"
  unfolding fun_eq_on_def by fast

lemma fun_eq_on_sym: "fun_eq_on f g A \<Longrightarrow> fun_eq_on g f A"
  using fun_eq_onD by (fastforce intro: fun_eq_onI)

lemma fun_eq_on_trans: "fun_eq_on f g A \<Longrightarrow> fun_eq_on g h A \<Longrightarrow> fun_eq_on f h A"
  using fun_eq_onD fun_eq_onD by (fastforce intro: fun_eq_onI)

lemma fun_eq_on_cong: "fun_eq_on f h A \<Longrightarrow> fun_eq_on g h A \<Longrightarrow> fun_eq_on f g A"
  using fun_eq_on_trans fun_eq_on_sym by fastforce

lemma fun_eq_on_im : "fun_eq_on f g A \<Longrightarrow> B\<subseteq>A \<Longrightarrow> f`B = g`B"
  using fun_eq_onD by force

lemma fun_eq_on_subset_and_diff_imp_eq_on:
  assumes "A\<subseteq>B" "fun_eq_on f g A" "fun_eq_on f g (B-A)"
  shows   "fun_eq_on f g B"
proof (rule fun_eq_onI)
  fix x assume "x\<in>B" with assms(1) show "f x = g x"
    using fun_eq_onD[OF assms(2)] fun_eq_onD[OF assms(3)]
    by    (cases "x\<in>A") auto    
qed

lemma fun_eq_on_set_and_comp_imp_eq:
  "fun_eq_on f g A \<Longrightarrow> fun_eq_on f g (-A) \<Longrightarrow> f = g"
  using fun_eq_on_subset_and_diff_imp_eq_on[of A UNIV]
  by    (simp add: Compl_eq_Diff_UNIV fun_eq_on_UNIV)

lemma fun_eq_on_bij_betw: "fun_eq_on f g A \<Longrightarrow> bij_betw f A B = bij_betw g A B"
  using bij_betw_cong unfolding fun_eq_on_def by fast

lemma fun_eq_on_restrict1: "fun_eq_on (restrict1 f A) f A"
  by (auto intro: fun_eq_onI) 

abbreviation "fixespointwise f A \<equiv> fun_eq_on f id A"

lemmas fixespointwiseI           = fun_eq_onI       [of   _ _ id]
lemmas fixespointwiseD           = fun_eq_onD       [of     _ id]
lemmas fixespointwise_cong       = fun_eq_on_trans  [of _ _ _ id]
lemmas fixespointwise_subset     = fun_eq_on_subset [of     _ id]
lemmas fixespointwise2_imp_eq_on = fun_eq_on_cong   [of     _ id]

lemmas fixespointwise_subset_and_diff_imp_eq_on =
  fun_eq_on_subset_and_diff_imp_eq_on[of _ _ _ id]

lemma id_fixespointwise: "fixespointwise id A"
  using fun_eq_on_def by fast

lemma fixespointwise_im: "fixespointwise f A \<Longrightarrow> B\<subseteq>A \<Longrightarrow> f`B = B"
  by (auto simp add: fun_eq_on_im)

lemma fixespointwise_comp:
  "fixespointwise f A \<Longrightarrow> fixespointwise g A \<Longrightarrow> fixespointwise (g\<circ>f) A"
  unfolding fun_eq_on_def by simp

lemma fixespointwise_insert:
  assumes "fixespointwise f A" "f ` (insert a A) = insert a A"
  shows   "fixespointwise f (insert a A)"
  using   assms(2) insert_compare_element[of a A "f a"]
          fixespointwiseD[OF assms(1)] fixespointwise_im[OF assms(1)]
  by      (cases "a\<in>A") (auto intro: fixespointwiseI)

lemma fixespointwise_restrict1:
  "fixespointwise f A \<Longrightarrow> fixespointwise (restrict1 f B) A"
  using fixespointwiseD[of f] by (auto intro: fixespointwiseI)

lemma fold_fixespointwise:
  "\<forall>x\<in>set xs. fixespointwise (f x) A \<Longrightarrow> fixespointwise (fold f xs) A"
proof (induct xs)
  case Nil show ?case using id_fixespointwise subst[of id] by fastforce
next
  case (Cons x xs)
  hence "fixespointwise (fold f xs \<circ> f x) A" 
    using fixespointwise_comp[of "f x" A "fold f xs"] by fastforce
  moreover have "fold f xs \<circ> f x = fold f (x#xs)" by simp
  ultimately show ?case using subst[of _ _ "\<lambda>f. fixespointwise f A"] by fast
qed

lemma funpower_fixespointwise:
  assumes "fixespointwise f A"
  shows   "fixespointwise (f^^n) A"
proof (induct n)
  case 0 show ?case using id_fixespointwise subst[of id] by fastforce
next
  case (Suc m)
  with assms have "fixespointwise (f \<circ> (f^^m)) A"
    using fixespointwise_comp by fast
  moreover have "f \<circ> (f^^m) = f^^(Suc m)" by simp
  ultimately show ?case using subst[of _ _ "\<lambda>f. fixespointwise f A"] by fast
qed

subsubsection {* Injectivity, surjectivity, bijectivity, and inverses *}

lemma inj_on_to_singleton:
  assumes "inj_on f A" "f`A = {b}"
  shows "\<exists>a. A = {a}"
proof-
  from assms(2) obtain a where a: "a\<in>A" "f a = b" by force
  with assms have "A = {a}" using inj_onD[of f A] by blast
  thus ?thesis by fast
qed

lemmas inj_inj_on = subset_inj_on[of _ UNIV, OF _ subset_UNIV]

lemma inj_on_eq_image': "\<lbrakk> inj_on f A; X\<subseteq>A; Y\<subseteq>A; f`X\<subseteq>f`Y \<rbrakk> \<Longrightarrow> X\<subseteq>Y"
  unfolding inj_on_def by fast

lemma inj_on_eq_image: "\<lbrakk> inj_on f A; X\<subseteq>A; Y\<subseteq>A; f`X=f`Y \<rbrakk> \<Longrightarrow> X=Y"
  using inj_on_eq_image'[of f A X Y] inj_on_eq_image'[of f A Y X] by simp

lemmas inj_eq_image = inj_on_eq_image[OF _ subset_UNIV subset_UNIV]

lemma induced_pow_fun_inj_on:
  assumes "inj_on f A"
  shows   "inj_on ((`) f) (Pow A)"
  using   inj_onD[OF assms] inj_onI[of "Pow A" "(`) f"]
  by      blast

lemma inj_on_minus_set: "inj_on ((-) A) (Pow A)"
  by (fast intro: inj_onI)

lemma induced_pow_fun_surj:
  "((`) f) ` (Pow A) = Pow (f`A)"
proof (rule seteqI)
  fix X show "X \<in> ((`) f) ` (Pow A) \<Longrightarrow> X \<in> Pow (f`A)" by fast
next
  fix Y assume Y: "Y \<in> Pow (f`A)"
  moreover hence "Y = f`{a\<in>A. f a \<in> Y}" by fast
  ultimately show "Y\<in> ((`) f) ` (Pow A)" by auto
qed

lemma bij_betw_f_the_inv_into_f:
  "bij_betw f A B \<Longrightarrow> y\<in>B \<Longrightarrow> f (the_inv_into A f y) = y"
\<comment> \<open>an equivalent lemma appears in the HOL library, but this version avoids the double
  @{const bij_betw} premises\<close>
  unfolding bij_betw_def by (blast intro: f_the_inv_into_f)

lemma bij_betw_the_inv_into_onto: "bij_betw f A B \<Longrightarrow> the_inv_into A f ` B = A"
  unfolding bij_betw_def by force

lemma bij_betw_imp_bij_betw_Pow:
  assumes "bij_betw f A B"
  shows   "bij_betw ((`) f) (Pow A) (Pow B)"
  unfolding bij_betw_def
proof (rule conjI, rule inj_onI)
  show "\<And>x y. \<lbrakk> x\<in>Pow A; y\<in>Pow A; f`x = f`y \<rbrakk> \<Longrightarrow> x=y"
    using inj_onD[OF bij_betw_imp_inj_on, OF assms] by blast
  show "(`) f ` Pow A = Pow B"
  proof
    show "(`) f ` Pow A \<subseteq> Pow B" using bij_betw_imp_surj_on[OF assms] by fast
    show "(`) f ` Pow A \<supseteq> Pow B"
    proof
      fix y assume y: "y\<in>Pow B"
      with assms have "y = f ` the_inv_into A f ` y"
        using bij_betw_f_the_inv_into_f[THEN sym] by fastforce
      moreover from y assms have "the_inv_into A f ` y \<subseteq> A"
        using bij_betw_the_inv_into_onto by fastforce
      ultimately show "y \<in> (`) f ` Pow A" by auto
    qed
  qed
qed

lemma comps_fixpointwise_imp_bij_betw:
  assumes "f`X\<subseteq>Y" "g`Y\<subseteq>X" "fixespointwise (g\<circ>f) X" "fixespointwise (f\<circ>g) Y"
  shows   "bij_betw f X Y"
  unfolding bij_betw_def
proof
  show "inj_on f X"
  proof (rule inj_onI)
    fix x y show "\<lbrakk> x\<in>X; y\<in>X; f x = f y \<rbrakk> \<Longrightarrow> x=y"
      using fixespointwiseD[OF assms(3), of x] fixespointwiseD[OF assms(3), of y]
      by    simp
  qed
  from assms(1,2) show "f`X = Y" using fixespointwiseD[OF assms(4)] by force
qed

lemma set_permutation_bij_restrict1:
  assumes "bij_betw f A A"
  shows   "bij (restrict1 f A)"
proof (rule bijI)
  have bij_f: "inj_on f A" "f`A = A" using iffD1[OF bij_betw_def, OF assms] by auto
  show "inj (restrict1 f A)"
  proof (rule injI)
    fix x y show "restrict1 f A x = restrict1 f A y \<Longrightarrow> x=y"
      using inj_onD bij_f by (cases "x\<in>A" "y\<in>A" rule: two_cases) auto
  qed
  show "surj (restrict1 f A)"
  proof (rule surjI)
    fix x
    define y where "y \<equiv> restrict1 (the_inv_into A f) A x"
    thus "restrict1 f A y = x"
      using the_inv_into_into[of f] bij_f f_the_inv_into_f[of f] by (cases "x\<in>A") auto
  qed
qed

lemma set_permutation_the_inv_restrict1:
  assumes "bij_betw f A A"
  shows   "the_inv (restrict1 f A) = restrict1 (the_inv_into A f) A"
proof (rule ext, rule the_inv_into_f_eq)
  from assms show "inj (restrict1 f A)"
    using bij_is_inj set_permutation_bij_restrict1 by fast
next
  fix a from assms show  "restrict1 f A (restrict1 (the_inv_into A f) A a) = a"
    using bij_betw_def[of f] by (simp add: the_inv_into_into f_the_inv_into_f)
qed simp

lemma the_inv_into_the_inv_into:
  "inj_on f A \<Longrightarrow> a\<in>A \<Longrightarrow> the_inv_into (f`A) (the_inv_into A f) a = f a"
  using inj_on_the_inv_into by (force intro: the_inv_into_f_eq imageI)

lemma the_inv_into_f_im_f_im:
  assumes "inj_on f A" "x\<subseteq>A"
  shows   "the_inv_into A f ` f ` x = x"
  using   assms(2) the_inv_into_f_f[OF assms(1)]
  by      force

lemma f_im_the_inv_into_f_im:
  assumes "inj_on f A" "x\<subseteq>f`A"
  shows   "f ` the_inv_into A f ` x = x"
  using   assms(2) f_the_inv_into_f[OF assms(1)]
  by      force

lemma the_inv_leftinv: "bij f \<Longrightarrow> the_inv f \<circ> f = id"
  using bij_def[of f] the_inv_f_f by fastforce


subsubsection {* Induced functions on sets of sets and lists of sets *}

text {*
  Here we create convenience abbreviations for distributing a function over a set of sets and over
  a list of sets.
*}

abbreviation setsetmapim :: "('a\<Rightarrow>'b) \<Rightarrow> 'a set set \<Rightarrow> 'b set set" (infix "\<turnstile>" 70)
  where "f\<turnstile>X \<equiv> ((`) f) ` X"

abbreviation setlistmapim :: "('a\<Rightarrow>'b) \<Rightarrow> 'a set list \<Rightarrow> 'b set list" (infix "\<Turnstile>" 70)
  where "f\<Turnstile>Xs \<equiv> map ((`) f) Xs"

lemma setsetmapim_comp: "(f\<circ>g)\<turnstile>A = f\<turnstile>(g\<turnstile>A)"
  by (auto simp add: image_comp)

lemma setlistmapim_comp: "(f\<circ>g)\<Turnstile>xs = f\<Turnstile>(g\<Turnstile>xs)"
  by auto

lemma setsetmapim_cong_subset:
  assumes "fun_eq_on g f (\<Union>A)" "B\<subseteq>A"
  shows   "g\<turnstile>B \<subseteq> f\<turnstile>B"
proof
  fix y assume "y \<in> g\<turnstile>B"
  from this obtain x where "x\<in>B" "y = g`x" by fast
  with assms(2) show "y \<in> f\<turnstile>B" using fun_eq_on_im[OF assms(1), of x] by fast
qed

lemma setsetmapim_cong: 
  assumes "fun_eq_on g f (\<Union>A)" "B\<subseteq>A"
  shows   "g\<turnstile>B = f\<turnstile>B"
  using   setsetmapim_cong_subset[OF assms]
          setsetmapim_cong_subset[OF fun_eq_on_sym, OF assms]
  by      fast

lemma setsetmapim_restrict1: "B\<subseteq>A \<Longrightarrow> restrict1 f (\<Union>A) \<turnstile> B = f\<turnstile>B"
  using setsetmapim_cong[of _ f] fun_eq_on_restrict1[of "\<Union>A" f] by simp

lemma setsetmapim_the_inv_into:
  assumes "inj_on f (\<Union>A)"
  shows   "(the_inv_into (\<Union>A) f) \<turnstile> (f\<turnstile>A) = A"
proof (rule seteqI)
  fix x assume "x \<in> (the_inv_into (\<Union>A) f) \<turnstile> (f\<turnstile>A)"
  from this obtain y where y: "y \<in> f\<turnstile>A" "x = the_inv_into (\<Union>A) f ` y" by auto
  from y(1) obtain z where z: "z\<in>A" "y = f`z" by fast
  moreover from z(1) have "the_inv_into (\<Union>A) f ` f ` z = z"
    using the_inv_into_f_f[OF assms] by force
  ultimately show "x\<in>A" using y(2) the_inv_into_f_im_f_im[OF assms] by simp
next
  fix x assume x: "x\<in>A"
  moreover hence "the_inv_into (\<Union>A) f ` f ` x = x"
    using the_inv_into_f_im_f_im[OF assms, of x] by fast
  ultimately show "x \<in> (the_inv_into (\<Union>A) f) \<turnstile> (f\<turnstile>A)" by auto
qed


subsubsection {* Induced functions on quotients *}

text {*
  Here we construct the induced function on a quotient for an inducing function that respects the
  relation that defines the quotient.
*}

lemma respects_imp_unique_image_rel: "f respects r \<Longrightarrow> y\<in>f`r``{a} \<Longrightarrow> y = f a"
  using congruentD[of r f] by auto

lemma ex1_class_image:
  assumes "refl_on A r" "f respects r" "X\<in>A//r"
  shows   "\<exists>!b. b\<in>f`X"
proof-
  from assms(3) obtain a where a: "a\<in>A" "X = r``{a}" by (auto intro: quotientE)
  thus ?thesis
    using refl_onD[OF assms(1)] ex1I[of _ "f a"]
          respects_imp_unique_image_rel[OF assms(2), of _ a]
    by    force
qed

definition quotientfun :: "('a\<Rightarrow>'b) \<Rightarrow> 'a set \<Rightarrow> 'b"
  where "quotientfun f X = (THE b. b\<in>f`X)"

lemma quotientfun_equality:
  assumes   "refl_on A r" "f respects r" "X\<in>A//r" "b\<in>f`X"
  shows     "quotientfun f X = b"
  unfolding quotientfun_def
  using     assms(4) ex1_class_image[OF assms(1-3)]
  by        (auto intro: the1_equality)

lemma quotientfun_classrep_equality:
  "\<lbrakk> refl_on A r; f respects r; a\<in>A \<rbrakk> \<Longrightarrow> quotientfun f (r``{a}) = f a"
  using refl_onD by (fastforce intro: quotientfun_equality quotientI)


subsubsection {* Support of a function *}

definition supp :: "('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a set" where "supp f = {x. f x \<noteq> 0}"

lemma suppI_contra: "x \<notin> supp f \<Longrightarrow> f x = 0"
  using supp_def by fast

lemma suppD_contra: "f x = 0 \<Longrightarrow> x \<notin> supp f"
  using supp_def by fast

abbreviation restrict0 :: "('a\<Rightarrow>'b::zero) \<Rightarrow> 'a set \<Rightarrow> ('a\<Rightarrow>'b)"
  where "restrict0 f A \<equiv> (\<lambda>a. if a \<in> A then f a else 0)"

lemma supp_restrict0 : "supp (restrict0 f A) \<subseteq> A"
proof-
  have "\<And>a. a \<notin> A \<Longrightarrow> a \<notin> supp (restrict0 f A)"
    using suppD_contra[of "restrict0 f A"] by simp
  thus ?thesis by fast
qed


subsection {* Lists *}


subsubsection {* Miscellaneous facts *}

lemma snoc_conv_cons: "\<exists>x xs. ys@[y] = x#xs"
  by (cases ys) auto

lemma cons_conv_snoc: "\<exists>ys y. x#xs = ys@[y]"
  by (cases xs rule: rev_cases) auto

lemma same_length_eq_append:
  "length as = length bs \<Longrightarrow> as@cs = bs@ds \<Longrightarrow> as = bs"
  by (induct as bs rule: list_induct2) auto

lemma count_list_append:
  "count_list (xs@ys) a = count_list xs a + count_list ys a"
  by (induct xs) auto

lemma count_list_snoc:
  "count_list (xs@[x]) y = (if y=x then Suc (count_list xs y) else count_list xs y)"
  by (induct xs) auto

lemma distinct_count_list:
  "distinct xs \<Longrightarrow> count_list xs a = (if a \<in> set xs then 1 else 0)"
  by (induct xs) auto

lemma map_fst_map_const_snd: "map fst (map (\<lambda>s. (s,b)) xs) = xs"
  by (induct xs) auto

lemma inj_on_distinct_setlistmapim:
  assumes "inj_on f A"
  shows "\<forall>X\<in>set Xs. X \<subseteq> A \<Longrightarrow> distinct Xs \<Longrightarrow> distinct (f\<Turnstile>Xs)"
proof (induct Xs)
  case (Cons X Xs)
  show ?case
  proof (cases "f`X \<in> set (f\<Turnstile>Xs)")
    case True
    from this obtain Y where Y: "Y\<in>set Xs" "f`X = f`Y" by auto
    with assms Y(1) Cons(2,3) show ?thesis
      using inj_on_eq_image[of f A X Y] by fastforce
  next
    case False with Cons show ?thesis by simp
  qed
qed simp

subsubsection {* Cases *}

lemma list_cases_Cons_snoc [case_names Nil Single Cons_snoc]:
  assumes       Nil: "xs = [] \<Longrightarrow> P"
  and        Single: "\<And>x. xs = [x] \<Longrightarrow> P"
  and     Cons_snoc: "\<And>x ys y. xs = x # ys @ [y] \<Longrightarrow> P"
  shows "P"
proof (cases xs, rule Nil)
  case (Cons x xs) with Single Cons_snoc show ?thesis
    by (cases xs rule: rev_cases) auto
qed

lemma two_lists_cases_Cons_Cons [case_names Nil1 Nil2 ConsCons]:
  assumes     Nil1: "\<And>ys. as = [] \<Longrightarrow> bs = ys \<Longrightarrow> P"
  and         Nil2: "\<And>xs. as = xs \<Longrightarrow> bs = [] \<Longrightarrow> P"
  and     ConsCons: "\<And>x xs y ys. as = x # xs \<Longrightarrow> bs = y # ys \<Longrightarrow> P"
  shows "P"
proof (cases as)
  case Cons with assms(2,3) show ?thesis by (cases bs) auto
qed (simp add: Nil1)

lemma two_lists_cases_snoc_Cons [case_names Nil1 Nil2 snoc_Cons]:
  assumes      Nil1: "\<And>ys. as = [] \<Longrightarrow> bs = ys \<Longrightarrow> P"
  and          Nil2: "\<And>xs. as = xs \<Longrightarrow> bs = [] \<Longrightarrow> P"
  and     snoc_Cons: "\<And>xs x y ys. as = xs @ [x] \<Longrightarrow> bs = y # ys \<Longrightarrow> P"
  shows "P"
proof (cases as rule: rev_cases)
  case snoc with Nil2 snoc_Cons show ?thesis by (cases bs) auto
qed (simp add: Nil1)

lemma two_lists_cases_snoc_Cons' [case_names both_Nil Nil1 Nil2 snoc_Cons]:
  assumes  both_Nil: "as = [] \<Longrightarrow> bs = [] \<Longrightarrow> P"
  and          Nil1: "\<And>y ys. as = [] \<Longrightarrow> bs = y#ys \<Longrightarrow> P"
  and          Nil2: "\<And>xs x. as = xs@[x] \<Longrightarrow> bs = [] \<Longrightarrow> P"
  and     snoc_Cons: "\<And>xs x y ys. as = xs @ [x] \<Longrightarrow> bs = y # ys \<Longrightarrow> P"
  shows "P"
proof (cases as bs rule: two_lists_cases_snoc_Cons)
  case (Nil1 ys) with assms(1,2) show "P" by (cases ys) auto
next
  case (Nil2 xs) with assms(1,3) show "P" by (cases xs rule: rev_cases) auto
qed (rule snoc_Cons)

lemma two_prod_lists_cases_snoc_Cons:
  assumes "\<And>xs. as = xs \<and> bs = [] \<Longrightarrow> P" "\<And>ys. as = [] \<and> bs = ys \<Longrightarrow> P"
          "\<And>xs aa ba ab bb ys. as = xs @ [(aa, ba)] \<and> bs = (ab, bb) # ys \<Longrightarrow> P"
  shows "P"
proof (rule two_lists_cases_snoc_Cons)
  from assms
    show  "\<And>ys. as = [] \<Longrightarrow> bs = ys \<Longrightarrow> P" "\<And>xs. as = xs \<Longrightarrow> bs = [] \<Longrightarrow> P"
    by    auto
  from assms(3) show "\<And>xs x y ys. as = xs @ [x] \<Longrightarrow> bs = y # ys \<Longrightarrow> P"
    by fast
qed

lemma three_lists_cases_snoc_mid_Cons
      [case_names Nil1 Nil2 Nil3 snoc_single_Cons snoc_mid_Cons]:
  assumes             Nil1: "\<And>ys zs. as = [] \<Longrightarrow> bs = ys \<Longrightarrow> cs = zs \<Longrightarrow> P"
  and                 Nil2: "\<And>xs zs. as = xs \<Longrightarrow> bs = [] \<Longrightarrow> cs = zs \<Longrightarrow> P"
  and                 Nil3: "\<And>xs ys. as = xs \<Longrightarrow> bs = ys \<Longrightarrow> cs = [] \<Longrightarrow> P"
  and     snoc_single_Cons:
    "\<And>xs x y z zs. as = xs @ [x] \<Longrightarrow> bs = [y] \<Longrightarrow> cs = z # zs \<Longrightarrow> P"
  and        snoc_mid_Cons:
    "\<And>xs x w ys y z zs. as = xs @ [x] \<Longrightarrow> bs = w # ys @ [y] \<Longrightarrow>
      cs = z # zs \<Longrightarrow> P"
  shows "P"
proof (cases as cs rule: two_lists_cases_snoc_Cons)
  case Nil1 with assms(1) show "P" by simp
next
  case Nil2 with assms(3) show "P" by simp
next
  case snoc_Cons
  with Nil2 snoc_single_Cons snoc_mid_Cons show "P"
    by (cases bs rule: list_cases_Cons_snoc) auto
qed


subsubsection {* Induction *}

lemma list_induct_CCons [case_names Nil Single CCons]:
  assumes Nil   : "P []"
  and     Single: "\<And>x. P [x]"
  and     CCons : "\<And>x y xs. P (y#xs) \<Longrightarrow> P (x # y # xs)"
  shows   "P xs"
proof (induct xs)
  case (Cons x xs) with Single CCons show ?case by (cases xs) auto
qed (rule Nil)

lemma list_induct_ssnoc [case_names Nil Single ssnoc]:
  assumes Nil   : "P []"
  and     Single: "\<And>x. P [x]"
  and     ssnoc : "\<And>xs x y. P (xs@[x]) \<Longrightarrow> P (xs@[x,y])"
  shows   "P xs"
proof (induct xs rule: rev_induct)
  case (snoc x xs) with Single ssnoc show ?case by (cases xs rule: rev_cases) auto
qed (rule Nil)

lemma list_induct2_snoc [case_names Nil1 Nil2 snoc]:
  assumes Nil1: "\<And>ys. P [] ys"
  and     Nil2: "\<And>xs. P xs []"
  and     snoc: "\<And>xs x ys y. P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y])"
  shows   "P xs ys"
proof (induct xs arbitrary: ys rule: rev_induct, rule Nil1)
  case (snoc b bs) with assms(2,3) show ?case by (cases ys rule: rev_cases) auto
qed

lemma list_induct2_snoc_Cons [case_names Nil1 Nil2 snoc_Cons]:
  assumes Nil1     : "\<And>ys. P [] ys"
  and     Nil2     : "\<And>xs. P xs []"
  and     snoc_Cons: "\<And>xs x y ys. P xs ys \<Longrightarrow> P (xs@[x]) (y#ys)"
  shows   "P xs ys"
proof (induct ys arbitrary: xs, rule Nil2)
  case (Cons y ys) with Nil1 snoc_Cons show ?case
    by (cases xs rule: rev_cases) auto
qed

lemma prod_list_induct3_snoc_Conssnoc_Cons_pairwise:
  assumes "\<And>ys zs. Q ([],ys,zs)" "\<And>xs zs. Q (xs,[],zs)" "\<And>xs ys. Q (xs,ys,[])"
          "\<And>xs x y z zs. Q (xs@[x],[y],z#zs)"
  and     step:
    "\<And>xs x y ys w z zs. Q (xs,ys,zs) \<Longrightarrow> Q (xs,ys@[w],z#zs) \<Longrightarrow>
      Q (xs@[x],y#ys,zs) \<Longrightarrow> Q (xs@[x],y#ys@[w],z#zs)"
  shows   "Q t"
proof (
  induct  t
  taking: "\<lambda>(xs,ys,zs). length xs + length ys + length zs"
  rule  : measure_induct_rule
)
  case (less t)
  show ?case
  proof (cases t)
    case (fields xs ys zs) from assms less fields show ?thesis
      by (cases xs ys zs rule: three_lists_cases_snoc_mid_Cons) auto
  qed
qed

lemma list_induct3_snoc_Conssnoc_Cons_pairwise
      [case_names Nil1 Nil2 Nil3 snoc_single_Cons snoc_Conssnoc_Cons]:
  assumes Nil1              : "\<And>ys zs. P [] ys zs"
  and     Nil2              : "\<And>xs zs. P xs [] zs"
  and     Nil3              : "\<And>xs ys. P xs ys []"
  and     snoc_single_Cons  : "\<And>xs x y z zs. P (xs@[x]) [y] (z#zs)"
  and     snoc_Conssnoc_Cons:
    "\<And>xs x y ys w z zs. P xs ys zs \<Longrightarrow> P xs (ys@[w]) (z#zs) \<Longrightarrow>
      P (xs@[x]) (y#ys) zs \<Longrightarrow> P (xs@[x]) (y#ys@[w]) (z#zs)"
  shows   "P xs ys zs"
  using   assms
          prod_list_induct3_snoc_Conssnoc_Cons_pairwise[of "\<lambda>(xs,ys,zs). P xs ys zs"]
  by      auto


subsubsection {* Alternating lists *}

primrec alternating_list :: "nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list"
  where zero: "alternating_list 0 s t = []"
      | Suc : "alternating_list (Suc k) s t =
                alternating_list k s t @ [if even k then s else t]"
\<comment> \<open>could be defined using Cons, but we want the alternating list to always start with the same
letter as it grows, and it's easier to do that via append\<close>

lemma alternating_list2: "alternating_list 2 s t = [s,t]"
  using arg_cong[OF Suc_1, THEN sym, of "\<lambda>n. alternating_list n s t"] by simp

lemma length_alternating_list: "length (alternating_list n s t) = n"
  by (induct n) auto

lemma alternating_list_Suc_Cons:
  "alternating_list (Suc k) s t = s # alternating_list k t s"
  by (induct k) auto

lemma alternating_list_SucSuc_ConsCons:
  "alternating_list (Suc (Suc k)) s t = s # t # alternating_list k s t"
  using alternating_list_Suc_Cons[of "Suc k" s] alternating_list_Suc_Cons[of k t]
  by    simp

lemma alternating_list_alternates:
  "alternating_list n s t = as@[a,b,c]@bs \<Longrightarrow> a=c"
proof (induct n arbitrary: bs)
  case (Suc m) hence prevcase:
    "\<And>xs. alternating_list m s t = as @ [a,b,c] @ xs \<Longrightarrow> a = c"
    "alternating_list (Suc m) s t = as @ [a,b,c] @ bs"
    by auto
  show ?case
  proof (cases bs rule: rev_cases)
    case Nil show ?thesis
    proof (cases m)
      case 0 with prevcase(2) show ?thesis by simp
    next
      case (Suc k) with prevcase(2) Nil show ?thesis by (cases k) auto
    qed
  next
    case (snoc ds d) with prevcase show ?thesis by simp
  qed      
qed simp

lemma alternating_list_split:
  "alternating_list (m+n) s t = alternating_list m s t @
    (if even m then alternating_list n s t else alternating_list n t s)"
  using alternating_list_SucSuc_ConsCons[of _ s]
  by    (induct n rule: nat_induct_step2) auto

lemma alternating_list_append:
  "even m \<Longrightarrow>
    alternating_list m s t @ alternating_list n s t = alternating_list (m+n) s t"
  "odd m \<Longrightarrow>
    alternating_list m s t @ alternating_list n t s = alternating_list (m+n) s t"
  using alternating_list_split[THEN sym, of m] by auto

lemma rev_alternating_list:
  "rev (alternating_list n s t) =
    (if even n then alternating_list n t s else alternating_list n s t)"
  using alternating_list_SucSuc_ConsCons[of _ s]
  by    (induct n rule: nat_induct_step2) auto

lemma set_alternating_list: "set (alternating_list n s t) \<subseteq> {s,t}"
  by (induct n) auto

lemma set_alternating_list1:
  assumes "n \<ge> 1"
  shows "s \<in> set (alternating_list n s t)"
proof (cases n)
  case 0 with assms show ?thesis by simp
next
  case (Suc m) thus ?thesis using alternating_list_Suc_Cons[of m s] by simp
qed

lemma set_alternating_list2:
  "n \<ge> 2 \<Longrightarrow> set (alternating_list n s t) = {s,t}"
proof (induct n rule: nat_induct_step2)
  case (SucSuc m) thus ?case
    using set_alternating_list alternating_list_SucSuc_ConsCons[of m s t] by fastforce
qed auto

lemma alternating_list_in_lists: "a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> alternating_list n a b \<in> lists A"
  by (induct n) auto


subsubsection {* Binary relation chains *}

text {* Here we consider lists where each pair of adjacent elements satisfy a given relation. *}

fun binrelchain :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  where "binrelchain P []  = True"
      | "binrelchain P [x] = True"
      | "binrelchain P (x # y # xs) = (P x y \<and> binrelchain P (y#xs))"

lemma binrelchain_Cons_reduce: "binrelchain P (x#xs) \<Longrightarrow> binrelchain P xs"
  by (induct xs) auto

lemma binrelchain_append_reduce1: "binrelchain P (xs@ys) \<Longrightarrow> binrelchain P xs"
proof (induct xs rule: list_induct_CCons)
  case (CCons x y xs) with binrelchain_Cons_reduce show ?case by fastforce
qed auto

lemma binrelchain_append_reduce2:
  "binrelchain P (xs@ys) \<Longrightarrow> binrelchain P ys"
proof (induct xs)
  case (Cons x xs) with binrelchain_Cons_reduce show ?case by fastforce
qed simp

lemma binrelchain_Conssnoc_reduce:
  "binrelchain P (x#xs@[y]) \<Longrightarrow> binrelchain P xs"
  using binrelchain_append_reduce1 binrelchain_Cons_reduce by fastforce

lemma binrelchain_overlap_join:
  "binrelchain P (xs@[x]) \<Longrightarrow> binrelchain P (x#ys) \<Longrightarrow> binrelchain P (xs@x#ys)"
  by (induct xs rule: list_induct_CCons) auto

lemma binrelchain_join:
  "\<lbrakk> binrelchain P (xs@[x]); binrelchain P (y#ys); P x y \<rbrakk> \<Longrightarrow>
    binrelchain P (xs @ x # y # ys)"
  using binrelchain_overlap_join by fastforce

lemma binrelchain_snoc:
  "binrelchain P (xs@[x]) \<Longrightarrow> P x y \<Longrightarrow> binrelchain P (xs@[x,y])"
  using binrelchain_join by fastforce

lemma binrelchain_sym_rev:
  assumes "\<And>x y. P x y \<Longrightarrow> P y x"
  shows   "binrelchain P xs \<Longrightarrow> binrelchain P (rev xs)"
proof (induct xs rule: list_induct_CCons)
  case (CCons x y xs) with assms show ?case by (auto intro: binrelchain_snoc)
qed auto

lemma binrelchain_remdup_adj:
  "binrelchain P (xs@[x,x]@ys) \<Longrightarrow> binrelchain P (xs@x#ys)"
  by (induct xs rule: list_induct_CCons) auto

abbreviation "proper_binrelchain P xs \<equiv> binrelchain P xs \<and> distinct xs"

lemma binrelchain_obtain_proper:
  "x\<noteq>y \<Longrightarrow> binrelchain P (x#xs@[y]) \<Longrightarrow>
    \<exists>zs. set zs \<subseteq> set xs \<and> length zs \<le> length xs \<and> proper_binrelchain P (x#zs@[y])"
proof (induct xs arbitrary: x)
  case (Cons w ws)
  show ?case
  proof (cases "w=x" "w=y" rule: two_cases)
    case one
    from one(1) Cons(3) have "binrelchain P (x#ws@[y])"
      using binrelchain_Cons_reduce by simp
    with Cons(1,2) obtain zs
      where "set zs \<subseteq> set ws" "length zs \<le> length ws" "proper_binrelchain P (x#zs@[y])"
      by    auto
    thus ?thesis by auto
  next
    case other
    with Cons(3) have "proper_binrelchain P (x#[]@[y])"
      using binrelchain_append_reduce1 by simp
    moreover have "length [] \<le> length (w#ws)" "set [] \<subseteq> set (w#ws)" by auto
    ultimately show ?thesis by blast
  next
    case neither
    from Cons(3) have "binrelchain P (w#ws@[y])"
      using binrelchain_Cons_reduce by simp
    with neither(2) Cons(1) obtain zs 
      where zs: "set zs \<subseteq> set ws" "length zs \<le> length ws"
                "proper_binrelchain P (w#zs@[y])"
      by    auto
    show ?thesis
    proof (cases "x\<in>set zs")
      case True
      from this obtain as bs where asbs: "zs = as@x#bs"
        using in_set_conv_decomp[of x] by auto
      with zs(3) have "proper_binrelchain P (x#bs@[y])"
        using binrelchain_append_reduce2[of P "w#as"] by auto
      moreover from zs(1) asbs have "set bs \<subseteq> set (w#ws)" by auto
      moreover from asbs zs(2) have "length bs \<le> length (w#ws)" by simp
      ultimately show ?thesis by auto
    next
      case False
      with zs(3) neither(1) Cons(2,3) have "proper_binrelchain P (x#(w#zs)@[y])"
        by simp
      moreover from zs(1) have "set (w#zs) \<subseteq> set (w#ws)" by auto
      moreover from zs(2) have "length (w#zs) \<le> length (w#ws)" by simp
      ultimately show ?thesis by blast
    qed
  qed (fastforce simp add: Cons(2))
qed simp

lemma binrelchain_trans_Cons_snoc:
  assumes "\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
  shows   "binrelchain P (x#xs@[y]) \<Longrightarrow> P x y"
proof (induct xs arbitrary: x)
  case Cons with assms show ?case using binrelchain_Cons_reduce by auto
qed simp

lemma binrelchain_cong:
  assumes "\<And>x y. P x y \<Longrightarrow> Q x y"
  shows   "binrelchain P xs \<Longrightarrow> binrelchain Q xs"
  using   assms binrelchain_Cons_reduce
  by      (induct xs rule: list_induct_CCons) auto

lemma binrelchain_funcong_Cons_snoc:
  assumes "\<And>x y. P x y \<Longrightarrow> f y = f x" "binrelchain P (x#xs@[y])"
  shows   "f y = f x"
  using   assms binrelchain_cong[of P]
          binrelchain_trans_Cons_snoc[of "\<lambda>x y. f y = f x" x xs y]
  by      auto

lemma binrelchain_funcong_extra_condition_Cons_snoc:
  assumes "\<And>x y. Q x \<Longrightarrow> P x y \<Longrightarrow> Q y" "\<And>x y. Q x \<Longrightarrow> P x y \<Longrightarrow> f y = f x"
  shows   "Q x \<Longrightarrow> binrelchain P (x#zs@[y]) \<Longrightarrow> f y = f x"
proof (induct zs arbitrary: x)
  case (Cons z zs) with assms show ?case
    using binrelchain_Cons_reduce[of P x "z#zs@[y]"] by fastforce
qed (simp add: assms)

lemma binrelchain_setfuncong_Cons_snoc:
  "\<lbrakk> \<forall>x\<in>A. \<forall>y. P x y \<longrightarrow> y\<in>A; \<forall>x\<in>A. \<forall>y. P x y \<longrightarrow> f y = f x; x\<in>A;
      binrelchain P (x#zs@[y]) \<rbrakk> \<Longrightarrow> f y = f x"
  using binrelchain_funcong_extra_condition_Cons_snoc[of "\<lambda>x. x\<in>A" P f x zs y]
  by    fast

lemma binrelchain_propcong_Cons_snoc:
  assumes "\<And>x y. Q x \<Longrightarrow> P x y \<Longrightarrow> Q y"
  shows   "Q x \<Longrightarrow> binrelchain P (x#xs@[y]) \<Longrightarrow> Q y"
proof (induct xs arbitrary: x)
  case Cons with assms show ?case using binrelchain_Cons_reduce by auto
qed (simp add: assms)

subsubsection {* Set of subseqs *}

lemma subseqs_Cons: "subseqs (x#xs) = map (Cons x) (subseqs xs) @ (subseqs xs)"
  using cong_let[of "subseqs xs" "\<lambda>xss. map (Cons x) xss @ xss"] by simp

abbreviation "ssubseqs xs \<equiv> set (subseqs xs)"

lemma nil_ssubseqs: "[] \<in> ssubseqs xs"
proof (induct xs)
  case (Cons x xs) thus ?case using subseqs_Cons[of x] by simp
qed simp

lemma ssubseqs_Cons: "ssubseqs (x#xs) = (Cons x) ` (ssubseqs xs) \<union> ssubseqs xs"
  using subseqs_Cons[of x] by simp

lemma ssubseqs_refl: "xs \<in> ssubseqs xs"
proof (induct xs)
  case (Cons x xs) thus ?case using ssubseqs_Cons by fast
qed (rule nil_ssubseqs)

lemma ssubseqs_subset: "as \<in> ssubseqs bs \<Longrightarrow> ssubseqs as \<subseteq> ssubseqs bs"
proof (induct bs arbitrary: as)
  case (Cons b bs) show ?case
  proof (cases "as \<in> set (subseqs bs)")
    case True with Cons show ?thesis using ssubseqs_Cons by fastforce
  next
    case False with Cons show ?thesis
      using nil_ssubseqs[of "b#bs"] ssubseqs_Cons[of "hd as"] ssubseqs_Cons[of b]
      by    (cases as) auto
  qed
qed simp

lemma ssubseqs_lists:
  "as \<in> lists A \<Longrightarrow> bs \<in> ssubseqs as \<Longrightarrow> bs \<in> lists A"
proof (induct as arbitrary: bs)
  case (Cons a as) thus ?case using ssubseqs_Cons[of a] by fastforce
qed simp

lemma delete1_ssubseqs:
  "as@bs \<in> ssubseqs (as@[a]@bs)"
proof (induct as)
  case Nil show ?case using ssubseqs_refl ssubseqs_Cons[of a bs] by auto
next
  case (Cons x xs) thus ?case using ssubseqs_Cons[of x] by simp
qed

lemma delete2_ssubseqs:
  "as@bs@cs \<in> ssubseqs (as@[a]@bs@[b]@cs)"
  using delete1_ssubseqs[of "as@[a]@bs"] delete1_ssubseqs ssubseqs_subset
  by    fastforce



subsection {* Orders and posets *}

text {*
  We have chosen to work with the @{const ordering} locale instead of the @{class order} class to
  more easily facilitate simultaneously working with both an order and its dual.
*}

subsubsection {* Dual ordering *}

context ordering
begin

abbreviation greater_eq  :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infix "\<succeq>" 50)
  where "greater_eq a b \<equiv> less_eq b a"
abbreviation greater  :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infix "\<succ>" 50)
  where "greater a b \<equiv> less b a"

lemma dual: "ordering greater_eq greater"
  using strict_iff_order refl antisym trans by unfold_locales fastforce

end (* context ordering *)

subsubsection {* Morphisms of posets *}

locale OrderingSetMap =
  domain  : ordering less_eq less
+ codomain: ordering less_eq' less' 
  for less_eq  :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infix "\<^bold>\<le>"  50)
  and less     :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infix "\<^bold><"  50)
  and less_eq' :: "'b\<Rightarrow>'b\<Rightarrow>bool" (infix "\<^bold>\<le>*" 50)
  and less'    :: "'b\<Rightarrow>'b\<Rightarrow>bool" (infix "\<^bold><*" 50)
+ fixes P :: "'a set"
  and   f :: "'a\<Rightarrow>'b"
  assumes ordsetmap: "a\<in>P \<Longrightarrow> b\<in>P \<Longrightarrow> a \<^bold>\<le> b \<Longrightarrow> f a \<^bold>\<le>* f b"
begin

lemma comp:
  assumes "OrderingSetMap less_eq' less' less_eq'' less'' Q g" "f`P \<subseteq> Q"
  shows   "OrderingSetMap less_eq less less_eq'' less'' P (g\<circ>f)"
proof (
  intro_locales, rule OrderingSetMap.axioms(2), rule assms(1), unfold_locales
)
  from assms(2)
    show  "\<And>a b. a \<in> P \<Longrightarrow> b \<in> P \<Longrightarrow> a \<^bold>\<le> b \<Longrightarrow> less_eq'' ((g \<circ> f) a) ((g \<circ> f) b)"
    using ordsetmap OrderingSetMap.ordsetmap[OF assms(1)]
    by    force
qed

lemma subset: "Q\<subseteq>P \<Longrightarrow> OrderingSetMap (\<^bold>\<le>) (\<^bold><) (\<^bold>\<le>*) (\<^bold><*) Q f"
  using ordsetmap by unfold_locales fast

lemma dual:
  "OrderingSetMap domain.greater_eq domain.greater
    codomain.greater_eq codomain.greater P f"
proof (intro_locales, rule domain.dual, rule codomain.dual, unfold_locales)
  from ordsetmap show "\<And>a b. a\<in>P \<Longrightarrow> b\<in>P \<Longrightarrow> a\<succeq>b \<Longrightarrow> f b \<^bold>\<le>* f a" by fast
qed

end (* context OrderingSetMap *)

locale OrderingSetIso = OrderingSetMap less_eq less less_eq' less' P f
  for less_eq  :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infix "\<^bold>\<le>"  50)
  and less     :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infix "\<^bold><"  50)
  and less_eq' :: "'b\<Rightarrow>'b\<Rightarrow>bool" (infix "\<^bold>\<le>*" 50)
  and less'    :: "'b\<Rightarrow>'b\<Rightarrow>bool" (infix "\<^bold><*" 50)
  and P :: "'a set"
  and f :: "'a\<Rightarrow>'b"
+ assumes inj               : "inj_on f P"
  and     rev_OrderingSetMap:
    "OrderingSetMap less_eq' less' less_eq less (f`P) (the_inv_into P f)"

abbreviation "subset_ordering_iso \<equiv> OrderingSetIso (\<subseteq>) (\<subset>) (\<subseteq>) (\<subset>)"

lemma (in OrderingSetMap) isoI:
  assumes "inj_on f P" "\<And>a b. a\<in>P \<Longrightarrow> b\<in>P \<Longrightarrow> f a \<^bold>\<le>* f b \<Longrightarrow> a \<^bold>\<le> b"
  shows   "OrderingSetIso less_eq less less_eq' less' P f"
  using   assms the_inv_into_f_f[OF assms(1)]
  by      unfold_locales auto

lemma OrderingSetIsoI_orders_greater2less:
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  assumes "inj_on f P" "\<And>a b. a \<in> P \<Longrightarrow> b \<in> P \<Longrightarrow> (b\<le>a) = (f a \<le> f b)"
  shows   "OrderingSetIso (greater_eq::'a\<Rightarrow>'a\<Rightarrow>bool) (greater::'a\<Rightarrow>'a\<Rightarrow>bool)
            (less_eq::'b\<Rightarrow>'b\<Rightarrow>bool) (less::'b\<Rightarrow>'b\<Rightarrow>bool) P f"
proof
  from assms(2) show "\<And>a b. a \<in> P \<Longrightarrow> b \<in> P \<Longrightarrow> b\<le>a \<Longrightarrow> f a \<le> f b" by auto
  from assms(2)
    show  "\<And>a b. a \<in> f ` P \<Longrightarrow> b \<in> f ` P \<Longrightarrow> b\<le>a \<Longrightarrow>
            the_inv_into P f a \<le> the_inv_into P f b"
    using the_inv_into_f_f[OF assms(1)]
    by    force
qed (rule assms(1))


context OrderingSetIso
begin

lemmas ordsetmap = ordsetmap

lemma ordsetmap_strict: "\<lbrakk> a\<in>P; b\<in>P; a\<^bold><b \<rbrakk> \<Longrightarrow> f a \<^bold><* f b"
  using domain.strict_iff_order codomain.strict_iff_order ordsetmap inj
        inj_on_contraD
  by    fastforce

lemmas inv_ordsetmap = OrderingSetMap.ordsetmap[OF rev_OrderingSetMap]

lemma rev_ordsetmap: "\<lbrakk> a\<in>P; b\<in>P; f a \<^bold>\<le>* f b \<rbrakk> \<Longrightarrow> a \<^bold>\<le> b"
  using inv_ordsetmap the_inv_into_f_f[OF inj] by fastforce

lemma inv_iso: "OrderingSetIso less_eq' less' less_eq less (f`P) (the_inv_into P f)"
  using inv_ordsetmap inj_on_the_inv_into[OF inj] the_inv_into_onto[OF inj]
        ordsetmap the_inv_into_the_inv_into[OF inj]
  by    unfold_locales auto

lemmas inv_ordsetmap_strict = OrderingSetIso.ordsetmap_strict[OF inv_iso]

lemma rev_ordsetmap_strict: "\<lbrakk> a\<in>P; b\<in>P; f a \<^bold><* f b \<rbrakk> \<Longrightarrow> a \<^bold>< b"
  using inv_ordsetmap_strict the_inv_into_f_f[OF inj] by fastforce

lemma iso_comp:
  assumes "OrderingSetIso less_eq' less' less_eq'' less'' Q g" "f`P \<subseteq> Q"
  shows   "OrderingSetIso less_eq less less_eq'' less'' P (g\<circ>f)"
proof (rule OrderingSetMap.isoI)
  from assms show "OrderingSetMap (\<^bold>\<le>) (\<^bold><) less_eq'' less'' P (g \<circ> f)"
    using OrderingSetIso.axioms(1) comp by fast
  from assms(2) show "inj_on (g \<circ> f) P"
    using OrderingSetIso.inj[OF assms(1)]
          comp_inj_on[OF inj, OF subset_inj_on]
    by    fast
next
  fix a b
  from assms(2) show "\<lbrakk> a\<in>P; b\<in>P; less_eq'' ((g\<circ>f) a) ((g\<circ>f) b) \<rbrakk> \<Longrightarrow> a\<^bold>\<le>b"
    using OrderingSetIso.rev_ordsetmap[OF assms(1)] rev_ordsetmap by force
qed

lemma iso_subset:
  "Q\<subseteq>P \<Longrightarrow> OrderingSetIso (\<^bold>\<le>) (\<^bold><) (\<^bold>\<le>*) (\<^bold><*) Q f"
  using subset[of Q] subset_inj_on[OF inj] rev_ordsetmap
  by    (blast intro: OrderingSetMap.isoI)

lemma iso_dual:
  "OrderingSetIso domain.greater_eq domain.greater
    codomain.greater_eq codomain.greater P f"
  by  (
        rule OrderingSetMap.isoI, rule OrderingSetMap.dual, unfold_locales,
        rule inj, rule rev_ordsetmap
      )

end (* context OrderingSetIso *)

lemma induced_pow_fun_subset_ordering_iso:
  assumes "inj_on f A"
  shows   "subset_ordering_iso (Pow A) ((`) f)"
proof
  show "\<And>a b. a \<in> Pow A \<Longrightarrow> b \<in> Pow A \<Longrightarrow> a \<subseteq> b \<Longrightarrow> f ` a \<subseteq> f ` b" by fast
  from assms show 2:"inj_on ((`) f) (Pow A)"
    using induced_pow_fun_inj_on by fast
  show "\<And>a b. a \<in> (`) f ` Pow A \<Longrightarrow> b \<in> (`) f ` Pow A \<Longrightarrow> a \<subseteq> b
        \<Longrightarrow> the_inv_into (Pow A) ((`) f) a \<subseteq> the_inv_into (Pow A) ((`) f) b"
  proof-
    fix Y1 Y2
    assume Y: "Y1 \<in> ((`) f) ` Pow A" "Y2 \<in> ((`) f) ` Pow A" "Y1 \<subseteq> Y2"
    from Y(1,2) obtain X1 X2 where "X1\<subseteq>A" "X2\<subseteq>A" "Y1 = f`X1" "Y2 = f`X2"
      by auto
    with assms Y(3)
      show  "the_inv_into (Pow A) ((`) f) Y1 \<subseteq> the_inv_into (Pow A) ((`) f) Y2"
      using inj_onD[OF assms] the_inv_into_f_f[OF 2, of X1]
            the_inv_into_f_f[OF 2, of X2]
      by    blast
  qed
qed

subsubsection {* More @{const arg_min} *}

lemma is_arg_minI:
  "\<lbrakk> P x; \<And>y. P y \<Longrightarrow> \<not> m y < m x \<rbrakk> \<Longrightarrow> is_arg_min m P x"
by (simp add: is_arg_min_def)

lemma is_arg_min_linorderI:
  "\<lbrakk> P x; \<And>y. P y \<Longrightarrow> m x \<le> (m y::_::linorder) \<rbrakk> \<Longrightarrow> is_arg_min m P x"
by (simp add: is_arg_min_linorder)

lemma is_arg_min_eq:
  "\<lbrakk> is_arg_min m P x; P z; m z = m x \<rbrakk> \<Longrightarrow> is_arg_min m P z"
by (metis is_arg_min_def)

lemma is_arg_minD1: "is_arg_min m P x \<Longrightarrow> P x"
unfolding is_arg_min_def by fast

lemma is_arg_minD2: "is_arg_min m P x \<Longrightarrow> P y \<Longrightarrow> \<not> m y < m x"
unfolding is_arg_min_def by fast

lemma is_arg_min_size: fixes m :: "'a \<Rightarrow> 'b::linorder"
shows "is_arg_min m P x \<Longrightarrow> m x = m (arg_min m P)"
by (metis arg_min_equality is_arg_min_linorder)

lemma is_arg_min_size_subprop:
  fixes   m :: "'a\<Rightarrow>'b::linorder"
  assumes "is_arg_min m P x" "Q x" "\<And>y. Q y \<Longrightarrow> P y"
  shows   "m (arg_min m Q) = m (arg_min m P)"
proof-
  have "\<not> is_arg_min m Q x \<Longrightarrow> \<not> is_arg_min m P x"
  proof
    assume x: "\<not> is_arg_min m Q x"
    from assms(2,3) show False
      using contrapos_nn[OF x, OF is_arg_minI] is_arg_minD2[OF assms(1)] by auto
  qed
  with assms(1) show ?thesis
    using is_arg_min_size[of m] is_arg_min_size[of m] by fastforce
qed

subsubsection {* Bottom of a set *}

context ordering
begin

definition has_bottom :: "'a set \<Rightarrow> bool"
  where "has_bottom P \<equiv> \<exists>z\<in>P. \<forall>x\<in>P. z \<^bold>\<le> x"

lemma has_bottomI: "z\<in>P \<Longrightarrow> (\<And>x. x\<in>P \<Longrightarrow> z \<^bold>\<le> x) \<Longrightarrow> has_bottom P"
  using has_bottom_def by auto

lemma has_uniq_bottom: "has_bottom P \<Longrightarrow> \<exists>!z\<in>P. \<forall>x\<in>P. z\<^bold>\<le>x"
  using has_bottom_def antisym by force

definition bottom :: "'a set \<Rightarrow> 'a"
  where "bottom P \<equiv> (THE z. z\<in>P \<and> (\<forall>x\<in>P. z\<^bold>\<le>x))"

lemma bottomD:
  assumes   "has_bottom P"
  shows     "bottom P \<in> P" "x\<in>P \<Longrightarrow> bottom P \<^bold>\<le> x"
  using     assms has_uniq_bottom theI'[of "\<lambda>z. z\<in>P \<and> (\<forall>x\<in>P. z\<^bold>\<le>x)"]
  unfolding bottom_def
  by        auto

lemma bottomI: "z\<in>P \<Longrightarrow> (\<And>y. y\<in>P \<Longrightarrow> z \<^bold>\<le> y) \<Longrightarrow> z = bottom P"
  using     has_bottomI has_uniq_bottom
            the1_equality[THEN sym, of "\<lambda>z. z\<in>P \<and> (\<forall>x\<in>P. z\<^bold>\<le>x)"]
  unfolding bottom_def
  by        simp

end (* context ordering *)

lemma has_bottom_pow: "order.has_bottom (Pow A)"
  by (fast intro: order.has_bottomI)

lemma bottom_pow: "order.bottom (Pow A) = {}"
proof (rule order.bottomI[THEN sym]) qed auto

context OrderingSetMap
begin

abbreviation "dombot \<equiv> domain.bottom P"
abbreviation "codbot \<equiv> codomain.bottom (f`P)"

lemma im_has_bottom: "domain.has_bottom P \<Longrightarrow> codomain.has_bottom (f`P)"
  using domain.bottomD ordsetmap by (fast intro: codomain.has_bottomI)

lemma im_bottom: "domain.has_bottom P \<Longrightarrow> f dombot = codbot"
  using domain.bottomD ordsetmap by (auto intro: codomain.bottomI)

end (* context OrderingSetMap *)

lemma (in OrderingSetIso) pullback_has_bottom:
  assumes "codomain.has_bottom (f`P)"
  shows   "domain.has_bottom P"
proof (rule domain.has_bottomI)
  from assms show "the_inv_into P f codbot \<in> P"
    using codomain.bottomD(1) the_inv_into_into[OF inj] by fast
  from assms show "\<And>x. x\<in>P \<Longrightarrow> the_inv_into P f codbot \<^bold>\<le> x"
    using codomain.bottomD inv_ordsetmap[of codbot] the_inv_into_f_f[OF inj]
    by    fastforce
qed

lemma (in OrderingSetIso) pullback_bottom:
  "\<lbrakk> domain.has_bottom P; x\<in>P; f x = codomain.bottom (f`P) \<rbrakk> \<Longrightarrow>
    x = domain.bottom P"
  using im_has_bottom codomain.bottomD(2) rev_ordsetmap
  by    (auto intro: domain.bottomI)

subsubsection {* Minimal and pseudominimal elements in sets *}

text {*
  We will call an element of a poset pseudominimal if the only element below it is the bottom of
  the poset.
*}

context ordering
begin

definition minimal_in :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "minimal_in P x \<equiv> x\<in>P \<and> (\<forall>z\<in>P. \<not> z \<^bold>< x)"

definition pseudominimal_in :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "pseudominimal_in P x \<equiv> minimal_in (P - {bottom P}) x"
\<comment> \<open>only makes sense for @{term "has_bottom P"}\<close>

lemma minimal_inD1: "minimal_in P x \<Longrightarrow> x\<in>P"
  using minimal_in_def by fast

lemma minimal_inD2: "minimal_in P x \<Longrightarrow> z\<in>P \<Longrightarrow> \<not> z \<^bold>< x"
  using minimal_in_def by fast

lemma pseudominimal_inD1: "pseudominimal_in P x \<Longrightarrow> x\<in>P"
  using pseudominimal_in_def minimal_inD1 by fast

lemma pseudominimal_inD2:
  "pseudominimal_in P x \<Longrightarrow> z\<in>P \<Longrightarrow> z\<^bold><x \<Longrightarrow> z = bottom P"
  using pseudominimal_in_def minimal_inD2 by fast

lemma pseudominimal_inI:
  assumes   "x\<in>P" "x \<noteq> bottom P" "\<And>z. z\<in>P \<Longrightarrow> z\<^bold><x \<Longrightarrow> z = bottom P"
  shows     "pseudominimal_in P x"
  using     assms
  unfolding pseudominimal_in_def minimal_in_def
  by        fast

lemma pseudominimal_ne_bottom: "pseudominimal_in P x \<Longrightarrow> x \<noteq> bottom P"
  using pseudominimal_in_def minimal_inD1 by fast

lemma pseudominimal_comp:
  "\<lbrakk> pseudominimal_in P x; pseudominimal_in P y; x\<^bold>\<le>y \<rbrakk> \<Longrightarrow> x = y"
  using pseudominimal_inD1 pseudominimal_inD2 pseudominimal_ne_bottom
        strict_iff_order[of x y]
  by    force

end (* context ordering *)

lemma pseudominimal_in_pow:
  assumes "order.pseudominimal_in (Pow A) x"
  shows "\<exists>a\<in>A. x = {a}"
proof-
  from assms obtain a where "{a} \<subseteq> x"
    using order.pseudominimal_ne_bottom bottom_pow[of A] by fast
  with assms show ?thesis
    using order.pseudominimal_inD1 order.pseudominimal_inD2[of _ x "{a}"]
          bottom_pow
    by    fast
qed

lemma pseudominimal_in_pow_singleton:
  "a\<in>A \<Longrightarrow> order.pseudominimal_in (Pow A) {a}"
  using singleton_pow bottom_pow by (fast intro: order.pseudominimal_inI)

lemma no_pseudominimal_in_pow_is_empty:
  "(\<And>x. \<not> order.pseudominimal_in (Pow A) {x}) \<Longrightarrow> A = {}"
  using pseudominimal_in_pow_singleton by (fast intro: equals0I)

lemma (in OrderingSetIso) pseudominimal_map:
  "domain.has_bottom P \<Longrightarrow> domain.pseudominimal_in P x \<Longrightarrow>
    codomain.pseudominimal_in (f`P) (f x)"
  using domain.pseudominimal_inD1 pullback_bottom
        domain.pseudominimal_ne_bottom rev_ordsetmap_strict
        domain.pseudominimal_inD2 im_bottom
  by    (blast intro: codomain.pseudominimal_inI)

lemma (in OrderingSetIso) pullback_pseudominimal_in:
  "\<lbrakk> domain.has_bottom P; x\<in>P; codomain.pseudominimal_in (f`P) (f x) \<rbrakk> \<Longrightarrow>
      domain.pseudominimal_in P x"
  using im_bottom codomain.pseudominimal_ne_bottom ordsetmap_strict
        codomain.pseudominimal_inD2 pullback_bottom
  by    (blast intro: domain.pseudominimal_inI)

subsubsection {* Set of elements below another *}

abbreviation (in ordering) below_in :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set" (infix ".\<^bold>\<le>" 70)
  where "P.\<^bold>\<le>x \<equiv> {y\<in>P. y\<^bold>\<le>x}"

abbreviation (in ord) below_in :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set" (infix ".\<le>" 70)
  where "P.\<le>x \<equiv> {y\<in>P. y\<le>x}"

context ordering
begin

lemma below_in_refl: "x\<in>P \<Longrightarrow> x \<in> P.\<^bold>\<le>x"
  using refl by fast

lemma below_in_singleton: "x\<in>P \<Longrightarrow> P.\<^bold>\<le>x \<subseteq> {y} \<Longrightarrow> y = x"
  using below_in_refl by fast

lemma bottom_in_below_in: "has_bottom P \<Longrightarrow> x\<in>P \<Longrightarrow> bottom P \<in> P.\<^bold>\<le>x"
  using bottomD by fast

lemma below_in_singleton_is_bottom:
  "\<lbrakk> has_bottom P; x\<in>P; P.\<^bold>\<le>x = {x} \<rbrakk> \<Longrightarrow> x = bottom P"
  using bottom_in_below_in by fast

lemma bottom_below_in:
  "has_bottom P \<Longrightarrow> x\<in>P \<Longrightarrow> bottom (P.\<^bold>\<le>x) = bottom P"
  using bottom_in_below_in by (fast intro: bottomI[THEN sym])

lemma bottom_below_in_relative:
  "\<lbrakk> has_bottom (P.\<^bold>\<le>y); x\<in>P; x\<^bold>\<le>y \<rbrakk> \<Longrightarrow> bottom (P.\<^bold>\<le>x) = bottom (P.\<^bold>\<le>y)"
  using bottomD trans by (blast intro: bottomI[THEN sym])

lemma has_bottom_pseudominimal_in_below_inI:
  assumes "has_bottom P" "x\<in>P" "pseudominimal_in P y" "y\<^bold>\<le>x"
  shows   "pseudominimal_in (P.\<^bold>\<le>x) y"
  using   assms(3,4) pseudominimal_inD1[OF assms(3)]
          pseudominimal_inD2[OF assms(3)]
          bottom_below_in[OF assms(1,2)] pseudominimal_ne_bottom
  by      (force intro: pseudominimal_inI)

lemma has_bottom_pseudominimal_in_below_in:
  assumes "has_bottom P" "x\<in>P" "pseudominimal_in (P.\<^bold>\<le>x) y"
  shows   "pseudominimal_in P y"
  using   pseudominimal_inD1[OF assms(3)]
          pseudominimal_inD2[OF assms(3)]
          pseudominimal_ne_bottom[OF assms(3)]
          bottom_below_in[OF assms(1,2)]
          strict_implies_order[of _ y] trans[of _ y x]
  by      (force intro: pseudominimal_inI)

lemma pseudominimal_in_below_in:
  assumes   "has_bottom (P.\<^bold>\<le>y)" "x\<in>P" "x\<^bold>\<le>y" "pseudominimal_in (P.\<^bold>\<le>x) w"
  shows     "pseudominimal_in (P.\<^bold>\<le>y) w"
  using     assms(3) trans[of w x y] trans[of _ w x] strict_iff_order
            pseudominimal_inD1[OF assms(4)]
            pseudominimal_inD2[OF assms(4)]
            pseudominimal_ne_bottom[OF assms(4)]
            bottom_below_in_relative[OF assms(1-3)]
  by        (force intro: pseudominimal_inI)

lemma collect_pseudominimals_below_in_less_eq_top:
  assumes "OrderingSetIso less_eq less (\<subseteq>) (\<subset>) (P.\<^bold>\<le>x) f"
          "f`(P.\<^bold>\<le>x) = Pow A" "a \<subseteq> {y. pseudominimal_in (P.\<^bold>\<le>x) y}"
  defines "w \<equiv> the_inv_into (P.\<^bold>\<le>x) f (\<Union>(f`a))"
  shows   "w \<^bold>\<le> x"
proof-
  from assms(2,3) have "(\<Union>(f`a)) \<in> f`(P.\<^bold>\<le>x)"
    using pseudominimal_inD1 by fastforce
  with assms(4) show ?thesis
    using OrderingSetIso.inj[OF assms(1)] the_inv_into_into[of f "P.\<^bold>\<le>x"] by force
qed

lemma collect_pseudominimals_below_in_poset:
  assumes   "OrderingSetIso less_eq less (\<subseteq>) (\<subset>) (P.\<^bold>\<le>x) f"
            "f`(P.\<^bold>\<le>x) = Pow A"
            "a \<subseteq> {y. pseudominimal_in (P.\<^bold>\<le>x) y}"
  defines   "w \<equiv> the_inv_into (P.\<^bold>\<le>x) f (\<Union>(f`a))"
  shows     "w \<in> P"
  using     assms(2-4) OrderingSetIso.inj[OF assms(1)] pseudominimal_inD1
            the_inv_into_into[of f "P.\<^bold>\<le>x" "\<Union>(f`a)"]
  by        force

lemma collect_pseudominimals_below_in_eq:
  assumes "x\<in>P" "OrderingSetIso less_eq less (\<subseteq>) (\<subset>) (P.\<^bold>\<le>x) f"
          "f`(P.\<^bold>\<le>x) = Pow A" "a \<subseteq> {y. pseudominimal_in (P.\<^bold>\<le>x) y}"
  defines w: "w \<equiv> the_inv_into (P.\<^bold>\<le>x) f (\<Union>(f`a))"
  shows   "a = {y. pseudominimal_in (P.\<^bold>\<le>w) y}"
proof
  from assms(3) have has_bot_ltx: "has_bottom (P.\<^bold>\<le>x)"
    using has_bottom_pow OrderingSetIso.pullback_has_bottom[OF assms(2)]
    by    auto
  from assms(3,4) have Un_fa: "(\<Union>(f`a)) \<in> f`(P.\<^bold>\<le>x)"
    using pseudominimal_inD1 by fastforce
  from assms have w_le_x: "w\<^bold>\<le>x" and w_P: "w\<in>P"
    using collect_pseudominimals_below_in_less_eq_top
          collect_pseudominimals_below_in_poset
    by    auto
  show "a \<subseteq> {y. pseudominimal_in (P.\<^bold>\<le>w) y}"
  proof
    fix y assume y: "y \<in> a"
    show "y \<in> {y. pseudominimal_in (P.\<^bold>\<le>w) y}"
    proof (rule CollectI, rule pseudominimal_inI, rule CollectI, rule conjI)
      from y assms(4) have y_le_x: "y \<in> P.\<^bold>\<le>x" using pseudominimal_inD1 by fast
      thus "y\<in>P" by simp
      from y w show "y \<^bold>\<le> w"
        using y_le_x Un_fa OrderingSetIso.inv_ordsetmap[OF assms(2)]
              the_inv_into_f_f[OF OrderingSetIso.inj, OF assms(2), of y]
        by    fastforce
      from assms(1) y assms(4) show "y \<noteq> bottom (P.\<^bold>\<le>w)"
        using w_P w_le_x has_bot_ltx bottom_below_in_relative
              pseudominimal_ne_bottom
        by    fast
    next
      fix z assume z: "z \<in> P.\<^bold>\<le>w" "z\<^bold><y"
      with y assms(4) have "z = bottom (P.\<^bold>\<le>x)"
        using w_le_x trans pseudominimal_inD2[ of "P.\<^bold>\<le>x" y z] by fast
      moreover from assms(1) have "bottom (P.\<^bold>\<le>w) = bottom (P.\<^bold>\<le>x)"
        using has_bot_ltx w_P w_le_x bottom_below_in_relative by fast
      ultimately show "z = bottom (P.\<^bold>\<le>w)" by simp
    qed
  qed
  show "a \<supseteq> {y. pseudominimal_in (P.\<^bold>\<le>w) y}"
  proof
    fix v assume "v \<in> {y. pseudominimal_in (P.\<^bold>\<le>w) y}"
    hence "pseudominimal_in (P.\<^bold>\<le>w) v" by fast
    moreover hence v_pm_ltx: "pseudominimal_in (P.\<^bold>\<le>x) v"
      using has_bot_ltx w_P w_le_x pseudominimal_in_below_in by fast
    ultimately
      have  "f v \<le> (\<Union>(f`a))"
      using w pseudominimal_inD1[of _ v] pseudominimal_inD1[of _ v] w_le_x w_P
            OrderingSetIso.ordsetmap[OF assms(2), of v w] Un_fa
            OrderingSetIso.inj[OF assms(2)]
            f_the_inv_into_f
      by    force
    with assms(3) obtain y where "y\<in>a" "f v \<subseteq> f y"
      using v_pm_ltx has_bot_ltx pseudominimal_in_pow
            OrderingSetIso.pseudominimal_map[OF assms(2)]
      by    force
    with assms(2,4) show "v \<in> a"
      using v_pm_ltx pseudominimal_inD1 pseudominimal_comp[of _ v y]
            OrderingSetIso.rev_ordsetmap[OF assms(2), of v y]
      by    fast
  qed
qed

end (* context ordering *)

subsubsection {* Lower bounds *}

context ordering
begin

definition lbound_of :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "lbound_of x y b \<equiv> b\<^bold>\<le>x \<and> b\<^bold>\<le>y"

lemma lbound_ofI: "b\<^bold>\<le>x \<Longrightarrow> b\<^bold>\<le>y \<Longrightarrow> lbound_of x y b"
  using lbound_of_def by fast

lemma lbound_ofD1: "lbound_of x y b \<Longrightarrow> b\<^bold>\<le>x"
  using lbound_of_def by fast

lemma lbound_ofD2: "lbound_of x y b \<Longrightarrow> b\<^bold>\<le>y"
  using lbound_of_def by fast

definition glbound_in_of :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "glbound_in_of P x y b \<equiv>
          b\<in>P \<and> lbound_of x y b \<and> (\<forall>a\<in>P. lbound_of x y a \<longrightarrow> a\<^bold>\<le>b)"

lemma glbound_in_ofI:
  "\<lbrakk> b\<in>P; lbound_of x y b; \<And>a. a\<in>P \<Longrightarrow> lbound_of x y a \<Longrightarrow> a\<^bold>\<le>b \<rbrakk> \<Longrightarrow>
    glbound_in_of P x y b"
  using glbound_in_of_def by auto

lemma glbound_in_ofD_in: "glbound_in_of P x y b \<Longrightarrow> b\<in>P"
  using glbound_in_of_def by fast

lemma glbound_in_ofD_lbound: "glbound_in_of P x y b \<Longrightarrow> lbound_of x y b"
  using glbound_in_of_def by fast

lemma glbound_in_ofD_glbound:
  "glbound_in_of P x y b \<Longrightarrow> a\<in>P \<Longrightarrow> lbound_of x y a \<Longrightarrow> a\<^bold>\<le>b"
  using glbound_in_of_def by fast

lemma glbound_in_of_less_eq1: "glbound_in_of P x y b \<Longrightarrow> b\<^bold>\<le>x"
  using glbound_in_ofD_lbound lbound_ofD1 by fast

lemma glbound_in_of_less_eq2: "glbound_in_of P x y b \<Longrightarrow> b\<^bold>\<le>y"
  using glbound_in_ofD_lbound lbound_ofD2 by fast

lemma pseudominimal_in_below_in_less_eq_glbound:
  assumes "pseudominimal_in (P.\<^bold>\<le>x) w" "pseudominimal_in (P.\<^bold>\<le>y) w"
          "glbound_in_of P x y b"
  shows   "w \<^bold>\<le> b"
  using assms lbound_ofI glbound_in_ofD_glbound
        pseudominimal_inD1[of "P.\<^bold>\<le>x"] pseudominimal_inD1[of "P.\<^bold>\<le>y"]
  by    fast

end (* context ordering *)

subsubsection {* Simplex-like posets *}

text {* Define a poset to be simplex-like if it is isomorphic to the power set of some set. *}

context ordering
begin

definition simplex_like :: "'a set \<Rightarrow> bool"
  where "simplex_like P \<equiv> finite P \<and>
          (\<exists>f A::nat set.
            OrderingSetIso less_eq less (\<subseteq>) (\<subset>) P f \<and> f`P = Pow A
          )"

lemma simplex_likeI:
  assumes "finite P" "OrderingSetIso less_eq less (\<subseteq>) (\<subset>) P f"
          "f`P = Pow (A::nat set)"
  shows   "simplex_like P"
  using assms simplex_like_def by auto

lemma simplex_likeD_finite: "simplex_like P \<Longrightarrow> finite P"
  using simplex_like_def by simp

lemma simplex_likeD_iso:
  "simplex_like P \<Longrightarrow>
    \<exists>f A::nat set. OrderingSetIso less_eq less (\<subseteq>) (\<subset>) P f \<and> f`P = Pow A"
  using simplex_like_def by simp

lemma simplex_like_has_bottom: "simplex_like P \<Longrightarrow> has_bottom P"
  using simplex_likeD_iso has_bottom_pow OrderingSetIso.pullback_has_bottom
  by    fastforce

lemma simplex_like_no_pseudominimal_imp_singleton:
  assumes "simplex_like P" "\<And>x. \<not> pseudominimal_in P x"
  shows "\<exists>p. P = {p}"
proof-
  obtain f and A::"nat set"
    where fA: "OrderingSetIso less_eq less (\<subseteq>) (\<subset>) P f" "f`P = Pow A"
    using simplex_likeD_iso[OF assms(1)]
    by    auto
  define e where e: "e \<equiv> {}:: nat set"
  with fA(2) have "e \<in> f`P" using Pow_bottom by simp
  from this obtain p where "p \<in> P" "f p = e" by fast
  have "\<And>x. \<not> order.pseudominimal_in (Pow A) {x}"
  proof
    fix x::nat assume "order.pseudominimal_in (Pow A) {x}"
    moreover with fA(2) have "{x} \<in> f`P"
      using order.pseudominimal_inD1 by fastforce
    ultimately show False
      using assms fA simplex_like_has_bottom
            OrderingSetIso.pullback_pseudominimal_in
      by    fastforce
  qed
  with e fA(2) show ?thesis
    using no_pseudominimal_in_pow_is_empty
          inj_on_to_singleton[OF OrderingSetIso.inj, OF fA(1)]
    by    force
qed

lemma simplex_like_no_pseudominimal_in_below_in_imp_singleton:
  "\<lbrakk> x\<in>P; simplex_like (P.\<^bold>\<le>x); \<And>z. \<not> pseudominimal_in (P.\<^bold>\<le>x) z \<rbrakk> \<Longrightarrow>
    P.\<^bold>\<le>x = {x}"
  using simplex_like_no_pseudominimal_imp_singleton below_in_singleton[of x P]
  by    fast

lemma pseudo_simplex_like_has_bottom:
  "OrderingSetIso less_eq less (\<subseteq>) (\<subset>) P f \<Longrightarrow> f`P = Pow A \<Longrightarrow>
    has_bottom P"
  using has_bottom_pow OrderingSetIso.pullback_has_bottom by fastforce

lemma pseudo_simplex_like_above_pseudominimal_is_top:
  assumes "OrderingSetIso less_eq less (\<subseteq>) (\<subset>) P f" "f`P = Pow A" "t\<in>P"
          "\<And>x. pseudominimal_in P x \<Longrightarrow> x \<^bold>\<le> t"
  shows   "f t = A"
proof
  from assms(2,3) show "f t \<subseteq> A" by fast
  show "A \<subseteq> f t"
  proof
    fix a assume "a\<in>A"
    moreover with assms(2) have "{a} \<in> f`P" by simp
    ultimately show "a \<in> f t"
      using assms pseudominimal_in_pow_singleton[of a A]
            pseudo_simplex_like_has_bottom[of P f]
            OrderingSetIso.pullback_pseudominimal_in[OF assms(1)]
            OrderingSetIso.ordsetmap[OF assms(1), of _ t]
      by    force
  qed
qed

lemma pseudo_simplex_like_below_in_above_pseudominimal_is_top:
  assumes "x\<in>P" "OrderingSetIso less_eq less (\<subseteq>) (\<subset>) (P.\<^bold>\<le>x) f"
          "f`(P.\<^bold>\<le>x) = Pow A" "t \<in> P.\<^bold>\<le>x"
          "\<And>y. pseudominimal_in (P.\<^bold>\<le>x) y \<Longrightarrow> y \<^bold>\<le> t"
  shows   "t = x"
  using   assms(1,3-5)
          pseudo_simplex_like_above_pseudominimal_is_top[OF assms(2)]
          below_in_refl[of x P] OrderingSetIso.ordsetmap[OF assms(2), of t x]
          inj_onD[OF OrderingSetIso.inj[OF assms(2)], of t x]
  by      auto

lemma simplex_like_below_in_above_pseudominimal_is_top:
  assumes "x\<in>P" "simplex_like (P.\<^bold>\<le>x)" "t \<in> P.\<^bold>\<le>x"
          "\<And>y. pseudominimal_in (P.\<^bold>\<le>x) y \<Longrightarrow> y \<^bold>\<le> t"
  shows   "t = x"
  using assms simplex_likeD_iso
        pseudo_simplex_like_below_in_above_pseudominimal_is_top[of x P _ _ t]
  by    blast

end (* context ordering *)

lemma (in OrderingSetIso) simplex_like_map:
  assumes "domain.simplex_like P"
  shows   "codomain.simplex_like (f`P)"
proof-
  obtain g::"'a \<Rightarrow> nat set" and A::"nat set"
    where gA: "OrderingSetIso (\<^bold>\<le>) (\<^bold><) (\<subseteq>) (\<subset>) P g" "g`P = Pow A"
    using domain.simplex_likeD_iso[OF assms]
    by    auto
  from gA(1) inj
    have  "OrderingSetIso (\<^bold>\<le>*) (\<^bold><*) (\<subseteq>) (\<subset>) (f`P)
            (g \<circ> (the_inv_into P f))"
    using OrderingSetIso.iso_comp[OF inv_iso] the_inv_into_onto
    by    fast
  moreover from gA(2) inj have "(g \<circ> (the_inv_into P f)) ` (f`P) = Pow A"
    using the_inv_into_onto by (auto simp add: image_comp[THEN sym])
  moreover from assms have "finite (f`P)"
    using domain.simplex_likeD_finite by fast
  ultimately show ?thesis by (auto intro: codomain.simplex_likeI)
qed

lemma (in OrderingSetIso) pullback_simplex_like:
  assumes "finite P" "codomain.simplex_like (f`P)"
  shows   "domain.simplex_like P"
proof-
  obtain g::"'b \<Rightarrow> nat set" and A::"nat set"
    where gA:  "OrderingSetIso (\<^bold>\<le>*) (\<^bold><*) (\<subseteq>) (\<subset>) (f`P) g"
               "g`(f`P) = Pow A"
    using codomain.simplex_likeD_iso[OF assms(2)]
    by    auto
  from assms(1) gA(2) show ?thesis
    using iso_comp[OF gA(1)]
    by    (auto intro: domain.simplex_likeI simp add: image_comp)
qed

lemma simplex_like_pow:
  assumes "finite A"
  shows "order.simplex_like (Pow A)"
proof-
  from assms obtain f::"'a\<Rightarrow>nat" where "inj_on f A"
    using finite_imp_inj_to_nat_seg[of A] by auto
  hence "subset_ordering_iso (Pow A) ((`) f)"
    using induced_pow_fun_subset_ordering_iso by fast
  with assms show ?thesis using induced_pow_fun_surj
    by (blast intro: order.simplex_likeI)
qed

subsubsection {* The superset ordering *}

abbreviation "supset_has_bottom       \<equiv> ordering.has_bottom       (\<supseteq>)"
abbreviation "supset_bottom           \<equiv> ordering.bottom           (\<supseteq>)"
abbreviation "supset_lbound_of        \<equiv> ordering.lbound_of        (\<supseteq>)"
abbreviation "supset_glbound_in_of    \<equiv> ordering.glbound_in_of    (\<supseteq>)"
abbreviation "supset_simplex_like     \<equiv> ordering.simplex_like     (\<supseteq>) (\<supset>)"
abbreviation "supset_pseudominimal_in \<equiv>
                ordering.pseudominimal_in (\<supseteq>) (\<supset>)"

abbreviation supset_below_in :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" (infix ".\<supseteq>" 70)
  where "P.\<supseteq>A \<equiv> ordering.below_in (\<supseteq>) P A"

lemma supset_poset: "ordering (\<supseteq>) (\<supset>)" ..

lemmas supset_bottomI            = ordering.bottomI            [OF supset_poset]
lemmas supset_pseudominimal_inI  = ordering.pseudominimal_inI  [OF supset_poset]
lemmas supset_pseudominimal_inD1 = ordering.pseudominimal_inD1 [OF supset_poset]
lemmas supset_pseudominimal_inD2 = ordering.pseudominimal_inD2 [OF supset_poset]
lemmas supset_lbound_ofI         = ordering.lbound_ofI         [OF supset_poset]
lemmas supset_lbound_of_def      = ordering.lbound_of_def      [OF supset_poset]
lemmas supset_glbound_in_ofI     = ordering.glbound_in_ofI     [OF supset_poset]
lemmas supset_pseudominimal_ne_bottom =
  ordering.pseudominimal_ne_bottom[OF supset_poset]
lemmas supset_has_bottom_pseudominimal_in_below_inI =
  ordering.has_bottom_pseudominimal_in_below_inI[OF supset_poset]
lemmas supset_has_bottom_pseudominimal_in_below_in =
  ordering.has_bottom_pseudominimal_in_below_in[OF supset_poset]

lemma OrderingSetIso_pow_complement:
  "OrderingSetIso (\<supseteq>) (\<supset>) (\<subseteq>) (\<subset>) (Pow A) ((-) A)"
  using inj_on_minus_set by (fast intro: OrderingSetIsoI_orders_greater2less)

lemma simplex_like_pow_above_in:
  assumes "finite A" "X\<subseteq>A"
  shows   "supset_simplex_like ((Pow A).\<supseteq>X)"
proof (
  rule OrderingSetIso.pullback_simplex_like, rule OrderingSetIso.iso_subset,
  rule OrderingSetIso_pow_complement
)
  from assms(1) show "finite ((Pow A).\<supseteq>X)" by simp
  from assms(1) have "finite (Pow (A-X))" by fast
  moreover from assms(2) have "((-) A) ` ((Pow A).\<supseteq>X) = Pow (A-X)"
    by auto
  ultimately
    show  "ordering.simplex_like (\<subseteq>) (\<subset>) ( ((-) A) ` ((Pow A).\<supseteq>X))"
    using simplex_like_pow
    by    fastforce
qed fast

end (* theory *)
