(*  
  Title:    Order_Predicates.thy
  Author:   Manuel Eberl, TU München

  Locales for order relations modelled as predicates (as opposed to sets of pairs).
*)
section \<open>Order Relations as Binary Predicates\<close>

theory Order_Predicates
imports 
  Main
  "HOL-Library.Disjoint_Sets"
  "HOL-Library.Permutations"
  "List-Index.List_Index"
begin



subsection \<open>Basic Operations on Relations\<close>

text \<open>The type of binary relations\<close>
type_synonym 'a relation = "'a \<Rightarrow> 'a \<Rightarrow> bool"

definition map_relation :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b relation \<Rightarrow> 'a relation" where
  "map_relation f R = (\<lambda>x y. R (f x) (f y))"

definition restrict_relation :: "'a set \<Rightarrow> 'a relation \<Rightarrow> 'a relation" where
  "restrict_relation A R = (\<lambda>x y. x \<in> A \<and> y \<in> A \<and> R x y)"

lemma restrict_relation_restrict_relation [simp]:
  "restrict_relation A (restrict_relation B R) = restrict_relation (A \<inter> B) R"
  by (intro ext) (auto simp add: restrict_relation_def)

lemma restrict_relation_empty [simp]: "restrict_relation {} R = (\<lambda>_ _. False)"
  by (simp add: restrict_relation_def)

lemma restrict_relation_UNIV [simp]: "restrict_relation UNIV R = R"
  by (simp add: restrict_relation_def)


subsection \<open>Preorders\<close>

text \<open>Preorders are reflexive and transitive binary relations.\<close>
locale preorder_on =
  fixes carrier :: "'a set"
  fixes le :: "'a relation"
  assumes not_outside: "le x y \<Longrightarrow> x \<in> carrier" "le x y \<Longrightarrow> y \<in> carrier"
  assumes refl: "x \<in> carrier \<Longrightarrow> le x x"
  assumes trans: "le x y \<Longrightarrow> le y z \<Longrightarrow> le x z"
begin

lemma carrier_eq: "carrier = {x. le x x}"
  using not_outside refl by auto
  
lemma preorder_on_map:
  "preorder_on (f -` carrier) (map_relation f le)"
  by unfold_locales (auto dest: not_outside simp: map_relation_def refl elim: trans)
  
lemma preorder_on_restrict:
  "preorder_on (carrier \<inter> A) (restrict_relation A le)"
  by unfold_locales (auto simp: restrict_relation_def refl intro: trans not_outside)

lemma preorder_on_restrict_subset:
  "A \<subseteq> carrier \<Longrightarrow> preorder_on A (restrict_relation A le)"
  using preorder_on_restrict[of A] by (simp add: Int_absorb1)

lemma restrict_relation_carrier [simp]:
  "restrict_relation carrier le = le"
  using not_outside by (intro ext) (auto simp add: restrict_relation_def)

end
  

subsection \<open>Total preorders\<close>

text \<open>Total preorders are preorders where any two elements are comparable.\<close>
locale total_preorder_on = preorder_on +
  assumes total: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> le x y \<or> le y x"
begin

lemma total': "\<not>le x y \<Longrightarrow> x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> le y x"
  using total[of x y] by blast

lemma total_preorder_on_map:
  "total_preorder_on (f -` carrier) (map_relation f le)"
proof -
  interpret R': preorder_on "f -` carrier" "map_relation f le"
    using preorder_on_map[of f] .
  show ?thesis by unfold_locales (simp add: map_relation_def total)
qed

lemma total_preorder_on_restrict:
  "total_preorder_on (carrier \<inter> A) (restrict_relation A le)"
proof -
  interpret R': preorder_on "carrier \<inter> A" "restrict_relation A le"
    by (rule preorder_on_restrict)
  from total show ?thesis
    by unfold_locales (auto simp: restrict_relation_def)
qed

lemma total_preorder_on_restrict_subset:
  "A \<subseteq> carrier \<Longrightarrow> total_preorder_on A (restrict_relation A le)"
  using total_preorder_on_restrict[of A] by (simp add: Int_absorb1)

end


text \<open>Some fancy notation for order relations\<close>
abbreviation (input) weakly_preferred :: "'a \<Rightarrow> 'a relation \<Rightarrow> 'a \<Rightarrow> bool"
    ("_ \<preceq>[_] _" [51,10,51] 60) where
  "a \<preceq>[R] b \<equiv> R a b"
  
definition strongly_preferred ("_ \<prec>[_] _" [51,10,51] 60) where
  "a \<prec>[R] b \<equiv> (a \<preceq>[R] b) \<and> \<not>(b \<preceq>[R] a)"

definition indifferent ("_ \<sim>[_] _" [51,10,51] 60) where
  "a \<sim>[R] b \<equiv> (a \<preceq>[R] b) \<and> (b \<preceq>[R] a)"

abbreviation (input) weakly_not_preferred ("_ \<succeq>[_] _" [51,10,51] 60) where
  "a \<succeq>[R] b \<equiv> b \<preceq>[R] a"
  term "a \<succeq>[R] b \<longleftrightarrow> b \<preceq>[R] a"

abbreviation (input) strongly_not_preferred ("_ \<succ>[_] _" [51,10,51] 60) where
  "a \<succ>[R] b \<equiv> b \<prec>[R] a"

context preorder_on
begin

lemma strict_trans: "a \<prec>[le] b \<Longrightarrow> b \<prec>[le] c \<Longrightarrow> a \<prec>[le] c"
  unfolding strongly_preferred_def by (blast intro: trans)

lemma weak_strict_trans: "a \<preceq>[le] b \<Longrightarrow> b \<prec>[le] c \<Longrightarrow> a \<prec>[le] c"
  unfolding strongly_preferred_def by (blast intro: trans)

lemma strict_weak_trans: "a \<prec>[le] b \<Longrightarrow> b \<preceq>[le] c \<Longrightarrow> a \<prec>[le] c"
  unfolding strongly_preferred_def by (blast intro: trans)

end
  
lemma (in total_preorder_on) not_weakly_preferred_iff:
  "a \<in> carrier \<Longrightarrow> b \<in> carrier \<Longrightarrow> \<not>a \<preceq>[le] b \<longleftrightarrow> b \<prec>[le] a"
  using total[of a b] by (auto simp: strongly_preferred_def)

lemma (in total_preorder_on) not_strongly_preferred_iff:
  "a \<in> carrier \<Longrightarrow> b \<in> carrier \<Longrightarrow> \<not>a \<prec>[le] b \<longleftrightarrow> b \<preceq>[le] a"
  using total[of a b] by (auto simp: strongly_preferred_def)



subsection \<open>Orders\<close>

locale order_on = preorder_on +
  assumes antisymmetric: "le x y \<Longrightarrow> le y x \<Longrightarrow> x = y"

locale linorder_on = order_on carrier le + total_preorder_on carrier le for carrier le


subsection \<open>Maximal elements\<close>

text \<open>
  Maximal elements are elements in a preorder for which there exists no strictly greater element.
\<close>

definition Max_wrt_among :: "'a relation \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "Max_wrt_among R A = {x\<in>A. R x x \<and> (\<forall>y\<in>A. R x y \<longrightarrow> R y x)}"

lemma Max_wrt_among_cong:
  assumes "restrict_relation A R = restrict_relation A R'"
  shows   "Max_wrt_among R A = Max_wrt_among R' A"
proof -
  from assms have "R x y \<longleftrightarrow> R' x y" if "x \<in> A" "y \<in> A" for x y
    using that by (auto simp: restrict_relation_def fun_eq_iff)
  thus ?thesis unfolding Max_wrt_among_def by blast
qed

definition Max_wrt :: "'a relation \<Rightarrow> 'a set" where
  "Max_wrt R = Max_wrt_among R UNIV"
  
lemma Max_wrt_altdef: "Max_wrt R = {x. R x x \<and> (\<forall>y. R x y \<longrightarrow> R y x)}"
  unfolding Max_wrt_def Max_wrt_among_def by simp

context preorder_on
begin

lemma Max_wrt_among_preorder:
  "Max_wrt_among le A = {x\<in>carrier \<inter> A. \<forall>y\<in>carrier \<inter> A. le x y \<longrightarrow> le y x}"
  unfolding Max_wrt_among_def using not_outside refl by blast

lemma Max_wrt_preorder:
  "Max_wrt le = {x\<in>carrier. \<forall>y\<in>carrier. le x y \<longrightarrow> le y x}"
  unfolding Max_wrt_altdef using not_outside refl by blast

lemma Max_wrt_among_subset:
  "Max_wrt_among le A \<subseteq> carrier" "Max_wrt_among le A \<subseteq> A"
  unfolding Max_wrt_among_preorder by auto
  
lemma Max_wrt_subset:
  "Max_wrt le \<subseteq> carrier"
  unfolding Max_wrt_preorder by auto

lemma Max_wrt_among_nonempty:
  assumes "B \<inter> carrier \<noteq> {}" "finite (B \<inter> carrier)"
  shows   "Max_wrt_among le B \<noteq> {}"
proof -
  define A where "A = B \<inter> carrier"
  have "A \<subseteq> carrier" by (simp add: A_def)
  from assms(2,1)[folded A_def] this have "{x\<in>A. (\<forall>y\<in>A. le x y \<longrightarrow> le y x)} \<noteq> {}"
  proof (induction A rule: finite_ne_induct)
    case (singleton x)
    thus ?case by (auto simp: refl)
  next
    case (insert x A)
    then obtain y where y: "y \<in> A" "\<And>z. z \<in> A \<Longrightarrow> le y z \<Longrightarrow> le z y" by blast
    thus ?case using insert.prems
      by (cases "le y x") (blast intro: trans)+
  qed
  thus ?thesis by (simp add: A_def Max_wrt_among_preorder Int_commute)
qed
  
lemma Max_wrt_nonempty:
  "carrier \<noteq> {} \<Longrightarrow> finite carrier \<Longrightarrow> Max_wrt le \<noteq> {}"
  using Max_wrt_among_nonempty[of UNIV] by (simp add: Max_wrt_def)

lemma Max_wrt_among_map_relation_vimage:
  "f -` Max_wrt_among le A \<subseteq> Max_wrt_among (map_relation f le) (f -` A)"
  by (auto simp: Max_wrt_among_def map_relation_def)

lemma Max_wrt_map_relation_vimage:
  "f -` Max_wrt le \<subseteq> Max_wrt (map_relation f le)"
  by (auto simp: Max_wrt_altdef map_relation_def)

lemma image_subset_vimage_the_inv_into: 
  assumes "inj_on f A" "B \<subseteq> A"
  shows   "f ` B \<subseteq> the_inv_into A f -` B"
  using assms by (auto simp: the_inv_into_f_f)

lemma Max_wrt_among_map_relation_bij_subset:
  assumes "bij (f :: 'a \<Rightarrow> 'b)"
  shows   "f ` Max_wrt_among le A \<subseteq> 
             Max_wrt_among (map_relation (inv f) le) (f ` A)"
  using assms Max_wrt_among_map_relation_vimage[of "inv f" A]
  by (simp add: bij_imp_bij_inv inv_inv_eq bij_vimage_eq_inv_image)
  
lemma Max_wrt_among_map_relation_bij:
  assumes "bij f"
  shows   "f ` Max_wrt_among le A = Max_wrt_among (map_relation (inv f) le) (f ` A)"
proof (intro equalityI Max_wrt_among_map_relation_bij_subset assms)
  interpret R: preorder_on "f ` carrier" "map_relation (inv f) le"
    using preorder_on_map[of "inv f"] assms 
      by (simp add: bij_imp_bij_inv bij_vimage_eq_inv_image inv_inv_eq)
  show "Max_wrt_among (map_relation (inv f) le) (f ` A) \<subseteq> f ` Max_wrt_among le A"
    unfolding Max_wrt_among_preorder R.Max_wrt_among_preorder 
    using assms bij_is_inj[OF assms]
    by (auto simp: map_relation_def inv_f_f image_Int [symmetric])
qed

lemma Max_wrt_map_relation_bij:
  "bij f \<Longrightarrow> f ` Max_wrt le = Max_wrt (map_relation (inv f) le)"
proof -
  assume bij: "bij f"
  interpret R: preorder_on "f ` carrier" "map_relation (inv f) le"
    using preorder_on_map[of "inv f"] bij
      by (simp add: bij_imp_bij_inv bij_vimage_eq_inv_image inv_inv_eq)
  from bij show ?thesis
    unfolding R.Max_wrt_preorder Max_wrt_preorder
    by (auto simp: map_relation_def inv_f_f bij_is_inj)
qed

lemma Max_wrt_among_mono:
  "le x y \<Longrightarrow> x \<in> Max_wrt_among le A \<Longrightarrow> y \<in> A \<Longrightarrow> y \<in> Max_wrt_among le A"
  using not_outside by (auto simp: Max_wrt_among_preorder intro: trans)

lemma Max_wrt_mono:
  "le x y \<Longrightarrow> x \<in> Max_wrt le \<Longrightarrow> y \<in> Max_wrt le"
  unfolding Max_wrt_def using Max_wrt_among_mono[of x y UNIV] by blast

end


context total_preorder_on
begin

lemma Max_wrt_among_total_preorder:
  "Max_wrt_among le A = {x\<in>carrier \<inter> A. \<forall>y\<in>carrier \<inter> A. le y x}"
  unfolding Max_wrt_among_preorder using total by blast

lemma Max_wrt_total_preorder:
  "Max_wrt le = {x\<in>carrier. \<forall>y\<in>carrier. le y x}"
  unfolding Max_wrt_preorder using total by blast

lemma decompose_Max:
  assumes A: "A \<subseteq> carrier"
  defines "M \<equiv> Max_wrt_among le A"
  shows   "restrict_relation A le = (\<lambda>x y. x \<in> A \<and> y \<in> M \<or> (y \<notin> M \<and> restrict_relation (A - M) le x y))"
  using A by (intro ext) (auto simp: M_def Max_wrt_among_total_preorder 
                            restrict_relation_def Int_absorb1 intro: trans)

end


subsection \<open>Weak rankings\<close>

inductive of_weak_ranking :: "'alt set list \<Rightarrow> 'alt relation" where
  "i \<le> j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> x \<in> xs ! i \<Longrightarrow> y \<in> xs ! j \<Longrightarrow> 
     x \<succeq>[of_weak_ranking xs] y"

lemma of_weak_ranking_Nil [simp]: "of_weak_ranking [] = (\<lambda>_ _. False)"
  by (intro ext) (simp add: of_weak_ranking.simps)

lemma of_weak_ranking_Nil' [code]: "of_weak_ranking [] x y = False"
  by simp
  
lemma of_weak_ranking_Cons [code]:
  "x \<succeq>[of_weak_ranking (z#zs)] y \<longleftrightarrow> x \<in> z \<and> y \<in> \<Union>(set (z#zs)) \<or> x \<succeq>[of_weak_ranking zs] y" 
      (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  assume ?lhs
  then obtain i j 
    where ij: "i < length (z#zs)" "j < length (z#zs)" "i \<le> j" "x \<in> (z#zs) ! i" "y \<in> (z#zs) ! j"
    by (blast elim: of_weak_ranking.cases)
  thus ?rhs by (cases i; cases j) (force intro: of_weak_ranking.intros)+
next
  assume ?rhs
  thus ?lhs
  proof (elim disjE conjE)
    assume "x \<in> z" "y \<in> \<Union>(set (z # zs))"
    then obtain j where "j < length (z # zs)" "y \<in> (z # zs) ! j" 
      by (subst (asm) set_conv_nth) auto
    with \<open>x \<in> z\<close> show "of_weak_ranking (z # zs) y x" 
      by (intro of_weak_ranking.intros[of 0 j]) auto
  next
    assume "of_weak_ranking zs y x"
    then obtain i j where "i < length zs" "j < length zs" "i \<le> j" "x \<in> zs ! i" "y \<in> zs ! j"
      by (blast elim: of_weak_ranking.cases)
    thus "of_weak_ranking (z # zs) y x"
      by (intro of_weak_ranking.intros[of "Suc i" "Suc j"]) auto
  qed
qed

lemma of_weak_ranking_indifference:
  assumes "A \<in> set xs" "x \<in> A" "y \<in> A"
  shows   "x \<preceq>[of_weak_ranking xs] y"
  using assms by (induction xs) (auto simp: of_weak_ranking_Cons)


lemma of_weak_ranking_map:
  "map_relation f (of_weak_ranking xs) = of_weak_ranking (map ((-`) f) xs)"
  by (intro ext, induction xs)
     (simp_all add: map_relation_def of_weak_ranking_Cons)

lemma of_weak_ranking_permute':
  assumes "f permutes (\<Union>(set xs))"
  shows   "map_relation f (of_weak_ranking xs) = of_weak_ranking (map ((`) (inv f)) xs)"
proof -
  have "map_relation f (of_weak_ranking xs) = of_weak_ranking (map ((-`) f) xs)"
    by (rule of_weak_ranking_map)
  also from assms have "map ((-`) f) xs = map ((`) (inv f)) xs"
    by (intro map_cong refl) (simp_all add: bij_vimage_eq_inv_image permutes_bij)
  finally show ?thesis .
qed 

lemma of_weak_ranking_permute:
  assumes "f permutes (\<Union>(set xs))"
  shows   "of_weak_ranking (map ((`) f) xs) = map_relation (inv f) (of_weak_ranking xs)"
  using of_weak_ranking_permute'[OF permutes_inv[OF assms]] assms
  by (simp add: inv_inv_eq permutes_bij)

definition is_weak_ranking where
  "is_weak_ranking xs \<longleftrightarrow> ({} \<notin> set xs) \<and>
     (\<forall>i j. i < length xs \<and> j < length xs \<and> i \<noteq> j \<longrightarrow> xs ! i \<inter> xs ! j = {})"

definition is_finite_weak_ranking where
  "is_finite_weak_ranking xs \<longleftrightarrow> is_weak_ranking xs \<and> (\<forall>x\<in>set xs. finite x)"

definition weak_ranking :: "'alt relation \<Rightarrow> 'alt set list" where
  "weak_ranking R = (SOME xs. is_weak_ranking xs \<and> R = of_weak_ranking xs)"

lemma is_weak_rankingI [intro?]:
  assumes "{} \<notin> set xs" "\<And>i j. i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> i \<noteq> j \<Longrightarrow> xs ! i \<inter> xs ! j = {}"
  shows   "is_weak_ranking xs"
  using assms by (auto simp add: is_weak_ranking_def)

lemma is_weak_ranking_nonempty: "is_weak_ranking xs \<Longrightarrow> {} \<notin> set xs"
  by (simp add: is_weak_ranking_def) 
     
lemma is_weak_rankingD:
  assumes "is_weak_ranking xs" "i < length xs" "j < length xs" "i \<noteq> j"
  shows   "xs ! i \<inter> xs ! j = {}"
  using assms by (simp add: is_weak_ranking_def)
  
lemma is_weak_ranking_iff:
  "is_weak_ranking xs \<longleftrightarrow> distinct xs \<and> disjoint (set xs) \<and> {} \<notin> set xs"
proof safe
  assume wf: "is_weak_ranking xs"
  from wf show "disjoint (set xs)"
    by (auto simp: disjoint_def is_weak_ranking_def set_conv_nth)
  show "distinct xs"
  proof (subst distinct_conv_nth, safe)
    fix i j assume ij: "i < length xs" "j < length xs" "i \<noteq> j" "xs ! i = xs ! j"
    then have "xs ! i \<inter> xs ! j = {}" by (intro is_weak_rankingD wf)
    with ij have "xs ! i = {}" by simp
    with ij have "{} \<in> set xs" by (auto simp: set_conv_nth)
    moreover from wf ij have "{} \<notin> set xs" by (intro is_weak_ranking_nonempty wf)
    ultimately show False by contradiction
 qed
next
  assume A: "distinct xs" "disjoint (set xs)" "{} \<notin> set xs"
  thus "is_weak_ranking xs"
    by (intro is_weak_rankingI) (auto simp: disjoint_def distinct_conv_nth)
qed (simp_all add: is_weak_ranking_nonempty)

lemma is_weak_ranking_rev [simp]: "is_weak_ranking (rev xs) \<longleftrightarrow> is_weak_ranking xs"
  by (simp add: is_weak_ranking_iff)

lemma is_weak_ranking_map_inj:
  assumes "is_weak_ranking xs" "inj_on f (\<Union>(set xs))"
  shows   "is_weak_ranking (map ((`) f) xs)"
  using assms by (auto simp: is_weak_ranking_iff distinct_map inj_on_image disjoint_image)

lemma of_weak_ranking_rev [simp]:
  "of_weak_ranking (rev xs) (x::'a) y \<longleftrightarrow> of_weak_ranking xs y x"
proof -
  have "of_weak_ranking (rev xs) y x" if "of_weak_ranking xs x y" for xs and x y :: 'a
  proof -
    from that obtain i j where "i < length xs" "j < length xs" "x \<in> xs ! i" "y \<in> xs ! j" "i \<ge> j"
      by (elim of_weak_ranking.cases) simp_all
    thus ?thesis
      by (intro of_weak_ranking.intros[of "length xs - i - 1" "length xs - j - 1"] diff_le_mono2)
         (auto simp: diff_le_mono2 rev_nth)
  qed
  from this[of xs y x] this[of "rev xs" x y] show ?thesis by (intro iffI) simp_all
qed


lemma is_weak_ranking_Nil [simp, code]: "is_weak_ranking []"
  by (auto simp: is_weak_ranking_def)

lemma is_finite_weak_ranking_Nil [simp, code]: "is_finite_weak_ranking []"
  by (auto simp: is_finite_weak_ranking_def)

lemma is_weak_ranking_Cons_empty [simp]:
  "\<not>is_weak_ranking ({} # xs)" by (simp add: is_weak_ranking_def)

lemma is_finite_weak_ranking_Cons_empty [simp]:
  "\<not>is_finite_weak_ranking ({} # xs)" by (simp add: is_finite_weak_ranking_def)
  
lemma is_weak_ranking_singleton [simp]:
  "is_weak_ranking [x] \<longleftrightarrow> x \<noteq> {}" 
  by (auto simp add: is_weak_ranking_def)

lemma is_finite_weak_ranking_singleton [simp]:
  "is_finite_weak_ranking [x] \<longleftrightarrow> x \<noteq> {} \<and> finite x" 
  by (auto simp add: is_finite_weak_ranking_def)
  
lemma is_weak_ranking_append:
  "is_weak_ranking (xs @ ys) \<longleftrightarrow> 
      is_weak_ranking xs \<and> is_weak_ranking ys \<and>
      (set xs \<inter> set ys = {} \<and> \<Union>(set xs) \<inter> \<Union>(set ys) = {})"
  by (simp only: is_weak_ranking_iff)
     (auto dest: disjointD disjoint_unionD1 disjoint_unionD2 intro: disjoint_union)

lemma is_weak_ranking_Cons [code]:
  "is_weak_ranking (x # xs) \<longleftrightarrow> 
      x \<noteq> {} \<and> is_weak_ranking xs \<and> x \<inter> \<Union>(set xs) = {}"
  using is_weak_ranking_append[of "[x]" xs] by auto

lemma is_finite_weak_ranking_Cons [code]:
  "is_finite_weak_ranking (x # xs) \<longleftrightarrow> 
      x \<noteq> {} \<and> finite x \<and> is_finite_weak_ranking xs \<and> x \<inter> \<Union>(set xs) = {}"
  by (auto simp add: is_finite_weak_ranking_def is_weak_ranking_Cons)

primrec is_weak_ranking_aux where
  "is_weak_ranking_aux A [] \<longleftrightarrow> True"
| "is_weak_ranking_aux A (x#xs) \<longleftrightarrow> x \<noteq> {} \<and>
       A \<inter> x = {} \<and> is_weak_ranking_aux (A \<union> x) xs"


lemma is_weak_ranking_aux:
  "is_weak_ranking_aux A xs \<longleftrightarrow> A \<inter> \<Union>(set xs) = {} \<and> is_weak_ranking xs"
  by (induction xs arbitrary: A) (auto simp: is_weak_ranking_Cons)

lemma is_weak_ranking_code [code]:
  "is_weak_ranking xs \<longleftrightarrow> is_weak_ranking_aux {} xs"
  by (subst is_weak_ranking_aux) auto

lemma of_weak_ranking_altdef:
  assumes "is_weak_ranking xs" "x \<in> \<Union>(set xs)" "y \<in> \<Union>(set xs)"
  shows   "of_weak_ranking xs x y \<longleftrightarrow> 
             find_index ((\<in>) x) xs \<ge> find_index ((\<in>) y) xs"
proof -
 from assms 
    have A: "find_index ((\<in>) x) xs < length xs" "find_index ((\<in>) y) xs < length xs"
    by (simp_all add: find_index_less_size_conv)
 from this[THEN nth_find_index] 
    have B: "x \<in> xs ! find_index ((\<in>) x) xs" "y \<in> xs ! find_index ((\<in>) y) xs" .
  show ?thesis
  proof
    assume "of_weak_ranking xs x y"
    then obtain i j where ij: "j \<le> i" "i < length xs" "j < length xs" "x \<in> xs ! i" "y \<in> xs !j"
      by (cases rule: of_weak_ranking.cases) simp_all
    with A B have "i = find_index ((\<in>) x) xs" "j = find_index ((\<in>) y) xs"
      using assms(1) unfolding is_weak_ranking_def by blast+
    with ij show "find_index ((\<in>) x) xs \<ge> find_index ((\<in>) y) xs" by simp
  next
    assume "find_index ((\<in>) x) xs \<ge> find_index ((\<in>) y) xs"
    from this A(2,1) B(2,1) show "of_weak_ranking xs x y"
      by (rule of_weak_ranking.intros)
  qed
qed

  
lemma total_preorder_of_weak_ranking:
  assumes "\<Union>(set xs) = A"
  assumes "is_weak_ranking xs"
  shows   "total_preorder_on A (of_weak_ranking xs)"
proof
  fix x y assume "x \<preceq>[of_weak_ranking xs] y"
  with assms show "x \<in> A" "y \<in> A"
    by (auto elim!: of_weak_ranking.cases)
next
  fix x assume "x \<in> A"
  with assms(1) obtain i where "i < length xs" "x \<in> xs ! i"
    by (auto simp: set_conv_nth)
  thus "x \<preceq>[of_weak_ranking xs] x" by (auto intro: of_weak_ranking.intros)
next
  fix x y assume "x \<in> A" "y \<in> A"
  with assms(1) obtain i j where ij: "i < length xs" "j < length xs" "x \<in> xs ! i" "y \<in> xs ! j"
    by (auto simp: set_conv_nth)
  consider "i \<le> j" | "j \<le> i" by force
  thus "x \<preceq>[of_weak_ranking xs] y \<or> y \<preceq>[of_weak_ranking xs] x"
    by cases (insert ij, (blast intro: of_weak_ranking.intros)+)
next
  fix x y z
  assume A: "x \<preceq>[of_weak_ranking xs] y" and B: "y \<preceq>[of_weak_ranking xs] z"
  from A obtain i j 
    where ij: "i \<ge> j" "i < length xs" "j < length xs" "x \<in> xs ! i" "y \<in> xs ! j"
    by (auto elim!: of_weak_ranking.cases)
  moreover from B obtain j' k 
    where j'k: "j' \<ge> k" "j' < length xs" "k < length xs" "y \<in> xs ! j'" "z \<in> xs ! k"
    by (auto elim!: of_weak_ranking.cases)
  moreover from ij j'k is_weak_rankingD[OF assms(2), of j j'] 
    have "j = j'" by blast
  ultimately show "x \<preceq>[of_weak_ranking xs] z" by (auto intro: of_weak_ranking.intros[of k i])
qed

lemma restrict_relation_of_weak_ranking_Cons:
  assumes "is_weak_ranking (A # As)"
  shows   "restrict_relation (\<Union>(set As)) (of_weak_ranking (A # As)) = of_weak_ranking As"
proof -
  from assms interpret R: total_preorder_on "\<Union>(set As)" "of_weak_ranking As"
    by (intro total_preorder_of_weak_ranking)
       (simp_all add: is_weak_ranking_Cons)
  from assms show ?thesis using R.not_outside
    by (intro ext) (auto simp: restrict_relation_def of_weak_ranking_Cons
                     is_weak_ranking_Cons)
qed




lemmas of_weak_ranking_wf = 
  total_preorder_of_weak_ranking is_weak_ranking_code insert_commute


(* Test *)
lemma "total_preorder_on {1,2,3,4::nat} (of_weak_ranking [{1,3},{2},{4}])"
  by (simp add: of_weak_ranking_wf)


context
  fixes x :: "'alt set" and xs :: "'alt set list"
  assumes wf: "is_weak_ranking (x#xs)"
begin

interpretation R: total_preorder_on "\<Union>(set (x#xs))" "of_weak_ranking (x#xs)"
  by (intro total_preorder_of_weak_ranking) (simp_all add: wf)

lemma of_weak_ranking_imp_in_set:
  assumes "of_weak_ranking xs a b"
  shows   "a \<in> \<Union>(set xs)" "b \<in> \<Union>(set xs)"
  using assms by (fastforce elim!: of_weak_ranking.cases)+

lemma of_weak_ranking_Cons':
  assumes "a \<in> \<Union>(set (x#xs))" "b \<in> \<Union>(set (x#xs))"
  shows   "of_weak_ranking (x#xs) a b \<longleftrightarrow> b \<in> x \<or> (a \<notin> x \<and> of_weak_ranking xs a b)"
proof
  assume "of_weak_ranking (x # xs) a b"
  with wf of_weak_ranking_imp_in_set[of a b] 
    show "(b \<in> x \<or>  a \<notin> x \<and> of_weak_ranking xs a b)"
    by (auto simp: is_weak_ranking_Cons of_weak_ranking_Cons)
next
  assume "b \<in> x \<or> a \<notin> x \<and> of_weak_ranking xs a b"
  with assms show "of_weak_ranking (x#xs) a b"
    by (fastforce simp: of_weak_ranking_Cons)
qed

lemma Max_wrt_among_of_weak_ranking_Cons1:
  assumes "x \<inter> A = {}"
  shows   "Max_wrt_among (of_weak_ranking (x#xs)) A = Max_wrt_among (of_weak_ranking xs) A"
proof -
  from wf interpret R': total_preorder_on "\<Union>(set xs)" "of_weak_ranking xs"
    by (intro total_preorder_of_weak_ranking) (simp_all add: is_weak_ranking_Cons)
  from assms show ?thesis
    by (auto simp: R.Max_wrt_among_total_preorder
          R'.Max_wrt_among_total_preorder of_weak_ranking_Cons)
qed

lemma Max_wrt_among_of_weak_ranking_Cons2:
  assumes "x \<inter> A \<noteq> {}"
  shows   "Max_wrt_among (of_weak_ranking (x#xs)) A = x \<inter> A"
proof -
  from wf interpret R': total_preorder_on "\<Union>(set xs)" "of_weak_ranking xs"
    by (intro total_preorder_of_weak_ranking) (simp_all add: is_weak_ranking_Cons)
  from assms obtain a where "a \<in> x \<inter> A" by blast
  with wf R'.not_outside(1)[of a] show ?thesis
    by (auto simp: R.Max_wrt_among_total_preorder is_weak_ranking_Cons
          R'.Max_wrt_among_total_preorder of_weak_ranking_Cons)
qed

lemma Max_wrt_among_of_weak_ranking_Cons:
  "Max_wrt_among (of_weak_ranking (x#xs)) A =
     (if x \<inter> A = {} then Max_wrt_among (of_weak_ranking xs) A else x \<inter> A)"
  using Max_wrt_among_of_weak_ranking_Cons1 Max_wrt_among_of_weak_ranking_Cons2 by simp

lemma Max_wrt_of_weak_ranking_Cons:
  "Max_wrt (of_weak_ranking (x#xs)) = x"
  using wf by (simp add: is_weak_ranking_Cons Max_wrt_def Max_wrt_among_of_weak_ranking_Cons)

end

lemma Max_wrt_of_weak_ranking:
  assumes "is_weak_ranking xs"
  shows   "Max_wrt (of_weak_ranking xs) = (if xs = [] then {} else hd xs)"
proof (cases xs)
  case Nil
  hence "of_weak_ranking xs = (\<lambda>_ _. False)" by (intro ext) simp_all
  with Nil show ?thesis by (simp add: Max_wrt_def Max_wrt_among_def)
next
  case (Cons x xs')
  with assms show ?thesis by (simp add: Max_wrt_of_weak_ranking_Cons)
qed


locale finite_total_preorder_on = total_preorder_on +
  assumes finite_carrier [intro]: "finite carrier"
begin

lemma finite_total_preorder_on_map:
  assumes "finite (f -` carrier)"
  shows   "finite_total_preorder_on (f -` carrier) (map_relation f le)"
proof -
  interpret R': total_preorder_on "f -` carrier" "map_relation f le"
    using total_preorder_on_map[of f] .
  from assms show ?thesis by unfold_locales simp
qed

function weak_ranking_aux :: "'a set \<Rightarrow> 'a set list" where
  "weak_ranking_aux {} = []"
| "A \<noteq> {} \<Longrightarrow> A \<subseteq> carrier \<Longrightarrow> weak_ranking_aux A =
     Max_wrt_among le A # weak_ranking_aux (A - Max_wrt_among le A)"
| "\<not>(A \<subseteq> carrier) \<Longrightarrow> weak_ranking_aux A = undefined"
by blast simp_all
termination proof (relation "Wellfounded.measure card")
  fix A
  let ?B = "Max_wrt_among le A"
  assume A: "A \<noteq> {}" "A \<subseteq> carrier"
  moreover from A(2) have "finite A" by (rule finite_subset) blast
  moreover from A have "?B \<noteq> {}" "?B \<subseteq> A"
    by (intro Max_wrt_among_nonempty Max_wrt_among_subset; force)+
  ultimately have "card (A - ?B) < card A"
    by (intro psubset_card_mono) auto
  thus "(A - ?B, A) \<in> measure card" by simp
qed simp_all

lemma weak_ranking_aux_Union:
  "A \<subseteq> carrier \<Longrightarrow> \<Union>(set (weak_ranking_aux A)) = A"
proof (induction A rule: weak_ranking_aux.induct [case_names empty nonempty])
  case (nonempty A)
  with Max_wrt_among_subset[of A] show ?case by auto
qed simp_all

lemma weak_ranking_aux_wf:
  "A \<subseteq> carrier \<Longrightarrow> is_weak_ranking (weak_ranking_aux A)"
proof (induction A rule: weak_ranking_aux.induct [case_names empty nonempty])
  case (nonempty A)
  have "is_weak_ranking (Max_wrt_among le A # weak_ranking_aux (A - Max_wrt_among le A))"
    unfolding is_weak_ranking_Cons
  proof (intro conjI)
    from nonempty.prems nonempty.hyps show "Max_wrt_among le A \<noteq> {}"
      by (intro Max_wrt_among_nonempty) auto
  next
    from nonempty.prems show "is_weak_ranking (weak_ranking_aux (A - Max_wrt_among le A))"
      by (intro nonempty.IH) blast
  next
    from nonempty.prems nonempty.hyps have "Max_wrt_among le A \<noteq> {}"
      by (intro Max_wrt_among_nonempty) auto
    moreover from nonempty.prems 
      have "\<Union>(set (weak_ranking_aux (A - Max_wrt_among le A))) = A - Max_wrt_among le A"
      by (intro weak_ranking_aux_Union) auto
    ultimately show "Max_wrt_among le A \<inter> \<Union>(set (weak_ranking_aux (A - Max_wrt_among le A))) = {}"
      by blast+
  qed
  with nonempty.prems nonempty.hyps show ?case by simp
qed simp_all    

lemma of_weak_ranking_weak_ranking_aux':
  assumes "A \<subseteq> carrier" "x \<in> A" "y \<in> A"
  shows   "of_weak_ranking (weak_ranking_aux A) x y \<longleftrightarrow> restrict_relation A le x y"
using assms
proof (induction A rule: weak_ranking_aux.induct [case_names empty nonempty])
  case (nonempty A)
  define M where "M = Max_wrt_among le A"
  from nonempty.prems nonempty.hyps have M: "M \<subseteq> A" unfolding M_def
    by (intro Max_wrt_among_subset)
  from nonempty.prems have in_MD: "le x y" if "x \<in> A" "y \<in> M" for x y
    using that unfolding M_def Max_wrt_among_total_preorder
    by (auto simp: Int_absorb1)
  from nonempty.prems have in_MI: "x \<in> M" if "y \<in> M" "x \<in> A"  "le y x" for x y
    using that unfolding M_def Max_wrt_among_total_preorder
    by (auto simp: Int_absorb1 intro: trans)

  from nonempty.prems nonempty.hyps
    have IH: "of_weak_ranking (weak_ranking_aux (A - M)) x y = 
                restrict_relation (A - M) le x y" if "x \<notin> M" "y \<notin> M"
       using that unfolding M_def by (intro nonempty.IH) auto
  from nonempty.prems 
    interpret R': total_preorder_on "A - M" "of_weak_ranking (weak_ranking_aux (A - M))"
    by (intro total_preorder_of_weak_ranking weak_ranking_aux_wf weak_ranking_aux_Union) auto
  
  from nonempty.prems nonempty.hyps M weak_ranking_aux_Union[of A] R'.not_outside[of x y] 
    show ?case
    by (cases "x \<in> M"; cases "y \<in> M")
       (auto simp: restrict_relation_def of_weak_ranking_Cons IH M_def [symmetric]
             intro: in_MD dest: in_MI)
qed simp_all

lemma of_weak_ranking_weak_ranking_aux:
  "of_weak_ranking (weak_ranking_aux carrier) = le"
proof (intro ext)
  fix x y
  have "is_weak_ranking (weak_ranking_aux carrier)" by (rule weak_ranking_aux_wf) simp
  then interpret R: total_preorder_on carrier "of_weak_ranking (weak_ranking_aux carrier)"
    by (intro total_preorder_of_weak_ranking weak_ranking_aux_wf weak_ranking_aux_Union)
       (simp_all add: weak_ranking_aux_Union)

  show "of_weak_ranking (weak_ranking_aux carrier) x y = le x y"
  proof (cases "x \<in> carrier \<and> y \<in> carrier")
    case True
    thus ?thesis
      using of_weak_ranking_weak_ranking_aux'[of carrier x y]  by simp
  next
    case False
    with R.not_outside have "of_weak_ranking (weak_ranking_aux carrier) x y = False"
      by auto
    also from not_outside False have "\<dots> = le x y" by auto
    finally show ?thesis .
  qed
qed

lemma weak_ranking_aux_unique':
  assumes "\<Union>(set As) \<subseteq> carrier" "is_weak_ranking As"
          "of_weak_ranking As = restrict_relation (\<Union>(set As)) le"
  shows   "As = weak_ranking_aux (\<Union>(set As))"
using assms
proof (induction As)
  case (Cons A As)
  have "restrict_relation (\<Union>(set As)) (of_weak_ranking (A # As)) = of_weak_ranking As"
    by (intro restrict_relation_of_weak_ranking_Cons Cons.prems)
  also have eq1: "of_weak_ranking (A # As) = restrict_relation (\<Union>(set (A # As))) le" by fact
  finally have eq: "of_weak_ranking As = restrict_relation (\<Union>(set As)) le"
    by (simp add: Int_absorb2)
  with Cons.prems have eq2: "weak_ranking_aux (\<Union>(set As)) = As"
    by (intro sym [OF Cons.IH]) (auto simp: is_weak_ranking_Cons)

  from eq1 have 
    "Max_wrt_among le (\<Union>(set (A # As))) = 
       Max_wrt_among (of_weak_ranking (A#As)) (\<Union>(set (A#As)))"
    by (intro Max_wrt_among_cong) simp_all
  also from Cons.prems have "\<dots> = A"
    by (subst Max_wrt_among_of_weak_ranking_Cons2)
       (simp_all add: is_weak_ranking_Cons)
  finally have Max: "Max_wrt_among le (\<Union>(set (A # As))) = A" .

  moreover from Cons.prems have "A \<noteq> {}" by (simp add: is_weak_ranking_Cons)
  ultimately have "weak_ranking_aux (\<Union>(set (A # As))) = A # weak_ranking_aux (A \<union> \<Union>(set As) - A)" 
    using Cons.prems by simp
  also from Cons.prems have "A \<union> \<Union>(set As) - A = \<Union>(set As)"
    by (auto simp: is_weak_ranking_Cons)
  also from eq2 have "weak_ranking_aux \<dots> = As" .
  finally show ?case ..
qed simp_all

lemma weak_ranking_aux_unique:
  assumes "is_weak_ranking As" "of_weak_ranking As = le"
  shows   "As = weak_ranking_aux carrier"
proof -
  interpret R: total_preorder_on "\<Union>(set As)" "of_weak_ranking As"
    by (intro total_preorder_of_weak_ranking assms) simp_all
  from assms have "x \<in> \<Union>(set As) \<longleftrightarrow> x \<in> carrier" for x
    using R.not_outside not_outside R.refl[of x] refl[of x]
    by blast
  hence eq: "\<Union>(set As) = carrier" by blast
  from assms eq have "As = weak_ranking_aux (\<Union>(set As))"
    by (intro weak_ranking_aux_unique') simp_all
  with eq show ?thesis by simp
qed

lemma weak_ranking_total_preorder:
  "is_weak_ranking (weak_ranking le)" "of_weak_ranking (weak_ranking le) = le"
proof -
  from weak_ranking_aux_wf[of carrier] of_weak_ranking_weak_ranking_aux
    have "\<exists>x. is_weak_ranking x \<and> le = of_weak_ranking x" by auto
  hence "is_weak_ranking (weak_ranking le) \<and> le = of_weak_ranking (weak_ranking le)"
    unfolding weak_ranking_def by (rule someI_ex)
  thus "is_weak_ranking (weak_ranking le)" "of_weak_ranking (weak_ranking le) = le"
    by simp_all
qed

lemma weak_ranking_altdef:
  "weak_ranking le = weak_ranking_aux carrier"
  by (intro weak_ranking_aux_unique weak_ranking_total_preorder)

lemma weak_ranking_Union: "\<Union>(set (weak_ranking le)) = carrier"
  by (simp add: weak_ranking_altdef weak_ranking_aux_Union)

lemma weak_ranking_unique:
  assumes "is_weak_ranking As" "of_weak_ranking As = le"
  shows   "As = weak_ranking le"
  using assms unfolding weak_ranking_altdef by (rule weak_ranking_aux_unique)

lemma weak_ranking_permute:
  assumes "f permutes carrier"
  shows   "weak_ranking (map_relation (inv f) le) = map ((`) f) (weak_ranking le)"
proof -
  from assms have "inv f -` carrier = carrier"
    by (simp add: permutes_vimage permutes_inv)
  then interpret R: finite_total_preorder_on "inv f -` carrier" "map_relation (inv f) le"
    by (intro finite_total_preorder_on_map) (simp_all add: finite_carrier)
  from assms have "is_weak_ranking (map ((`) f) (weak_ranking le))"
    by (intro is_weak_ranking_map_inj) 
       (simp_all add: weak_ranking_total_preorder permutes_inj_on)
  with assms show ?thesis
    by (intro sym[OF R.weak_ranking_unique])
       (simp_all add: of_weak_ranking_permute weak_ranking_Union weak_ranking_total_preorder)
qed

lemma weak_ranking_index_unique:
  assumes "is_weak_ranking xs" "i < length xs" "j < length xs" "x \<in> xs ! i" "x \<in> xs ! j"
  shows   "i = j"
  using assms unfolding is_weak_ranking_def by auto

lemma weak_ranking_index_unique':
  assumes "is_weak_ranking xs" "i < length xs" "x \<in> xs ! i"
  shows   "i = find_index ((\<in>) x) xs"
  using assms find_index_less_size_conv nth_mem
  by (intro weak_ranking_index_unique[OF assms(1,2) _ assms(3)]
        nth_find_index[of "(\<in>) x"]) blast+

lemma weak_ranking_eqclass1:
  assumes "A \<in> set (weak_ranking le)" "x \<in> A" "y \<in> A"
  shows   "le x y"
proof -
  from assms obtain i where "weak_ranking le ! i = A" "i < length (weak_ranking le)" 
    by (auto simp: set_conv_nth)
  with assms have "of_weak_ranking (weak_ranking le) x y"
    by (intro of_weak_ranking.intros[of i i]) auto
  thus ?thesis by (simp add: weak_ranking_total_preorder)
qed

lemma weak_ranking_eqclass2:
  assumes A: "A \<in> set (weak_ranking le)" "x \<in> A" and le: "le x y" "le y x"
  shows   "y \<in> A"
proof -
  define xs where "xs = weak_ranking le"
  have wf: "is_weak_ranking xs" by (simp add: xs_def weak_ranking_total_preorder)
  let ?le' = "of_weak_ranking xs"
  from le have le': "?le' x y" "?le' y x" by (simp_all add: weak_ranking_total_preorder xs_def)
  from le'(1) obtain i j
    where ij: "j \<le> i" "i < length xs" "j < length xs" "x \<in> xs ! i" "y \<in> xs ! j"
    by (cases rule: of_weak_ranking.cases)
  from le'(2) obtain i' j'
    where i'j': "j' \<le> i'" "i' < length xs" "j' < length xs" "x \<in> xs ! j'" "y \<in> xs ! i'"
    by (cases rule: of_weak_ranking.cases)
  from ij i'j' have eq: "i = j'" "j = i'"
    by (intro weak_ranking_index_unique[OF wf]; simp)+
  moreover from A obtain k where k: "k < length xs" "A = xs ! k" 
    by (auto simp: xs_def set_conv_nth)
  ultimately have "k = i" using ij i'j' A
    by (intro weak_ranking_index_unique[OF wf, of _ _ x]) auto
  with ij i'j' k eq show ?thesis by (auto simp: xs_def)
qed

lemma hd_weak_ranking:
  assumes "x \<in> hd (weak_ranking le)" "y \<in> carrier"
  shows   "le y x"
proof -
  from weak_ranking_Union assms obtain i
    where "i < length (weak_ranking le)" "y \<in> weak_ranking le ! i"
    by (auto simp: set_conv_nth)
  moreover from assms(2) weak_ranking_Union have "weak_ranking le \<noteq> []" by auto
  ultimately have "of_weak_ranking (weak_ranking le) y x" using assms(1)
    by (intro of_weak_ranking.intros[of 0 i]) (auto simp: hd_conv_nth)
  thus ?thesis by (simp add: weak_ranking_total_preorder)
qed

lemma last_weak_ranking:
  assumes "x \<in> last (weak_ranking le)" "y \<in> carrier"
  shows   "le x y"
proof -
  from weak_ranking_Union assms obtain i
    where "i < length (weak_ranking le)" "y \<in> weak_ranking le ! i"
    by (auto simp: set_conv_nth)
  moreover from assms(2) weak_ranking_Union have "weak_ranking le \<noteq> []" by auto
  ultimately have "of_weak_ranking (weak_ranking le) x y" using assms(1)
    by (intro of_weak_ranking.intros[of i "length (weak_ranking le) - 1"])
       (auto simp: last_conv_nth)
  thus ?thesis by (simp add: weak_ranking_total_preorder)
qed

text \<open>
  The index in weak ranking of a given alternative. An element with index 0 is 
  first-ranked; larger indices correspond to less-preferred alternatives.
\<close>
definition weak_ranking_index :: "'a \<Rightarrow> nat" where
  "weak_ranking_index x = find_index (\<lambda>A. x \<in> A) (weak_ranking le)"

lemma nth_weak_ranking_index:
  assumes "x \<in> carrier"
  shows   "weak_ranking_index x < length (weak_ranking le)" 
          "x \<in> weak_ranking le ! weak_ranking_index x"
proof -
  from assms weak_ranking_Union show "weak_ranking_index x < length (weak_ranking le)"
     unfolding weak_ranking_index_def by (auto simp add: find_index_less_size_conv)
  thus "x \<in> weak_ranking le ! weak_ranking_index x" unfolding weak_ranking_index_def
    by (rule nth_find_index)
qed

lemma ranking_index_eqI:
  "i < length (weak_ranking le) \<Longrightarrow> x \<in> weak_ranking le ! i \<Longrightarrow> weak_ranking_index x = i"
  using weak_ranking_index_unique'[of "weak_ranking le" i x]
  by (simp add: weak_ranking_index_def weak_ranking_total_preorder)

lemma ranking_index_le_iff [simp]:
  assumes "x \<in> carrier" "y \<in> carrier"
  shows   "weak_ranking_index x \<ge> weak_ranking_index y \<longleftrightarrow> le x y"
proof -
  have "le x y \<longleftrightarrow> of_weak_ranking (weak_ranking le) x y"
    by (simp add: weak_ranking_total_preorder)
  also have "\<dots> \<longleftrightarrow> weak_ranking_index x \<ge> weak_ranking_index y"
  proof
    assume "weak_ranking_index x \<ge> weak_ranking_index y"
    thus "of_weak_ranking (weak_ranking le) x y"
      by (rule of_weak_ranking.intros) (simp_all add: nth_weak_ranking_index assms)
  next
    assume "of_weak_ranking (weak_ranking le) x y"
    then obtain i j where 
      "i \<le> j" "i < length (weak_ranking le)" "j < length (weak_ranking le)"
      "x \<in> weak_ranking le ! j" "y \<in> weak_ranking le ! i"
      by (elim of_weak_ranking.cases) blast
    with ranking_index_eqI[of i] ranking_index_eqI[of j]
      show "weak_ranking_index x \<ge> weak_ranking_index y" by simp
  qed
  finally show ?thesis ..
qed

end

lemma weak_ranking_False [simp]: "weak_ranking (\<lambda>_ _. False) = []"
proof -
  interpret finite_total_preorder_on "{}" "\<lambda>_ _. False"
    by unfold_locales simp_all
  have "[] = weak_ranking (\<lambda>_ _. False)" by (rule weak_ranking_unique) simp_all
  thus ?thesis ..
qed

lemmas of_weak_ranking_weak_ranking = 
  finite_total_preorder_on.weak_ranking_total_preorder(2)

lemma finite_total_preorder_on_iff:
  "finite_total_preorder_on A R \<longleftrightarrow> total_preorder_on A R \<and> finite A"
  by (simp add: finite_total_preorder_on_def finite_total_preorder_on_axioms_def)

lemma finite_total_preorder_of_weak_ranking:
  assumes "\<Union>(set xs) = A" "is_finite_weak_ranking xs"
  shows   "finite_total_preorder_on A (of_weak_ranking xs)"
proof -
  from assms(2) have "is_weak_ranking xs" by (simp add: is_finite_weak_ranking_def)
  from assms(1) and this interpret total_preorder_on A "of_weak_ranking xs"
    by (rule total_preorder_of_weak_ranking)
  from assms(2) show ?thesis
    by unfold_locales (simp add: assms(1)[symmetric] is_finite_weak_ranking_def)
qed  

lemma weak_ranking_of_weak_ranking:
  assumes "is_finite_weak_ranking xs"
  shows   "weak_ranking (of_weak_ranking xs) = xs"
proof -
  from assms interpret finite_total_preorder_on "\<Union>(set xs)" "of_weak_ranking xs"
    by (intro finite_total_preorder_of_weak_ranking) simp_all
  from assms show ?thesis
    by (intro sym[OF weak_ranking_unique]) (simp_all add: is_finite_weak_ranking_def)
qed


lemma weak_ranking_eqD:
  assumes "finite_total_preorder_on alts R1"
  assumes "finite_total_preorder_on alts R2"
  assumes "weak_ranking R1 = weak_ranking R2"
  shows   "R1 = R2"
proof -
  from assms have "of_weak_ranking (weak_ranking R1) = of_weak_ranking (weak_ranking R2)" by simp
  with assms(1,2) show ?thesis by (simp add: of_weak_ranking_weak_ranking)
qed

lemma weak_ranking_eq_iff:
  assumes "finite_total_preorder_on alts R1"
  assumes "finite_total_preorder_on alts R2"
  shows   "weak_ranking R1 = weak_ranking R2 \<longleftrightarrow> R1 = R2"
  using assms weak_ranking_eqD by auto


definition preferred_alts :: "'alt relation \<Rightarrow> 'alt \<Rightarrow> 'alt set" where
  "preferred_alts R x = {y. y \<succeq>[R] x}"

lemma (in preorder_on) preferred_alts_refl [simp]: "x \<in> carrier \<Longrightarrow> x \<in> preferred_alts le x"
  by (simp add: preferred_alts_def refl)  

lemma (in preorder_on) preferred_alts_altdef:
  "preferred_alts le x = {y\<in>carrier. y \<succeq>[le] x}"
  by (auto simp: preferred_alts_def intro: not_outside)
  
lemma (in preorder_on) preferred_alts_subset: "preferred_alts le x \<subseteq> carrier"
  unfolding preferred_alts_def using not_outside by blast


subsection \<open>Rankings\<close>

(* TODO: Extend theory on rankings. Can probably mostly be based on
   existing theory on weak rankings. *)

definition ranking :: "'a relation \<Rightarrow> 'a list" where
  "ranking R = map the_elem (weak_ranking R)"

locale finite_linorder_on = linorder_on +
  assumes finite_carrier [intro]: "finite carrier"
begin

sublocale finite_total_preorder_on carrier le
  by unfold_locales (fact finite_carrier)

lemma singleton_weak_ranking:
  assumes "A \<in> set (weak_ranking le)"
  shows   "is_singleton A"
proof (rule is_singletonI')
  from assms show "A \<noteq> {}"
    using weak_ranking_total_preorder(1) is_weak_ranking_iff by auto
next
  fix x y assume "x \<in> A" "y \<in> A"
  with assms 
    have "x \<preceq>[of_weak_ranking (weak_ranking le)] y" "y \<preceq>[of_weak_ranking (weak_ranking le)] x"
    by (auto intro!: of_weak_ranking_indifference)
  with weak_ranking_total_preorder(2) 
    show "x = y" by (intro antisymmetric) simp_all
qed

lemma weak_ranking_ranking: "weak_ranking le = map (\<lambda>x. {x}) (ranking le)"
  unfolding ranking_def map_map o_def
proof (rule sym, rule map_idI)
  fix A assume "A \<in> set (weak_ranking le)"
  hence "is_singleton A" by (rule singleton_weak_ranking)
  thus "{the_elem A} = A" by (auto elim: is_singletonE)
qed

end

end
