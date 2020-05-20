theory MissingRelation
imports Main
begin

lemma range_dom[simp]:
  "f `` Domain f = Range f"
  "converse f `` Range f = Domain f" by auto

lemma Gr_Image_image[simp]:
  shows "BNF_Def.Gr A f `` B = f ` (A \<inter> B)"
  unfolding BNF_Def.Gr_def by auto

definition univalent where "univalent R = (\<forall> x y z. (x,y)\<in> R \<and> (x,z)\<in> R \<longrightarrow> z = y)"

lemma univalent_right_unique[simp]:
  shows "right_unique (\<lambda> x y. (x,y) \<in> R) = univalent R"
        "univalent {(x,y).r x y} = right_unique r"
  unfolding univalent_def right_unique_def by auto

declare univalent_right_unique(1)[pred_set_conv]

lemma univalent_inter[intro]:
  assumes "univalent f_a \<or> univalent f_b"
  shows "univalent (f_a \<inter> f_b)"
  using assms unfolding univalent_def by auto

lemma univalent_union[intro]:
  assumes "univalent f_a" "univalent f_b" "Domain f_a \<inter> Domain f_b = Domain (f_a \<inter> f_b)"
  shows "univalent (f_a \<union> f_b)"
  unfolding univalent_def
proof(clarify,rule ccontr)
  from assms have uni:"univalent (f_a \<inter> f_b)" by auto
  fix x y z
  assume a:"(x, y) \<in> f_a \<union> f_b" "(x, z) \<in> f_a \<union> f_b" "z \<noteq> y"
  show False 
  proof(cases "(x,y) \<in> f_a")
    case True
    hence fb:"(x,z)\<in>f_b" using a assms[unfolded univalent_def] by auto
    hence "x \<in> (Domain f_a \<inter> Domain f_b)" using True by auto
    with assms uni fb True have "z = y" by (metis DomainE IntD1 IntD2 univalent_def)
    with a show False by auto
  next
    case False
    hence fb:"(x,z)\<in>f_a" "(x,y) \<in> f_b" using a assms[unfolded univalent_def] by auto
    hence "x \<in> (Domain f_a \<inter> Domain f_b)" by auto
    with assms uni fb have "z = y" by (metis DomainE IntD1 IntD2 univalent_def)
    with a show False by auto
  qed
qed

lemma Gr_domain[simp]:
  shows "Domain (BNF_Def.Gr A f) = A"
    and "Domain (BNF_Def.Gr A id O R) = A \<inter> Domain R" unfolding BNF_Def.Gr_def by auto

lemma in_Gr[simp]:
  shows "(x,y) \<in> BNF_Def.Gr A f \<longleftrightarrow> x \<in> A \<and> f x = y"
  unfolding BNF_Def.Gr_def by auto

lemma Id_on_domain[simp]:
  "Domain (Id_on A O f) = A \<inter> Domain f" by auto

lemma Domain_id_on:
  shows "Domain (R O S) = Domain R \<inter> R\<inverse> `` Domain S"
  by auto

lemma Id_on_int:
  "Id_on A O f = (A \<times> UNIV) \<inter> f" by auto

lemma Domain_int_univ:
  "Domain (A \<times> UNIV \<inter> f) = A \<inter> Domain f" by auto

lemma Domain_O:
  assumes "a \<subseteq> Domain x" "x `` a \<subseteq> Domain y"
  shows "a \<subseteq> Domain (x O y)"
  proof fix xa assume xa:"xa \<in> a" hence "xa \<in> Domain x" using assms by auto
    then obtain w where xaw:"(xa,w) \<in> x" by auto
    with xa have "w \<in> Domain y" using assms by auto
    then obtain v where "(w,v) \<in> y" by auto
    with xaw have "(xa,v) \<in> x O y" by auto
    thus "xa \<in> Domain (x O y)" by auto qed

lemma fst_UNIV[intro]:
  "A \<subseteq> fst ` A \<times> UNIV" by force

lemma Gr_range[simp]:
  shows "Range (BNF_Def.Gr A f) = f ` A" unfolding BNF_Def.Gr_def by auto

lemma tuple_disj[simp]:
  shows "{y. y = x \<or> y = z} = {x,z}" by auto

lemma univalent_empty [intro]: "univalent {}" unfolding univalent_def by auto

lemma univalent_char : "univalent R \<longleftrightarrow> converse R O R \<subseteq> Id"
  unfolding univalent_def by auto

lemma univalentD [dest]: "univalent R \<Longrightarrow> (x,y)\<in> R \<Longrightarrow> (x,z)\<in> R \<Longrightarrow> z = y"
  unfolding univalent_def by auto

lemma univalentI: "converse R O R \<subseteq> Id \<Longrightarrow> univalent R"
  unfolding univalent_def by auto

lemma univalent_composes[intro]:assumes "univalent R" "univalent S"
 shows "univalent (R O S)" using assms unfolding univalent_char by auto

lemma id_univalent[intro]:"univalent (Id_on x)" unfolding univalent_char by auto

lemma univalent_insert:
  assumes "\<And> c. (a,c) \<notin> R"
  shows "univalent (insert (a,b) R) \<longleftrightarrow> univalent R"
  using assms unfolding univalent_def by auto

lemma univalent_set_distinctI[intro]: (* not an iff: duplicates of A and B might align *)
  assumes "distinct A"
  shows "univalent (set (zip A B))"
  using assms proof(induct A arbitrary:B)
  case (Cons a A)
  hence univ:"univalent (set (zip A (tl B)))" by auto
  from Cons(2) have "a \<notin> set (take x A)" for x using in_set_takeD by fastforce
  hence "a \<notin> Domain (set (zip A (tl B)))"
    unfolding Domain_fst set_map[symmetric] map_fst_zip_take by auto
  hence "\<And> c. (a,c) \<notin> set (zip A (tl B))" by auto
  from univ univalent_insert[OF this] show ?case by(cases B,auto)
qed auto

lemma set_zip_conv[simp]:
"(set (zip A B))\<inverse> = set (zip B A)" unfolding set_zip by auto

lemma univalent_O_converse[simp]:
  assumes "univalent (converse R)"
  shows "R O converse R = Id_on (Domain R)"
  using assms[unfolded univalent_char] by auto

lemma Image_outside_Domain[simp]:
  assumes "Domain R \<inter> A = {}"
  shows "R `` A = {}"
  using assms by auto

lemma Image_Domain[simp]:
  assumes "Domain R = A"
  shows "R `` A = Range R"
  using assms by auto

lemma Domain_set_zip[simp]:
  assumes "length A = length B"
  shows "Domain (set (zip A B)) = set A"
  unfolding Domain_fst set_map[symmetric] map_fst_zip[OF assms]..

lemma Range_set_zip[simp]:
  assumes "length A = length B"
  shows "Range (set (zip A B)) = set B"
  unfolding Range_snd set_map[symmetric] map_snd_zip[OF assms]..

lemma Gr_univalent[intro]:
  shows "univalent (BNF_Def.Gr A f)"
  unfolding BNF_Def.Gr_def univalent_def by auto

lemma univalent_fn[simp]:
  assumes "univalent R"
  shows "BNF_Def.Gr (Domain R) (\<lambda> x. SOME y. (x,y) \<in> R) = R" (is "?lhs = _")
  unfolding set_eq_iff
proof(clarify,standard)
  fix a b assume a:"(a, b) \<in> R"
  hence "(a,SOME y. (a, y) \<in> R) \<in> R" using someI by metis
  with assms a have [simp]:"(SOME y. (a, y) \<in> R) = b" by auto
  show "(a, b) \<in> ?lhs" using a by auto
next
  fix a b assume a:"(a,b) \<in> ?lhs"
  hence "a \<in> Domain R" "(SOME y. (a, y) \<in> R) = b" by auto
  thus "(a,b) \<in> R" using someI by auto
qed

lemma Gr_not_in[intro]:
  shows "x \<notin> F \<or> f x \<noteq> y \<Longrightarrow> (x,y) \<notin> BNF_Def.Gr F f" by auto

lemma Gr_insert[simp]:
  shows "BNF_Def.Gr (insert x F) f = insert (x,f x) (BNF_Def.Gr F f)"
  unfolding BNF_Def.Gr_def by auto

lemma Gr_empty[simp]:
  shows "BNF_Def.Gr {} f = {}" by auto

lemma Gr_card[simp]:
  shows "card (BNF_Def.Gr A f) = card A"
proof(cases "finite A")
  case True
  hence "finite (BNF_Def.Gr A f)" by (induct A,auto)
  with True show ?thesis by (induct A,auto)
next
  have [simp]: "infinite (Domain (A - {x})) = infinite (Domain (A::('a \<times> 'b) set))"
    for A x
    using Diff_infinite_finite Domain_Diff_subset finite.emptyI
              finite.insertI finite_Domain finite_subset Diff_subset Domain_mono
    by metis
  have "infinite (Domain A) \<Longrightarrow> \<exists> a. a \<in> fst ` A" for A::"('a \<times> 'b) set"
    using finite.simps unfolding Domain_fst by fastforce
  hence [intro]:"infinite (Domain A) \<Longrightarrow> \<exists> a b. (a,b) \<in> A" for A::"('a \<times> 'b) set"
    by fast
  let ?Gr = "BNF_Def.Gr A f"
  case False
  hence "infinite ?Gr"
    by(intro infinite_coinduct[of "infinite o Domain"],auto)
  with False show ?thesis by (auto simp:BNF_Def.Gr_def)
qed

lemma univalent_finite[simp]:
  assumes "univalent R"
  shows "card (Domain R) = card R"
        "finite (Domain R) \<longleftrightarrow> finite R"
proof -
  let ?R = "BNF_Def.Gr (Domain R) (\<lambda> x. SOME y. (x,y) \<in> R)"
  have "card (Domain ?R) = card ?R" by auto
  thus "card (Domain  R) = card  R"
    unfolding univalent_fn[OF assms].
  thus "finite (Domain R) \<longleftrightarrow> finite R"
    by (metis Domain_empty_iff card_0_eq card_infinite finite.emptyI)
qed

lemma trancl_power_least:
  "p \<in> R\<^sup>+ \<longleftrightarrow> (\<exists>n. p \<in> R ^^ Suc n \<and> (p \<in> R ^^ n \<longrightarrow> n = 0))"
proof
  assume "p \<in> R\<^sup>+"
  from this[unfolded trancl_power] obtain n where p:"n>0" "p \<in> R ^^ n" by auto
  define n' where "n' = n - 1"
  with p have "Suc n' = n" by auto
  with p have "p \<in> R ^^ Suc n'" by auto
  thus "\<exists>n. p \<in> R ^^ Suc n \<and> (p \<in> R ^^ n \<longrightarrow> n = 0)" proof (induct n')
    case 0 hence "p \<in> R ^^ 0 O R \<and> (p \<in> R ^^ 0 \<longrightarrow> 0 = 0)" by auto
    then show ?case by force
  next
    case (Suc n)
    show ?case proof(cases "p \<in> R ^^ Suc n")
      case False with Suc show ?thesis by blast
    qed (rule Suc)
  qed next
  assume "\<exists>n. p \<in> R ^^ Suc n \<and> (p \<in> R ^^ n \<longrightarrow> n = 0)"
  with zero_less_Suc have "\<exists>n>0. p \<in> R ^^ n" by blast
  thus "p \<in> R\<^sup>+" unfolding trancl_power.
qed

lemma refl_on_tranclI :
  assumes "refl_on A r"
  shows "refl_on A (trancl r)"
  proof
    show "r\<^sup>+ \<subseteq> A \<times> A"
      by( rule trancl_subset_Sigma
        , auto simp: assms[THEN refl_onD1] assms[THEN refl_onD2])
    show "x \<in> A \<Longrightarrow> (x, x) \<in> r\<^sup>+" for x
      using assms[THEN refl_onD] by auto
  qed

definition idempotent where
  "idempotent r \<equiv> r O r = r"

lemma trans_def: "trans r = ((Id \<union> r) O r = r)" "trans r = (r O (Id \<union> r) = r)"
  by(auto simp:trans_def)

lemma idempotent_impl_trans: "idempotent r \<Longrightarrow> trans r"
  by(auto simp:trans_def idempotent_def)

lemma refl_trans_impl_idempotent[intro]: "refl_on A r \<Longrightarrow> trans r \<Longrightarrow> idempotent r"
  by(auto simp:refl_on_def trans_def idempotent_def)

lemma idempotent_subset:
  assumes "idempotent R" "S \<subseteq> R"
  shows "S O R \<subseteq> R" "R O S \<subseteq> R" "S O R O S \<subseteq> R"
  using assms by (auto simp:idempotent_def)

(* not really about relations, but I need it in GraphRewriting.thy.
   Renaming the entire file to 'preliminaries' just because this is here would be too much. *)
lemma list_sorted_max[simp]:
  shows "sorted list \<Longrightarrow> list = (x#xs) \<Longrightarrow> fold max xs x = (last list)"
proof (induct list arbitrary:x xs)
  case (Cons a list)
  hence "xs = y # ys \<Longrightarrow> fold max ys y = last xs" "sorted (x # xs)" "sorted xs" for y ys 
    using Cons.prems(1,2) by auto
  hence "xs \<noteq> [] \<Longrightarrow> fold max xs x = last xs"
    by (metis (full_types) fold_simps(2) max.orderE sorted.elims(2) sorted2)
  thus ?case unfolding Cons by auto
qed auto

end