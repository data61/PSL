section {* Simplicial complexes *}

text {*
  In this section we develop the basic theory of abstract simplicial complexes as a collection of
  finite sets, where the power set of each member set is contained in the collection. Note that in
  this development we allow the empty simplex, since allowing it or not seemed of no logical
  consequence, but of some small practical consequence. 
*}

theory Simplicial
imports Prelim

begin

subsection {* Geometric notions *}

text {*
  The geometric notions attached to a simplicial complex of main interest to us are those of facets
  (subsets of codimension one), adjacency (sharing a facet in common), and chains of adjacent
  simplices.
*}

subsubsection {* Facets *}

definition facetrel :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<lhd>" 60)
  where "y \<lhd> x \<equiv> \<exists>v. v \<notin> y \<and> x = insert v y"

lemma facetrelI: "v \<notin> y \<Longrightarrow> x = insert v y \<Longrightarrow> y \<lhd> x"
  using facetrel_def by fast

lemma facetrelI_card: "y \<subseteq> x \<Longrightarrow> card (x-y) = 1 \<Longrightarrow> y \<lhd> x"
  using card1[of "x-y"] by (blast intro: facetrelI)

lemma facetrel_complement_vertex: "y\<lhd>x \<Longrightarrow> x = insert v y \<Longrightarrow> v\<notin>y"
  using facetrel_def[of y x] by fastforce

lemma facetrel_diff_vertex: "v\<in>x \<Longrightarrow> x-{v} \<lhd> x"
  by (auto intro: facetrelI)

lemma facetrel_conv_insert: "y \<lhd> x \<Longrightarrow> v \<in> x - y \<Longrightarrow> x = insert v y"
  unfolding facetrel_def by fast

lemma facetrel_psubset: "y \<lhd> x \<Longrightarrow> y \<subset> x"
  unfolding facetrel_def by fast

lemma facetrel_subset: "y \<lhd> x \<Longrightarrow> y \<subseteq> x"
  using facetrel_psubset by fast

lemma facetrel_card: "y \<lhd> x \<Longrightarrow> card (x-y) = 1"
  using insert_Diff_if[of _ y y] unfolding facetrel_def by fastforce

lemma finite_facetrel_card: "finite x \<Longrightarrow> y\<lhd>x \<Longrightarrow> card x = Suc (card y)"
  using facetrel_def[of y x] card_insert_disjoint[of x] by auto

lemma facetrelI_cardSuc: "z\<subseteq>x \<Longrightarrow> card x = Suc (card z) \<Longrightarrow> z\<lhd>x"
  using card_ge_0_finite finite_subset[of z] card_Diff_subset[of z x]
  by    (force intro: facetrelI_card)

lemma facet2_subset: "\<lbrakk> z\<lhd>x; z\<lhd>y; x\<inter>y - z \<noteq> {} \<rbrakk> \<Longrightarrow> x \<subseteq> y"
  unfolding facetrel_def by force

lemma inj_on_pullback_facet:
  assumes "inj_on f x" "z \<lhd> f`x"
  obtains y where "y \<lhd> x" "f`y = z"
proof
  from assms(2) obtain v where v: "v\<notin>z" "f`x = insert v z"
    using facetrel_def[of z] by auto
  define u and y where "u \<equiv> the_inv_into x f v" and y: "y \<equiv> {v\<in>x. f v \<in> z}"
  moreover with assms(2) v have "x = insert u y"
    using the_inv_into_f_eq[OF assms(1)] the_inv_into_into[OF assms(1)]
    by    auto
  ultimately show "y \<lhd> x"
    using v f_the_inv_into_f[OF assms(1)] by (force intro: facetrelI)
  from y assms(2) show "f`y = z" using facetrel_subset by fast
qed


subsubsection {* Adjacency *}

definition adjacent :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sim>" 70)
  where "x \<sim> y \<equiv> \<exists>z. z\<lhd>x \<and> z\<lhd>y"

lemma adjacentI: "z\<lhd>x \<Longrightarrow> z\<lhd>y \<Longrightarrow> x \<sim> y"
  using adjacent_def by fast

lemma empty_not_adjacent: "\<not> {} \<sim> x"
  unfolding facetrel_def adjacent_def by fast

lemma adjacent_sym: "x \<sim> y \<Longrightarrow> y \<sim> x"
  unfolding adjacent_def by fast

lemma adjacent_refl:
  assumes "x \<noteq> {}"
  shows   "x \<sim> x"
proof-
  from assms obtain v where v: "v\<in>x" by fast
  thus "x \<sim> x" using facetrelI[of v "x-{v}"] unfolding adjacent_def by fast
qed

lemma common_facet: "\<lbrakk> z\<lhd>x; z\<lhd>y; x \<noteq> y \<rbrakk> \<Longrightarrow> z = x \<inter> y"
  using facetrel_subset facet2_subset by fast

lemma adjacent_int_facet1: "x \<sim> y \<Longrightarrow> x \<noteq> y \<Longrightarrow> (x \<inter> y) \<lhd> x"
  using common_facet unfolding adjacent_def by fast

lemma adjacent_int_facet2: "x \<sim> y \<Longrightarrow> x \<noteq> y \<Longrightarrow> (x \<inter> y) \<lhd> y"
  using adjacent_sym adjacent_int_facet1 by (fastforce simp add: Int_commute)

lemma adjacent_conv_insert: "x \<sim> y \<Longrightarrow> v \<in> x - y \<Longrightarrow> x = insert v (x\<inter>y)"
  using adjacent_int_facet1 facetrel_conv_insert by fast

lemma adjacent_int_decomp:
  "x \<sim> y \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>v. v \<notin> y \<and> x = insert v (x\<inter>y)"
  using adjacent_int_facet1 unfolding facetrel_def by fast

lemma adj_antivertex:
  assumes "x\<sim>y" "x\<noteq>y"
  shows   "\<exists>!v. v\<in>x-y"
proof (rule ex_ex1I)
  from assms obtain w where w: "w\<notin>y" "x = insert w (x\<inter>y)"
    using adjacent_int_decomp by fast
  thus "\<exists>v. v\<in>x-y" by auto
  from w have "\<And>v. v\<in>x-y \<Longrightarrow> v=w" by fast
  thus "\<And>v v'. v\<in>x-y \<Longrightarrow> v'\<in>x-y \<Longrightarrow> v=v'" by auto
qed

lemma adjacent_card: "x \<sim> y \<Longrightarrow> card x = card y"
  unfolding adjacent_def facetrel_def by (cases "finite x" "x=y" rule: two_cases) auto

lemma adjacent_to_adjacent_int_subset:
  assumes "C \<sim> D" "f`C \<sim> f`D" "f`C \<noteq> f`D"
  shows   "f`C \<inter> f`D \<subseteq> f`(C\<inter>D)"
proof
  from assms(1,3) obtain v where v: "v \<notin> D" "C = insert v (C\<inter>D)"
    using adjacent_int_decomp by fast
  from assms(2,3) obtain w where w: "w \<notin> f`D" "f`C = insert w (f`C\<inter>f`D)"
    using adjacent_int_decomp[of "f`C" "f`D"] by fast
  from w have w': "w \<in> f`C - f`D" by fast
  with v assms(1,2) have fv_w: "f v = w" using adjacent_conv_insert by fast
  fix b assume "b \<in> f`C \<inter> f`D"
  from this obtain a1 a2
    where a1: "a1 \<in> C" "b = f a1"
    and   a2: "a2 \<in> D" "b = f a2"
    by    fast
  from v a1 a2(2) have "a1 \<notin> D \<Longrightarrow> f a2 = w" using fv_w by auto
  with a2(1) w' have "a1 \<in> D" by fast
  with a1 show "b \<in> f`(C\<inter>D)" by fast
qed

lemma adjacent_to_adjacent_int:
  "\<lbrakk> C \<sim> D; f`C \<sim> f`D; f`C \<noteq> f`D \<rbrakk> \<Longrightarrow> f`(C\<inter>D) = f`C \<inter> f`D"
  using adjacent_to_adjacent_int_subset by fast

subsubsection {* Chains of adjacent sets *}

abbreviation "adjacentchain  \<equiv> binrelchain adjacent"
abbreviation "padjacentchain \<equiv> proper_binrelchain adjacent"

lemmas adjacentchain_Cons_reduce   = binrelchain_Cons_reduce   [of adjacent]
lemmas adjacentchain_obtain_proper = binrelchain_obtain_proper [of _ _ adjacent]

lemma adjacentchain_card: "adjacentchain (x#xs@[y]) \<Longrightarrow> card x = card y"
  using adjacent_card by (induct xs arbitrary: x) auto


subsection {* Locale and basic facts *}

locale SimplicialComplex =
  fixes   X :: "'a set set"
  assumes finite_simplices: "\<forall>x\<in>X. finite x"
  and     faces           : "x\<in>X \<Longrightarrow> y\<subseteq>x \<Longrightarrow> y\<in>X"

context SimplicialComplex
begin

abbreviation "Subcomplex Y \<equiv> Y \<subseteq> X \<and> SimplicialComplex Y"

definition "maxsimp x \<equiv> x\<in>X \<and> (\<forall>z\<in>X. x\<subseteq>z \<longrightarrow> z=x)"

definition adjacentset :: "'a set \<Rightarrow> 'a set set"
  where "adjacentset x = {y\<in>X. x\<sim>y}"

lemma finite_simplex: "x\<in>X \<Longrightarrow> finite x"
  using finite_simplices by simp

lemma singleton_simplex: "v\<in>\<Union>X \<Longrightarrow> {v} \<in> X"
  using faces by auto

lemma maxsimpI: "x \<in> X \<Longrightarrow> (\<And>z. z\<in>X \<Longrightarrow> x\<subseteq>z \<Longrightarrow> z=x) \<Longrightarrow> maxsimp x"
  using maxsimp_def by auto

lemma maxsimpD_simplex: "maxsimp x \<Longrightarrow> x\<in>X"
  using maxsimp_def by fast

lemma maxsimpD_maximal: "maxsimp x \<Longrightarrow> z\<in>X \<Longrightarrow> x\<subseteq>z \<Longrightarrow> z=x"
  using maxsimp_def by auto

lemmas finite_maxsimp = finite_simplex[OF maxsimpD_simplex]

lemma maxsimp_nempty: "X \<noteq> {{}} \<Longrightarrow> maxsimp x \<Longrightarrow> x \<noteq> {}"
  unfolding maxsimp_def by fast 

lemma maxsimp_vertices: "maxsimp x \<Longrightarrow> x\<subseteq>\<Union>X"
  using maxsimpD_simplex by fast

lemma adjacentsetD_adj: "y \<in> adjacentset x \<Longrightarrow> x\<sim>y"
  using adjacentset_def by fast

lemma max_in_subcomplex:
  "\<lbrakk> Subcomplex Y; y \<in> Y; maxsimp y \<rbrakk> \<Longrightarrow> SimplicialComplex.maxsimp Y y"
  using maxsimpD_maximal by (fast intro: SimplicialComplex.maxsimpI)

lemma face_im:
  assumes "w \<in> X" "y \<subseteq> f`w"
  defines "u \<equiv> {a\<in>w. f a \<in> y}"
  shows "y \<in> f\<turnstile>X"
  using assms faces[of w u] image_eqI[of y "op ` f" u X]
  by    fast

lemma im_faces: "x \<in> f \<turnstile> X \<Longrightarrow> y \<subseteq> x \<Longrightarrow> y \<in> f \<turnstile> X"
  using faces face_im[of _ y] by (cases "y={}") auto

lemma map_is_simplicial_morph: "SimplicialComplex (f\<turnstile>X)"
proof
  show "\<forall>x\<in>f\<turnstile>X. finite x" using finite_simplices by fast
  show "\<And>x y. x \<in>f\<turnstile>X \<Longrightarrow> y\<subseteq>x \<Longrightarrow> y\<in>f\<turnstile>X" using im_faces by fast
qed

lemma vertex_set_int:
  assumes "SimplicialComplex Y"
  shows   "\<Union>(X\<inter>Y) = \<Union>X \<inter> \<Union>Y"
proof
  have "\<And>v. v \<in> \<Union>X \<inter> \<Union>Y \<Longrightarrow> v\<in> \<Union>(X\<inter>Y)"
    using faces SimplicialComplex.faces[OF assms] by auto
  thus "\<Union>(X\<inter>Y) \<supseteq> \<Union>X \<inter> \<Union>Y" by fast
qed auto

end (* context SimplicialComplex *)

subsection {* Chains of maximal simplices *}

text {*
  Chains of maximal simplices (with respect to adjacency) will allow us to walk through chamber
  complexes. But there is much we can say about them in simplicial complexes. We will call a chain
  of maximal simplices proper (using the prefix @{text p} as a naming convention to denote proper)
  if no maximal simplex appears more than once in the chain. (Some sources elect to call improper
  chains prechains, and reserve the name chain to describe a proper chain. And usually a slightly
  weaker notion of proper is used, requiring only that no maximal simplex appear twice in succession. But
  it essentially makes no difference, and we found it easier to use @{const distinct} rather than
  @{term "binrelchain not_equal"}.)
*}

context SimplicialComplex
begin

definition "maxsimpchain xs  \<equiv> (\<forall>x\<in>set xs. maxsimp x) \<and> adjacentchain xs"
definition "pmaxsimpchain xs \<equiv> (\<forall>x\<in>set xs. maxsimp x) \<and> padjacentchain xs"

function min_maxsimpchain :: "'a set list \<Rightarrow> bool"
  where
    "min_maxsimpchain [] = True"
  | "min_maxsimpchain [x] = maxsimp x"
  | "min_maxsimpchain (x#xs@[y]) =
      (x\<noteq>y \<and> is_arg_min length (\<lambda>zs. maxsimpchain (x#zs@[y])) xs)"
  by (auto, rule list_cases_Cons_snoc)
  termination by (relation "measure length") auto

lemma maxsimpchain_snocI:
  "\<lbrakk> maxsimpchain (xs@[x]); maxsimp y; x\<sim>y \<rbrakk> \<Longrightarrow> maxsimpchain (xs@[x,y])"
  using maxsimpchain_def binrelchain_snoc maxsimpchain_def by auto

lemma maxsimpchainD_maxsimp:
  "maxsimpchain xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> maxsimp x"
  using maxsimpchain_def by fast

lemma maxsimpchainD_adj: "maxsimpchain xs \<Longrightarrow> adjacentchain xs"
  using maxsimpchain_def by fast

lemma maxsimpchain_CConsI:
  "\<lbrakk> maxsimp w; maxsimpchain (x#xs); w\<sim>x \<rbrakk> \<Longrightarrow> maxsimpchain (w#x#xs)"
  using maxsimpchain_def by auto

lemma maxsimpchain_Cons_reduce:
  "maxsimpchain (x#xs) \<Longrightarrow> maxsimpchain xs"
  using     adjacentchain_Cons_reduce maxsimpchain_def by fastforce

lemma maxsimpchain_append_reduce1:
  "maxsimpchain (xs@ys) \<Longrightarrow> maxsimpchain xs"
  using binrelchain_append_reduce1 maxsimpchain_def by auto

lemma maxsimpchain_append_reduce2:
  "maxsimpchain (xs@ys) \<Longrightarrow> maxsimpchain ys"
  using binrelchain_append_reduce2 maxsimpchain_def by auto

lemma maxsimpchain_remdup_adj:
  "maxsimpchain (xs@[x,x]@ys) \<Longrightarrow> maxsimpchain (xs@[x]@ys)"
  using maxsimpchain_def binrelchain_remdup_adj by auto

lemma maxsimpchain_rev: "maxsimpchain xs \<Longrightarrow> maxsimpchain (rev xs)"
  using     maxsimpchainD_maxsimp adjacent_sym
            binrelchain_sym_rev[of adjacent]
  unfolding maxsimpchain_def
  by        fastforce

lemma maxsimpchain_overlap_join:
  "maxsimpchain (xs@[w]) \<Longrightarrow> maxsimpchain (w#ys) \<Longrightarrow>
    maxsimpchain (xs@w#ys)"
  using binrelchain_overlap_join maxsimpchain_def by auto

lemma pmaxsimpchain: "pmaxsimpchain xs \<Longrightarrow> maxsimpchain xs"
  using maxsimpchain_def pmaxsimpchain_def by fast

lemma pmaxsimpchainI_maxsimpchain:
  "maxsimpchain xs \<Longrightarrow> distinct xs \<Longrightarrow> pmaxsimpchain xs"
  using maxsimpchain_def pmaxsimpchain_def by fast

lemma pmaxsimpchain_CConsI:
  "\<lbrakk> maxsimp w; pmaxsimpchain (x#xs); w\<sim>x; w \<notin> set (x#xs) \<rbrakk> \<Longrightarrow>
    pmaxsimpchain (w#x#xs)"
  using pmaxsimpchain_def by auto

lemmas pmaxsimpchainD_maxsimp =
  maxsimpchainD_maxsimp[OF pmaxsimpchain]
lemmas pmaxsimpchainD_adj =
  maxsimpchainD_adj [OF pmaxsimpchain]

lemma pmaxsimpchainD_distinct: "pmaxsimpchain xs \<Longrightarrow> distinct xs"
  using pmaxsimpchain_def by fast

lemma pmaxsimpchain_Cons_reduce:
  "pmaxsimpchain (x#xs) \<Longrightarrow> pmaxsimpchain xs"
  using maxsimpchain_Cons_reduce pmaxsimpchain pmaxsimpchainD_distinct
  by    (fastforce intro: pmaxsimpchainI_maxsimpchain)

lemma pmaxsimpchain_append_reduce1:
  "pmaxsimpchain (xs@ys) \<Longrightarrow> pmaxsimpchain xs"
  using maxsimpchain_append_reduce1 pmaxsimpchain pmaxsimpchainD_distinct
  by    (fastforce intro: pmaxsimpchainI_maxsimpchain)

lemma maxsimpchain_obtain_pmaxsimpchain:
  assumes "x\<noteq>y" "maxsimpchain (x#xs@[y])"
  shows   "\<exists>ys. set ys \<subseteq> set xs \<and> length ys \<le> length xs \<and>
            pmaxsimpchain (x#ys@[y])"
proof-
  obtain ys
    where ys: "set ys \<subseteq> set xs" "length ys \<le> length xs" "padjacentchain (x#ys@[y])"
    using maxsimpchainD_adj[OF assms(2)]
          adjacentchain_obtain_proper[OF assms(1)]
    by    auto
  from ys(1) assms(2) have "\<forall>a\<in>set (x#ys@[y]). maxsimp a"
    using maxsimpchainD_maxsimp by auto
  with ys show ?thesis unfolding pmaxsimpchain_def by auto
qed

lemma min_maxsimpchainD_maxsimpchain:
  assumes "min_maxsimpchain xs"
  shows   "maxsimpchain xs"
proof (cases xs rule: list_cases_Cons_snoc)
  case Nil thus ?thesis using maxsimpchain_def by simp
next
  case Single with assms show ?thesis using maxsimpchain_def by simp
next
  case Cons_snoc with assms show ?thesis using is_arg_minD1 by fastforce
qed

lemma min_maxsimpchainD_min_betw:
  "min_maxsimpchain (x#xs@[y]) \<Longrightarrow> maxsimpchain (x#ys@[y]) \<Longrightarrow>
    length ys \<ge> length xs"
  using is_arg_minD2 by fastforce

lemma min_maxsimpchainI_betw:
  assumes "x\<noteq>y" "maxsimpchain (x#xs@[y])"
          "\<And>ys. maxsimpchain (x#ys@[y]) \<Longrightarrow> length xs \<le> length ys"
  shows   "min_maxsimpchain (x#xs@[y])"
  using   assms by (simp add: is_arg_min_linorderI)

lemma min_maxsimpchainI_betw_compare:
  assumes "x\<noteq>y" "maxsimpchain (x#xs@[y])"
          "min_maxsimpchain (x#ys@[y])" "length xs = length ys"
  shows   "min_maxsimpchain (x#xs@[y])"
  using   assms min_maxsimpchainD_min_betw min_maxsimpchainI_betw
  by      auto

lemma min_maxsimpchain_pmaxsimpchain:
  assumes "min_maxsimpchain xs"
  shows   "pmaxsimpchain xs"
proof (
  rule pmaxsimpchainI_maxsimpchain, rule min_maxsimpchainD_maxsimpchain,
  rule assms, cases xs rule: list_cases_Cons_snoc
)
  case (Cons_snoc x ys y)
  have "\<not> distinct (x#ys@[y]) \<Longrightarrow> False"
  proof (cases "x\<in>set ys" "y\<in>set ys" rule: two_cases)
    case both
    from both(1) obtain as bs where "ys = as@x#bs"
      using in_set_conv_decomp[of x ys] by fast
    with assms Cons_snoc show False
      using min_maxsimpchainD_maxsimpchain[OF assms]
            maxsimpchain_append_reduce2[of "x#as"]
            min_maxsimpchainD_min_betw[of x ys y]
      by    fastforce
  next
    case one
    from one(1) obtain as bs where "ys = as@x#bs"
      using in_set_conv_decomp[of x ys] by fast
    with assms Cons_snoc show False
      using min_maxsimpchainD_maxsimpchain[OF assms]
            maxsimpchain_append_reduce2[of "x#as"]
            min_maxsimpchainD_min_betw[of x ys y]
      by    fastforce
  next
    case other
    from other(2) obtain as bs where "ys = as@y#bs"
      using in_set_conv_decomp[of y ys] by fast
    with assms Cons_snoc show False
      using min_maxsimpchainD_maxsimpchain[OF assms]
            maxsimpchain_append_reduce1[of "x#as@[y]"]
            min_maxsimpchainD_min_betw[of x ys y]
      by    fastforce
  next
    case neither
    moreover assume "\<not> distinct (x # ys @ [y])"
    ultimately obtain as a bs cs where "ys = as@[a]@bs@[a]@cs"
      using assms Cons_snoc not_distinct_decomp[of ys] by auto
    with assms Cons_snoc show False
      using min_maxsimpchainD_maxsimpchain[OF assms]
            maxsimpchain_append_reduce1[of "x#as@[a]"]
            maxsimpchain_append_reduce2[of "x#as@[a]@bs" "a#cs@[y]"]
            maxsimpchain_overlap_join[of "x#as" a "cs@[y]"]
            min_maxsimpchainD_min_betw[of x ys y "as@a#cs"]
      by    auto
  qed
  with Cons_snoc show "distinct xs" by fast
qed auto

lemma min_maxsimpchain_rev:
  assumes "min_maxsimpchain xs"
  shows   "min_maxsimpchain (rev xs)"
proof (cases xs rule: list_cases_Cons_snoc)
  case Single with assms show ?thesis
    using min_maxsimpchainD_maxsimpchain maxsimpchainD_maxsimp by simp
next
  case (Cons_snoc x ys y)
  moreover have "min_maxsimpchain (y # rev ys @ [x])"
  proof (rule min_maxsimpchainI_betw)
    from Cons_snoc assms show "y\<noteq>x"
      using min_maxsimpchain_pmaxsimpchain pmaxsimpchainD_distinct by auto
    from Cons_snoc show "maxsimpchain (y # rev ys @ [x])"
      using min_maxsimpchainD_maxsimpchain[OF assms] maxsimpchain_rev
      by    fastforce
    from Cons_snoc assms
      show  "\<And>zs. maxsimpchain (y#zs@[x]) \<Longrightarrow> length (rev ys) \<le> length zs"
      using maxsimpchain_rev min_maxsimpchainD_min_betw[of x ys y]
      by    fastforce
  qed
  ultimately show ?thesis by simp
qed simp

lemma min_maxsimpchain_adj:
  "\<lbrakk> maxsimp x; maxsimp y; x\<sim>y; x\<noteq>y \<rbrakk> \<Longrightarrow> min_maxsimpchain [x,y]"
  using maxsimpchain_def min_maxsimpchainI_betw[of x y "[]"] by simp

lemma min_maxsimpchain_betw_CCons_reduce:
  assumes "min_maxsimpchain (w#x#ys@[z])"
  shows   "min_maxsimpchain (x#ys@[z])"
proof (rule min_maxsimpchainI_betw)
  from assms show "x\<noteq>z"
    using min_maxsimpchain_pmaxsimpchain pmaxsimpchainD_distinct
    by    fastforce
  show "maxsimpchain (x#ys@[z])" 
    using min_maxsimpchainD_maxsimpchain[OF assms]
          maxsimpchain_Cons_reduce
    by    fast
next
 fix zs assume "maxsimpchain (x#zs@[z])"
  hence "maxsimpchain (w#x#zs@[z])"
    using min_maxsimpchainD_maxsimpchain[OF assms] maxsimpchain_def
    by    fastforce
  with assms show "length ys \<le> length zs"
    using min_maxsimpchainD_min_betw[of w "x#ys" z "x#zs"] by simp
qed

lemma min_maxsimpchain_betw_uniform_length:
  assumes "min_maxsimpchain (x#xs@[y])" "min_maxsimpchain (x#ys@[y])"
  shows   "length xs = length ys"
  using   min_maxsimpchainD_min_betw[OF assms(1)]
          min_maxsimpchainD_min_betw[OF assms(2)]
          min_maxsimpchainD_maxsimpchain[OF assms(1)]
          min_maxsimpchainD_maxsimpchain[OF assms(2)]
  by      fastforce

lemma not_min_maxsimpchainI_betw:
  "\<lbrakk> maxsimpchain (x#ys@[y]); length ys < length xs \<rbrakk> \<Longrightarrow>
    \<not> min_maxsimpchain (x#xs@[y])"
  using min_maxsimpchainD_min_betw not_less by blast

lemma maxsimpchain_in_subcomplex:
  "\<lbrakk> Subcomplex Y; set ys \<subseteq> Y; maxsimpchain ys \<rbrakk> \<Longrightarrow>
    SimplicialComplex.maxsimpchain Y ys"
  using maxsimpchain_def max_in_subcomplex
        SimplicialComplex.maxsimpchain_def
  by    force

end (* context SimplicialComplex *)

subsection {* Isomorphisms of simplicial complexes *}

text {*
  Here we develop the concept of isomorphism of simplicial complexes. Note that we have not
  bothered to first develop the concept of morphism of simplicial complexes, since every function
  on the vertex set of a simplicial complex can be considered a morphism of complexes (see lemma
  @{text "map_is_simplicial_morph"} above).
*}

locale SimplicialComplexIsomorphism = SimplicialComplex X
  for X :: "'a set set"
+ fixes f :: "'a \<Rightarrow> 'b"
  assumes inj: "inj_on f (\<Union>X)"
begin

lemmas morph = map_is_simplicial_morph[of f]

lemma iso_codim_map:
  "x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> card (f`x - f`y) = card (x-y)"
  using inj inj_on_image_set_diff[of f _ x y] finite_simplex subset_inj_on[of f _ "x-y"]
        inj_on_iff_eq_card[of "x-y"]
  by    fastforce

lemma maxsimp_im_max: "maxsimp x \<Longrightarrow> w \<in> X \<Longrightarrow> f`x \<subseteq> f`w \<Longrightarrow> f`w = f`x"
  using maxsimpD_simplex inj_onD[OF inj] maxsimpD_maximal[of x w] by blast

lemma maxsimp_map:
  "maxsimp x \<Longrightarrow> SimplicialComplex.maxsimp (f\<turnstile>X) (f`x)"
  using maxsimpD_simplex maxsimp_im_max morph
        SimplicialComplex.maxsimpI[of "f\<turnstile>X" "f`x"]
  by    fastforce

lemma iso_adj_int_im:
  assumes "maxsimp x" "maxsimp y" "x\<sim>y" "x\<noteq>y"
  shows "(f`x \<inter> f`y) \<lhd> f`x"
proof (rule facetrelI_card)
  from assms(1,2) have  1: "f ` x \<subseteq> f ` y \<Longrightarrow> f ` y = f ` x"
    using maxsimp_map SimplicialComplex.maxsimpD_simplex[OF morph]
          SimplicialComplex.maxsimpD_maximal[OF morph]
    by    simp
  thus "f`x \<inter> f`y \<subseteq> f`x" by fast

  from assms(1) have "card (f`x - f`x \<inter> f`y) \<le> card (f`x - f`(x\<inter>y))"
    using finite_maxsimp card_mono[of "f`x - f`(x\<inter>y)" "f`x - f`x \<inter> f`y"] by fast
  moreover from assms(1,3,4) have "card (f`x - f`(x\<inter>y)) = 1"
    using maxsimpD_simplex faces[of x] maxsimpD_simplex
          iso_codim_map adjacent_int_facet1[of x y] facetrel_card
    by    fastforce
  ultimately have "card (f`x - f`x \<inter> f`y) \<le> 1" by simp
  moreover from assms(1,2,4) have "card (f`x - f`x \<inter> f`y) \<noteq> 0"
    using 1 maxsimpD_simplex finite_maxsimp
          inj_onD[OF induced_pow_fun_inj_on, OF inj, of x y]
    by    auto
  ultimately show "card (f`x - f`x \<inter> f`y) = 1" by simp
qed

lemma iso_adj_map:
  assumes "maxsimp x" "maxsimp y" "x\<sim>y" "x\<noteq>y"
  shows   "f`x \<sim> f`y"
  using assms(3,4) iso_adj_int_im[OF assms] adjacent_sym
        iso_adj_int_im[OF assms(2) assms(1)]
  by    (auto simp add: Int_commute intro: adjacentI)

lemma pmaxsimpchain_map:
  "pmaxsimpchain xs \<Longrightarrow> SimplicialComplex.pmaxsimpchain (f\<turnstile>X) (f\<Turnstile>xs)"
proof (induct xs rule: list_induct_CCons)
  case Nil show ?case
    using map_is_simplicial_morph SimplicialComplex.pmaxsimpchain_def
    by    fastforce
next
  case (Single x) thus ?case
    using map_is_simplicial_morph pmaxsimpchainD_maxsimp maxsimp_map
          SimplicialComplex.pmaxsimpchain_def
    by    fastforce
next
  case (CCons x y xs)
  have "SimplicialComplex.pmaxsimpchain (f \<turnstile> X) ( f`x # f`y # f\<Turnstile>xs)"
  proof (
    rule SimplicialComplex.pmaxsimpchain_CConsI,
    rule map_is_simplicial_morph
  )
    from CCons(2) show "SimplicialComplex.maxsimp (f\<turnstile>X) (f`x)"
      using pmaxsimpchainD_maxsimp maxsimp_map by simp
    from CCons show "SimplicialComplex.pmaxsimpchain (f\<turnstile>X) (f`y # f\<Turnstile>xs)"
      using pmaxsimpchain_Cons_reduce by simp
    from CCons(2) show "f`x \<sim> f`y"
      using pmaxsimpchain_def iso_adj_map by simp
    from inj CCons(2) have "distinct (f\<Turnstile>(x#y#xs))"
      using     maxsimpD_simplex inj_on_distinct_setlistmapim
      unfolding pmaxsimpchain_def
      by        blast
    thus "f`x \<notin> set (f`y # f\<Turnstile>xs)" by simp
  qed
  thus ?case by simp
qed

end (* context SimplicialComplexIsomorphism *)

subsection {* The complex associated to a poset *}

text {*
  A simplicial complex is naturally a poset under the subset relation. The following develops the
  reverse direction: constructing a simplicial complex from a suitable poset.
*}

context ordering
begin

definition PosetComplex :: "'a set \<Rightarrow> 'a set set"
  where "PosetComplex P \<equiv> (\<Union>x\<in>P. { {y. pseudominimal_in (P.\<^bold>\<le>x) y} })"

lemma poset_is_SimplicialComplex:
  assumes "\<forall>x\<in>P. simplex_like (P.\<^bold>\<le>x)"
  shows   "SimplicialComplex (PosetComplex P)"
proof (rule SimplicialComplex.intro, rule ballI)
  fix a assume "a \<in> PosetComplex P"
  from this obtain x where "x\<in>P" "a = {y. pseudominimal_in (P.\<^bold>\<le>x) y}"
    unfolding PosetComplex_def by fast
  with assms show "finite a"
    using pseudominimal_inD1 simplex_likeD_finite finite_subset[of a "P.\<^bold>\<le>x"] by fast
next
  fix a b assume ab: "a \<in> PosetComplex P" "b\<subseteq>a"
  from ab(1) obtain x where x: "x\<in>P" "a = {y. pseudominimal_in (P.\<^bold>\<le>x) y}"
    unfolding PosetComplex_def by fast
  from assms x(1) obtain f and A::"nat set"
    where fA: "OrderingSetIso less_eq less (op \<subseteq>) (op \<subset>) (P.\<^bold>\<le>x) f"
              "f`(P.\<^bold>\<le>x) = Pow A"
    using simplex_likeD_iso[of "P.\<^bold>\<le>x"]
    by    auto
  define x' where x': "x' \<equiv> the_inv_into (P.\<^bold>\<le>x) f (\<Union>(f`b))"
  from fA x(2) ab(2) x' have x'_P: "x'\<in>P"
    using collect_pseudominimals_below_in_poset[of P x f] by simp
  moreover from x fA ab(2) x' have "b = {y. pseudominimal_in (P.\<^bold>\<le>x') y}"
    using collect_pseudominimals_below_in_eq[of x P f] by simp
  ultimately show "b \<in> PosetComplex P" unfolding PosetComplex_def by fast
qed

definition poset_simplex_map :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "poset_simplex_map P x = {y. pseudominimal_in (P.\<^bold>\<le>x) y}"

lemma poset_to_PosetComplex_OrderingSetMap:
  assumes "\<And>x. x\<in>P \<Longrightarrow> simplex_like (P.\<^bold>\<le>x)"
  shows   "OrderingSetMap (op \<^bold>\<le>) (op \<^bold><) (op \<subseteq>) (op \<subset>) P (poset_simplex_map P)"
proof
  from assms
    show  "\<And>a b. \<lbrakk> a\<in>P; b\<in>P; a\<^bold>\<le>b \<rbrakk> \<Longrightarrow>
            poset_simplex_map P a \<subseteq> poset_simplex_map P b"
    using     simplex_like_has_bottom pseudominimal_in_below_in
    unfolding poset_simplex_map_def
    by        fast
qed

end (* context ordering *)

text {*
  When a poset affords a simplicial complex, there is a natural morphism of posets from the
  source poset into the poset of sets in the complex, as above. However, some further assumptions
  are necessary to ensure that this morphism is an isomorphism. These conditions are collected in
  the following locale.
*}

locale ComplexLikePoset = ordering less_eq less
  for less_eq  :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infix "\<^bold>\<le>"  50)
  and less     :: "'a\<Rightarrow>'a\<Rightarrow>bool" (infix "\<^bold><"  50)
+ fixes   P :: "'a set"
  assumes below_in_P_simplex_like: "x\<in>P \<Longrightarrow> simplex_like (P.\<^bold>\<le>x)"
  and     P_has_bottom           : "has_bottom P"
  and     P_has_glbs             : "x\<in>P \<Longrightarrow> y\<in>P \<Longrightarrow> \<exists>b. glbound_in_of P x y b"
begin

abbreviation "smap \<equiv> poset_simplex_map P"

lemma smap_onto_PosetComplex: "smap ` P = PosetComplex P"
  using poset_simplex_map_def PosetComplex_def by auto

lemma ordsetmap_smap: "\<lbrakk> a\<in>P; b\<in>P; a\<^bold>\<le>b \<rbrakk> \<Longrightarrow> smap a \<subseteq> smap b"
  using OrderingSetMap.ordsetmap[
          OF poset_to_PosetComplex_OrderingSetMap, OF below_in_P_simplex_like
        ]
        poset_simplex_map_def
  by    simp

lemma inj_on_smap: "inj_on smap P"
proof (rule inj_onI)
  fix x y assume xy: "x\<in>P" "y\<in>P" "smap x = smap y"
  show "x = y"
  proof (cases "smap x = {}")
    case True with xy show ?thesis
      using poset_simplex_map_def below_in_P_simplex_like P_has_bottom
            simplex_like_no_pseudominimal_in_below_in_imp_singleton[of x P]
            simplex_like_no_pseudominimal_in_below_in_imp_singleton[of y P]
            below_in_singleton_is_bottom[of P x] below_in_singleton_is_bottom[of P y]
      by    auto
  next
    case False
    from this obtain z where "z \<in> smap x" by fast
    with xy(3) have z1: "z \<in> P.\<^bold>\<le>x" "z \<in> P.\<^bold>\<le>y"
      using pseudominimal_inD1 poset_simplex_map_def by auto
    hence "lbound_of x y z" by (auto intro: lbound_ofI)
    with z1(1) obtain b where b: "glbound_in_of P x y b"
      using xy(1,2) P_has_glbs by fast
    moreover have "b \<in> P.\<^bold>\<le>x" "b \<in> P.\<^bold>\<le>y"
      using glbound_in_ofD_in[OF b] glbound_in_of_less_eq1[OF b]
            glbound_in_of_less_eq2[OF b]
      by    auto
    ultimately show ?thesis
      using     xy below_in_P_simplex_like 
                pseudominimal_in_below_in_less_eq_glbound[of P x _ y b]
                simplex_like_below_in_above_pseudominimal_is_top[of x P]
                simplex_like_below_in_above_pseudominimal_is_top[of y P]
      unfolding poset_simplex_map_def
      by        force
  qed
qed

lemma OrderingSetIso_smap:
  "OrderingSetIso (op \<^bold>\<le>) (op \<^bold><) (op \<subseteq>) (op \<subset>) P smap"
proof (rule OrderingSetMap.isoI)
  show "OrderingSetMap op \<^bold>\<le> op \<^bold>< op \<subseteq> op \<subset> P smap"
    using poset_simplex_map_def below_in_P_simplex_like
          poset_to_PosetComplex_OrderingSetMap
    by    simp
next
  fix x y assume xy: "x\<in>P" "y\<in>P" "smap x \<subseteq> smap y"
  from xy(2) have "simplex_like (P.\<^bold>\<le>y)" using below_in_P_simplex_like by fast
  from this obtain g and A::"nat set"
    where "OrderingSetIso (op \<^bold>\<le>) (op \<^bold><) (op \<subseteq>) (op \<subset>) (P.\<^bold>\<le>y) g"
          "g`(P.\<^bold>\<le>y) = Pow A"
    using simplex_likeD_iso[of "P.\<^bold>\<le>y"]
    by    auto
  with xy show "x\<^bold>\<le>y"
    using poset_simplex_map_def collect_pseudominimals_below_in_eq[of y P g]
          collect_pseudominimals_below_in_poset[of P y g]
          inj_onD[OF inj_on_smap, of "the_inv_into (P.\<^bold>\<le>y) g (\<Union>(g ` smap x))" x]
          collect_pseudominimals_below_in_less_eq_top[of P y g A "smap x"]
    by    simp
qed (rule inj_on_smap)

lemmas rev_ordsetmap_smap =
  OrderingSetIso.rev_ordsetmap[OF OrderingSetIso_smap]

end (* context ComplexLikePoset *)

end (* theory *)
