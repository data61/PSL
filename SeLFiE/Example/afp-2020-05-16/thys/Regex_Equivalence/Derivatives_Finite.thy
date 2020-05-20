(* Author: Dmitriy Traytel, ported by Tobias Nipkow *)

section \<open>Finiteness of Derivatives Modulo ACI\<close>

(*<*)
(* split into Norm and Fin theories *)
theory Derivatives_Finite
imports "Regular-Sets.Derivatives"
begin
(*>*)

text \<open>Lifting constructors to lists\<close>

fun rexp_of_list where
  "rexp_of_list OP N [] = N"
| "rexp_of_list OP N [r] = r"
| "rexp_of_list OP N (r # rs) = OP r (rexp_of_list OP N rs)"

abbreviation "PLUS \<equiv> rexp_of_list Plus Zero"
abbreviation "TIMES \<equiv> rexp_of_list Times One"

lemma list_singleton_induct [case_names nil single cons]:
assumes "P []" and "\<And>x. P [x]" and "\<And>x y xs. P (y # xs) \<Longrightarrow> P (x # (y # xs))"
shows "P xs"
using assms by induction_schema (pat_completeness, lexicographic_order)


subsection \<open>ACI normalization\<close>

fun toplevel_summands :: "'a rexp \<Rightarrow> 'a rexp set" where
  "toplevel_summands (Plus r s) = toplevel_summands r \<union> toplevel_summands s"
| "toplevel_summands r = {r}"

abbreviation "flatten LISTOP X \<equiv> LISTOP (sorted_list_of_set X)"

lemma toplevel_summands_nonempty[simp]:
  "toplevel_summands r \<noteq> {}"
  by (induct r) auto

lemma toplevel_summands_finite[simp]:
  "finite (toplevel_summands r)"
  by (induct r) auto

primrec ACI_norm :: "('a::linorder) rexp \<Rightarrow> 'a rexp"  ("\<guillemotleft>_\<guillemotright>") where
  "\<guillemotleft>Zero\<guillemotright> = Zero"
| "\<guillemotleft>One\<guillemotright> = One"
| "\<guillemotleft>Atom a\<guillemotright> = Atom a"
| "\<guillemotleft>Plus r s\<guillemotright> = flatten PLUS (toplevel_summands (Plus \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>))"
| "\<guillemotleft>Times r s\<guillemotright> = Times \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>"
| "\<guillemotleft>Star r\<guillemotright> = Star \<guillemotleft>r\<guillemotright>"

lemma Plus_toplevel_summands: "Plus r s \<in> toplevel_summands t \<Longrightarrow> False"
by (induction t) auto

lemma toplevel_summands_not_Plus[simp]:
  "(\<forall>r s. x \<noteq> Plus r s) \<Longrightarrow> toplevel_summands x = {x}"
by (induction x) auto

lemma toplevel_summands_PLUS_strong:
  "\<lbrakk>xs \<noteq> []; list_all (\<lambda>x. \<not>(\<exists>r s. x = Plus r s)) xs\<rbrakk> \<Longrightarrow> toplevel_summands (PLUS xs) = set xs"
  by (induct xs rule: list_singleton_induct) auto

lemma toplevel_summands_flatten:
  "\<lbrakk>X \<noteq> {}; finite X; \<forall>x \<in> X. \<not>(\<exists>r s. x = Plus r s)\<rbrakk> \<Longrightarrow> toplevel_summands (flatten PLUS X) = X"
  using toplevel_summands_PLUS_strong[of "sorted_list_of_set X"]
  unfolding list_all_iff by fastforce

lemma ACI_norm_Plus: "\<guillemotleft>r\<guillemotright> = Plus s t \<Longrightarrow> \<exists>s t. r = Plus s t"
by (induction r) auto

lemma toplevel_summands_flatten_ACI_norm_image:
  "toplevel_summands (flatten PLUS (ACI_norm ` toplevel_summands r)) = ACI_norm ` toplevel_summands r"
by (intro toplevel_summands_flatten) (auto dest!: ACI_norm_Plus intro: Plus_toplevel_summands)

lemma toplevel_summands_flatten_ACI_norm_image_Union:
  "toplevel_summands (flatten PLUS (ACI_norm ` toplevel_summands r \<union> ACI_norm ` toplevel_summands s)) =
    ACI_norm ` toplevel_summands r \<union> ACI_norm ` toplevel_summands s"
by (intro toplevel_summands_flatten) (auto dest!: ACI_norm_Plus[OF sym] intro: Plus_toplevel_summands)

lemma toplevel_summands_ACI_norm:
  "toplevel_summands \<guillemotleft>r\<guillemotright> = ACI_norm ` toplevel_summands r"
by (induction r) (auto simp: toplevel_summands_flatten_ACI_norm_image_Union)

lemma ACI_norm_flatten:
  "\<guillemotleft>r\<guillemotright> = flatten PLUS (ACI_norm ` toplevel_summands r)"
by (induction r) (auto simp: image_Un toplevel_summands_flatten_ACI_norm_image)

theorem ACI_norm_idem[simp]: "\<guillemotleft>\<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>r\<guillemotright>"
proof (induct r)
  case (Plus r s)
  have "\<guillemotleft>\<guillemotleft>Plus r s\<guillemotright>\<guillemotright> = \<guillemotleft>flatten PLUS (toplevel_summands \<guillemotleft>r\<guillemotright> \<union> toplevel_summands \<guillemotleft>s\<guillemotright>)\<guillemotright>"
    (is "_ = \<guillemotleft>flatten PLUS ?U\<guillemotright>") by simp
  also have "\<dots> = flatten PLUS (ACI_norm ` toplevel_summands (flatten PLUS ?U))"
    by (simp only: ACI_norm_flatten)
  also have "toplevel_summands (flatten PLUS ?U) = ?U"
    by (intro toplevel_summands_flatten) (auto intro: Plus_toplevel_summands)
  also have "flatten PLUS (ACI_norm ` ?U) = flatten PLUS (toplevel_summands \<guillemotleft>r\<guillemotright> \<union> toplevel_summands \<guillemotleft>s\<guillemotright>)"
    by (simp only: image_Un toplevel_summands_ACI_norm[symmetric] Plus)
  finally show ?case by simp
qed auto

subsection "Atoms"

lemma atoms_toplevel_summands:
  "atoms s = (\<Union>r\<in>toplevel_summands s. atoms r)"
by (induct s) auto

lemma wf_PLUS: "atoms (PLUS xs) \<subseteq> \<Sigma> \<longleftrightarrow> (\<forall>r \<in> set xs. atoms r \<subseteq> \<Sigma>)"
by (induct xs rule: list_singleton_induct) auto

lemma atoms_PLUS: "atoms (PLUS xs) = (\<Union>r \<in> set xs. atoms r)"
by (induct xs rule: list_singleton_induct) auto

lemma atoms_flatten_PLUS:
  "finite X \<Longrightarrow> atoms (flatten PLUS X) = (\<Union>r \<in> X. atoms r)"
using wf_PLUS[of "sorted_list_of_set X"] by auto

theorem atoms_ACI_norm: "atoms \<guillemotleft>r\<guillemotright> = atoms r"
proof (induct r)
  case (Plus r1 r2) thus ?case
   using atoms_toplevel_summands[of "\<guillemotleft>r1\<guillemotright>"] atoms_toplevel_summands[of "\<guillemotleft>r2\<guillemotright>"]
   by(simp add: atoms_flatten_PLUS ball_Un Un_commute)
qed auto


subsection "Language"

lemma toplevel_summands_lang: "r \<in> toplevel_summands s \<Longrightarrow> lang r \<subseteq> lang s"
by (induct s) auto

lemma toplevel_summands_lang_UN:
  "lang s = (\<Union>r\<in>toplevel_summands s. lang r)"
by (induct s) auto

lemma toplevel_summands_in_lang:
  "w \<in> lang s = (\<exists>r\<in>toplevel_summands s. w \<in> lang r)"
by (induct s) auto

lemma lang_PLUS: "lang (PLUS xs) = (\<Union>r \<in> set xs. lang r)"
by (induct xs rule: list_singleton_induct) auto

lemma lang_PLUS_map[simp]:
  "lang (PLUS (map f xs)) = (\<Union>a\<in>set xs. lang (f a))"
by (induct xs rule: list_singleton_induct) auto

lemma lang_flatten_PLUS[simp]:
  "finite X \<Longrightarrow> lang (flatten PLUS X) = (\<Union>r \<in> X. lang r)"
using lang_PLUS[of "sorted_list_of_set X"] by fastforce

theorem lang_ACI_norm[simp]: "lang \<guillemotleft>r\<guillemotright> = lang r"
proof (induct r)
  case (Plus r1 r2)
  moreover
  from Plus[symmetric] have "lang (Plus r1 r2) \<subseteq> lang \<guillemotleft>Plus r1 r2\<guillemotright>"
    using toplevel_summands_in_lang[of _ "\<guillemotleft>r1\<guillemotright>"] toplevel_summands_in_lang[of _ "\<guillemotleft>r2\<guillemotright>"]
    by auto
  ultimately show ?case by (fastforce dest!: toplevel_summands_lang)
qed auto


subsection \<open>Finiteness of ACI-Equivalent Derivatives\<close>

lemma toplevel_summands_deriv:
  "toplevel_summands (deriv as r) = (\<Union>s\<in>toplevel_summands r. toplevel_summands (deriv as s))"
by (induction r) (auto simp: Let_def)

lemma derivs_Zero[simp]: "derivs xs Zero = Zero"
by (induction xs) auto

lemma derivs_One: "derivs xs One \<in> {Zero, One}"
by (induction xs) auto

lemma derivs_Atom: "derivs xs (Atom as) \<in> {Zero, One, Atom as}"
proof (induction xs)
  case Cons thus ?case by (auto intro: insertE[OF derivs_One])
qed simp

lemma derivs_Plus: "derivs xs (Plus r s) = Plus (derivs xs r) (derivs xs s)"
by (induction xs arbitrary: r s) auto

lemma derivs_PLUS: "derivs xs (PLUS ys) = PLUS (map (derivs xs) ys)"
by (induction ys rule: list_singleton_induct) (auto simp: derivs_Plus)

lemma toplevel_summands_derivs_Times: "toplevel_summands (derivs xs (Times r s)) \<subseteq>
  {Times (derivs xs r) s} \<union>
  {r'. \<exists>ys zs. r' \<in> toplevel_summands (derivs ys s) \<and> ys \<noteq> [] \<and> zs @ ys = xs}"
proof (induction xs arbitrary: r s)
  case (Cons x xs)
  thus ?case by (auto simp: Let_def derivs_Plus) (fastforce intro: exI[of _ "x#xs"])+
qed simp

lemma toplevel_summands_derivs_Star_nonempty:
  "xs \<noteq> [] \<Longrightarrow> toplevel_summands (derivs xs (Star r)) \<subseteq>
    {Times (derivs ys r) (Star r) | ys. \<exists>zs. ys \<noteq> [] \<and> zs @ ys = xs}"
proof (induction xs rule: length_induct)
  case (1 xs)
  then obtain y ys where "xs = y # ys" by (cases xs) auto
  thus ?case using spec[OF 1(1)]
    by (auto dest!: subsetD[OF toplevel_summands_derivs_Times] intro: exI[of _ "y#ys"])
       (auto elim!: impE dest!: meta_spec subsetD)
qed

lemma toplevel_summands_derivs_Star:
  "toplevel_summands (derivs xs (Star r)) \<subseteq>
    {Star r} \<union> {Times (derivs ys r) (Star r) | ys. \<exists>zs. ys \<noteq> [] \<and> zs @ ys = xs}"
by (cases "xs = []") (auto dest!: toplevel_summands_derivs_Star_nonempty)

lemma toplevel_summands_PLUS:
 "xs \<noteq> [] \<Longrightarrow> toplevel_summands (PLUS (map f xs)) = (\<Union>r \<in> set xs. toplevel_summands (f r))"
by (induction xs rule: list_singleton_induct) simp_all

lemma ACI_norm_toplevel_summands_Zero: "toplevel_summands r \<subseteq> {Zero} \<Longrightarrow> \<guillemotleft>r\<guillemotright> = Zero"
by (subst ACI_norm_flatten) (auto dest: subset_singletonD)

lemma finite_ACI_norm_toplevel_summands:
  "finite {f \<guillemotleft>s\<guillemotright> |s. toplevel_summands s \<subseteq> B}" if "finite B"
proof -
  have *: "{f \<guillemotleft>s\<guillemotright> | s.
    toplevel_summands s \<subseteq> B} \<subseteq> (f \<circ> flatten PLUS \<circ> (`) ACI_norm) ` Pow B"
    by (subst ACI_norm_flatten) auto
  with that show ?thesis 
    by (rule finite_surj [OF iffD2 [OF finite_Pow_iff]])
qed

theorem finite_derivs: "finite {\<guillemotleft>derivs xs r\<guillemotright> | xs . True}"
proof (induct r)
  case Zero show ?case by simp
next
  case One show ?case
   by (rule finite_surj[of "{Zero, One}"]) (blast intro: insertE[OF derivs_One])+
next
  case (Atom as) show ?case
    by (rule finite_surj[of "{Zero, One, Atom as}"]) (blast intro: insertE[OF derivs_Atom])+
next
  case (Plus r s)
  show ?case by (auto simp: derivs_Plus intro!: finite_surj[OF finite_cartesian_product[OF Plus]])
next
  case (Times r s)
  hence "finite (\<Union> (toplevel_summands ` {\<guillemotleft>derivs xs s\<guillemotright> | xs . True}))" by auto
  moreover have "{\<guillemotleft>r'\<guillemotright> |r'. \<exists>ys. r' \<in> toplevel_summands (derivs ys s)} =
    {r'. \<exists>ys. r' \<in> toplevel_summands \<guillemotleft>derivs ys s\<guillemotright>}"
    by (auto simp: toplevel_summands_ACI_norm)
  ultimately have fin: "finite {\<guillemotleft>r'\<guillemotright> |r'. \<exists>ys. r' \<in> toplevel_summands (derivs ys s)}"
    by (fastforce intro: finite_subset[of _ "\<Union> (toplevel_summands ` {\<guillemotleft>derivs xs s\<guillemotright> | xs . True})"])
  let ?X = "\<lambda>xs. {Times (derivs ys r) s | ys. True} \<union> {r'. r' \<in> (\<Union>ys. toplevel_summands (derivs ys s))}"
  show ?case
  proof (simp only: ACI_norm_flatten,
      rule finite_surj[of "{X. \<exists>xs. X \<subseteq> ACI_norm ` ?X xs}" _ "flatten PLUS"])
    show "finite {X. \<exists>xs. X \<subseteq> ACI_norm ` ?X xs}"
      using fin by (fastforce simp: image_Un elim: finite_subset[rotated] intro: finite_surj[OF Times(1), of _ "\<lambda>r. Times r \<guillemotleft>s\<guillemotright>"])
  qed (fastforce dest!: subsetD[OF toplevel_summands_derivs_Times] intro!: imageI)
next
  case (Star r)
  let ?f = "\<lambda>f r'. Times r' (Star (f r))"
  let ?X = "{Star r} \<union> ?f id ` {r'. r' \<in> {derivs ys r|ys. True}}"
  show ?case
  proof (simp only: ACI_norm_flatten,
      rule finite_surj[of "{X. X \<subseteq> ACI_norm ` ?X}" _ "flatten PLUS"])
    have *: "\<And>X. ACI_norm ` ?f (\<lambda>x. x) ` X = ?f ACI_norm ` ACI_norm ` X" by (auto simp: image_def)
    show "finite {X. X \<subseteq> ACI_norm ` ?X}"
      by (rule finite_Collect_subsets)
         (auto simp: * intro!: finite_imageI[of _ "?f ACI_norm"] intro: finite_subset[OF _ Star])
  qed (fastforce dest!: subsetD[OF toplevel_summands_derivs_Star] intro!: imageI)
qed


subsection \<open>Deriving preserves ACI-equivalence\<close>

lemma ACI_norm_PLUS:
  "list_all2 (\<lambda>r s. \<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright>) xs ys \<Longrightarrow> \<guillemotleft>PLUS xs\<guillemotright> = \<guillemotleft>PLUS ys\<guillemotright>"
proof (induct rule: list_all2_induct)
  case (Cons x xs y ys)
  hence "length xs = length ys" by (elim list_all2_lengthD)
  thus ?case using Cons by (induct xs ys rule: list_induct2) auto
qed simp

lemma toplevel_summands_ACI_norm_deriv:
  "(\<Union>a\<in>toplevel_summands r. toplevel_summands \<guillemotleft>deriv as \<guillemotleft>a\<guillemotright>\<guillemotright>) = toplevel_summands \<guillemotleft>deriv as \<guillemotleft>r\<guillemotright>\<guillemotright>"
proof (induct r)
  case (Plus r1 r2) thus ?case
   unfolding toplevel_summands.simps toplevel_summands_ACI_norm
     toplevel_summands_deriv[of as "\<guillemotleft>Plus r1 r2\<guillemotright>"] image_Un Union_Un_distrib
   by (simp add: image_UN)
qed (auto simp: Let_def)


lemma toplevel_summands_nullable:
  "nullable s = (\<exists>r\<in>toplevel_summands s. nullable r)"
by (induction s) auto

lemma nullable_PLUS:
  "nullable (PLUS xs) = (\<exists>r \<in> set xs. nullable r)"
by (induction xs rule: list_singleton_induct) auto

theorem ACI_norm_nullable: "nullable \<guillemotleft>r\<guillemotright> = nullable r"
proof (induction r)
  case (Plus r1 r2) thus ?case using toplevel_summands_nullable
    by (auto simp: nullable_PLUS)
qed auto

theorem ACI_norm_deriv: "\<guillemotleft>deriv as \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>deriv as r\<guillemotright>"
proof (induction r arbitrary: as)
  case (Plus r1 r2) thus ?case
   unfolding deriv.simps ACI_norm_flatten[of "deriv as \<guillemotleft>Plus r1 r2\<guillemotright>"]
     toplevel_summands_deriv[of as "\<guillemotleft>Plus r1 r2\<guillemotright>"] image_Un image_UN
   by (auto simp: toplevel_summands_ACI_norm toplevel_summands_flatten_ACI_norm_image_Union)
     (auto simp: toplevel_summands_ACI_norm[symmetric] toplevel_summands_ACI_norm_deriv)
qed (simp_all add: ACI_norm_nullable)

corollary deriv_preserves: "\<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright> \<Longrightarrow> \<guillemotleft>deriv as r\<guillemotright> = \<guillemotleft>deriv as s\<guillemotright>"
  by (rule box_equals[OF _ ACI_norm_deriv ACI_norm_deriv]) (erule arg_cong)

lemma derivs_snoc[simp]: "derivs (xs @ [x]) r = (deriv x (derivs xs r))"
by (induction xs arbitrary: r) auto

theorem ACI_norm_derivs: "\<guillemotleft>derivs xs \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>derivs xs r\<guillemotright>"
proof (induction xs arbitrary: r rule: rev_induct)
  case (snoc x xs) thus ?case
    using ACI_norm_deriv[of x "derivs xs r"] ACI_norm_deriv[of x "derivs xs \<guillemotleft>r\<guillemotright>"] by auto
qed simp

subsection \<open>Alternative ACI defintions\<close>

text \<open>Not necessary but conceptually nicer (and seems also to be faster?!)\<close>

fun ACI_nPlus :: "'a::linorder rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "ACI_nPlus (Plus r1 r2) s = ACI_nPlus r1 (ACI_nPlus r2 s)"
| "ACI_nPlus r (Plus s1 s2) =
  (if r = s1 then Plus s1 s2
  else if r < s1 then Plus r (Plus s1 s2)
  else Plus s1 (ACI_nPlus r s2))"
| "ACI_nPlus r s =
  (if r = s then r
  else if r < s then Plus r s
  else Plus s r)"

primrec ACI_norm_alt where 
  "ACI_norm_alt Zero = Zero"
| "ACI_norm_alt One = One"
| "ACI_norm_alt (Atom a) = Atom a"
| "ACI_norm_alt (Plus r s) = ACI_nPlus (ACI_norm_alt r) (ACI_norm_alt s)"
| "ACI_norm_alt (Times r s) = Times (ACI_norm_alt r) (ACI_norm_alt s)"
| "ACI_norm_alt (Star r) = Star (ACI_norm_alt r)"

lemma toplevel_summands_ACI_nPlus:
  "toplevel_summands (ACI_nPlus r s) = toplevel_summands (Plus r s)"
  by (induct r s rule: ACI_nPlus.induct) auto

lemma toplevel_summands_ACI_norm_alt:
  "toplevel_summands (ACI_norm_alt r) = ACI_norm_alt ` toplevel_summands r"
  by (induct r) (auto simp: toplevel_summands_ACI_nPlus)

lemma ACI_norm_alt_Plus:
  "ACI_norm_alt r = Plus s t \<Longrightarrow> \<exists>s t. r = Plus s t"
  by (induct r) auto

lemma toplevel_summands_flatten_ACI_norm_alt_image:
  "toplevel_summands (flatten PLUS (ACI_norm_alt ` toplevel_summands r)) = ACI_norm_alt ` toplevel_summands r"
  by (intro toplevel_summands_flatten) (auto dest!: ACI_norm_alt_Plus intro: Plus_toplevel_summands)

lemma ACI_norm_ACI_norm_alt: "\<guillemotleft>ACI_norm_alt r\<guillemotright> = \<guillemotleft>r\<guillemotright>"
proof (induction r)
  case (Plus r s) show ?case
    using ACI_norm_flatten [of r] ACI_norm_flatten [of s]
    by (auto simp add: toplevel_summands_ACI_nPlus)
      (metis ACI_norm_flatten Plus.IH(1) Plus.IH(2) image_Un toplevel_summands.simps(1) toplevel_summands_ACI_nPlus toplevel_summands_ACI_norm)
qed auto

lemma ACI_nPlus_singleton_PLUS: 
  "\<lbrakk>xs \<noteq> []; sorted xs; distinct xs; \<forall>x \<in> {x} \<union> set xs. \<not>(\<exists>r s. x = Plus r s)\<rbrakk> \<Longrightarrow>
  ACI_nPlus x (PLUS xs) = (if x \<in> set xs then PLUS xs else PLUS (insort x xs))"
proof (induct xs rule: list_singleton_induct)
  case (single y)
  thus ?case
    by (cases x y rule: linorder_cases) (induct x y rule: ACI_nPlus.induct, auto)+
next
  case (cons y1 y2 ys) thus ?case by (cases x) (auto)
qed simp

lemma ACI_nPlus_PLUS:
  "\<lbrakk>xs1 \<noteq> []; xs2 \<noteq> []; \<forall>x \<in> set (xs1 @ xs2). \<not>(\<exists>r s. x = Plus r s); sorted xs2; distinct xs2\<rbrakk>\<Longrightarrow>
  ACI_nPlus (PLUS xs1) (PLUS xs2) = flatten PLUS (set (xs1 @ xs2))"
proof (induct xs1 arbitrary: xs2 rule: list_singleton_induct)
  case (single x1)
  thus ?case
    apply (auto intro!: trans[OF ACI_nPlus_singleton_PLUS] simp del: sorted_list_of_set_insert)
    apply (simp only: insert_absorb)
    apply (metis List.finite_set finite_sorted_distinct_unique sorted_list_of_set)
    apply (rule arg_cong[of _ _ PLUS])
    apply (metis remdups_id_iff_distinct sorted_list_of_set_sort_remdups sorted_sort_id)
    done
next
  case (cons x11 x12 xs1) thus ?case
  apply (simp del: sorted_list_of_set_insert)
  apply (rule trans[OF ACI_nPlus_singleton_PLUS])
  apply (auto simp del: sorted_list_of_set_insert simp add: insert_commute[of x11])
  apply (auto simp only: Un_insert_left[of x11, symmetric] insert_absorb) []
  apply (auto simp only: Un_insert_right[of _ x11, symmetric] insert_absorb) []
  apply (auto simp add: insert_commute[of x12])
  done
qed simp

lemma ACI_nPlus_flatten_PLUS:
  "\<lbrakk>X1 \<noteq> {}; X2 \<noteq> {}; finite X1; finite X2; \<forall>x \<in> X1 \<union> X2. \<not>(\<exists>r s. x = Plus r s)\<rbrakk>\<Longrightarrow>
  ACI_nPlus (flatten PLUS X1) (flatten PLUS X2) = flatten PLUS (X1 \<union> X2)"
  by (rule trans[OF ACI_nPlus_PLUS]) auto

lemma ACI_nPlus_ACI_norm [simp]: "ACI_nPlus \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright> = \<guillemotleft>Plus r s\<guillemotright>"
  by (auto simp: image_Un Un_assoc ACI_norm_flatten [of r] ACI_norm_flatten [of s] ACI_norm_flatten [of "Plus r s"]
    toplevel_summands_flatten_ACI_norm_image
    intro!: trans [OF ACI_nPlus_flatten_PLUS])
    (metis ACI_norm_Plus Plus_toplevel_summands)+

lemma ACI_norm_alt:
  "ACI_norm_alt r = \<guillemotleft>r\<guillemotright>"
  by (induct r) auto

declare ACI_norm_alt[symmetric, code]

inductive ACI where
  ACI_refl:       "ACI r r" |
  ACI_sym:        "ACI r s \<Longrightarrow> ACI s r" |
  ACI_trans:      "ACI r s \<Longrightarrow> ACI s t \<Longrightarrow> ACI r t" |
  ACI_Plus_cong:  "\<lbrakk>ACI r1 s1; ACI r2 s2\<rbrakk> \<Longrightarrow> ACI (Plus r1 r2) (Plus s1 s2)" |
  ACI_Times_cong: "\<lbrakk>ACI r1 s1; ACI r2 s2\<rbrakk> \<Longrightarrow> ACI (Times r1 r2) (Times s1 s2)" |
  ACI_Star_cong:  "ACI r s \<Longrightarrow> ACI (Star r) (Star s)" |
  ACI_assoc:      "ACI (Plus (Plus r s) t) (Plus r (Plus s t))" |
  ACI_comm:       "ACI (Plus r s) (Plus s r)" |
  ACI_idem:       "ACI (Plus r r) r"

lemma ACI_atoms: "ACI r s \<Longrightarrow> atoms r = atoms s"
  by (induct rule: ACI.induct) auto

lemma ACI_nullable: "ACI r s \<Longrightarrow> nullable r = nullable s"
  by (induct rule: ACI.induct) auto

lemma ACI_lang: "ACI r s \<Longrightarrow> lang r = lang s"
  by (induct rule: ACI.induct) auto

lemma ACI_deriv: "ACI r s \<Longrightarrow> ACI (deriv a r) (deriv a s)"
proof (induct arbitrary: a rule: ACI.induct)
  case (ACI_Times_cong r1 s1 r2 s2) thus ?case
    by (auto simp: Let_def intro: ACI.intros dest: ACI_nullable)
      (metis ACI.ACI_Times_cong ACI_Plus_cong)
qed (auto intro: ACI.intros)

lemma ACI_Plus_assocI[intro]:
  "ACI (Plus r1 r2) s2 \<Longrightarrow> ACI (Plus r1 (Plus s1 r2)) (Plus s1 s2)"
  "ACI (Plus r1 r2) s2 \<Longrightarrow> ACI (Plus r1 (Plus r2 s1)) (Plus s1 s2)"
  by (metis ACI_assoc ACI_comm ACI_Plus_cong ACI_refl ACI_trans)+

lemma ACI_Plus_idemI[intro]: "\<lbrakk>ACI r s1; ACI r s2\<rbrakk> \<Longrightarrow> ACI r (Plus s1 s2)"
  by (metis ACI_Plus_cong ACI_idem ACI_sym ACI_trans)

lemma ACI_Plus_idemI'[intro]:
  "\<lbrakk>ACI r1 s1; ACI (Plus r1 r2) s2\<rbrakk> \<Longrightarrow> ACI (Plus r1 r2) (Plus s1 s2)"
  by (rule ACI_trans[OF ACI_Plus_cong[OF ACI_sym[OF ACI_idem] ACI_refl]
             ACI_trans[OF ACI_assoc ACI_trans[OF ACI_Plus_cong ACI_refl]]])

lemma ACI_ACI_nPlus: "\<lbrakk>ACI r1 s1; ACI r2 s2\<rbrakk> \<Longrightarrow> ACI (ACI_nPlus r1 r2) (Plus s1 s2)"
proof (induct r1 r2 arbitrary: s1 s2 rule: ACI_nPlus.induct)
  case 1
  from 1(2)[OF ACI_refl 1(1)[OF ACI_refl 1(4)]] 1(3) show ?case by (auto intro: ACI_comm ACI_trans)
next
  case ("2_1" r1 r2)
  with ACI_Plus_cong[OF ACI_refl "2_1"(1)[OF _ _ "2_1"(2) ACI_refl], of r1]
    show ?case by (auto intro: ACI.intros)
next
  case ("2_2" r1 r2)
  with ACI_Plus_cong[OF ACI_refl "2_2"(1)[OF _ _ "2_2"(2) ACI_refl], of r1]
    show ?case by (auto intro: ACI.intros)
next
  case ("2_3" _ r1 r2)
  with ACI_Plus_cong[OF ACI_refl "2_3"(1)[OF _ _ "2_3"(2) ACI_refl], of r1]
    show ?case by (auto intro: ACI.intros)
next
  case ("2_4" _ _ r1 r2)
  with ACI_Plus_cong[OF ACI_refl "2_4"(1)[OF _ _ "2_4"(2) ACI_refl], of r1]
    show ?case by (auto intro: ACI.intros)
next
  case ("2_5" _ r1 r2)
  with ACI_Plus_cong[OF ACI_refl "2_5"(1)[OF _ _ "2_5"(2) ACI_refl], of r1]
    show ?case by (auto intro: ACI.intros)
qed (auto intro: ACI.intros)

lemma ACI_ACI_norm: "ACI \<guillemotleft>r\<guillemotright> r"
  unfolding ACI_norm_alt[symmetric]
  by (induct r) (auto intro: ACI.intros simp: ACI_ACI_nPlus)

lemma ACI_norm_eqI: "ACI r s \<Longrightarrow> \<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright>"
  by (induct rule: ACI.induct) (auto simp: toplevel_summands_ACI_norm ACI_norm_flatten[symmetric]
    toplevel_summands_flatten_ACI_norm_image_Union ac_simps)

lemma ACI_I: "\<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright> \<Longrightarrow> ACI r s"
  by (metis ACI_ACI_norm ACI_sym ACI_trans)

lemma ACI_decidable: "ACI r s = (\<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright>)"
  by (metis ACI_I ACI_norm_eqI)

(*<*)
end
(*>*)
