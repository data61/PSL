(* Author: Dmitriy Traytel *)

section \<open>Derivatives of $\Pi$-Extended Regular Expressions\<close>
(*<*)
theory Pi_Derivatives
imports Pi_Regular_Exp
begin
(*>*)

locale embed = project \<Sigma> wf_atom project lookup
  for \<Sigma> :: "nat \<Rightarrow> 'a set"
  and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool"
  and project :: "'a \<Rightarrow> 'a"
  and lookup :: "'b \<Rightarrow> 'a \<Rightarrow> bool" +
fixes embed :: "'a \<Rightarrow> 'a list"
assumes embed: "\<And>a. a \<in> \<Sigma> n \<Longrightarrow> b \<in> set (embed a) = (b \<in> \<Sigma> (Suc n) \<and> project b = a)"
begin

subsection \<open>Syntactic Derivatives\<close>

primrec lderiv :: "'a \<Rightarrow> 'b rexp \<Rightarrow> 'b rexp" where
  "lderiv _ Zero = Zero"
| "lderiv _ Full = Full"
| "lderiv _ One = Zero"
| "lderiv a (Atom b) = (if lookup b a then One else Zero)"
| "lderiv a (Plus r s) = Plus (lderiv a r) (lderiv a s)"
| "lderiv a (Times r s) =
    (let r's = Times (lderiv a r) s
     in if final r then Plus r's (lderiv a s) else r's)"
| "lderiv a (Star r) = Times (lderiv a r) (Star r)"
| "lderiv a (Not r) = Not (lderiv a r)"
| "lderiv a (Inter r s) = Inter (lderiv a r) (lderiv a s)"
| "lderiv a (Pr r) = Pr (PLUS (map (\<lambda>a'. lderiv a' r) (embed a)))"

primrec lderivs where
  "lderivs [] r = r"
| "lderivs (w#ws) r = lderivs ws (lderiv w r)"



subsection \<open>Finiteness of ACI-Equivalent Derivatives\<close>

lemma toplevel_summands_lderiv:
  "toplevel_summands (lderiv as r) = (\<Union>s\<in>toplevel_summands r. toplevel_summands (lderiv as s))"
  by (induct r) (auto simp: Let_def)

lemma lderivs_Zero[simp]: "lderivs xs Zero = Zero"
  by (induct xs) auto

lemma lderivs_Full[simp]: "lderivs xs Full = Full"
  by (induct xs) auto

lemma lderivs_One: "lderivs xs One \<in> {Zero, One}"
  by (induct xs) auto

lemma lderivs_Atom: "lderivs xs (Atom as) \<in> {Zero, One, Atom as}"
proof (induct xs)
  case (Cons x xs) thus ?case by (auto intro: insertE[OF lderivs_One])
qed simp

lemma lderivs_Plus: "lderivs xs (Plus r s) = Plus (lderivs xs r) (lderivs xs s)"
  by (induct xs arbitrary: r s) auto

lemma lderivs_PLUS: "lderivs xs (PLUS ys) = PLUS (map (lderivs xs) ys)"
  by (induct ys rule: list_singleton_induct) (auto simp: lderivs_Plus)

lemma toplevel_summands_lderivs_Times: "toplevel_summands (lderivs xs (Times r s)) \<subseteq>
  {Times (lderivs xs r) s} \<union>
  {r'. \<exists>ys zs. r' \<in> toplevel_summands (lderivs ys s) \<and> ys \<noteq> [] \<and> zs @ ys = xs}"
proof (induct xs arbitrary: r s)
  case (Cons x xs)
  thus ?case by (auto simp: Let_def lderivs_Plus) (fastforce intro: exI[of _ "x#xs"])+
qed simp

lemma toplevel_summands_lderivs_Star_nonempty:
  "xs \<noteq> [] \<Longrightarrow> toplevel_summands (lderivs xs (Star r)) \<subseteq>
    {Times (lderivs ys r) (Star r) | ys. \<exists>zs. ys \<noteq> [] \<and> zs @ ys = xs}"
proof (induct xs rule: length_induct)
  case (1 xs)
  then obtain y ys where "xs = y # ys" by (cases xs) auto
  thus ?case using spec[OF 1(1)]
    by (auto dest!: subsetD[OF toplevel_summands_lderivs_Times] intro: exI[of _ "y#ys"])
       (auto elim!: impE dest!: meta_spec subsetD)
qed

lemma toplevel_summands_lderivs_Star:
  "toplevel_summands (lderivs xs (Star r)) \<subseteq>
    {Star r} \<union> {Times (lderivs ys r) (Star r) | ys. \<exists>zs. ys \<noteq> [] \<and> zs @ ys = xs}"
  by (cases "xs = []") (auto dest!: toplevel_summands_lderivs_Star_nonempty)

lemma ex_lderivs_Pr: "\<exists>s. lderivs ass (Pr r) = Pr s"
  by (induct ass arbitrary: r) auto

lemma toplevel_summands_PLUS:
 "xs \<noteq> [] \<Longrightarrow> toplevel_summands (PLUS (map f xs)) = (\<Union>r \<in> set xs. toplevel_summands (f r))"
  by (induct xs rule: list_singleton_induct) simp_all

lemma lderiv_toplevel_summands_Zero:
  "\<lbrakk>lderivs xs (Pr r) = Pr s; toplevel_summands r = {Zero}\<rbrakk> \<Longrightarrow> toplevel_summands s = {Zero}"
proof (induct xs arbitrary: r s)
  case (Cons y ys)
  from Cons.prems(1) have "toplevel_summands (PLUS (map (\<lambda>a. lderiv a r) (embed y))) = {Zero}"
  proof (cases "embed y = []")
    case False
    show ?thesis using Cons.prems(2) unfolding toplevel_summands_PLUS[OF False]
      by (subst toplevel_summands_lderiv) (simp add: False)
  qed simp
  with Cons show ?case by simp
qed simp

lemma toplevel_summands_lderivs_Pr:
  "\<lbrakk>xs \<noteq> []; lderivs xs (Pr r) = Pr s\<rbrakk> \<Longrightarrow>
    toplevel_summands s \<subseteq> {Zero} \<or> toplevel_summands s \<subseteq> (\<Union>xs. toplevel_summands (lderivs xs r))"
proof (induct xs arbitrary: r s)
  case (Cons y ys) note * = this
  show ?case
  proof (cases "embed y = []")
    case True with Cons show ?thesis by (cases "ys = []") (auto dest: lderiv_toplevel_summands_Zero)
  next
    case False 
    show ?thesis
    proof (cases ys)
      case Nil with * show ?thesis
        by (auto simp: toplevel_summands_PLUS[OF False]) (metis lderivs.simps)
    next
      case (Cons z zs)
      have "toplevel_summands s \<subseteq> {Zero} \<or> toplevel_summands s \<subseteq>
       (\<Union>xs. toplevel_summands (lderivs xs (PLUS (map (\<lambda>a. lderiv a r) (embed y)))))" (is "_ \<or> ?B")
        by (rule *(1)) (auto simp: Cons *(3)[symmetric])
      thus ?thesis
      proof
        assume ?B
        also have "\<dots> \<subseteq> (\<Union>xs. toplevel_summands (lderivs xs r))"
          by (auto simp: lderivs_PLUS toplevel_summands_PLUS[OF False]) (metis lderivs.simps(2))
        finally show ?thesis ..
      qed blast
    qed
  qed
qed simp

lemma lderivs_Pr:
  "{lderivs xs (Pr r) | xs. True} \<subseteq>
    {Pr s | s. toplevel_summands s \<subseteq> {Zero} \<or>
               toplevel_summands s \<subseteq> (\<Union>xs. toplevel_summands (lderivs xs r))}"
  (is "?L \<subseteq>?R")
proof (rule subsetI)
  fix s assume "s \<in> ?L"
  then obtain xs where "s = lderivs xs (Pr r)" by blast
  moreover obtain t where "lderivs xs (Pr r) = Pr t" using ex_lderivs_Pr by blast
  ultimately show "s \<in> ?R"
    by (cases "xs = []") (auto dest!: toplevel_summands_lderivs_Pr elim!: allE[of _ "[]"])
qed

lemma ACI_norm_toplevel_summands_Zero: "toplevel_summands r \<subseteq> {Zero} \<Longrightarrow> \<guillemotleft>r\<guillemotright> = Zero"
  by (subst ACI_norm_flatten) (auto dest: subset_singletonD)

lemma ACI_norm_lderivs_Pr:
  "ACI_norm ` {lderivs xs (Pr r) | xs. True} \<subseteq>
    {Pr Zero} \<union> {Pr \<guillemotleft>s\<guillemotright> | s. toplevel_summands s \<subseteq> (\<Union>xs. toplevel_summands \<guillemotleft>lderivs xs r\<guillemotright>)}"
proof (intro subset_trans[OF image_mono[OF lderivs_Pr]] subsetI,
       elim imageE CollectE exE conjE disjE)
  fix x x' s :: "'b rexp"
  assume *: "x = \<guillemotleft>x'\<guillemotright>" "x' = Pr s" and "toplevel_summands s \<subseteq> {Zero}"
  hence "\<guillemotleft>Pr s\<guillemotright> = Pr Zero" using ACI_norm_toplevel_summands_Zero by simp
  thus "x \<in> {Pr Zero} \<union>
    {Pr \<guillemotleft>s\<guillemotright> |s. toplevel_summands s \<subseteq> (\<Union>xs. toplevel_summands \<guillemotleft>lderivs xs r\<guillemotright>)}"
    unfolding * by blast
next
  fix x x' s :: "'b rexp"
  assume *: "x = \<guillemotleft>x'\<guillemotright>" "x' = Pr s" and "toplevel_summands s \<subseteq> (\<Union>xs. toplevel_summands (lderivs xs r))"
  hence "toplevel_summands \<guillemotleft>s\<guillemotright> \<subseteq> (\<Union>xs. toplevel_summands \<guillemotleft>lderivs xs r\<guillemotright>)"
    by (fastforce simp: toplevel_summands_ACI_norm)
  moreover have "x = Pr \<guillemotleft>\<guillemotleft>s\<guillemotright>\<guillemotright>" unfolding * ACI_norm_idem ACI_norm.simps(10) ..
  ultimately show "x \<in> {Pr Zero} \<union>
    {Pr \<guillemotleft>s\<guillemotright> |s. toplevel_summands s \<subseteq> (\<Union>xs. toplevel_summands \<guillemotleft>lderivs xs r\<guillemotright>)}"
    by blast
qed

lemma finite_ACI_norm_toplevel_summands: "finite B \<Longrightarrow> finite {f \<guillemotleft>s\<guillemotright> |s. toplevel_summands s \<subseteq> B}"
  apply (elim finite_surj [OF iffD2 [OF finite_Pow_iff], of _ _ "f o flatten PLUS o image ACI_norm"])
  apply (subst ACI_norm_flatten)
  apply auto
  done

lemma lderivs_Not: "lderivs xs (Not r) = Not (lderivs xs r)"
  by (induct xs arbitrary: r) auto

lemma lderivs_Inter: "lderivs xs (Inter r s) = Inter (lderivs xs r) (lderivs xs s)"
  by (induct xs arbitrary: r s) auto

theorem finite_lderivs: "finite {\<guillemotleft>lderivs xs r\<guillemotright> | xs . True}"
proof (induct r)
  case Zero show ?case by simp
next
  case Full show ?case by simp
next
  case One show ?case
   by (rule finite_surj[of "{Zero, One}"]) (blast intro: insertE[OF lderivs_One])+
next
  case (Atom as) show ?case
    by (rule finite_surj[of "{Zero, One, Atom as}"]) (blast intro: insertE[OF lderivs_Atom])+
next
  case (Plus r s)
  show ?case by (auto simp: lderivs_Plus intro!: finite_surj[OF finite_cartesian_product[OF Plus]])
next
  case (Times r s)
  hence "finite (\<Union> (toplevel_summands ` {\<guillemotleft>lderivs xs s\<guillemotright> | xs . True}))" by auto
  moreover have "{\<guillemotleft>r'\<guillemotright> |r'. \<exists>ys. r' \<in> toplevel_summands (lderivs ys s)} =
    {r'. \<exists>ys. r' \<in> toplevel_summands \<guillemotleft>lderivs ys s\<guillemotright>}"
    unfolding toplevel_summands_ACI_norm by auto
  ultimately have fin: "finite {\<guillemotleft>r'\<guillemotright> |r'. \<exists>ys. r' \<in> toplevel_summands (lderivs ys s)}"
    by (fastforce intro: finite_subset[of _ "\<Union> (toplevel_summands ` {\<guillemotleft>lderivs xs s\<guillemotright> | xs . True})"])
  let ?X = "\<lambda>xs. {Times (lderivs ys r) s | ys. True} \<union> {r'. r' \<in> (\<Union>ys. toplevel_summands (lderivs ys s))}"
  show ?case
  proof (simp only: ACI_norm_flatten,
      rule finite_surj[of "{X. \<exists>xs. X \<subseteq> ACI_norm ` ?X xs}" _ "flatten PLUS"])
    show "finite {X. \<exists>xs. X \<subseteq> ACI_norm ` ?X xs}"
      using fin by (fastforce simp: image_Un elim: finite_subset[rotated] intro: finite_surj[OF Times(1), of _ "\<lambda>r. Times r \<guillemotleft>s\<guillemotright>"])
  qed (fastforce dest!: subsetD[OF toplevel_summands_lderivs_Times] intro!: imageI)
next
  case (Star r)
  let ?f = "\<lambda>f r'. Times r' (Star (f r))"
  let ?X = "{Star r} \<union> ?f id ` {r'. r' \<in> {lderivs ys r|ys. True}}"
  show ?case
  proof (simp only: ACI_norm_flatten,
      rule finite_surj[of "{X. X \<subseteq> ACI_norm ` ?X}" _ "flatten PLUS"])
    have *: "\<And>X. ACI_norm ` ?f (\<lambda>x. x) ` X = ?f ACI_norm ` ACI_norm ` X" by (auto simp: image_def)
    show "finite {X. X \<subseteq> ACI_norm ` ?X}"
      by (rule finite_Collect_subsets)
         (auto simp: * intro!: finite_imageI[of _ "?f ACI_norm"] intro: finite_subset[OF _ Star])
  qed (fastforce dest!: subsetD[OF toplevel_summands_lderivs_Star] intro!: imageI)
next
  case (Not r) thus ?case by (auto simp: lderivs_Not) (blast intro: finite_surj)
next
  case (Inter r s)
  show ?case by (auto simp: lderivs_Inter intro!: finite_surj[OF finite_cartesian_product[OF Inter]])
next
  case (Pr r)
  hence *: "finite (\<Union> (toplevel_summands ` {\<guillemotleft>lderivs xs r\<guillemotright> | xs . True}))" by auto
  have "finite (\<Union>xs. toplevel_summands \<guillemotleft>lderivs xs r\<guillemotright>)" by (rule finite_subset[OF _ *]) auto
  hence fin: "finite {Pr \<guillemotleft>s\<guillemotright> |s. toplevel_summands s \<subseteq> (\<Union>xs. toplevel_summands \<guillemotleft>lderivs xs r\<guillemotright>)}"
    by (intro finite_ACI_norm_toplevel_summands)
  have "{s. \<exists>xs. s = \<guillemotleft>lderivs xs (Pr r)\<guillemotright>} = {\<guillemotleft>s\<guillemotright>| s. \<exists>xs. s = lderivs xs (Pr r)}" by auto
  thus ?case using finite_subset[OF ACI_norm_lderivs_Pr, of r] fin unfolding image_Collect by auto
qed

subsection \<open>Wellformedness and language of derivatives\<close>

lemma wf_lderiv[simp]: "wf n r \<Longrightarrow> wf n (lderiv w r)"
  by (induct r arbitrary: n w) (auto simp add: Let_def)

lemma wf_lderivs[simp]: "wf n r \<Longrightarrow> wf n (lderivs ws r)"
  by (induct ws arbitrary: r) (auto intro: wf_lderiv)

lemma lQuot_map_project:
assumes "as \<in> \<Sigma> n" "A \<subseteq> lists (\<Sigma> (Suc n))"
shows "lQuot as (map project ` A) = map project ` (\<Union>a \<in> set (embed as). lQuot a A)" (is "?L = ?R")
proof (intro equalityI image_subsetI subsetI)
  fix xss assume "xss \<in> ?L"
  with assms obtain zss
    where zss: "zss \<in> A" "as # xss = map project zss"
    unfolding lQuot_def by fastforce
  hence "xss = map project (tl zss)" by auto
  with zss assms(2) show "xss \<in> ?R" using embed[OF project, of _ n] unfolding lQuot_def by fastforce
next
  fix xss assume "xss \<in> (\<Union>a \<in> set (embed as). lQuot a A)"
  with assms(1) show "map project xss \<in> lQuot as (map project ` A)" unfolding lQuot_def
    by (fastforce intro!: rev_image_eqI simp: embed)
qed

lemma lang_lderiv: "\<lbrakk>wf n r; w \<in> \<Sigma> n\<rbrakk> \<Longrightarrow> lang n (lderiv w r) = lQuot w (lang n r)"
proof (induct r arbitrary: n w)
  case (Pr r)
  hence *: "wf (Suc n) r" "\<And>w'. w' \<in> set (embed w) \<Longrightarrow>  w' \<in> \<Sigma> (Suc n)" by (auto simp: embed)
  from Pr(1)[OF *] lQuot_map_project[OF Pr(3) lang_subset_lists[OF *(1)]] show ?case
    by (auto simp: wf_lderiv[OF *(1)])
qed (auto simp: Let_def lang_final[symmetric])

lemma lang_lderivs: "\<lbrakk>wf n r; wf_word n ws\<rbrakk> \<Longrightarrow> lang n (lderivs ws r) = lQuots ws (lang n r)"
  by (induct ws arbitrary: r) (auto simp: lang_lderiv)

corollary lderivs_final:
assumes "wf n r" "wf_word n ws"
shows "final (lderivs ws r) \<longleftrightarrow> ws \<in> lang n r"
  using lang_lderivs[OF assms] lang_final[of "lderivs ws r" n] by auto

abbreviation "lderivs_set n r s \<equiv> {(\<guillemotleft>lderivs w r\<guillemotright>, \<guillemotleft>lderivs w s\<guillemotright>) | w. wf_word n w}"



subsection \<open>Deriving preserves ACI-equivalence\<close>

lemma ACI_norm_PLUS:
  "list_all2 (\<lambda>r s. \<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright>) xs ys \<Longrightarrow> \<guillemotleft>PLUS xs\<guillemotright> = \<guillemotleft>PLUS ys\<guillemotright>"
proof (induct rule: list_all2_induct)
  case (Cons x xs y ys)
  hence "length xs = length ys" by (elim list_all2_lengthD)
  thus ?case using Cons by (induct xs ys rule: list_induct2) auto
qed simp

lemma toplevel_summands_ACI_norm_lderiv:
  "(\<Union>a\<in>toplevel_summands r. toplevel_summands \<guillemotleft>lderiv as \<guillemotleft>a\<guillemotright>\<guillemotright>) = toplevel_summands \<guillemotleft>lderiv as \<guillemotleft>r\<guillemotright>\<guillemotright>"
proof (induct r)
  case (Plus r1 r2) thus ?case
   unfolding toplevel_summands.simps toplevel_summands_ACI_norm
     toplevel_summands_lderiv[of as "\<guillemotleft>Plus r1 r2\<guillemotright>"] image_Un Union_Un_distrib
   by (simp add: image_UN)
qed (auto simp: Let_def)

theorem ACI_norm_lderiv:
  "\<guillemotleft>lderiv as \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>lderiv as r\<guillemotright>"
proof (induct r arbitrary: as)
  case (Plus r1 r2) thus ?case
   unfolding lderiv.simps ACI_norm_flatten[of "lderiv as \<guillemotleft>Plus r1 r2\<guillemotright>"]
     toplevel_summands_lderiv[of as "\<guillemotleft>Plus r1 r2\<guillemotright>"] image_Un image_UN
   by (auto simp: toplevel_summands_ACI_norm toplevel_summands_flatten_ACI_norm_image_Union)
     (auto simp: toplevel_summands_ACI_norm[symmetric] toplevel_summands_ACI_norm_lderiv)
next
  case (Pr r)
  hence "list_all2 (\<lambda>r s. \<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright>)
    (map (\<lambda>a. lderiv a \<guillemotleft>r\<guillemotright>) (embed as)) (map (\<lambda>a. lderiv a r) (embed as))"
    unfolding list_all2_map1 list_all2_map2 by (intro list_all2_refl)
  thus ?case unfolding lderiv.simps ACI_norm.simps by (blast intro: ACI_norm_PLUS)
qed (simp_all add: Let_def)


corollary lderiv_preserves: "\<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright> \<Longrightarrow> \<guillemotleft>lderiv as r\<guillemotright> = \<guillemotleft>lderiv as s\<guillemotright>"
  by (rule box_equals[OF _ ACI_norm_lderiv ACI_norm_lderiv]) (erule arg_cong)

lemma lderivs_snoc[simp]: "lderivs (ws @ [w]) r = (lderiv w (lderivs ws r))"
  by (induct ws arbitrary: r) auto

theorem ACI_norm_lderivs:
  "\<guillemotleft>lderivs ws \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>lderivs ws r\<guillemotright>"
proof (induct ws arbitrary: r rule: rev_induct)
  case (snoc w ws) thus ?case
    using ACI_norm_lderiv[of w "lderivs ws r"] ACI_norm_lderiv[of w "lderivs ws \<guillemotleft>r\<guillemotright>"] by auto
qed simp

lemma lderivs_alt: "\<guillemotleft>lderivs w r\<guillemotright> = fold (\<lambda>a r. \<guillemotleft>lderiv a r\<guillemotright>) w \<guillemotleft>r\<guillemotright>"
  by (induct w arbitrary: r) (auto simp: ACI_norm_lderiv)

lemma finite_fold_lderiv: "finite {fold (\<lambda>a r. \<guillemotleft>lderiv a r\<guillemotright>) w \<guillemotleft>s\<guillemotright> |w. True}"
  using finite_lderivs unfolding lderivs_alt .

end

(*<*)
end
(*>*)
