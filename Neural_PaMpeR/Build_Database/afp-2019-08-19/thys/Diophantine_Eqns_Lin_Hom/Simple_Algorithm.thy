(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

theory Simple_Algorithm
  imports
    Linear_Diophantine_Equations
    Minimize_Wrt
begin

(*TODO: move?*)
lemma concat_map_nth0: "xs \<noteq> [] \<Longrightarrow> f (xs ! 0) \<noteq> [] \<Longrightarrow> concat (map f xs) ! 0 = f (xs ! 0) ! 0"
  by (induct xs) (auto simp: nth_append)


subsection \<open>Reverse-Lexicographic Enumeration of Potential Minimal Solutions\<close>

fun rlex2 :: "(nat list \<times> nat list) \<Rightarrow> (nat list \<times> nat list) \<Rightarrow> bool"  (infix "<\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2" 50)
  where
    "(xs, ys) <\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2 (us, vs) \<longleftrightarrow> xs @ ys <\<^sub>r\<^sub>l\<^sub>e\<^sub>x us @ vs"

lemma rlex2_irrefl:
  "\<not> x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2 x"
  by (cases x) (auto simp: rlex_irrefl)

lemma rlex2_not_sym: "x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2 y \<Longrightarrow> \<not> y <\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2 x"
  using rlex_not_sym by (cases x; cases y; simp)

lemma less_imp_rlex2: "\<not> (case x of (x, y) \<Rightarrow> \<lambda>(u, v). \<not> x @ y <\<^sub>v u @ v) y \<Longrightarrow> x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2 y"
  using less_imp_rlex by (cases x; cases y; auto)


text \<open>Generate all lists (of natural numbers) of length \<open>n\<close> with elements bounded by \<open>B\<close>.\<close>
fun gen :: "nat \<Rightarrow> nat \<Rightarrow> nat list list"
  where
    "gen B 0 = [[]]"
  | "gen B (Suc n) = [x#xs . xs \<leftarrow> gen B n, x \<leftarrow> [0 ..< B + 1]]"

definition "generate A B m n = tl [(x, y) . y \<leftarrow> gen B n, x \<leftarrow> gen A m]"

definition "check a b = filter (\<lambda>(x, y). a \<bullet> x = b \<bullet> y)"

definition "minimize = minimize_wrt (\<lambda>(x, y) (u, v). \<not> x @ y <\<^sub>v u @ v)"

definition "solutions a b =
  (let A = Max (set b); B = Max (set a); m = length a; n = length b
  in minimize (check a b (generate A B m n)))"

lemma set_gen: "set (gen B n) = {xs. length xs = n \<and> (\<forall>i<n. xs ! i \<le> B)}" (is "_ = ?A n")
proof (induct n)
  case [simp]: (Suc n)
  { fix xs assume "xs \<in> ?A (Suc n)"
    then have "xs \<in> set (gen B (Suc n))"
      by (cases xs) (force simp: All_less_Suc2)+ }
  then show ?case by (auto simp: less_Suc_eq_0_disj)
qed simp

abbreviation "gen2 A B m n \<equiv> [(x, y) . y \<leftarrow> gen B n, x \<leftarrow> gen A m]"

lemma sorted_wrt_gen:
  "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x) (gen B n)"
by (induction n)
   (auto simp: rlex_Cons sorted_wrt_append sorted_wrt_map rlex_irrefl
    intro!: sorted_wrt_concat_map [where h = id, simplified])

lemma sorted_wrt_gen2: "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2) (gen2 A B m n)"
  by (intro sorted_wrt_concat_map_map [where Q = "(<\<^sub>r\<^sub>l\<^sub>e\<^sub>x)"] sorted_wrt_gen)
    (auto simp: set_gen rlex_def intro:  lex_append_leftI lex_append_rightI)

lemma gen_ne [simp]: "gen B n \<noteq> []" by (induct n) auto

lemma gen2_ne: "gen2 A B m n \<noteq> []" by auto

lemma sorted_wrt_generate: "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2) (generate A B m n)"
  by (auto simp: generate_def intro: sorted_wrt_tl sorted_wrt_gen2)

abbreviation "check_generate a b \<equiv> check a b (generate (Max (set b)) (Max (set a)) (length a) (length b))"

lemma sorted_wrt_check_generate: "sorted_wrt (<\<^sub>r\<^sub>l\<^sub>e\<^sub>x\<^sub>2) (check_generate a b)"
  by (auto simp: check_def intro: sorted_wrt_filter sorted_wrt_generate)

lemma in_tl_gen2: "x \<in> set (tl (gen2 A B m n)) \<Longrightarrow> x \<in> set (gen2 A B m n)"
  by (rule list.set_sel) simp

lemma gen_nth0 [simp]: "gen B n ! 0 = zeroes n"
  by (induct n) (auto simp: nth_append concat_map_nth0)

lemma gen2_nth0 [simp]:
  "gen2 A B m n ! 0 = (zeroes m, zeroes n)"
  by (auto simp: concat_map_nth0)

lemma set_gen2:
  "set (gen2 A B m n) = {(x, y). length x = m \<and> length y = n \<and> (\<forall>i<m. x ! i \<le> A) \<and> (\<forall>j<n. y ! j \<le> B)}"
  by (auto simp: set_gen)

lemma gen2_unique:
  assumes "i < j"
    and "j < length (gen2 A B m n)"
  shows "gen2 A B m n ! i \<noteq> gen2 A B m n ! j"
  using sorted_wrt_nth_less [OF sorted_wrt_gen2 assms]
  by (auto simp: rlex2_irrefl)

lemma zeroes_ni_tl_gen2:
  "(zeroes m, zeroes n) \<notin> set (tl (gen2 A B m n))"
proof -
  have "gen2 A B m n ! 0 = (zeroes m, zeroes n)" by (auto simp: generate_def)
  with gen2_unique[of 0 _ A m B n] show ?thesis
    by (metis (no_types, lifting) Suc_eq_plus1 in_set_conv_nth length_tl less_diff_conv nth_tl zero_less_Suc)
qed

lemma set_generate:
  "set (generate A B m n) = {(x, y). (x, y) \<noteq> (zeroes m, zeroes n) \<and> (x, y) \<in> set (gen2 A B m n)}"
proof
  show "set (generate A B m n)
    \<subseteq> {(x, y).(x, y) \<noteq> (zeroes m, zeroes n) \<and> (x, y) \<in> set (gen2 A B m n)}"
    using in_tl_gen2 and mem_Collect_eq and zeroes_ni_tl_gen2 by (auto simp: generate_def)
next
  have "(zeroes m, zeroes n) = hd (gen2 A B m n)"
    by (simp add: hd_conv_nth)
  moreover have "set (gen2 A B m n) = set (generate A B m n) \<union> {(zeroes m, zeroes n)}"
    by (metis Un_empty_right generate_def Un_insert_right gen2_ne calculation list.exhaust_sel list.simps(15))
  ultimately show " {(x, y). (x, y) \<noteq> (zeroes m, zeroes n) \<and> (x, y) \<in> set (gen2 A B m n)}
    \<subseteq> set (generate A B m n)"
    by blast
qed

lemma set_check_generate:
  "set (check_generate a b) = {(x, y).
    (x, y) \<noteq> (zeroes (length a), zeroes (length b)) \<and>
    length x = length a \<and> length y = length b \<and> a \<bullet> x = b \<bullet> y \<and>
    (\<forall>i<length a. x ! i \<le> Max (set b)) \<and> (\<forall>j<length b. y ! j \<le> Max (set a))}"
  unfolding check_def and set_filter and set_generate and set_gen2 by auto

lemma set_minimize_check_generate:
  "set (minimize (check_generate a b)) =
    {(x, y)\<in>set (check_generate a b). \<not> (\<exists>(u, v)\<in>set (check_generate a b). u @ v <\<^sub>v x @ y)}"
  unfolding minimize_def
  by (subst set_minimize_wrt [OF _ sorted_wrt_check_generate]) (auto dest: rlex_not_sym less_imp_rlex)

lemma set_solutions_iff:
  "set (solutions a b) =
    {(x, y) \<in> set (check_generate a b). \<not> (\<exists>(u, v)\<in>set (check_generate a b). u @ v <\<^sub>v x @ y)}"
  by (auto simp: solutions_def set_minimize_check_generate)


subsubsection \<open>Completeness: every minimal solution is generated by \<open>solutions\<close>\<close>

lemma (in hlde) solutions_complete:
  "Minimal_Solutions \<subseteq> set (solutions a b)"
proof (rule subrelI)
  let ?A = "Max (set b)" and ?B = "Max (set a)"
  fix x y assume min: "(x, y) \<in> Minimal_Solutions"
  then have "(x, y) \<in> set (check a b (generate ?A ?B m n))"
    by (auto simp: Minimal_Solutions_alt_def set_check_generate less_eq_def in_Solutions_iff)
  moreover have "\<forall>(u, v) \<in> set (check a b (generate ?A ?B m n)). \<not> u @ v <\<^sub>v x @ y"
    using min and no0
    by (auto simp: check_def set_generate neq_0_iff' set_gen nonzero_iff dest!: Minimal_Solutions_min)
  ultimately show "(x, y) \<in> set (solutions a b)" by (auto simp: set_solutions_iff)
qed


subsubsection \<open>Correctness: \<open>solutions\<close> generates only minimal solutions.\<close>

lemma (in hlde) solutions_sound:
  "set (solutions a b) \<subseteq> Minimal_Solutions"
proof (rule subrelI)
  fix x y assume sol: "(x, y) \<in> set (solutions a b)"
  show "(x, y) \<in> Minimal_Solutions"
  proof (rule Minimal_SolutionsI')
    show *: "(x, y) \<in> Solutions"
      using sol by (auto simp: set_solutions_iff in_Solutions_iff check_def set_generate set_gen)
    show "nonzero x"
      using sol and nonzero_iff and replicate_eqI and nonzero_Solutions_iff [OF *]
      by (fastforce simp: solutions_def minimize_def check_def set_generate set_gen dest!: minimize_wrtD)
    show "\<not> (\<exists>(u, v)\<in>Minimal_Solutions. u @ v <\<^sub>v x @ y)"
    proof
      have min_cg: "(x, y) \<in> set (minimize (check_generate a b))"
        using sol by (auto simp: solutions_def)
      note * = in_minimize_wrt_False [OF _ sorted_wrt_check_generate min_cg [unfolded minimize_def]]

      assume "\<exists>(u, v)\<in>Minimal_Solutions. u @ v <\<^sub>v x @ y"
      then obtain u and v where "(u, v) \<in> Minimal_Solutions" and less: "u @ v <\<^sub>v x @ y" by blast
      then have "(u, v) \<in> set (solutions a b)" by (auto intro: solutions_complete [THEN subsetD])
      then have "(u, v) \<in> set (check_generate a b)"
        by (auto simp: solutions_def minimize_def dest: minimize_wrtD)
      from * [OF _ _ _ this] and less show False
        using less_imp_rlex and rlex_not_sym by force
    qed
  qed
qed

lemma (in hlde) set_solutions [simp]: "set (solutions a b) = Minimal_Solutions"
  using solutions_sound and solutions_complete by blast

end
