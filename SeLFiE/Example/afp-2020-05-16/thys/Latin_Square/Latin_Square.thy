(*  Title:       Latin Squares
    Author:      Alexander Bentkamp <bentkamp at gmail.com>, 2015
    Maintainer:  Alexander Bentkamp <bentkamp at gmail.com>
*)

theory Latin_Square
imports Marriage.Marriage
begin

text \<open>
  This theory is about Latin Squares. A Latin Square is a $n \times n$ table filled with
  integers from 1 to n where each number appears exactly once in each row and each column.

  As described in "Das Buch der Beweise" a nice way to describe these squares by a $3 \times n$ matrix.
  Each column of this matrix contains the index of the row r, the index of the column c and the
  number in the cell (r,c). This $3 \times n$ matrix is called orthogonal array ("Zeilenmatrix").

  I thought about different ways to formalize this orthogonal array, and came up with this:
  As the order of the columns in the array does not matter at all and no column can be a
  duplicate of another column, the orthogonal array is in fact a set of 3-tuples. Another
  advantage of formalizing it as a set is that it can easily model partially filled squares.
  For these 3-tuples I decided against 3-lists and against $nat \times nat \times nat$
  (which is really $(nat \times nat) \times nat$) in favor of
  a function from a type with three elements to nat.

  Additionally I use the numbers $0$ to $n-1$ instead of $1$ to $n$ for indexing the rows and columns as
  well as for filling the cells.
\<close>

datatype latin_type = Row | Col | Num

text\<open>latin\_type is of sort enum, needed for "value" command\<close>
instantiation latin_type :: enum
begin
  definition "enum_latin_type == [Row, Col, Num]"
  definition "enum_all_latin_type (P:: latin_type \<Rightarrow> bool) = (P Row \<and> P Col \<and> P Num)"
  definition "enum_ex_latin_type (P:: latin_type \<Rightarrow> bool) = (\<exists>x. P x)"

instance
  apply standard
     apply (auto simp add: enum_latin_type_def enum_all_latin_type_def enum_ex_latin_type_def)
   apply (case_tac x,auto)
by (metis latin_type.exhaust)

end


text\<open>Given a latin\_type t, you might want to reference the other two.
   These are "next t" and "next (next t)":\<close>
definition [simp]:"next t \<equiv> (case t of Row \<Rightarrow> Col | Col \<Rightarrow> Num | Num \<Rightarrow> Row)"

lemma all_types_next_eqiv:"(\<forall>t. P (next t)) \<longleftrightarrow> (\<forall>t. P t)"
  apply (rule iffI)
   using next_def latin_type.case latin_type.exhaust apply metis
  apply metis
done

text \<open>We call a column of the orthogonal array a latin\_entry:\<close>
type_synonym latin_entry = "latin_type \<Rightarrow> nat"

text \<open>This function removes one element of the 3-tupel and returns the other two as a pair:\<close>
definition without :: "latin_type \<Rightarrow> latin_entry \<Rightarrow> nat \<times> nat" where
[simp]:"without t \<equiv> \<lambda>e. (e (next t), e (next (next t)))"

value "without Row (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 1 | Num \<Rightarrow> 2)" \<comment> \<open>returns (1,2)\<close>

abbreviation "row_col \<equiv> without Num" text \<open>returns row and column of a latin\_entry as a pair.\<close>
abbreviation "col_num \<equiv> without Row" text \<open>returns column and number of a latin\_entry as a pair.\<close>
abbreviation "num_row \<equiv> without Col" text \<open>returns number and row of a latin\_entry as a pair.\<close>

text\<open>A partial latin square is a square that contains each number at most once in each row and each
   column, but not all cells have to be filled. Equivalently we can say that any two rows of the
   orthogonal array contain each pair of two numbers at most once. This can be expressed using the
   inj\_on predicate:\<close>
definition partial_latin_square :: "latin_entry set \<Rightarrow> nat \<Rightarrow> bool" where
"partial_latin_square s n \<equiv>
  (\<forall>t. inj_on (without t) s) \<and> \<comment> \<open>numbers are unique in each column (t=Row), numbers are unique in each row (t=Col), rows-column combinations are specified unambiguously (t=Num)\<close>
  (\<forall>e\<in>s. \<forall>t. e t < n) \<comment> \<open>all numbers, column indices and row indices are <n\<close>"

value "partial_latin_square {
  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 1 | Num \<Rightarrow> 0),
  (\<lambda>t. case t of Row \<Rightarrow> 1 | Col \<Rightarrow> 0 | Num \<Rightarrow> 1)
} 2" \<comment> \<open>True\<close>

value "partial_latin_square {
  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 0 | Num \<Rightarrow> 1),
  (\<lambda>t. case t of Row \<Rightarrow> 1 | Col \<Rightarrow> 0 | Num \<Rightarrow> 1)
} 2" \<comment> \<open>False, because 1 appears twice in column 0\<close>

text \<open>Looking at the orthogonal array a latin square is given iff any two rows of the
   orthogonal array contain each pair of two numbers at exactly once:\<close>
definition latin_square :: "latin_entry set \<Rightarrow> nat \<Rightarrow> bool" where
"latin_square s n \<equiv>
  (\<forall>t. bij_betw (without t) s ({0..<n}\<times>{0..<n}))" (* numbers exactly once in each column (t=Row), numbers exactly once in each row (t=Col), rows-column combinations are specified exactly once (t=Num) *)

value "latin_square {
  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 0 | Num \<Rightarrow> 1),  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 1 | Num \<Rightarrow> 0),
  (\<lambda>t. case t of Row \<Rightarrow> 1 | Col \<Rightarrow> 0 | Num \<Rightarrow> 0),  (\<lambda>t. case t of Row \<Rightarrow> 1 | Col \<Rightarrow> 1 | Num \<Rightarrow> 1)
} 2" \<comment> \<open>True\<close>

value "latin_square {
  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 0 | Num \<Rightarrow> 1),  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 1 | Num \<Rightarrow> 0),
  (\<lambda>t. case t of Row \<Rightarrow> 1 | Col \<Rightarrow> 0 | Num \<Rightarrow> 0),  (\<lambda>t. case t of Row \<Rightarrow> 1 | Col \<Rightarrow> 1 | Num \<Rightarrow> 0)
} 2" \<comment> \<open>False, because 0 appears twice in Col 1 and twice in Row 1\<close>

text \<open>A latin rectangle is a partial latin square in which the first m rows are filled and the following
   rows are empty:\<close>
definition latin_rect :: "latin_entry set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"latin_rect s m n \<equiv>
  m \<le> n \<and>
  partial_latin_square s n \<and>
  bij_betw row_col s ({0..<m}\<times>{0..<n}) \<and>
  bij_betw num_row s ({0..<n}\<times>{0..<m})"

value "latin_rect {
  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 0 | Num \<Rightarrow> 1),  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 1 | Num \<Rightarrow> 0)
} 1 2" \<comment> \<open>True\<close>

value "latin_rect {
  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 0 | Num \<Rightarrow> 1),  (\<lambda>t. case t of Row \<Rightarrow> 0 | Col \<Rightarrow> 1 | Num \<Rightarrow> 0),
  (\<lambda>t. case t of Row \<Rightarrow> 1 | Col \<Rightarrow> 0 | Num \<Rightarrow> 0),  (\<lambda>t. case t of Row \<Rightarrow> 1 | Col \<Rightarrow> 1 | Num \<Rightarrow> 1)
} 1 2" \<comment> \<open>False\<close>

text \<open>There is another equivalent description of latin rectangles, which is easier to prove:\<close>
lemma latin_rect_iff:
"m\<le>n \<and> partial_latin_square s n \<and> card s = n*m \<and> (\<forall>e\<in>s. e Row < m) \<longleftrightarrow> latin_rect s m n"
proof (rule iffI)
  assume prems:"m\<le>n \<and> partial_latin_square s n \<and> card s = n * m \<and> (\<forall>e\<in>s. e Row < m)"

  have bij1:"bij_betw row_col s ({0..<m}\<times>{0..<n})" using prems
  proof
    have "inj_on row_col s" using prems partial_latin_square_def by blast
    moreover have "{0..<m} \<times> {0..<n} = row_col ` s"
    proof-
      have "row_col ` s \<subseteq> {0..<m} \<times> {0..<n}" using prems partial_latin_square_def by auto
      moreover have "card (row_col ` s) = card ({0..<m} \<times> {0..<n})" using prems card_image[OF \<open>inj_on row_col s\<close>] by auto
      ultimately show "{0..<m} \<times> {0..<n} = row_col ` s" using card_subset_eq[of "{0..<m} \<times> {0..<n}" "row_col ` s"] by auto
    qed
    ultimately show ?thesis unfolding bij_betw_def by auto
  qed

  have bij2:"bij_betw num_row s ({0..<n}\<times>{0..<m})" using prems
  proof
    have "inj_on num_row s" using prems partial_latin_square_def by blast
    moreover have "{0..<n} \<times> {0..<m} = num_row ` s"
    proof-
      have "num_row ` s \<subseteq> {0..<n} \<times> {0..<m}" using prems partial_latin_square_def by auto
      moreover have "card (num_row ` s) = card ({0..<n} \<times> {0..<m})" using prems card_image[OF \<open>inj_on num_row s\<close>] by auto
      ultimately show "{0..<n} \<times> {0..<m} = num_row ` s" using card_subset_eq[of "{0..<n} \<times> {0..<m}" "num_row ` s"] by auto
    qed
    ultimately show ?thesis unfolding bij_betw_def by auto
  qed

  from prems bij1 bij2 show "latin_rect s m n" unfolding latin_rect_def by auto
next
  assume prems:"latin_rect s m n"
  have "m\<le>n" "partial_latin_square s n" using latin_rect_def prems by auto
  moreover have "card s = m * n"
  proof -
    have "bij_betw row_col s ({0..<m} \<times> {0..<n})" using latin_rect_def prems by auto
    then show ?thesis using bij_betw_same_card[of row_col s "{0..<m} \<times> {0..<n}"] by auto
  qed
  moreover have "\<forall>e\<in>s. e Row < m" using latin_rect_def prems using atLeast0LessThan bij_betwE by fastforce
  ultimately show "m\<le>n \<and> partial_latin_square s n \<and> card s = n * m \<and> (\<forall>e\<in>s. e Row < m)" by auto
qed

text \<open>A square is a latin square iff it is a partial latin square with all $n^2$ cells filled:\<close>
lemma partial_latin_square_full:
"partial_latin_square s n \<and> card s = n*n \<longleftrightarrow> latin_square s n"
proof (rule iffI)
  assume prem: "partial_latin_square s n \<and> card s = n * n"
  have "\<forall>t. (without t) ` s \<subseteq> {0..<n} \<times> {0..<n}"
  proof
    fix t show "(without t) ` s \<subseteq> {0..<n} \<times> {0..<n}" using partial_latin_square_def next_def atLeast0LessThan prem by (cases t) auto
  qed
  then show "partial_latin_square s n \<and> card s = n * n \<Longrightarrow> latin_square s n"
    unfolding latin_square_def using partial_latin_square_def
    by (metis bij_betw_def card_atLeastLessThan card_cartesian_product card_image card_subset_eq diff_zero finite_SigmaI finite_atLeastLessThan)
next
  assume prem:"latin_square s n"
  then have "bij_betw row_col s ({0..<n} \<times> {0..<n})" using latin_square_def by blast
  moreover have "partial_latin_square s n"
  proof -
    have "\<forall>t. \<forall>e\<in>s. (without t) e \<in> ({0..<n}\<times>{0..<n})" using prem latin_square_def bij_betwE by metis
    then have 1:"\<forall>e\<in>s.\<forall>t. e t < n" using latin_square_def all_types_next_eqiv[of "\<lambda>t. \<forall>e\<in>s. e t < n"] bij_betwE by auto
    have 2:"(\<forall>t. inj_on (without t) s)" using prem bij_betw_def latin_square_def by auto
    from 1 2 show ?thesis using partial_latin_square_def by auto
  qed
  ultimately show "partial_latin_square s n \<and> card s = n*n" by (auto simp add:  bij_betw_same_card)
qed

text \<open>Now we prove Lemma 1 from chapter 27 in "Das Buch der Beweise". But first some lemmas, that prove
   very intuitive facts:\<close>

lemma bij_restrict:
assumes "bij_betw f A B" "\<forall>a\<in>A. P a \<longleftrightarrow> Q (f a)"
shows "bij_betw f {a\<in>A. P a} {b\<in>B. Q b}"
proof -
  have inj: "inj_on f {a\<in>A. P a}" using assms bij_betw_def by (metis (mono_tags, lifting) inj_onD inj_onI mem_Collect_eq)
  have surj1: "f ` {a\<in>A. P a} \<subseteq> {b\<in>B. Q b}" using assms(1) assms(2) bij_betwE by blast
  have surj2: "{b\<in>B. Q b} \<subseteq> f ` {a\<in>A. P a}"
  proof
    fix b
    assume "b \<in> {b \<in> B. Q b}"
    then obtain a where "f a = b" "a\<in>A" using assms(1) bij_betw_inv_into_right bij_betwE bij_betw_inv_into mem_Collect_eq by (metis (no_types, lifting))
    then show "b \<in> f ` {a\<in>A. P a}" using \<open>b \<in> {b \<in> B. Q b}\<close> assms(2) by blast
  qed
  with inj surj1 surj2 show ?thesis using bij_betw_imageI by fastforce
qed

lemma cartesian_product_margin1:
assumes "a\<in>A"
shows "{p\<in>A\<times>B. fst p = a} = {a}\<times>B"
using SigmaI assms by auto

lemma cartesian_product_margin2:
assumes "b\<in>B"
shows "{p\<in>A\<times>B. snd p = b} = A\<times>{b}"
using SigmaI assms by auto

text \<open>The union of sets containing at most k elements each cannot contain more elements than
   the number of sets times k:\<close>
lemma limited_family_union: "finite B \<Longrightarrow> \<forall>P\<in>B. card P \<le> k \<Longrightarrow> card (\<Union>B) \<le> card B * k"
proof (induction B rule:finite_induct)
  case empty
  then show ?case by auto
next
  case (insert P B)
  have "card (\<Union>(insert P B)) \<le> card P + card (\<Union>B)" by (simp add: card_Un_le)
  then have "card (\<Union>(insert P B)) \<le> card P + card B * k" using insert by auto
  then show ?case using insert by simp
qed

text \<open>If f hits each element at most k times, the domain of f can only be k times bigger than the
   image of f:\<close>
lemma limited_preimages:
assumes "\<forall>x \<in> f ` D. card ((f -` {x})\<inter>D) \<le> k" "finite D"
shows "card D \<le> card (f ` D) * k "
proof -
  let ?preimages = "(\<lambda>x. (f -` {x})\<inter>D) ` (f ` D)"
  have "D = \<Union>?preimages" by auto
  have "card (\<Union>?preimages) \<le> card ?preimages * k" using limited_family_union[of "?preimages" k] assms by auto
  moreover have "card (?preimages) * k \<le> card (f ` D) * k" using card_image_le[of "f ` D" "\<lambda>x. (f -` {x})\<inter>D"] assms by auto
  ultimately have "card (\<Union>?preimages) \<le> card (f ` D) * k" using le_trans by blast
  then show ?thesis using \<open>D = \<Union>?preimages\<close> by metis
qed

text \<open>Let $A_1, \dots, A_n$ be sets with $k>0$ elements each. Any element is only contained in at most $k$ of
   these sets. Then there are more different elements in total than sets $A_i$:\<close>
lemma union_limited_replicates:
assumes "finite I" "\<forall>i\<in>I. finite (A i)" "k>0" "\<forall>i\<in>I. card (A i) = k" "\<forall>i\<in>I. \<forall>x\<in>(A i). card {i\<in>I. x\<in>A i} \<le> k"
shows "card (\<Union>i\<in>I. (A i)) \<ge> card I" using assms
proof -
  let ?pairs = "{(i,x). i\<in>I \<and> x\<in>A i}"

  have card_pairs: "card ?pairs = card I * k" using assms
  proof (induction I rule:finite_induct)
    case empty
    then show ?case using card_eq_0_iff by auto
  next
    case (insert i0 I)
    have "\<forall>i\<in>I. \<forall>x\<in>(A i). card {i\<in>I. x\<in>A i} \<le> k"
    proof (rule ballI)+
      fix i x assume "i \<in> I" "x\<in>A i"
      then have "card {i \<in> insert i0 I. x \<in> A i} \<le> k" using insert by auto
      moreover have "finite {i \<in> insert i0 I. x \<in> A i}" using insert by auto
      ultimately show "card  {i\<in>I. x\<in>A i} \<le> k" using card_mono[of "{i \<in> insert i0 I. x \<in> A i}" "{i \<in> I. x \<in> A i}"] le_trans by blast
    qed
    then have card_S: "card {(i, x). i \<in> I \<and> x \<in> A i} = card I * k" using insert by auto

    have card_B: "card {(i, x). i=i0 \<and> x\<in>A i0} = k" using insert by auto

    have "{(i, x). i \<in> insert i0 I \<and> x \<in> A i} = {(i, x). i \<in> I \<and> x \<in> A i} \<union> {(i, x). i=i0 \<and> x\<in>A i0}" by auto
    moreover have "{(i, x). i \<in> I \<and> x \<in> A i} \<inter> {(i, x). i=i0 \<and> x\<in>A i0} = {}" using insert by auto
    moreover have "finite {(i, x). i \<in> I \<and> x \<in> A i}" using insert rev_finite_subset[of "I \<times> \<Union>(A ` I)" "{(i, x). i \<in> I \<and> x \<in> A i}"] by auto
    moreover have "finite {(i, x). i=i0 \<and> x\<in>A i0}" using insert card_B card_infinite neq0_conv by blast
    ultimately have "card {(i, x). i \<in> insert i0 I \<and> x \<in> A i} = card {(i, x). i \<in> I \<and> x \<in> A i} + card {(i, x). i=i0 \<and> x\<in>A i0}" by (simp add: card_Un_disjoint)
    with card_S card_B have "card {(i, x). i \<in> insert i0 I \<and> x \<in> A i} = (card I + 1) * k" by auto
    then show ?case using insert by auto
  qed

  define f where "f ix = (case ix of (i,x) \<Rightarrow> x)" for ix :: "'a \<times> 'b"

  have preimages_le_k: "\<forall>x \<in> f ` ?pairs. card ((f -` {x}) \<inter> ?pairs) \<le> k"
  proof
    fix x0 assume x0_def: "x0 \<in> f ` ?pairs"
    have "(f -` {x0}) \<inter> ?pairs = {(i,x). i\<in>I \<and> x\<in>A i \<and> x=x0}" using f_def by auto
    moreover have "card {(i,x). i\<in>I \<and> x\<in>A i \<and> x=x0} = card {i\<in>I. x0\<in>A i}" using \<open>finite I\<close>
    proof -
      have "inj_on (\<lambda>i. (i,x0)) {i\<in>I. x0\<in>A i}" by (meson Pair_inject inj_onI)
      moreover have "(\<lambda>i. (i,x0)) ` {i\<in>I. x0\<in>A i} = {(i,x). i\<in>I \<and> x\<in>A i \<and> x=x0}" by (rule subset_antisym) blast+
      ultimately show ?thesis using card_image by fastforce
    qed
    ultimately have 1:"card ((f -` {x0}) \<inter> ?pairs) = card  {i\<in>I. x0\<in>A i}" by auto

    have"\<exists>i0. x0\<in>A i0 \<and> i0\<in>I" using x0_def f_def by auto
    then have "card {i\<in>I. x0\<in>A i} \<le> k" using assms by auto
    with 1 show "card ((f -` {x0}) \<inter> ?pairs) \<le> k" by auto
  qed

  have "card ?pairs \<le> card (f ` ?pairs) * k"
  proof -
    have "finite {(i, x). i \<in> I \<and> x \<in> A i}" using assms card_pairs not_finite_existsD by fastforce
    then show ?thesis using limited_preimages[of f ?pairs k, OF preimages_le_k] by auto
  qed

  then have "card I  \<le> card (f ` ?pairs) " using card_pairs assms by auto
  moreover have "f ` ?pairs = (\<Union>i\<in>I. (A i))" using f_def [abs_def] by auto
  ultimately show ?thesis using f_def by auto
qed

text \<open>In a $m \times n$ latin rectangle each number appears in m columns:\<close>
lemma latin_rect_card_col:
assumes "latin_rect s m n" "x<n"
shows "card {e Col|e. e\<in>s \<and> e Num = x} = m"
proof -
  have "card {e \<in> s. e Num = x} = m"
  proof -
    have 1:"bij_betw num_row s ({0..<n}\<times>{0..<m})" using assms latin_rect_def by auto
    have 2:"\<forall>e\<in>s. e Num = x \<longleftrightarrow> fst (num_row e) = x" by simp
    have "bij_betw num_row {e\<in>s. e Num = x} ({x}\<times>{0..<m})"
      using bij_restrict[OF 1 2] cartesian_product_margin1[of x "{0..<n}" " {0..<m}"] assms by auto
    then show ?thesis using card_cartesian_product by (simp add: bij_betw_same_card)
  qed
  moreover have "card {e\<in>s. e Num = x} = card {e Col |e. e \<in> s \<and> e Num = x}"
  proof -
    have "inj_on col_num s" using assms latin_rect_def[of s m n] partial_latin_square_def[of s n] by blast
    then have "inj_on col_num {e\<in>s. e Num = x}" by (metis (mono_tags, lifting) inj_onD inj_onI mem_Collect_eq)
    then have "inj_on (\<lambda>e. e Col) {e\<in>s. e Num = x}" unfolding inj_on_def using without_def by auto
    moreover have "(\<lambda>e. e Col) ` {e\<in>s. e Num = x} = {e Col |e. e \<in> s \<and> e Num = x}" by (rule subset_antisym) blast+
    ultimately show ?thesis using card_image by fastforce
  qed
  ultimately show ?thesis by auto
qed

text \<open>In a $m \times n$ latin rectangle each column contains m numbers:\<close>
lemma latin_rect_card_num:
assumes "latin_rect s m n" "x<n"
shows "card {e Num|e. e\<in>s \<and> e Col = x} = m"
proof -
  have "card {e \<in> s. e Col = x} = m"
  proof -
    have 1:"bij_betw row_col s ({0..<m}\<times>{0..<n})" using assms latin_rect_def by auto
    have 2:"\<forall>e\<in>s. e Col = x \<longleftrightarrow> snd (row_col e) = x" by simp
    have "bij_betw row_col {e\<in>s. e Col = x} ({0..<m}\<times>{x})"
      using bij_restrict[OF 1 2] cartesian_product_margin2[of x "{0..<n}" " {0..<m}"] assms by auto
    then show ?thesis using card_cartesian_product by (simp add: bij_betw_same_card)
  qed
  moreover have "card {e\<in>s. e Col = x} = card {e Num |e. e \<in> s \<and> e Col = x}"
  proof -
    have "inj_on col_num s" using assms latin_rect_def[of s m n] partial_latin_square_def[of s n] by blast
    then have "inj_on col_num {e\<in>s. e Col = x}" by (metis (mono_tags, lifting) inj_onD inj_onI mem_Collect_eq)
    then have "inj_on (\<lambda>e. e Num) {e\<in>s. e Col = x}" unfolding inj_on_def using without_def by auto
    moreover have "(\<lambda>e. e Num) ` {e\<in>s. e Col = x} = {e Num |e. e \<in> s \<and> e Col = x}" by (rule subset_antisym) blast+
    ultimately show ?thesis using card_image by fastforce
  qed
  ultimately show ?thesis by auto
qed

text \<open>Finally we prove lemma 1 chapter 27 of "Das Buch der Beweise":\<close>
theorem
  assumes "latin_rect s (n-m) n" "m\<le>n"
  shows "\<exists>s'. s\<subseteq>s' \<and> latin_square s' n"
using assms
proof (induction m arbitrary:s) \<comment> \<open>induction over the number of empty rows\<close>
  case 0
  then have "bij_betw row_col s ({0..<n} \<times> {0..<n})" using latin_rect_def by auto
  then have "card s = n*n" by (simp add:bij_betw_same_card)
  then show ?case using partial_latin_square_full 0 latin_rect_def by auto
next
  case (Suc m)

  \<comment> \<open>We use the Hall theorem on the sets $A_j$ of numbers that do not occur in column $j$:\<close>
  let ?not_in_column = "\<lambda>j. {0..<n} - {e Num |e. e\<in>s \<and> e Col = j}"

  \<comment> \<open>Proof of the hall condition:\<close>
  have "\<forall>J\<subseteq>{0..<n}. card J \<le> card (\<Union>j\<in>J. ?not_in_column j)"
  proof (rule allI; rule impI)
    fix J assume J_def:"J\<subseteq>{0..<n}"
    have "\<forall>j\<in>J. card (?not_in_column j) = Suc m"
    proof
      fix j assume j_def:"j\<in>J"
      have "{e Num |e. e\<in>s \<and> e Col = j} \<subseteq> {0..<n}" using atLeastLessThan_iff Suc latin_rect_def partial_latin_square_def by auto
      moreover then have "finite {e Num |e. e\<in>s \<and> e Col = j}" using finite_subset by auto
      ultimately have "card (?not_in_column j) = card {0..<n} - card {e Num |e. e \<in> s \<and> e Col = j}" using card_Diff_subset[of "{e Num |e. e\<in>s \<and> e Col = j}" "{0..<n}"] by auto
      then show "card(?not_in_column j) = Suc m" using latin_rect_card_num J_def j_def Suc by auto
    qed
    moreover have "\<forall>j0\<in>J. \<forall>x\<in>?not_in_column j0. card {j \<in> J. x \<in> ?not_in_column j} \<le> Suc m"
    proof (rule ballI; rule ballI)
      fix j0 x assume "j0 \<in> J" "x \<in> ?not_in_column j0"
      then have "card ({0..<n} - {e Col|e. e\<in>s \<and> e Num = x}) = Suc m"
      proof -
        have "card {e Col|e. e\<in>s \<and> e Num = x} = n - Suc m" using latin_rect_card_col \<open>x \<in> ?not_in_column j0\<close> Suc by auto
        moreover have "{e Col|e. e\<in>s \<and> e Num = x}\<subseteq>{0..<n}" using Suc latin_rect_def partial_latin_square_def by auto
        moreover then have "finite {e Col|e. e\<in>s \<and> e Num = x}" using finite_subset by auto
        ultimately show ?thesis using card_Diff_subset[of "{e Col|e. e\<in>s \<and> e Num = x}" "{0..<n}"] using Suc.prems by auto
      qed
      moreover have "{j \<in> J. x \<in> ?not_in_column j} \<subseteq> {0..<n} - {e Col|e. e\<in>s \<and> e Num = x}" using Diff_mono J_def using \<open>x \<in> ?not_in_column j0\<close> by blast
      ultimately show "card {j \<in> J. x \<in> ?not_in_column j} \<le> Suc m" by (metis (no_types, lifting) card_mono finite_Diff finite_atLeastLessThan)
    qed
    moreover have "finite J" using J_def finite_subset by auto
    ultimately show "card J \<le> card (\<Union>j\<in>J. ?not_in_column j)" using union_limited_replicates[of J ?not_in_column "Suc m"] by auto
  qed

  \<comment> \<open>The Hall theorem gives us a system of distinct representatives, which we can use to fill the next row:\<close>
  then obtain R where R_def:"\<forall>j\<in>{0..<n}. R j \<in> ?not_in_column j \<and> inj_on R {0..<n}" using marriage_HV[of "{0..<n}" "?not_in_column"] by blast

  define new_row where "new_row = (\<lambda>j. rec_latin_type (n - Suc m) j (R j)) ` {0..<n}"
  define s' where "s' = s \<union> new_row"

  \<comment> \<open>s' is now a latin rect with one more row:\<close>
  have "latin_rect s' (n-m) n"
  proof -
    \<comment> \<open>We prove all four criteria specified in the lemma latinrectiff:\<close>
    have "n-m \<le> n" by auto
    moreover have "partial_latin_square s' n"
    proof -
      have "inj_on (without Col) s'" unfolding inj_on_def
      proof (rule ballI; rule ballI; rule impI)
        fix e1 e2 assume "e1 \<in> s'" "e2 \<in> s'" "num_row e1 = num_row e2"
        then have "e1 Num = e2 Num" "e1 Row = e2 Row" using without_def by auto
        moreover have "e1 Col = e2 Col"
        proof (cases)
          assume "e1 Row = n - Suc m"
          then have "e2 Row = n - Suc m" using without_def \<open>num_row e1 = num_row e2\<close> by auto
          have "\<forall>e\<in>s. e Row < n - Suc m" using Suc latin_rect_iff by blast
          then have "e1 \<in> new_row" "e2 \<in> new_row"  using s'_def \<open>e1 \<in> s'\<close> \<open>e2 \<in> s'\<close> \<open>e1 Row = n - Suc m\<close> \<open>e2 Row = n - Suc m\<close> by auto
          then have "e1 Num = R (e1 Col)" "e2 Num = R (e2 Col)" using new_row_def by auto
          then have "R (e1 Col) = R (e2 Col)" using \<open>e1 Num = e2 Num\<close> by auto
          moreover have "e1 Col < n" "e2 Col < n" using \<open>e1 \<in> new_row\<close> \<open>e2 \<in> new_row\<close> new_row_def by auto
          ultimately show "e1 Col = e2 Col" using R_def inj_on_def by (metis (mono_tags, lifting) atLeast0LessThan lessThan_iff)
        next
          assume "e1 Row \<noteq> n - Suc m"
          then have "e1\<in>s" "e2\<in>s" using new_row_def s'_def \<open>e1\<in>s'\<close> \<open>e2\<in>s'\<close> \<open>e1 Row = e2 Row\<close> by auto
          then show "e1 Col = e2 Col" using Suc latin_rect_def bij_betw_def by (metis \<open>num_row e1 = num_row e2\<close> inj_onD)
        qed
        ultimately show "e1=e2" using latin_type.induct[of "\<lambda>t. e1 t = e2 t"] by auto
      qed
      moreover have "inj_on (without Row) s'" unfolding inj_on_def
      proof (rule ballI; rule ballI; rule impI)
        fix e1 e2 assume "e1 \<in> s'" "e2 \<in> s'" "col_num e1 = col_num e2"
        then have "e1 Col = e2 Col" "e1 Num = e2 Num" using without_def by auto
        moreover have "e1 Row = e2 Row"
        proof (cases)
          assume "e1 Row = n - Suc m"
          have "\<forall>e\<in>s. e Row < n - Suc m" using Suc latin_rect_iff by blast
          then have "e2 Num \<in> ?not_in_column (e2 Col)" using R_def new_row_def \<open>e1 Col = e2 Col\<close> \<open>e1 Num = e2 Num\<close> using s'_def \<open>e1 \<in> s'\<close> \<open>e1 Row = n - Suc m\<close> by auto
          then show "e1 Row = e2 Row" using new_row_def \<open>e1 Row = n - Suc m\<close>  s'_def \<open>e2 \<in> s'\<close> by auto
        next
          assume "e1 Row \<noteq> n - Suc m"
          then have "e1\<in>s" using new_row_def s'_def \<open>e1\<in>s'\<close> by auto
          then have "e2 Num \<notin> ?not_in_column (e2 Col)" using \<open>e1 Col = e2 Col\<close> \<open>e1 Num = e2 Num\<close> by auto
          then have "e2\<in>s" using new_row_def s'_def \<open>e2\<in>s'\<close> R_def by auto
          moreover have "inj_on col_num s" using Suc.prems latin_rect_def[of s "(n - Suc m)" n] partial_latin_square_def[of s n] by blast
          ultimately show "e1 Row = e2 Row" using Suc latin_rect_def by (metis \<open>col_num e1 = col_num e2\<close> \<open>e1 \<in> s\<close> inj_onD)
        qed
        ultimately show "e1=e2" using latin_type.induct[of "\<lambda>t. e1 t = e2 t"] by auto
      qed
      moreover have "inj_on (without Num) s'" unfolding inj_on_def
      proof (rule ballI; rule ballI; rule impI)
        fix e1 e2 assume "e1 \<in> s'" "e2 \<in> s'" "row_col e1 = row_col e2"
        then have "e1 Row = e2 Row" "e1 Col = e2 Col" using without_def by auto
        moreover have "e1 Num = e2 Num"
        proof (cases)
          assume "e1 Row = n - Suc m"
          then have "e2 Row = n - Suc m" using without_def \<open>row_col e1 = row_col e2\<close> by auto
          have "\<forall>e\<in>s. e Row < n - Suc m" using Suc latin_rect_iff by blast
          then show "e1 Num = e2 Num" using \<open>e1 Col = e2 Col\<close> using new_row_def s'_def \<open>e1 \<in> s'\<close> \<open>e2 \<in> s'\<close> \<open>e1 Row = n - Suc m\<close> \<open>e2 Row = n - Suc m\<close> by auto
        next
          assume "e1 Row \<noteq> n - Suc m"
          then have "e1\<in>s" "e2\<in>s" using new_row_def s'_def \<open>e1\<in>s'\<close> \<open>e2\<in>s'\<close> \<open>e1 Row = e2 Row\<close> by auto
          then show "e1 Num = e2 Num" using Suc latin_rect_def bij_betw_def by (metis \<open>row_col e1 = row_col e2\<close> inj_onD)
        qed
        ultimately show "e1=e2" using latin_type.induct[of "\<lambda>t. e1 t = e2 t"] by auto
      qed
      moreover have "\<forall>e\<in>s'. \<forall>t. e t < n"
      proof (rule ballI; rule allI)
        fix e t assume "e\<in>s'"
        then show "e t < n"
        proof (cases)
          assume "e\<in>new_row"
          then show ?thesis using new_row_def R_def by (induction t) auto
        next
          assume "e\<notin>new_row"
          then show ?thesis using s'_def \<open>e\<in>s'\<close> latin_rect_def partial_latin_square_def Suc by auto
        qed
      qed
      ultimately show "partial_latin_square s' n" unfolding partial_latin_square_def using latin_type.induct[of "\<lambda>t. inj_on (without t) s'"] by auto
    qed
    moreover have "card s' = n * (n - m)"
    proof -
      have card_s:"card s = n * (n - Suc m)" using latin_rect_iff Suc by auto
      have card_new_row:"card new_row = n" unfolding new_row_def
      proof -
        have "inj_on (\<lambda>j. rec_latin_type (n - Suc m) j (R j)) {0..<n}" unfolding inj_on_def
        proof (rule ballI; rule ballI; rule impI)
          fix j1 j2 assume "j1 \<in> {0..<n}" "j2 \<in> {0..<n}" "rec_latin_type (n - Suc m) j1 (R j1) = rec_latin_type (n - Suc m) j2 (R j2)"
          then show  "j1 = j2" using latin_type.rec(2)[of "(n - Suc m)" j1 "R j1"] latin_type.rec(2)[of _ j2 _] by auto
        qed
        then show "card ((\<lambda>j. rec_latin_type (n - Suc m) j (R j)) ` {0..<n}) = n" by (simp add: card_image)
      qed
      have "s \<inter> new_row = {}"
      proof -
        have "\<forall>e\<in>s. e Row < n - Suc m" using Suc latin_rect_iff by blast
        then have "\<forall>e \<in> new_row. e \<notin> s" using new_row_def by auto
        then show ?thesis by blast
      qed
      moreover have "finite s" using Suc latin_rect_def by (metis bij_betw_finite finite_SigmaI finite_atLeastLessThan)
      moreover have "finite new_row" using new_row_def by simp
      ultimately have "card s' = card s + card new_row" using s'_def card_Un_disjoint by auto
      with card_s card_new_row show ?thesis using Suc by (metis Suc_diff_Suc Suc_le_lessD add.commute mult_Suc_right)
    qed
    moreover have "\<forall>e\<in>s'. e Row < (n - m)"
    proof (rule ballI; cases)
      fix e
      assume "e\<in>new_row"
      then show "e Row < n - m" using Suc new_row_def R_def by auto
    next
      fix e
      assume "e \<in> s'" "e\<notin>new_row"
      then have "e Row < n - Suc m"  using latin_rect_iff Suc  s'_def \<open>e\<in>s'\<close> by auto
      then show "e Row < n - m" by auto
    qed
    ultimately show ?thesis using latin_rect_iff[of "n-m" n] by auto
  qed

  \<comment> \<open>Finally we use the induction hypothesis:\<close>
  then obtain s'' where "s' \<subseteq> s''" "latin_square s'' n" using Suc by auto
  then have "s \<subseteq> s''" using s'_def by auto
  then show "\<exists>s'. s \<subseteq> s' \<and> latin_square s' n" using \<open>latin_square s'' n\<close> by auto
qed

end
