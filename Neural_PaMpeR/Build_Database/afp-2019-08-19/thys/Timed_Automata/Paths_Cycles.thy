theory Paths_Cycles
  imports Floyd_Warshall Timed_Automata
begin

chapter \<open>Library for Paths, Arcs and Lengths\<close>

lemma length_eq_distinct:
  assumes "set xs = set ys" "distinct xs" "length xs = length ys"
  shows "distinct ys"
using assms card_distinct distinct_card by fastforce

section \<open>Arcs\<close>

fun arcs :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> (nat * nat) list" where
  "arcs a b [] = [(a,b)]" |
  "arcs a b (x # xs) = (a, x) # arcs x b xs"

definition arcs' :: "nat list \<Rightarrow> (nat * nat) set" where
  "arcs' xs = set (arcs (hd xs) (last xs) (butlast (tl xs)))"

lemma arcs'_decomp:
  "length xs > 1 \<Longrightarrow> (i, j) \<in> arcs' xs \<Longrightarrow> \<exists> zs ys. xs = zs @ i # j # ys"
proof (induction xs)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  then have "length xs > 0" by auto
  then obtain y ys where xs: "xs = y # ys" by (metis Suc_length_conv less_imp_Suc_add)
  show ?case
  proof (cases "(i, j) = (x, y)")
    case True
    with xs have "x # xs = [] @ i # j # ys" by simp
    then show ?thesis by auto
  next
    case False
    then show ?thesis
    proof (cases "length ys > 0", goal_cases)
      case 2
      then have "ys = []" by auto
      then have "arcs' (x#xs) = {(x,y)}" using xs by (auto simp add: arcs'_def)
      with Cons.prems(2) 2(1) show ?case by auto
    next
      case True
      with xs Cons.prems(2) False have "(i, j) \<in> arcs' xs" by (auto simp add: arcs'_def)
      with Cons.IH[OF _ this] True xs obtain zs ys where "xs = zs @ i # j # ys" by auto
      then have "x # xs = (x # zs) @ i # j # ys" by simp
      then show ?thesis by blast
    qed
  qed
qed

lemma arcs_decomp_tail:
  "arcs j l (ys @ [i]) = arcs j i ys @ [(i, l)]"
by (induction ys arbitrary: j) auto

lemma arcs_decomp: "xs = ys @ y # zs \<Longrightarrow> arcs x z xs = arcs x y ys @ arcs y z zs"
by (induction ys arbitrary: x xs) simp+

lemma distinct_arcs_ex:
  "distinct xs \<Longrightarrow> i \<notin> set xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> \<exists> a b. a \<noteq> x \<and> (a,b) \<in> set (arcs i j xs)"
 apply (induction xs arbitrary: i)
  apply simp
 apply (rename_tac a xs i)
 apply (case_tac xs)
  apply simp
  apply metis
by auto

lemma cycle_rotate_2_aux:
  "(i, j) \<in> set (arcs a b (xs @ [c])) \<Longrightarrow> (i,j) \<noteq> (c,b) \<Longrightarrow> (i, j) \<in> set (arcs a c xs)"
by (induction xs arbitrary: a) auto

lemma arcs_set_elem1:
  assumes "j \<noteq> k" "k \<in> set (i # xs)"
  shows "\<exists> l. (k, l) \<in> set (arcs i j xs)" using assms
by (induction xs arbitrary: i) auto

lemma arcs_set_elem2:
  assumes "i \<noteq> k" "k \<in> set (j # xs)"
  shows "\<exists> l. (l, k) \<in> set (arcs i j xs)" using assms
proof (induction xs arbitrary: i)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases "k = x") auto
qed

section \<open>Length of Paths\<close>

lemmas (in linordered_ab_monoid_add) comm = add.commute

lemma len_add:
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  shows "len M i j xs + len M i j xs = len (\<lambda>i j. M i j + M i j) i j xs"
proof (induction xs arbitrary: i j)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  have "M i x + len M x j xs + (M i x + len M x j xs) = M i x + (len M x j xs + M i x) + len M x j xs"
  by (simp add: assoc)
  also have "\<dots> = M i x + (M i x + len M x j xs) + len M x j xs" by (simp add: comm)
  also have "\<dots> = (M i x + M i x) + (len M x j xs + len M x j xs)" by (simp add: assoc)
  finally have "M i x + len M x j xs + (M i x + len M x j xs)
                = (M i x + M i x) + len (\<lambda>i j. M i j + M i j) x j xs"
  using Cons by simp
  thus ?case by simp
qed

section \<open>Canonical Matrices\<close>

abbreviation
  "canonical M n \<equiv> \<forall> i j k. i \<le> n \<and> j \<le> n \<and> k \<le> n \<longrightarrow> M i k \<le> M i j + M j k"

lemma fw_canonical:
 "cycle_free m n \<Longrightarrow> canonical (fw m n n n n) n"
proof (clarify, goal_cases)
  case 1
  with fw_shortest[OF \<open>cycle_free m n\<close>] show ?case
  by auto
qed

lemma canonical_len:
  "canonical M n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..n} \<Longrightarrow> M i j \<le> len M i j xs"
proof (induction xs arbitrary: i)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  then have "M x j \<le> len M x j xs" by auto
  from Cons.prems \<open>canonical M n\<close> have "M i j \<le> M i x + M x j" by simp
  also with Cons have "\<dots> \<le> M i x + len M x j xs" by (simp add: add_mono)
  finally show ?case by simp
qed

section \<open>Cycle Rotation\<close>

lemma cycle_rotate:
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "length xs > 1" "(i, j) \<in> arcs' xs"
  shows "\<exists> ys zs. len M a a xs = len M i i (j # ys @ a # zs) \<and> xs = zs @ i # j # ys" using assms
proof -
  assume A: "length xs > 1" "(i, j) \<in> arcs' xs"
  from arcs'_decomp[OF this] obtain ys zs where xs: "xs = zs @ i # j # ys" by blast
  from len_decomp[OF this, of M a a]
  have "len M a a xs = len M a i zs + len M i a (j # ys)" .
  also have "\<dots> = len M i a (j # ys) + len M a i zs" by (simp add: comm)
  also from len_comp[of M i i "j # ys" a zs] have "\<dots> = len M i i (j # ys @ a # zs)" by auto
  finally show ?thesis using xs by auto
qed

lemma cycle_rotate_2:
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "xs \<noteq> []" "(i, j) \<in> set (arcs a a xs)"
  shows "\<exists> ys. len M a a xs = len M i i (j # ys) \<and> set ys \<subseteq> set (a # xs) \<and> length ys < length xs"
using assms proof -
  assume A:"xs \<noteq> []" "(i, j) \<in> set (arcs a a xs)"
  { fix ys assume A:"a = i" "xs = j # ys"
    then have ?thesis by auto
  } note * = this
  { fix b ys assume A:"a = j" "xs = ys @ [i]"
    then have ?thesis
    proof (auto, goal_cases)
      case 1
      have "len M j j (ys @ [i]) = M i j + len M j i ys"
      using len_decomp[of "ys @ [i]" ys i "[]" M j j] by (auto simp: comm)
      thus ?case by blast
    qed
  } note ** = this
  { assume "length xs = 1"
    then obtain b where xs: "xs = [b]" by (metis One_nat_def length_0_conv length_Suc_conv) 
    with A(2) have "a = i \<and> b = j \<or> a = j \<and> b = i" by auto
    then have ?thesis using * ** xs by auto
  } note *** = this
  show ?thesis
  proof (cases "length xs = 0")
    case True with A show ?thesis by auto
  next
    case False
    thus ?thesis
    proof (cases "length xs = 1", goal_cases)
      case True with *** show ?thesis by auto
    next
      case 2
      hence "length xs > 1" by linarith
      then obtain b c ys where ys:"xs = b # ys @ [c]"
      by (metis One_nat_def assms(1) 2(2) length_0_conv length_Cons list.exhaust rev_exhaust) 
      thus ?thesis
      proof (cases "(i,j) = (a,b)", goal_cases)
        case True
        with ys * show ?thesis by auto
      next
        case False
        then show ?thesis
        proof (cases "(i,j) = (c,a)", goal_cases)
          case True
          with ys ** show ?thesis by auto
        next
          case 2
          with A(2) ys have "(i, j) \<in> arcs' xs"
          using cycle_rotate_2_aux by (auto simp: arcs'_def) (* slow *)
          from cycle_rotate[OF \<open>length xs > 1\<close> this, of M a] show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma cycle_rotate_len_arcs:
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "length xs > 1" "(i, j) \<in> arcs' xs"
  shows "\<exists> ys zs. len M a a xs = len M i i (j # ys @ a # zs)
                \<and> set (arcs a a xs) = set (arcs i i (j # ys @ a # zs)) \<and> xs = zs @ i # j # ys"
using assms
proof -
  assume A: "length xs > 1" "(i, j) \<in> arcs' xs"
  from arcs'_decomp[OF this] obtain ys zs where xs: "xs = zs @ i # j # ys" by blast
  from len_decomp[OF this, of M a a]
  have "len M a a xs = len M a i zs + len M i a (j # ys)" .
  also have "\<dots> = len M i a (j # ys) + len M a i zs" by (simp add: comm)
  also from len_comp[of M i i "j # ys" a zs] have "\<dots> = len M i i (j # ys @ a # zs)" by auto
  finally show ?thesis
  using xs arcs_decomp[OF xs, of a a] arcs_decomp[of "j # ys @ a # zs" "j # ys" a zs i i] by force
qed

lemma cycle_rotate_2':
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "xs \<noteq> []" "(i, j) \<in> set (arcs a a xs)"
  shows "\<exists> ys. len M a a xs = len M i i (j # ys) \<and> set (i # j # ys) = set (a # xs)
             \<and> 1 + length ys = length xs \<and> set (arcs a a xs) = set (arcs i i (j # ys))"
proof -
  note A = assms
  { fix ys assume A:"a = i" "xs = j # ys"
    then have ?thesis by auto
  } note * = this
  { fix b ys assume A:"a = j" "xs = ys @ [i]"
    then have ?thesis
    proof (auto, goal_cases)
      case 1
      have "len M j j (ys @ [i]) = M i j + len M j i ys"
      using len_decomp[of "ys @ [i]" ys i "[]" M j j] by (auto simp: comm)
      moreover have "arcs j j (ys @ [i]) = arcs j i ys @ [(i, j)]" using arcs_decomp_tail by auto
      ultimately show ?case by auto
    qed
  } note ** = this
  { assume "length xs = 1"
    then obtain b where xs: "xs = [b]" by (metis One_nat_def length_0_conv length_Suc_conv) 
    with A(2) have "a = i \<and> b = j \<or> a = j \<and> b = i" by auto
    then have ?thesis using * ** xs by auto
  } note *** = this
  show ?thesis
  proof (cases "length xs = 0")
    case True with A show ?thesis by auto
  next
    case False
    thus ?thesis
    proof (cases "length xs = 1", goal_cases)
      case True with *** show ?thesis by auto
    next
      case 2
      hence "length xs > 1" by linarith
      then obtain b c ys where ys:"xs = b # ys @ [c]"
      by (metis One_nat_def assms(1) 2(2) length_0_conv length_Cons list.exhaust rev_exhaust) 
      thus ?thesis
      proof (cases "(i,j) = (a,b)")
        case True
        with ys * show ?thesis by blast
      next
        case False
        then show ?thesis
        proof (cases "(i,j) = (c,a)", goal_cases)
          case True
          with ys ** show ?thesis by force
        next
          case 2
          with A(2) ys have "(i, j) \<in> arcs' xs"
          using cycle_rotate_2_aux by (auto simp add: arcs'_def) (* slow *)
          from cycle_rotate_len_arcs[OF \<open>length xs > 1\<close> this, of M a] show ?thesis by auto
        qed
      qed
    qed
  qed
qed

section \<open>Equivalent Characterizations of Cycle-Freeness\<close>

lemma negative_cycle_dest_diag:
  "\<not> cycle_free M n \<Longrightarrow> \<exists> i xs. i \<le> n \<and> set xs \<subseteq> {0..n} \<and> len M i i xs < \<one>"
proof (auto simp: cycle_free_def, goal_cases)
  case (1 i xs j)
  from this(4) have "len M i j xs < len M i j (rem_cycles i j xs)" by auto
  from negative_cycle_dest[OF this] obtain i' ys
  where *:"len M i' i' ys < \<one>" "set (i' # ys) \<subseteq> set (i # j # xs)" by auto
  from this(2) 1(1-3) have "set ys \<subseteq> {0..n}" "i' \<le> n" by auto
  with * show ?case by auto
next
  case 2 then show ?case by fastforce
qed

abbreviation cyc_free :: "('a::linordered_ab_monoid_add) mat \<Rightarrow> nat \<Rightarrow> bool" where
  "cyc_free m n \<equiv> \<forall> i xs. i \<le> n \<and> set xs \<subseteq> {0..n} \<longrightarrow> len m i i xs \<ge> \<one>"

lemma cycle_free_diag_intro:
  "cyc_free M n \<Longrightarrow> cycle_free M n"
using negative_cycle_dest_diag by force

lemma cycle_free_diag_equiv:
  "cyc_free M n \<longleftrightarrow> cycle_free M n" using negative_cycle_dest_diag
by (force simp: cycle_free_def)

lemma cycle_free_diag_dest:
  "cycle_free M n \<Longrightarrow> cyc_free M n"
using cycle_free_diag_equiv by blast

lemma cyc_free_diag_dest:
  assumes "cyc_free M n" "i \<le> n" "set xs \<subseteq> {0..n}"
  shows "len M i i xs \<ge> \<one>"
using assms by auto

lemma cycle_free_0_0:
  fixes M :: "('a::linordered_ab_monoid_add) mat"
  assumes "cycle_free M n"
  shows "M 0 0 \<ge> \<one>"
using cyc_free_diag_dest[OF cycle_free_diag_dest[OF assms], of 0 "[]"] by auto

section \<open>More Theorems Related to Floyd-Warshall\<close>

lemma D_cycle_free_len_dest:
  "cycle_free m n
    \<Longrightarrow> \<forall> i \<le> n. \<forall> j \<le> n. D m i j n = m' i j \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..n}
    \<Longrightarrow> \<exists> ys. set ys \<subseteq> {0..n} \<and> len m' i j xs = len m i j ys"
proof (induction xs arbitrary: i)
  case Nil
  with Nil have "m' i j = D m i j n" by simp
  from D_dest''[OF this]
  obtain ys where "set ys \<subseteq> {0..n}" "len m' i j [] = len m i j ys"
  by auto
  then show ?case by auto
next
  case (Cons y ys)
  from Cons.IH[OF Cons.prems(1,2) _ \<open>j \<le> n\<close>, of y] Cons.prems(5)
  obtain zs where zs:"set zs \<subseteq> {0..n}" "len m' y j ys = len m y j zs" by auto
  with Cons have "m' i y = D m i y n" by simp
  from D_dest''[OF this] obtain ws where ws:"set ws \<subseteq> {0..n}" "m' i y = len m i y ws" by auto
  with len_comp[of m i j ws y zs] zs Cons.prems(5)
  have "len m' i j (y # ys) = len m i j (ws @ y # zs)" "set (ws @ y # zs) \<subseteq> {0..n}" by auto
  then show ?case by blast
qed

lemma D_cyc_free_preservation:
  "cyc_free m n \<Longrightarrow> \<forall> i \<le> n. \<forall> j \<le> n. D m i j n = m' i j \<Longrightarrow> cyc_free m' n"
proof (auto, goal_cases)
  case (1 i xs)
  from D_cycle_free_len_dest[OF _ 1(2,3,3,4)] 1(1) cycle_free_diag_equiv
  obtain ys where "set ys \<subseteq> {0..n} \<and> len m' i i xs = len m i i ys" by fast
  with 1(1,3) show ?case by auto
qed

abbreviation "FW m n \<equiv> fw m n n n n"

lemma FW_cyc_free_preservation:
  "cyc_free m n \<Longrightarrow> cyc_free (FW m n) n"
apply (rule D_cyc_free_preservation)
 apply assumption
apply safe
apply (rule fw_shortest_path)
using cycle_free_diag_equiv by auto

lemma cyc_free_diag_dest':
  "cyc_free m n \<Longrightarrow> i \<le> n \<Longrightarrow> m i i \<ge> \<one>"
proof goal_cases
  case 1
  then have "i \<le> n \<and> set [] \<subseteq> {0..n}" by auto
  with 1(1) have "\<one> \<le> len m i i []" by blast
  then show ?case by auto
qed

lemma FW_diag_neutral_preservation:
  "\<forall> i \<le> n. M i i = \<one> \<Longrightarrow> cyc_free M n \<Longrightarrow> \<forall> i\<le>n. (FW M n) i i = \<one>"
proof (auto, goal_cases)
  case (1 i)
  from this(3) have "(FW M n) i i \<le> M i i" by (auto intro: fw_mono)
  with 1 have "(FW M n) i i \<le> \<one>" by auto
  with cyc_free_diag_dest'[OF FW_cyc_free_preservation[OF 1(2)] \<open>i \<le> n\<close>] show "FW M n i i = \<one>" by auto
qed  

lemma FW_fixed_preservation:
  fixes M :: "('a::linordered_ab_monoid_add) mat"
  assumes A: "i \<le> n" "M 0 i + M i 0 = \<one>" "canonical (FW M n) n" "cyc_free (FW M n) n"
  shows "FW M n 0 i + FW M n i 0 = \<one>" using assms
proof -
  let ?M' = "FW M n"
  assume A: "i \<le> n" "M 0 i + M i 0 = \<one>" "canonical ?M' n" "cyc_free ?M' n"
  from \<open>i \<le> n\<close> have "?M' 0 i + ?M' i 0 \<le> M 0 i + M i 0" by (auto intro: fw_mono add_mono)
  with A(2) have "?M' 0 i + ?M' i 0 \<le> \<one>" by auto
  moreover from \<open>canonical ?M' n\<close> \<open>i \<le> n\<close>
  have "?M' 0 0 \<le> ?M' 0 i + ?M' i 0" by auto
  moreover from cyc_free_diag_dest'[OF  \<open>cyc_free ?M' n\<close>] have "\<one> \<le> ?M' 0 0" by simp
  ultimately show "?M' 0 i + ?M' i 0 = \<one>" by (auto simp: add_mono)
qed

lemma diag_cyc_free_neutral:
  "cyc_free M n \<Longrightarrow> \<forall>k\<le>n. M k k \<le> \<one> \<Longrightarrow> \<forall>i\<le>n. M i i = \<one>"
proof (clarify, goal_cases)
  case (1 i)
  note A = this
  then have "i \<le> n \<and> set [] \<subseteq> {0..n}" by auto
  with A(1) have "\<one> \<le> M i i" by fastforce
  with A(2) \<open>i \<le> n\<close> show "M i i = \<one>" by auto
qed

lemma fw_upd_canonical_id:
  "canonical M n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> fw_upd M k i j = M"
proof (auto simp: fw_upd_def upd_def less_eq[symmetric] min.coboundedI2, goal_cases)
  case 1
  then have "M i j \<le> M i k + M k j" by auto
  then have "min (M i j) (M i k + M k j) = M i j" by (simp split: split_min)
  thus ?case by force
qed

lemma fw_canonical_id:
  "canonical M n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> fw M n k i j = M"
proof (induction k arbitrary: i j)
  case 0
  then show ?case
  proof (induction i arbitrary: j)
    case 0
    then show ?case
    proof (induction j)
      case 0 thus ?case by (auto intro: fw_upd_canonical_id)
    next
      case Suc thus ?case by (auto intro: fw_upd_canonical_id)
    qed
  next
    case Suc
    then show ?case
    proof (induction j)
      case 0 thus ?case by (auto intro: fw_upd_canonical_id)
    next
      case Suc thus ?case by (auto intro: fw_upd_canonical_id)
    qed
  qed
next
  case Suc
  then show ?case
  proof (induction i arbitrary: j)
    case 0
    then show ?case
    proof (induction j)
      case 0 thus ?case by (auto intro: fw_upd_canonical_id)
    next
      case Suc thus ?case by (auto intro: fw_upd_canonical_id)
    qed
  next
    case Suc
    then show ?case
    proof (induction j)
      case 0 thus ?case by (auto intro: fw_upd_canonical_id)
    next
      case Suc thus ?case by (auto intro: fw_upd_canonical_id)
    qed
  qed
qed

lemmas FW_canonical_id = fw_canonical_id[OF _ order.refl order.refl order.refl]

section \<open>Helper Lemmas for Bouyer's Theorem on Approximation\<close>

lemma aux1: "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..n} \<Longrightarrow> (a,b) \<in> set (arcs i j xs) \<Longrightarrow> a \<le> n \<and> b \<le> n"
by (induction xs arbitrary: i) auto

lemma arcs_distinct1:
  "i \<notin> set xs \<Longrightarrow> j \<notin> set xs \<Longrightarrow> distinct xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> (a,b) \<in> set (arcs i j xs) \<Longrightarrow> a \<noteq> b"
apply (induction xs arbitrary: i)
 apply fastforce
apply (rename_tac a' xs i)
apply (case_tac xs)
 apply auto
done

lemma arcs_distinct2:
  "i \<notin> set xs \<Longrightarrow> j \<notin> set xs \<Longrightarrow> distinct xs \<Longrightarrow> i \<noteq> j \<Longrightarrow> (a,b) \<in> set (arcs i j xs) \<Longrightarrow> a \<noteq> b"
by (induction xs arbitrary: i) auto

lemma arcs_distinct3: "distinct (a # b # c # xs) \<Longrightarrow> (i,j) \<in> set (arcs a b xs) \<Longrightarrow> i \<noteq> c \<and> j \<noteq> c"
by (induction xs arbitrary: a) force+

lemma arcs_elem:
  assumes "(a, b) \<in> set (arcs i j xs)" shows "a \<in> set (i # xs)" "b \<in> set (j # xs)"
using assms by (induction xs arbitrary: i) auto

lemma arcs_distinct_dest1:
  "distinct (i # a # zs) \<Longrightarrow> (b,c) \<in> set (arcs a j zs) \<Longrightarrow> b \<noteq> i"
using arcs_elem by fastforce

lemma arcs_distinct_fix:
  "distinct (a # x # xs @ [b]) \<Longrightarrow> (a,c) \<in> set (arcs a b (x # xs)) \<Longrightarrow> c = x"
using arcs_elem(1) by fastforce

lemma disjE3: "A \<or> B \<or> C \<Longrightarrow> (A \<Longrightarrow> G) \<Longrightarrow> (B \<Longrightarrow> G) \<Longrightarrow> (C \<Longrightarrow> G) \<Longrightarrow> G"
by auto

lemma arcs_predecessor:
  assumes "(a, b) \<in> set (arcs i j xs)" "a \<noteq> i"
  shows "\<exists> c. (c, a) \<in> set (arcs i j xs)" using assms
by (induction xs arbitrary: i) auto

lemma arcs_successor:
  assumes "(a, b) \<in> set (arcs i j xs)" "b \<noteq> j"
  shows "\<exists> c. (b,c) \<in> set (arcs i j xs)" using assms
apply (induction xs arbitrary: i)
 apply simp
apply (rename_tac aa xs i)
apply (case_tac xs)
by auto

lemma arcs_predecessor':
  assumes "(a, b) \<in> set (arcs i j (x # xs))" "(a,b) \<noteq> (i, x)"
  shows "\<exists> c. (c, a) \<in> set (arcs i j (x # xs))" using assms
by (induction xs arbitrary: i x) auto

lemma arcs_cases:
  assumes "(a, b) \<in> set (arcs i j xs)" "xs \<noteq> []"
  shows "(\<exists> ys. xs = b # ys \<and> a = i) \<or> (\<exists> ys. xs = ys @ [a] \<and> b = j)
       \<or> (\<exists> c d ys. (a,b) \<in> set (arcs c d ys) \<and> xs = c # ys @ [d])"
using assms
proof (induction xs arbitrary: i)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "(a, b) = (i, x)")
    case True
    with Cons.prems show ?thesis by auto
  next
    case False
    note F = this
    show ?thesis
    proof (cases "xs = []")
      case True
      with F Cons.prems show ?thesis by auto
    next
      case False
      from F Cons.prems have "(a, b) \<in> set (arcs x j xs)" by auto
      from Cons.IH[OF this False] have
        "(\<exists>ys. xs = b # ys \<and> a = x) \<or> (\<exists>ys. xs = ys @ [a] \<and> b = j)
         \<or> (\<exists>c d ys. (a, b) \<in> set (arcs c d ys) \<and> xs = c # ys @ [d])"
      .
      then show ?thesis
      proof (rule disjE3, goal_cases)
        case 1
        from 1 obtain ys where *: "xs = b # ys \<and> a = x" by auto
        show ?thesis
        proof (cases "ys = []")
          case True
          with * show ?thesis by auto
        next
          case False
          then obtain z zs where zs: "ys = zs @ [z]" by (metis append_butlast_last_id) 
          with * show ?thesis by auto
        qed
      next
        case 2 then show ?case by auto
      next
        case 3 with False show ?case by auto
      qed
    qed
  qed
qed

lemma arcs_cases':
  assumes "(a, b) \<in> set (arcs i j xs)" "xs \<noteq> []"
  shows "(\<exists> ys. xs = b # ys \<and> a = i) \<or> (\<exists> ys. xs = ys @ [a] \<and> b = j) \<or> (\<exists> ys zs. xs = ys @ a # b # zs)"
using assms
proof (induction xs arbitrary: i)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "(a, b) = (i, x)")
    case True
    with Cons.prems show ?thesis by auto
  next
    case False
    note F = this
    show ?thesis
    proof (cases "xs = []")
      case True
      with F Cons.prems show ?thesis by auto
    next
      case False
      from F Cons.prems have "(a, b) \<in> set (arcs x j xs)" by auto
      from Cons.IH[OF this False] have
        "(\<exists>ys. xs = b # ys \<and> a = x) \<or> (\<exists>ys. xs = ys @ [a] \<and> b = j)
         \<or> (\<exists>ys zs. xs = ys @ a # b # zs)"
      .
      then show ?thesis
      proof (rule disjE3, goal_cases)
        case 1
        from 1 obtain ys where *: "xs = b # ys \<and> a = x" by auto
        show ?thesis
        proof (cases "ys = []")
          case True
          with * show ?thesis by auto
        next
          case False
          then obtain z zs where zs: "ys = zs @ [z]" by (metis append_butlast_last_id) 
          with * show ?thesis by auto
        qed
      next
        case 2 then show ?case by auto
      next
        case 3
        then obtain ys zs where "xs = ys @ a # b # zs" by auto
        then have "x # xs = (x # ys) @ a # b # zs" by auto
        then show ?thesis by blast
      qed
    qed
  qed
qed

lemma arcs_successor':
  assumes "(a, b) \<in> set (arcs i j xs)" "b \<noteq> j"
  shows "\<exists> c. xs = [b] \<and> a = i \<or> (\<exists> ys. xs = b # c # ys \<and> a = i) \<or> (\<exists> ys. xs = ys @ [a,b] \<and> c = j)
       \<or> (\<exists> ys zs. xs = ys @ a # b # c # zs)"
using assms
proof (induction xs arbitrary: i)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "(a, b) = (i, x)")
    case True
    with Cons.prems show ?thesis by (cases xs) auto
  next
    case False
    note F = this
    show ?thesis
    proof (cases "xs = []")
      case True
      with F Cons.prems show ?thesis by auto
    next
      case False
      from F Cons.prems have "(a, b) \<in> set (arcs x j xs)" by auto
      from Cons.IH[OF this \<open>b \<noteq> j\<close>] obtain c where c:
        "xs = [b] \<and> a = x \<or> (\<exists>ys. xs = b # c # ys \<and> a = x) \<or> (\<exists>ys. xs = ys @ [a, b] \<and> c = j)
         \<or> (\<exists>ys zs. xs = ys @ a # b # c # zs)"
      ..
      then show ?thesis
      proof (standard, goal_cases)
        case 1 with Cons.prems show ?case by auto
      next
        case 2
        then show ?thesis
        proof (rule disjE3, goal_cases)
          case 1
          from 1 obtain ys where *: "xs = b # ys \<and> a = x" by auto
          show ?thesis
          proof (cases "ys = []")
            case True
            with * show ?thesis by auto
          next
            case False
            then obtain z zs where zs: "ys = z # zs" by (cases ys) auto
            with * show ?thesis by fastforce
          qed
        next
          case 2 then show ?case by auto
        next
          case 3
          then obtain ys zs where "xs = ys @ a # b # c # zs" by auto
          then have "x # xs = (x # ys) @ a # b # c # zs" by auto
          then show ?thesis by blast
        qed
      qed
    qed
  qed
qed

lemma list_last:
  "xs = [] \<or> (\<exists> y ys. xs = ys @ [y])"
by (induction xs) auto

lemma arcs_predecessor'':
  assumes "(a, b) \<in> set (arcs i j xs)" "a \<noteq> i"
 shows "\<exists> c. xs = [a] \<or> (\<exists> ys. xs = a # b # ys) \<or> (\<exists> ys. xs = ys @ [c,a] \<and> b = j)
       \<or> (\<exists> ys zs. xs = ys @ c # a # b # zs)"
using assms
proof (induction xs arbitrary: i)
  case Nil then show ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "(a, b) = (i, x)")
    case True
    with Cons.prems show ?thesis by (cases xs) auto
  next
    case False
    note F = this
    show ?thesis
    proof (cases "xs = []")
      case True
      with F Cons.prems show ?thesis by auto
    next
      case False
      from F Cons.prems have *: "(a, b) \<in> set (arcs x j xs)" by auto
      from False obtain y ys where xs: "xs = y # ys" by (cases xs) auto
      show ?thesis
      proof (cases "(a,b) = (x,y)")
        case True with * xs show ?thesis by auto
      next
        case False
        with * xs have **: "(a, b) \<in> set (arcs y j ys)" by auto
        show ?thesis
        proof (cases "ys = []")
          case True with ** xs show ?thesis by force
        next
          case False
          from arcs_cases'[OF ** this] obtain ws zs where ***:
            "ys = b # ws \<and> a = y \<or> ys = ws @ [a] \<and> b = j \<or> ys = ws @ a # b # zs"
          by auto
          then show ?thesis
           apply rule
            using xs apply blast
           apply safe
            using xs list_last[of ws] apply -
            apply (rotate_tac 3)
            apply (case_tac "ws = []")
             apply auto[]
            apply (subgoal_tac "\<exists>y ys. ws = ys @ [y]")
             apply fastforce
            apply simp
           apply (case_tac "ws = []")
            apply (subgoal_tac "x # xs = [x] @ y # a # b # zs")
             apply (rule exI[where x = y])
             apply blast
            apply simp
           subgoal
           proof goal_cases
             case 1
             then obtain u us where "ws = us @ [u]" by auto
             with 1(1,2) have "x # xs = (x # y # us) @ u # a # b # zs" by auto
             then show ?case by blast
           qed
          done
        qed
      qed
    qed
  qed
qed

lemma arcs_ex_middle:
  "\<exists> b. (a, b) \<in> set (arcs i j (ys @ a # xs))"
by (induction xs arbitrary: i ys) (auto simp: arcs_decomp)

lemma arcs_ex_head:
  "\<exists> b. (i, b) \<in> set (arcs i j xs)"
by (cases xs) auto

subsection \<open>Successive\<close>

fun successive where
  "successive _ [] = True" |
  "successive P [_] = True" |
  "successive P (x # y # xs) \<longleftrightarrow> \<not> P y \<and> successive P xs \<or> \<not> P x \<and> successive P (y # xs)"

lemma "\<not> successive (\<lambda> x. x > (0 :: nat)) [Suc 0, Suc 0]" by simp
lemma "successive (\<lambda> x. x > (0 :: nat)) [Suc 0]" by simp
lemma "successive (\<lambda> x. x > (0 :: nat)) [Suc 0, 0, Suc 0]" by simp
lemma "\<not> successive (\<lambda> x. x > (0 :: nat)) [Suc 0, 0, Suc 0, Suc 0]" by simp
lemma "\<not> successive (\<lambda> x. x > (0 :: nat)) [Suc 0, 0, 0, Suc 0, Suc 0]" by simp
lemma "successive (\<lambda> x. x > (0 :: nat)) [Suc 0, 0, Suc 0, 0, Suc 0]" by simp
lemma "\<not> successive (\<lambda> x. x > (0 :: nat)) [Suc 0, Suc 0, 0, Suc 0]" by simp
lemma "successive (\<lambda> x. x > (0 :: nat)) [0, 0, Suc 0, 0]" by simp

lemma successive_step: "successive P (x # xs) \<Longrightarrow> \<not> P x \<Longrightarrow> successive P xs"
  apply (cases xs)
   apply simp
  apply (rename_tac y ys)
  apply (case_tac ys)
   apply auto
done

lemma successive_step_2: "successive P (x # y # xs) \<Longrightarrow> \<not> P y \<Longrightarrow> successive P xs"
  apply (cases xs)
   apply simp
  apply (rename_tac z zs)
  apply (case_tac zs)
   apply auto
done

lemma successive_stepI:
  "successive P xs \<Longrightarrow> \<not> P x \<Longrightarrow> successive P (x # xs)"
by (cases xs) auto

theorem list_two_induct[case_names Nil Single Cons]:
  fixes P :: "'a list \<Rightarrow> bool" 
    and list :: "'a list" 
  assumes Nil: "P []"
  assumes Single: "\<And> x. P [x]"
    and Cons: "\<And>x1 x2 xs. P xs \<Longrightarrow> P (x2 # xs) \<Longrightarrow> P (x1 # x2 # xs)"
  shows "P xs"
using assms
 apply (induction "length xs" arbitrary: xs rule: less_induct)
 apply (rename_tac xs)
 apply (case_tac xs)
  apply simp
 apply (rename_tac ys)
 apply (case_tac ys)
  apply simp
 apply (rename_tac zs)
 apply (case_tac zs)
by auto

lemma successive_end_1:
  "successive P xs \<Longrightarrow> \<not> P x \<Longrightarrow> successive P (xs @ [x])"
by (induction _ xs rule: list_two_induct) auto

lemma successive_ends_1:
  "successive P xs \<Longrightarrow> \<not> P x \<Longrightarrow> successive P ys \<Longrightarrow> successive P (xs @ x # ys)"
by (induction _ xs rule: list_two_induct) (fastforce intro: successive_stepI)+

lemma successive_ends_1':
  "successive P xs \<Longrightarrow> \<not> P x \<Longrightarrow> P y \<Longrightarrow> \<not> P z \<Longrightarrow> successive P ys \<Longrightarrow> successive P (xs @ x # y # z # ys)"
by (induction _ xs rule: list_two_induct) (fastforce intro: successive_stepI)+

lemma successive_end_2:
  "successive P xs \<Longrightarrow> \<not> P x \<Longrightarrow> successive P (xs @ [x,y])"
by (induction _ xs rule: list_two_induct) auto

lemma successive_end_2':
  "successive P (xs @ [x]) \<Longrightarrow> \<not> P x \<Longrightarrow> successive P (xs @ [x,y])"
by (induction _ xs rule: list_two_induct) auto

lemma successive_end_3:
  "successive P (xs @ [x]) \<Longrightarrow> \<not> P x \<Longrightarrow> P y \<Longrightarrow> \<not> P z \<Longrightarrow> successive P (xs @ [x,y,z])"
by (induction _ xs rule: list_two_induct) auto

lemma successive_step_rev:
  "successive P (xs @ [x]) \<Longrightarrow> \<not> P x \<Longrightarrow> successive P xs"
by (induction _ xs rule: list_two_induct) auto

lemma successive_glue:
  "successive P (zs @ [z]) \<Longrightarrow> successive P (x # xs) \<Longrightarrow> \<not> P z \<or> \<not> P x \<Longrightarrow> successive P (zs @ [z] @ x # xs)"
proof goal_cases
  case A: 1
  show ?thesis
  proof (cases "P x")
    case False
    with A(1,2) successive_ends_1 successive_step show ?thesis by fastforce
  next
    case True
    with A(1,3) successive_step_rev have "\<not> P z" "successive P zs" by fastforce+
    with A(2) successive_ends_1 show ?thesis by fastforce
  qed
qed

lemma successive_glue':
  "successive P (zs @ [y]) \<and> \<not> P z \<or> successive P zs \<and> \<not> P y 
  \<Longrightarrow> successive P (x # xs) \<and> \<not> P w \<or> successive P xs \<and> \<not> P x
  \<Longrightarrow> \<not> P z \<or> \<not> P w \<Longrightarrow> successive P (zs @ y # z # w # x # xs)"
by (metis append_Cons append_Nil successive.simps(3) successive_ends_1 successive_glue successive_stepI)

lemma successive_dest_head:
  "xs = w # x # ys \<Longrightarrow> successive P xs \<Longrightarrow> successive P (x # xs) \<and> \<not> P w \<or> successive P xs \<and> \<not> P x"
by auto

lemma successive_dest_tail:
  "xs = zs @ [y,z] \<Longrightarrow> successive P xs \<Longrightarrow> successive P (zs @ [y]) \<and> \<not> P z \<or> successive P zs \<and> \<not> P y"
 apply (induction _ xs arbitrary: zs rule: list_two_induct)
   apply simp+
 apply (rename_tac zs)
 apply (case_tac zs)
  apply simp
 apply (rename_tac ws)
 apply (case_tac ws)
  apply force+
done

lemma successive_split:
  "xs = ys @ zs \<Longrightarrow> successive P xs \<Longrightarrow> successive P ys \<and> successive P zs"
 apply (induction _ xs arbitrary: ys rule: list_two_induct)
   apply simp
  apply (rename_tac ys, case_tac ys)
   apply simp
  apply simp
 apply (rename_tac ys, case_tac ys)
  apply simp
 apply (rename_tac list, case_tac list)
  apply (auto intro: successive_stepI)
done

lemma successive_decomp:
  "xs = x # ys @ zs @ [z] \<Longrightarrow> successive P xs \<Longrightarrow> \<not> P x \<or> \<not> P z \<Longrightarrow> successive P (zs @ [z] @ (x # ys))"
by (metis Cons_eq_appendI successive_glue successive_split)

lemma successive_predecessor:
  assumes "(a, b) \<in> set (arcs i j xs)" "a \<noteq> i" "successive P (arcs i j xs)" "P (a,b)" "xs \<noteq> []"
 shows "\<exists> c. (xs = [a] \<and> c = i \<or> (\<exists> ys. xs = a # b # ys \<and> c = i) \<or> (\<exists> ys. xs = ys @ [c,a] \<and> b = j)
       \<or> (\<exists> ys zs. xs = ys @ c # a # b # zs)) \<and> \<not> P (c,a)"
proof -
  from arcs_predecessor''[OF assms(1,2)] obtain c where c:
    "xs = [a] \<or> (\<exists>ys. xs = a # b # ys) \<or> (\<exists>ys. xs = ys @ [c, a] \<and> b = j)
    \<or> (\<exists>ys zs. xs = ys @ c # a # b # zs)"
  by auto
  then show ?thesis
  proof (safe, goal_cases)
    case 1
    with assms have "arcs i j xs = [(i, a), (a, j)]" by auto
    with assms have "\<not> P (i, a)" by auto
    with 1 show ?case by simp
  next
    case 2
    with assms have "\<not> P (i, a)" by fastforce
    with 2 show ?case by auto
  next
    case 3
    with assms have "\<not> P (c, a)" using arcs_decomp successive_dest_tail by fastforce 
    with 3 show ?case by auto
  next
    case 4
    with assms(3,4) have "\<not> P (c, a)" using arcs_decomp successive_split by fastforce
    with 4 show ?case by auto
  qed
qed

thm arcs_successor'

lemma successive_successor:
  assumes "(a, b) \<in> set (arcs i j xs)" "b \<noteq> j" "successive P (arcs i j xs)" "P (a,b)" "xs \<noteq> []"
 shows "\<exists> c. (xs = [b] \<and> c = j \<or> (\<exists> ys. xs = b # c # ys) \<or> (\<exists> ys. xs = ys @ [a,b] \<and> c = j)
       \<or> (\<exists> ys zs. xs = ys @ a # b # c # zs)) \<and> \<not> P (b,c)"
proof -
  from arcs_successor'[OF assms(1,2)] obtain c where c:
    "xs = [b] \<and> a = i \<or> (\<exists>ys. xs = b # c # ys \<and> a = i) \<or> (\<exists>ys. xs = ys @ [a, b] \<and> c = j)
     \<or> (\<exists>ys zs. xs = ys @ a # b # c # zs)"
  ..
  then show ?thesis
  proof (safe, goal_cases)
    case 1
    with assms(1,2) have "arcs i j xs = [(a,b), (b,j)]" by auto
    with assms have "\<not> P (b,j)" by auto
    with 1 show ?case by simp
  next
    case 2
    with assms have "\<not> P (b, c)" by fastforce
    with 2 show ?case by auto
  next
    case 3
    with assms have "\<not> P (b, c)" using arcs_decomp successive_dest_tail by fastforce 
    with 3 show ?case by auto
  next
    case 4
    with assms(3,4) have "\<not> P (b, c)" using arcs_decomp successive_split by fastforce
    with 4 show ?case by auto
  qed
qed

lemmas add_mono_right = add_mono[OF order_refl]
lemmas add_mono_left  = add_mono[OF _ order_refl]

subsubsection \<open>Obtaining successive and distinct paths\<close>

lemma canonical_successive:
  fixes A B
  defines "M \<equiv> \<lambda> i j. min (A i j) (B i j)"
  assumes "canonical A n"
  assumes "set xs \<subseteq> {0..n}"
  assumes "i \<le> n" "j \<le> n"
  shows "\<exists> ys. len M i j ys \<le> len M i j xs \<and> set ys \<subseteq> {0..n}
               \<and> successive (\<lambda> (a, b). M a b = A a b) (arcs i j ys)"
using assms
proof (induction xs arbitrary: i rule: list_two_induct)
  case Nil show ?case by fastforce
next
  case 2: (Single x i)
  show ?case
  proof (cases "M i x = A i x \<and> M x j = A x j")
    case False
    then have "successive (\<lambda>(a, b). M a b = A a b) (arcs i j [x])" by auto
    with 2 show ?thesis by blast
  next
    case True
    with 2 have "M i j \<le> M i x + M x j" unfolding min_def by fastforce
    with 2(3-) show ?thesis apply simp apply (rule exI[where x = "[]"]) by auto
  qed
next
  case 3: (Cons x y xs i)
  show ?case
  proof (cases "M i y \<le> M i x + M x y", goal_cases)
    case 1
    from 3 obtain ys where
      "len M i j ys \<le> len M i j (y # xs) \<and> set ys \<subseteq> {0..n}
       \<and> successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs i j ys)"
    by fastforce
    moreover from 1 have "len M i j (y # xs) \<le> len M i j (x # y # xs)"
    using add_mono by (auto simp: assoc[symmetric])
    ultimately show ?case by force
  next
    case False
    { assume "M i x = A i x" "M x y = A x y"
      with 3(3-) have "A i y \<le> M i x + M x y" by auto
      then have "M i y \<le> M i x + M x y" unfolding M_def min_def by auto
    } note * = this
    with False have "M i x \<noteq> A i x \<or> M x y \<noteq> A x y" by auto
    then show ?thesis
    proof (standard, goal_cases)
      case 1
      from 3 obtain ys where ys:
        "len M x j ys \<le> len M x j (y # xs)" "set ys \<subseteq> {0..n}"
        "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs x j ys)"
      by force+
      from 1 successive_stepI[OF ys(3), of "(i, x)"] have
        "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs i j (x # ys))"
      by auto
      moreover have "len M i j (x # ys) \<le> len M i j (x # y # xs)" using add_mono_right[OF ys(1)]
      by auto
      ultimately show ?case using 3(5) ys(2) by fastforce
    next
      case 2
      from 3 obtain ys where ys:
        "len M y j ys \<le> len M y j xs" "set ys \<subseteq> {0..n}"
        "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs y j ys)"
      by force+
      from this(3) 2 have
        "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs i j (x # y # ys))" 
      by simp
      moreover from add_mono_right[OF ys(1)] have
        "len M i j (x # y # ys) \<le> len M i j (x # y # xs)"
      by (auto simp: assoc[symmetric])
      ultimately show ?thesis using ys(2) 3(5) by fastforce
    qed
  qed
qed

lemma canonical_successive_distinct:
  fixes A B
  defines "M \<equiv> \<lambda> i j. min (A i j) (B i j)"
  assumes "canonical A n"
  assumes "set xs \<subseteq> {0..n}"
  assumes "i \<le> n" "j \<le> n"
  assumes "distinct xs" "i \<notin> set xs" "j \<notin> set xs"
  shows "\<exists> ys. len M i j ys \<le> len M i j xs \<and> set ys \<subseteq> set xs
               \<and> successive (\<lambda> (a, b). M a b = A a b) (arcs i j ys)
               \<and> distinct ys \<and> i \<notin> set ys \<and> j \<notin> set ys"
using assms
proof (induction xs arbitrary: i rule: list_two_induct)
  case Nil show ?case by fastforce
next
  case 2: (Single x i)
  show ?case
  proof (cases "M i x = A i x \<and> M x j = A x j")
    case False
    then have "successive (\<lambda>(a, b). M a b = A a b) (arcs i j [x])" by auto
    with 2 show ?thesis by blast
  next
    case True
    with 2 have "M i j \<le> M i x + M x j" unfolding min_def by fastforce
    with 2(3-) show ?thesis apply simp apply (rule exI[where x = "[]"]) by auto
  qed
next
  case 3: (Cons x y xs i)
  show ?case
  proof (cases "M i y \<le> M i x + M x y")
    case 1: True
    from 3(2)[OF 3(3,4)] 3(5-10) obtain ys where ys:
      "len M i j ys \<le> len M i j (y # xs)" "set ys \<subseteq> set (x # y # xs)"
       "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs i j ys)"
       "distinct ys \<and> i \<notin> set ys \<and> j \<notin> set ys"
    by fastforce
    moreover from 1 have "len M i j (y # xs) \<le> len M i j (x # y # xs)"
    using add_mono by (auto simp: assoc[symmetric])
    ultimately have "len M i j ys \<le> len M i j (x # y # xs)" by auto
    then show ?thesis using ys(2-) by blast
  next
    case False
    { assume "M i x = A i x" "M x y = A x y"
      with 3(3-) have "A i y \<le> M i x + M x y" by auto
      then have "M i y \<le> M i x + M x y" unfolding M_def min_def by auto
    } note * = this
    with False have "M i x \<noteq> A i x \<or> M x y \<noteq> A x y" by auto
    then show ?thesis
    proof (standard, goal_cases)
      case 1
      from 3(2)[OF 3(3,4)] 3(5-10) obtain ys where ys:
        "len M x j ys \<le> len M x j (y # xs)" "set ys \<subseteq> set (y # xs)"
        "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs x j ys)"
        "distinct ys" "i \<notin> set ys" "x \<notin> set ys" "j \<notin> set ys" 
      by fastforce
      from 1 successive_stepI[OF ys(3), of "(i, x)"] have
        "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs i j (x # ys))"
      by auto
      moreover have "len M i j (x # ys) \<le> len M i j (x # y # xs)" using add_mono_right[OF ys(1)]
      by auto
      moreover have "distinct (x # ys)" "i \<notin> set (x # ys)" "j \<notin> set (x # ys)" using ys(4-) 3(8-)
      by auto
      moreover from ys(2) have "set (x # ys) \<subseteq> set (x # y # xs)" by auto
      ultimately show ?case by fastforce
    next
      case 2
      from 3(1)[OF 3(3,4)] 3(5-) obtain ys where ys:
        "len M y j ys \<le> len M y j xs" "set ys \<subseteq> set xs"
        "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs y j ys)"
        "distinct ys" "j \<notin> set ys" "y \<notin> set ys" "i \<notin> set ys" "x \<notin> set ys"
      by fastforce
      from this(3) 2 have
        "successive (\<lambda>a. case a of (a, b) \<Rightarrow> M a b = A a b) (arcs i j (x # y # ys))" 
      by simp
      moreover from add_mono_right[OF ys(1)] have
        "len M i j (x # y # ys) \<le> len M i j (x # y # xs)"
      by (auto simp: assoc[symmetric])
      moreover have "distinct (x # y # ys)" "i \<notin> set (x # y # ys)" "j \<notin> set (x # y # ys)"
      using ys(4-) 3(8-) by auto
      ultimately show ?thesis using ys(2) by fastforce
    qed
  qed
qed

lemma successive_snd_last: "successive P (xs @ [x, y]) \<Longrightarrow> P y \<Longrightarrow> \<not> P x"
by (induction _ xs rule: list_two_induct) auto

lemma canonical_shorten_rotate_neg_cycle:
  fixes A B
  defines "M \<equiv> \<lambda> i j. min (A i j) (B i j)"
  assumes "canonical A n"
  assumes "set xs \<subseteq> {0..n}"
  assumes "i \<le> n"
  assumes "len M i i xs < \<one>"
  shows "\<exists> j ys. len M j j ys < \<one> \<and> set (j # ys) \<subseteq> set (i # xs)
               \<and> successive (\<lambda> (a, b). M a b = A a b) (arcs j j ys)
               \<and> distinct ys \<and> j \<notin> set ys \<and>
               (ys \<noteq> [] \<longrightarrow> M j (hd ys) \<noteq> A j (hd ys) \<or> M (last ys) j \<noteq> A (last ys) j)"
using assms
proof -
  note A = assms
  from negative_len_shortest[OF _ A(5)] obtain j ys where ys:
    "distinct (j # ys)" "len M j j ys < \<one>" "j \<in> set (i # xs)" "set ys \<subseteq> set xs"
  by blast
  from this(1,3) canonical_successive_distinct[OF A(2) subset_trans[OF this(4) A(3)], of j j B] A(3,4)
  obtain zs where zs:
    "len M j j zs \<le> len M j j ys"
    "set zs \<subseteq> set ys" "successive (\<lambda>(a, b). M a b = A a b) (arcs j j zs)"
    "distinct zs" "j \<notin> set zs"
  by (force simp: M_def)
  show ?thesis
  proof (cases "zs = []")
    assume "zs \<noteq> []"
    then obtain w ws where ws: "zs = w # ws" by (cases zs) auto
    show ?thesis
    proof (cases "ws = []")
      case False
      then obtain u us where us: "ws = us @ [u]" by (induction ws) auto
      show ?thesis
      proof (cases "M j w = A j w \<and> M u j = A u j")
        case True
        have "u \<le> n" "j \<le> n" "w \<le> n" using us ws zs(2) ys(3,4) A(3,4) by auto
        with A(2) True have "M u w \<le> M u j + M j w" unfolding M_def min_def by fastforce
        then have
          "len M u u (w # us) \<le> len M j j zs"
        using ws us by (simp add: len_comp comm) (auto intro: add_mono simp: assoc[symmetric])
        moreover have "set (u # w # us) \<subseteq> set (i # xs)" using ws us zs(2) ys(3,4) by auto
        moreover have "distinct (w # us)" "u \<notin> set (w # us)" using ws us zs(4) by auto
        moreover have "successive (\<lambda>(a, b). M a b = A a b) (arcs u u (w # us))"
        proof (cases us)
          case Nil
          with zs(3) ws us True show ?thesis by auto
        next
          case (Cons v vs)
          with zs(3) ws us True have "M w v \<noteq> A w v" by auto
          with ws us Cons zs(3) True arcs_decomp_tail successive_split show ?thesis by (simp, blast)
        qed
        moreover have "M (last (w # us)) u \<noteq> A (last (w # us)) u"
        proof (cases "us = []")
          case T: True
          with zs(3) ws us True show ?thesis by auto
        next
          case False
          then obtain v vs where vs: "us = vs @ [v]" by (induction us) auto
          with ws us have "arcs j j zs = arcs j v (w # vs) @ [(v, u), (u,j)]" by (simp add: arcs_decomp)
          with zs(3) True have "M v u \<noteq> A v u"
          using successive_snd_last[of "\<lambda>(a, b). M a b = A a b" "arcs j v (w # vs)"] by auto
          with vs show ?thesis by simp
        qed
        ultimately show ?thesis using zs(1) ys(2)
        by (intro exI[where x = u], intro exI[where x = "w # us"]) fastforce
      next
        case False
        with zs ws us ys show ?thesis by (intro exI[where x = j], intro exI[where x = "zs"]) auto
      qed
    next
      case True
      with True ws zs ys show ?thesis by (intro exI[where x = j], intro exI[where x = "zs"]) fastforce
    qed
  next
    case True
    with ys zs show ?thesis by (intro exI[where x = j], intro exI[where x = "zs"]) fastforce
  qed
qed

(* Generated by sledgehammer/z3 *)
lemma successive_arcs_extend_last:
  "successive P (arcs i j xs) \<Longrightarrow> \<not> P (i, hd xs) \<or> \<not> P (last xs, j) \<Longrightarrow> xs \<noteq> []
  \<Longrightarrow> successive P (arcs i j xs @ [(i, hd xs)])"
proof -
  assume a1: "\<not> P (i, hd xs) \<or> \<not> P (last xs, j)"
  assume a2: "successive P (arcs i j xs)"
  assume a3: "xs \<noteq> []"
  then have f4: "\<not> P (last xs, j) \<longrightarrow> successive P (arcs i (last xs) (butlast xs))"
    using a2 by (metis (no_types) append_butlast_last_id arcs_decomp_tail successive_step_rev)
  have f5: "arcs i j xs = arcs i (last xs) (butlast xs) @ [(last xs, j)]"
    using a3 by (metis (no_types) append_butlast_last_id arcs_decomp_tail)
  have "([] @ arcs i j xs @ [(i, hd xs)]) @ [(i, hd xs)] = arcs i j xs @ [(i, hd xs), (i, hd xs)]"
    by simp
  then have "P (last xs, j) \<longrightarrow> successive P (arcs i j xs @ [(i, hd xs)])"
    using a2 a1 by (metis (no_types) self_append_conv2 successive_end_2 successive_step_rev)
  then show ?thesis
    using f5 f4 successive_end_2 by fastforce
qed

lemma cycle_rotate_arcs:
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "length xs > 1" "(i, j) \<in> arcs' xs"
  shows "\<exists> ys zs. set (arcs a a xs) = set (arcs i i (j # ys @ a # zs)) \<and> xs = zs @ i # j # ys" using assms
proof -
  assume A: "length xs > 1" "(i, j) \<in> arcs' xs"
  from arcs'_decomp[OF this] obtain ys zs where xs: "xs = zs @ i # j # ys" by blast
  with arcs_decomp[OF this, of a a] arcs_decomp[of "j # ys @ a # zs" "j # ys" a zs i i]
  show ?thesis by force
qed

lemma cycle_rotate_len_arcs_successive:
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "length xs > 1" "(i, j) \<in> arcs' xs" "successive P (arcs a a xs)" "\<not> P (a, hd xs) \<or> \<not> P (last xs, a)"
  shows "\<exists> ys zs. len M a a xs = len M i i (j # ys @ a # zs)
                \<and> set (arcs a a xs) = set (arcs i i (j # ys @ a # zs)) \<and> xs = zs @ i # j # ys
                \<and> successive P (arcs i i (j # ys @ a # zs))"
using assms
proof -
  note A = assms
  from arcs'_decomp[OF A(1,2)] obtain ys zs where xs: "xs = zs @ i # j # ys" by blast
  note arcs1 = arcs_decomp[OF xs, of a a]
  note arcs2 = arcs_decomp[of "j # ys @ a # zs" "j # ys" a zs i i]
  have *:"successive P (arcs i i (j # ys @ a # zs))"
  proof (cases "ys = []")
    case True
    show ?thesis
    proof (cases zs)
      case Nil
      with A(3,4) xs True show ?thesis by auto
    next
      case (Cons z zs')
      with True arcs2 A(3,4) xs show ?thesis apply simp
      by (metis arcs.simps(1,2) arcs1 successive.simps(3) successive_split successive_step) 
    qed
  next
    case False
    then obtain y ys' where ys: "ys = ys' @ [y]" by (metis append_butlast_last_id)
    show ?thesis
    proof (cases zs)
      case Nil
      with A(3,4) xs ys have
        "\<not> P (a, i) \<or> \<not> P (y, a)" "successive P (arcs a a (i # j # ys' @ [y]))"
      by simp+
      from successive_decomp[OF _ this(2,1)] show ?thesis using ys Nil arcs_decomp by fastforce
    next
      case (Cons z zs')
      with A(3,4) xs ys have
        "\<not> P (a, z) \<or> \<not> P (y, a)" "successive P (arcs a a (z # zs' @ i # j # ys' @ [y]))"
      by simp+
      from successive_decomp[OF _ this(2,1)] show ?thesis using ys Cons arcs_decomp by fastforce
    qed
  qed
  from len_decomp[OF xs, of M a a] have "len M a a xs = len M a i zs + len M i a (j # ys)" .
  also have "\<dots> = len M i a (j # ys) + len M a i zs" by (simp add: comm)
  also from len_comp[of M i i "j # ys" a zs] have "\<dots> = len M i i (j # ys @ a # zs)" by auto
  finally show ?thesis
  using * xs arcs_decomp[OF xs, of a a] arcs_decomp[of "j # ys @ a # zs" "j # ys" a zs i i] by force
qed

lemma successive_successors:
  "xs = ys @ a # b # c # zs \<Longrightarrow> successive P (arcs i j xs) \<Longrightarrow> \<not> P (a,b) \<or> \<not> P (b, c)"
 apply (induction _ xs arbitrary: i ys rule: list_two_induct)
   apply fastforce
  apply fastforce
 apply (rename_tac ys, case_tac ys)
  apply fastforce
 apply (rename_tac list, case_tac list)
  apply fastforce+
done

lemma successive_successors':
  "xs = ys @ a # b # zs \<Longrightarrow> successive P xs \<Longrightarrow> \<not> P a \<or> \<not> P b"
using successive_split by fastforce

lemma cycle_rotate_len_arcs_successive':
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "length xs > 1" "(i, j) \<in> arcs' xs" "successive P (arcs a a xs)"
          "\<not> P (a, hd xs) \<or> \<not> P (last xs, a)"
  shows "\<exists> ys zs. len M a a xs = len M i i (j # ys @ a # zs)
                \<and> set (arcs a a xs) = set (arcs i i (j # ys @ a # zs)) \<and> xs = zs @ i # j # ys
                \<and> successive P (arcs i i (j # ys @ a # zs) @ [(i,j)])"
using assms
proof -
  note A = assms
  from arcs'_decomp[OF A(1,2)] obtain ys zs where xs: "xs = zs @ i # j # ys" by blast
  note arcs1 = arcs_decomp[OF xs, of a a]
  note arcs2 = arcs_decomp[of "j # ys @ a # zs" "j # ys" a zs i i]
  have *:"successive P (arcs i i (j # ys @ a # zs) @ [(i,j)])"
  proof (cases "ys = []")
    case True
    show ?thesis
    proof (cases zs)
      case Nil
      with A(3,4) xs True show ?thesis by auto
    next
      case (Cons z zs')
      with True arcs2 A(3,4) xs show ?thesis
       apply simp
       apply (cases "P (a, z)")
        apply (simp add: arcs_decomp)
        apply (simp only: append_Cons[symmetric])
        using successive_split[of "((a, z) # arcs z i zs') @ [(i, j), (j, a)]" _ "[(j, a)]" P]
        apply auto[]
       subgoal (* Generated by sledgehammer *)
       proof simp
         assume a1: "successive P ((a, z) # arcs z a (zs' @ [i, j]))"
         assume a2: "\<not> P (a, z)"
         assume a3: "zs = z # zs'"
         assume a4: "ys = []"
         assume a5: "xs = z # zs' @ [i, j]"
         have f6: "\<forall>p pa ps. \<not> successive p ((pa::nat \<times> nat) # ps) \<or> p pa \<or> successive p ps"
           by (meson successive_step)
         have "(a, z) # arcs z i zs' @ (i, j) # arcs j a [] = arcs a a xs"
           using a4 a3 by (simp add: arcs1)
         then have "arcs z a (zs' @ [i, j]) = arcs z i zs' @ [(i, j), (j, a)]"
           using a5 by simp
         then show
           "\<not> P (j, a) \<and> successive P ((a, z) # arcs z i zs' @ [(i, j)])
          \<or> \<not> P (i, j) \<and> (successive P (arcs z i zs' @ [(i, j)])
          \<or> \<not> P (j, a) \<and> successive P ((a, z) # arcs z i zs' @ [(i, j)]))"
         using f6 a2 a1
         by (metis successive.simps(1) successive_dest_tail successive_ends_1 successive_stepI)
       qed
      done
    qed  
  next
    case False
    then obtain y ys' where ys: "ys = ys' @ [y]" by (metis append_butlast_last_id)
    show ?thesis
    proof (cases zs)
      case Nil
      with A(3,4) xs ys have *:
        "\<not> P (a, i) \<or> \<not> P (y, a)" "successive P (arcs a a (i # j # ys' @ [y]))"
      by simp+
      from successive_decomp[OF _ this(2,1)] ys Nil arcs_decomp have
        "successive P (arcs i i (j # ys @ a # zs))"
      by fastforce
      moreover from * have "\<not> P (a, i) \<or> \<not> P (i, j)" by auto
      ultimately show ?thesis
      by (metis append_Cons last_snoc list.distinct(1) list.sel(1) Nil successive_arcs_extend_last)
    next
      case (Cons z zs')
      with A(3,4) xs ys have *:
        "\<not> P (a, z) \<or> \<not> P (y, a)" "successive P (arcs a a (z # zs' @ i # j # ys' @ [y]))"
        by simp_all
      from successive_decomp[OF _ this(2,1)] ys Cons arcs_decomp have **:
        "successive P (arcs i i (j # ys @ a # zs))"
        by fastforce
      from Cons have "zs \<noteq> []" by auto
      then obtain w ws where ws: "zs = ws @ [w]" by (induction zs) auto
      with A(3,4) xs ys have *:
        "successive P (arcs a a (ws @ [w] @ i # j # ys' @ [y]))"
        by simp
      from successive_successors[OF _ *] have "\<not> P (w, i) \<or> \<not> P (i, j)" by auto
      with * show ?thesis
        by (metis ** append_is_Nil_conv last.simps last_append list.distinct(2) list.sel(1)
                successive_arcs_extend_last ws) 
    qed
  qed
  from len_decomp[OF xs, of M a a] have "len M a a xs = len M a i zs + len M i a (j # ys)" .
  also have "\<dots> = len M i a (j # ys) + len M a i zs" by (simp add: comm)
  also from len_comp[of M i i "j # ys" a zs] have "\<dots> = len M i i (j # ys @ a # zs)" by auto
  finally show ?thesis
  using * xs arcs_decomp[OF xs, of a a] arcs_decomp[of "j # ys @ a # zs" "j # ys" a zs i i] by force
qed

lemma cycle_rotate_3:
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "xs \<noteq> []" "(i, j) \<in> set (arcs a a xs)" "successive P (arcs a a xs)" "\<not> P (a, hd xs) \<or> \<not> P (last xs, a)"
  shows "\<exists> ys. len M a a xs = len M i i (j # ys) \<and> set (i # j # ys) = set (a # xs) \<and> 1 + length ys = length xs
             \<and> set (arcs a a xs) = set (arcs i i (j # ys))
             \<and> successive P (arcs i i (j # ys))"
proof -
  note A = assms
  { fix ys assume A:"a = i" "xs = j # ys"
    with assms(3) have ?thesis by auto
  } note * = this
  have **: ?thesis if A: "a = j" "xs = ys @ [i]" for ys using A
  proof (safe, goal_cases)
    case 1
    have "len M j j (ys @ [i]) = M i j + len M j i ys"
    using len_decomp[of "ys @ [i]" ys i "[]" M j j] by (auto simp: comm)
    moreover have "arcs j j (ys @ [i]) = arcs j i ys @ [(i, j)]" using arcs_decomp_tail by auto
    moreover with assms(3,4) A have "successive P ((i,j) # arcs j i ys)"
     apply simp
     apply (case_tac ys)
      apply simp
     apply simp
    by (metis arcs.simps(2) calculation(2) 1(1) successive_split successive_step)
    ultimately show ?case by auto
  qed
  { assume "length xs = 1"
    then obtain b where xs: "xs = [b]" by (metis One_nat_def length_0_conv length_Suc_conv) 
    with A(2) have "a = i \<and> b = j \<or> a = j \<and> b = i" by auto
    then have ?thesis using * ** xs by auto
  } note *** = this
  show ?thesis
  proof (cases "length xs = 0")
    case True with A show ?thesis by auto
  next
    case False
    thus ?thesis
    proof (cases "length xs = 1", goal_cases)
      case True with *** show ?thesis by auto
    next
      case 2
      hence "length xs > 1" by linarith
      then obtain b c ys where ys:"xs = b # ys @ [c]"
      by (metis One_nat_def assms(1) 2(2) length_0_conv length_Cons list.exhaust rev_exhaust) 
      thus ?thesis
      proof (cases "(i,j) = (a,b)")
        case True
        with ys * show ?thesis by blast
      next
        case False
        then show ?thesis
        proof (cases "(i,j) = (c,a)", goal_cases)
          case True
          with ys ** show ?thesis by force
        next
          case 2
          with A(2) ys have "(i, j) \<in> arcs' xs"
          using cycle_rotate_2_aux by (auto simp add: arcs'_def) (* slow *)
          from cycle_rotate_len_arcs_successive[OF \<open>length xs > 1\<close> this A(3,4), of M] show ?thesis
          by auto
        qed
      qed
    qed
  qed
qed

lemma cycle_rotate_3':
  fixes M :: "('a :: linordered_ab_monoid_add) mat"
  assumes "xs \<noteq> []" "(i, j) \<in> set (arcs a a xs)" "successive P (arcs a a xs)" "\<not> P (a, hd xs) \<or> \<not> P (last xs, a)"
  shows "\<exists> ys. len M a a xs = len M i i (j # ys) \<and> set (i # j # ys) = set (a # xs) \<and> 1 + length ys = length xs
             \<and> set (arcs a a xs) = set (arcs i i (j # ys))
             \<and> successive P (arcs i i (j # ys) @ [(i, j)])"
proof -
  note A = assms
  have *: ?thesis if "a = i" "xs = j # ys" for ys
  using that assms(3) successive_arcs_extend_last[OF assms(3,4)] by auto
  have **: ?thesis if A:"a = j" "xs = ys @ [i]" for ys
  using A proof (auto, goal_cases)
    case 1
    have "len M j j (ys @ [i]) = M i j + len M j i ys"
    using len_decomp[of "ys @ [i]" ys i "[]" M j j] by (auto simp: comm)
    moreover have "arcs j j (ys @ [i]) = arcs j i ys @ [(i, j)]" using arcs_decomp_tail by auto
    moreover with assms(3,4) A have "successive P ((i,j) # arcs j i ys @ [(i, j)])"
     apply simp
     apply (case_tac ys)
      apply simp
     apply simp
    by (metis successive_step)
    ultimately show ?case by auto
  qed
  { assume "length xs = 1"
    then obtain b where xs: "xs = [b]" by (metis One_nat_def length_0_conv length_Suc_conv) 
    with A(2) have "a = i \<and> b = j \<or> a = j \<and> b = i" by auto
    then have ?thesis using * ** xs by auto
  } note *** = this
  show ?thesis
  proof (cases "length xs = 0")
    case True with A show ?thesis by auto
  next
    case False
    thus ?thesis
    proof (cases "length xs = 1", goal_cases)
      case True with *** show ?thesis by auto
    next
      case 2
      hence "length xs > 1" by linarith
      then obtain b c ys where ys:"xs = b # ys @ [c]"
      by (metis One_nat_def assms(1) 2(2) length_0_conv length_Cons list.exhaust rev_exhaust) 
      thus ?thesis
      proof (cases "(i,j) = (a,b)")
        case True
        with ys * show ?thesis by blast
      next
        case False
        then show ?thesis
        proof (cases "(i,j) = (c,a)", goal_cases)
          case True
          with ys ** show ?thesis by force
        next
          case 2
          with A(2) ys have "(i, j) \<in> arcs' xs"
          using cycle_rotate_2_aux by (auto simp add: arcs'_def) (* slow *)
          from cycle_rotate_len_arcs_successive'[OF \<open>length xs > 1\<close> this A(3,4), of M] show ?thesis
          by auto
        qed
      qed
    qed
  qed
qed

end
