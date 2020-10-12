theory DBM_Basics
  imports DBM Paths_Cycles
begin

fun get_const where
  "get_const (Le c) = c" |
  "get_const (Lt c) = c" |
  "get_const \<infinity> = undefined"


subsection \<open>Discourse on updating DBMs\<close>

abbreviation DBM_update :: "('t::time) DBM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('t DBMEntry) \<Rightarrow> ('t::time) DBM"
where
  "DBM_update M m n v \<equiv> (\<lambda> x y. if m = x \<and> n = y then v else M x y)"
  
fun DBM_upd :: "('t::time) DBM \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 't DBMEntry) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 't DBM"
where
  "DBM_upd M f 0 0 _ = DBM_update M 0 0 (f 0 0)" |
  "DBM_upd M f (Suc i) 0 n = DBM_update (DBM_upd M f i n n) (Suc i) 0 (f (Suc i) 0)" |
  "DBM_upd M f i (Suc j) n = DBM_update (DBM_upd M f i j n) i (Suc j) (f i (Suc j))"
  
lemma upd_1:
assumes "j \<le> n"
shows "DBM_upd M1 f (Suc m) n N (Suc m) j = DBM_upd M1 f (Suc m) j N (Suc m) j"
using assms
by (induction n) auto

lemma upd_2:
assumes "i \<le> m"
shows "DBM_upd M1 f (Suc m) n N i j = DBM_upd M1 f (Suc m) 0 N i j"
using assms
proof (induction n)
  case 0 thus ?case by blast
next
  case (Suc n)
  thus ?case by simp
qed

lemma upd_3:
assumes "m \<le> N" "n \<le> N" "j \<le> n" "i \<le> m"
shows "(DBM_upd M1 f m n N) i j = (DBM_upd M1 f i j N) i j"
using assms
proof (induction m arbitrary: n i j, goal_cases)
  case (1 n) thus ?case by (induction n) auto
next
  case (2 m n i j) thus ?case
  proof (cases "i = Suc m")
    case True thus ?thesis using upd_1[OF \<open>j \<le> n\<close>] by blast
    next
    case False
    with \<open>i \<le> Suc m\<close> have "i \<le> m" by auto
    with upd_2[OF this] have "DBM_upd M1 f (Suc m) n N i j = DBM_upd M1 f m N N i j" by force
    also have "\<dots> = DBM_upd M1 f i j N i j" using False 2 by force
    finally show ?thesis .
  qed
qed

lemma upd_id:
  assumes "m \<le> N" "n \<le> N" "i \<le> m" "j \<le> n"
  shows "(DBM_upd M1 f m n N) i j = f i j"
proof -
  from assms upd_3 have "DBM_upd M1 f m n N i j = DBM_upd M1 f i j N i j" by blast
  also have "\<dots> = f i j" by (cases i; cases j; fastforce)
  finally show ?thesis .
qed


subsection \<open>Zones and DBMs\<close>

definition DBM_zone_repr :: "('t::time) DBM \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('c, 't :: time) zone"
("[_]\<^bsub>_,_\<^esub>" [72,72,72] 72)
where
  "[M]\<^bsub>v,n\<^esub> = {u . DBM_val_bounded v u M n}"

lemma dbm_entry_val_mono_1:
  "dbm_entry_val u (Some c) (Some c') b \<Longrightarrow> b \<preceq> b' \<Longrightarrow> dbm_entry_val u (Some c) (Some c') b'"
proof (induction b, goal_cases)
  case 1 thus ?case using le_dbm_le le_dbm_lt by (induction b'; fastforce)
next
  case 2 thus ?case using lt_dbm_le lt_dbm_lt by (induction b'; fastforce)
next
  case 3 thus ?case unfolding dbm_le_def by auto
qed

lemma dbm_entry_val_mono_2:
  "dbm_entry_val u None (Some c) b \<Longrightarrow> b \<preceq> b' \<Longrightarrow> dbm_entry_val u None (Some c) b'"
proof (induction b, goal_cases)
  case 1 thus ?case using le_dbm_le le_dbm_lt by (induction b'; fastforce)
next
  case 2 thus ?case using lt_dbm_le lt_dbm_lt by (induction b'; fastforce)
next
  case 3 thus ?case unfolding dbm_le_def by auto
qed

lemma dbm_entry_val_mono_3:
  "dbm_entry_val u (Some c) None b \<Longrightarrow> b \<preceq> b' \<Longrightarrow> dbm_entry_val u (Some c) None b'"
proof (induction b, goal_cases)
  case 1 thus ?case using le_dbm_le le_dbm_lt by (induction b'; fastforce)
next
  case 2 thus ?case using lt_dbm_le lt_dbm_lt by (induction b'; fastforce)
next
  case 3 thus ?case unfolding dbm_le_def by auto
qed

lemma DBM_le_subset:
  "\<forall> i j. i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> M i j \<preceq> M' i j \<Longrightarrow> u \<in> [M]\<^bsub>v,n\<^esub> \<Longrightarrow> u \<in> [M']\<^bsub>v,n\<^esub>"
proof -
  assume A: "\<forall>i j. i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> M i j \<preceq> M' i j" "u \<in> [M]\<^bsub>v,n\<^esub>"
  hence "DBM_val_bounded v u M n" by (simp add: DBM_zone_repr_def)
  with A(1) have "DBM_val_bounded v u M' n" unfolding DBM_val_bounded_def
  proof (auto, goal_cases)
    case 1 from this(1,2) show ?case unfolding less_eq[symmetric] by fastforce
  next
    case (2 c)
    hence "dbm_entry_val u None (Some c) (M 0 (v c))" "M 0 (v c) \<preceq> M' 0 (v c)" by auto
    thus ?case using dbm_entry_val_mono_2 by fast
  next
    case (3 c)
    hence "dbm_entry_val u (Some c) None (M (v c) 0)" "M (v c) 0 \<preceq> M' (v c) 0" by auto
    thus ?case using dbm_entry_val_mono_3 by fast 
  next
    case (4 c1 c2)
    hence "dbm_entry_val u (Some c1) (Some c2) (M (v c1) (v c2))" "M (v c1) (v c2) \<preceq> M' (v c1) (v c2)"
    by auto
    thus ?case using dbm_entry_val_mono_1 by fast
  qed
  thus "u \<in> [M']\<^bsub>v,n\<^esub>" by (simp add: DBM_zone_repr_def)
qed


subsection \<open>DBMs Without Negative Cycles are Non-Empty\<close>

text \<open>
  We need all of these assumptions for the proof that matrices without negative cycles
  represent non-negative zones:
    * Abelian (linearly ordered) monoid
    * Time is non-trivial
    * Time is dense
\<close>
lemmas (in linordered_ab_monoid_add) comm = add.commute

lemma sum_gt_neutral_dest':
  "(a :: (('a :: time) DBMEntry)) \<ge> \<one> \<Longrightarrow> a + b > \<one> \<Longrightarrow> \<exists> d. Le d \<le> a \<and> Le (-d) \<le> b \<and> d \<ge> 0"
proof -
  assume "a + b > \<one>" "a \<ge> \<one>"
  show ?thesis
  proof (cases "b \<ge> \<one>")
    case True
    with \<open>a \<ge> \<one>\<close> show ?thesis by (auto simp: neutral)
  next
    case False
    hence "b < Le 0" by (auto simp: neutral)
    with \<open>a \<ge> \<one>\<close> \<open>a + b > \<one>\<close> show ?thesis
    proof (cases a, cases b, auto simp: neutral, goal_cases)
      case (1 a' b')
      from 1(2) have "a' + b' > 0" by (auto elim: dbm_lt.cases simp: less mult)
      hence "b' > -a'" by (metis add.commute diff_0 diff_less_eq)
      with \<open>Le 0 \<le> Le a'\<close> show ?case
      by (auto simp: dbm_le_def less_eq le_dbm_le)
    next
      case (2 a' b')
      from this(2) have "a' + b' > 0" by (auto elim: dbm_lt.cases simp: less mult)
      hence "b' > -a'" by (metis add.commute diff_0 diff_less_eq)
      with \<open>Le 0 \<le> Le a'\<close> show ?case
      by (auto simp: dbm_le_def less_eq le_dbm_le)
    next
      case (3 a') thus ?case by (auto simp: dbm_le_def less_eq)
    next
      case (4 a')
      thus ?case
      proof (cases b, auto, goal_cases)
        case (1 b')
        have "b' < 0" using 1(2) by (metis dbm_lt.intros(3) less less_asym neqE)
        from 1 have "a' + b' > 0" by (auto elim: dbm_lt.cases simp: less mult)
        then have "-b' < a'" by (metis diff_0 diff_less_eq)
        with \<open>b' < 0\<close> show ?case by (auto simp: dbm_le_def less_eq)
      next
        case (2 b')
        then have A: "b' \<le> 0" "a' > 0" by (auto elim: dbm_lt.cases simp: less less_eq dbm_le_def)
        show ?case
        proof (cases "b' = 0")
          case True
          from dense[OF A(2)] obtain d where d: "d > 0" "d < a'" by auto
          then have "Le (-d) < Lt b'" "Le d < Lt a'" unfolding less using True by auto
          with d(1) show ?thesis by - (rule exI[where x = "d"], auto)
        next
          case False
          with A(1) have *: "- b' > 0" by simp
          from 2 have "a' + b' > 0" by (auto elim: dbm_lt.cases simp: less mult)
          then have "-b' < a'" by (metis less_add_same_cancel1 minus_add_cancel minus_less_iff) 
          from dense[OF this] obtain d where d:
            "d > -b'" "-d < b'" "d < a'"
          by (auto simp add: minus_less_iff)
          then have "Le (-d) < Lt b'" "Le d < Lt a'" unfolding less by auto
          with d(1) * show ?thesis
          by - (rule exI[where x = "d"], auto,
                meson d(2) dual_order.order_iff_strict less_trans neg_le_0_iff_le)
        qed
      next
        case 3 thus ?case by (auto simp: dbm_le_def less_eq)
      qed
    next
      case 5 thus ?case
      proof (cases b, auto, goal_cases)
        case (1 b')
        from this(2) have "-b' \<ge> 0"
        by (metis dbm_lt.intros(3) leI less less_asym neg_less_0_iff_less) 
        let ?d = "- b'"
        have "Le ?d \<le> \<infinity>" "Le (- ?d) \<le> Le b'" by (auto simp: any_le_inf)
        with \<open>-b' \<ge> 0\<close> show ?case by auto
      next
        case (2 b')
        then have "b' \<le> 0" by (auto elim: dbm_lt.cases simp: less)
        from non_trivial_neg obtain e :: 'a where e:"e < 0" by blast
        let ?d = "- (b' + e)"
        from e \<open>b' \<le> 0\<close> have "Le ?d \<le> \<infinity>" "Le (- ?d) \<le> Lt b'" "b' + e < 0"
        by (auto simp: dbm_lt.intros(4) less less_imp_le any_le_inf add_nonpos_neg)
        then have "Le ?d \<le> \<infinity>" "Le (- ?d) \<le> Lt b'" "?d \<ge> 0"
        using less_imp_le neg_0_le_iff_le by blast+
        thus ?case by auto
      qed
    qed
  qed
qed

lemma sum_gt_neutral_dest:
  "(a :: (('a :: time) DBMEntry)) + b > \<one> \<Longrightarrow> \<exists> d. Le d \<le> a \<and> Le (-d) \<le> b"
proof -
  assume A: "a + b > \<one>"
  then have A': "b + a > \<one>" by (simp add: comm)
  show ?thesis
  proof (cases "a \<ge> \<one>")
    case True
    with A sum_gt_neutral_dest' show ?thesis by auto
  next
    case False
    { assume "b \<le> \<one>"
      with False have "a \<le> \<one>" "b \<le> \<one>" by auto
      from add_mono[OF this] have "a + b \<le> \<one>" by auto
      with A have False by auto
    }
    then have "b \<ge> \<one>" by fastforce
    with sum_gt_neutral_dest'[OF this A'] show ?thesis by auto
  qed
qed

subsection \<open>
  Negative Cycles in DBMs
\<close>

lemma DBM_val_bounded_neg_cycle1:
fixes i xs assumes
  bounded: "DBM_val_bounded v u M n" and A:"i \<le> n" "set xs \<subseteq> {0..n}" "len M i i xs < \<one>" and
  surj_on: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)" and at_most: "i \<noteq> 0" "cnt 0 xs \<le> 1"
shows False
proof -
  from A(1) surj_on at_most obtain c where c: "v c = i" by auto
  with DBM_val_bounded_len'3[OF bounded at_most(2), of c c] A(1,2) surj_on 
  have bounded:"dbm_entry_val u (Some c) (Some c) (len M i i xs)" by force
  from A(3) have "len M i i xs \<prec> Le 0" by (simp add: neutral less)
  then show False using bounded by (cases rule: dbm_lt.cases) (auto elim: dbm_entry_val.cases)
qed

lemma cnt_0_I:
  "x \<notin> set xs \<Longrightarrow> cnt x xs = 0"
by (induction xs) auto

lemma distinct_cnt: "distinct xs \<Longrightarrow> cnt x xs \<le> 1"
 apply (induction xs)
  apply simp
  apply (rename_tac a xs)
 apply (case_tac "x = a")
using cnt_0_I by fastforce+

lemma DBM_val_bounded_neg_cycle:
fixes i xs assumes
  bounded: "DBM_val_bounded v u M n" and A:"i \<le> n" "set xs \<subseteq> {0..n}" "len M i i xs < \<one>" and
  surj_on: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
shows False
proof -
  from negative_len_shortest[OF _ A(3)] obtain j ys where ys:
    "distinct (j # ys)" "len M j j ys < \<one>" "j \<in> set (i # xs)" "set ys \<subseteq> set xs"
  by blast
  show False
  proof (cases "ys = []")
    case True
    show ?thesis
    proof (cases "j = 0")
      case True
      with \<open>ys = []\<close> ys bounded show False unfolding DBM_val_bounded_def neutral less_eq[symmetric]
      by auto
    next
      case False
      with \<open>ys = []\<close> DBM_val_bounded_neg_cycle1[OF bounded _ _ ys(2) surj_on] ys(3) A(1,2)
      show False by auto
    qed
  next
    case False
    from distinct_arcs_ex[OF _ _ this, of j 0 j] ys(1) obtain a b where arc:
      "a \<noteq> 0" "(a, b) \<in> set (arcs j j ys)"
    by auto
    from cycle_rotate_2'[OF False this(2)] obtain zs where zs:
      "len M j j ys = len M a a (b # zs)" "set (a # b # zs) = set (j # ys)"
      "1 + length zs = length ys" "set (arcs j j ys) = set (arcs a a (b # zs))"
    by blast
    with distinct_card[OF ys(1)] have "distinct (a # b # zs)" by (intro card_distinct) auto
    with distinct_cnt[of "b # zs"] have *: "cnt 0 (b # zs) \<le> 1" by fastforce
    show ?thesis
     apply (rule DBM_val_bounded_neg_cycle1[OF bounded _ _ _ surj_on \<open>a \<noteq> 0\<close> *]) 
       using zs(2) ys(3,4) A(1,2) apply fastforce+
    using zs(1) ys(2) by simp
  qed
qed

subsection \<open>Floyd-Warshall Algorithm Preservers Zones\<close>

lemma D_dest: "x = D m i j k \<Longrightarrow>
  x \<in> {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
using Min_elem_dest[OF D_base_finite'' D_base_not_empty] by (fastforce simp add: D_def)

lemma FW_zone_equiv:
  "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k) \<Longrightarrow> [M]\<^bsub>v,n\<^esub> = [FW M n]\<^bsub>v,n\<^esub>"
proof safe
  fix u assume A: "u \<in> [FW M n]\<^bsub>v,n\<^esub>"
  { fix i j assume "i \<le> n" "j \<le> n"
    hence "FW M n i j \<le> M i j" using fw_mono[of n n n i j M n] by simp
    hence "FW M n i j \<preceq> M i j" by (simp add: less_eq)
  }
  with DBM_le_subset[of n "FW M n" M] A show "u \<in> [M]\<^bsub>v,n\<^esub>" by auto
next
  fix u assume u:"u \<in> [M]\<^bsub>v,n\<^esub>" and surj_on: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  hence *:"DBM_val_bounded v u M n" by (simp add: DBM_zone_repr_def)
  note ** = DBM_val_bounded_neg_cycle[OF this _ _ _ surj_on]
  have cyc_free: "cyc_free M n" using ** by fastforce
  with cycle_free_diag_equiv have cycle_free: "cycle_free M n" by auto
  from cycle_free_diag[OF this] have diag_ge_zero: "\<forall>k\<le>n. M k k \<ge> Le 0" unfolding neutral by auto
  
  have "DBM_val_bounded v u (FW M n) n" unfolding DBM_val_bounded_def
  proof (auto, goal_cases)
    case 1
    from fw_shortest_path[OF cycle_free, of 0 n 0 n n] have **:
      "D M 0 0 n = FW M n 0 0"
    by (simp add: neutral)
    from D_dest[OF **[symmetric]] obtain xs where xs:
        "FW M n 0 0 = len M 0 0 xs" "set xs \<subseteq> {0..n}"
        "0 \<notin> set xs" "distinct xs"
    by auto
    with cyc_free have "FW M n 0 0 \<ge> \<one>" by auto
    then show ?case unfolding neutral less_eq by simp
  next
    case (2 c)
    with fw_shortest_path[OF cycle_free, of 0 n "v c" n n] have **:
      "D M 0 (v c) n = FW M n 0 (v c)"
    by (simp add: neutral)
    from D_dest[OF **[symmetric]] obtain xs where xs:
        "FW M n 0 (v c) = len M 0 (v c) xs" "set xs \<subseteq> {0..n}"
        "0 \<notin> set xs" "v c \<notin> set xs" "distinct xs"
    by auto
    show ?case unfolding xs(1) using xs surj_on \<open>v c \<le> n\<close>
    by - (rule DBM_val_bounded_len'2[OF * xs(3)]; auto)
  next
    case (3 c)
    with fw_shortest_path[OF cycle_free, of "v c" n 0 n n] have **:
      "D M (v c) 0 n = FW M n (v c) 0"
    by (simp add: neutral)
    with D_dest[OF **[symmetric]] obtain xs where xs:
      "FW M n (v c) 0 = len M (v c) 0 xs" "set xs \<subseteq> {0..n}"
      "0 \<notin> set xs" "v c \<notin> set xs" "distinct xs"
    by auto
    show ?case unfolding xs(1) using xs surj_on \<open>v c \<le> n\<close>
    by - (rule DBM_val_bounded_len'1[OF * xs(3)]; auto)
  next
    case (4 c1 c2)
    with fw_shortest_path[OF cycle_free, of "v c1" n "v c2" n n]
    have "D M (v c1) (v c2) n = FW M n (v c1) (v c2)" by (simp add: neutral)
    from D_dest[OF this[symmetric]] obtain xs where xs:
      "FW M n (v c1) (v c2) = len M (v c1) (v c2) xs" "set xs \<subseteq> {0..n}"
      "v c1 \<notin> set xs" "v c2 \<notin> set xs" "distinct xs"
    by auto
    show ?case
    unfolding xs(1)
     apply (rule DBM_val_bounded_len'3[OF *])
        using xs surj_on \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> apply auto
     apply (drule distinct_cnt[of _ 0])
    by auto
  qed
  then show "u \<in> [FW M n]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def by simp
qed

lemma new_negative_cycle_aux':
  fixes M :: "('a :: time) DBM"
  fixes i j d
  defines "M' \<equiv> \<lambda> i' j'. if (i' = i \<and> j' = j) then Le d
                       else if (i' = j \<and> j' = i) then Le (-d)
                       else M i' j'"
  assumes "i \<le> n" "j \<le> n" "set xs \<subseteq> {0..n}" "cycle_free M n" "length xs = m"
  assumes "len M' i i (j # xs) < \<one> \<or> len M' j j (i # xs) < \<one>"
  assumes "i \<noteq> j"
  shows "\<exists>xs. set xs \<subseteq> {0..n} \<and> j \<notin> set xs \<and> i \<notin> set xs
              \<and> (len M' i i (j # xs) < \<one> \<or> len M' j j (i # xs) < \<one>)" using assms
proof (induction _ m arbitrary: xs rule: less_induct)
  case (less x)
  { fix b a xs assume A: "(i, j) \<notin> set (arcs b a xs)" "(j, i) \<notin> set (arcs b a xs)"
    with \<open>i \<noteq> j\<close> have "len M' b a xs = len M b a xs"
    unfolding M'_def by (induction xs arbitrary: b) auto
  } note * = this
  { fix a xs assume A:"(i, j) \<notin> set (arcs a a xs)" "(j, i) \<notin> set (arcs a a xs)"
    assume a: "a \<le> n" and xs: "set xs \<subseteq> {0..n}" and cycle: "\<not> len M' a a xs \<ge> \<one>"
    from *[OF A] have "len M' a a xs = len M a a xs" .
    with \<open>cycle_free M n\<close> \<open>i \<le> n\<close> cycle xs a have False unfolding cycle_free_def by auto
  } note ** = this
  { fix a :: nat fix ys :: "nat list"
    assume A: "ys \<noteq> []" "length ys \<le> length xs" "set ys \<subseteq> set xs" "a \<le> n"
    assume cycle: "len M' a a ys < \<one>"
    assume arcs: "(i, j) \<in> set (arcs a a ys) \<or> (j, i) \<in> set (arcs a a ys)"
    from arcs have ?thesis
    proof
      assume "(i, j) \<in> set (arcs a a ys)"
      from cycle_rotate_2[OF \<open>ys \<noteq> []\<close> this, of M']
      obtain ws where ws: "len M' a a ys = len M' i i (j # ws)" "set ws \<subseteq> set (a # ys)"
        "length ws < length ys" by auto
      with cycle less.hyps(1)[OF _ less.hyps(2) , of "length ws" ws] less.prems A
      show ?thesis by fastforce
    next
      assume "(j, i) \<in> set (arcs a a ys)"
      from cycle_rotate_2[OF \<open>ys \<noteq> []\<close> this, of M']
      obtain ws where ws: "len M' a a ys = len M' j j (i # ws)" "set ws \<subseteq> set (a # ys)"
        "length ws < length ys" by auto
      with cycle less.hyps(1)[OF _ less.hyps(2) , of "length ws" ws] less.prems A
      show ?thesis by fastforce
    qed
  } note *** = this
  { fix a :: nat fix ys :: "nat list"
    assume A: "ys \<noteq> []" "length ys \<le> length xs" "set ys \<subseteq> set xs" "a \<le> n"
    assume cycle: "\<not> len M' a a ys \<ge> \<one>"
    with A **[of a ys] less.prems
    have "(i, j) \<in> set (arcs a a ys) \<or> (j, i) \<in> set (arcs a a ys)" by auto
    with ***[OF A] cycle have ?thesis by auto
  } note neg_cycle_IH = this
  from cycle_free_diag[OF \<open>cycle_free M n\<close>] have "\<forall>i. i \<le> n \<longrightarrow> Le 0 \<le> M i i" unfolding neutral by auto
  then have M'_diag: "\<forall>i. i \<le> n \<longrightarrow> Le 0 \<le> M' i i" unfolding M'_def using \<open>i \<noteq> j\<close> by auto
  from less(8) show ?thesis
  proof standard
    assume cycle:"len M' i i (j # xs) < \<one>"
    show ?thesis
    proof (cases "i \<in> set xs")
      case False
      then show ?thesis
      proof (cases "j \<in> set xs")
        case False
        with \<open>i \<notin> set xs\<close> show ?thesis using less.prems(3,6) by auto
      next
        case True
        then obtain ys zs where ys_zs: "xs = ys @ j # zs" by (meson split_list)
        with len_decomp[of "j # xs" "j # ys" j zs M' i i]
        have len: "len M' i i (j # xs) = M' i j + len M' j j ys + len M' j i zs" by auto
        show ?thesis
        proof (cases "len M' j j ys \<ge> \<one>")
          case True
          have "len M' i i (j # zs) = M' i j + len M' j i zs" by simp
          also from len True have "M' i j + len M' j i zs \<le> len M' i i (j # xs)"
          by (metis add_le_impl add_lt_neutral comm not_le)
          finally have cycle': "len M' i i (j # zs) < \<one>" using cycle by auto
          from ys_zs less.prems(5) have "x > length zs" by auto
          from cycle' less.prems ys_zs less.hyps(1)[OF this less.hyps(2) , of zs]
          show ?thesis by auto
        next
          case False
          with M'_diag less.prems have "ys \<noteq> []" by (auto simp: neutral)
          from neg_cycle_IH[OF this] ys_zs False less.prems(1,2) show ?thesis by auto
        qed
      qed
    next
      case True
      then obtain ys zs where ys_zs: "xs = ys @ i # zs" by (meson split_list)
      with len_decomp[of "j # xs" "j # ys" i zs M' i i]
      have len: "len M' i i (j # xs) = M' i j + len M' j i ys + len M' i i zs" by auto
      show ?thesis
      proof (cases "len M' i i zs \<ge> \<one>")
        case True
        have "len M' i i (j # ys) = M' i j + len M' j i ys" by simp
        also from len True have "M' i j + len M' j i ys \<le> len M' i i (j # xs)"
        by (metis add_lt_neutral comm not_le)
        finally have cycle': "len M' i i (j # ys) < \<one>" using cycle by auto
        from ys_zs less.prems(5) have "x > length ys" by auto
        from cycle' less.prems ys_zs less.hyps(1)[OF this less.hyps(2) , of ys]
        show ?thesis by auto
      next
        case False
        with less.prems(1,7) M'_diag have "zs \<noteq> []" by (auto simp: neutral)
        from neg_cycle_IH[OF this] ys_zs False less.prems(1,2) show ?thesis by auto
      qed
    qed
  next
    assume cycle:"len M' j j (i # xs) < \<one>"
    show ?thesis
    proof (cases "j \<in> set xs")
      case False
      then show ?thesis
      proof (cases "i \<in> set xs")
        case False
        with \<open>j \<notin> set xs\<close> show ?thesis using less.prems(3,6) by auto
      next
        case True
        then obtain ys zs where ys_zs: "xs = ys @ i # zs" by (meson split_list)
        with len_decomp[of "i # xs" "i # ys" i zs M' j j]
        have len: "len M' j j (i # xs) = M' j i + len M' i i ys + len M' i j zs" by auto
        show ?thesis
        proof (cases "len M' i i ys \<ge> \<one>")
          case True
          have "len M' j j (i # zs) = M' j i + len M' i j zs" by simp
          also from len True have "M' j i + len M' i j zs \<le> len M' j j (i # xs)"
          by (metis add_le_impl add_lt_neutral comm not_le)
          finally have cycle': "len M' j j (i # zs) < \<one>" using cycle by auto
          from ys_zs less.prems(5) have "x > length zs" by auto
          from cycle' less.prems ys_zs less.hyps(1)[OF this less.hyps(2) , of zs]
          show ?thesis by auto
        next
          case False
          with less.prems M'_diag have "ys \<noteq> []" by (auto simp: neutral)
          from neg_cycle_IH[OF this] ys_zs False less.prems(1,2) show ?thesis by auto
        qed
      qed
    next
      case True
      then obtain ys zs where ys_zs: "xs = ys @ j # zs" by (meson split_list)
      with len_decomp[of "i # xs" "i # ys" j zs M' j j]
      have len: "len M' j j (i # xs) = M' j i + len M' i j ys + len M' j j zs" by auto
      show ?thesis
      proof (cases "len M' j j zs \<ge> \<one>")
        case True
        have "len M' j j (i # ys) = M' j i + len M' i j ys" by simp
        also from len True have "M' j i + len M' i j ys \<le> len M' j j (i # xs)"
        by (metis add_lt_neutral comm not_le)
        finally have cycle': "len M' j j (i # ys) < \<one>" using cycle by auto
        from ys_zs less.prems(5) have "x > length ys" by auto
        from cycle' less.prems ys_zs less.hyps(1)[OF this less.hyps(2) , of ys]
        show ?thesis by auto
      next
        case False
        with less.prems(2,7) M'_diag have "zs \<noteq> []" by (auto simp: neutral)
        from neg_cycle_IH[OF this] ys_zs False less.prems(1,2) show ?thesis by auto
      qed
    qed
  qed
qed

lemma new_negative_cycle_aux:
  fixes M :: "('a :: time) DBM"
  fixes i d
  defines "M' \<equiv> \<lambda> i' j'. if (i' = i \<and> j' = 0) then Le d
                       else if (i' = 0 \<and> j' = i) then Le (-d)
                       else M i' j'"
  assumes "i \<le> n" "set xs \<subseteq> {0..n}" "cycle_free M n" "length xs = m"
  assumes "len M' 0 0 (i # xs) < \<one> \<or> len M' i i (0 # xs) < \<one>"
  assumes "i \<noteq> 0"
  shows "\<exists>xs. set xs \<subseteq> {0..n} \<and> 0 \<notin> set xs \<and> i \<notin> set xs
              \<and> (len M' 0 0 (i # xs) < \<one> \<or> len M' i i (0 # xs) < \<one>)" using assms
proof (induction _ m arbitrary: xs rule: less_induct)
  case (less x)
  { fix b a xs assume A: "(0, i) \<notin> set (arcs b a xs)" "(i, 0) \<notin> set (arcs b a xs)"
    then have "len M' b a xs = len M b a xs"
    unfolding M'_def by (induction xs arbitrary: b) auto
  } note * = this
  { fix a xs assume A:"(0, i) \<notin> set (arcs a a xs)" "(i, 0) \<notin> set (arcs a a xs)"
    assume a: "a \<le> n" and xs: "set xs \<subseteq> {0..n}" and cycle: "\<not> len M' a a xs \<ge> \<one>"
    from *[OF A] have "len M' a a xs = len M a a xs" .
    with \<open>cycle_free M n\<close> \<open>i \<le> n\<close> cycle xs a have False unfolding cycle_free_def by auto
  } note ** = this
  { fix a :: nat fix ys :: "nat list"
    assume A: "ys \<noteq> []" "length ys \<le> length xs" "set ys \<subseteq> set xs" "a \<le> n"
    assume cycle: "len M' a a ys < \<one>"
    assume arcs: "(0, i) \<in> set (arcs a a ys) \<or> (i, 0) \<in> set (arcs a a ys)"
    from arcs have ?thesis
    proof
      assume "(0, i) \<in> set (arcs a a ys)"
      from cycle_rotate_2[OF \<open>ys \<noteq> []\<close> this, of M']
      obtain ws where ws: "len M' a a ys = len M' 0 0 (i # ws)" "set ws \<subseteq> set (a # ys)"
        "length ws < length ys" by auto
      with cycle less.hyps(1)[OF _ less.hyps(2) , of "length ws" ws] less.prems A
      show ?thesis by fastforce
    next
      assume "(i, 0) \<in> set (arcs a a ys)"
      from cycle_rotate_2[OF \<open>ys \<noteq> []\<close> this, of M']
      obtain ws where ws: "len M' a a ys = len M' i i (0 # ws)" "set ws \<subseteq> set (a # ys)"
        "length ws < length ys" by auto
      with cycle less.hyps(1)[OF _ less.hyps(2) , of "length ws" ws] less.prems A
      show ?thesis by fastforce
    qed
  } note *** = this
  { fix a :: nat fix ys :: "nat list"
    assume A: "ys \<noteq> []" "length ys \<le> length xs" "set ys \<subseteq> set xs" "a \<le> n"
    assume cycle: "\<not> len M' a a ys \<ge> \<one>"
    with A **[of a ys]  less.prems(2)
    have "(0, i) \<in> set (arcs a a ys) \<or> (i, 0) \<in> set (arcs a a ys)" by auto
    with ***[OF A] cycle have ?thesis by auto
  } note neg_cycle_IH = this
  from cycle_free_diag[OF \<open>cycle_free M n\<close>] have "\<forall>i. i \<le> n \<longrightarrow> Le 0 \<le> M i i" unfolding neutral by auto
  then have M'_diag: "\<forall>i. i \<le> n \<longrightarrow> Le 0 \<le> M' i i" unfolding M'_def using \<open>i \<noteq> 0\<close> by auto
  from less(7) show ?thesis
  proof standard
    assume cycle:"len M' 0 0 (i # xs) < \<one>"
    show ?thesis
    proof (cases "0 \<in> set xs")
      case False
      thus ?thesis
      proof (cases "i \<in> set xs")
        case False
        with \<open>0 \<notin> set xs\<close> show ?thesis using less.prems by auto
      next
        case True
        then obtain ys zs where ys_zs: "xs = ys @ i # zs" by (meson split_list)
        with len_decomp[of "i # xs" "i # ys" i zs M' 0 0]
        have len: "len M' 0 0 (i # xs) = M' 0 i + len M' i i ys + len M' i 0 zs" by auto
        show ?thesis
        proof (cases "len M' i i ys \<ge> \<one>")
          case True
          have "len M' 0 0 (i # zs) = M' 0 i + len M' i 0 zs" by simp
          also from len True have "M' 0 i + len M' i 0 zs \<le> len M' 0 0 (i # xs)"
          by (metis add_le_impl add_lt_neutral comm not_le)
          finally have cycle': "len M' 0 0 (i # zs) < \<one>" using cycle by auto
          from ys_zs less.prems(4) have "x > length zs" by auto
          from cycle' less.prems ys_zs less.hyps(1)[OF this less.hyps(2) , of zs]
          show ?thesis by auto
        next
          case False
          with less.prems(1,6) M'_diag have "ys \<noteq> []" by (auto simp: neutral)
          from neg_cycle_IH[OF this] ys_zs False less.prems(1,2) show ?thesis by auto
        qed
      qed
    next
      case True
      then obtain ys zs where ys_zs: "xs = ys @ 0 # zs" by (meson split_list)
      with len_decomp[of "i # xs" "i # ys" 0 zs M' 0 0]
      have len: "len M' 0 0 (i # xs) = M' 0 i + len M' i 0 ys + len M' 0 0 zs" by auto
      show ?thesis
      proof (cases "len M' 0 0 zs \<ge> \<one>")
        case True
        have "len M' 0 0 (i # ys) = M' 0 i + len M' i 0 ys" by simp
        also from len True have "M' 0 i + len M' i 0 ys \<le> len M' 0 0 (i # xs)"
        by (metis add_lt_neutral comm not_le)
        finally have cycle': "len M' 0 0 (i # ys) < \<one>" using cycle by auto
        from ys_zs less.prems(4) have "x > length ys" by auto
        from cycle' less.prems ys_zs less.hyps(1)[OF this less.hyps(2) , of ys]
        show ?thesis by auto
      next
        case False
        with less.prems(1,6) M'_diag have "zs \<noteq> []" by (auto simp: neutral)
        from neg_cycle_IH[OF this] ys_zs False less.prems(1,2) show ?thesis by auto
      qed
    qed
  next
    assume cycle: "len M' i i (0 # xs) < \<one>"
    show ?thesis
    proof (cases "i \<in> set xs")
      case False
      thus ?thesis
      proof (cases "0 \<in> set xs")
        case False
        with \<open>i \<notin> set xs\<close> show ?thesis using less.prems by auto
      next
        case True
        then obtain ys zs where ys_zs: "xs = ys @ 0 # zs" by (meson split_list)
        with len_decomp[of "0 # xs" "0 # ys" 0 zs M' i i]
        have len: "len M' i i (0 # xs) = M' i 0 + len M' 0 0 ys + len M' 0 i zs" by auto
        show ?thesis
        proof (cases "len M' 0 0 ys \<ge> \<one>")
          case True
          have "len M' i i (0 # zs) = M' i 0 + len M' 0 i zs" by simp
          also from len True have "M' i 0 + len M' 0 i zs \<le> len M' i i (0 # xs)"
          by (metis add_le_impl add_lt_neutral comm not_le)
          finally have cycle': "len M' i i (0 # zs) < \<one>" using cycle by auto
          from ys_zs less.prems(4) have "x > length zs" by auto
          from cycle' less.prems ys_zs less.hyps(1)[OF this less.hyps(2) , of zs]
          show ?thesis by auto
        next
          case False
          with less.prems(1,6) M'_diag have "ys \<noteq> []" by (auto simp: neutral)
          from neg_cycle_IH[OF this] ys_zs False less.prems(1,2) show ?thesis by auto
        qed
      qed
    next
      case True
      then obtain ys zs where ys_zs: "xs = ys @ i # zs" by (meson split_list)
      with len_decomp[of "0 # xs" "0 # ys" i zs M' i i]
      have len: "len M' i i (0 # xs) = M' i 0 + len M' 0 i ys + len M' i i zs" by auto
      show ?thesis
      proof (cases "len M' i i zs \<ge> \<one>")
        case True
        have "len M' i i (0 # ys) = M' i 0 + len M' 0 i ys" by simp
        also from len True have "M' i 0 + len M' 0 i ys \<le> len M' i i (0 # xs)"
        by (metis add_lt_neutral comm not_le)
        finally have cycle': "len M' i i (0 # ys) < \<one>" using cycle by auto
        from ys_zs less.prems(4) have "x > length ys" by auto
        from cycle' less.prems ys_zs less.hyps(1)[OF this less.hyps(2) , of ys]
        show ?thesis by auto
      next
        case False
        with less.prems(1,6) M'_diag have "zs \<noteq> []" by (auto simp: neutral)
        from neg_cycle_IH[OF this] ys_zs False less.prems(1,2) show ?thesis by auto
      qed
    qed
  qed
qed


section \<open>The Characteristic Property of Canonical DBMs\<close>

theorem fix_index':
  fixes M :: "(('a :: time) DBMEntry) mat"
  assumes "Le r \<le> M i j" "Le (-r) \<le> M j i" "cycle_free M n" "canonical M n" "i \<le> n" "j \<le> n" "i \<noteq> j"
  defines "M' \<equiv> \<lambda> i' j'. if (i' = i \<and> j' = j) then Le r
                       else if (i' = j \<and> j' = i) then Le (-r)
                       else M i' j'"
  shows "(\<forall> u. DBM_val_bounded v u M' n \<longrightarrow> DBM_val_bounded v u M n) \<and> cycle_free M' n"
proof -
  note A = assms
  note r = assms(1,2)
  from \<open>cycle_free M n\<close> have diag_cycles: "\<forall>i xs. i \<le> n \<and> set xs \<subseteq> {0..n} \<longrightarrow> Le 0 \<le> len M i i xs"
  unfolding cycle_free_def neutral by auto
  let ?M' = "\<lambda> i' j'. if (i' = i \<and> j' = j) then Le r
                       else if (i' = j \<and> j' = i) then Le (-r)
                       else M i' j'"
  have "?M' i' j' \<le> M i' j'" when "i' \<le> n" "j' \<le> n" for i' j' using assms by auto
  with DBM_le_subset[folded less_eq, of n ?M' M] have "DBM_val_bounded v u M n"
  if "DBM_val_bounded v u ?M' n" for u unfolding DBM_zone_repr_def using that by auto
  then have not_empty:"\<forall> u. DBM_val_bounded v u ?M' n \<longrightarrow> DBM_val_bounded v u M n" by auto
  { fix a xs assume prems: "a \<le> n" "set xs \<subseteq> {0..n}" and cycle: "\<not> len ?M' a a xs \<ge> \<one>"
    { fix b assume A: "(i, j) \<notin> set (arcs b a xs)" "(j, i) \<notin> set (arcs b a xs)"
      with \<open>i \<noteq> j\<close> have "len ?M' b a xs = len M b a xs" by (induction xs arbitrary: b) auto
    } note * = this
    { fix a b xs assume A: "i \<notin> set (a # xs)" "j \<notin> set (a # xs)"
      then have "len ?M' a b xs = len M a b xs" by (induction xs arbitrary: a, auto)
    } note ** = this
    { assume A:"(i, j) \<notin> set (arcs a a xs)" "(j, i) \<notin> set (arcs a a xs)"
      from *[OF this] have "len ?M' a a xs = len M a a xs" .
      with \<open>cycle_free M n\<close> prems cycle have False by (auto simp: cycle_free_def)
    }
    then have arcs:"(i, j) \<in> set (arcs a a xs) \<or> (j, i) \<in> set (arcs a a xs)" by auto
    with \<open>i \<noteq> j\<close> have "xs \<noteq> []" by auto
    from arcs obtain xs where xs: "set xs \<subseteq> {0..n}"
      "len ?M' i i (j # xs) < \<one> \<or> len ?M' j j (i # xs) < \<one>"
    proof (standard, goal_cases)
      case 1
      from cycle_rotate_2'[OF \<open>xs \<noteq> []\<close> this(2), of ?M'] prems obtain ys where
        "len ?M' i i (j # ys) = len ?M' a a xs" "set ys \<subseteq> {0..n}"
      by fastforce
      with 1 cycle show ?thesis by fastforce
    next
      case 2
      from cycle_rotate_2'[OF \<open>xs \<noteq> []\<close> this(2), of ?M'] prems obtain ys where
        "len ?M' j j (i # ys) = len ?M' a a xs" "set ys \<subseteq> {0..n}"
      by fastforce
      with 2 cycle show ?thesis by fastforce
    qed
    from new_negative_cycle_aux'[OF \<open>i \<le> n\<close> \<open>j \<le> n\<close> this(1) \<open>cycle_free M n\<close> _ this(2) \<open>i \<noteq> j\<close>]
    obtain xs where xs:
      "set xs \<subseteq> {0..n}" "i \<notin> set xs" "j \<notin> set xs"
      "len ?M' i i (j # xs) < \<one> \<or> len ?M' j j (i # xs) < \<one>"
    by auto
    from this(4) have False
    proof
      assume A: "len ?M' j j (i # xs) < \<one>"
      show False
      proof (cases xs)
        case Nil
        with \<open>i \<noteq> j\<close> have *:"?M' j i = Le (-r)" "?M' i j = Le r" by simp+
        from Nil have "len ?M' j j (i # xs) = ?M' j i + ?M' i j" by simp
        with * have "len ?M' j j (i # xs) = Le 0" by (simp add: mult)
        then show False using A by (simp add: neutral)
      next
        case (Cons y ys)
        have *:"M i y + M y j \<ge> M i j"
        using \<open>canonical M n\<close> Cons xs \<open>i \<le> n\<close> \<open>j \<le> n\<close> by (simp add: mult less_eq)
        have "Le 0 = Le (-r) + Le r" by (simp add: mult)
        also have "\<dots> \<le> Le (-r) + M i j" using r by (simp add: add_mono)
        also have "\<dots> \<le> Le (-r) + M i y + M y j" using * by (simp add: add_mono assoc)
        also have "\<dots> \<le> Le (-r) + ?M' i y + len M y j ys"
        using canonical_len[OF \<open>canonical M n\<close>] xs(1-3) \<open>i \<le> n\<close> \<open>j \<le> n\<close> Cons by (simp add: add_mono)
        also have "\<dots> = len ?M' j j (i # xs)" using Cons \<open>i \<noteq> j\<close> ** xs(1-3) by (simp add: assoc)
        also have "\<dots> < Le 0" using A by (simp add: neutral)
        finally show False by simp
      qed
    next
      assume A: "len ?M' i i (j # xs) < \<one>"
      show False
      proof (cases xs)
        case Nil
        with \<open>i \<noteq> j\<close> have *:"?M' j i = Le (-r)" "?M' i j = Le r" by simp+
        from Nil have "len ?M' i i (j # xs) = ?M' i j + ?M' j i" by simp
        with * have "len ?M' i i (j # xs) = Le 0" by (simp add: mult)
        then show False using A by (simp add: neutral)
      next
        case (Cons y ys)
        have *:"M j y + M y i \<ge> M j i"
        using \<open>canonical M n\<close> Cons xs \<open>i \<le> n\<close> \<open>j \<le> n\<close> by (simp add: mult less_eq)
        have "Le 0 = Le r + Le (-r)" by (simp add: mult)
        also have "\<dots> \<le> Le r + M j i" using r by (simp add: add_mono)
        also have "\<dots> \<le> Le r + M j y + M y i" using * by (simp add: add_mono assoc)
        also have "\<dots> \<le> Le r + ?M' j y + len M y i ys"
        using canonical_len[OF \<open>canonical M n\<close>] xs(1-3) \<open>i \<le> n\<close> \<open>j \<le> n\<close> Cons by (simp add: add_mono)
        also have "\<dots> = len ?M' i i (j # xs)" using Cons \<open>i \<noteq> j\<close> ** xs(1-3) by (simp add: assoc)
        also have "\<dots> < Le 0" using A by (simp add: neutral)
        finally show False by simp
      qed
    qed
  } note * = this
  have "cycle_free ?M' n" using negative_cycle_dest_diag * by fastforce
  then show ?thesis using not_empty \<open>i \<noteq> j\<close> r unfolding M'_def by auto
qed

lemma fix_index:
  fixes M :: "(('a :: time) DBMEntry) mat"
  assumes "M 0 i + M i 0 > \<one>" "cycle_free M n" "canonical M n" "i \<le> n" "i \<noteq> 0"
  shows
  "\<exists> (M' :: ('a DBMEntry) mat). ((\<exists> u. DBM_val_bounded v u M' n) \<longrightarrow> (\<exists> u. DBM_val_bounded v u M n))
     \<and> M' 0 i + M' i 0 = \<one> \<and> cycle_free M' n
     \<and> (\<forall> j. i \<noteq> j \<and> M 0 j + M j 0 = \<one> \<longrightarrow> M' 0 j + M' j 0 = \<one>)
     \<and> (\<forall> j. i \<noteq> j \<and> M 0 j + M j 0 > \<one> \<longrightarrow> M' 0 j + M' j 0 > \<one>)"
proof -
  note A = assms
  from sum_gt_neutral_dest[OF assms(1)] obtain d where d: "Le d \<le> M i 0" "Le (-d) \<le> M 0 i" by auto
  have "i \<noteq> 0" using A by - (rule ccontr; simp)
  let ?M' = "\<lambda>i' j'. if i' = i \<and> j' = 0 then Le d else if i' = 0 \<and> j' = i then Le (-d) else M i' j'"
  from fix_index'[OF d(1,2) A(2,3,4) _ \<open>i \<noteq> 0\<close>] have M':
    "\<forall>u. DBM_val_bounded v u ?M' n \<longrightarrow> DBM_val_bounded v u M n" "cycle_free ?M' n"
  by auto
  moreover from \<open>i \<noteq> 0\<close> have "\<forall> j. i \<noteq> j \<and> M 0 j + M j 0 = \<one> \<longrightarrow> ?M' 0 j + ?M' j 0 = \<one>" by auto
  moreover from \<open>i \<noteq> 0\<close> have "\<forall> j. i \<noteq> j \<and> M 0 j + M j 0 > \<one> \<longrightarrow> ?M' 0 j + ?M' j 0 > \<one>" by auto
  moreover from \<open>i \<noteq> 0\<close> have "?M' 0 i + ?M' i 0 = \<one>" unfolding neutral mult by auto
  ultimately show ?thesis by blast
qed

subsubsection \<open>
  Putting it together
\<close>

lemma FW_not_empty:
  "DBM_val_bounded v u (FW M' n) n \<Longrightarrow> DBM_val_bounded v u M' n"
proof -
  assume A: "DBM_val_bounded v u (FW M' n) n"
  have "\<forall>i j. i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> FW M' n i j \<le> M' i j" using fw_mono by blast
  from DBM_le_subset[of n "FW M' n" M' _ v, OF this[unfolded less_eq]]
  show "DBM_val_bounded v u M' n" using A by (auto simp: DBM_zone_repr_def)
qed

lemma fix_indices:
  fixes M :: "(('a :: time) DBMEntry) mat"
  assumes "set xs \<subseteq> {0..n}" "distinct xs"
  assumes "cyc_free M n" "canonical M n"
  shows 
  "\<exists> (M' :: ('a DBMEntry) mat). ((\<exists> u. DBM_val_bounded v u M' n) \<longrightarrow> (\<exists> u. DBM_val_bounded v u M n))
     \<and> (\<forall> i \<in> set xs. i \<noteq> 0 \<longrightarrow> M' 0 i + M' i 0 = \<one>) \<and> cyc_free M' n
     \<and> (\<forall> i\<le>n. i \<notin> set xs \<and> M 0 i + M i 0 = \<one> \<longrightarrow> M' 0 i + M' i 0 = \<one>)" using assms
proof (induction xs arbitrary: M)
  case Nil then show ?case by auto
next
  case (Cons i xs)
  show ?case
  proof (cases "M 0 i + M i 0 \<le> \<one> \<or> i = 0")
    case True
    note T = this
    show ?thesis
    proof (cases "i = 0")
      case False
      from Cons.prems have "0 \<le> n" "set [i] \<subseteq> {0..n}" by auto
      with Cons.prems(3) False T have "M 0 i + M i 0 = \<one>" by fastforce
      with Cons.IH[OF _ _ Cons.prems(3,4)] Cons.prems(1,2) show ?thesis by auto
    next
      case True
      with Cons.IH[OF _ _ Cons.prems(3,4)] Cons.prems(1,2) show ?thesis by auto
    qed
  next
    case False
    with Cons.prems have "\<one> < M 0 i + M i 0" "i \<le> n" "i \<noteq> 0" by auto
    with fix_index[OF this(1) cycle_free_diag_intro[OF Cons.prems(3)] Cons.prems(4) this(2,3), of v]
    obtain M' :: "('a DBMEntry) mat" where M':
      "((\<exists>u. DBM_val_bounded v u M' n) \<longrightarrow> (\<exists>u. DBM_val_bounded v u M n))" "(M' 0 i + M' i 0 = \<one>)"
      "cyc_free M' n" "\<forall>j\<le>n. i \<noteq> j \<and> M 0 j + M j 0 > \<one> \<longrightarrow> M' 0 j + M' j 0 > \<one>"
      "\<forall>j. i \<noteq> j \<and> M 0 j + M j 0 = \<one> \<longrightarrow> M' 0 j + M' j 0 = \<one>"
    using cycle_free_diag_equiv by blast
    let ?M' = "FW M' n"
    from fw_canonical[of M' n] cycle_free_diag_equiv \<open>cyc_free M' n\<close> have "canonical ?M' n" by auto
    from FW_cyc_free_preservation[OF \<open>cyc_free M' n\<close>] have "cyc_free ?M' n"
    by auto
    from FW_fixed_preservation[OF \<open>i \<le> n\<close> M'(2) \<open>canonical ?M' n\<close> \<open>cyc_free ?M' n\<close>]
    have fixed:"?M' 0 i + ?M' i 0 = \<one>" by (auto simp: add_mono)
    from Cons.IH[OF _ _ \<open>cyc_free ?M' n\<close> \<open>canonical ?M' n\<close>] Cons.prems(1,2,3)
    obtain M'' :: "('a DBMEntry) mat"
    where M'': "((\<exists>u. DBM_val_bounded v u M'' n) \<longrightarrow> (\<exists>u. DBM_val_bounded v u ?M' n))"
      "(\<forall>i\<in>set xs. i \<noteq> 0 \<longrightarrow> M'' 0 i + M'' i 0 = \<one>)" "cyc_free M'' n"
      "(\<forall>i\<le>n. i \<notin> set xs \<and> ?M' 0 i + ?M' i 0 = \<one> \<longrightarrow> M'' 0 i + M'' i 0 = \<one>)"
    by auto
    from FW_fixed_preservation[OF _ _ \<open>canonical ?M' n\<close> \<open>cyc_free ?M' n\<close>] M'(5)
    have "\<forall>j\<le>n. i \<noteq> j \<and> M 0 j + M j 0 = \<one> \<longrightarrow> ?M' 0 j + ?M' j 0 = \<one>" by auto
    with M''(4) have "\<forall>j\<le>n. j \<notin> set (i # xs) \<and> M 0 j + M j 0 = \<one> \<longrightarrow> M'' 0 j + M'' j 0 = \<one>" by auto
    moreover from M''(2) M''(4) fixed Cons.prems(2) \<open>i \<le> n\<close>
    have "(\<forall>i\<in>set (i#xs). i \<noteq> 0 \<longrightarrow> M'' 0 i + M'' i 0 = \<one>)" by auto
    moreover from M''(1) M'(1) FW_not_empty[of v _ M' n]
    have "(\<exists>u. DBM_val_bounded v u M'' n) \<longrightarrow> (\<exists>u. DBM_val_bounded v u M n)" by auto
    ultimately show ?thesis using \<open>cyc_free M'' n\<close> M''(4) by auto
  qed
qed

lemma cyc_free_obtains_valuation:
  "cyc_free M n \<Longrightarrow> \<forall> c. v c \<le> n \<longrightarrow> v c > 0 \<Longrightarrow> \<exists> u. DBM_val_bounded v u M n"
proof -
  assume A: "cyc_free M n" "\<forall> c. v c \<le> n \<longrightarrow> v c > 0"
  let ?M = "FW M n"
  from fw_canonical[of M n] cycle_free_diag_equiv A have "canonical ?M n" by auto
  from FW_cyc_free_preservation[OF A(1) ] have "cyc_free ?M n" .
  have "set [0..<n+1] \<subseteq> {0..n}" "distinct [0..<n+1]" by auto
  from fix_indices[OF this \<open>cyc_free ?M n\<close> \<open>canonical ?M n\<close>]
  obtain M' :: "('a DBMEntry) mat" where M':
    "(\<exists>u. DBM_val_bounded v u M' n) \<longrightarrow> (\<exists>u. DBM_val_bounded v u (FW M n) n)"
    "\<forall>i\<in>set [0..<n + 1]. i \<noteq> 0 \<longrightarrow> M' 0 i + M' i 0 = \<one>" "cyc_free M' n"
  by blast
  let ?M' = "FW M' n"
  have "\<And> i. i \<le> n \<Longrightarrow> i \<in> set [0..<n + 1]" by auto
  with M'(2) have M'_fixed: "\<forall>i\<le>n. i \<noteq> 0 \<longrightarrow> M' 0 i + M' i 0 = \<one>" by fastforce
  from fw_canonical[of M' n] cycle_free_diag_equiv M'(3) have "canonical ?M' n" by blast
  from FW_fixed_preservation[OF _ _ this FW_cyc_free_preservation[OF M'(3)]] M'_fixed
  have fixed: "\<forall>i\<le>n. i \<noteq> 0 \<longrightarrow> ?M' 0 i + ?M' i 0 = \<one>" by auto
  have *: "\<And>i. i \<le> n \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> \<exists> d. ?M' 0 i = Le (-d) \<and> ?M' i 0 = Le d"
  proof -
    fix i assume i: "i \<le> n" "i \<noteq> 0"
    from i fixed have *:"dbm_add (?M' 0 i) (?M' i 0) = Le 0" by (auto simp add: mult neutral)
    moreover
    { fix a b :: 'a assume "a + b = 0"
      then have "a = -b" by (simp add: eq_neg_iff_add_eq_0) 
    }
    ultimately show "\<exists>d. ?M' 0 i = Le (-d) \<and> ?M' i 0 = Le d"
    by (cases "?M' 0 i"; cases "?M' i 0"; simp)
  qed
  then obtain f where f: "\<forall> i\<le>n. i \<noteq> 0 \<longrightarrow> Le (f i) = ?M' i 0 \<and> Le (- f i) = ?M' 0 i" by metis
  let ?u = "\<lambda> c. f (v c)"
  have "DBM_val_bounded v ?u ?M' n"
  proof (auto simp add: DBM_val_bounded_def, goal_cases)
    case 1
    from cyc_free_diag_dest'[OF FW_cyc_free_preservation[OF M'(3)]] show ?case
    unfolding neutral less_eq by fast
  next
    case (2 c)
    with A(2) have **: "v c > 0" by auto
    with *[OF 2] obtain d where d: "Le (-d) = ?M' 0 (v c)" by auto
    with f 2 ** have "Le (- f (v c)) = Le (- d)" by simp
    then have "- f (v c) \<le> - d" by auto
    from dbm_entry_val.intros(2)[of ?u , OF this] d
    show ?case by auto
  next
    case (3 c)
    with A(2) have **: "v c > 0" by auto
    with *[OF 3] obtain d where d: "Le d = ?M' (v c) 0" by auto
    with f 3 ** have "Le (f (v c)) = Le d" by simp
    then have "f (v c) \<le> d" by auto
    from dbm_entry_val.intros(1)[of ?u, OF this] d
    show ?case by auto
  next
    case (4 c1 c2)
    with A(2) have **: "v c1 > 0" "v c2 > 0" by auto
    with *[OF 4(1)] obtain d1 where d1: "Le d1 = ?M' (v c1) 0" by auto
    with f 4 ** have "Le (f (v c1)) = Le d1" by simp
    then have d1': "f (v c1) = d1" by auto
    from *[OF 4(2)] ** obtain d2 where d2: "Le d2 = ?M' (v c2) 0" by auto
    with f 4 ** have "Le (f (v c2)) = Le d2" by simp
    then have d2': "f (v c2) = d2" by auto
    have "Le d1 \<le> ?M' (v c1) (v c2) + Le d2" using \<open>canonical ?M' n\<close> 4 d1 d2
    by (auto simp add: less_eq mult)
    then show ?case
    proof (cases "?M' (v c1) (v c2)", auto, goal_cases)
      case (1 d)
      from this(1) have "d1 \<le> d + d2" by (auto simp: mult less_eq le_dbm_le)
      then have "d1 - d2 \<le> d" by (simp add: diff_le_eq) 
      then show ?case using d1' d2' by auto
    next
      case (2 d)
      from this(1) have "d1 < d + d2" by (auto simp: mult less_eq dbm_le_def elim: dbm_lt.cases)
      then have "d1 - d2 < d" using diff_less_eq by blast 
      then show ?case using d1' d2' by auto
    qed
  qed
  from M'(1) FW_not_empty[OF this] obtain u where "DBM_val_bounded v u ?M n" by auto
  from FW_not_empty[OF this] show ?thesis by auto
qed

subsection \<open>Floyd-Warshall and Empty DBMs\<close>

theorem FW_detects_empty_zone:
  "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k) \<Longrightarrow> \<forall> c. v c \<le> n \<longrightarrow> v c > 0
  \<Longrightarrow> [FW M n]\<^bsub>v,n\<^esub> = {} \<longleftrightarrow> (\<exists> i\<le>n. (FW M n) i i < Le 0)"
proof
  assume surj_on:"\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" and "\<exists>i\<le>n. (FW M n) i i < Le 0"
  then obtain i where *: "len (FW M n) i i [] < \<one>" "i \<le>n" by (auto simp add: neutral)
  show "[FW M n]\<^bsub>v,n\<^esub> = {}"
  proof (rule ccontr, goal_cases)
    case 1
    then obtain u where "DBM_val_bounded v u (FW M n) n" unfolding DBM_zone_repr_def by auto
    from DBM_val_bounded_neg_cycle[OF this *(2) _ *(1) surj_on] show ?case by auto
  qed
next
  assume surj_on: "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" and empty: "[FW M n]\<^bsub>v,n\<^esub> = {}"
  and    cn: "\<forall> c. v c \<le> n \<longrightarrow> v c > 0"
  show "\<exists> i\<le>n. (FW M n) i i < Le 0"
  proof (rule ccontr, goal_cases)
    case 1
    then have *:"\<forall>i\<le>n. FW M n i i \<ge> \<one>" by (auto simp add: neutral)
    have "cyc_free M n"
    proof (rule ccontr)
      assume "\<not> cyc_free M n"
      then have A: "\<not> cycle_free M n" using cycle_free_diag_equiv by auto
      from FW_neg_cycle_detect[OF A] * show False by auto
    qed
    from FW_cyc_free_preservation[OF this] have "cyc_free (FW M n) n" .
    from cyc_free_obtains_valuation[OF \<open>cyc_free (FW M n) n\<close> cn] empty
    obtain u where "DBM_val_bounded v u (FW M n) n" by blast
    with empty show ?case by (auto simp add: DBM_zone_repr_def)
  qed
qed

(* This definition is "internal" to the theorems for the correctness of the Floyd-Warshall algorithm
   and we want to reuse this as a variable name, so we hide it away *)
hide_const D

subsection \<open>Mixed Corollaries\<close>

lemma cyc_free_not_empty:
  assumes "cyc_free M n" "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c"
  shows "[(M :: ('a :: time) DBM)]\<^bsub>v,n\<^esub> \<noteq> {}"
using cyc_free_obtains_valuation[OF assms(1,2)] unfolding DBM_zone_repr_def by auto

lemma empty_not_cyc_free:
  assumes "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c" "[(M :: ('a :: time) DBM)]\<^bsub>v,n\<^esub> = {}"
  shows "\<not> cyc_free M n"
using assms by (meson cyc_free_not_empty)

lemma not_empty_cyc_free:
  assumes "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists> c. v c = k)" "[(M :: ('a :: time) DBM)]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "cyc_free M n" using DBM_val_bounded_neg_cycle[OF _ _ _ _ assms(1)] assms(2)
unfolding DBM_zone_repr_def by fastforce

lemma neg_cycle_empty:
  assumes "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists> c. v c = k)" "set xs \<subseteq> {0..n}" "i \<le> n" "len M i i xs < \<one>"
  shows "[(M :: ('a :: time) DBM)]\<^bsub>v,n\<^esub> = {}" using assms
by (metis leD not_empty_cyc_free)

abbreviation clock_numbering' :: "('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "clock_numbering' v n \<equiv> \<forall> c. v c > 0 \<and> (\<forall>x. \<forall>y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"

lemma non_empty_dbm_diag_set:
  "clock_numbering' v n \<Longrightarrow> [M]\<^bsub>v,n\<^esub> \<noteq> {} \<Longrightarrow> [M]\<^bsub>v,n\<^esub> = [(\<lambda> i j. if i = j then \<one> else M i j)]\<^bsub>v,n\<^esub>"
proof (auto simp: DBM_zone_repr_def, goal_cases)
  case 1
  { fix c assume A: "v c = 0"
    from 1 have "v c > 0" by auto
    with A have False by auto
  } note * = this
  from 1(1) have [simp]: "Le 0 \<preceq> M 0 0" by (auto simp: DBM_val_bounded_def)
  from 1 show ?case
    apply (auto simp add: DBM_val_bounded_def neutral)
         using * apply meson+
    apply (rename_tac c1 c2)
    apply (case_tac "c1 = c2")
     apply auto
  done
next
  case (2 x xa)
  note G = this
  { fix c assume A: "v c = 0"
    from 2 have "v c > 0" by auto
    with A have False by auto
  } note * = this
  { fix c assume A: "v c \<le> n" "M (v c) (v c) < \<one>"
    with 2(1) have False
      apply (auto simp: neutral DBM_val_bounded_def less)
      apply (cases rule: dbm_lt.cases)
    by fastforce+
  } note ** = this
  from 2(1) have [simp]: "Le 0 \<preceq> M 0 0" by (auto simp: DBM_val_bounded_def)
  from 2 show ?case
  proof (auto simp add: DBM_val_bounded_def neutral, goal_cases)
    case 1 with * show ?case by presburger
    case 2 with * show ?case by presburger
  next
    case (3 c1 c2)
    show ?case
    proof (cases "v c1 = v c2")
      case True
      with 3 have "c1 = c2" by auto
      moreover with **[OF 3(8)] not_less have "M (v c2) (v c2) \<ge> \<one>" by auto
      ultimately show "dbm_entry_val xa (Some c1) (Some c2) (M (v c1) (v c2))" unfolding neutral
      by (cases "M (v c1) (v c2)") (auto simp add: less_eq dbm_le_def, fastforce+)
    next
      case False
      with 3 show ?thesis by presburger
    qed
  qed
qed

lemma non_empty_cycle_free:
  assumes "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
    and "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
  shows "cycle_free M n"
apply (rule ccontr)
apply (drule negative_cycle_dest_diag) 
using DBM_val_bounded_neg_cycle assms unfolding DBM_zone_repr_def by blast

lemma neg_diag_empty:
  assumes "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" "i \<le> n" "M i i < \<one>"
  shows "[M]\<^bsub>v,n\<^esub> = {}"
unfolding DBM_zone_repr_def using DBM_val_bounded_neg_cycle[of v _ M n i "[]"] assms by auto

lemma canonical_empty_zone:
  assumes "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c"
    and "canonical M n"
  shows "[M]\<^bsub>v,n\<^esub> = {} \<longleftrightarrow> (\<exists>i\<le>n. M i i < \<one>)"
using FW_detects_empty_zone[OF assms(1,2), of M] FW_canonical_id[OF assms(3)] unfolding neutral
by simp

end
