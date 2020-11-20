theory Approx_Beta
  imports DBM_Zone_Semantics Regions_Beta Closure
begin

chapter \<open>Correctness of \<open>\<beta>\<close>-approximation from \<open>\<alpha>\<close>-regions\<close>

text \<open>Instantiating real\<close>

instantiation real :: linordered_ab_monoid_add
begin

definition
  neutral_real: "\<one> = (0 :: real)"

instance by standard (auto simp: neutral_real)

end

text \<open>Merging the locales for the two types of regions\<close>

locale Regions =
  fixes X and k :: "'c \<Rightarrow> nat" and v :: "'c \<Rightarrow> nat" and n :: nat and not_in_X
  assumes finite: "finite X"
  assumes clock_numbering: "clock_numbering' v n" "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c \<in> X. v c = k)"
                           "\<forall> c \<in> X. v c \<le> n"
  assumes not_in_X: "not_in_X \<notin> X"
  assumes non_empty: "X \<noteq> {}"
begin

definition \<R>_def:  "\<R> \<equiv> {Regions.region X I r | I r. Regions.valid_region X k I r}"
definition \<R>\<^sub>\<beta>_def: "\<R>\<^sub>\<beta> \<equiv> {Regions_Beta.region X I J r | I J r. Regions_Beta.valid_region X k I J r}"
definition V_def:  "V \<equiv> {v . \<forall> x \<in> X. v x \<ge> 0}"

sublocale alpha_interp: AlphaClosure X k \<R> V by (unfold_locales) (auto simp: finite \<R>_def V_def)

sublocale beta_interp: Beta_Regions' X k \<R>\<^sub>\<beta> V v n not_in_X
using finite non_empty clock_numbering not_in_X by (unfold_locales) (auto simp: \<R>\<^sub>\<beta>_def V_def)

abbreviation "Approx\<^sub>\<beta> \<equiv> beta_interp.Approx\<^sub>\<beta>"

section \<open>Preparing Bouyer's Theorem\<close>

lemma region_dbm:
  assumes "R \<in> \<R>"
  defines "v' \<equiv> \<lambda> i. THE c. c \<in> X \<and> v c = i"
  obtains M
  where"[M]\<^bsub>v,n\<^esub> = R"
  and "\<forall> i \<le> n. \<forall> j \<le> n. M i 0 = \<infinity> \<and> j > 0 \<and> i \<noteq> j\<longrightarrow> M i j = \<infinity> \<and> M j i = \<infinity>"
  and "\<forall> i \<le> n. M i i = Le 0"
  and "\<forall> i \<le> n. \<forall> j \<le> n. i > 0 \<and> j > 0 \<and> M i 0 \<noteq> \<infinity> \<and> M j 0 \<noteq> \<infinity> \<longrightarrow> (\<exists> d :: int.
        (- k (v' j) \<le> d \<and> d \<le> k (v' i) \<and> M i j = Le d \<and> M j i = Le (-d))
      \<or> (- k (v' j) \<le> d - 1 \<and> d \<le> k (v' i) \<and> M i j = Lt d \<and> M j i = Lt (-d + 1)))"
  and "\<forall> i \<le> n. i > 0 \<and> M i 0 \<noteq> \<infinity> \<longrightarrow>
        (\<exists> d :: int. d \<le> k (v' i) \<and> d \<ge> 0
          \<and> (M i 0 = Le d \<and> M 0 i = Le (-d) \<or> M i 0 = Lt d \<and> M 0 i = Lt (-d + 1)))"
  and "\<forall> i \<le> n. i > 0 \<longrightarrow> (\<exists> d :: int. - k (v' i) \<le> d \<and> d \<le> 0 \<and> (M 0 i = Le d \<or> M 0 i = Lt d))"
  and "\<forall> i. \<forall> j. M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>"
  and "\<forall> i \<le> n. \<forall> j \<le> n. M i j \<noteq> \<infinity> \<and> i > 0 \<and> j > 0 \<longrightarrow>
      (\<exists> d:: int. (M i j = Le d \<or> M i j = Lt d) \<and> (- k (v' j)) \<le> d \<and> d \<le> k (v' i))"
proof -
  from assms obtain I r where R: "R = region X I r" "valid_region X k I r" unfolding \<R>_def by blast
  let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Regions.intv.Intv d}"
  define f where "f x = (if isIntv (I x) then Lt (intv_const (I x) + 1)
                 else if isConst (I x) then Le (intv_const (I x))
                 else \<infinity>)" for x
  define g where "g x = (if isIntv (I x) then Lt (- intv_const (I x))
                 else if isConst (I x) then Le (- intv_const (I x))
                 else Lt (- k x))" for x
  define h where "h x y = (if isIntv (I x) \<and> isIntv (I y) then
                      if (y, x) \<in> r \<and> (x, y) \<notin> r then Lt (int (intv_const (I x)) - intv_const (I y) + 1)
                      else if (x, y) \<in> r \<and> (y, x) \<notin> r then Lt (int (intv_const (I x)) - intv_const (I y))
                      else Le (int (intv_const (I x)) - intv_const (I y))
                   else if isConst (I x) \<and> isConst (I y) then Le (int (intv_const (I x)) - intv_const (I y))
                   else if isIntv (I x) \<and> isConst (I y) then Lt (int (intv_const (I x)) + 1 - intv_const (I y))
                   else if isConst (I x) \<and> isIntv (I y) then Lt (int (intv_const (I x)) - intv_const (I y))
                   else \<infinity>)" for x y
  let ?M = "\<lambda> i j. if i = 0 then if j = 0 then Le 0 else g (v' j)
                   else if j = 0 then f (v' i) else if i = j then Le 0 else h (v' i) (v' j)"
  have "[?M]\<^bsub>v,n\<^esub> \<subseteq> R"
  proof
    fix u assume u: "u \<in> [?M]\<^bsub>v,n\<^esub>"
    show "u \<in> R" unfolding R
    proof (standard, goal_cases)
      case 1
      show ?case
      proof
        fix c assume c: "c \<in> X"
        with clock_numbering have c2: "v c \<le> n" "v c > 0" "v' (v c) = c" unfolding v'_def by auto
        with u have "dbm_entry_val u None (Some c) (g c)"
        unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
        then show "0 \<le> u c" by (cases "isIntv (I c)"; cases "isConst (I c)") (auto simp: g_def)
      qed
    next
      case 2
      show ?case
      proof
        fix c assume c: "c \<in> X"
        with clock_numbering have c2: "v c \<le> n" "v c > 0" "v' (v c) = c" unfolding v'_def by auto
        with u have *: "dbm_entry_val u None (Some c) (g c)" "dbm_entry_val u (Some c) None (f c)"
        unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
        show "intv_elem c u (I c)"
        proof (cases "I c")
          case (Const d)
          then have "\<not> isIntv (I c)" "isConst (I c)" by auto
          with * Const show ?thesis unfolding g_def f_def using Const by auto
        next
          case (Intv d)
          then have "isIntv (I c)" "\<not> isConst (I c)" by auto
          with * Intv show ?thesis unfolding g_def f_def by auto
        next
          case (Greater d)
          then have "\<not> isIntv (I c)" "\<not> isConst (I c)" by auto
          with * Greater R(2) c show ?thesis unfolding g_def f_def by fastforce
        qed
      qed
    next
      show "?X\<^sub>0 = ?X\<^sub>0" ..
      show "\<forall>x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)"
      proof (standard, standard)
        fix x y assume A: "x \<in> ?X\<^sub>0" "y \<in> ?X\<^sub>0"
        show "(x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)"
        proof (cases "x = y")
          case True
          have "refl_on ?X\<^sub>0 r" using R(2) by auto
          with A True show ?thesis unfolding refl_on_def by auto
        next
          case False
          from A obtain d d' where AA:
            "I x = Intv d" "I y = Intv d'" "isIntv (I x)" "isIntv (I y)" "\<not> isConst (I x)" "\<not> isConst (I y)"
          by auto
          from A False clock_numbering have B:
            "v x \<le> n" "v x > 0" "v' (v x) = x" "v y \<le> n" "v y > 0" "v' (v y) = y" "v x \<noteq> v y"
          unfolding v'_def by auto
          with u have *: 
            "dbm_entry_val u (Some x) (Some y) (h x y)" "dbm_entry_val u (Some y) (Some x) (h y x)"
            "dbm_entry_val u None (Some x) (g x)" "dbm_entry_val u (Some x) None (f x)"
            "dbm_entry_val u None (Some y) (g y)" "dbm_entry_val u (Some y) None (f y)"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by force+
          show "(x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)"
          proof
            assume C: "(x, y) \<in> r"
            show "frac (u x) \<le> frac (u y)"
            proof (cases "(y, x) \<in> r")
              case False
              with * AA C have **:
                "u x - u y < int d - d'"
                "d < u x" "u x < d + 1" "d' < u y" "u y < d' + 1"
              unfolding f_def g_def h_def by auto
              from nat_intv_frac_decomp[OF **(2,3)] nat_intv_frac_decomp[OF **(4,5)] **(1) show
                "frac (u x) \<le> frac (u y)"
              by simp
            next
              case True
              with * AA C have **:
                "u x - u y \<le> int d - d'"
                "d < u x" "u x < d + 1" "d' < u y" "u y < d' + 1"
              unfolding f_def g_def h_def by auto
              from nat_intv_frac_decomp[OF **(2,3)] nat_intv_frac_decomp[OF **(4,5)] **(1) show
                "frac (u x) \<le> frac (u y)"
              by simp
            qed
          next
            assume "frac (u x) \<le> frac (u y)"
            show "(x, y) \<in> r"
            proof (rule ccontr)
              assume C: "(x,y) \<notin> r"
              moreover from R(2) have "total_on ?X\<^sub>0 r" by auto
              ultimately have "(y, x) \<in> r" using False A unfolding total_on_def by auto
              with *(2-) AA C have **:
                "u y - u x < int d' - d"
                "d < u x" "u x < d + 1" "d' < u y" "u y < d' + 1"
              unfolding f_def g_def h_def by auto
              from nat_intv_frac_decomp[OF **(2,3)] nat_intv_frac_decomp[OF **(4,5)] **(1) have
                "frac (u y) < frac (u x)"
              by simp
              with \<open>frac _ \<le> _\<close> show False by auto
            qed
          qed
        qed
      qed
    qed
  qed
  moreover have "R \<subseteq> [?M]\<^bsub>v,n\<^esub>"
  proof
    fix u assume u: "u \<in> R"
    show "u \<in> [?M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def DBM_val_bounded_def
    proof (safe, goal_cases)
      case 1 then show ?case by auto
    next
      case (2 c)
      with clock_numbering have "c \<in> X" by metis
      with clock_numbering have *: "c \<in> X" "v c > 0" "v' (v c) = c" unfolding v'_def by auto
      with R u have "intv_elem c u (I c)" "valid_intv (k c) (I c)" by auto
      then have "dbm_entry_val u None (Some c) (g c)" unfolding g_def by (cases "I c") auto
      with * show ?case by auto
    next
      case (3 c)
      with clock_numbering have "c \<in> X" by metis
      with clock_numbering have *: "c \<in> X" "v c > 0" "v' (v c) = c" unfolding v'_def by auto
      with R u have "intv_elem c u (I c)" "valid_intv (k c) (I c)" by auto
      then have "dbm_entry_val u (Some c) None (f c)" unfolding f_def by (cases "I c") auto
      with * show ?case by auto
    next
      case (4 c1 c2)
      with clock_numbering have "c1 \<in> X" "c2 \<in> X" by metis+
      with clock_numbering have *:
        "c1 \<in> X" "v c1 > 0" "v' (v c1) = c1" "c2 \<in> X" "v c2 > 0" "v' (v c2) = c2"
      unfolding v'_def by auto
      with R u have
        "intv_elem c1 u (I c1)" "valid_intv (k c1) (I c1)"
        "intv_elem c2 u (I c2)" "valid_intv (k c2) (I c2)"
      by auto
      then have "dbm_entry_val u (Some c1) (Some c2) (h c1 c2)" unfolding h_def
      proof(cases "I c1", cases "I c2", fastforce+, cases "I c2", fastforce, goal_cases)
      case (1 d d')
        then show ?case
        proof (cases "(c2, c1) \<in> r", goal_cases)
          case 1
          show ?case
          proof (cases "(c1, c2) \<in> r")
            case True
            with 1 *(1,4) R(1) u have "frac (u c1) = frac (u c2)" by auto
            with 1 have "u c1 - u c2 = real d - d'" by (fastforce dest: nat_intv_frac_decomp)
            with 1 show ?thesis by auto
          next
            case False with 1 show ?thesis by auto
          qed
        next
          case 2
          show ?case
          proof (cases "c1 = c2")
            case True then show ?thesis by auto
          next
            case False
            with 2 R(2) *(1,4) have "(c1, c2) \<in> r" by (fastforce simp: total_on_def)
            with 2 *(1,4) R(1) u have "frac (u c1) < frac (u c2)" by auto
            with 2 have "u c1 - u c2 < real d - d'" by (fastforce dest: nat_intv_frac_decomp)
            with 2 show ?thesis by auto
          qed
        qed
      qed fastforce+
      then show ?case
      proof (cases "v c1 = v c2", goal_cases)
        case True with * clock_numbering have "c1 = c2" by auto
        then show ?thesis by auto
      next
        case 2 with * show ?case by auto
      qed
    qed
  qed
  ultimately have "[?M]\<^bsub>v,n\<^esub> = R" by blast
  moreover have "\<forall> i \<le> n. \<forall> j \<le> n. ?M i 0 = \<infinity> \<and> j > 0 \<and> i \<noteq> j \<longrightarrow> ?M i j = \<infinity> \<and> ?M j i = \<infinity>"
  unfolding f_def h_def by auto
  moreover have "\<forall> i \<le> n. ?M i i = Le 0" by auto
  moreover
  { fix i j assume A: "i \<le> n" "j \<le> n" "i > 0" "j > 0" "?M i 0 \<noteq> \<infinity>" "?M j 0 \<noteq> \<infinity>"
    with clock_numbering(2) obtain c1 c2 where B: "v c1 = i" "v c2 = j" "c1 \<in> X" "c2 \<in> X" by meson
    with clock_numbering(1) A have C: "v' i = c1" "v' j = c2" unfolding v'_def by force+
    from R(2) B have valid: "valid_intv (k c1) (I c1)" "valid_intv (k c2) (I c2)" by auto
    have "\<exists> d :: int. (- k (v' j) \<le> d \<and> d \<le> k (v' i) \<and> ?M i j = Le d \<and> ?M j i = Le (-d)
      \<or> (- k (v' j) \<le> d - 1 \<and> d \<le> k (v' i) \<and> ?M i j = Lt d \<and> ?M j i = Lt (-d + 1)))"
    proof (cases "i = j")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis
      proof (cases "I c1", goal_cases)
        case 1
        then show ?case
        proof (cases "I c2")
          case Const
          let ?d = "int (intv_const (I c1)) - int (intv_const (I c2))"
          from Const 1 have "isConst (I c1)" "isConst (I c2)" by auto
          with A(1-4) C valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
        next
          case Intv
          let ?d = "int(intv_const (I c1)) - int (intv_const (I c2))"
          from Intv 1 have "isConst (I c1)" "isIntv (I c2)" by auto
          with A(1-4) C valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
        next
          case Greater
          then have "\<not> isIntv (I c2)" "\<not> isConst (I c2)" by auto
          with A 1(1) C have False unfolding f_def by simp
          then show ?thesis by fast
        qed
      next
        case 2
        then show ?case
        proof (cases "I c2")
          case Const
          let ?d = "int (intv_const (I c1)) + 1 - int (intv_const (I c2))"
          from Const 2 have "isIntv (I c1)" "isConst (I c2)" by auto
          with A(1-4) C valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
        next
          case Intv
          with 2 have *: "isIntv (I c1)" "isIntv (I c2)" by auto
          from Intv A(1-4) C show ?thesis apply simp
          proof (standard, goal_cases)
            case 1
            show ?case
            proof (cases "(c2, c1) \<in> r")
              case True
              note T = this
              show ?thesis
              proof (cases "(c1, c2) \<in> r")
                case True
                let ?d = "int (intv_const (I c1)) - int (intv_const (I c2))"
                from True T * valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
              next
                case False
                let ?d = "int (intv_const (I c1)) - int (intv_const (I c2)) + 1"
                from False T * valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
              qed
            next
              case False
              let ?d = "int (intv_const (I c1)) - int (intv_const (I c2))"
              from False * valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
            qed
          qed
        next
          case Greater
          then have "\<not> isIntv (I c2)" "\<not> isConst (I c2)" by auto
          with A 2(1) C have False unfolding f_def by simp
          then show ?thesis by fast
        qed
      next
        case 3
        then have "\<not> isIntv (I c1)" "\<not> isConst (I c1)" by auto
        with A 3(1) C have False unfolding f_def by simp
        then show ?thesis by fast
      qed
    qed
  }
  moreover
  { fix i assume A: "i \<le> n" "i > 0" "?M i 0 \<noteq> \<infinity>"
    with clock_numbering(2) obtain c1 where B: "v c1 = i" "c1 \<in> X" by meson
    with clock_numbering(1) A have C: "v' i = c1" unfolding v'_def by force+
    from R(2) B have valid: "valid_intv (k c1) (I c1)" by auto
    have "\<exists> d :: int. d \<le> k (v' i) \<and> d \<ge> 0
      \<and> (?M i 0 = Le d \<and> ?M 0 i = Le (-d) \<or> ?M i 0 = Lt d \<and> ?M 0 i = Lt (-d + 1))"
    proof (cases "i = 0")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis
      proof (cases "I c1", goal_cases)
        case 1
        let ?d = "int (intv_const (I c1))"
        from 1 have "isConst (I c1)" "\<not> isIntv (I c1)" by auto
        with A C valid show ?thesis unfolding f_def g_def by (intro exI[where x = ?d]) auto
      next
        case 2
        let ?d = "int (intv_const (I c1)) + 1"
        from 2 have "isIntv(I c1)" "\<not> isConst (I c1)" by auto
        with A C valid show ?thesis unfolding f_def g_def by (intro exI[where x = ?d]) auto
      next
        case 3
        then have "\<not> isIntv (I c1)" "\<not> isConst (I c1)" by auto
        with A 3(1) C have False unfolding f_def by simp
        then show ?thesis by fast
      qed
    qed
  }
  moreover
  { fix i assume A: "i \<le> n" "i > 0"
    with clock_numbering(2) obtain c1 where B: "v c1 = i" "c1 \<in> X" by meson
    with clock_numbering(1) A have C: "v' i = c1" unfolding v'_def by force+
    from R(2) B have valid: "valid_intv (k c1) (I c1)" by auto
    have "\<exists> d :: int. - k (v' i) \<le> d \<and> d \<le> 0 \<and> (?M 0 i = Le d \<or> ?M 0 i = Lt d)"
    proof (cases "i = 0")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis
      proof (cases "I c1", goal_cases)
        case 1
        let ?d = "- int (intv_const (I c1))"
        from 1 have "isConst (I c1)" "\<not> isIntv (I c1)" by auto
        with A C valid show ?thesis unfolding f_def g_def by (intro exI[where x = ?d]) auto
      next
        case 2
        let ?d = "- int (intv_const (I c1))"
        from 2 have "isIntv(I c1)" "\<not> isConst (I c1)" by auto
        with A C valid show ?thesis unfolding f_def g_def by (intro exI[where x = ?d]) auto
      next
        case 3
        let ?d = "- (k c1)"
        from 3 have "\<not> isIntv (I c1)" "\<not> isConst (I c1)" by auto
        with A C show ?thesis unfolding g_def by (intro exI[where x = ?d]) auto
      qed
    qed
  }
  moreover have "\<forall> i. \<forall> j. ?M i j \<noteq> \<infinity> \<longrightarrow> get_const (?M i j) \<in> \<int>" unfolding f_def g_def h_def by auto
  moreover have "\<forall> i \<le> n. \<forall> j \<le> n. i > 0 \<and> j > 0 \<and> ?M i j \<noteq> \<infinity>
    \<longrightarrow> (\<exists> d:: int. (?M i j = Le d \<or> ?M i j = Lt d) \<and> (- k (v' j)) \<le> d \<and> d \<le> k (v' i))"
  proof (auto, goal_cases)
    case A: (1 i j)
    with clock_numbering(2) obtain c1 c2 where B: "v c1 = i" "c1 \<in> X" "v c2 = j" "c2 \<in> X" by meson
    with clock_numbering(1) A have C: "v' i = c1" "v' j = c2" unfolding v'_def by force+
    from R(2) B have valid: "valid_intv (k c1) (I c1)" "valid_intv (k c2) (I c2)" by auto
    with A B C show ?case
    proof (simp, goal_cases)
      case 1
      show ?case
      proof (cases "I c1", goal_cases)
        case 1
        then show ?case
        proof (cases "I c2")
          case Const
          let ?d = "int (intv_const (I c1)) - int (intv_const (I c2))"
          from Const 1 have "isConst (I c1)" "isConst (I c2)" by auto
          with A(1-4) C valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
        next
          case Intv
          let ?d = "int(intv_const (I c1)) - int (intv_const (I c2))"
          from Intv 1 have "isConst (I c1)" "isIntv (I c2)" by auto
          with A(1-4) C valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
        next
          case Greater
          then have "\<not> isIntv (I c2)" "\<not> isConst (I c2)" by auto
          with A 1(1) C show ?thesis unfolding h_def by simp
        qed
      next
        case 2
        then show ?case
        proof (cases "I c2")
          case Const
          let ?d = "int (intv_const (I c1)) + 1 - int (intv_const (I c2))"
          from Const 2 have "isIntv (I c1)" "isConst (I c2)" by auto
          with A(1-4) C valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
        next
          case Intv
          with 2 have *: "isIntv (I c1)" "isIntv (I c2)" by auto
          from Intv A(1-4) C show ?thesis
          proof goal_cases
            case 1
            show ?case
            proof (cases "(c2, c1) \<in> r")
              case True
              note T = this
              show ?thesis
              proof (cases "(c1, c2) \<in> r")
                case True
                let ?d = "int (intv_const (I c1)) - int (intv_const (I c2))"
                from True T * valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
              next
                case False
                let ?d = "int (intv_const (I c1)) - int (intv_const (I c2)) + 1"
                from False T * valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
              qed
            next
              case False
              let ?d = "int (intv_const (I c1)) - int (intv_const (I c2))"
              from False * valid show ?thesis unfolding h_def by (intro exI[where x = ?d]) auto
            qed
          qed
        next
          case Greater
          then have "\<not> isIntv (I c2)" "\<not> isConst (I c2)" by auto
          with A 2(1) C show ?thesis unfolding h_def by simp
        qed
      next
        case 3
        then have "\<not> isIntv (I c1)" "\<not> isConst (I c1)" by auto
        with A 3(1) C show ?thesis unfolding h_def by simp
      qed
    qed
  qed
  moreover show ?thesis
    apply (rule that)
           apply (rule calculation(1))
          apply (rule calculation(2))
         apply (rule calculation(3))
        apply (blast intro: calculation)+
     apply (rule calculation(7))
    using calculation(8) apply blast
  done
qed

lemma len_inf_elem:
  "(a, b) \<in> set (arcs i j xs) \<Longrightarrow> M a b = \<infinity> \<Longrightarrow> len M i j xs = \<infinity>"
apply (induction rule: arcs.induct)
  apply (auto simp: mult)
  apply (rename_tac a' b' x xs)
  apply (case_tac "M a' x")
by auto

lemma dbm_add_strict_right_mono_neutral: "a < Le d \<Longrightarrow> a + Le (-d) < Le 0"
unfolding less mult by (cases a) (auto elim!: dbm_lt.cases)

lemma dbm_lt_not_inf_less[intro]: "A \<noteq> \<infinity> \<Longrightarrow> A \<prec> \<infinity>" by (cases A) auto

lemma add_inf[simp]:
  "a + \<infinity> = \<infinity>" "\<infinity> + a = \<infinity>"
unfolding mult by (cases a) auto

lemma inf_lt[simp,dest!]:
  "\<infinity> < x \<Longrightarrow> False"
by (cases x) (auto simp: less)

lemma zone_diag_lt:
  assumes "a \<le> n" "b \<le> n" and C: "v c1 = a" "v c2 = b" and not0: "a > 0" "b > 0"
  shows "[(\<lambda> i j. if i = a \<and> j = b then Lt d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. u c1 - u c2 < d}"
unfolding DBM_zone_repr_def DBM_val_bounded_def
proof (standard, goal_cases)
  case 1
  then show ?case using \<open>a \<le> n\<close> \<open>b \<le> n\<close> C by fastforce
next
  case 2
  then show ?case
  proof (safe, goal_cases)
    case 1 from not0 show ?case unfolding dbm_le_def by auto
  next
    case 2 with not0 show ?case by auto
  next
    case 3 with not0 show ?case by auto
  next
    case (4 u' y z)
    show ?case
    proof (cases "v y = a \<and> v z = b")
      case True
      with 4 clock_numbering C \<open>a \<le> n\<close> \<open>b \<le> n\<close> have "u' y - u' z < d" by metis
      with True show ?thesis by auto
    next
      case False then show ?thesis by auto
    qed
  qed
qed

lemma zone_diag_le:
  assumes "a \<le> n" "b \<le> n" and C: "v c1 = a" "v c2 = b" and not0: "a > 0" "b > 0"
  shows "[(\<lambda> i j. if i = a \<and> j = b then Le d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. u c1 - u c2 \<le> d}"
unfolding DBM_zone_repr_def DBM_val_bounded_def
proof (rule, goal_cases)
  case 1
  then show ?case using \<open>a \<le> n\<close> \<open>b \<le> n\<close> C by fastforce
next
  case 2
  then show ?case
  proof (safe, goal_cases)
    case 1 from not0 show ?case unfolding dbm_le_def by auto
  next
    case 2 with not0 show ?case by auto
  next
    case 3 with not0 show ?case by auto
  next
    case (4 u' y z)
    show ?case
    proof (cases "v y = a \<and> v z = b")
      case True
      with 4 clock_numbering C \<open>a \<le> n\<close> \<open>b \<le> n\<close> have "u' y - u' z \<le> d" by metis
      with True show ?thesis by auto
    next
      case False then show ?thesis by auto
    qed
  qed
qed

lemma zone_diag_lt_2:
  assumes "a \<le> n" and C: "v c = a" and not0: "a > 0"
  shows "[(\<lambda> i j. if i = a \<and> j = 0 then Lt d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. u c < d}"
unfolding DBM_zone_repr_def DBM_val_bounded_def
proof (rule, goal_cases)
  case 1
  then show ?case using \<open>a \<le> n\<close> C by fastforce
next
  case 2
  then show ?case
  proof (safe, goal_cases)
    case 1 from not0 show ?case unfolding dbm_le_def by auto
  next
    case 2 with not0 show ?case by auto
  next
    case (3 u c)
    show ?case
    proof (cases "v c = a")
      case False then show ?thesis by auto
    next
      case True
      with 3 clock_numbering C \<open>a \<le> n\<close> have "u c < d" by metis
      with C show ?thesis by auto
    qed
  next
    case (4 u' y z)
    from clock_numbering(1) have "0 < v z" by auto
    then show ?case by auto
  qed
qed

lemma zone_diag_le_2:
  assumes "a \<le> n" and C: "v c = a" and not0: "a > 0"
  shows "[(\<lambda> i j. if i = a \<and> j = 0 then Le d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. u c \<le> d}"
unfolding DBM_zone_repr_def DBM_val_bounded_def
proof (rule, goal_cases)
  case 1
  then show ?case using \<open>a \<le> n\<close> C by fastforce
next
  case 2
  then show ?case
  proof (safe, goal_cases)
    case 1 from not0 show ?case unfolding dbm_le_def by auto
  next
    case 2 with not0 show ?case by auto
  next
    case (3 u c)
    show ?case
    proof (cases "v c = a")
      case False then show ?thesis by auto
    next
      case True
      with 3 clock_numbering C \<open>a \<le> n\<close> have "u c \<le> d" by metis
      with C show ?thesis by auto
    qed
  next
    case (4 u' y z)
    from clock_numbering(1) have "0 < v z" by auto
    then show ?case by auto
  qed
qed

lemma zone_diag_lt_3:
  assumes "a \<le> n" and C: "v c = a" and not0: "a > 0"
  shows "[(\<lambda> i j. if i = 0 \<and> j = a then Lt d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. - u c < d}"
unfolding DBM_zone_repr_def DBM_val_bounded_def
proof (rule, goal_cases)
  case 1
  then show ?case using \<open>a \<le> n\<close> C by fastforce
next
  case 2
  then show ?case
  proof (safe, goal_cases)
    case 1 from not0 show ?case unfolding dbm_le_def by auto
  next
    case (2 u c)
    show ?case
    proof (cases "v c = a", goal_cases)
      case False then show ?thesis by auto
    next
      case True
      with 2 clock_numbering C \<open>a \<le> n\<close> have "- u c < d" by metis
      with C show ?thesis by auto
    qed
  next
    case (3 u) with not0 show ?case by auto
  next
    case (4 u' y z)
    from clock_numbering(1) have "0 < v y" by auto
    then show ?case by auto
  qed
qed

lemma len_int_closed:
  "\<forall> i j. (M i j :: real) \<in> \<int> \<Longrightarrow> len M i j xs \<in> \<int>"
by (induction xs arbitrary: i) auto

lemma get_const_distr:
  "a \<noteq> \<infinity> \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> get_const (a + b) = get_const a + get_const b"
by (cases a) (cases b, auto simp: mult)+

lemma len_int_dbm_closed:
  "\<forall> (i, j) \<in> set (arcs i j xs). (get_const (M i j) :: real) \<in> \<int> \<and> M i j \<noteq> \<infinity>
  \<Longrightarrow> get_const (len M i j xs) \<in> \<int> \<and> len M i j xs \<noteq> \<infinity>"
by (induction xs arbitrary: i) (auto simp: get_const_distr, simp add: dbm_add_not_inf mult)

lemma zone_diag_le_3:
  assumes "a \<le> n" and C: "v c = a" and not0: "a > 0"
  shows "[(\<lambda> i j. if i = 0 \<and> j = a then Le d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. - u c \<le> d}"
unfolding DBM_zone_repr_def DBM_val_bounded_def
proof (rule, goal_cases)
  case 1
  then show ?case using \<open>a \<le> n\<close> C by fastforce
next
  case 2
  then show ?case
  proof (safe, goal_cases)
    case 1 from not0 show ?case unfolding dbm_le_def by auto
  next
    case (2 u c)
    show ?case
    proof (cases "v c = a")
      case False then show ?thesis by auto
    next
      case True
      with 2 clock_numbering C \<open>a \<le> n\<close> have "- u c \<le> d" by metis
      with C show ?thesis by auto
    qed
  next
    case (3 u) with not0 show ?case by auto
  next
    case (4 u' y z)
    from clock_numbering(1) have "0 < v y" by auto
    then show ?case by auto
  qed
qed

lemma dbm_lt':
  assumes "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "M a b \<le> Lt d" "a \<le> n" "b \<le> n" "v c1 = a" "v c2 = b" "a > 0" "b > 0"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 - u c2 < d}"
proof -
  from assms have "[M]\<^bsub>v,n\<^esub> \<subseteq> [(\<lambda> i j. if i = a \<and> j = b then Lt d else \<infinity>)]\<^bsub>v,n\<^esub>"
    apply safe
    apply (rule DBM_le_subset)
  unfolding less_eq dbm_le_def by auto
  moreover from zone_diag_lt[OF \<open>a \<le> n\<close> \<open>b \<le> n\<close> assms(5-)]
  have "[(\<lambda> i j. if i = a \<and> j = b then Lt d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. u c1 - u c2 < d}" by blast
  moreover from assms have "[M]\<^bsub>v,n\<^esub> \<subseteq> V" by auto
  ultimately show ?thesis by auto
qed

lemma dbm_lt'2:
  assumes "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "M a 0 \<le> Lt d" "a \<le> n" "v c1 = a" "a > 0"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 < d}"
proof -
  from assms(2) have "[M]\<^bsub>v,n\<^esub> \<subseteq> [(\<lambda> i j. if i = a \<and> j = 0 then Lt d else \<infinity>)]\<^bsub>v,n\<^esub>"
    apply safe
    apply (rule DBM_le_subset)
  unfolding less_eq dbm_le_def by auto
  moreover from zone_diag_lt_2[OF \<open>a \<le> n\<close> assms(4,5)]
  have "[(\<lambda> i j. if i = a \<and> j = 0 then Lt d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. u c1 < d}" by blast
  ultimately show ?thesis using assms(1) by auto
qed

lemma dbm_lt'3:
  assumes "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "M 0 a \<le> Lt d" "a \<le> n" "v c1 = a" "a > 0"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. - u c1 < d}"
proof -
  from assms(2) have "[M]\<^bsub>v,n\<^esub> \<subseteq> [(\<lambda> i j. if i = 0 \<and> j = a then Lt d else \<infinity>)]\<^bsub>v,n\<^esub>"
    apply safe
    apply (rule DBM_le_subset)
  unfolding less_eq dbm_le_def by auto
  moreover from zone_diag_lt_3[OF \<open>a \<le> n\<close> assms(4,5)]
  have "[(\<lambda> i j. if i = 0 \<and> j = a then Lt d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. - u c1 < d}" by blast
  ultimately show ?thesis using assms(1) by auto
qed

lemma dbm_le':
  assumes "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "M a b \<le> Le d" "a \<le> n" "b \<le> n" "v c1 = a" "v c2 = b" "a > 0" "b > 0"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 - u c2 \<le> d}"
proof -
  from assms have "[M]\<^bsub>v,n\<^esub> \<subseteq> [(\<lambda> i j. if i = a \<and> j = b then Le d else \<infinity>)]\<^bsub>v,n\<^esub>"
    apply safe
    apply (rule DBM_le_subset)
  unfolding less_eq dbm_le_def by auto
  moreover from zone_diag_le[OF \<open>a \<le> n\<close> \<open>b \<le> n\<close> assms(5-)]
  have "[(\<lambda> i j. if i = a \<and> j = b then Le d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. u c1 - u c2 \<le> d}" by blast
  moreover from assms have "[M]\<^bsub>v,n\<^esub> \<subseteq> V" by auto
  ultimately show ?thesis by auto
qed

lemma dbm_le'2:
  assumes "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "M a 0 \<le> Le d" "a \<le> n" "v c1 = a" "a > 0"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 \<le> d}"
proof -
  from assms(2) have "[M]\<^bsub>v,n\<^esub> \<subseteq> [(\<lambda> i j. if i = a \<and> j = 0 then Le d else \<infinity>)]\<^bsub>v,n\<^esub>"
    apply safe
    apply (rule DBM_le_subset)
  unfolding less_eq dbm_le_def by auto
  moreover from zone_diag_le_2[OF \<open>a \<le> n\<close> assms(4,5)]
  have "[(\<lambda> i j. if i = a \<and> j = 0 then Le d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. u c1 \<le> d}" by blast
  ultimately show ?thesis using assms(1) by auto
qed

lemma dbm_le'3:
  assumes "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "M 0 a \<le> Le d" "a \<le> n" "v c1 = a" "a > 0"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. - u c1 \<le> d}"
proof -
  from assms(2) have "[M]\<^bsub>v,n\<^esub> \<subseteq> [(\<lambda> i j. if i = 0 \<and> j = a then Le d else \<infinity>)]\<^bsub>v,n\<^esub>"
    apply safe
    apply (rule DBM_le_subset)
  unfolding less_eq dbm_le_def by auto
  moreover from zone_diag_le_3[OF \<open>a \<le> n\<close> assms(4,5)]
  have "[(\<lambda> i j. if i = 0 \<and> j = a then Le d else \<infinity>)]\<^bsub>v,n\<^esub> = {u. - u c1 \<le> d}" by blast
  ultimately show ?thesis using assms(1) by auto
qed

lemma int_zone_dbm:
  assumes "\<forall> (_,d) \<in> collect_clock_pairs cc. d \<in> \<int>" "\<forall> c \<in> collect_clks cc. v c \<le> n"
  obtains M where "{u. u \<turnstile> cc} = [M]\<^bsub>v,n\<^esub>" and "dbm_int M n"
using int_zone_dbm[OF _ assms] clock_numbering(1) by auto

lemma non_empty_dbm_diag_set':
  assumes "clock_numbering' v n" "\<forall>i\<le>n. \<forall>j\<le>n. M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>"
          "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  obtains M' where "[M]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub> \<and> (\<forall>i\<le>n. \<forall>j\<le>n. M' i j \<noteq> \<infinity> \<longrightarrow> get_const (M' i j) \<in> \<int>)
    \<and> (\<forall> i \<le> n. M' i i = \<one>)"
proof -
  let ?M = "\<lambda>i j. if i = j then \<one> else M i j"
  from non_empty_dbm_diag_set[OF assms(1,3)] have "[M]\<^bsub>v,n\<^esub> = [?M]\<^bsub>v,n\<^esub>" by auto
  moreover from assms(2) have "\<forall>i\<le>n. \<forall>j\<le>n. ?M i j \<noteq> \<infinity> \<longrightarrow> get_const (?M i j) \<in> \<int>"
  unfolding neutral by auto
  moreover have "\<forall> i \<le> n. ?M i i = \<one>" by auto
  ultimately show ?thesis by (auto intro: that)
qed

lemma dbm_entry_int:
  "x \<noteq> \<infinity> \<Longrightarrow> get_const x \<in> \<int> \<Longrightarrow> \<exists> d :: int. x = Le d \<or> x = Lt d"
apply (cases x) using Ints_cases by auto

abbreviation "vabstr \<equiv> beta_interp.vabstr"


section \<open>Bouyer's Main Theorem\<close>

theorem region_zone_intersect_empty_approx_correct:
  assumes "R \<in> \<R>" "Z \<subseteq> V" "R \<inter> Z = {}" "vabstr Z M"
  shows "R \<inter> Approx\<^sub>\<beta> Z = {}"
proof -
  define v' where "v' i = (THE c. c \<in> X \<and> v c = i)" for i
  from region_dbm[OF assms(1)] obtain M\<^sub>R where M\<^sub>R:
    "[M\<^sub>R]\<^bsub>v,n\<^esub> = R" "\<forall>i\<le>n. \<forall>j\<le>n. M\<^sub>R i 0 = \<infinity> \<and> 0 < j \<and> i \<noteq> j \<longrightarrow> M\<^sub>R i j = \<infinity> \<and> M\<^sub>R j i = \<infinity>"
    "\<forall>i\<le>n. M\<^sub>R i i = Le 0"
    "\<forall>i\<le>n. \<forall>j\<le>n. 0 < i \<and> 0 < j \<and> M\<^sub>R i 0 \<noteq> \<infinity> \<and> M\<^sub>R j 0 \<noteq> \<infinity> \<longrightarrow>
     (\<exists>d. - int (k (THE c. c \<in> X \<and> v c = j)) \<le> d \<and> d \<le> int (k (THE c. c \<in> X \<and> v c = i))
          \<and> M\<^sub>R i j = Le d \<and> M\<^sub>R j i = Le (real_of_int (- d))
        \<or> - int (k (THE c. c \<in> X \<and> v c = j)) \<le> d - 1 \<and> d \<le> int (k (THE c. c \<in> X \<and> v c = i))
          \<and> M\<^sub>R i j = Lt d \<and> M\<^sub>R j i = Lt (real_of_int (- d + 1)))"
    "\<forall>i\<le>n. 0 < i \<and> M\<^sub>R i 0 \<noteq> \<infinity> \<longrightarrow> (\<exists>d\<le>int (k (THE c. c \<in> X \<and> v c = i)). d \<ge> 0 \<and>
      (M\<^sub>R i 0 = Le d \<and> M\<^sub>R 0 i = Le (real_of_int (- d)) \<or> M\<^sub>R i 0 = Lt d \<and> M\<^sub>R 0 i = Lt (real_of_int (- d + 1))))"
    "\<forall>i\<le>n. 0 < i \<longrightarrow> (\<exists>d\<ge>- int (k (THE c. c \<in> X \<and> v c = i)). d \<le> 0 \<and> (M\<^sub>R 0 i = Le d \<or> M\<^sub>R 0 i = Lt d))"
    "\<forall>i j. M\<^sub>R i j \<noteq> \<infinity> \<longrightarrow> get_const (M\<^sub>R i j) \<in> \<int>"
    "\<forall>i\<le>n. \<forall>j\<le>n. M\<^sub>R i j \<noteq> \<infinity> \<and> 0 < i \<and> 0 < j \<longrightarrow> (\<exists>d. (M\<^sub>R i j = Le d \<or> M\<^sub>R i j = Lt d)
        \<and> - int (k (THE c. c \<in> X \<and> v c = j)) \<le> d \<and> d \<le> int (k (THE c. c \<in> X \<and> v c = i)))"
  .
  show ?thesis
  proof (cases "R = {}")
    case True then show ?thesis by auto
  next
    case False
    from clock_numbering(2) have cn_weak: "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists> c. v c = k)" by auto
    
    show ?thesis
    proof (cases "Z = {}")
      case True
      then show ?thesis using beta_interp.apx_empty by blast
    next
      case False
      from assms(4) have
        "Z = [M]\<^bsub>v,n\<^esub>" "\<forall> i\<le>n. \<forall> j\<le>n. M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>"
      by auto
      from this(1) non_empty_dbm_diag_set'[OF clock_numbering(1) this(2)] \<open>Z \<noteq> {}\<close> obtain M where M:
        "Z = [M]\<^bsub>v,n\<^esub> \<and> (\<forall>i\<le>n. \<forall>j\<le>n. M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>) \<and> (\<forall>i\<le>n. M i i = \<one>)"
      by auto
      with not_empty_cyc_free[OF cn_weak] False have "cyc_free M n" by auto
      then have "cycle_free M n" using cycle_free_diag_equiv by auto
      from M have "Z = [FW M n]\<^bsub>v,n\<^esub>" unfolding neutral by (auto intro!: FW_zone_equiv[OF cn_weak])
      moreover from fw_canonical[OF \<open>cycle_free M _\<close>] M have "canonical (FW M n) n" unfolding neutral by auto
      moreover from FW_int_preservation M have
        "\<forall>i\<le>n. \<forall>j\<le>n. FW M n i j \<noteq> \<infinity> \<longrightarrow> get_const (FW M n i j) \<in> \<int>"
      by auto
      ultimately obtain M where M:
        "[M]\<^bsub>v,n\<^esub> = Z" "canonical M n" "\<forall>i\<le>n. \<forall>j\<le>n. M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>"
      by blast
      let ?M = "\<lambda> i j. min (M i j) (M\<^sub>R i j)"
      from M(1) M\<^sub>R(1) assms have "[M]\<^bsub>v,n\<^esub> \<inter> [M\<^sub>R]\<^bsub>v,n\<^esub> = {}" by auto
      moreover from DBM_le_subset[folded less_eq, of n ?M M] have "[?M]\<^bsub>v,n\<^esub> \<subseteq> [M]\<^bsub>v,n\<^esub>" by auto
      moreover from DBM_le_subset[folded less_eq, of n ?M M\<^sub>R] have "[?M]\<^bsub>v,n\<^esub> \<subseteq> [M\<^sub>R]\<^bsub>v,n\<^esub>" by auto
      ultimately have "[?M]\<^bsub>v,n\<^esub> = {}" by blast
      then have "\<not> cyc_free ?M n" using cyc_free_not_empty[of n ?M v] clock_numbering(1) by auto
      then obtain i xs where xs: "i \<le> n" "set xs \<subseteq> {0..n}" "len ?M i i xs < \<one>" by auto
      from this(1,2) canonical_shorten_rotate_neg_cycle[OF M(2) this(2,1,3)] obtain i ys where ys:
        "len ?M i i ys < \<one>"
        "set ys \<subseteq> {0..n}" "successive (\<lambda>(a, b). ?M a b = M a b) (arcs i i ys)" "i \<le> n"
        and distinct: "distinct ys" "i \<notin> set ys"
        and cycle_closes: "ys \<noteq> [] \<longrightarrow> ?M i (hd ys) \<noteq> M i (hd ys) \<or> ?M (last ys) i \<noteq> M (last ys) i"
      by fastforce
      
      have one_M_aux:
        "len ?M i j ys = len M\<^sub>R i j ys" if "\<forall> (a,b) \<in> set (arcs i j ys). M a b \<ge> M\<^sub>R a b" for j
      using that by (induction ys arbitrary: i) (auto simp: min_def)
      have one_M: "\<exists> (a,b) \<in> set (arcs i i ys). M a b < M\<^sub>R a b"
      proof (rule ccontr, goal_cases)
        case 1
        then have "\<forall>(a, b)\<in>set (arcs i i ys). M\<^sub>R a b \<le> M a b" by auto
        from one_M_aux[OF this] have "len ?M i i ys = len M\<^sub>R i i ys" .
        with Nil ys(1) xs(3) have "len M\<^sub>R i i ys < \<one>" by simp
        from DBM_val_bounded_neg_cycle[OF _ \<open>i \<le> n\<close> \<open>set ys \<subseteq> _\<close> this cn_weak]
        have "[M\<^sub>R]\<^bsub>v,n\<^esub> = {}" unfolding DBM_zone_repr_def by auto
        with \<open>R \<noteq> {}\<close> M\<^sub>R(1) show False by auto
      qed
      have one_M_R_aux:
        "len ?M i j ys = len M i j ys" if "\<forall> (a,b) \<in> set (arcs i j ys). M a b \<le> M\<^sub>R a b" for j
      using that by (induction ys arbitrary: i) (auto simp: min_def)
      have one_M_R: "\<exists> (a,b) \<in> set (arcs i i ys). M a b > M\<^sub>R a b"
      proof (rule ccontr, goal_cases)
        case 1
        then have "\<forall>(a, b)\<in>set (arcs i i ys). M\<^sub>R a b \<ge> M a b" by auto
        from one_M_R_aux[OF this] have "len ?M i i ys = len M i i ys" .
        with Nil ys(1) xs(3) have "len M i i ys < \<one>" by simp
        from DBM_val_bounded_neg_cycle[OF _ \<open>i \<le> n\<close> \<open>set ys \<subseteq> _\<close> this cn_weak]
        have "[M]\<^bsub>v,n\<^esub> = {}" unfolding DBM_zone_repr_def by auto
        with \<open>Z \<noteq> {}\<close> M(1) show False by auto
      qed
      
      have 0: "(0,0) \<notin> set (arcs i i ys)"
      proof (cases "ys = []")
        case False with distinct show ?thesis using arcs_distinct1 by blast 
      next
        case True with ys(1) have "?M i i < \<one>" by auto
        then have "M i i < \<one> \<or> M\<^sub>R i i < \<one>" by (simp add: min_less_iff_disj)
        from one_M one_M_R True show ?thesis by auto
      qed
      
      { fix a b assume A: "(a,b) \<in> set (arcs i i ys)"
        assume not0: "a > 0"
        from aux1[OF ys(4,4,2) A] have C2: "a \<le> n" by auto
        then obtain c1 where C: "v c1 = a" "c1 \<in> X"
        using clock_numbering(2) not0 unfolding v'_def by meson
        then have "v' a = c1" using clock_numbering C2 not0 unfolding v'_def by fastforce
        with C C2 have "\<exists> c \<in> X. v c = a \<and> v' a = c" "a \<le> n" by auto
      } note clock_dest_1 = this
      { fix a b assume A: "(a,b) \<in> set (arcs i i ys)"
        assume not0: "b > 0"
        from aux1[OF ys(4,4,2) A] have C2: "b \<le> n" by auto
        then obtain c2 where C: "v c2 = b" "c2 \<in> X"
        using clock_numbering(2) not0 unfolding v'_def by meson
        then have "v' b = c2" using clock_numbering C2 not0 unfolding v'_def by fastforce
        with C C2 have "\<exists> c \<in> X. v c = b \<and> v' b = c" "b \<le> n" by auto
      } note clock_dest_2 = this
      have clock_dest:
        "\<And> a b. (a,b) \<in> set (arcs i i ys) \<Longrightarrow> a > 0 \<Longrightarrow> b > 0 \<Longrightarrow>
          \<exists> c1 \<in> X. \<exists> c2 \<in> X. v c1 = a \<and> v c2 = b \<and> v' a = c1 \<and> v' b = c2 &&& a \<le> n &&& b \<le> n"
      using clock_dest_1 clock_dest_2 by (auto) presburger
      
      { fix a assume A: "(a,0) \<in> set (arcs i i ys)"
        assume not0: "a > 0"
        assume bounded: "M\<^sub>R a 0 \<noteq> \<infinity>" 
        assume lt: "M a 0 < M\<^sub>R a 0"
        from clock_dest_1[OF A not0] obtain c1 where C:
          "v c1 = a" "c1 \<in> X" "v' a = c1" and C2: "a \<le> n"
        by blast
        from C2 not0 bounded M\<^sub>R(5) obtain d :: int where *:
          "d \<le> int (k (v' a))"
          "M\<^sub>R a 0 = Le d \<and> M\<^sub>R 0 a = Le (- d) \<or> M\<^sub>R a 0 = Lt d \<and> M\<^sub>R 0 a = Lt (- d + 1)"
        unfolding v'_def by auto
        with C have **: "d \<le> int (k c1)" by auto
        from *(2) have ?thesis
        proof (standard, goal_cases)
          case 1
          with lt have "M a 0 < Le d" by auto
          then have "M a 0 \<le> Lt d" unfolding less less_eq dbm_le_def by (fastforce elim!: dbm_lt.cases)
          from dbm_lt'2[OF assms(2)[folded M(1)] this C2 C(1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 < d}"
          by auto
          from beta_interp.\<beta>_boundedness_lt'[OF ** C(2) this] have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 < d}"
          .
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c1) None (M\<^sub>R a 0)" "dbm_entry_val u None (Some c1) (M\<^sub>R 0 a)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            then have "u c1 = d" using 1 by auto
            then have "u \<notin> {u \<in> V. u c1 < d}" by auto
          }
          ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
        next
          case 2
          from 2 lt have "M a 0 \<noteq> \<infinity>" by auto
          with dbm_entry_int[OF this] M(3) \<open>a \<le> n\<close>
          obtain d' :: int where d': "M a 0 = Le d' \<or> M a 0 = Lt d'" by auto
          then have "M a 0 \<le> Le (d - 1)" using lt 2
          apply (auto simp: less_eq dbm_le_def less)
           apply (cases rule: dbm_lt.cases)
                 apply auto
          apply rule
          apply (cases rule: dbm_lt.cases)
          by auto
          with lt have "M a 0 \<le> Le (d - 1)" by auto
          from dbm_le'2[OF assms(2)[folded M(1)] this C2 C(1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 \<le> d - 1}"
          by auto
          from beta_interp.\<beta>_boundedness_le'[OF _ C(2) this] ** have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 \<le> d - 1}"
          by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u None (Some c1) (M\<^sub>R 0 a)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            then have "u c1 > d - 1" using 2 by auto
            then have "u \<notin> {u \<in> V. u c1 \<le> d - 1}" by auto
          }
          ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
        qed
      } note bounded_zero_1 = this
      
      { fix a assume A: "(0,a) \<in> set (arcs i i ys)"
        assume not0: "a > 0"
        assume bounded: "M\<^sub>R a 0 \<noteq> \<infinity>" 
        assume lt: "M 0 a < M\<^sub>R 0 a"
        from clock_dest_2[OF A not0] obtain c1 where C:
          "v c1 = a" "c1 \<in> X" "v' a = c1" and C2: "a \<le> n"
        by blast
        from C2 not0 bounded M\<^sub>R(5) obtain d :: int where *:
          "d \<le> int (k (v' a))"
          "M\<^sub>R a 0 = Le d \<and> M\<^sub>R 0 a = Le (- d) \<or> M\<^sub>R a 0 = Lt d \<and> M\<^sub>R 0 a = Lt (- d + 1)"
        unfolding v'_def by auto
        with C have **: "- int (k c1) \<le> - d" by auto
        from *(2) have ?thesis
        proof (standard, goal_cases)
          case 1
          with lt have "M 0 a < Le (-d)" by auto
          then have "M 0 a \<le> Lt (-d)" unfolding less less_eq dbm_le_def by (fastforce elim!: dbm_lt.cases)
          from dbm_lt'3[OF assms(2)[folded M(1)] this C2 C(1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. d < u c1}"
          by auto
          from beta_interp.\<beta>_boundedness_gt'[OF _ C(2) this] ** have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. - u c1 < -d}"
          by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c1) None (M\<^sub>R a 0)" "dbm_entry_val u None (Some c1) (M\<^sub>R 0 a)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with 1 have "u \<notin> {u \<in> V. - u c1 < -d}" by auto
          }
          ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
        next
          case 2
          from 2 lt have "M 0 a \<noteq> \<infinity>" by auto
          with dbm_entry_int[OF this] M(3) \<open>a \<le> n\<close>
          obtain d' :: int where d': "M 0 a = Le d' \<or> M 0 a = Lt d'" by auto
          then have "M 0 a \<le> Le (-d)" using lt 2
            apply (auto simp: less_eq dbm_le_def less)
             apply (cases rule: dbm_lt.cases)
                    apply auto
             apply rule
             apply (metis get_const.simps(2) 2 of_int_less_iff of_int_minus zless_add1_eq)
            apply (cases rule: dbm_lt.cases)
            apply auto
            apply (rule dbm_lt.intros(5))
          by (simp add: int_lt_Suc_le)
          from dbm_le'3[OF assms(2)[folded M(1)] this C2 C(1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. d \<le> u c1}"
          by auto
          from beta_interp.\<beta>_boundedness_ge'[OF _ C(2) this] ** have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. - u c1 \<le> -d}"
          by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c1) None (M\<^sub>R a 0)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with 2 have "u \<notin> {u \<in> V. - u c1 \<le> -d}" by auto
          }
          ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
        qed
      } note bounded_zero_2 = this
      
      { fix a b c c1 c2 assume A: "(a,b) \<in> set (arcs i i ys)"
        assume not0: "a > 0" "b > 0"
        assume lt: "M a b = Lt c"
        assume neg: "M a b + M\<^sub>R b a < \<one>"
        assume C: "v c1 = a" "v c2 = b" "c1 \<in> X" "c2 \<in> X" and C2: "a \<le> n" "b \<le> n"
        assume valid: "-k c2 \<le> -get_const (M\<^sub>R b a)" "-get_const (M\<^sub>R b a) \<le> k c1"
        from neg have "M\<^sub>R b a \<noteq> \<infinity>" by auto
        then obtain d where *: "M\<^sub>R b a = Le d \<or> M\<^sub>R b a = Lt d" by (cases "M\<^sub>R b a", auto)+
        with M\<^sub>R(7) \<open>_ _ _ \<noteq> \<infinity>\<close> have "d \<in> \<int>" by fastforce
        with * obtain d :: int where *: "M\<^sub>R b a = Le d \<or> M\<^sub>R b a = Lt d" using Ints_cases by auto 
        with valid have valid: "- k c2 \<le> -d" "-d \<le> k c1" by auto
        from * neg lt have "M a b \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
        by (auto elim!: dbm_lt.cases)
        from dbm_lt'[OF assms(2)[folded M(1)] this C2 C(1,2) not0] have
          "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 - u c2 < - d}"
        .
        from beta_interp.\<beta>_boundedness_diag_lt'[OF valid C(3,4) this] have
          "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 - u c2 < -d}"
        .
        moreover
        { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
          with C C2 have
            "dbm_entry_val u (Some c2) (Some c1) (M\<^sub>R b a)"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
          with * have "u \<notin> {u \<in> V. u c1 - u c2 < -d}" by auto
        }
        ultimately have ?thesis using M\<^sub>R(1) M(1) by auto
      } note neg_sum_lt = this

      { fix a b assume A: "(a,b) \<in> set (arcs i i ys)"
        assume not0: "a > 0" "b > 0"
        assume neg: "M a b + M\<^sub>R b a < \<one>"
        from clock_dest[OF A not0] obtain c1 c2 where
          C: "v c1 = a" "v c2 = b" "c1 \<in> X" "c2 \<in> X" and C2: "a \<le> n" "b \<le> n"
        by blast
        then have C3: "v' a = c1" "v' b = c2" unfolding v'_def using clock_numbering(1) by auto
        from neg have inf: "M a b \<noteq> \<infinity>" "M\<^sub>R b a \<noteq> \<infinity>" by auto
        from M\<^sub>R(8) inf not0 C(3,4) C2 C3 obtain d :: int where d:
          "M\<^sub>R b a = Le d \<or> M\<^sub>R b a = Lt d" "- int (k c1) \<le> d" "d \<le> int (k c2)"
        unfolding v'_def by auto
        from inf obtain c where c: "M a b = Le c \<or> M a b = Lt c" by (cases "M a b") auto
        { assume **: "M a b \<le> Lt (-d)"
          from dbm_lt'[OF assms(2)[folded M(1)] this C2 C(1,2) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 - u c2 < (- d)}"
          .
          from beta_interp.\<beta>_boundedness_diag_lt'[OF _ _ C(3,4) this] d have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 - u c2 < -d}"
          by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c2) (Some c1) (M\<^sub>R b a)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with d have "u \<notin> {u \<in> V. u c1 - u c2 < -d}" by auto
          }
          ultimately have ?thesis using M\<^sub>R(1) M(1) by auto
        } note aux = this
        from c have ?thesis
        proof (standard, goal_cases)
          case 2
          with neg d have "M a b \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
          by (auto elim!: dbm_lt.cases)
          with aux show ?thesis .
        next
          case 1
          note A = this
          from d(1) show ?thesis
          proof (standard, goal_cases)
            case 1
            with A neg d have "M a b \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            with aux show ?thesis .
          next
            case 2
            with A neg d have "M a b \<le> Le (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            from dbm_le'[OF assms(2)[folded M(1)] this C2 C(1,2) not0] have
              "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 - u c2 \<le> - d}"
            .
            from beta_interp.\<beta>_boundedness_diag_le'[OF _ _ C(3,4) this] d have
              "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 - u c2 \<le> -d}"
            by auto
            moreover
            { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
              with C C2 have
                "dbm_entry_val u (Some c2) (Some c1) (M\<^sub>R b a)"
              unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
              with A 2 have "u \<notin> {u \<in> V. u c1 - u c2 \<le> -d}" by auto
            }
            ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
          qed
        qed
      } note neg_sum_1 = this

      { fix a b assume A: "(a,0) \<in> set (arcs i i ys)"
        assume not0: "a > 0"
        assume neg: "M a 0 + M\<^sub>R 0 a < \<one>"
        from clock_dest_1[OF A not0] obtain c1 where C: "v c1 = a" "c1 \<in> X" and C2: "a \<le> n" by blast
        with clock_numbering(1) have C3: "v' a = c1" unfolding v'_def by auto
        from neg have inf: "M a 0 \<noteq> \<infinity>" "M\<^sub>R 0 a \<noteq> \<infinity>" by auto
        from M\<^sub>R(6) not0 C2 C3 obtain d :: int where d:
          "M\<^sub>R 0 a = Le d \<or> M\<^sub>R 0 a = Lt d" "- int (k c1) \<le> d" "d \<le> 0"
        unfolding v'_def by auto
        from inf obtain c where c: "M a 0 = Le c \<or> M a 0 = Lt c" by (cases "M a 0") auto
        { assume "M a 0 \<le> Lt (-d)"
          from dbm_lt'2[OF assms(2)[folded M(1)] this C2 C(1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 < - d}"
          .
          from beta_interp.\<beta>_boundedness_lt'[OF _ C(2) this] d have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 < -d}"
          by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u None (Some c1) (M\<^sub>R 0 a)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with d have "u \<notin> {u \<in> V. u c1 < -d}" by auto
          }
          ultimately have ?thesis using M\<^sub>R(1) M(1) by auto
        } note aux = this
        from c have ?thesis
        proof (standard, goal_cases)
          case 2
          with neg d have "M a 0 \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
          by (auto elim!: dbm_lt.cases)
          with aux show ?thesis .
        next
          case 1
          note A = this
          from d(1) show ?thesis
          proof (standard, goal_cases)
            case 1
            with A neg d have "M a 0 \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            with aux show ?thesis .
          next
            case 2
            with A neg d have "M a 0 \<le> Le (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            from dbm_le'2[OF assms(2)[folded M(1)] this C2 C(1) not0] have
              "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 \<le> - d}"
            .
            from beta_interp.\<beta>_boundedness_le'[OF _ C(2) this] d have
              "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 \<le> -d}"
            by auto
            moreover
            { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
              with C C2 have
                "dbm_entry_val u None (Some c1) (M\<^sub>R 0 a)"
              unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
              with A 2 have "u \<notin> {u \<in> V. u c1 \<le> -d}" by auto
            }
            ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
          qed
        qed
      } note neg_sum_1' = this

      { fix a b assume A: "(0,b) \<in> set (arcs i i ys)"
        assume not0: "b > 0"
        assume neg: "M 0 b + M\<^sub>R b 0 < \<one>"
        from clock_dest_2[OF A not0] obtain c2 where
          C:  "v c2 = b" "c2 \<in> X" and C2: "b \<le> n"
        by blast
        with clock_numbering(1) have C3: "v' b = c2" unfolding v'_def by auto
        from neg have "M 0 b \<noteq> \<infinity>" "M\<^sub>R b 0 \<noteq> \<infinity>" by auto
        with M\<^sub>R(5) not0 C2 C3 obtain d :: int where d:
          "M\<^sub>R b 0 = Le d \<or> M\<^sub>R b 0 = Lt d" "d \<le> k c2" 
        unfolding v'_def by fastforce
        from \<open>M 0 b \<noteq> \<infinity>\<close> obtain c where c: "M 0 b = Le c \<or> M 0 b = Lt c" by (cases "M 0 b") auto
        { assume "M 0 b \<le> Lt (-d)"
          from dbm_lt'3[OF assms(2)[folded M(1)] this C2 C(1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c2 > d}"
          by simp
          from beta_interp.\<beta>_boundedness_gt'[OF _ C(2) this] d have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. - u c2 < -d}"
          by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c2) None (M\<^sub>R b 0)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with d have "u \<notin> {u \<in> V. - u c2 < -d}" by auto
          }
          ultimately have ?thesis using M\<^sub>R(1) M(1) by auto
        } note aux = this
        from c have ?thesis
        proof (standard, goal_cases)
          case 2
          with neg d have "M 0 b \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
          by (auto elim!: dbm_lt.cases)
          with aux show ?thesis .
        next
          case A: 1
          from d(1) show ?thesis
          proof (standard, goal_cases)
            case 1
            with A neg have "M 0 b \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            with aux show ?thesis .
          next
            case 2
            with A neg c have "M 0 b \<le> Le (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            from dbm_le'3[OF assms(2)[folded M(1)] this C2 C(1) not0] have
              "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c2 \<ge> d}"
            by simp
            from beta_interp.\<beta>_boundedness_ge'[OF _ C(2) this] d(2) have
              "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. - u c2 \<le> -d}"
            by auto
            moreover
            { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
              with C C2 have
                "dbm_entry_val u (Some c2) None (M\<^sub>R b 0)"
              unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
              with A 2 have "u \<notin> {u \<in> V. - u c2 \<le> -d}" by auto
            }
            ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
          qed
        qed
      } note neg_sum_1'' = this

      { fix a b assume A: "(a,b) \<in> set (arcs i i ys)"
        assume not0: "b > 0" "a > 0"
        assume neg: "M\<^sub>R a b + M b a < \<one>"
        from clock_dest[OF A not0(2,1)] obtain c1 c2 where
          C: "v c1 = a" "v c2 = b" "c1 \<in> X" "c2 \<in> X" and C2: "a \<le> n" "b \<le> n"
        by blast
        then have C3: "v' a = c1" "v' b = c2" unfolding v'_def using clock_numbering(1) by auto
        from neg have inf: "M b a \<noteq> \<infinity>" "M\<^sub>R a b \<noteq> \<infinity>" by auto
        with M\<^sub>R(8) not0 C(3,4) C2 C3 obtain d :: int where d:
          "M\<^sub>R a b = Le d \<or> M\<^sub>R a b = Lt d" "d \<ge> -int (k c2)" "d \<le> int (k c1)" 
        unfolding v'_def by blast
        from inf obtain c where c: "M b a = Le c \<or> M b a = Lt c" by (cases "M b a") auto
        { assume "M b a \<le> Lt (-d)"
          from dbm_lt'[OF assms(2)[folded M(1)] this C2(2,1) C(2,1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c2 - u c1 < - d}"
          .
          from beta_interp.\<beta>_boundedness_diag_lt'[OF _ _ C(4,3) this] d
          have "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c2 - u c1 < -d}" by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c1) (Some c2) (M\<^sub>R a b)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with d have "u \<notin> {u \<in> V. u c2 - u c1 < -d}" by auto
          }
          ultimately have ?thesis using M\<^sub>R(1) M(1) by auto
        } note aux = this
        from c have ?thesis
        proof (standard, goal_cases)
          case 2
          with neg d have "M b a \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
          by (auto elim!: dbm_lt.cases)
          with aux show ?thesis .
        next
          case A: 1
          from d(1) show ?thesis
          proof (standard, goal_cases)
            case 1
            with A neg d have "M b a \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            with aux show ?thesis .
          next
            case 2
            with A neg d have "M b a \<le> Le (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            from dbm_le'[OF assms(2)[folded M(1)] this C2(2,1) C(2,1) not0] have
              "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c2 - u c1 \<le> - d}"
            .
            from beta_interp.\<beta>_boundedness_diag_le'[OF _ _ C(4,3) this] d
            have "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c2 - u c1 \<le> -d}" by auto
            moreover
            { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
              with C C2 have
                "dbm_entry_val u (Some c1) (Some c2) (M\<^sub>R a b)"
              unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
              with A 2 have "u \<notin> {u \<in> V. u c2 - u c1 \<le> -d}" by auto
            }
            ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
          qed
        qed
      } note neg_sum_2 = this

      { fix a b assume A: "(a,0) \<in> set (arcs i i ys)"
        assume not0: "a > 0"
        assume neg: "M\<^sub>R a 0 + M 0 a < \<one>"
        from clock_dest_1[OF A not0] obtain c1 where C: "v c1 = a" "c1 \<in> X" and C2: "a \<le> n" by blast
        with clock_numbering(1) have C3: "v' a = c1" unfolding v'_def by auto
        from neg have inf: "M 0 a \<noteq> \<infinity>" "M\<^sub>R a 0 \<noteq> \<infinity>" by auto
        with M\<^sub>R(5) not0 C2 C3 obtain d :: int where d:
          "M\<^sub>R a 0 = Le d \<or> M\<^sub>R a 0 = Lt d" "d \<le> int (k c1)" "d \<ge> 0"
        unfolding v'_def by auto
        from inf obtain c where c: "M 0 a = Le c \<or> M 0 a = Lt c" by (cases "M 0 a") auto
        { assume "M 0 a \<le> Lt (-d)"
          from dbm_lt'3[OF assms(2)[folded M(1)] this C2 C(1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 > d}"
          by simp
          from beta_interp.\<beta>_boundedness_gt'[OF _ C(2) this] d have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 > d}"
          by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c1) None (M\<^sub>R a 0)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with d have "u \<notin> {u \<in> V. u c1 > d}" by auto
          }
          ultimately have ?thesis using M\<^sub>R(1) M(1) by auto
        } note aux = this
        from c have ?thesis
        proof (standard, goal_cases)
          case 2
          with neg d have "M 0 a \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
          by (auto elim!: dbm_lt.cases)
          with aux show ?thesis .
        next
          case A: 1
          from d(1) show ?thesis
          proof (standard, goal_cases)
            case 1
            with A neg d have "M 0 a \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            with aux show ?thesis .
          next
            case 2
            with A neg d have "M 0 a \<le> Le (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            from dbm_le'3[OF assms(2)[folded M(1)] this C2 C(1) not0] have
              "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 \<ge> d}"
            by simp
            from beta_interp.\<beta>_boundedness_ge'[OF _ C(2) this] d have
              "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 \<ge> d}"
            by auto
            moreover
            { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
              with C C2 have
                "dbm_entry_val u (Some c1) None (M\<^sub>R a 0)"
              unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
              with A 2 have "u \<notin> {u \<in> V. u c1 \<ge> d}" by auto
            }
            ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
          qed
        qed
      } note neg_sum_2' = this

      { fix a b assume A: "(0,b) \<in> set (arcs i i ys)"
        assume not0: "b > 0"
        assume neg: "M\<^sub>R 0 b + M b 0 < \<one>"
        from clock_dest_2[OF A not0] obtain c2 where
          C:  "v c2 = b" "c2 \<in> X" and C2: "b \<le> n"
        by blast
        with clock_numbering(1) have C3: "v' b = c2" unfolding v'_def by auto
        from neg have "M b 0 \<noteq> \<infinity>" "M\<^sub>R 0 b \<noteq> \<infinity>" by auto
        with M\<^sub>R(6) not0 C2 C3 obtain d :: int where d:
          "M\<^sub>R 0 b = Le d \<or> M\<^sub>R 0 b = Lt d" "-d \<le> k c2" 
        unfolding v'_def by fastforce
        from \<open>M b 0 \<noteq> \<infinity>\<close> obtain c where c: "M b 0 = Le c \<or> M b 0 = Lt c" by (cases "M b 0") auto
        { assume "M b 0 \<le> Lt (-d)"
          from dbm_lt'2[OF assms(2)[folded M(1)] this C2 C(1) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c2 < - d}"
          by simp
          from beta_interp.\<beta>_boundedness_lt'[OF _ C(2) this] d have
            "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c2 < -d}"
          by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u None (Some c2) (M\<^sub>R 0 b)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with d have "u \<notin> {u \<in> V. u c2 < -d}" by auto
          }
          ultimately have ?thesis using M\<^sub>R(1) M(1) by auto
        } note aux = this
        from c have ?thesis
        proof (standard, goal_cases)
          case 2
          with neg d have "M b 0 \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
          by (auto elim!: dbm_lt.cases)
          with aux show ?thesis .
        next
          case 1
          note A = this
          from d(1) show ?thesis
          proof (standard, goal_cases)
            case 1
            with A neg have "M b 0 \<le> Lt (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            with aux show ?thesis .
          next
            case 2
            with A neg c have "M b 0 \<le> Le (-d)" unfolding less_eq dbm_le_def mult neutral less
            by (auto elim!: dbm_lt.cases)
            from dbm_le'2[OF assms(2)[folded M(1)] this C2 C(1) not0] have
              "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c2 \<le> - d}"
            by simp
            from beta_interp.\<beta>_boundedness_le'[OF _ C(2) this] d(2) have
              "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c2 \<le> -d}"
            by auto
            moreover
            { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
              with C C2 have
                "dbm_entry_val u None (Some c2) (M\<^sub>R 0 b)"
              unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
              with A 2 have "u \<notin> {u \<in> V. u c2 \<le> -d}" by auto
            }
            ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
          qed
        qed
      } note neg_sum_2'' = this

      { fix a b assume A: "(a,b) \<in> set (arcs i i ys)"
        assume not0: "a > 0" "b > 0"
        assume bounded: "M\<^sub>R a 0 \<noteq> \<infinity>" "M\<^sub>R b 0 \<noteq> \<infinity>"
        assume lt: "M a b < M\<^sub>R a b"
        from clock_dest[OF A not0] obtain c1 c2 where
          C: "v c1 = a" "v c2 = b" "c1 \<in> X" "c2 \<in> X" and C2: "a \<le> n" "b \<le> n"
        by blast
        from C C2 clock_numbering(1,3) have C3: "v' b = c2" "v' a = c1" unfolding v'_def by blast+
        with C C2 not0 bounded M\<^sub>R(4) obtain d :: int where *:
          "- int (k c2) \<le> d \<and> d \<le> int (k c1) \<and> M\<^sub>R a b = Le d \<and> M\<^sub>R b a = Le (- d)
         \<or> - int (k c2) \<le> d - 1 \<and> d \<le> int (k c1) \<and> M\<^sub>R a b = Lt d \<and> M\<^sub>R b a = Lt (- d + 1)"
        unfolding v'_def by force
        from * have ?thesis
        proof (standard, goal_cases)
          case 1
          with lt have "M a b < Le d" by auto
          then have "M a b \<le> Lt d" unfolding less less_eq dbm_le_def by (fastforce elim!: dbm_lt.cases)
          from dbm_lt'[OF assms(2)[folded M(1)] this C2 C(1,2) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 - u c2 < d}"
          .
          from beta_interp.\<beta>_boundedness_diag_lt'[OF _ _ C(3,4) this] 1
          have "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 - u c2 < d}" by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c1) (Some c2) (M\<^sub>R a b)" "dbm_entry_val u (Some c2) (Some c1) (M\<^sub>R b a)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with 1 have "u \<notin> {u \<in> V. u c1 - u c2 < d}" by auto
          }
          ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
        next
          case 2
          with lt have "M a b \<noteq> \<infinity>" by auto
          with dbm_entry_int[OF this] M(3) \<open>a \<le> n\<close> \<open>b \<le> n\<close>
          obtain d' :: int where d': "M a b = Le d' \<or> M a b = Lt d'" by auto
          then have "M a b \<le> Le (d - 1)" using lt 2
           apply (auto simp: less_eq dbm_le_def less)
            apply (cases rule: dbm_lt.cases)
                 apply auto
           apply (rule dbm_lt.intros)
           apply (cases rule: dbm_lt.cases)
          by auto
          with lt have "M a b \<le> Le (d - 1)" by auto
          from dbm_le'[OF assms(2)[folded M(1)] this C2 C(1,2) not0] have
            "[M]\<^bsub>v,n\<^esub> \<subseteq> {u \<in> V. u c1 - u c2 \<le> d - 1}"
          .
          from beta_interp.\<beta>_boundedness_diag_le'[OF _ _ C(3,4) this] 2
          have "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) \<subseteq> {u \<in> V. u c1 - u c2 \<le> d - 1}" by auto
          moreover
          { fix u assume u: "u \<in> [M\<^sub>R]\<^bsub>v,n\<^esub>"
            with C C2 have
              "dbm_entry_val u (Some c2) (Some c1) (M\<^sub>R b a)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with 2 have "u \<notin> {u \<in> V. u c1 - u c2 \<le> d - 1}" by auto
          }
          ultimately show ?thesis using M\<^sub>R(1) M(1) by auto
        qed
      } note bounded = this

      { assume not_bounded: "\<forall> (a,b) \<in> set (arcs i i ys). M a b < M\<^sub>R a b \<longrightarrow> M\<^sub>R a 0 = \<infinity> \<or> M\<^sub>R b 0 = \<infinity>"
        have "\<exists> y z zs. set zs \<union> {0, y, z} = set (i # ys) \<and> len ?M 0 0 (y # z # zs) < Le 0 \<and> 
                    (\<forall> (a,b) \<in> set (arcs 0 0 (y # z # zs)). M a b < M\<^sub>R a b \<longrightarrow> a = y \<and> b = z)
                    \<and> M y z < M\<^sub>R y z \<and> distinct (0 # y # z # zs) \<or> ?thesis"
        proof (cases ys)
          case Nil
          show ?thesis
          proof (cases "M i i < M\<^sub>R i i")
            case True
            then have "?M i i = M i i" by (simp add: min.strict_order_iff)
            with Nil ys(1) xs(3) have *: "M i i < \<one>" by simp
            with neg_cycle_empty[OF cn_weak _ \<open>i \<le> n\<close>, of "[]" M] have "[M]\<^bsub>v,n\<^esub> = {}" by auto
            with \<open>Z \<noteq> {}\<close> M(1) show ?thesis by auto
          next
            case False
            then have "?M i i = M\<^sub>R i i" by (simp add: min_absorb2) 
            with Nil ys(1) xs(3) have "M\<^sub>R i i < \<one>" by simp
            with neg_cycle_empty[OF cn_weak _ \<open>i \<le> n\<close>, of "[]" M\<^sub>R] have "[M\<^sub>R]\<^bsub>v,n\<^esub> = {}" by auto
            with \<open>R \<noteq> {}\<close> M\<^sub>R(1) show ?thesis by auto
          qed
        next
          case (Cons w ws)
          note ws = this
          show ?thesis
          proof (cases ws)
            case Nil
            with ws ys xs(3) have *:
              "?M i w + ?M w i < \<one>" "?M w i = M w i \<longrightarrow> ?M i w \<noteq> M i w" "(i, w) \<in> set (arcs i i ys)"
            by auto
            have "R \<inter> Approx\<^sub>\<beta> Z = {}"
            proof (cases "?M w i = M w i")
              case True
              with *(2) have "?M i w = M\<^sub>R i w" unfolding min_def by auto
              with *(1) True have neg: "M\<^sub>R i w + M w i < \<one>" by auto
              show ?thesis
              proof (cases "i = 0")
                case True
                show ?thesis
                proof (cases "w = 0")
                  case True with 0 \<open>i = 0\<close> *(3) show ?thesis by auto
                next
                  case False with \<open>i = 0\<close> neg_sum_2'' *(3) neg show ?thesis by blast
                qed
              next
                case False
                show ?thesis
                proof (cases "w = 0")
                  case True with \<open>i \<noteq> 0\<close> neg_sum_2' *(3) neg show ?thesis by blast
                next
                  case False with \<open>i \<noteq> 0\<close> neg_sum_2 *(3) neg show ?thesis by blast
                qed
              qed
            next
              case False
              have "M\<^sub>R w i < M w i"
              proof (rule ccontr, goal_cases)
                case 1
                then have "M\<^sub>R w i \<ge> M w i" by auto
                with False show False unfolding min_def by auto
              qed
              with one_M ws Nil have "M i w < M\<^sub>R i w" by auto
              then have "?M i w = M i w" unfolding min_def by auto
              moreover from False *(2) have "?M w i = M\<^sub>R w i" unfolding min_def by auto
              ultimately have neg: "M i w + M\<^sub>R w i < \<one>" using *(1) by auto
              show ?thesis
              proof (cases "i = 0")
                case True
                show ?thesis
                proof (cases "w = 0")
                  case True with 0 \<open>i = 0\<close> *(3) show ?thesis by auto
                next
                  case False with \<open>i = 0\<close> neg_sum_1'' *(3) neg show ?thesis by blast
                qed
              next
                case False
                show ?thesis
                proof (cases "w = 0")
                  case True with \<open>i \<noteq> 0\<close> neg_sum_1' *(3) neg show ?thesis by blast
                next
                  case False with \<open>i \<noteq> 0\<close> neg_sum_1 *(3) neg show ?thesis by blast
                qed
              qed
            qed
            then show ?thesis by simp
          next
            case zs: (Cons z zs)
            from one_M obtain a b where *:
              "(a,b) \<in> set (arcs i i ys)" "M a b < M\<^sub>R a b"
            by fastforce
            from cycle_rotate_3'[OF _ *(1) ys(3)] ws cycle_closes obtain ws' where ws':
              "len ?M i i ys = len ?M a a (b # ws')" "set (a # b # ws') = set (i # ys)"
              "1 + length ws' = length ys" "set (arcs i i ys) = set (arcs a a (b # ws'))"
              and successive: "successive (\<lambda>(a, b). ?M a b = M a b) (arcs a a (b # ws') @ [(a, b)])"
            by blast
            from successive have successive_arcs:
              "successive (\<lambda>(a, b). ?M a b = M a b) (arcs a b (b # ws' @ [a]))"
            using arcs_decomp_tail by auto
            from ws'(4) one_M_R *(2) obtain c d where **:
              "(c,d) \<in> set (arcs a a (b # ws'))" "M c d > M\<^sub>R c d" "(a,b) \<noteq> (c,d)"
            by fastforce
            from card_distinct[of "a # b # ws'"] distinct_card[of "i # ys"] ws'(2,3) distinct
            have distinct: "distinct (a # b # ws')" by simp
            from ws zs ws'(3) have "ws' \<noteq> []" by auto
            then obtain z zs where z: "ws' = zs @ [z]" by (metis append_butlast_last_id)
            then have "b # ws' = (b # zs) @ [z]" by simp
            with len_decomp[OF this, of ?M a a] arcs_decomp_tail have rotated:
              "len ?M a a (b # ws') = len ?M z z (a # b # zs)"
              "set (arcs a a (b # ws')) = set (arcs z z (a # b # zs))"
            by (auto simp add: comm)
            from ys(1) xs(3) ws'(1) have "len ?M a a (b # ws') < \<one>" by auto
            from ws'(2) ys(2) \<open>i \<le> n\<close> z have n_bounds: "a \<le> n" "b \<le> n" "set ws' \<subseteq> {0..n}" "z \<le> n" by auto
            from * have a_b: "?M a b = M a b" by (simp add: min.strict_order_iff)
            from successive successive_split[of _ "arcs a z (b # zs)" "[(z,a), (a,b)]"]
            have first: "successive (\<lambda>(a, b). ?M a b = M a b) (arcs a z (b # zs))" and
                 last_two: "successive (\<lambda>(a, b). ?M a b = M a b) [(z, a), (a, b)]"
            using arcs_decomp_tail z by auto
            from * not_bounded have not_bounded': "M\<^sub>R a 0 = \<infinity> \<or> M\<^sub>R b 0 = \<infinity>" by auto
            from this(1) have "z = 0"
            proof
              assume inf: "M\<^sub>R b 0 = \<infinity>"
              from a_b successive obtain z where z: "(b,z) \<in> set (arcs b a ws')" "?M b z \<noteq> M b z"
              by (cases ws') auto
              then have "?M b z = M\<^sub>R b z" by (meson min_def)
              from arcs_distinct2[OF _ _ _ _ z(1)] distinct have "b \<noteq> z" by auto
              from z n_bounds have "z \<le> n"
                apply (induction ws' arbitrary: b)
                 apply auto[]
                 apply (rename_tac ws' b)
                apply (case_tac ws')
                 apply auto
              done
              have "M\<^sub>R b z = \<infinity>"
              proof (cases "z = 0")
                case True
                with inf show ?thesis by auto
              next
                case False
                with inf M\<^sub>R(2) \<open>b \<noteq> z\<close> \<open>z \<le> n\<close> \<open>b \<le> n\<close> show ?thesis by blast
              qed
              with \<open>?M b z = M\<^sub>R b z\<close> have "len ?M b a ws' = \<infinity>" by (auto intro: len_inf_elem[OF z(1)])
              then have "\<infinity> = len ?M a a (b # ws')" by simp
              with \<open>len ?M a a _ < \<one>\<close> show ?thesis by auto
            next
              assume inf: "M\<^sub>R a 0 = \<infinity>"
              show "z = 0"
              proof (rule ccontr)
                assume "z \<noteq> 0"
                with last_two a_b have "?M z a = M\<^sub>R z a" by (auto simp: min_def)
                from distinct z have "a \<noteq> z" by auto
                with \<open>z \<noteq> 0\<close> \<open>a \<le> n\<close> \<open>z \<le> n\<close> M\<^sub>R(2) inf have "M\<^sub>R z a = \<infinity>" by blast
                with \<open>?M z a = M\<^sub>R z a\<close> have "len ?M z z (a # b # zs) = \<infinity>" by (auto intro: len_inf_elem)
                with \<open>len ?M a a _ < \<one>\<close> rotated show False by auto
              qed
            qed
            { fix c d assume A: "(c, d) \<in> set (arcs 0 0 (a # b # zs))" "M c d < M\<^sub>R c d"
              then have *: "?M c d = M c d" by (simp add: min.strict_order_iff)
              from rotated(2) A \<open>z = 0\<close> not_bounded ws'(4) have **: "M\<^sub>R c 0 = \<infinity> \<or> M\<^sub>R d 0 = \<infinity>" by auto
              { assume inf: "M\<^sub>R c 0 = \<infinity>"
                fix x assume x: "(x, c) \<in> set (arcs a 0 (b # zs))" "?M x c \<noteq> M x c"
                from x(2) have "?M x c = M\<^sub>R x c" unfolding min_def by auto
                from arcs_elem[OF x(1)] z \<open>z = 0\<close> have
                  "x \<in> set (a # b # ws')" "c \<in> set (a # b # ws')"
                by auto
                with n_bounds have "x \<le> n" "c \<le> n" by auto
                have "x = 0"
                proof (rule ccontr)
                  assume "x \<noteq> 0"
                  from distinct z arcs_distinct1[OF _ _ _ _ x(1)] \<open>z = 0\<close>have "x \<noteq> c" by auto
                  with \<open>x \<noteq> 0\<close> \<open>c \<le> n\<close> \<open>x \<le> n\<close> M\<^sub>R(2) inf have "M\<^sub>R x c = \<infinity>" by blast
                  with \<open>?M x c = M\<^sub>R x c\<close> have
                    "len ?M a 0 (b # zs) = \<infinity>"
                  by (fastforce intro: len_inf_elem[OF x(1)])
                  with \<open>z = 0\<close> have "len ?M z z (a # b # zs) = \<infinity>" by auto
                  with \<open>len ?M a a _ < \<one>\<close> rotated show False by auto
                qed
                with arcs_distinct_dest1[OF _ x(1), of z] z distinct x \<open>z = 0\<close> have False by auto
              } note c_0_inf = this
              have "a = c \<and> b = d"
              proof (cases "(c, d) = (0, a)")
                case True
                with last_two \<open>z = 0\<close> * a_b have False by auto
                then show ?thesis by simp
              next
                case False
                show ?thesis
                proof (rule ccontr, goal_cases)
                  case 1
                  with False A(1) have ***: "(c, d) \<in> set (arcs b 0 zs)" by auto
                  from successive z \<open>z = 0\<close> have
                    "successive (\<lambda>(a, b). ?M a b = M a b) ([(a, b)] @ arcs b 0 zs @ [(0, a), (a, b)])"
                  by (simp add: arcs_decomp)
                  then have ****: "successive (\<lambda>(a, b). ?M a b = M a b) (arcs b 0 zs)"
                  using successive_split[of _ "[(a, b)]" "arcs b 0 zs @ [(0, a), (a, b)]"]
                        successive_split[of _ "arcs b 0 zs" "[(0, a), (a, b)]"]
                  by auto
                  from successive_predecessor[OF *** _ this] successive z
                  obtain x where x: "(x, c) \<in> set (arcs a 0 (b # zs))" "?M x c \<noteq> M x c"
                  proof (cases "c = b")
                    case False
                    then have "zs \<noteq> []" using *** by auto
                    from successive_predecessor[OF *** False **** _ this] * obtain x where x:
                      "(zs = [c] \<and> x = b \<or> (\<exists>ys. zs = c # d # ys \<and> x = b)
                        \<or> (\<exists>ys. zs = ys @ [x, c] \<and> d = 0) \<or> (\<exists>ys ws. zs = ys @ x # c # d # ws))"
                      "?M x c \<noteq> M x c"
                    by blast+
                    from this(1) have "(x, c) \<in> set (arcs a 0 (b # zs))" using arcs_decomp by auto
                    with x(2) show ?thesis by (auto intro: that)
                  next
                    case True
                    have ****: "successive (\<lambda>(a, b). ?M a b = M a b) (arcs a 0 (b # zs))"
                    using first \<open>z = 0\<close> arcs_decomp successive_arcs z by auto 
                    show ?thesis
                    proof (cases zs)
                      case Nil
                      with **** True *** * show ?thesis by (auto intro: that)
                    next
                      case (Cons u us)
                      with *** True distinct z \<open>z = 0\<close> have "distinct (b # u # us @ [0])" by auto
                      from arcs_distinct_fix[OF this] *** True Cons have "d = u" by auto
                      with **** * Cons True show ?thesis by (auto intro: that)
                    qed
                  qed
                  show False
                  proof (cases "d = 0")
                    case True
                    from ** show False
                    proof
                      assume "M\<^sub>R c 0 = \<infinity>" from c_0_inf[OF this x] show False .
                    next
                      assume "M\<^sub>R d 0 = \<infinity>" with \<open>d = 0\<close> M\<^sub>R(3) show False by auto
                    qed
                  next
                    case False with *** have "zs \<noteq> []" by auto
                    from successive_successor[OF \<open>(c,d) \<in> set (arcs b 0 zs)\<close> False **** _ this] *
                    obtain e where
                      "(zs = [d] \<and> e = 0 \<or> (\<exists>ys. zs = d # e # ys) \<or> (\<exists>ys. zs = ys @ [c, d] \<and> e = 0)
                        \<or> (\<exists>ys ws. zs = ys @ c # d # e # ws))" "?M d e \<noteq> M d e"
                    by blast
                    then have e: "(d, e) \<in> set (arcs b 0 zs)" "?M d e \<noteq> M d e" using arcs_decomp by auto
                    from ** show False
                    proof
                      assume inf: "M\<^sub>R d 0 = \<infinity>"
                      from e have "?M d e = M\<^sub>R d e" by (meson min_def)
                      from arcs_distinct2[OF _ _ _ _ e(1)] z \<open>z = 0\<close> distinct have "d \<noteq> e" by auto
                      from z n_bounds have "set zs \<subseteq> {0..n}" by auto
                      with e have "e \<le> n"
                        apply (induction zs arbitrary: d)
                         apply auto
                        apply (case_tac zs)
                         apply auto
                      done
                      from n_bounds z arcs_elem(2)[OF A(1)] have "d \<le> n" by auto
                      have "M\<^sub>R d e = \<infinity>"
                      proof (cases "e = 0")
                        case True
                        with inf show ?thesis by auto
                      next
                        case False
                        with inf M\<^sub>R(2) \<open>d \<noteq> e\<close> \<open>e \<le> n\<close> \<open>d \<le> n\<close> show ?thesis by blast
                      qed
                      with \<open>?M d e = M\<^sub>R d e\<close> have "len ?M b 0 zs = \<infinity>" by (auto intro: len_inf_elem[OF e(1)])
                      with \<open>z = 0\<close> rotated have "\<infinity> = len ?M a a (b # ws')" by simp
                      with \<open>len ?M a a _ < \<one>\<close> show ?thesis by auto
                    next
                      assume "M\<^sub>R c 0 = \<infinity>" from c_0_inf[OF this x] show False .
                    qed
                  qed
                qed
              qed
            }
            then have "\<forall>(c, d)\<in>set (arcs 0 0 (a # b # zs)). M c d < M\<^sub>R c d \<longrightarrow> c = a \<and> d = b"
            by blast
            moreover from ys(1) xs(3) have "len ?M i i ys < Le 0" unfolding neutral by auto
            moreover with rotated ws'(1) have "len ?M z z (a # b # zs) < Le 0" by auto
            moreover from \<open>z = 0\<close> z ws'(2) have "set zs \<union> {0, a, b} = set (i # ys)" by auto
            moreover from \<open>z = 0\<close> distinct z have "distinct (0 # a # b # zs)" by auto
            ultimately show ?thesis using \<open>z = 0\<close> \<open>M a b < M\<^sub>R a b\<close> by blast
          qed
        qed note * = this
        { assume "\<not> ?thesis"
          with * obtain y z zs where *:
            "set zs \<union> {0, y, z} = set (i # ys)" "len ?M 0 0 (y # z # zs) < Le 0"
            "\<forall>(a, b)\<in>set (arcs 0 0 (y # z # zs)). M a b < M\<^sub>R a b \<longrightarrow> a = y \<and> b = z" "M y z < M\<^sub>R y z"
            and distinct': "distinct (0 # y # z # zs)"
          by blast
          then have "y \<noteq> 0" "z \<noteq> 0" by auto
          let ?r = "len M\<^sub>R z 0 zs"
          have "\<forall>(a, b)\<in>set (arcs z 0 zs). ?M a b = M\<^sub>R a b"
          proof (safe, goal_cases)
            case A: (1 a b)
            have "M\<^sub>R a b \<le> M a b"
            proof (rule ccontr, goal_cases)
              case 1
              with *(3) A have "a = y" "b = z" by auto
              with A distinct' arcs_distinct3[OF _ A, of y] show False by auto
            qed
            then show ?case by (simp add: min_def)
          qed
          then have r: "len ?M z 0 zs = ?r" by (induction zs arbitrary: z) auto
          with *(2) have **: "?M 0 y + (?M y z + ?r) < Le 0" by simp
          from M\<^sub>R(1) \<open>R \<noteq> {}\<close> obtain u where u: "DBM_val_bounded v u M\<^sub>R n"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
          from *(1) \<open>i \<le> n\<close> \<open>set ys \<subseteq> _\<close> have "y \<le> n" "z \<le> n" by fastforce+
          from *(1) ys(2,4) have "set zs \<subseteq> {0 ..n}" by auto
          from \<open>y \<le> n\<close> \<open>z \<le> n\<close> clock_numbering(2) \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close> obtain c1 c2 where C:
            "c1 \<in> X" "c2 \<in> X" "v c1 = y" "v c2 = z"
          by blast+
          with clock_numbering(1,3) have C2: "v' y = c1" "v' z = c2" unfolding v'_def by auto
          with C have "v (v' z) = z" by auto
          with DBM_val_bounded_len'1[OF u, of zs "v' z"] have "dbm_entry_val u (Some (v' z)) None ?r"
          using \<open>z \<le> n\<close> clock_numbering(2) \<open>set zs \<subseteq> _\<close> distinct' by force
          from len_inf_elem ** have tl_not_inf: "\<forall>(a, b)\<in>set (arcs z 0 zs). M\<^sub>R a b \<noteq> \<infinity>" by fastforce
          with M\<^sub>R(7) len_int_dbm_closed have "get_const ?r \<in> \<int> \<and> ?r \<noteq> \<infinity>" by blast
          then obtain r :: int where r': "?r = Le r \<or> ?r = Lt r" using Ints_cases by (cases ?r) auto
          from r' \<open>dbm_entry_val _ _ _ _\<close> C C2 have le: "u (v' z) \<le> r" by fastforce
          from arcs_ex_head obtain z' where "(z, z') \<in> set (arcs z 0 zs)" by blast
          then have z':
            "(z, z') \<in> set (arcs 0 0 (y # z # zs))" "(z, z') \<in> set (arcs z 0 zs)"
          by auto
          have "M\<^sub>R z 0 \<noteq> \<infinity>"
          proof (rule ccontr, goal_cases)
            case 1
            then have inf: "M\<^sub>R z 0 = \<infinity>" by auto
            have "M\<^sub>R z z' = \<infinity>"
            proof (cases "z' = 0")
              case True
              with 1 show ?thesis by auto
            next
              case False
              from arcs_elem[OF z'(1)] *(1) \<open>i \<le> n\<close> \<open>set ys \<subseteq> _\<close> have "z' \<le> n" by fastforce
              moreover from distinct' *(1) arcs_distinct1[OF _ _ _ _ z'(1)] have "z \<noteq> z'" by auto
              ultimately show ?thesis using M\<^sub>R(2) \<open>z \<le> n\<close> False inf by blast
            qed
            with tl_not_inf z'(2) show False by auto
          qed
          with M\<^sub>R(5) \<open>z \<noteq> 0\<close> \<open>z \<le> n\<close> obtain d :: int where d:
            "M\<^sub>R z 0 = Le d \<and> M\<^sub>R 0 z = Le (-d) \<or> M\<^sub>R z 0 = Lt d \<and> M\<^sub>R 0 z = Lt (-d + 1)"
            "d \<le> k (v' z)" "0 \<le> d"
          unfolding v'_def by auto
          text \<open>Needs property that len of integral dbm entries is integral and definition of \<open>M_R\<close>\<close>
          from this (1) have rr: "?r \<ge> M\<^sub>R z 0"
          proof (standard, goal_cases)
            case A: 1
            with u \<open>z \<le> n\<close> C C2 have *: "- u (v' z) \<le> -d" unfolding DBM_val_bounded_def by fastforce
            from r' show ?case
            proof (standard, goal_cases)
              case 1
              with le * A show ?case unfolding less_eq dbm_le_def by fastforce
            next
              case 2
              with \<open>dbm_entry_val _ _ _ _\<close> C C2 have "u (v' z) < r" by fastforce
              with * have "r > d" by auto
              with A 2 show ?case unfolding less_eq dbm_le_def by fastforce
            qed
          next
            case A: 2
            with u \<open>z \<le> n\<close> C C2 have *: "- u (v' z) < -d + 1" unfolding DBM_val_bounded_def by fastforce
            from r' show ?case
            proof (standard, goal_cases)
              case 1
              with le * A show ?case unfolding less_eq dbm_le_def by fastforce
            next
              case 2
              with \<open>dbm_entry_val _ _ _ _\<close> C C2 have "u (v' z) \<le> r" by fastforce
              with * have "r \<ge> d" by auto
              with A 2 show ?case unfolding less_eq dbm_le_def by fastforce
            qed
          qed
          with *(3) \<open>y \<noteq> 0\<close> have "M 0 y \<ge> M\<^sub>R 0 y" by fastforce
          then have "?M 0 y = M\<^sub>R 0 y" by (simp add: min.absorb2)
          moreover from *(4) have "?M y z = M y z" unfolding min_def by auto
          ultimately have **: "M\<^sub>R 0 y + (M y z + M\<^sub>R z 0) < Le 0"
          using ** add_mono_right[OF add_mono_right[OF rr], of "M\<^sub>R 0 y" "M y z"] by simp
          from ** have not_inf: "M\<^sub>R 0 y \<noteq> \<infinity>" "M y z \<noteq> \<infinity>" "M\<^sub>R z 0 \<noteq> \<infinity>" by auto
          from M\<^sub>R(6) \<open>y \<noteq> 0\<close> \<open>y \<le> n\<close> obtain c :: int where c:
            "M\<^sub>R 0 y = Le c \<or> M\<^sub>R 0 y = Lt c" "- k (v' y) \<le> c" "c \<le> 0"
          unfolding v'_def by auto
          have ?thesis
          proof (cases "M\<^sub>R 0 y + M\<^sub>R z 0 = Lt (c + d)")
            case True
            from ** have "(M\<^sub>R 0 y + M\<^sub>R z 0) + M y z < Le 0" using comm assoc by metis
            with True have **: "Lt (c + d) + M y z < Le 0" by simp
            then have "M y z \<le> Le (- (c + d))" unfolding less less_eq dbm_le_def mult
            by (cases "M y z") (fastforce elim!: dbm_lt.cases)+
            from dbm_le'[OF assms(2)[folded M(1)] this \<open>y \<le> n\<close> \<open>z \<le> n\<close> C(3,4)] \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close> M
            have subs: "Z \<subseteq> {u \<in> V. u c1 - u c2 \<le> - (c + d)}" by blast
            with c d have "- k (v' z) \<le> - (c + d)" "- (c + d) \<le> k (v' y)" by auto
            with beta_interp.\<beta>_boundedness_diag_le'[OF _ _ C(1,2) subs] C2 have 
              "Approx\<^sub>\<beta> Z \<subseteq> {u \<in> V. u c1 - u c2 \<le> - (c + d)}"
            by auto
            moreover
            { fix u assume u: "u \<in> R"
              with C \<open>y \<le> n\<close> \<open>z \<le> n\<close> M\<^sub>R(1) have
                "dbm_entry_val u (Some c2) None (M\<^sub>R z 0)" "dbm_entry_val u None (Some c1) (M\<^sub>R 0 y)"
              unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
              with True c d(1) have "u \<notin> {u \<in> V. u c1 - u c2 \<le> - (c + d)}" unfolding mult by auto
            }
            ultimately show ?thesis by blast
          next
            case False
            with c d have "M\<^sub>R 0 y + M\<^sub>R z 0 = Le (c + d)" unfolding mult by fastforce
            moreover from ** have "(M\<^sub>R 0 y + M\<^sub>R z 0) + M y z < Le 0" using comm assoc by metis
            ultimately have **: "Le (c + d) + M y z < Le 0" by simp
            then have "M y z \<le> Lt (- (c + d))" unfolding less less_eq dbm_le_def mult
            by (cases "M y z") (fastforce elim!: dbm_lt.cases)+
            from dbm_lt'[OF assms(2)[folded M(1)] this \<open>y \<le> n\<close> \<open>z \<le> n\<close> C(3,4)] \<open>y \<noteq> 0\<close> \<open>z \<noteq> 0\<close> M
            have subs: "Z \<subseteq> {u \<in> V. u c1 - u c2 < - (c + d)}" by auto
            from c d(2-) C2 have "- k c2 \<le> - (c + d)" "- (c + d) \<le> k c1" by auto
            from beta_interp.\<beta>_boundedness_diag_lt'[OF this C(1,2) subs] have 
              "Approx\<^sub>\<beta> Z \<subseteq> {u \<in> V. u c1 - u c2 < - (c + d)}"
            .
            moreover
            { fix u assume u: "u \<in> R"
              with C \<open>y \<le> n\<close> \<open>z \<le> n\<close> M\<^sub>R(1) have
                "dbm_entry_val u (Some c2) None (M\<^sub>R z 0)" "dbm_entry_val u None (Some c1) (M\<^sub>R 0 y)"
              unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
              with c d(1) have "u \<notin> {u \<in> V. u c1 - u c2 < - (c + d)}" by auto
            }
            ultimately show ?thesis by auto
          qed
        } then have ?thesis by auto
      }
      with bounded 0 bounded_zero_1 bounded_zero_2 show ?thesis by blast
    qed
  qed
qed


section \<open>Nice Corollaries of Bouyer's Theorem\<close>

lemma \<R>_V: "\<Union> \<R> = V" unfolding V_def \<R>_def using region_cover[of X _ k] by auto

lemma regions_beta_V: "R \<in> \<R>\<^sub>\<beta> \<Longrightarrow> R \<subseteq> V" unfolding V_def \<R>\<^sub>\<beta>_def by auto

lemma apx_V: "Z \<subseteq> V \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> V"
proof (goal_cases)
  case 1
  from beta_interp.apx_in[OF 1] obtain U where "Approx\<^sub>\<beta> Z = \<Union>U" "U \<subseteq> \<R>\<^sub>\<beta>" by auto
  with regions_beta_V show ?thesis by auto
qed

corollary approx_\<beta>_closure_\<alpha>:
  assumes "Z \<subseteq> V" "vabstr Z M"
  shows "Approx\<^sub>\<beta> Z \<subseteq> Closure\<^sub>\<alpha> Z"
proof -
  note T = region_zone_intersect_empty_approx_correct[OF _ assms(1) _ assms(2-)]
  have "- \<Union>{R \<in> \<R>. R \<inter> Z \<noteq> {}} = \<Union>{R \<in> \<R>. R \<inter> Z = {}} \<union> - V"
  proof (safe, goal_cases)
    case 1 with \<R>_V show False by fast
  next
    case 2 then show ?case using alpha_interp.valid_regions_distinct_spec by fastforce
  next
    case 3 then show ?case using \<R>_V unfolding V_def by blast
  qed
  with T apx_V[OF assms(1)] have "Approx\<^sub>\<beta> Z \<inter> - \<Union>{R \<in> \<R>. R \<inter> Z \<noteq> {}} = {}" by auto
  then show ?thesis unfolding alpha_interp.cla_def by blast
qed

definition "V' \<equiv> {Z. Z \<subseteq> V \<and> (\<exists> M. vabstr Z M)}"

corollary approx_\<beta>_closure_\<alpha>': "Z \<in> V' \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> Closure\<^sub>\<alpha> Z"
using approx_\<beta>_closure_\<alpha> unfolding V'_def by auto

text \<open>We could prove this more directly too (without using \<open>Closure\<^sub>\<alpha> Z\<close>), obviously\<close>
lemma apx_empty_iff:
  assumes "Z \<subseteq> V" "vabstr Z M"
  shows "Z = {} \<longleftrightarrow> Approx\<^sub>\<beta> Z = {}"
using alpha_interp.cla_empty_iff[OF assms(1)] approx_\<beta>_closure_\<alpha>[OF assms] beta_interp.apx_subset
by auto

lemma apx_empty_iff':
  assumes "Z \<in> V'" shows "Z = {} \<longleftrightarrow> Approx\<^sub>\<beta> Z = {}"
using apx_empty_iff assms unfolding V'_def by force

lemma apx_V':
  assumes "Z \<subseteq> V" shows "Approx\<^sub>\<beta> Z \<in> V'"
proof (cases "Z = {}")
  case True
  with beta_interp.apx_empty beta_interp.empty_zone_dbm show ?thesis unfolding V'_def neutral by auto
next
  case False
  then have non_empty: "Approx\<^sub>\<beta> Z \<noteq> {}" using beta_interp.apx_subset by blast
  from beta_interp.apx_in[OF assms] obtain U M where *:
    "Approx\<^sub>\<beta> Z = \<Union>U" "U \<subseteq> \<R>\<^sub>\<beta>" "Z \<subseteq> Approx\<^sub>\<beta> Z" "vabstr (Approx\<^sub>\<beta> Z) M"
  by blast
  moreover from * beta_interp.\<R>_union have "\<Union> U \<subseteq> V" by blast
  ultimately show ?thesis using *(1,4) unfolding V'_def by auto
qed

section \<open>A New Zone Semantics Abstracting with \<open>Approx\<^sub>\<beta>\<close>\<close>

lemma step_z_V':
  assumes "A \<turnstile> \<langle>l,Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle>" "valid_abstraction A X k" "\<forall>c\<in>clk_set A. v c \<le> n" "Z \<in> V'"
  shows "Z' \<in> V'"
proof -
  from assms(3) clock_numbering have numbering: "global_clock_numbering A v n" by metis
  from assms(4) obtain M where M:
    "Z \<subseteq> V" "Z = [M]\<^bsub>v,n\<^esub>" "dbm_int M n"
  unfolding V'_def by auto
  from alpha_interp.step_z_V[OF assms(1) M(1)] M(2) assms(1) step_z_dbm_DBM[OF _ numbering]
       step_z_dbm_preserves_int[OF _ numbering assms(2) M(3)]
  obtain M' where M': "Z' \<subseteq> V" "Z' = [M']\<^bsub>v,n\<^esub>" "dbm_int M' n" by metis
  then show ?thesis unfolding V'_def by blast
qed

lemma steps_z_V':
  "A \<turnstile> \<langle>l,Z\<rangle> \<leadsto>* \<langle>l',Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> \<forall>c\<in>clk_set A. v c \<le> n \<Longrightarrow> Z \<in> V' \<Longrightarrow> Z' \<in> V'"
by (induction rule: steps_z.induct) (auto intro: step_z_V')


subsection \<open>Single Step\<close>

inductive step_z_beta ::
  "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^sub>\<beta> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_beta: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Approx\<^sub>\<beta> Z'\<rangle>"

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l',u'\<rangle>"

declare step_z_beta.intros[intro]

lemma step_z_alpha_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l',Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> \<forall>c\<in>clk_set A. v c \<le> n \<Longrightarrow> Z \<in> V' \<Longrightarrow> Z' \<noteq> {}
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z''\<rangle> \<and> Z'' \<noteq> {}"
 apply (induction rule: step_z_beta.induct)
 apply (frule step_z_V')
    apply assumption+
 apply (rotate_tac 4)
 apply (drule apx_empty_iff')
by blast

lemma step_z_alpha_complete:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> \<forall>c\<in>clk_set A. v c \<le> n \<Longrightarrow> Z \<in> V' \<Longrightarrow> Z' \<noteq> {}
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z''\<rangle> \<and> Z'' \<noteq> {}"
 apply (frule step_z_V')
    apply assumption+
 apply (rotate_tac 4)
 apply (drule apx_empty_iff')
by blast

subsection \<open>Multi step\<close>

inductive
  steps_z_beta :: "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l, Z\<rangle>" |
  step: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l'', Z''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l'', Z''\<rangle>"

declare steps_z_beta.intros[intro]

lemma V'_V: "Z \<in> V' \<Longrightarrow> Z \<subseteq> V" unfolding V'_def by auto

lemma steps_z_beta_V':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow>\<forall>c\<in>clk_set A. v c \<le> n \<Longrightarrow> Z \<in> V' \<Longrightarrow> Z' \<in> V'"
proof (induction rule: steps_z_beta.induct)
  case refl then show ?case by fast
next
  case (step A l Z l' Z' l'' Z'')
  from this(2) obtain Z''' where Z''': "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto> \<langle>l'',Z'''\<rangle>" "Z'' = Approx\<^sub>\<beta> Z'''" by auto
  from step_z_V'[OF this(1)] step have "Z''' \<in> V'" by auto
  from apx_V'[OF V'_V, OF this] Z'''(2) show ?case by auto
qed

lemma alpha_beta_step:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> \<forall>c\<in>clk_set A. v c \<le> n \<Longrightarrow> Z \<in> V'
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l', Z''\<rangle> \<and> Z' \<subseteq> Z''"
  apply (induction rule: step_z_beta.induct)
  apply (frule step_z_V')
    apply assumption+
  apply (rotate_tac 4)
  apply (drule approx_\<beta>_closure_\<alpha>')
  apply auto
done 

subsubsection \<open>Soundness\<close>

lemma alpha_beta_step':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> \<forall>c\<in>clk_set A. v c \<le> n \<Longrightarrow> Z \<in> V' \<Longrightarrow> W \<subseteq> V
  \<Longrightarrow> Z \<subseteq> W \<Longrightarrow> \<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l', W'\<rangle> \<and> Z' \<subseteq> W'"
proof (induction rule: step_z_beta.induct)
  case (step_beta A l Z l' Z')
  from alpha_interp.step_z_mono[OF step_beta(1,6)] obtain W' where W':
    "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',W'\<rangle>" "Z' \<subseteq> W'"
  by blast
  from approx_\<beta>_closure_\<alpha>'[OF step_z_V'[OF step_beta(1-4)]]
       alpha_interp.cla_mono[OF this(2)] this(1)
  show ?case by auto
qed

lemma alpha_beta_steps:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> \<forall>c\<in>clk_set A. v c \<le> n \<Longrightarrow> Z \<in> V'
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l', Z''\<rangle> \<and> Z' \<subseteq> Z''"
proof (induction rule: steps_z_beta.induct)
  case refl then show ?case by auto
next
  case (step A l Z l' Z' l'' Z'')
  then obtain Z''' where *: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z'''\<rangle>" "Z' \<subseteq> Z'''" by auto
  from alpha_beta_step'[OF step.hyps(2) step.prems(1,2) steps_z_beta_V'[OF step.hyps(1) step.prems]
                        alpha_interp.steps_z_alpha_V[OF this(1) V'_V] this(2)] step.prems
  obtain W' where "A \<turnstile> \<langle>l', Z'''\<rangle> \<leadsto>\<^sub>\<alpha> \<langle>l'',W'\<rangle>" "Z'' \<subseteq> W'" by blast
  with * show ?case by auto
qed

corollary steps_z_beta_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle> \<Longrightarrow> \<forall>c\<in>clk_set A. v c \<le> n \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<in> V' \<Longrightarrow> Z' \<noteq> {}
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z''\<rangle> \<and> Z'' \<noteq> {}"
proof (goal_cases)
  case 1
  then have "Z \<subseteq> V" unfolding V'_def by auto
  from alpha_beta_steps[OF 1(1,3,2,4)] obtain Z''' where *:
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<alpha>* \<langle>l',Z'''\<rangle>" "Z' \<subseteq> Z'''"
    by blast
  from alpha_interp.steps_z_alpha_closure_involutive[OF *(1) 1(3) \<open>Z \<subseteq> V\<close>] obtain Z'' where
    Z'': "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z''\<rangle>" "Closure\<^sub>\<alpha> Z''' \<subseteq> Closure\<^sub>\<alpha> Z''" "Z'' \<subseteq> Z'''"
    by blast
  with alpha_interp.closure_subs[OF alpha_interp.steps_z_alpha_V[OF *(1) \<open>Z \<subseteq> V\<close>]] 1(5)
    alpha_interp.cla_empty_iff[OF alpha_interp.steps_z_V, OF this(1) \<open>Z \<subseteq> V\<close>] *(2)
  have "Z'' \<noteq> {}" by auto
  with Z'' show ?thesis by auto
qed

subsubsection \<open>Completeness\<close>

lemma apx_mono:
  "Z' \<subseteq> V \<Longrightarrow> Z \<subseteq> Z' \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> Approx\<^sub>\<beta> Z'"
proof (goal_cases)
  case 1
  with beta_interp.apx_in have
    "Approx\<^sub>\<beta> Z' \<in> {S. \<exists>U M. S = \<Union>U \<and> U \<subseteq> \<R>\<^sub>\<beta> \<and> Z' \<subseteq> S \<and> beta_interp.vabstr S M
                      \<and> beta_interp.normalized M}"
  by auto
  with 1 obtain U M where
    "Approx\<^sub>\<beta> Z' = \<Union>U" "U \<subseteq> \<R>\<^sub>\<beta>" "Z \<subseteq> Approx\<^sub>\<beta> Z'" "beta_interp.vabstr (Approx\<^sub>\<beta> Z') M"
    "beta_interp.normalized M"
  by auto
  with beta_interp.apx_min show ?thesis by auto
qed

lemma step_z_beta_mono:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<Longrightarrow> Z \<subseteq> W \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', W'\<rangle> \<and> Z' \<subseteq> W'"
proof (goal_cases)
  case 1
  then obtain Z'' where *: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z''\<rangle>" "Z' = Approx\<^sub>\<beta> Z''" by auto
  from alpha_interp.step_z_mono[OF this(1) 1(2)] obtain W' where
    "A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l',W'\<rangle>" "Z'' \<subseteq> W'"
  by auto
  moreover with *(2) apx_mono[OF alpha_interp.step_z_V] \<open>W \<subseteq> V\<close> have
    "Z' \<subseteq> Approx\<^sub>\<beta> W'"
  by metis
  ultimately show ?case by blast
qed

lemma steps_z_beta_V: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle> \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<subseteq> V"
proof (induction rule: steps_z_beta.induct)
  case refl then show ?case by blast
next
  case (step A l Z l' Z' l'' Z'')
  then obtain Z''' where "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto> \<langle>l'',Z'''\<rangle>" "Z'' = Approx\<^sub>\<beta> Z'''" by auto
  with alpha_interp.step_z_V[OF this(1)] apx_V step(3,4) show "Z'' \<subseteq> V" by auto
qed

lemma steps_z_beta_mono:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle> \<Longrightarrow> Z \<subseteq> W \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', W'\<rangle> \<and> Z' \<subseteq> W'"
proof (induction rule: steps_z_beta.induct)
  case refl then show ?case by auto
next
  case (step A l Z l' Z' l'' Z'')
  then obtain W' where "A \<turnstile> \<langle>l, W\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',W'\<rangle>" "Z' \<subseteq> W'" by auto
  with step_z_beta_mono[OF step(2) this(2) steps_z_beta_V[OF this(1) step(5)]] show ?case by blast
qed

lemma steps_z_beta_alt:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l'', Z''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l'', Z''\<rangle>"
by (rotate_tac, induction rule: steps_z_beta.induct) blast+

lemma steps_z_beta_complete:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',Z''\<rangle> \<and> Z' \<subseteq> Z''"
proof (induction rule: steps_z.induct)
  case refl with apx_empty_iff show ?case by blast
next
  case (step A l Z l' Z' l'' Z'')
  with alpha_interp.step_z_V[OF this(1,5)] obtain Z''' where
    "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l'',Z'''\<rangle>" "Z'' \<subseteq> Z'''"
  by blast
  with steps_z_beta_mono[OF this(1) beta_interp.apx_subset apx_V[OF alpha_interp.step_z_V[OF step(1,5)]]]
  obtain W' where "A \<turnstile> \<langle>l', Approx\<^sub>\<beta> Z'\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l'', W'\<rangle>" " Z'' \<subseteq> W'" by auto
  moreover with step(1) have "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l'',W'\<rangle>" by (auto intro: steps_z_beta_alt)
  ultimately show ?case by auto
qed

lemma steps_z_beta_complete':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l',Z'\<rangle> \<Longrightarrow> valid_abstraction A X k \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<noteq> {}
  \<Longrightarrow> \<exists> Z''. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l',Z''\<rangle> \<and> Z'' \<noteq> {}"
using steps_z_beta_complete by fast

end

end
