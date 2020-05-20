theory Regions_Beta
imports Misc DBM_Normalization DBM_Operations
begin

chapter \<open>Refinement to \<open>\<beta>\<close>-regions\<close>

section \<open>Definition\<close>

type_synonym 'c ceiling = "('c \<Rightarrow> nat)"

datatype intv =
  Const nat |
  Intv nat |
  Greater nat

datatype intv' =
  Const' int |
  Intv' int |
  Greater' int |
  Smaller' int

type_synonym t = real

instantiation real :: time
begin
  instance proof
    fix x y :: real
    assume "x < y" 
    then show "\<exists>z>x. z < y" using dense_order_class.dense by blast 
  next
    have "(1 :: real) \<noteq> 0" by auto
    then show "\<exists>x. (x::real) \<noteq> 0" ..
  qed
end

inductive valid_intv :: "nat \<Rightarrow> intv \<Rightarrow> bool"
where
  "0 \<le> d \<Longrightarrow> d \<le> c \<Longrightarrow> valid_intv c (Const d)" |
  "0 \<le> d \<Longrightarrow> d < c  \<Longrightarrow> valid_intv c (Intv d)" |
  "valid_intv c (Greater c)"

inductive valid_intv' :: "int \<Rightarrow> int \<Rightarrow> intv' \<Rightarrow> bool"
where
  "valid_intv' l _ (Smaller' (-l))" |
  "-l \<le> d \<Longrightarrow> d \<le> u \<Longrightarrow> valid_intv' l u (Const' d)" |
  "-l \<le> d \<Longrightarrow> d < u  \<Longrightarrow> valid_intv' l u (Intv' d)" |
  "valid_intv' _ u (Greater' u)"

inductive intv_elem :: "'c \<Rightarrow> ('c,t) cval \<Rightarrow> intv \<Rightarrow> bool"
where
  "u x = d \<Longrightarrow> intv_elem x u (Const d)" |
  "d < u x \<Longrightarrow> u x < d + 1 \<Longrightarrow> intv_elem x u (Intv d)" |
  "c < u x \<Longrightarrow> intv_elem x u (Greater c)"

inductive intv'_elem :: "'c \<Rightarrow> 'c \<Rightarrow> ('c,t) cval \<Rightarrow> intv' \<Rightarrow> bool"
where
  "u x - u y < c \<Longrightarrow> intv'_elem x y u (Smaller' c)" |
  "u x - u y = d \<Longrightarrow> intv'_elem x y u (Const' d)" |
  "d < u x - u y \<Longrightarrow> u x - u y < d + 1 \<Longrightarrow> intv'_elem x y u (Intv' d)" |
  "c < u x - u y \<Longrightarrow> intv'_elem x y u (Greater' c)"

abbreviation "total_preorder r \<equiv> refl r \<and> trans r"

inductive isConst :: "intv \<Rightarrow> bool"
where
  "isConst (Const _)"

inductive isIntv :: "intv \<Rightarrow> bool"
where
  "isIntv (Intv _)"

inductive isGreater :: "intv \<Rightarrow> bool"
where
  "isGreater (Greater _)"

declare isIntv.intros[intro!] isConst.intros[intro!] isGreater.intros[intro!]

declare isIntv.cases[elim!] isConst.cases[elim!] isGreater.cases[elim!]

inductive valid_region :: "'c set \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> ('c \<Rightarrow> intv) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> intv') \<Rightarrow> 'c rel \<Rightarrow> bool"
where
  "\<lbrakk>X\<^sub>0 = {x \<in> X. \<exists> d. I x = Intv d}; refl_on X\<^sub>0 r; trans r; total_on X\<^sub>0 r; \<forall> x \<in> X. valid_intv (k x) (I x);
    \<forall> x \<in> X. \<forall> y \<in> X. isGreater (I x) \<or> isGreater (I y) \<longrightarrow> valid_intv' (k y) (k x) (J x y)\<rbrakk>
  \<Longrightarrow> valid_region X k I J r"

inductive_set region for X I J r
where
  "\<forall> x \<in> X. u x \<ge> 0 \<Longrightarrow> \<forall> x \<in> X. intv_elem x u (I x) \<Longrightarrow> X\<^sub>0 = {x \<in> X. \<exists> d. I x = Intv d} \<Longrightarrow>
   \<forall> x \<in> X\<^sub>0. \<forall> y \<in> X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y) \<Longrightarrow>
   \<forall> x \<in> X. \<forall> y \<in> X. isGreater (I x) \<or> isGreater (I y) \<longrightarrow> intv'_elem x y u (J x y)
  \<Longrightarrow> u \<in> region X I J r"


text \<open>Defining the unique element of a partition that contains a valuation\<close>

definition part ("[_]\<^sub>_" [61,61] 61) where "part v \<R> \<equiv> THE R. R \<in> \<R> \<and> v \<in> R"

text \<open>
  First we need to show that the set of regions is a partition of the set of all clock
  assignments. This property is only claimed by P. Bouyer.
\<close>

inductive_cases[elim!]: "intv_elem x u (Const d)"
inductive_cases[elim!]: "intv_elem x u (Intv d)"
inductive_cases[elim!]: "intv_elem x u (Greater d)"
inductive_cases[elim!]: "valid_intv c (Greater d)"
inductive_cases[elim!]: "valid_intv c (Const d)"
inductive_cases[elim!]: "valid_intv c (Intv d)"
inductive_cases[elim!]: "intv'_elem x y u (Const' d)"
inductive_cases[elim!]: "intv'_elem x y u (Intv' d)"
inductive_cases[elim!]: "intv'_elem x y u (Greater' d)"
inductive_cases[elim!]: "intv'_elem x y u (Smaller' d)"
inductive_cases[elim!]: "valid_intv' l u (Greater' d)"
inductive_cases[elim!]: "valid_intv' l u (Smaller' d)"
inductive_cases[elim!]: "valid_intv' l u (Const' d)"
inductive_cases[elim!]: "valid_intv' l u (Intv' d)"

declare valid_intv.intros[intro]
declare valid_intv'.intros[intro]
declare intv_elem.intros[intro]
declare intv'_elem.intros[intro]

declare region.cases[elim]
declare valid_region.cases[elim]

section \<open>Basic Properties\<close>

text \<open>First we show that all valid intervals are distinct\<close>

lemma valid_intv_distinct:
  "valid_intv c I \<Longrightarrow> valid_intv c I' \<Longrightarrow> intv_elem x u I \<Longrightarrow> intv_elem x u I' \<Longrightarrow> I = I'"
by (cases I) (cases I', auto)+

lemma valid_intv'_distinct:
  "-c \<le> d \<Longrightarrow> valid_intv' c d I \<Longrightarrow> valid_intv' c d I' \<Longrightarrow> intv'_elem x y u I \<Longrightarrow> intv'_elem x y u I'
  \<Longrightarrow> I = I'"
by (cases I) (cases I', auto)+

text \<open>From this we show that all valid regions are distinct\<close>

lemma valid_regions_distinct:
  "valid_region X k I J r \<Longrightarrow> valid_region X k I' J' r' \<Longrightarrow> v \<in> region X I J r \<Longrightarrow> v \<in> region X I' J' r'
  \<Longrightarrow> region X I J r = region X I' J' r'"
proof goal_cases
  case 1
  note A = 1
  { fix x assume x: "x \<in> X"
    with A(1) have "valid_intv (k x) (I x)" by auto
    moreover from A(2) x have "valid_intv (k x) (I' x)" by auto
    moreover from A(3) x have "intv_elem x v (I x)" by auto
    moreover from A(4) x have "intv_elem x v (I' x)" by auto
    ultimately have "I x = I' x" using valid_intv_distinct by fastforce
  } note * = this
  { fix x y assume x: "x \<in> X" and y: "y \<in> X" and B: "isGreater (I x) \<or> isGreater (I y)"
    with * have C: "isGreater (I' x) \<or> isGreater (I' y)" by auto
    from A(1) x y B have "valid_intv' (k y) (k x) (J x y)" by fastforce
    moreover from A(2) x y C have "valid_intv' (k y) (k x) (J' x y)" by fastforce
    moreover from A(3) x y B have "intv'_elem x y v (J x y)" by force
    moreover from A(4) x y C have "intv'_elem x y v (J' x y)" by force
    moreover from x y valid_intv'_distinct have "- int (k y) \<le> int (k x)" by simp
    ultimately have "J x y = J' x y" by (blast intro: valid_intv'_distinct)
  } note ** = this
  from A show ?thesis
  proof (auto, goal_cases)
    case (1 u)
    note A = this
    { fix x assume x: "x \<in> X"
      from A(5) x have "intv_elem x u (I x)" by auto
      with * x have "intv_elem x u (I' x)" by auto
    }
    then have "\<forall> x \<in> X. intv_elem x u (I' x)" by auto
    note B = this
    { fix x y assume x: "x \<in> X" and y: "y \<in> X" and B: "isGreater (I' x) \<or> isGreater (I' y)"
      with * have "isGreater (I x) \<or> isGreater (I y)" by auto
      with x y A(5) have "intv'_elem x y u (J x y)" by force
      with **[OF x y \<open>isGreater (I x) \<or> _\<close>] have "intv'_elem x y u (J' x y)" by simp
    } note C = this
    let ?X\<^sub>0 = "{x \<in> X. \<exists> d. I' x = Intv d}"
    { fix x y assume x: "x \<in> ?X\<^sub>0" and y: "y \<in> ?X\<^sub>0"
      have "(x, y) \<in> r' \<longleftrightarrow> frac (u x) \<le> frac (u y)"
      proof
        assume "frac (u x) \<le> frac (u y)"
        with A(5) x y * have "(x,y) \<in> r" by auto
        with A(3) x y * have "frac (v x) \<le> frac (v y)" by auto
        with A(4) x y   show "(x,y) \<in> r'" by auto
      next
        assume "(x,y) \<in> r'"
        with A(4) x y   have "frac (v x) \<le> frac (v y)" by auto
        with A(3) x y * have "(x,y) \<in> r" by auto
        with A(5) x y * show "frac (u x) \<le> frac (u y)" by auto
      qed
    }
    then have *: "\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. (x, y) \<in> r' \<longleftrightarrow> frac (u x) \<le> frac (u y)" by auto
    from A(5) have "\<forall>x\<in>X. 0 \<le> u x" by auto
    from region.intros[OF this B _ *] C show ?case by auto
  next
    case (2 u)
    note A = this
    { fix x assume x: "x \<in> X"
      from A(5) x have "intv_elem x u (I' x)" by auto
      with * x have "intv_elem x u (I x)" by auto
    }
    then have "\<forall> x \<in> X. intv_elem x u (I x)" by auto
    note B = this
    { fix x y assume x: "x \<in> X" and y: "y \<in> X" and B: "isGreater (I x) \<or> isGreater (I y)"
      with * have "isGreater (I' x) \<or> isGreater (I' y)" by auto
      with x y A(5) have "intv'_elem x y u (J' x y)" by force
      with **[OF x y \<open>isGreater (I x) \<or> _\<close>] have "intv'_elem x y u (J x y)" by simp
    } note C = this
    let ?X\<^sub>0 = "{x \<in> X. \<exists> d. I x = Intv d}"
    { fix x y assume x: "x \<in> ?X\<^sub>0" and y: "y \<in> ?X\<^sub>0"
      have "(x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)"
      proof
        assume "frac (u x) \<le> frac (u y)"
        with A(5) x y * have "(x,y) \<in> r'" by auto
        with A(4) x y * have "frac (v x) \<le> frac (v y)" by auto
        with A(3) x y   show "(x,y) \<in> r" by auto
      next
        assume "(x,y) \<in> r"
        with A(3) x y   have "frac (v x) \<le> frac (v y)" by auto
        with A(4) x y * have "(x,y) \<in> r'" by auto
        with A(5) x y * show "frac (u x) \<le> frac (u y)" by auto
      qed
    }
    then have *:"\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)" by auto
    from A(5) have "\<forall>x\<in>X. 0 \<le> u x" by auto
    from region.intros[OF this B _ *] C show ?case by auto
  qed
qed

locale Beta_Regions =
  fixes X k \<R> and V :: "('c, t) cval set"
  defines "\<R> \<equiv> {region X I J r | I J r. valid_region X k I J r}"
  defines "V \<equiv> {v . \<forall> x \<in> X. v x \<ge> 0}"
  assumes finite: "finite X"
  assumes non_empty: "X \<noteq> {}"
begin

lemma \<R>_regions_distinct:
  "\<lbrakk>R \<in> \<R>; v \<in> R; R' \<in> \<R>; R \<noteq> R'\<rbrakk> \<Longrightarrow> v \<notin> R'"
unfolding \<R>_def using valid_regions_distinct by blast

text \<open>
  Secondly, we also need to show that every valuations belongs to a region which is part of
  the partition.
\<close>

definition intv_of :: "nat \<Rightarrow> t \<Rightarrow> intv" where
  "intv_of c v \<equiv>
    if (v > c) then Greater c
    else if (\<exists> x :: nat. x = v) then (Const (nat (floor v)))
    else (Intv (nat (floor v)))"

definition intv'_of :: "int \<Rightarrow> int \<Rightarrow> t \<Rightarrow> intv'" where
  "intv'_of l u v \<equiv>
    if (v > u) then Greater' u
    else if (v < l) then Smaller' l
    else if (\<exists> x :: int. x = v) then (Const' (floor v))
    else (Intv' (floor v))"

lemma region_cover:
  "\<forall> x \<in> X. v x \<ge> 0 \<Longrightarrow> \<exists> R. R \<in> \<R> \<and> v \<in> R"
proof (standard, standard)
  assume assm: "\<forall> x \<in> X. 0 \<le> v x"
  let ?I = "\<lambda> x. intv_of (k x) (v x)"
  let ?J = "\<lambda> x y. intv'_of (-k y) (k x) (v x - v y)"
  let ?X\<^sub>0 = "{x \<in> X. \<exists> d. ?I x = Intv d}"
  let ?r = "{(x,y). x \<in> ?X\<^sub>0 \<and> y \<in> ?X\<^sub>0 \<and> frac (v x) \<le> frac (v y)}"
  { fix x y d assume A: "x \<in> X" "y \<in> X"
    then have "intv'_elem x y v (intv'_of (- int (k y)) (int (k x)) (v x - v y))" unfolding intv'_of_def
    proof (auto, goal_cases)
      case (1 a)
      then have "\<lfloor>v x - v y\<rfloor> = v x - v y" by (metis of_int_floor_cancel)
      then show ?case by auto
    next
      case 2
      then have "\<lfloor>v x - v y\<rfloor> < v x - v y" by (meson eq_iff floor_eq_iff not_less)
      with 2 show ?case by auto
    qed
  } note intro = this
  show "v \<in> region X ?I ?J ?r"
  proof (standard, auto simp: assm intro: intro, goal_cases)
    case (1 x)
    thus ?case unfolding intv_of_def
    proof (auto, goal_cases)
      case (1 a)
      note A = this
      from A(2) have "\<lfloor>v x\<rfloor> = v x" by (metis floor_of_int of_int_of_nat_eq)
      with assm A(1) have "v x = real (nat \<lfloor>v x\<rfloor>)" by auto
      then show ?case by auto
    next
      case 2
      note A = this
      from A(1,2) have "real (nat \<lfloor>v x\<rfloor>) < v x"
      proof -
        have f1: "0 \<le> v x"
          using assm 1 by blast
        have "v x \<noteq> real_of_int (int (nat \<lfloor>v x\<rfloor>))"
          by (metis (no_types) 2(2) of_int_of_nat_eq)
        then show ?thesis
          using f1 by linarith
      qed
      moreover from assm have "v x < real (nat (\<lfloor>v x\<rfloor>) + 1)" by linarith
      ultimately show ?case by auto
    qed
  qed
  { fix x y assume "x \<in> X" "y \<in> X"
    then have "valid_intv' (int (k y)) (int (k x)) (intv'_of (- int (k y)) (int (k x)) (v x - v y))"
    unfolding intv'_of_def
     apply auto
      apply (metis floor_of_int le_floor_iff linorder_not_less of_int_minus of_int_of_nat_eq valid_intv'.simps)
    by (metis floor_less_iff less_eq_real_def not_less of_int_minus of_int_of_nat_eq valid_intv'.intros(3))
  }
  moreover
  { fix x assume x: "x \<in> X"
    then have "valid_intv (k x) (intv_of (k x) (v x))"
    proof (auto simp: intv_of_def, goal_cases)
      case (1 a)
      then show ?case
      by (intro valid_intv.intros(1)) (auto, linarith)
    next
      case 2
      then show ?case
      apply (intro valid_intv.intros(2))
      using assm floor_less_iff nat_less_iff by fastforce+
    qed
  }
  ultimately have "valid_region X k ?I ?J ?r"
  by (intro valid_region.intros, auto simp: refl_on_def trans_def total_on_def)
  then show "region X ?I ?J ?r \<in> \<R>" unfolding \<R>_def by auto
qed

lemma region_cover_V: "v \<in> V \<Longrightarrow> \<exists> R. R \<in> \<R> \<and> v \<in> R" using region_cover unfolding V_def by simp

text \<open>
  Note that we cannot show that every region is non-empty anymore.
  The problem are regions fixing differences between an 'infeasible' constant.
\<close>

text \<open>
  We can show that there is always exactly one region a valid valuation belongs to.
  Note that we do not need non-emptiness for that.
\<close>
lemma regions_partition:
  "\<forall>x \<in> X. 0 \<le> v x \<Longrightarrow> \<exists>! R \<in> \<R>. v \<in> R"
proof goal_cases
  case 1
  note A = this
  with region_cover[OF ] obtain R where R: "R \<in> \<R> \<and> v \<in> R" by fastforce
  moreover 
  { fix R' assume "R' \<in> \<R> \<and> v \<in> R'"
   with R valid_regions_distinct[OF _ _ _ _] have "R' = R" unfolding \<R>_def by blast
  }
  ultimately show ?thesis by auto
qed

lemma region_unique:
  "v \<in> R \<Longrightarrow> R \<in> \<R> \<Longrightarrow> [v]\<^sub>\<R> = R"
proof goal_cases
  case 1
  note A = this
  from A obtain I J r where *:
    "valid_region X k I J r" "R = region X I J r" "v \<in> region X I J r"
  by (auto simp: \<R>_def)
  from this(3) have "\<forall>x\<in>X. 0 \<le> v x" by auto
  from theI'[OF regions_partition[OF this]] obtain I' J' r' where
    v: "valid_region X k I' J' r'" "[v]\<^sub>\<R> = region X I' J' r'" "v \<in> region X I' J' r'"
  unfolding part_def \<R>_def by auto
  from valid_regions_distinct[OF *(1) v(1) *(3) v(3)] v(2) *(2) show ?case by auto
qed

lemma regions_partition':
  "\<forall>x\<in>X. 0 \<le> v x \<Longrightarrow> \<forall>x\<in>X. 0 \<le> v' x \<Longrightarrow> v' \<in> [v]\<^sub>\<R> \<Longrightarrow> [v']\<^sub>\<R> = [v]\<^sub>\<R>"
proof goal_cases
  case 1
  note A = this
  from theI'[OF regions_partition[OF A(1)]] A(3) obtain I J r where
    v: "valid_region X k I J r" "[v]\<^sub>\<R> = region X I J r" "v' \<in> region X I J r"
  unfolding part_def \<R>_def by blast
  from theI'[OF regions_partition[OF A(2)]] obtain I' J' r' where
    v': "valid_region X k I' J' r'" "[v']\<^sub>\<R> = region X I' J' r'" "v' \<in> region X I' J' r'"
  unfolding part_def \<R>_def by auto
  from valid_regions_distinct[OF v'(1) v(1) v'(3) v(3)] v(2) v'(2) show ?case by simp
qed

lemma regions_closed:
  "R \<in> \<R> \<Longrightarrow> v \<in> R \<Longrightarrow> t \<ge> 0 \<Longrightarrow> [v \<oplus> t]\<^sub>\<R> \<in> \<R>"
proof goal_cases
  case 1
  note A = this
  then obtain I J r where "v \<in> region X I J r" unfolding \<R>_def by auto
  from this(1) have "\<forall> x \<in> X. v x \<ge> 0" by auto
  with A(3) have "\<forall> x \<in> X. (v \<oplus> t) x \<ge> 0" unfolding cval_add_def by simp
  from regions_partition[OF this] obtain R' where "R' \<in> \<R>" "(v \<oplus> t) \<in> R'" by auto
  with region_unique[OF this(2,1)] show ?case by auto
qed

lemma regions_closed':
  "R \<in> \<R> \<Longrightarrow> v \<in> R \<Longrightarrow> t \<ge> 0 \<Longrightarrow> (v \<oplus> t) \<in> [v \<oplus> t]\<^sub>\<R>"
proof goal_cases
  case 1
  note A = this
  then obtain I J r where "v \<in> region X I J r" unfolding \<R>_def by auto
  from this(1) have "\<forall> x \<in> X. v x \<ge> 0" by auto
  with A(3) have "\<forall> x \<in> X. (v \<oplus> t) x \<ge> 0" unfolding cval_add_def by simp
  from regions_partition[OF this] obtain R' where "R' \<in> \<R>" "(v \<oplus> t) \<in> R'" by auto
  with region_unique[OF this(2,1)] show ?case by auto
qed

lemma valid_regions_I_cong:
  "valid_region X k I J r \<Longrightarrow> \<forall> x \<in> X. I x = I' x
  \<Longrightarrow> \<forall> x \<in> X. \<forall> y \<in> X. (isGreater (I x) \<or> isGreater (I y)) \<longrightarrow> J x y = J' x y
  \<Longrightarrow> region X I J r = region X I' J' r \<and> valid_region X k I' J' r"
proof (auto, goal_cases)
  case (1 v)
  note A = this
  then have [simp]:
    "\<And> x. x \<in> X \<Longrightarrow> I' x = I x"
    "\<And> x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> isGreater (I x) \<or> isGreater (I y) \<Longrightarrow> J x y = J' x y"
  by metis+
  show ?case
  proof (standard, goal_cases)
    case 1 from A(4) show ?case by auto
  next
    case 2 from A(4) show ?case by auto
  next
    case 3 show "{x \<in> X. \<exists>d. I x = Intv d} = {x \<in> X. \<exists>d. I' x = Intv d}" by auto
  next
    case 4
    let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
    from A(4) show "\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. ((x, y) \<in> r) = (frac (v x) \<le> frac (v y))" by auto
  next
    case 5 from A(4) show ?case by force
  qed
next
  case (2 v)
  note A = this
  then have [simp]:
    "\<And> x. x \<in> X \<Longrightarrow> I' x = I x"
    "\<And> x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> isGreater (I x) \<or> isGreater (I y) \<Longrightarrow> J x y = J' x y"
  by metis+
  show ?case
  proof (standard, goal_cases)
    case 1 from A(4) show ?case by auto
  next
    case 2 from A(4) show ?case by auto
  next
    case 3
    show "{x \<in> X. \<exists>d. I' x = Intv d} = {x \<in> X. \<exists>d. I x = Intv d}" by auto
  next
    case 4
    let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I' x = Intv d}"
    from A(4) show "\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. ((x, y) \<in> r) = (frac (v x) \<le> frac (v y))" by auto
  next
    case 5 from A(4) show ?case by force
  qed
next
  case 3
  note A = this
  then have [simp]:
    "\<And> x. x \<in> X \<Longrightarrow> I' x = I x"
    "\<And> x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> isGreater (I x) \<or> isGreater (I y) \<Longrightarrow> J x y = J' x y"
  by metis+
  show ?case
    apply rule
         apply (subgoal_tac "{x \<in> X. \<exists>d. I x = Intv d} = {x \<in> X. \<exists>d. I' x = Intv d}")
          apply assumption
  using A by force+
qed

fun intv_const :: "intv \<Rightarrow> nat"
where
  "intv_const (Const d) = d" |
  "intv_const (Intv d) = d"  |
  "intv_const (Greater d) = d"

fun intv'_const :: "intv' \<Rightarrow> int"
where
  "intv'_const (Smaller' d) = d" |
  "intv'_const (Const' d) = d" |
  "intv'_const (Intv' d) = d"  |
  "intv'_const (Greater' d) = d"

lemma finite_\<R>_aux:
  fixes P A B assumes "finite {x. A x}" "finite {x. B x}"
  shows "finite {(I, J) | I J. P I J r \<and> A I \<and> B J}"
using assms by (fastforce intro: pairwise_finiteI finite_ex_and1 finite_ex_and2)

lemma finite_\<R>:
  notes [[simproc add: finite_Collect]]
  shows "finite \<R>"
proof -
  { fix I J r assume A: "valid_region X k I J r"
    let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
    from A have "refl_on ?X\<^sub>0 r" by auto
    then have "r \<subseteq> X \<times> X" by (auto simp: refl_on_def)
    then have "r \<in> Pow (X \<times> X)" by auto
  }
  then have "{r. \<exists>I J. valid_region X k I J r} \<subseteq> Pow (X \<times> X)" by auto
  from finite_subset[OF this] finite have fin: "finite {r. \<exists>I J. valid_region X k I J r}" by auto
  let ?u = "Max {k x | x. x \<in> X}"
  let ?l = "- Max {k x | x. x \<in> X}"
  let ?I = "{intv. intv_const intv \<le> ?u}"
  let ?J = "{intv. ?l \<le> intv'_const intv \<and> intv'_const intv \<le> ?u}"
  let ?S = "{r. \<exists>I J. valid_region X k I J r}"
  let ?fin_mapI = "\<lambda> I. \<forall>x. (x \<in> X \<longrightarrow> I x \<in> ?I) \<and> (x \<notin> X \<longrightarrow> I x = Const 0)"
  let ?fin_mapJ = "\<lambda> J. \<forall>x. \<forall>y. (x \<in> X \<and> y \<in> X \<longrightarrow> J x y \<in> ?J)
                              \<and> (x \<notin> X \<longrightarrow> J x y = Const' 0) \<and> (y \<notin> X \<longrightarrow> J x y = Const' 0)"
  let ?\<R> = "{region X I J r | I J r. valid_region X k I J r \<and> ?fin_mapI I \<and> ?fin_mapJ J}"
  let ?f = "\<lambda>r. {region X I J r | I J . valid_region X k I J r \<and> ?fin_mapI I \<and> ?fin_mapJ J}"
  let ?g = "\<lambda>r. {(I, J) | I J . valid_region X k I J r \<and> ?fin_mapI I \<and> ?fin_mapJ J}"
  have "?I = (Const ` {d. d \<le> ?u}) \<union> (Intv ` {d. d \<le> ?u}) \<union> (Greater ` {d. d \<le> ?u})"
  by auto (case_tac x, auto)
  then have "finite ?I" by auto
  from finite_set_of_finite_funs[OF \<open>finite X\<close> this] have finI: "finite {I. ?fin_mapI I}" .
  have "?J = (Smaller' ` {d. ?l \<le> d \<and> d \<le> ?u}) \<union> (Const' ` {d. ?l \<le> d \<and> d \<le> ?u})
           \<union> (Intv' ` {d. ?l \<le> d \<and> d \<le> ?u}) \<union> (Greater' ` {d. ?l \<le> d \<and> d \<le> ?u})"
  by auto (case_tac x, auto)
  then have "finite ?J" by auto
  from finite_set_of_finite_funs2[OF \<open>finite X\<close> \<open>finite X\<close> this] have finJ: "finite {J. ?fin_mapJ J}" .
  from finite_\<R>_aux[OF finI finJ, of "valid_region X k"] have "\<forall>r \<in> ?S. finite (?g r)" by simp
  moreover have "\<forall> r \<in> ?S. ?f r = (\<lambda> (I, J). region X I J r) ` ?g r" by auto
  ultimately have "\<forall>r \<in> ?S. finite (?f r)" by auto
  moreover have "?\<R> = \<Union> (?f `?S)" by auto
  ultimately have "finite ?\<R>" using fin by auto
  moreover have "\<R> \<subseteq> ?\<R>"
  proof
    fix R assume R: "R \<in> \<R>"
    then obtain I J r where I: "R = region X I J r" "valid_region X k I J r" unfolding \<R>_def by auto
    let ?I = "\<lambda> x. if x \<in> X then I x else Const 0"
    let ?J = "\<lambda> x y. if x \<in> X \<and> y \<in> X \<and> (isGreater (I x) \<or> isGreater (I y)) then J x y else Const' 0"
    let ?R = "region X ?I ?J r"
    from valid_regions_I_cong[OF I(2)] I have *: "R = ?R" "valid_region X k ?I ?J r" by auto
    have "\<forall>x. x \<notin> X \<longrightarrow> ?I x = Const 0" by auto
    moreover have "\<forall>x. x \<in> X \<longrightarrow> intv_const (I x) \<le> ?u"
    proof auto
      fix x assume x: "x \<in> X"
      with I(2) have "valid_intv (k x) (I x)" by auto
      moreover from \<open>finite X\<close> x have "k x \<le> ?u" by (auto intro: Max_ge)
      ultimately  show "intv_const (I x) \<le> Max {k x |x. x \<in> X}" by (cases "I x") auto
    qed
    ultimately have **: "?fin_mapI ?I" by auto
    have "\<forall>x y. x \<notin> X \<longrightarrow> ?J x y = Const' 0" by auto
    moreover have "\<forall>x y. y \<notin> X \<longrightarrow> ?J x y = Const' 0" by auto
    moreover have "\<forall>x. \<forall> y. x \<in> X \<and> y \<in> X \<longrightarrow> ?l \<le> intv'_const (?J x y) \<and> intv'_const (?J x y) \<le> ?u"
    proof clarify
      fix x y assume x: "x \<in> X" assume y: "y \<in> X"
      show "?l \<le> intv'_const (?J x y) \<and> intv'_const (?J x y) \<le> ?u"
      proof (cases "isGreater (I x) \<or> isGreater (I y)")
        case True
        with x y I(2) have "valid_intv' (k y) (k x) (J x y)" by fastforce
        moreover from \<open>finite X\<close> x have "k x \<le> ?u" by (auto intro: Max_ge)
        moreover from \<open>finite X\<close> y have "?l \<le> -k y" by (auto intro: Max_ge)
        ultimately show ?thesis by (cases "J x y") auto
      next
        case False then show ?thesis by auto
      qed
    qed
    ultimately have "?fin_mapJ ?J" by auto
    with * ** show "R \<in> ?\<R>" by blast
  qed
  ultimately show "finite \<R>" by (blast intro: finite_subset)
qed

end

section \<open>Approximation with \<open>\<beta>\<close>-regions\<close>

locale Beta_Regions' = Beta_Regions +
  fixes v n not_in_X
  assumes clock_numbering: "\<forall> c. v c > 0 \<and> (\<forall>x. \<forall>y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
                           "\<forall>k :: nat \<le>n. k > 0 \<longrightarrow> (\<exists>c \<in> X. v c = k)" "\<forall> c \<in> X. v c \<le> n"
  assumes not_in_X: "not_in_X \<notin> X"
begin

definition "v' \<equiv> \<lambda> i. if i \<le> n then (THE c. c \<in> X \<and> v c = i) else not_in_X"

lemma v_v':
  "\<forall> c \<in> X. v' (v c) = c"
using clock_numbering unfolding v'_def by auto

abbreviation
  "vabstr (S :: ('a, t) zone) M \<equiv> S = [M]\<^bsub>v,n\<^esub> \<and> (\<forall> i\<le>n. \<forall> j\<le>n. M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>)"

definition normalized:
  "normalized M \<equiv>
    (\<forall> i j. 0 < i \<and> i \<le> n \<and> 0 < j \<and> j \<le> n \<and> M i j \<noteq> \<infinity> \<longrightarrow>
       Lt (- ((k o v') j)) \<le> M i j \<and> M i j \<le> Le ((k o v') i))
    \<and> (\<forall> i \<le> n. i > 0 \<longrightarrow> (M i 0 \<le> Le ((k o v') i) \<or> M i 0 = \<infinity>) \<and> Lt (- ((k o v') i)) \<le> M 0 i)"

definition apx_def:
  "Approx\<^sub>\<beta> Z \<equiv> \<Inter> {S. \<exists> U M. S = \<Union> U \<and> U \<subseteq> \<R> \<and> Z \<subseteq> S \<and> vabstr S M \<and> normalized M}"

lemma apx_min:
  "S = \<Union> U \<Longrightarrow> U \<subseteq> \<R> \<Longrightarrow> S = [M]\<^bsub>v,n\<^esub> \<Longrightarrow> \<forall> i\<le>n. \<forall> j\<le>n. M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>
  \<Longrightarrow> normalized M \<Longrightarrow> Z \<subseteq> S \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> S"
unfolding apx_def by blast

lemma "U \<noteq> {} \<Longrightarrow> x \<in> \<Inter> U \<Longrightarrow> \<exists> S \<in> U. x \<in> S" by auto

lemma \<R>_union: "\<Union> \<R> = V" using region_cover unfolding V_def \<R>_def by auto

lemma all_dbm: "\<exists> M. vabstr (\<Union>\<R>) M \<and> normalized M"
proof -
  let ?M = "\<lambda> i j. if i = 0 then Le 0 else \<infinity>"
  have "[?M]\<^bsub>v,n\<^esub> = V" unfolding V_def DBM_zone_repr_def DBM_val_bounded_def
  proof (auto, goal_cases)
    case (1 u c)
    with clock_numbering have "dbm_entry_val u None (Some c) (Le 0)" by auto
    then show ?case by auto
  next
    case (2 u c)
    from clock_numbering(1) have "0 \<noteq> v c" by auto
    with 2 show ?case by auto 
  next
    case (3 u c)
    from clock_numbering(1) have "0 \<noteq> v c" by auto
    with 3 show ?case by auto 
  next
    case (4 u c)
    with clock_numbering have "c \<in> X" by blast
    with 4(1) show ?case by auto
  next
    case (5 u c1)
    from clock_numbering(1) have "0 \<noteq> v c1" by auto
    with 5 show ?case by auto
  qed
  moreover have "\<forall> i\<le>n. \<forall> j\<le>n. ?M i j \<noteq> \<infinity> \<longrightarrow> get_const (?M i j) \<in> \<int>" by auto
  moreover have "normalized ?M" unfolding normalized less_eq dbm_le_def by auto
  ultimately show ?thesis using \<R>_union by auto
qed

lemma \<R>_int:
  "R \<in> \<R> \<Longrightarrow> R' \<in> \<R> \<Longrightarrow> R \<noteq> R' \<Longrightarrow> R \<inter> R' = {}" using \<R>_regions_distinct by blast

lemma aux1:
  "u \<in> R \<Longrightarrow> R \<in> \<R> \<Longrightarrow> U \<subseteq> \<R> \<Longrightarrow> u \<in> \<Union> U \<Longrightarrow> R \<subseteq> \<Union> U" using \<R>_int by blast

lemma aux2: "x \<in> \<Inter> U \<Longrightarrow> U \<noteq> {} \<Longrightarrow> \<exists> S \<in> U. x \<in> S" by blast

lemma aux2': "x \<in> \<Inter> U \<Longrightarrow> U \<noteq> {} \<Longrightarrow> \<forall> S \<in> U. x \<in> S" by blast

lemma apx_subset: "Z \<subseteq> Approx\<^sub>\<beta> Z" unfolding apx_def by auto

lemma aux3:
  "\<forall> X \<in> U. \<forall> Y \<in> U. X \<inter> Y \<in> U \<Longrightarrow> S \<subseteq> U \<Longrightarrow> S \<noteq> {} \<Longrightarrow> finite S \<Longrightarrow> \<Inter> S \<in> U"
proof goal_cases
  case 1
  with finite_list obtain l where "set l = S" by blast
  then show ?thesis using 1
  proof (induction l arbitrary: S)
    case Nil thus ?case by auto
  next
    case (Cons x xs)
    show ?case
    proof (cases "set xs = {}")
      case False
      with Cons have "\<Inter>(set xs) \<in> U" by auto
      with Cons.prems(1-3) show ?thesis by force
    next
      case True
      with Cons.prems show ?thesis by auto
    qed
  qed
qed

lemma empty_zone_dbm:
  "\<exists> M :: t DBM. vabstr {} M \<and> normalized M \<and> (\<forall>k \<le> n. M k k \<le> Le 0)"
proof -
  from non_empty obtain c where c: "c \<in> X" by auto
  with clock_numbering have c': "v c > 0" "v c \<le> n" by auto
  let ?M = "\<lambda>i j. if i = v c \<and> j = 0 \<or> i = j then Le (0::t) else if i = 0 \<and> j = v c then Lt 0 else \<infinity>"
  have "[?M]\<^bsub>v,n\<^esub> = {}" unfolding DBM_zone_repr_def DBM_val_bounded_def using c' by auto
  moreover have "\<forall> i\<le>n. \<forall> j\<le>n. ?M i j \<noteq> \<infinity> \<longrightarrow> get_const (?M i j) \<in> \<int>" by auto
  moreover have "normalized ?M" unfolding normalized less_eq dbm_le_def by auto
  ultimately show ?thesis by auto
qed

lemma valid_dbms_int:
  "\<forall>X\<in>{S. \<exists>M. vabstr S M}. \<forall>Y\<in>{S. \<exists>M. vabstr S M}. X \<inter> Y \<in> {S. \<exists>M. vabstr S M}"
proof (auto, goal_cases)
  case (1 M1 M2)
  obtain M' where M': "M' = And M1 M2" by fast
  from DBM_and_sound1[OF ] DBM_and_sound2[OF] DBM_and_complete[OF ]
  have "[M1]\<^bsub>v,n\<^esub> \<inter> [M2]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def M' by auto
  moreover from 1 have "\<forall> i\<le>n. \<forall> j\<le>n. M' i j \<noteq> \<infinity> \<longrightarrow> get_const (M' i j) \<in> \<int>"
  unfolding M' by (auto split: split_min)
  ultimately show ?case by auto
qed

print_statement split_min

lemma split_min':
  "P (min i j) = ((min i j = i \<longrightarrow> P i) \<and> (min i j = j \<longrightarrow> P j))"
unfolding min_def by auto

lemma normalized_and_preservation:
  "normalized M1 \<Longrightarrow> normalized M2 \<Longrightarrow> normalized (And M1 M2)"
unfolding normalized by safe (subst And.simps, split split_min', fastforce)+

lemma valid_dbms_int':
  "\<forall>X\<in>{S. \<exists>M. vabstr S M \<and> normalized M}. \<forall>Y\<in>{S. \<exists>M. vabstr S M \<and> normalized M}.
    X \<inter> Y \<in> {S. \<exists>M. vabstr S M \<and> normalized M}"
proof (auto, goal_cases)
  case (1 M1 M2)
  obtain M' where M': "M' = And M1 M2" by fast
  from DBM_and_sound1 DBM_and_sound2 DBM_and_complete
  have "[M1]\<^bsub>v,n\<^esub> \<inter> [M2]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>" unfolding M' DBM_zone_repr_def by auto
  moreover from M' 1 have "\<forall> i\<le>n. \<forall> j\<le>n. M' i j \<noteq> \<infinity> \<longrightarrow> get_const (M' i j) \<in> \<int>"
  by (auto split: split_min)
  moreover from normalized_and_preservation[OF 1(2,4)] have "normalized M'" unfolding M' .
  ultimately show ?case by auto
qed

lemma apx_in:
  "Z \<subseteq> V \<Longrightarrow> Approx\<^sub>\<beta> Z \<in> {S. \<exists> U M. S = \<Union> U \<and> U \<subseteq> \<R> \<and> Z \<subseteq> S \<and> vabstr S M \<and> normalized M}"
proof -
  assume "Z \<subseteq> V"
  let ?A = "{S. \<exists> U M. S = \<Union> U \<and> U \<subseteq> \<R> \<and> Z \<subseteq> S \<and> vabstr S M \<and> normalized M}"
  let ?U = "{R \<in> \<R>. \<forall> S \<in> ?A. R \<subseteq> S}"
  have "?A \<subseteq> {S. \<exists> U. S = \<Union> U \<and> U \<subseteq> \<R>}" by auto
  moreover from finite_\<R> have "finite \<dots>" by auto
  ultimately have "finite ?A" by (auto intro: finite_subset)
  from all_dbm obtain M where M:
    "vabstr (\<Union>\<R>) M" "normalized M"
  by auto
  with \<open>_ \<subseteq> V\<close> \<R>_union have "V \<in> ?A" by blast
  then have "?A \<noteq> {}" by blast
  have "?A \<subseteq> {S. \<exists> M. vabstr S M \<and> normalized M}" by auto
  with aux3[OF valid_dbms_int' this \<open>?A \<noteq> _\<close> \<open>finite ?A\<close>] have
    "\<Inter> ?A \<in> {S. \<exists> M. vabstr S M \<and> normalized M}"
  by blast
  then obtain M where *: "vabstr (Approx\<^sub>\<beta> Z) M" "normalized M" unfolding apx_def by auto
  have "\<Union> ?U = \<Inter> ?A"
  proof (safe, goal_cases)
    case 1
    show ?case
    proof (cases "Z = {}")
      case False
      then obtain v where "v \<in> Z" by auto
      with region_cover \<open>Z \<subseteq> V\<close> obtain R where "R \<in> \<R>" "v \<in> R" unfolding V_def by blast
      with aux1[OF this(2,1)] \<open>v \<in> Z\<close> have "R \<in> ?U" by blast
      with 1 show ?thesis by blast
    next
      case True
      with empty_zone_dbm have "{} \<in> ?A" by auto
      with 1(1,3) show ?thesis by blast
    qed
  next
    case (2 v)
    from aux2[OF 2 \<open>?A \<noteq> _\<close>] obtain S where "v \<in> S" "S \<in> ?A" by blast
    then obtain R where "v \<in> R" "R \<in> \<R>" by auto
    { fix S assume "S \<in> ?A"
      with aux2'[OF 2 \<open>?A \<noteq> _\<close>] have "v \<in> S" by auto
      with \<open>S \<in> ?A\<close> obtain U M R' where *:
        "v \<in> R'" "R' \<in> \<R>" "S = \<Union>U" "U \<subseteq> \<R>" "vabstr S M" "Z \<subseteq> S"
      by blast
      from aux1[OF this(1,2,4)] *(3) \<open>v \<in> S\<close> have "R' \<subseteq> S" by blast
      moreover from \<R>_regions_distinct[OF *(2,1) \<open>R \<in> \<R>\<close>] \<open>v \<in> R\<close> have "R' = R" by fast
      ultimately have "R \<subseteq> S" by fast
    }
    with \<open>R \<in> \<R>\<close> have "R \<in> ?U" by auto
    with \<open>v \<in> R\<close> show ?case by auto
  qed
  then have "Approx\<^sub>\<beta> Z = \<Union>?U" "?U \<subseteq> \<R>" "Z \<subseteq> Approx\<^sub>\<beta> Z" unfolding apx_def by auto
  with * show ?thesis by blast
qed

lemma apx_empty:
  "Approx\<^sub>\<beta> {} = {}"
unfolding apx_def using empty_zone_dbm by blast

end

section \<open>Computing \<open>\<beta>\<close>-Approximation\<close>

context Beta_Regions'
begin

lemma dbm_regions:
  "vabstr S M \<Longrightarrow> normalized M \<Longrightarrow> [M]\<^bsub>v,n\<^esub> \<noteq> {} \<Longrightarrow> [M]\<^bsub>v,n\<^esub> \<subseteq> V \<Longrightarrow> \<exists> U \<subseteq> \<R>. S = \<Union> U"
proof goal_cases
  case A: 1
  let ?U =
    "{R \<in> \<R>. \<exists> I J r. R = region X I J r \<and> valid_region X k I J r \<and>
      (\<forall> c \<in> X.
        (\<forall> d. I c = Const d \<longrightarrow> M (v c) 0 \<ge> Le d \<and> M 0 (v c) \<ge> Le (-d)) \<and>
        (\<forall> d. I c = Intv d \<longrightarrow>  M (v c) 0 \<ge> Lt (d + 1) \<and> M 0 (v c) \<ge> Lt (-d)) \<and> 
        (I c = Greater (k c) \<longrightarrow>  M (v c) 0 = \<infinity>)
      ) \<and>
      (\<forall> x \<in> X. \<forall> y \<in> X.
        (\<forall> c d. I x = Intv c \<and> I y = Intv d \<longrightarrow> M (v x) (v y) \<ge>
          (if (x, y) \<in> r then if (y, x) \<in> r then Le (c - d) else Lt (c - d) else Lt (c - d + 1))) \<and>
        (\<forall> c d. I x = Intv c \<and> I y = Intv d \<longrightarrow> M (v y) (v x) \<ge>
          (if (y, x) \<in> r then if (x, y) \<in> r then Le (d - c) else Lt (d - c) else Lt (d - c + 1))) \<and>
        (\<forall> c d. I x = Const c \<and> I y = Const d \<longrightarrow> M (v x) (v y) \<ge> Le (c - d)) \<and>
        (\<forall> c d. I x = Const c \<and> I y = Const d \<longrightarrow> M (v y) (v x) \<ge> Le (d - c)) \<and>
        (\<forall> c d. I x = Intv c \<and> I y = Const d \<longrightarrow> M (v x) (v y) \<ge> Lt (c - d + 1)) \<and>
        (\<forall> c d. I x = Intv c \<and> I y = Const d \<longrightarrow> M (v y) (v x) \<ge> Lt (d - c)) \<and>
        (\<forall> c d. I x = Const c \<and> I y = Intv d \<longrightarrow> M (v x) (v y) \<ge> Lt (c - d)) \<and>
        (\<forall> c d. I x = Const c \<and> I y = Intv d \<longrightarrow> M (v y) (v x) \<ge> Lt (d - c + 1)) \<and>
        ((isGreater (I x) \<or> isGreater (I y)) \<and> J x y = Greater' (k x) \<longrightarrow> M (v x) (v y) = \<infinity>) \<and>
        (\<forall> c. (isGreater (I x) \<or> isGreater (I y)) \<and> J x y = Const' c
          \<longrightarrow> M (v x) (v y) \<ge> Le c \<and> M (v y) (v x) \<ge> Le (- c)) \<and>
        (\<forall> c. (isGreater (I x) \<or> isGreater (I y)) \<and> J x y = Intv' c
          \<longrightarrow> M (v x) (v y) \<ge> Lt (c + 1) \<and> M (v y) (v x) \<ge> Lt (- c))
      )
     }"
  have "\<Union> ?U = [M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def DBM_val_bounded_def
  proof (standard, goal_cases)
    case 1
    show ?case
    proof (auto, goal_cases)
      case 1
      from A(3) show "Le 0 \<preceq> M 0 0" unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
    next
      case (2 u I J r c)
      note B = this
      from B(6) clock_numbering have "c \<in> X" by blast
      with B(1) v_v' have *: "intv_elem c u (I c)" "v' (v c) = c" by auto
      from clock_numbering(1) have "v c > 0" by auto
      show ?case
      proof (cases "I c")
        case (Const d)
        with B(4) \<open>c \<in> X\<close> have "M 0 (v c) \<ge> Le (- real d)" by auto
        with * Const show ?thesis by - (rule dbm_entry_val_mono_2[folded less_eq], auto)
      next
        case (Intv d)
        with B(4) \<open>c \<in> X\<close> have "M 0 (v c) \<ge> Lt (- real d)" by auto
        with * Intv show ?thesis by - (rule dbm_entry_val_mono_2[folded less_eq], auto)
      next
        case (Greater d)
        with B(3) \<open>c \<in> X\<close> have "I c = Greater (k c)" by fastforce
        with * have "- u c < - k c" by auto
        moreover from A(2) *(2) \<open>v c \<le> n\<close> \<open>v c > 0\<close> have
          "Lt (- k c) \<le> M 0 (v c)"
        unfolding normalized by force
        ultimately show ?thesis by - (rule dbm_entry_val_mono_2[folded less_eq], auto)
      qed
    next
      case (3 u I J r c)
      note B = this
      from B(6) clock_numbering have "c \<in> X" by blast
      with B(1) v_v' have *: "intv_elem c u (I c)" "v' (v c) = c" by auto
      from clock_numbering(1) have "v c > 0" by auto
      show ?case
      proof (cases "I c")
        case (Const d)
        with B(4) \<open>c \<in> X\<close> have "M (v c) 0 \<ge> Le d" by auto
        with * Const show ?thesis by - (rule dbm_entry_val_mono_3[folded less_eq], auto)
      next
        case (Intv d)
        with B(4) \<open>c \<in> X\<close> have "M (v c) 0 \<ge> Lt (real d + 1)" by auto
        with * Intv show ?thesis by - (rule dbm_entry_val_mono_3[folded less_eq], auto)
      next
        case (Greater d)
        with B(3) \<open>c \<in> X\<close> have "I c = Greater (k c)" by fastforce
        with B(4) \<open>c \<in> X\<close> show ?thesis by auto
      qed
    next
      case B: (4 u I J r c1 c2)
      from B(6,7) clock_numbering have "c1 \<in> X" "c2 \<in> X" by blast+
      with B(1) v_v' have *:
        "intv_elem c1 u (I c1)" "intv_elem c2 u (I c2)" "v' (v c1) = c1" "v' (v c2) = c2"
      by auto
      from clock_numbering(1) have "v c1 > 0" "v c2 > 0" by auto
      { assume C: "isGreater (I c1) \<or> isGreater (I c2)"
        with B(1) \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> have **: "intv'_elem c1 c2 u (J c1 c2)" by force
        have ?case
        proof (cases "J c1 c2")
          case (Smaller' c)
          with C B(3) \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> have "c \<le> - k c2" by fastforce
          moreover from C \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> ** Smaller' have "u c1 - u c2 < c" by auto
          moreover from A(2) *(3,4) B(6,7) \<open>v c1 > 0\<close> \<open>v c2 > 0\<close> have
            "M (v c1) (v c2) \<ge> Lt (- k c2) \<or> M (v c1) (v c2) = \<infinity>"
          unfolding normalized by fastforce
          ultimately show ?thesis by (safe) (rule dbm_entry_val_mono_1[folded less_eq], auto)
        next
          case (Const' c)
          with C B(5) \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> have "M (v c1) (v c2) \<ge> Le c" by auto
          with Const' ** \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> show ?thesis
          by (auto intro: dbm_entry_val_mono_1[folded less_eq])
        next
          case (Intv' c)
          with C B(5) \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> have "M (v c1) (v c2) \<ge> Lt (real_of_int c + 1)" by auto
          with Intv' ** \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> show ?thesis
          by (auto intro: dbm_entry_val_mono_1[folded less_eq])
        next
          case (Greater' c)
          with C B(3) \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> have "c = k c1" by fastforce
          with Greater' C B(5) \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> show ?thesis by auto
        qed
      } note GreaterI = this
      show ?case
      proof (cases "I c1")
        case (Const c)
        show ?thesis
        proof (cases "I c2", goal_cases)
          case (1 d)
          with Const \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> *(1,2) have "u c1 = c" "u c2 = d" by auto
          moreover from \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> 1 Const B(5) have
            "Le (real c - real d) \<le> M (v c1) (v c2)"
          by meson
          ultimately show ?thesis by (auto intro: dbm_entry_val_mono_1[folded less_eq])
        next
          case (Intv d)
          with Const \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> *(1,2) have "u c1 = c" "d < u c2" by auto
          then have "u c1 - u c2 < c - real d" by auto
          moreover from Const \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> Intv B(5) have
            "Lt (real c - d) \<le> M (v c1) (v c2)"
          by meson
          ultimately show ?thesis by (auto intro: dbm_entry_val_mono_1[folded less_eq])
        next
          case Greater then show ?thesis by (auto intro: GreaterI)
        qed
      next
        case (Intv c)
        show ?thesis
        proof (cases "I c2", goal_cases)
          case (Const d)
          with Intv \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> *(1,2) have "u c1 < c + 1" "d = u c2" by auto
          then have "u c1 - u c2 < c - real d + 1" by auto
          moreover from \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> Intv Const B(5) have
            "Lt (real c - real d + 1) \<le> M (v c1) (v c2)"
          by meson
          ultimately show ?thesis by (auto intro: dbm_entry_val_mono_1[folded less_eq])
        next
          case (2 d)
          show ?case
          proof (cases "(c1,c2) \<in> r")
            case True
            note T = this
            show ?thesis
            proof (cases "(c2,c1) \<in> r")
              case True
              with T B(5) 2 Intv \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> have
                "Le (real c - real d) \<le> M (v c1) (v c2)"
              by auto
              moreover from nat_intv_frac_decomp[of c "u c1"] nat_intv_frac_decomp[of d "u c2"]
                            B(1,2) \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> T True Intv 2 *(1,2)
              have "u c1 - u c2 = real c - d" by auto
              ultimately show ?thesis by (auto intro: dbm_entry_val_mono_1[folded less_eq])
            next
              case False
              with T B(5) 2 Intv \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> have
                "Lt (real c - real d) \<le> M (v c1) (v c2)"
              by auto
              moreover from nat_intv_frac_decomp[of c "u c1"] nat_intv_frac_decomp[of d "u c2"]
                            B(1,2) \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> T False Intv 2 *(1,2)
              have "u c1 - u c2 < real c - d" by auto
              ultimately show ?thesis by (auto intro: dbm_entry_val_mono_1[folded less_eq])
            qed
          next
            case False
            with B(5) 2 Intv \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> have
                "Lt (real c - real d + 1) \<le> M (v c1) (v c2)"
            by meson
            moreover from 2 Intv \<open>c1 \<in> X\<close> \<open>c2 \<in> X\<close> * have "u c1 - u c2 < c - real d + 1" by auto
            ultimately show ?thesis by (auto intro: dbm_entry_val_mono_1[folded less_eq])
          qed
        next
          case Greater then show ?thesis by (auto intro: GreaterI)
        qed
      next
        case Greater then show ?thesis by (auto intro: GreaterI)
      qed
    qed
  next
    case 2 show ?case
    proof (safe, goal_cases)
      case (1 u)
      with A(4) have "u \<in> V" unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
      with region_cover obtain R where "R \<in> \<R>" "u \<in> R" unfolding V_def by auto
      then obtain I J r where R: "R = region X I J r" "valid_region X k I J r" unfolding \<R>_def by auto
      have "(\<forall>c\<in>X. (\<forall>d. I c = Const d \<longrightarrow> Le (real d) \<le> M (v c) 0 \<and> Le (- real d) \<le> M 0 (v c)) \<and>
                 (\<forall>d. I c = Intv d \<longrightarrow> Lt (real d + 1) \<le> M (v c) 0 \<and> Lt (- real d) \<le> M 0 (v c)) \<and>
                 (I c = Greater (k c) \<longrightarrow> M (v c) 0 = \<infinity>))"
      proof safe
        fix c assume "c \<in> X"
        with R \<open>u \<in> R\<close> have *: "intv_elem c u (I c)" by auto
        fix d assume **: "I c = Const d"
        with * have "u c = d" by fastforce
        moreover from ** clock_numbering(3) \<open>c \<in> X\<close> 1 have
          "dbm_entry_val u (Some c) None (M (v c) 0)"
        by auto
        ultimately show "Le (real d) \<le> M (v c) 0"
        unfolding less_eq dbm_le_def by (cases "M (v c) 0") auto
      next
        fix c assume "c \<in> X"
        with R \<open>u \<in> R\<close> have *: "intv_elem c u (I c)" by auto
        fix d assume **: "I c = Const d"
        with * have "u c = d" by fastforce
        moreover from ** clock_numbering(3) \<open>c \<in> X\<close> 1 have
          "dbm_entry_val u None (Some c) (M 0 (v c))"
        by auto
        ultimately show "Le (- real d) \<le> M 0 (v c)"
        unfolding less_eq dbm_le_def by (cases "M 0 (v c)") auto
      next
        fix c assume "c \<in> X"
        with R \<open>u \<in> R\<close> have *: "intv_elem c u (I c)" by auto
        fix d assume **: "I c = Intv d"
        with * have "d < u c" "u c < d + 1" by fastforce+
        moreover from ** clock_numbering(3) \<open>c \<in> X\<close> 1 have
          "dbm_entry_val u (Some c) None (M (v c) 0)"
        by auto
        moreover have
          "M (v c) 0 \<noteq> \<infinity> \<Longrightarrow> get_const (M (v c) 0) \<in> \<int>"
        using \<open>c \<in> X\<close> clock_numbering A(1) by auto
        ultimately show "Lt (real d + 1) \<le> M (v c) 0" unfolding less_eq dbm_le_def
        apply (cases "M (v c) 0")
          apply auto
         apply (rename_tac x1)
         apply (subgoal_tac "x1 > d")
          apply (rule dbm_lt.intros(5))
          apply (metis nat_intv_frac_gt0 frac_eq_0_iff less_irrefl linorder_not_le of_nat_1 of_nat_add)
         apply simp
        apply (rename_tac x2)
        apply (subgoal_tac "x2 > d + 1")
         apply (rule dbm_lt.intros(6))
         apply (metis of_nat_1 of_nat_add)
        apply simp
        by (metis nat_intv_not_int One_nat_def add.commute add.right_neutral add_Suc_right le_less_trans
                  less_eq_real_def linorder_neqE_linordered_idom semiring_1_class.of_nat_simps(2))
      next
        fix c assume "c \<in> X"
        with R \<open>u \<in> R\<close> have *: "intv_elem c u (I c)" by auto
        fix d assume **: "I c = Intv d"
        with * have "d < u c" "u c < d + 1" by fastforce+
        moreover from ** clock_numbering(3) \<open>c \<in> X\<close> 1 have
          "dbm_entry_val u None (Some c) (M 0 (v c))"
        by auto
        moreover have "M 0 (v c) \<noteq> \<infinity> \<Longrightarrow> get_const (M 0 (v c)) \<in> \<int>" using \<open>c \<in> X\<close> clock_numbering A(1) by auto
        ultimately show "Lt (- real d) \<le> M 0 (v c)" unfolding less_eq dbm_le_def
          proof (cases "M 0 (v c)", -, auto, goal_cases)
            case prems: (1 x1)
            then have "u c = d + frac (u c)" by (metis nat_intv_frac_decomp \<open>u c < d + 1\<close>) 
            with prems(5) have "- x1 \<le> d + frac (u c)" by auto
            with prems(1) frac_ge_0 frac_lt_1 have "- x1 \<le> d"
            by - (rule ints_le_add_frac2[of "frac (u c)" d "-x1"]; fastforce)
            with prems have "- d \<le> x1" by auto
            then show ?case by auto
          next
            case prems: (2 x1)
            then have "u c = d + frac (u c)" by (metis nat_intv_frac_decomp \<open>u c < d + 1\<close>) 
            with prems(5) have "- x1 \<le> d + frac (u c)" by auto
            with prems(1) frac_ge_0 frac_lt_1 have "- x1 \<le> d"
            by - (rule ints_le_add_frac2[of "frac (u c)" d "-x1"]; fastforce)
            with prems(6) have "- d < x1" by auto
            then show ?case by auto
        qed
      next
        fix c assume "c \<in> X"
        with R \<open>u \<in> R\<close> have *: "intv_elem c u (I c)" by auto
        fix d assume **: "I c = Greater (k c)"
        have "M (v c) 0 \<le> Le ((k o v') (v c)) \<or> M (v c) 0 = \<infinity>"
        using A(2) \<open>c \<in> X\<close> clock_numbering unfolding normalized by auto
        with v_v' \<open>c \<in> X\<close> have "M (v c) 0 \<le> Le (k c) \<or> M (v c) 0 = \<infinity>" by auto
        moreover from * ** have "k c < u c" by fastforce
        moreover from ** clock_numbering(3) \<open>c \<in> X\<close> 1 have
          "dbm_entry_val u (Some c) None (M (v c) 0)"
        by auto
        moreover have
          "M (v c) 0 \<noteq> \<infinity> \<Longrightarrow> get_const (M (v c) 0) \<in> \<int>"
        using \<open>c \<in> X\<close> clock_numbering A(1) by auto
        ultimately show "M (v c) 0 = \<infinity>" unfolding less_eq dbm_le_def
          apply -
          apply (rule ccontr)
          using ** apply (cases "M (v c) 0")
        by auto
      qed
      moreover
      { fix x y assume X: "x \<in> X" "y \<in> X"
        with R \<open>u \<in> R\<close> have *: "intv_elem x u (I x)" "intv_elem y u (I y)" by auto
        from X R \<open>u \<in> R\<close> have **:
          "isGreater (I x) \<or> isGreater (I y) \<longrightarrow> intv'_elem x y u (J x y)"
        by force
        have int: "M (v x) (v y) \<noteq> \<infinity> \<Longrightarrow> get_const (M (v x) (v y)) \<in> \<int>" using X clock_numbering A(1)
        by auto
        have int2: "M (v y) (v x) \<noteq> \<infinity> \<Longrightarrow> get_const (M (v y) (v x)) \<in> \<int>" using X clock_numbering A(1)
        by auto
        from 1 clock_numbering(3) X 1 have ***:
          "dbm_entry_val u (Some x) (Some y) (M (v x) (v y))"
          "dbm_entry_val u (Some y) (Some x) (M (v y) (v x))"
        by auto
        have
         "(\<forall> c d. I x = Intv c \<and> I y = Intv d \<longrightarrow> M (v x) (v y) \<ge>
            (if (x, y) \<in> r then if (y, x) \<in> r then Le (c - d) else Lt (c - d) else Lt (c - d + 1))) \<and>
          (\<forall> c d. I x = Intv c \<and> I y = Intv d \<longrightarrow> M (v y) (v x) \<ge>
            (if (y, x) \<in> r then if (x, y) \<in> r then Le (d - c) else Lt (d - c) else Lt (d - c + 1))) \<and>
          (\<forall> c d. I x = Const c \<and> I y = Const d \<longrightarrow> M (v x) (v y) \<ge> Le (c - d)) \<and>
          (\<forall> c d. I x = Const c \<and> I y = Const d \<longrightarrow> M (v y) (v x) \<ge> Le (d - c)) \<and>
          (\<forall> c d. I x = Intv c \<and> I y = Const d \<longrightarrow> M (v x) (v y) \<ge> Lt (c - d + 1)) \<and>
          (\<forall> c d. I x = Intv c \<and> I y = Const d \<longrightarrow> M (v y) (v x) \<ge> Lt (d - c)) \<and>
          (\<forall> c d. I x = Const c \<and> I y = Intv d \<longrightarrow> M (v x) (v y) \<ge> Lt (c - d)) \<and>
          (\<forall> c d. I x = Const c \<and> I y = Intv d \<longrightarrow> M (v y) (v x) \<ge> Lt (d - c + 1)) \<and>
          ((isGreater (I x) \<or> isGreater (I y)) \<and> J x y = Greater' (k x) \<longrightarrow> M (v x) (v y) = \<infinity>) \<and>
          (\<forall> c. (isGreater (I x) \<or> isGreater (I y)) \<and> J x y = Const' c
            \<longrightarrow> M (v x) (v y) \<ge> Le c \<and> M (v y) (v x) \<ge> Le (- c)) \<and>
          (\<forall> c. (isGreater (I x) \<or> isGreater (I y)) \<and> J x y = Intv' c
            \<longrightarrow> M (v x) (v y) \<ge> Lt (c + 1) \<and> M (v y) (v x) \<ge> Lt (- c))"
        proof (auto, goal_cases)
          case **: (1 c d)
          with R \<open>u \<in> R\<close> X have "frac (u x) = frac (u y)" by auto
          with * ** nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "u x - u y = real c - d"
          by auto
          with *** show ?case unfolding less_eq dbm_le_def by (cases "M (v x) (v y)") auto
        next
          case **: (2 c d)
          with R \<open>u \<in> R\<close> X have "frac (u x) > frac (u y)" by auto
          with * ** nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "real c - d < u x - u y" "u x - u y < real c - d + 1"
          by auto
          with *** int show ?case unfolding less_eq dbm_le_def
          by (cases "M (v x) (v y)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case **: (3 c d)
          from ** R \<open>u \<in> R\<close> X have "frac (u x) < frac (u y)" by auto
          with * ** nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "real c - d - 1 < u x - u y" "u x - u y < real c - d"
          by auto
          with *** int show ?case unfolding less_eq dbm_le_def
          by (cases "M (v x) (v y)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (4 c d) with R(1) \<open>u \<in> R\<close> X show ?case by auto
        next
          case **: (5 c d)
          with R \<open>u \<in> R\<close> X have "frac (u x) = frac (u y)" by auto
          with * ** nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "u x - u y = real c - d" by auto
          with *** show ?case unfolding less_eq dbm_le_def by (cases "M (v y) (v x)") auto
        next
          case **: (6 c d)
          from ** R \<open>u \<in> R\<close> X have "frac (u x) < frac (u y)" by auto
          with * ** nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "real d - c < u y - u x" "u y - u x < real d - c + 1"
          by auto
          with *** int2 show ?case unfolding less_eq dbm_le_def
          by (cases "M (v y) (v x)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case **: (7 c d)
          from ** R \<open>u \<in> R\<close> X have "frac (u x) > frac (u y)" by auto
          with * ** nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "real d - c - 1 < u y - u x" "u y - u x < real d - c"
          by auto
          with *** int2 show ?case unfolding less_eq dbm_le_def
          by (cases "M (v y) (v x)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (8 c d) with R(1) \<open>u \<in> R\<close> X show ?case by auto
        next
          case (9 c d)
          with * nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have 
            "u x - u y = real c - d" by auto
          with *** show ?case unfolding less_eq dbm_le_def by (cases "M (v x) (v y)") auto
        next
          case (10 c d)
          with * nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "u x - u y = real c - d"
          by auto
          with *** show ?case unfolding less_eq dbm_le_def by (cases "M (v y) (v x)") auto
        next
          case (11 c d)
          with * nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "real c - d < u x - u y"
          by auto
          with *** int show ?case unfolding less_eq dbm_le_def
          by (cases "M (v x) (v y)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (12 c d)
          with * nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "real d - c - 1 < u y - u x"
          by auto
          with *** int2 show ?case unfolding less_eq dbm_le_def
          by (cases "M (v y) (v x)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (13 c d)
          with * nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "real c - d - 1 < u x - u y"
          by auto
          with *** int show ?case unfolding less_eq dbm_le_def
          by (cases "M (v x) (v y)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (14 c d)
          with * nat_intv_frac_decomp[of c "u x"] nat_intv_frac_decomp[of d "u y"] have
            "real d - c < u y - u x"
          by auto
          with *** int2 show ?case unfolding less_eq dbm_le_def
          by (cases "M (v y) (v x)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (15 d)
          have "M (v x) (v y) \<le> Le ((k o v') (v x)) \<or> M (v x) (v y) = \<infinity>"
          using A(2) X clock_numbering unfolding normalized by auto
          with v_v' X have "M (v x) (v y) \<le> Le (k x) \<or> M (v x) (v y) = \<infinity>" by auto
          moreover from 15 * ** have "u x - u y > k x" by auto
          ultimately show ?case unfolding less_eq dbm_le_def using *** by (cases "M (v x) (v y)", auto)
        next
          case (16 d)
          have "M (v x) (v y) \<le> Le ((k o v') (v x)) \<or> M (v x) (v y) = \<infinity>"
          using A(2) X clock_numbering unfolding normalized by auto
          with v_v' X have "M (v x) (v y) \<le> Le (k x) \<or> M (v x) (v y) = \<infinity>" by auto
          moreover from 16 * ** have "u x - u y > k x" by auto
          ultimately show ?case unfolding less_eq dbm_le_def using *** by (cases "M (v x) (v y)", auto)
        next
          case 17 with ** *** show ?case unfolding less_eq dbm_le_def by (cases "M (v x) (v y)", auto)
        next
          case 18 with ** *** show ?case unfolding less_eq dbm_le_def by (cases "M (v y) (v x)", auto)
        next
          case 19 with ** *** show ?case unfolding less_eq dbm_le_def by (cases "M (v x) (v y)", auto)
        next
          case 20 with ** *** show ?case unfolding less_eq dbm_le_def by (cases "M (v y) (v x)", auto)
        next
          case (21 c d)
          with ** have "c < u x - u y" by auto
          with *** int show ?case unfolding less_eq dbm_le_def
          by (cases "M (v x) (v y)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (22 c d)
          with ** have "u x - u y < c + 1" by auto
          then have "u y - u x > - c - 1" by auto
          with *** int2 show ?case unfolding less_eq dbm_le_def
          by (cases "M (v y) (v x)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (23 c d)
          with ** have "c < u x - u y" by auto
          with *** int show ?case unfolding less_eq dbm_le_def
          by (cases "M (v x) (v y)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        next
          case (24 c d)
          with ** have "u x - u y < c + 1" by auto
          then have "u y - u x > - c - 1" by auto
          with *** int2 show ?case unfolding less_eq dbm_le_def
          by (cases "M (v y) (v x)", auto) (fastforce intro: int_lt_Suc_le int_lt_neq_prev_lt)+
        qed
      }
      ultimately show ?case using R \<open>u \<in> R\<close> \<open>R \<in> \<R>\<close>
        apply -
        apply standard
         apply standard
         apply rule
          apply assumption
         apply (rule exI[where x = I], rule exI[where x = J], rule exI[where x = r])
      by auto
    qed
  qed
  with A have "S = \<Union>?U" by auto
  moreover have "?U \<subseteq> \<R>" by blast
  ultimately show ?case by blast
qed

lemma dbm_regions':
  "vabstr S M \<Longrightarrow> normalized M \<Longrightarrow> S \<subseteq> V \<Longrightarrow> \<exists> U \<subseteq> \<R>. S = \<Union> U"
using dbm_regions by (cases "S = {}") auto

lemma dbm_regions'':
  "dbm_int M n \<Longrightarrow> normalized M \<Longrightarrow> [M]\<^bsub>v,n\<^esub> \<subseteq> V \<Longrightarrow> \<exists> U \<subseteq> \<R>. [M]\<^bsub>v,n\<^esub> = \<Union> U"
using dbm_regions' by auto

lemma canonical_saturated_1:
  assumes "Le r \<le> M (v c1) 0"
    and "Le (- r) \<le> M 0 (v c1)"
    and "cycle_free M n"
    and "canonical M n"
    and "v c1 \<le> n"
    and "v c1 > 0"
    and "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c"
  obtains u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c1 = r"
proof -
  let ?M' = "\<lambda>i' j'. if i'=v c1 \<and> j'=0 then Le r else if i'=0 \<and> j'=v c1 then Le (- r) else M i' j'"
  from fix_index'[OF assms(1-5)] assms(6) have M':
    "\<forall>u. DBM_val_bounded v u ?M' n \<longrightarrow> DBM_val_bounded v u M n"
    "cycle_free ?M' n" "?M' (v c1) 0 = Le r" "?M' 0 (v c1) = Le (- r)"
  by auto
  with cyc_free_obtains_valuation[unfolded cycle_free_diag_equiv, of ?M' n v] assms(7) obtain u where
    u: "DBM_val_bounded v u ?M' n"
  by fastforce
  with assms(5,6) M'(3,4) have "u c1 = r" unfolding DBM_val_bounded_def by fastforce
  moreover from u M'(1) have "u \<in> [M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def by auto
  ultimately show thesis by (auto intro: that)
qed

lemma canonical_saturated_2:
  assumes "Le r \<le> M 0 (v c2)"
    and "Le (- r) \<le> M (v c2) 0"
    and "cycle_free M n"
    and "canonical M n"
    and "v c2 \<le> n"
    and "v c2 > 0"
    and "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c"
  obtains u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c2 = - r"
proof -
  let ?M' = "\<lambda>i' j'. if i'=0 \<and> j'=v c2 then Le r else if i'=v c2 \<and> j'=0 then Le (-r) else M i' j'"
  from fix_index'[OF assms(1-4)] assms(5,6) have M':
    "\<forall>u. DBM_val_bounded v u ?M' n \<longrightarrow> DBM_val_bounded v u M n"
    "cycle_free ?M' n" "?M' 0 (v c2) = Le r" "?M' (v c2) 0 = Le (- r)"
  by auto
  with cyc_free_obtains_valuation[unfolded cycle_free_diag_equiv, of ?M' n v] assms(7) obtain u where
    u: "DBM_val_bounded v u ?M' n"
  by fastforce
  with assms(5,6) M'(3,4) have "u c2 \<le> -r" "- u c2 \<le> r" unfolding DBM_val_bounded_def by fastforce+
  then have "u c2 = -r" by (simp add: le_minus_iff)
  moreover from u M'(1) have "u \<in> [M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def by auto
  ultimately show thesis by (auto intro: that)
qed

lemma canonical_saturated_3:
  assumes "Le r \<le> M (v c1) (v c2)"
    and "Le (- r) \<le> M (v c2) (v c1)"
    and "cycle_free M n"
    and "canonical M n"
    and "v c1 \<le> n" "v c2 \<le> n"
    and "v c1 \<noteq> v c2"
    and "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c"
  obtains u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c1 - u c2 = r"
proof -
  let ?M'="\<lambda>i' j'. if i'=v c1 \<and> j'=v c2 then Le r else if i'=v c2 \<and> j'=v c1 then Le (-r) else M i' j'"
  from fix_index'[OF assms(1-7), of v] assms(7,8) have M':
    "\<forall>u. DBM_val_bounded v u ?M' n \<longrightarrow> DBM_val_bounded v u M n"
    "cycle_free ?M' n" "?M' (v c1) (v c2) = Le r" "?M' (v c2) (v c1) = Le (- r)"
  by auto
  with cyc_free_obtains_valuation[unfolded cycle_free_diag_equiv, of ?M' n v] assms obtain u where u:
    "DBM_val_bounded v u ?M' n"
  by fastforce
  with assms(5,6) M'(3,4) have
    "u c1 - u c2 \<le> r" "u c2 - u c1 \<le> - r"
  unfolding DBM_val_bounded_def by fastforce+
  then have "u c1 - u c2 = r" by (simp add: le_minus_iff)
  moreover from u M'(1) have "u \<in> [M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def by auto
  ultimately show thesis by (auto intro: that)
qed

lemma DBM_canonical_subset_le:
  notes any_le_inf[intro]
  fixes M :: "t DBM"
  assumes "canonical M n" "[M]\<^bsub>v,n\<^esub> \<subseteq> [M']\<^bsub>v,n\<^esub>" "[M]\<^bsub>v,n\<^esub> \<noteq> {}" "i \<le> n" "j \<le> n" "i \<noteq> j"
  shows "M i j \<le> M' i j"
proof -
  from non_empty_cycle_free[OF assms(3)] clock_numbering(2) have "cycle_free M n" by auto
  with assms(1,4,5) have non_neg:
    "M i j + M j i \<ge> Le 0"
  by (metis cycle_free_diag order.trans neutral)
  
  from clock_numbering have cn: "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c" by auto
  show ?thesis
  proof (cases "i = 0")
    case True
    show ?thesis
    proof (cases "j = 0")
      case True
      with assms \<open>i = 0\<close> show ?thesis
      unfolding neutral DBM_zone_repr_def DBM_val_bounded_def less_eq by auto
    next
      case False
      then have "j > 0" by auto
      with \<open>j \<le> n\<close> clock_numbering obtain c2 where c2: "v c2 = j" by auto
      note t = canonical_saturated_2[OF _ _ \<open>cycle_free M n\<close> assms(1) assms(5)[folded c2] _ cn,unfolded c2]
      show ?thesis
      proof (rule ccontr, goal_cases)
        case 1
        { fix d assume 1: "M 0 j = \<infinity>"
          obtain r where r: "Le r \<le> M 0 j" "Le (-r) \<le> M j 0" "d < r"
          proof (cases "M j 0")
            case (Le d')
            obtain r where "r > - d'" using gt_ex by blast
            with Le 1 show ?thesis by (intro that[of "max r (d + 1)"]) auto
          next
            case (Lt d')
            obtain r where "r > - d'" using gt_ex by blast
            with Lt 1 show ?thesis by (intro that[of "max r (d + 1)"]) auto
          next
            case INF
            with 1 show ?thesis by (intro that[of "d + 1"]) auto
          qed
          then have "\<exists> r. Le r \<le> M 0 j \<and> Le (-r) \<le> M j 0 \<and> d < r" by auto
        } note inf_case = this
        { fix a b d :: real assume 1: "a < b" assume b: "b + d > 0"
          then have *: "b > -d" by auto
          obtain r where "r > - d" "r > a" "r < b"
          proof (cases "a \<ge> - d")
            case True
            from 1 obtain r where "r > a" "r < b" using dense by auto
            with True show ?thesis by (auto intro: that[of r])
          next
            case False
            with * obtain r where "r > -d" "r < b" using dense by auto
            with False show ?thesis by (auto intro: that[of r])
          qed
          then have "\<exists> r. r > -d \<and> r > a \<and> r < b" by auto
        } note gt_case = this
        { fix a r assume r: "Le r \<le> M 0 j" "Le (-r) \<le> M j 0" "a < r" "M' 0 j = Le a \<or> M' 0 j = Lt a"
          from t[OF this(1,2) \<open>0 < j\<close>] obtain u where u: "u \<in> [M]\<^bsub>v,n\<^esub>" "u c2 = - r" .
          with \<open>j \<le> n\<close> c2 assms(2) have "dbm_entry_val u None (Some c2) (M' 0 j)"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by blast
          with u(2) r(3,4) have False by auto
        } note contr = this
        from 1 True have "M' 0 j < M 0 j" by auto
        then show False unfolding less
        proof (cases rule: dbm_lt.cases)
          case (1 d)
          with inf_case obtain r where r: "Le r \<le> M 0 j" "Le (-r) \<le> M j 0" "d < r" by auto
          from contr[OF this] 1 show False by fast
        next
          case (2 d)
          with inf_case obtain r where r: "Le r \<le> M 0 j" "Le (-r) \<le> M j 0" "d < r" by auto
          from contr[OF this] 2 show False by fast
        next
          case (3 a b)
          obtain r where r: "Le r \<le> M 0 j" "Le (-r) \<le> M j 0" "a < r"
          proof (cases "M j 0")
            case (Le d')
            with 3 non_neg \<open>i = 0\<close> have "b + d' \<ge> 0" unfolding mult by auto
            then have "b \<ge> - d'" by auto
            with 3 obtain r where "r \<ge> - d'" "r > a" "r \<le> b" by blast
            with Le 3 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d')
            with 3 non_neg \<open>i = 0\<close> have "b + d' > 0" unfolding mult by auto
            from gt_case[OF 3(3) this] obtain r where "r > - d'" "r > a" "r \<le> b" by auto
            with Lt 3 show ?thesis by (intro that[of r]) auto
          next
            case INF
            with 3 show ?thesis by (intro that[of b]) auto
          qed
          from contr[OF this] 3 show False by fast
        next
          case (4 a b)
          obtain r where r: "Le r \<le> M 0 j" "Le (-r) \<le> M j 0" "a < r"
          proof (cases "M j 0")
            case (Le d)
            with 4 non_neg \<open>i = 0\<close> have "b + d > 0" unfolding mult by auto
            from gt_case[OF 4(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Le 4 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d)
            with 4 non_neg \<open>i = 0\<close> have "b + d > 0" unfolding mult by auto
            from gt_case[OF 4(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Lt 4 show ?thesis by (intro that[of r]) auto
          next
            case INF
            from 4 dense obtain r where "r > a" "r < b" by auto
            with 4 INF show ?thesis by (intro that[of r]) auto
          qed
          from contr[OF this] 4 show False by fast
        next
          case (5 a b)
          obtain r where r: "Le r \<le> M 0 j" "Le (-r) \<le> M j 0" "a \<le> r"
          proof (cases "M j 0")
            case (Le d')
            with 5 non_neg \<open>i = 0\<close> have "b + d' \<ge> 0" unfolding mult by auto
            then have "b \<ge> - d'" by auto
            with 5 obtain r where "r \<ge> - d'" "r \<ge> a" "r \<le> b" by blast
            with Le 5 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d')
            with 5 non_neg \<open>i = 0\<close> have "b + d' > 0" unfolding mult by auto
            then have "b > - d'" by auto
            with 5 obtain r where "r > - d'" "r \<ge> a" "r \<le> b" by blast
            with Lt 5 show ?thesis by (intro that[of r]) auto
          next
            case INF
            with 5 show ?thesis by (intro that[of b]) auto
          qed
          from t[OF this(1,2) \<open>j > 0\<close>] obtain u where u: "u \<in> [M]\<^bsub>v,n\<^esub>" "u c2 = - r" .
          with \<open>j \<le> n\<close> c2 assms(2) have "dbm_entry_val u None (Some c2) (M' 0 j)"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by blast
          with u(2) r(3) 5 show False by auto
        next
          case (6 a b)
          obtain r where r: "Le r \<le> M 0 j" "Le (-r) \<le> M j 0" "a < r"
          proof (cases "M j 0")
            case (Le d)
            with 6 non_neg \<open>i = 0\<close> have "b + d > 0" unfolding mult by auto
            from gt_case[OF 6(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Le 6 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d)
            with 6 non_neg \<open>i = 0\<close> have "b + d > 0" unfolding mult by auto
            from gt_case[OF 6(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Lt 6 show ?thesis by (intro that[of r]) auto
          next
            case INF
            from 6 dense obtain r where "r > a" "r < b" by auto
            with 6 INF show ?thesis by (intro that[of r]) auto
          qed
          from contr[OF this] 6 show False by fast
        qed
      qed
    qed
  next
    case False
    then have "i > 0" by auto
    with \<open>i \<le> n\<close> clock_numbering obtain c1 where c1: "v c1 = i" by auto
    show ?thesis
    proof (cases "j = 0")
      case True
      note t = canonical_saturated_1[OF _ _ \<open>cycle_free M n\<close> assms(1) assms(4)[folded c1] _ cn,
                                     unfolded c1]
      show ?thesis
      proof (rule ccontr, goal_cases)
        case 1
        { fix d assume 1: "M i 0 = \<infinity>"
          obtain r where r: "Le r \<le> M i 0" "Le (-r) \<le> M 0 i" "d < r"
          proof (cases "M 0 i")
            case (Le d')
            obtain r where "r > - d'" using gt_ex by blast
            with Le 1 show ?thesis by (intro that[of "max r (d + 1)"]) auto
          next
            case (Lt d')
            obtain r where "r > - d'" using gt_ex by blast
            with Lt 1 show ?thesis by (intro that[of "max r (d + 1)"]) auto
          next
            case INF
            with 1 show ?thesis by (intro that[of "d + 1"]) auto
          qed
          then have "\<exists> r. Le r \<le> M i 0 \<and> Le (-r) \<le> M 0 i \<and> d < r" by auto
        } note inf_case = this
        { fix a b d :: real assume 1: "a < b" assume b: "b + d > 0"
          then have *: "b > -d" by auto
          obtain r where "r > - d" "r > a" "r < b"
          proof (cases "a \<ge> - d")
            case True
            from 1 obtain r where "r > a" "r < b" using dense by auto
            with True show ?thesis by (auto intro: that[of r])
          next
            case False
            with * obtain r where "r > -d" "r < b" using dense by auto
            with False show ?thesis by (auto intro: that[of r])
          qed
          then have "\<exists> r. r > -d \<and> r > a \<and> r < b" by auto
        } note gt_case = this
        { fix a r assume r: "Le r \<le> M i 0" "Le (-r) \<le> M 0 i" "a < r" "M' i 0 = Le a \<or> M' i 0 = Lt a"
          from t[OF this(1,2) \<open>i > 0\<close>] obtain u where u: "u \<in> [M]\<^bsub>v,n\<^esub>" "u c1 = r" .
          with \<open>i \<le> n\<close> c1 assms(2) have "dbm_entry_val u (Some c1) None (M' i 0)"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by blast
          with u(2) r(3,4) have False by auto
        } note contr = this
        from 1 True have "M' i 0 < M i 0" by auto
        then show False unfolding less
        proof (cases rule: dbm_lt.cases)
          case (1 d)
          with inf_case obtain r where r: "Le r \<le> M i 0" "Le (-r) \<le> M 0 i" "d < r" by auto
          from contr[OF this] 1 show False by fast
        next
          case (2 d)
          with inf_case obtain r where r: "Le r \<le> M i 0" "Le (-r) \<le> M 0 i" "d < r" by auto
          from contr[OF this] 2 show False by fast
        next
          case (3 a b)
          obtain r where r: "Le r \<le> M i 0" "Le (-r) \<le> M 0 i" "a < r"
          proof (cases "M 0 i")
            case (Le d')
            with 3 non_neg \<open>j = 0\<close> have "b + d' \<ge> 0" unfolding mult by auto
            then have "b \<ge> - d'" by auto
            with 3 obtain r where "r \<ge> - d'" "r > a" "r \<le> b" by blast
            with Le 3 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d')
            with 3 non_neg \<open>j = 0\<close> have "b + d' > 0" unfolding mult by auto
            from gt_case[OF 3(3) this] obtain r where "r > - d'" "r > a" "r \<le> b" by auto
            with Lt 3 show ?thesis by (intro that[of r]) auto
          next
            case INF
            with 3 show ?thesis by (intro that[of b]) auto
          qed
          from contr[OF this] 3 show False by fast
        next
          case (4 a b)
          obtain r where r: "Le r \<le> M i 0" "Le (-r) \<le> M 0 i" "a < r"
          proof (cases "M 0 i")
            case (Le d)
            with 4 non_neg \<open>j = 0\<close> have "b + d > 0" unfolding mult by auto
            from gt_case[OF 4(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Le 4 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d)
            with 4 non_neg \<open>j = 0\<close> have "b + d > 0" unfolding mult by auto
            from gt_case[OF 4(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Lt 4 show ?thesis by (intro that[of r]) auto
          next
            case INF
            from 4 dense obtain r where "r > a" "r < b" by auto
            with 4 INF show ?thesis by (intro that[of r]) auto
          qed
          from contr[OF this] 4 show False by fast
        next
          case (5 a b)
          obtain r where r: "Le r \<le> M i 0" "Le (-r) \<le> M 0 i" "a \<le> r"
          proof (cases "M 0 i")
            case (Le d')
            with 5 non_neg \<open>j = 0\<close> have "b + d' \<ge> 0" unfolding mult by auto
            then have "b \<ge> - d'" by auto
            with 5 obtain r where "r \<ge> - d'" "r \<ge> a" "r \<le> b" by blast
            with Le 5 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d')
            with 5 non_neg \<open>j = 0\<close> have "b + d' > 0" unfolding mult by auto
            then have "b > - d'" by auto
            with 5 obtain r where "r > - d'" "r \<ge> a" "r \<le> b" by blast
            with Lt 5 show ?thesis by (intro that[of r]) auto
          next
            case INF
            with 5 show ?thesis by (intro that[of b]) auto
          qed
          from t[OF this(1,2) \<open>i > 0\<close>] obtain u where u: "u \<in> [M]\<^bsub>v,n\<^esub>" "u c1 = r" .
          with \<open>i \<le> n\<close> c1 assms(2) have "dbm_entry_val u (Some c1) None (M' i 0)"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by blast
          with u(2) r(3) 5 show False by auto
        next
          case (6 a b)
          obtain r where r: "Le r \<le> M i 0" "Le (-r) \<le> M 0 i" "a < r"
          proof (cases "M 0 i")
            case (Le d)
            with 6 non_neg \<open>j = 0\<close> have "b + d > 0" unfolding mult by auto
            from gt_case[OF 6(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Le 6 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d)
            with 6 non_neg \<open>j = 0\<close> have "b + d > 0" unfolding mult by auto
            from gt_case[OF 6(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Lt 6 show ?thesis by (intro that[of r]) auto
          next
            case INF
            from 6 dense obtain r where "r > a" "r < b" by auto
            with 6 INF show ?thesis by (intro that[of r]) auto
          qed
          from contr[OF this] 6 show False by fast
        qed
      qed
    next
      case False
      then have "j > 0" by auto
      with \<open>j \<le> n\<close> clock_numbering obtain c2 where c2: "v c2 = j" by auto
      note t = canonical_saturated_3[OF _ _ \<open>cycle_free M n\<close> assms(1) assms(4)[folded c1]
                                        assms(5)[folded c2] _ cn, unfolded c1 c2]
      show ?thesis
      proof (rule ccontr, goal_cases)
        case 1
        { fix d assume 1: "M i j = \<infinity>"
          obtain r where r: "Le r \<le> M i j" "Le (-r) \<le> M j i" "d < r"
          proof (cases "M j i")
            case (Le d')
            obtain r where "r > - d'" using gt_ex by blast
            with Le 1 show ?thesis by (intro that[of "max r (d + 1)"]) auto
          next
            case (Lt d')
            obtain r where "r > - d'" using gt_ex by blast
            with Lt 1 show ?thesis by (intro that[of "max r (d + 1)"]) auto
          next
            case INF
            with 1 show ?thesis by (intro that[of "d + 1"]) auto
          qed
          then have "\<exists> r. Le r \<le> M i j \<and> Le (-r) \<le> M j i \<and> d < r" by auto
        } note inf_case = this
        { fix a b d :: real assume 1: "a < b" assume b: "b + d > 0"
          then have *: "b > -d" by auto
          obtain r where "r > - d" "r > a" "r < b"
          proof (cases "a \<ge> - d")
            case True
            from 1 obtain r where "r > a" "r < b" using dense by auto
            with True show ?thesis by (auto intro: that[of r])
          next
            case False
            with * obtain r where "r > -d" "r < b" using dense by auto
            with False show ?thesis by (auto intro: that[of r])
          qed
          then have "\<exists> r. r > -d \<and> r > a \<and> r < b" by auto
        } note gt_case = this
        { fix a r assume r: "Le r \<le> M i j" "Le (-r) \<le> M j i" "a < r" "M' i j = Le a \<or> M' i j = Lt a"
          from t[OF this(1,2) \<open>i \<noteq> j\<close>] obtain u where u: "u \<in> [M]\<^bsub>v,n\<^esub>" "u c1 - u c2 = r" .
          with \<open>i \<le> n\<close> \<open>j \<le> n\<close> c1 c2 assms(2) have "dbm_entry_val u (Some c1) (Some c2) (M' i j)"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by blast
          with u(2) r(3,4) have False by auto
        } note contr = this
        from 1 have "M' i j < M i j" by auto
        then show False unfolding less
        proof (cases rule: dbm_lt.cases)
          case (1 d)
          with inf_case obtain r where r: "Le r \<le> M i j" "Le (-r) \<le> M j i" "d < r" by auto
          from contr[OF this] 1 show False by fast
        next
          case (2 d)
          with inf_case obtain r where r: "Le r \<le> M i j" "Le (-r) \<le> M j i" "d < r" by auto
          from contr[OF this] 2 show False by fast
        next
          case (3 a b)
          obtain r where r: "Le r \<le> M i j" "Le (-r) \<le> M j i" "a < r"
          proof (cases "M j i")
            case (Le d')
            with 3 non_neg have "b + d' \<ge> 0" unfolding mult by auto
            then have "b \<ge> - d'" by auto
            with 3 obtain r where "r \<ge> - d'" "r > a" "r \<le> b" by blast
            with Le 3 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d')
            with 3 non_neg have "b + d' > 0" unfolding mult by auto
            from gt_case[OF 3(3) this] obtain r where "r > - d'" "r > a" "r \<le> b" by auto
            with Lt 3 show ?thesis by (intro that[of r]) auto
          next
            case INF
            with 3 show ?thesis by (intro that[of b]) auto
          qed
          from contr[OF this] 3 show False by fast
        next
          case (4 a b)
          obtain r where r: "Le r \<le> M i j" "Le (-r) \<le> M j i" "a < r"
          proof (cases "M j i")
            case (Le d)
            with 4 non_neg have "b + d > 0" unfolding mult by auto
            from gt_case[OF 4(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Le 4 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d)
            with 4 non_neg have "b + d > 0" unfolding mult by auto
            from gt_case[OF 4(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Lt 4 show ?thesis by (intro that[of r]) auto
          next
            case INF
            from 4 dense obtain r where "r > a" "r < b" by auto
            with 4 INF show ?thesis by (intro that[of r]) auto
          qed
          from contr[OF this] 4 show False by fast
        next
          case (5 a b)
          obtain r where r: "Le r \<le> M i j" "Le (-r) \<le> M j i" "a \<le> r"
          proof (cases "M j i")
            case (Le d')
            with 5 non_neg have "b + d' \<ge> 0" unfolding mult by auto
            then have "b \<ge> - d'" by auto
            with 5 obtain r where "r \<ge> - d'" "r \<ge> a" "r \<le> b" by blast
            with Le 5 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d')
            with 5 non_neg have "b + d' > 0" unfolding mult by auto
            then have "b > - d'" by auto
            with 5 obtain r where "r > - d'" "r \<ge> a" "r \<le> b" by blast
            with Lt 5 show ?thesis by (intro that[of r]) auto
          next
            case INF
            with 5 show ?thesis by (intro that[of b]) auto
          qed
          from t[OF this(1,2) \<open>i \<noteq> j\<close>] obtain u where u: "u \<in> [M]\<^bsub>v,n\<^esub>" "u c1 - u c2= r" .
          with \<open>i \<le> n\<close> \<open>j \<le> n\<close> c1 c2 assms(2) have "dbm_entry_val u (Some c1) (Some c2) (M' i j)"
          unfolding DBM_zone_repr_def DBM_val_bounded_def by blast
          with u(2) r(3) 5 show False by auto
        next
          case (6 a b)
          obtain r where r: "Le r \<le> M i j" "Le (-r) \<le> M j i" "a < r"
          proof (cases "M j i")
            case (Le d)
            with 6 non_neg have "b + d > 0" unfolding mult by auto
            from gt_case[OF 6(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Le 6 show ?thesis by (intro that[of r]) auto
          next
            case (Lt d)
            with 6 non_neg have "b + d > 0" unfolding mult by auto
            from gt_case[OF 6(3) this] obtain r where "r > - d" "r > a" "r < b" by auto
            with Lt 6 show ?thesis by (intro that[of r]) auto
          next
            case INF
            from 6 dense obtain r where "r > a" "r < b" by auto
            with 6 INF show ?thesis by (intro that[of r]) auto
          qed
          from contr[OF this] 6 show False by fast
        qed
      qed
    qed
  qed
qed

lemma DBM_set_diag:
  assumes "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "[M]\<^bsub>v,n\<^esub> = [(\<lambda> i j. if i = j then Le 0 else M i j)]\<^bsub>v,n\<^esub>"
using non_empty_dbm_diag_set[OF clock_numbering(1) assms] unfolding neutral by auto

lemma DBM_le_subset':
  assumes "\<forall>i \<le> n. \<forall> j \<le> n. i \<noteq> j \<longrightarrow> M i j \<le> M' i j"
  and "\<forall> i\<le>n. M' i i \<ge> Le 0"
  and "u \<in> [M]\<^bsub>v,n\<^esub>"
  shows "u \<in> [M']\<^bsub>v,n\<^esub>"
proof -
  let ?M = "\<lambda> i j. if i = j then Le 0 else M i j"
  have "\<forall>i j. i \<le> n \<longrightarrow> j \<le> n \<longrightarrow> ?M i j \<le> M' i j" using assms(1,2) by auto
  moreover from DBM_set_diag assms(3) have "u \<in> [?M]\<^bsub>v,n\<^esub>" by auto
  ultimately show ?thesis using DBM_le_subset[folded less_eq, of n ?M M' u v] by auto
qed

lemma neg_diag_empty_spec:
  assumes "i \<le> n" "M i i < \<one>"
  shows "[M]\<^bsub>v,n\<^esub> = {}"
using assms neg_diag_empty[where v= v and M = M, OF _ assms] clock_numbering(2) by auto

lemma canonical_empty_zone_spec:
  assumes "canonical M n"
  shows "[M]\<^bsub>v,n\<^esub> = {} \<longleftrightarrow> (\<exists>i\<le>n. M i i < \<one>)"
using canonical_empty_zone[of n v M, OF _ _ assms] clock_numbering by auto

lemma norm_set_diag:
  assumes "canonical M n" "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  obtains M' where "[M]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>" "[norm M (k o v') n]\<^bsub>v,n\<^esub> = [norm M' (k o v') n]\<^bsub>v,n\<^esub>"
                   "\<forall> i \<le> n. M' i i = \<one>" "canonical M' n"
proof -
  from assms(2) neg_diag_empty_spec have *: "\<forall> i\<le>n. M i i \<ge> Le 0" unfolding neutral by force
  let ?M = "\<lambda>i j. if i = j then Le 0 else M i j"
  let ?NM = "norm M (k o v') n"
  let ?M2 = "\<lambda>i j. if i = j then Le 0 else ?NM i j"
  from assms have "[?NM]\<^bsub>v,n\<^esub> \<noteq> {}"
  by (metis Collect_empty_eq norm_mono DBM_zone_repr_def clock_numbering(1) mem_Collect_eq)
  from DBM_set_diag[OF this] DBM_set_diag[OF assms(2)] have
    "[M]\<^bsub>v,n\<^esub> = [?M]\<^bsub>v,n\<^esub>" "[?NM]\<^bsub>v,n\<^esub> = [?M2]\<^bsub>v,n\<^esub>"
  by auto
  moreover have "norm ?M (k o v') n = ?M2" unfolding norm_def by fastforce
  moreover have "\<forall> i \<le> n. ?M i i = \<one>" unfolding neutral by auto
  moreover have "canonical ?M n" using assms(1) *
  unfolding neutral[symmetric] less_eq[symmetric] mult[symmetric] by fastforce
  ultimately show ?thesis by (auto intro: that)
qed

lemma norm_normalizes:
  notes any_le_inf[intro]
  shows "normalized (norm M (k o v') n)"
unfolding normalized
proof (safe, goal_cases)
  case (1 i j)
  show ?case
  proof (cases "M i j < Lt (- real (k (v' j)))")
    case True with 1 show ?thesis unfolding norm_def less by (auto simp: Let_def)
  next
    case False
    with 1 show ?thesis unfolding norm_def by (auto simp: Let_def)
  qed
next
  case (2 i j)
  have **: "- real ((k o v') j) \<le> (k o v') i" by simp
  then have *: "Lt (- k (v' j)) < Le (k (v' i))" by (auto intro: Lt_lt_LeI)
  show ?case
  proof (cases "M i j \<le> Le (real (k (v' i)))")
    case False with 2 show ?thesis unfolding norm_def less_eq dbm_le_def by (auto simp: Let_def)
  next
    case True with 2 show ?thesis unfolding norm_def by (auto simp: Let_def)
  qed
next
  case (3 i)
  show ?case
  proof (cases "M i 0 \<le> Le (real (k (v' i)))")
    case False then have "Le (real (k (v' i))) \<prec> M i 0" unfolding less_eq dbm_le_def by auto
    with 3 show ?thesis unfolding norm_def by auto
  next
    case True
    with 3 show ?thesis unfolding norm_def less_eq dbm_le_def by (auto simp: Let_def)
  qed
next
  case (4 i)
  show ?case
  proof (cases "M 0 i < Lt (- real (k (v' i)))")
    case True with 4 show ?thesis unfolding norm_def less by auto
  next
    case False with 4 show ?thesis unfolding norm_def by (auto simp: Let_def)
  qed
qed

lemma norm_int_preservation:
  assumes "dbm_int M n" "i \<le> n" "j \<le> n" "norm M (k o v') n i j \<noteq> \<infinity>"
  shows "get_const (norm M (k o v') n i j) \<in> \<int>"
using assms unfolding norm_def by (auto simp: Let_def)

lemma norm_V_preservation':
  notes any_le_inf[intro]
  assumes "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "canonical M n" "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "[norm M (k o v') n]\<^bsub>v,n\<^esub> \<subseteq> V"
proof -
  let ?M = "norm M (k o v') n"
  from non_empty_cycle_free[OF assms(3)] clock_numbering(2) have *: "cycle_free M n" by auto
  { fix c assume "c \<in> X"
    with clock_numbering have c: "c \<in> X" "v c > 0" "v c \<le> n" by auto
    with assms(2) have
      "M 0 (v c) + M (v c) 0 \<ge> M 0 0"
    unfolding mult less_eq by blast
    moreover from cycle_free_diag[OF *] have "M 0 0 \<ge> Le 0" unfolding neutral by auto
    ultimately have ge_0: "M 0 (v c) + M (v c) 0 \<ge> Le 0" by auto
    have "M 0 (v c) \<le> Le 0"
    proof (cases "M 0 (v c)")
      case (Le d)
      with ge_0 have "M (v c) 0 \<ge> Le (-d)"
       apply (cases "M (v c) 0")
         unfolding mult apply auto
         apply (rename_tac x1)
         apply (subgoal_tac "-d \<le> x1")
         apply auto
       apply (rename_tac x2)
       apply (subgoal_tac "-d < x2")
      by auto
      with Le canonical_saturated_2[OF _ _ \<open>cycle_free M n\<close> assms(2) c(3)] clock_numbering(1)
      obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = -d" by auto
      with assms(1) c(1) Le show ?thesis unfolding V_def by fastforce
    next
      case (Lt d)
      show ?thesis
      proof (cases "d \<le> 0")
        case True
        then have "Lt d < Le 0" by (auto intro: Lt_lt_LeI)
        with Lt show ?thesis by auto
      next
        case False
        then have "d > 0" by auto
        note Lt' = Lt
        show ?thesis
        proof (cases "M (v c) 0")
          case (Le d')
          with Lt ge_0 have *: "d > -d'" unfolding mult by auto
          show ?thesis
          proof (cases "d' < 0")
            case True
            from * clock_numbering(1) canonical_saturated_1[OF _ _ \<open>cycle_free _ _\<close> assms(2) c(3)] Lt Le
            obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = d'" by auto
            with \<open>d' < 0\<close> assms(1) \<open>c \<in> X\<close> show ?thesis unfolding V_def by fastforce
          next
            case False
            then have "d' \<ge> 0" by auto
            with \<open>d > 0\<close> have "Le (d / 2) \<le> Lt d" "Le (- (d /2)) \<le> Le d'" by auto
            with canonical_saturated_2[OF _ _ \<open>cycle_free _ _\<close> assms(2) c(3)] Lt Le clock_numbering(1)
            obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = - (d / 2)" by auto
            with \<open>d > 0\<close> assms(1) \<open>c \<in> X\<close> show ?thesis unfolding V_def by fastforce
          qed
        next
          case (Lt d')
          with Lt' ge_0 have *: "d > -d'" unfolding mult by auto
          then have **: "-d < d'" by auto
          show ?thesis
          proof (cases "d' \<le> 0")
            case True
            from assms(1,3) c obtain u where u:
              "u \<in> V" "dbm_entry_val u (Some c) None (M (v c) 0)"
            unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
            with u(1) True Lt \<open>c \<in> X\<close> show ?thesis unfolding V_def by auto
          next
            case False
            with \<open>d > 0\<close> have "Le (d / 2) \<le> Lt d" "Le (- (d /2)) \<le> Lt d'" by auto
            with canonical_saturated_2[OF _ _ \<open>cycle_free _ _\<close> assms(2) c(3)] Lt Lt' clock_numbering(1)
            obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = - (d / 2)" by auto
            with \<open>d > 0\<close> assms(1) \<open>c \<in> X\<close> show ?thesis unfolding V_def by fastforce
          qed
        next
          case INF
          show ?thesis
          proof (cases "d > 0")
            case True
            from \<open>d > 0\<close> have "Le (d / 2) \<le> Lt d" by auto
            with INF canonical_saturated_2[OF _ _ \<open>cycle_free _ _\<close> assms(2) c(3)] Lt clock_numbering(1)
            obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = - (d / 2)" by auto
            with \<open>d > 0\<close> assms(1) \<open>c \<in> X\<close> show ?thesis unfolding V_def by fastforce
          next
            case False
            with Lt show ?thesis by auto
          qed
        qed
      qed
    next
      case INF
      obtain u r where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = - r" "r > 0"
      proof (cases "M (v c) 0")
        case (Le d)
        let ?d = "if d \<le> 0 then -d + 1 else d"
        from Le INF canonical_saturated_2[OF _ _ \<open>cycle_free _ _\<close> assms(2) c(3), of ?d] clock_numbering(1)
        obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = - ?d" by (cases "d < 0") force+
        from that[OF this] show thesis by auto
      next
        case (Lt d)
        let ?d = "if d \<le> 0 then -d + 1 else d"
        from Lt INF canonical_saturated_2[OF _ _ \<open>cycle_free _ _\<close> assms(2) c(3), of ?d] clock_numbering(1)
        obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = - ?d" by (cases "d < 0") force+
        from that[OF this] show thesis by auto
      next
        case INF
        with \<open>M 0 (v c) = \<infinity>\<close> canonical_saturated_2[OF _ _ \<open>cycle_free _ _\<close> assms(2) c(3)] clock_numbering(1)
        obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c = - 1" by auto
        from that[OF this] show thesis by auto
      qed
      with assms(1) \<open>c \<in> X\<close> show ?thesis unfolding V_def by fastforce
    qed
    moreover then have "\<not> Le 0 \<prec> M 0 (v c)" unfolding less[symmetric] by auto
    ultimately have *: "?M 0 (v c) \<le> Le 0" using assms(3) c unfolding norm_def by (auto simp: Let_def)
    fix u assume u: "u \<in> [?M]\<^bsub>v,n\<^esub>"
    with c have "dbm_entry_val u None (Some c) (?M 0 (v c))"
    unfolding DBM_val_bounded_def DBM_zone_repr_def by auto
    with * have "u c \<ge> 0" by (cases "?M 0 (v c)") auto
  } note ge_0 = this
  then show ?thesis unfolding V_def by auto
qed

lemma norm_V_preservation:
  assumes "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "canonical M n"
  shows "[norm M (k o v') n]\<^bsub>v,n\<^esub> \<subseteq> V" (is "[?M]\<^bsub>v,n\<^esub> \<subseteq> V")
proof (cases "[M]\<^bsub>v,n\<^esub> = {}")
  case True
  obtain i where i: "i \<le> n" "M i i < \<one>" by (metis True assms(2) canonical_empty_zone_spec)
  have "\<not> Le (k (v' i)) < Le 0" unfolding less by (cases "k (v' i) = 0", auto)
  with i have "?M i i < \<one>" unfolding norm_def by (auto simp: neutral less Let_def)
  with neg_diag_empty_spec[OF \<open>i \<le> n\<close>] have "[?M]\<^bsub>v,n\<^esub> = {}" .
  then show ?thesis by auto
next
  case False
  from norm_set_diag[OF assms(2) False] norm_V_preservation' False assms
  show ?thesis by metis
qed

lemma norm_min:
  assumes "normalized M1" "[M]\<^bsub>v,n\<^esub> \<subseteq> [M1]\<^bsub>v,n\<^esub>"
          "canonical M n" "[M]\<^bsub>v,n\<^esub> \<noteq> {}" "[M]\<^bsub>v,n\<^esub> \<subseteq> V"
  shows "[norm M (k o v') n]\<^bsub>v,n\<^esub> \<subseteq> [M1]\<^bsub>v,n\<^esub>" (is "[?M2]\<^bsub>v,n\<^esub> \<subseteq> [M1]\<^bsub>v,n\<^esub>")
proof -
  have le: "\<And> i j. i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> i \<noteq> j\<Longrightarrow> M i j \<le> M1 i j" using assms(2,3,4)
  by (auto intro!: DBM_canonical_subset_le)
  from assms have "[M1]\<^bsub>v,n\<^esub> \<noteq> {}" by auto
  with neg_diag_empty_spec have *: "\<forall> i\<le>n. M1 i i \<ge> Le 0" unfolding neutral by force
  from assms norm_V_preservation have V: "[?M2]\<^bsub>v,n\<^esub> \<subseteq> V" by auto
  have "u \<in> [M1]\<^bsub>v,n\<^esub>" if "u \<in> [?M2]\<^bsub>v,n\<^esub>" for u
  proof -
    from that V have V: "u \<in> V" by fast
    show ?thesis unfolding DBM_zone_repr_def DBM_val_bounded_def
    proof (safe, goal_cases)
      case 1 with * show ?case unfolding less_eq by fast
    next
      case (2 c)
      then have c: "v c > 0" "v c \<le> n" "c \<in> X" "v' (v c) = c" using clock_numbering v_v' by metis+
      with V have v_bound: "dbm_entry_val u None (Some c) (Le 0)" unfolding V_def by auto
      from that c have bound:
        "dbm_entry_val u None (Some c) (?M2 0 (v c))"
      unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
      show ?case
      proof (cases "M 0 (v c) < Lt (- k c)")
        case False
        show ?thesis
        proof (cases "Le 0 < M 0 (v c)")
          case True
          with le c(1,2) have "Le 0 \<le> M1 0 (v c)" by fastforce
          with dbm_entry_val_mono_2[OF v_bound, folded less_eq] show ?thesis by fast
        next
          case F: False
          with assms(3) False c have "?M2 0 (v c) = M 0 (v c)" unfolding less norm_def by auto
          with le c bound show ?thesis by (auto intro: dbm_entry_val_mono_2[folded less_eq])
        qed
      next
        case True
        have "Lt (- k c) \<prec> Le 0" by auto
        with True c assms(3) have "?M2 0 (v c) = Lt (- k c)" unfolding less norm_def by auto
        moreover from assms(1) c have "Lt (- k c) \<le> M1 0 (v c)" unfolding normalized by auto
        ultimately show ?thesis using le c bound by (auto intro: dbm_entry_val_mono_2[folded less_eq])
      qed
    next
      case (3 c)
      then have c: "v c > 0" "v c \<le> n" "c \<in> X" "v' (v c) = c" using clock_numbering v_v' by metis+
      from that c have bound:
        "dbm_entry_val u (Some c) None (?M2 (v c) 0)"
      unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
      show ?case
      proof (cases "M (v c) 0 \<le> Le (k c)")
        case False
        with le c have "\<not> M1 (v c) 0 \<le> Le (k c)" by fastforce
        with assms(1) c show ?thesis unfolding normalized by fastforce
      next
        case True
        show ?thesis
        proof (cases "M (v c) 0 < Lt 0")
          case T: True
          have "\<not> Le (real (k c)) \<prec> Lt 0" by auto
          with T True c have "?M2 (v c) 0 = Lt 0" unfolding norm_def less by (auto simp: Let_def)
          with bound V c show ?thesis unfolding V_def by auto
        next
          case False
          with True assms(3) c have "?M2 (v c) 0 = M (v c) 0" unfolding less less_eq norm_def
          by (auto simp: Let_def)
          with dbm_entry_val_mono_3[OF bound, folded less_eq] le c show ?thesis by auto
        qed
      qed
    next
      case (4 c1 c2)
      then have c:
        "v c1 > 0" "v c1 \<le> n" "c1 \<in> X" "v' (v c1) = c1" "v c2 > 0" "v c2 \<le> n" "c2 \<in> X" "v' (v c2) = c2"
      using clock_numbering v_v' by metis+
      from that c have bound:
        "dbm_entry_val u (Some c1) (Some c2) (?M2 (v c1) (v c2))"
      unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
      show ?case
      proof (cases "c1 = c2")
        case True
        then have "dbm_entry_val u (Some c1) (Some c2) (Le 0)" by auto
        with c True * dbm_entry_val_mono_1[OF this, folded less_eq] show ?thesis by auto
      next
        case False
        with clock_numbering(1) \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> have neq: "v c1 \<noteq> v c2" by auto
        show ?thesis
        proof (cases "Le (k c1) < M (v c1) (v c2)")
          case False
          show ?thesis
          proof (cases "M (v c1) (v c2) < Lt (- real (k c2))")
            case F: False
            with c False assms(3) have
              "?M2 (v c1) (v c2) = M (v c1) (v c2)"
            unfolding norm_def less by auto
            with dbm_entry_val_mono_1[OF bound, folded less_eq] le c neq show ?thesis by auto
          next
            case True
            with c False assms(3) have "?M2 (v c1) (v c2) = Lt (- k c2)" unfolding less norm_def
            by auto
            moreover from assms(1) c have "M1 (v c1) (v c2) = \<infinity> \<or> M1 (v c1) (v c2) \<ge> Lt (- k c2)"
            unfolding normalized by fastforce
            ultimately show ?thesis using dbm_entry_val_mono_1[OF bound, folded less_eq] by auto
          qed
        next
          case True
          with le c neq have "M1 (v c1) (v c2) > Le (k c1)" by fastforce
          moreover from True c assms(3) have "?M2 (v c1) (v c2) = \<infinity>" unfolding norm_def less
          by auto
          moreover from assms(1) c have "M1 (v c1) (v c2) = \<infinity> \<or> M1 (v c1) (v c2) \<le> Le (k c1)"
          unfolding normalized by fastforce
          ultimately show ?thesis by auto
        qed
      qed
    qed
  qed
  then show ?thesis by blast
qed

lemma apx_norm_eq:
  assumes "canonical M n" "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "dbm_int M n"
  shows "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) = [norm M (k o v') n]\<^bsub>v,n\<^esub>"
proof -
  let ?M = "norm M (k o v') n"
  from assms norm_V_preservation norm_int_preservation norm_normalizes
  have *: "vabstr ([?M]\<^bsub>v,n\<^esub>) ?M" "normalized ?M" "[?M]\<^bsub>v,n\<^esub> \<subseteq> V" by presburger+
  from dbm_regions'[OF this] obtain U where U: "U \<subseteq> \<R>" "[?M]\<^bsub>v,n\<^esub> = \<Union>U" by auto
  from assms(3) have **: "[M]\<^bsub>v,n\<^esub> \<subseteq> [?M]\<^bsub>v,n\<^esub>" by (simp add: norm_mono clock_numbering(1) subsetI) 
  show ?thesis
  proof (cases "[M]\<^bsub>v,n\<^esub> = {}")
    case True
    from canonical_empty_zone_spec[OF \<open>canonical M n\<close>] True obtain i where i:
      "i \<le> n" "M i i < \<one>"
    by auto
    with assms(3) have "?M i i < \<one>" unfolding neutral norm_def
    proof (cases "i = 0", auto intro: Lt_lt_LeI, goal_cases)
      case 1
      then show ?case unfolding less by auto
    next
      case 2
      have "\<not> Le (real (k (v' i))) \<prec> Le 0" by auto
      with 2 show ?case by (auto simp: Let_def less)
    qed
    from neg_diag_empty[of n v i ?M, OF _ \<open>i \<le> n\<close> this] clock_numbering have
      "[?M]\<^bsub>v,n\<^esub> = {}"
    by (auto intro: Lt_lt_LeI)
    with apx_empty True show ?thesis by auto
  next
    case False
    from apx_in[OF assms(2)] obtain U' M1 where U':
      "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) = \<Union>U'" "U' \<subseteq> \<R>" "[M]\<^bsub>v,n\<^esub> \<subseteq> Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>)"
      "vabstr (Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>)) M1" "normalized M1"
    by auto
    from norm_min[OF U'(5) _ assms(1) False assms(2)] U'(3,4) *(1) apx_min[OF U(2,1) _ _ *(2) **]
    show ?thesis by blast
  qed
qed

end        


section \<open>Auxiliary \<open>\<beta>\<close>-boundedness Theorems\<close>

context Beta_Regions'
begin

lemma \<beta>_boundedness_diag_lt:
  fixes m :: int
  assumes "- k y \<le> m" "m \<le> k x" "x \<in> X" "y \<in> X"
  shows "\<exists> U \<subseteq> \<R>. \<Union> U = {u \<in> V. u x - u y < m}"
proof -
  note A = assms
  note B = A(1,2)
  let ?U = "{R \<in> \<R>. \<exists> I J r c d (e :: int). R = region X I J r \<and> valid_region X k I J r \<and>
    (I x = Const c \<and> I y = Const d \<and> real c - d < m \<or>
     I x = Const c \<and> I y = Intv d  \<and> real c - d \<le> m \<or>
     I x = Intv c  \<and> I y = Const d \<and> real c + 1 - d \<le> m \<or>
     I x = Intv c  \<and> I y = Intv d  \<and> real c - d \<le> m \<and> (x,y) \<in> r \<and> (y, x) \<notin> r \<or>
     I x = Intv c  \<and> I y = Intv d  \<and> real c - d < m \<and> (y, x) \<in> r \<or>
     (I x = Greater (k x) \<or> I y = Greater (k y)) \<and> J x y = Smaller' (- k y) \<or>
     (I x = Greater (k x) \<or> I y = Greater (k y)) \<and> J x y = Intv' e  \<and> e < m \<or>
     (I x = Greater (k x) \<or> I y = Greater (k y)) \<and> J x y = Const' e \<and> e < m
    )}"
  { fix u I J r assume "u \<in> region X I J r" "I x = Greater (k x) \<or> I y = Greater (k y)"
    with A(3,4) have "intv'_elem x y u (J x y)" by force
  } note * = this
  { fix u I J r assume "u \<in> region X I J r"
    with A(3,4) have "intv_elem x u (I x)" "intv_elem y u (I y)" by force+
  } note ** = this
  have "\<Union> ?U = {u \<in> V. u x - u y < m}"
  proof (safe, goal_cases)
    case (2 u) with **[OF this(1)] show ?case by auto
  next
    case (4 u) with **[OF this(1)] show ?case by auto
  next
    case (6 u) with **[OF this(1)] show ?case by auto
  next
    case (8 u X I J r c d)
    from this A(3,4) have "intv_elem x u (I x)" "intv_elem y u (I y)" "frac (u x) < frac (u y)" by force+
    with nat_intv_frac_decomp 8(4,5) have
      "u x = c + frac (u x)" "u y = d + frac (u y)" "frac (u x) < frac (u y)"
    by force+
    with 8(6) show ?case by linarith
  next
    case (10 u X I J r c d)
    with **[OF this(1)] 10(4,5) have "u x < c + 1" "d < u y" by auto
    then have "u x - u y < real (c + 1) - real d" by linarith
    moreover from 10(6) have "real c + 1 - d \<le> m"
    proof -
      have "int c - int d < m"
        using 10(6) by linarith
      then show ?thesis
        by simp
    qed
    ultimately show ?case by linarith
  next
    case 12 with *[OF this(1)] B show ?case by auto
  next
    case 14 with *[OF this(1)] B show ?case by auto
  next
    case (23 u)
    from region_cover_V[OF this(1)] obtain R where R: "R \<in> \<R>" "u \<in> R" by auto
    then obtain I J r where R': "R = region X I J r" "valid_region X k I J r" unfolding \<R>_def by auto
    with R' R(2) A have C:
      "intv_elem x u (I x)" "intv_elem y u (I y)" "valid_intv (k x) (I x)" "valid_intv (k y) (I y)"
    by auto
    { assume A: "I x = Greater (k x) \<or> I y = Greater (k y)"
      obtain intv and d :: int where intv:
        "valid_intv' (k y) (k x) intv" "intv'_elem x y u intv"
        "intv = Smaller' (- k y) \<or> intv = Intv' d \<and> d < m \<or> intv = Const' d \<and> d < m"
      proof (cases "u x - u y < - int (k y)")
        case True
        have "valid_intv' (k y) (k x) (Smaller' (- k y))" ..
        moreover with True have "intv'_elem x y u (Smaller' (- k y))" by auto
        ultimately show thesis by (auto intro: that)
      next
        case False
        show thesis
        proof (cases "\<exists> (c :: int). u x - u y = c")
          case True
          then obtain c :: int where c: "u x - u y = c" by auto
          have "valid_intv' (k y) (k x) (Const' c)" using False B(2) 23(2) c by fastforce
          moreover with c have "intv'_elem x y u (Const' c)" by auto
          moreover have "c < m" using c 23(2) by auto
          ultimately show thesis by (auto intro: that)
        next
          case False
          then obtain c :: real where c: "u x - u y = c" "c \<notin> \<int>" by (metis Ints_cases)
          have "valid_intv' (k y) (k x) (Intv' (floor c))"
          proof
            show "- int (k y) \<le> \<lfloor>c\<rfloor>" using \<open>\<not> _ < _\<close> c by linarith
            show "\<lfloor>c\<rfloor> < int (k x)" using B(2) 23(2) c by linarith
          qed
          moreover have "intv'_elem x y u (Intv' (floor c))"
          proof
            from c(1,2) show "\<lfloor>c\<rfloor> < u x - u y" by (meson False eq_iff not_le of_int_floor_le)
            from c(1,2) show "u x - u y < \<lfloor>c\<rfloor> + 1" by simp
          qed
          moreover have "\<lfloor>c\<rfloor> < m" using c 23(2) by linarith
          ultimately show thesis using that by auto
        qed
      qed
      let ?J = "\<lambda> a b. if x = a \<and> y = b then intv else J a b"
      let ?R = "region X I ?J r"
      let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
      have "u \<in> ?R"
      proof (standard, goal_cases)
        case 1 from R R' show ?case by auto
      next
        case 2 from R R' show ?case by auto
      next
        case 3 show "?X\<^sub>0 = ?X\<^sub>0" by auto
      next
        case 4 from R R' show "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)" by auto
      next
        case 5
        show ?case
        proof (clarify, goal_cases)
          case (1 a b)
          show ?case
          proof (cases "x = a \<and> y = b")
            case True with intv show ?thesis by auto
          next
            case False
            with R(2) R'(1) 1 show ?thesis by force
          qed
        qed
      qed
      have "valid_region X k I ?J r"
      proof
        show "?X\<^sub>0 = ?X\<^sub>0" ..
        show "refl_on ?X\<^sub>0 r" using R' by auto
        show "trans r" using R' by auto
        show "total_on ?X\<^sub>0 r" using R' by auto
        show "\<forall>x\<in>X. valid_intv (k x) (I x)" using R' by auto
        show "\<forall>xa\<in>X. \<forall>ya\<in>X. isGreater (I xa) \<or> isGreater (I ya)
              \<longrightarrow> valid_intv' (int (k ya)) (int (k xa)) (if x = xa \<and> y = ya then intv else J xa ya)"
        proof (clarify, goal_cases)
          case (1 a b)
          show ?case
          proof (cases "x = a \<and> y = b")
            case True
            with B intv show ?thesis by auto
          next
            case False
            with R'(2) 1 show ?thesis by force
          qed
        qed
      qed
      moreover then have "?R \<in> \<R>" unfolding \<R>_def by auto
      ultimately have "?R \<in> ?U" using intv
        apply clarify
        apply (rule exI[where x = I], rule exI[where x = ?J], rule exI[where x = r])
      using A by fastforce
      with \<open>u \<in> region _ _ _ _\<close> have ?case by (intro Complete_Lattices.UnionI) blast+
    } note * = this
    show ?case
    proof (cases "I x")
      case (Const c)
      show ?thesis
      proof (cases "I y", goal_cases)
        case (1 d)
        with C(1,2) Const A(2,3) 23(2) have "real c - real d < m" by auto
        with Const 1 R R' show ?thesis by blast
      next
        case (Intv d)
        with C(1,2) Const A(2,3) 23(2) have "real c - (d + 1) < m" by auto
        then have "c < 1 + (d + m)" by linarith
        then have "real c - d \<le> m" by simp
        with Const Intv R R' show ?thesis by blast
      next
        case (Greater d) with * C(4) show ?thesis by auto
      qed
    next
      case (Intv c)
      show ?thesis
      proof (cases "I y", goal_cases)
        case (Const d)
        with C(1,2) Intv A(2,3) 23(2) have "real c - d < m" by auto
        then have "real c < m + d" by linarith
        then have "c < m + d" by linarith 
        then have "real c + 1 - d \<le> m" by simp
        with Const Intv R R' show ?thesis by blast
      next
        case (2 d)
        show ?thesis
        proof (cases "(y, x) \<in> r")
          case True
          with C(1,2) R R' Intv 2 A(3,4) have
            "c < u x" "u x < c + 1" "d < u y" "u y < d + 1" "frac (u x) \<ge> frac (u y)"
          by force+
          with 23(2) nat_intv_frac_decomp have "c + frac (u x) - (d + frac (u y)) < m" by auto
          with \<open>frac _ \<ge> _\<close> have "real c - real d < m" by linarith
          with Intv 2 True R R' show ?thesis by blast
        next
          case False
          with R R' A(3,4) Intv 2 have "(x,y) \<in> r" by fastforce
          with C(1,2) R R' Intv 2 have "c < u x" "u y < d + 1" by force+
          with 23(2) have "c < 1 + d + m" by auto
          then have "real c - d \<le> m" by simp
          with Intv 2 False \<open>_ \<in> r\<close> R R' show ?thesis by blast
        qed
      next
        case (Greater d) with * C(4) show ?thesis by auto
      qed
    next
      case (Greater d) with * C(3) show ?thesis by auto
    qed
  qed (auto intro: A simp: V_def, (fastforce dest!: *)+)
  moreover have "?U \<subseteq> \<R>" by fastforce
  ultimately show ?thesis by blast
qed

lemma \<beta>_boundedness_diag_eq:
  fixes m :: int
  assumes "- k y \<le> m" "m \<le> k x" "x \<in> X" "y \<in> X"
  shows "\<exists> U \<subseteq> \<R>. \<Union> U = {u \<in> V. u x - u y = m}"
proof -
  note A = assms
  note B = A(1,2)
  let ?U = "{R \<in> \<R>. \<exists> I J r c d (e :: int). R = region X I J r \<and> valid_region X k I J r \<and>
    (I x = Const c \<and> I y = Const d \<and> real c - d = m \<or>
     I x = Intv c  \<and> I y = Intv d  \<and> real c - d = m \<and> (x, y) \<in> r \<and> (y, x) \<in> r \<or>
     (I x = Greater (k x) \<or> I y = Greater (k y)) \<and> J x y = Const' e \<and> e = m
    )}"
  { fix u I J r assume "u \<in> region X I J r" "I x = Greater (k x) \<or> I y = Greater (k y)"
    with A(3,4) have "intv'_elem x y u (J x y)" by force
  } note * = this
  { fix u I J r assume "u \<in> region X I J r"
    with A(3,4) have "intv_elem x u (I x)" "intv_elem y u (I y)" by force+
  } note ** = this
  have "\<Union> ?U = {u \<in> V. u x - u y = m}"
  proof (safe, goal_cases)
    case (2 u) with **[OF this(1)] show ?case by auto
  next
    case (4 u X I J r c d)
    from this A(3,4) have "intv_elem x u (I x)" "intv_elem y u (I y)" "frac (u x) = frac (u y)" by force+
    with nat_intv_frac_decomp 4(4,5) have
      "u x = c + frac (u x)" "u y = d + frac (u y)" "frac (u x) = frac (u y)"
    by force+
    with 4(6) show ?case by linarith
  next
    case (9 u)
    from region_cover_V[OF this(1)] obtain R where R: "R \<in> \<R>" "u \<in> R" by auto
    then obtain I J r where R': "R = region X I J r" "valid_region X k I J r" unfolding \<R>_def by auto
    with R' R(2) A have C:
      "intv_elem x u (I x)" "intv_elem y u (I y)" "valid_intv (k x) (I x)" "valid_intv (k y) (I y)"
    by auto
    { assume A: "I x = Greater (k x) \<or> I y = Greater (k y)"
      obtain intv where intv:
        "valid_intv' (k y) (k x) intv" "intv'_elem x y u intv" "intv = Const' m"
      proof (cases "u x - u y < - int (k y)")
        case True
        with 9 B show ?thesis by auto
      next
        case False
        show thesis
        proof (cases "\<exists> (c :: int). u x - u y = c")
          case True
          then obtain c :: int where c: "u x - u y = c" by auto
          have "valid_intv' (k y) (k x) (Const' c)" using False B(2) 9(2) c by fastforce
          moreover with c have "intv'_elem x y u (Const' c)" by auto
          moreover have "c = m" using c 9(2) by auto
          ultimately show thesis by (auto intro: that)
        next
          case False
          then have "u x - u y \<notin> \<int>" by (metis Ints_cases)
          with 9 show ?thesis by auto
        qed
      qed
      let ?J = "\<lambda> a b. if x = a \<and> y = b then intv else J a b"
      let ?R = "region X I ?J r"
      let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
      have "u \<in> ?R"
      proof (standard, goal_cases)
        case 1 from R R' show ?case by auto
      next
        case 2 from R R' show ?case by auto
      next
        case 3 show "?X\<^sub>0 = ?X\<^sub>0" by auto
      next
        case 4 from R R' show "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)" by auto
      next
        case 5
        show ?case
        proof (clarify, goal_cases)
          case (1 a b)
          show ?case
          proof (cases "x = a \<and> y = b")
            case True with intv show ?thesis by auto
          next
            case False with R(2) R'(1) 1 show ?thesis by force
          qed
        qed
      qed
      have "valid_region X k I ?J r"
      proof (standard, goal_cases)
        show "?X\<^sub>0 = ?X\<^sub>0" ..
        show "refl_on ?X\<^sub>0 r" using R' by auto
        show "trans r" using R' by auto
        show "total_on ?X\<^sub>0 r" using R' by auto
        show "\<forall>x\<in>X. valid_intv (k x) (I x)" using R' by auto
      next
        case 6
        then show ?case
        proof (clarify, goal_cases)
          case (1 a b)
          show ?case
          proof (cases "x = a \<and> y = b")
            case True with B intv show ?thesis by auto
          next
            case False with R'(2) 1 show ?thesis by force
          qed
        qed
      qed
      moreover then have "?R \<in> \<R>" unfolding \<R>_def by auto
      ultimately have "?R \<in> ?U" using intv
        apply clarify
        apply (rule exI[where x = I], rule exI[where x = ?J], rule exI[where x = r])
      using A by fastforce
      with \<open>u \<in> region _ _ _ _\<close> have ?case by (intro Complete_Lattices.UnionI) blast+
    } note * = this
    show ?case
    proof (cases "I x")
      case (Const c)
      show ?thesis
      proof (cases "I y", goal_cases)
        case (1 d)
        with C(1,2) Const A(2,3) 9(2) have "real c - d = m" by auto
        with Const 1 R R' show ?thesis by blast
      next
        case (Intv d)
        from Intv Const C(1,2) have range: "d < u y" "u y < d + 1" and eq: "u x = c" by auto
        from eq have "u x \<in> \<int>" by auto
        with nat_intv_not_int[OF range] have "u x - u y \<notin> \<int>" using Ints_diff by fastforce
        with 9 show ?thesis by auto
      next
        case Greater with C * show ?thesis by auto
      qed
    next
      case (Intv c)
      show ?thesis
      proof (cases "I y", goal_cases)
        case (Const d)
        from Intv Const C(1,2) have range: "c < u x" "u x < c + 1" and eq: "u y = d" by auto
        from eq have "u y \<in> \<int>" by auto
        with nat_intv_not_int[OF range] have "u x - u y \<notin> \<int>" using Ints_add by fastforce
        with 9 show ?thesis by auto
      next
        case (2 d)
        with Intv C have range: "c < u x" "u x < c + 1" "d < u y" "u y < d + 1" by auto
        show ?thesis
        proof (cases "(x, y) \<in> r")
          case True
          note T = this
          show ?thesis
          proof (cases "(y, x) \<in> r")
            case True
            with Intv 2 T R' \<open>u \<in> R\<close> A(3,4) have "frac (u x) = frac (u y)" by force
            with nat_intv_frac_decomp[OF range(1,2)] nat_intv_frac_decomp[OF range(3,4)] have
              "u x - u y = real c - real d"
            by algebra
            with 9 have "real c - d = m" by auto
            with T True Intv 2 R R' show ?thesis by force
          next
            case False
            with Intv 2 T R' \<open>u \<in> R\<close> A(3,4) have "frac (u x) < frac (u y)" by force
            then have
              "frac (u x - u y) \<noteq> 0"
            by (metis add.left_neutral diff_add_cancel frac_add frac_unique_iff less_irrefl)
            then have "u x - u y \<notin> \<int>" by (metis frac_eq_0_iff)
            with 9 show ?thesis by auto
          qed
        next
          case False
          note F = this
          show ?thesis
          proof (cases "x = y")
            case True
            with R'(2) Intv \<open>x \<in> X\<close> have "(x, y) \<in> r" "(y, x) \<in> r" by (auto simp: refl_on_def)
            with Intv True R' R 9(2) show ?thesis by force
          next
            case False
            with F R'(2) Intv 2 \<open>x \<in> X\<close> \<open>y \<in> X\<close> have "(y, x) \<in> r" by (fastforce simp: total_on_def)
            with F Intv 2 R' \<open>u \<in> R\<close> A(3,4) have "frac (u x) > frac (u y)" by force
            then have
              "frac (u x - u y) \<noteq> 0"
            by (metis add.left_neutral diff_add_cancel frac_add frac_unique_iff less_irrefl)
            then have "u x - u y \<notin> \<int>" by (metis frac_eq_0_iff)
            with 9 show ?thesis by auto
          qed
        qed
      next
        case Greater with * C show ?thesis by force
      qed
    next
      case Greater with * C show ?thesis by force
    qed
  qed (auto intro: A simp: V_def dest: *)
  moreover have "?U \<subseteq> \<R>" by fastforce
  ultimately show ?thesis by blast
qed

lemma \<beta>_boundedness_lt:
  fixes m :: int
  assumes "m \<le> k x" "x \<in> X"
  shows "\<exists> U \<subseteq> \<R>. \<Union> U = {u \<in> V. u x < m}"
proof -
  note A = assms
  let ?U = "{R \<in> \<R>. \<exists> I J r c. R = region X I J r \<and> valid_region X k I J r \<and>
    (I x = Const c \<and> c < m \<or> I x = Intv c \<and> c < m)}"
  { fix u I J r assume "u \<in> region X I J r"
    with A have "intv_elem x u (I x)" by force+
  } note ** = this
  have "\<Union> ?U = {u \<in> V. u x < m}"
  proof (safe, goal_cases)
    case (2 u) with **[OF this(1)] show ?case by auto
  next
    case (4 u) with **[OF this(1)] show ?case by auto
  next
    case (5 u)
    from region_cover_V[OF this(1)] obtain R where R: "R \<in> \<R>" "u \<in> R" by auto
    then obtain I J r where R': "R = region X I J r" "valid_region X k I J r" unfolding \<R>_def by auto
    with R' R(2) A have C:
      "intv_elem x u (I x)" "valid_intv (k x) (I x)"
    by auto
    show ?case
    proof (cases "I x")
      case (Const c)
      with 5 C(1) have "c < m" by auto
      with R R' Const show ?thesis by blast
    next
      case (Intv c)
      with 5 C(1) have "c < m" by auto
      with R R' Intv show ?thesis by blast
    next
      case (Greater c) with 5 C A Greater show ?thesis by auto
    qed
  qed (auto intro: A simp: V_def)
  moreover have "?U \<subseteq> \<R>" by fastforce
  ultimately show ?thesis by blast
qed

lemma \<beta>_boundedness_gt:
  fixes m :: int
  assumes "m \<le> k x" "x \<in> X"
  shows "\<exists> U \<subseteq> \<R>. \<Union> U = {u \<in> V. u x > m}"
proof -
  note A = assms
  let ?U = "{R \<in> \<R>. \<exists> I J r c. R = region X I J r \<and> valid_region X k I J r \<and>
    (I x = Const c \<and> c > m \<or> I x = Intv c \<and> c \<ge> m \<or> I x = Greater (k x))}"
  { fix u I J r assume "u \<in> region X I J r"
    with A have "intv_elem x u (I x)" by force+
  } note ** = this
  have "\<Union> ?U = {u \<in> V. u x > m}"
  proof (safe, goal_cases)
    case (2 u) with **[OF this(1)] show ?case by auto
  next
    case (4 u) with **[OF this(1)] show ?case by auto
  next
    case (6 u) with A **[OF this(1)] show ?case by auto
  next
    case (7 u)
    from region_cover_V[OF this(1)] obtain R where R: "R \<in> \<R>" "u \<in> R" by auto
    then obtain I J r where R': "R = region X I J r" "valid_region X k I J r" unfolding \<R>_def by auto
    with R' R(2) A have C:
      "intv_elem x u (I x)" "valid_intv (k x) (I x)"
    by auto
    show ?case
    proof (cases "I x")
      case (Const c)
      with 7 C(1) have "c > m" by auto
      with R R' Const show ?thesis by blast
    next
      case (Intv c)
      with 7 C(1) have "c \<ge> m" by auto
      with R R' Intv show ?thesis by blast
    next
      case (Greater c)
      with C have "k x = c" by auto
      with R R' Greater show ?thesis by blast
    qed
  qed (auto intro: A simp: V_def)
  moreover have "?U \<subseteq> \<R>" by fastforce
  ultimately show ?thesis by blast
qed

lemma \<beta>_boundedness_eq:
  fixes m :: int
  assumes "m \<le> k x" "x \<in> X"
  shows "\<exists> U \<subseteq> \<R>. \<Union> U = {u \<in> V. u x = m}"
proof -
  note A = assms
  let ?U = "{R \<in> \<R>. \<exists> I J r c. R = region X I J r \<and> valid_region X k I J r \<and> I x = Const c \<and> c = m}"
  have "\<Union> ?U = {u \<in> V. u x = m}"
  proof (safe, goal_cases)
    case (2 u) with A show ?case by force
  next
    case (3 u)
    from region_cover_V[OF this(1)] obtain R where R: "R \<in> \<R>" "u \<in> R" by auto
    then obtain I J r where R': "R = region X I J r" "valid_region X k I J r" unfolding \<R>_def by auto
    with R' R(2) A have C: "intv_elem x u (I x)" "valid_intv (k x) (I x)" by auto
    show ?case
    proof (cases "I x")
      case (Const c)
      with 3 C(1) have "c = m" by auto
      with R R' Const show ?thesis by blast
    next
      case (Intv c)
      with C have "c < u x" "u x < c + 1" by auto
      from nat_intv_not_int[OF this] 3 show ?thesis by auto
    next
      case (Greater c)
      with C 3 A show ?thesis by auto
    qed
  qed (force intro: A simp: V_def)
  moreover have "?U \<subseteq> \<R>" by fastforce
  ultimately show ?thesis by blast
qed

lemma \<beta>_boundedness_diag_le:
  fixes m :: int
  assumes "- k y \<le> m" "m \<le> k x" "x \<in> X" "y \<in> X"
  shows "\<exists> U \<subseteq> \<R>. \<Union> U = {u \<in> V. u x - u y \<le> m}"
proof -
  from \<beta>_boundedness_diag_eq[OF assms] \<beta>_boundedness_diag_lt[OF assms] obtain U1 U2 where A:
    "U1 \<subseteq> \<R>" "\<Union> U1 = {u \<in> V. u x - u y < m}" "U2 \<subseteq> \<R>" "\<Union> U2 = {u \<in> V. u x - u y = m}"
  by blast
  then have "{u \<in> V. u x - u y \<le> m} = \<Union> (U1 \<union> U2)" "U1 \<union> U2 \<subseteq> \<R>" by auto
  then show ?thesis by blast
qed

lemma \<beta>_boundedness_le:
  fixes m :: int
  assumes "m \<le> k x" "x \<in> X"
  shows "\<exists> U \<subseteq> \<R>. \<Union> U = {u \<in> V. u x \<le> m}"
proof -
  from \<beta>_boundedness_lt[OF assms] \<beta>_boundedness_eq[OF assms] obtain U1 U2 where A:
    "U1 \<subseteq> \<R>" "\<Union> U1 = {u \<in> V. u x  < m}" "U2 \<subseteq> \<R>" "\<Union> U2 = {u \<in> V. u x = m}"
  by blast
  then have "{u \<in> V. u x \<le> m} = \<Union> (U1 \<union> U2)" "U1 \<union> U2 \<subseteq> \<R>" by auto
  then show ?thesis by blast
qed

lemma \<beta>_boundedness_ge:
  fixes m :: int
  assumes "m \<le> k x" "x \<in> X"
  shows "\<exists> U \<subseteq> \<R>. \<Union> U = {u \<in> V. u x \<ge> m}"
proof -
  from \<beta>_boundedness_gt[OF assms] \<beta>_boundedness_eq[OF assms] obtain U1 U2 where A:
    "U1 \<subseteq> \<R>" "\<Union> U1 = {u \<in> V. u x  > m}" "U2 \<subseteq> \<R>" "\<Union> U2 = {u \<in> V. u x = m}"
  by blast
  then have "{u \<in> V. u x \<ge> m} = \<Union> (U1 \<union> U2)" "U1 \<union> U2 \<subseteq> \<R>" by auto
  then show ?thesis by blast
qed

lemma \<beta>_boundedness_diag_lt':
  fixes m :: int
  shows
  "- k y \<le> (m :: int) \<Longrightarrow> m \<le> k x \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> Z \<subseteq> {u \<in> V. u x - u y < m}
  \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> {u \<in> V. u x - u y < m}"
proof (goal_cases)
  case 1
  note A = this
  from \<beta>_boundedness_diag_lt[OF A(1-4)] obtain U where U:
    "U \<subseteq> \<R>" "{u \<in> V. u x - u y < m} = \<Union>U"
  by auto
  from 1 clock_numbering have *: "v x > 0" "v y > 0" "v x \<le> n" "v y \<le> n" by auto
  have **: "\<And> c. v c = 0 \<Longrightarrow> False"
  proof -
    fix c assume "v c = 0"
    moreover from clock_numbering(1) have "v c > 0" by auto
    ultimately show False by auto
  qed
  let ?M = "\<lambda> i j. if (i = v x \<and> j = v y) then Lt m else if i = j \<or> i = 0 then Le 0 else \<infinity>"
  have "{u \<in> V. u x - u y < m} = [?M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def DBM_val_bounded_def
  using * ** proof (auto, goal_cases)
    case (1 u c)
    with clock_numbering have "c \<in> X" by metis
    with 1 show ?case unfolding V_def by auto
  next
    case (2 u c1 c2)
    with clock_numbering(1) have "x = c1" "y = c2" by auto
    with 2(5) show ?case by auto
  next
    case (3 u c1 c2)
    with clock_numbering(1) have "c1 = c2" by auto
    then show ?case by auto
  next
    case (4 u c1 c2)
    with clock_numbering(1) have "c1 = c2" by auto
    then show ?case by auto
  next
    case (5 u c1 c2)
    with clock_numbering(1) have "x = c1" "y = c2" by auto
    with 5(6) show ?case by auto
  next
    case (6 u)
    show ?case unfolding V_def
    proof safe
      fix c assume "c \<in> X"
      with clock_numbering have "v c > 0" "v c \<le> n" by auto
      with 6(6) show "u c \<ge> 0" by auto
    qed
  next
    case (7 u)
    then have "dbm_entry_val u (Some x) (Some y) (Lt (real_of_int m))" by metis
    then show ?case by auto
  qed
  then have "vabstr {u \<in> V. u x - u y < m} ?M" by auto
  moreover have "normalized ?M" unfolding normalized less_eq dbm_le_def using A v_v' by auto
  ultimately show ?thesis using apx_min[OF U(2,1)] A(5) by blast
qed

lemma \<beta>_boundedness_diag_le':
  fixes m :: int
  shows
  "- k y \<le> (m :: int) \<Longrightarrow> m \<le> k x \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> Z \<subseteq> {u \<in> V. u x - u y \<le> m}
  \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> {u \<in> V. u x - u y \<le> m}"
proof (goal_cases)
  case 1
  note A = this
  from \<beta>_boundedness_diag_le[OF A(1-4)] obtain U where U:
    "U \<subseteq> \<R>" "{u \<in> V. u x - u y \<le> m} = \<Union>U"
  by auto
  from 1 clock_numbering have *: "v x > 0" "v y > 0" "v x \<le> n" "v y \<le> n" by auto
  have **: "\<And> c. v c = 0 \<Longrightarrow> False"
  proof -
    fix c assume "v c = 0"
    moreover from clock_numbering(1) have "v c > 0" by auto
    ultimately show False by auto
  qed
  let ?M = "\<lambda> i j. if (i = v x \<and> j = v y) then Le m else if i = j \<or> i = 0 then Le 0 else \<infinity>"
  have "{u \<in> V. u x - u y \<le> m} = [?M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def DBM_val_bounded_def
  using * **
  proof (auto, goal_cases)
    case (1 u c)
    with clock_numbering have "c \<in> X" by metis
    with 1 show ?case unfolding V_def by auto
  next
    case (2 u c1 c2)
    with clock_numbering(1) have "x = c1" "y = c2" by auto
    with 2(5) show ?case by auto
  next
    case (3 u c1 c2)
    with clock_numbering(1) have "c1 = c2" by auto
    then show ?case by auto
  next
    case (4 u c1 c2)
    with clock_numbering(1) have "c1 = c2" by auto
    then show ?case by auto
  next
    case (5 u c1 c2)
    with clock_numbering(1) have "x = c1" "y = c2" by auto
    with 5(6) show ?case by auto
  next
    case (6 u)
    show ?case unfolding V_def
    proof safe
      fix c assume "c \<in> X"
      with clock_numbering have "v c > 0" "v c \<le> n" by auto
      with 6(6) show "u c \<ge> 0" by auto
    qed
  next
    case (7 u)
    then have "dbm_entry_val u (Some x) (Some y) (Le (real_of_int m))" by metis
    then show ?case by auto
  qed
  then have "vabstr {u \<in> V. u x - u y \<le> m} ?M" by auto
  moreover have "normalized ?M" unfolding normalized less_eq dbm_le_def using A v_v' by auto
  ultimately show ?thesis using apx_min[OF U(2,1)] A(5) by blast
qed

lemma \<beta>_boundedness_lt':
  fixes m :: int
  shows
  "m \<le> k x \<Longrightarrow> x \<in> X \<Longrightarrow> Z \<subseteq> {u \<in> V. u x < m} \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> {u \<in> V. u x < m}"
proof (goal_cases)
  case 1
  note A = this
  from \<beta>_boundedness_lt[OF A(1,2)] obtain U where U: "U \<subseteq> \<R>" "{u \<in> V. u x < m} = \<Union>U" by auto
  from 1 clock_numbering have *: "v x > 0" "v x \<le> n" by auto
  have **: "\<And> c. v c = 0 \<Longrightarrow> False"
  proof -
    fix c assume "v c = 0"
    moreover from clock_numbering(1) have "v c > 0" by auto
    ultimately show False by auto
  qed
  let ?M = "\<lambda> i j. if (i = v x \<and> j = 0) then Lt m else if i = j \<or> i = 0 then Le 0 else \<infinity>"
  have "{u \<in> V. u x < m} = [?M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def DBM_val_bounded_def
  using * **
  proof (auto, goal_cases)
    case (1 u c)
    with clock_numbering have "c \<in> X" by metis
    with 1 show ?case unfolding V_def by auto
  next
    case (2 u c1)
    with clock_numbering(1) have "x = c1" by auto
    with 2(4) show ?case by auto
  next
    case (3 u c)
    with clock_numbering have "c \<in> X" by metis
    with 3 show ?case unfolding V_def by auto
  next
    case (4 u c1 c2)
    with clock_numbering(1) have "c1 = c2" by auto
    then show ?case by auto
  next
    case (5 u)
    show ?case unfolding V_def
    proof safe
      fix c assume "c \<in> X"
      with clock_numbering have "v c > 0" "v c \<le> n" by auto
      with 5(4) show "u c \<ge> 0" by auto
    qed
  qed
  then have "vabstr {u \<in> V. u x < m} ?M" by auto
  moreover have "normalized ?M" unfolding normalized less_eq dbm_le_def using A v_v' by auto
  ultimately show ?thesis using apx_min[OF U(2,1)] A(3) by blast
qed

lemma \<beta>_boundedness_gt':
  fixes m :: int
  shows
  "m \<le> k x \<Longrightarrow> x \<in> X \<Longrightarrow> Z \<subseteq> {u \<in> V. u x > m} \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> {u \<in> V. u x > m}"
proof goal_cases
  case 1
  from \<beta>_boundedness_gt[OF this(1,2)] obtain U where U: "U \<subseteq> \<R>" "{u \<in> V. u x > m} = \<Union>U" by auto
  from 1 clock_numbering have *: "v x > 0" "v x \<le> n" by auto
  have **: "\<And> c. v c = 0 \<Longrightarrow> False"
  proof -
    fix c assume "v c = 0"
    moreover from clock_numbering(1) have "v c > 0" by auto
    ultimately show False by auto
  qed
  obtain M where "vabstr {u \<in> V. u x > m} M" "normalized M"
  proof (cases "m \<ge> 0")
    case True
    let ?M = "\<lambda> i j. if (i = 0 \<and> j = v x) then Lt (-m) else if i = j \<or> i = 0 then Le 0 else \<infinity>"
    have "{u \<in> V. u x > m} = [?M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def DBM_val_bounded_def
    using * **
    proof (auto, goal_cases)
      case (1 u c)
      with clock_numbering(1) have "x = c" by auto
      with 1(5) show ?case by auto
    next
      case (2 u c)
      with clock_numbering have "c \<in> X" by metis
      with 2 show ?case unfolding V_def by auto
    next
      case (3 u c1 c2)
      with clock_numbering(1) have "c1 = c2" by auto
      then show ?case by auto
    next
      case (4 u c1 c2)
      with clock_numbering(1) have "c1 = c2" by auto
      then show ?case by auto
    next
      case (5 u)
      show ?case unfolding V_def
      proof safe
        fix c assume "c \<in> X"
        with clock_numbering have c: "v c > 0" "v c \<le> n" by auto
        show "u c \<ge> 0"
        proof (cases "v c = v x")
          case False
          with 5(4) c show ?thesis by auto
        next
          case True
          with 5(4) c have "- u c < - m" by auto
          with \<open>m \<ge> 0\<close> show ?thesis by auto
        qed
      qed
    qed
    moreover have "normalized ?M" unfolding normalized using 1 v_v' by auto
    ultimately show ?thesis by (intro that[of ?M]) auto
  next
    case False
    then have "{u \<in> V. u x > m} = V" unfolding V_def using \<open>x \<in> X\<close> by auto
    with \<R>_union all_dbm that show ?thesis by auto
  qed
  with apx_min[OF U(2,1)] 1(3) show ?thesis by blast
qed

lemma obtains_dbm_le:
  fixes m :: int
  assumes "x \<in> X" "m \<le> k x"
  obtains M where "vabstr {u \<in> V. u x \<le> m} M" "normalized M"
proof -
  from assms clock_numbering have *: "v x > 0" "v x \<le> n" by auto
  have **: "\<And> c. v c = 0 \<Longrightarrow> False"
  proof -
    fix c assume "v c = 0"
    moreover from clock_numbering(1) have "v c > 0" by auto
    ultimately show False by auto
  qed
  let ?M = "\<lambda> i j. if (i = v x \<and> j = 0) then Le m else if i = j \<or> i = 0 then Le 0 else \<infinity>"
  have "{u \<in> V. u x \<le> m} = [?M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def DBM_val_bounded_def
  using * **
  proof (auto, goal_cases)
    case (1 u c)
    with clock_numbering have "c \<in> X" by metis
    with 1 show ?case unfolding V_def by auto
  next
    case (2 u c1)
    with clock_numbering(1) have "x = c1" by auto
    with 2(4) show ?case by auto
  next
    case (3 u c)
    with clock_numbering have "c \<in> X" by metis
    with 3 show ?case unfolding V_def by auto
  next
    case (4 u c1 c2)
    with clock_numbering(1) have "c1 = c2" by auto
    then show ?case by auto
  next
    case (5 u)
    show ?case unfolding V_def
    proof safe
      fix c assume "c \<in> X"
      with clock_numbering have "v c > 0" "v c \<le> n" by auto
      with 5(4) show "u c \<ge> 0" by auto
    qed
  qed
  then have "vabstr {u \<in> V. u x \<le> m} ?M" by auto
  moreover have "normalized ?M" unfolding normalized using assms v_v' by auto
  ultimately show ?thesis ..
qed


lemma \<beta>_boundedness_le':
  fixes m :: int
  shows
  "m \<le> k x \<Longrightarrow> x \<in> X \<Longrightarrow> Z \<subseteq> {u \<in> V. u x \<le> m} \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> {u \<in> V. u x \<le> m}"
proof (goal_cases)
  case 1
  from \<beta>_boundedness_le[OF this(1,2)] obtain U where U: "U \<subseteq> \<R>" "{u \<in> V. u x \<le> m} = \<Union>U" by auto
  from obtains_dbm_le 1 obtain M where "vabstr {u \<in> V. u x \<le> m} M" "normalized M" by auto
  with apx_min[OF U(2,1)] 1(3) show ?thesis by blast
qed

lemma obtains_dbm_ge:
  fixes m :: int
  assumes "x \<in> X" "m \<le> k x"
  obtains M where "vabstr {u \<in> V. u x \<ge> m} M" "normalized M"
proof -
  from assms clock_numbering have *: "v x > 0" "v x \<le> n" by auto
  have **: "\<And> c. v c = 0 \<Longrightarrow> False"
  proof -
    fix c assume "v c = 0"
    moreover from clock_numbering(1) have "v c > 0" by auto
    ultimately show False by auto
  qed
  obtain M where "vabstr {u \<in> V. u x \<ge> m} M" "normalized M"
  proof (cases "m \<ge> 0")
    case True
    let ?M = "\<lambda> i j. if (i = 0 \<and> j = v x) then Le (-m) else if i = j \<or> i = 0 then Le 0 else \<infinity>"
    have "{u \<in> V. u x \<ge> m} = [?M]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def DBM_val_bounded_def
    using * **
    proof (auto, goal_cases)
      case (1 u c)
      with clock_numbering(1) have "x = c" by auto
      with 1(5) show ?case by auto
    next
      case (2 u c)
      with clock_numbering have "c \<in> X" by metis
      with 2 show ?case unfolding V_def by auto
    next
      case (3 u c1 c2)
      with clock_numbering(1) have "c1 = c2" by auto
      then show ?case by auto
    next
      case (4 u c1 c2)
      with clock_numbering(1) have "c1 = c2" by auto
      then show ?case by auto
    next
      case (5 u)
      show ?case unfolding V_def
      proof safe
        fix c assume "c \<in> X"
        with clock_numbering have c: "v c > 0" "v c \<le> n" by auto
        show "u c \<ge> 0"
        proof (cases "v c = v x")
          case False
          with 5(4) c show ?thesis by auto
        next
          case True
          with 5(4) c have "- u c \<le> - m" by auto
          with \<open>m \<ge> 0\<close> show ?thesis by auto
        qed
      qed
    qed
    moreover have "normalized ?M" unfolding normalized using assms v_v' by auto
    ultimately show ?thesis by (intro that[of ?M]) auto
  next
    case False
    then have "{u \<in> V. u x \<ge> m} = V" unfolding V_def using \<open>x \<in> X\<close> by auto
    with \<R>_union all_dbm that show ?thesis by auto
  qed
  then show ?thesis ..
qed

lemma \<beta>_boundedness_ge':
  fixes m :: int
  shows "m \<le> k x \<Longrightarrow> x \<in> X \<Longrightarrow> Z \<subseteq> {u \<in> V. u x \<ge> m} \<Longrightarrow> Approx\<^sub>\<beta> Z \<subseteq> {u \<in> V. u x \<ge> m}"
proof (goal_cases)
  case 1
  from \<beta>_boundedness_ge[OF this(1,2)] obtain U where U: "U \<subseteq> \<R>" "{u \<in> V. u x \<ge> m} = \<Union>U" by auto
  from obtains_dbm_ge 1 obtain M where "vabstr {u \<in> V. u x \<ge> m} M" "normalized M" by auto
  with apx_min[OF U(2,1)] 1(3) show ?thesis by blast
qed

end

end
