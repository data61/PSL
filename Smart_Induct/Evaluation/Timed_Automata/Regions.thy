chapter \<open>The Classic Construction for Decidability\<close>

theory Regions
imports Timed_Automata Misc
begin

text \<open>
  The following is a formalization of regions in the correct version of Patricia Bouyer et al.
\<close>

section \<open>Definition of Regions\<close>

type_synonym 'c ceiling = "('c \<Rightarrow> nat)"

datatype intv =
  Const nat |
  Intv nat |
  Greater nat

type_synonym t = real

instantiation real :: time
begin
  instance proof
    fix x y :: real assume "x < y"
    then show "\<exists> z > x. z < y" using Rats_cases using dense_order_class.dense by blast
  next
    have "(1:: real) \<noteq> 0" by auto
    then show "\<exists>x. (x::real) \<noteq> 0" by blast
  qed
end

inductive valid_intv :: "nat \<Rightarrow> intv \<Rightarrow> bool"
where
  "0 \<le> d \<Longrightarrow> d \<le> c \<Longrightarrow> valid_intv c (Const d)" |
  "0 \<le> d \<Longrightarrow> d < c  \<Longrightarrow> valid_intv c (Intv d)" |
  "valid_intv c (Greater c)"

inductive intv_elem :: "'c \<Rightarrow> ('c,t) cval \<Rightarrow> intv \<Rightarrow> bool"
where
  "u x = d \<Longrightarrow> intv_elem x u (Const d)" |
  "d < u x \<Longrightarrow> u x < d + 1 \<Longrightarrow> intv_elem x u (Intv d)" |
  "c < u x \<Longrightarrow> intv_elem x u (Greater c)"

abbreviation "total_preorder r \<equiv> refl r \<and> trans r"

inductive valid_region :: "'c set \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> ('c \<Rightarrow> intv) \<Rightarrow> 'c rel \<Rightarrow> bool"
where
  "\<lbrakk>X\<^sub>0 = {x \<in> X. \<exists> d. I x = Intv d}; refl_on X\<^sub>0 r; trans r; total_on X\<^sub>0 r; \<forall> x \<in> X. valid_intv (k x) (I x)\<rbrakk>
  \<Longrightarrow> valid_region X k I r"

inductive_set region for X I r
where
  "\<forall> x \<in> X. u x \<ge> 0 \<Longrightarrow> \<forall> x \<in> X. intv_elem x u (I x) \<Longrightarrow> X\<^sub>0 = {x \<in> X. \<exists> d. I x = Intv d} \<Longrightarrow>
   \<forall> x \<in> X\<^sub>0. \<forall> y \<in> X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)
  \<Longrightarrow> u \<in> region X I r"

text \<open>Defining the unique element of a partition that contains a valuation\<close>

definition part ("[_]\<^sub>_" [61,61] 61) where "part v \<R> \<equiv> THE R. R \<in> \<R> \<and> v \<in> R"

inductive_set Succ for \<R> R where
  "u \<in> R \<Longrightarrow> R \<in> \<R> \<Longrightarrow> R' \<in> \<R> \<Longrightarrow> t \<ge> 0 \<Longrightarrow> R' = [u \<oplus> t]\<^sub>\<R> \<Longrightarrow> R' \<in> Succ \<R> R"

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

declare valid_intv.intros[intro]
declare intv_elem.intros[intro]
declare Succ.intros[intro]

declare Succ.cases[elim]

declare region.cases[elim]
declare valid_region.cases[elim]

section \<open>Basic Properties\<close>

text \<open>First we show that all valid intervals are distinct.\<close>

lemma valid_intv_distinct:
  "valid_intv c I \<Longrightarrow> valid_intv c I' \<Longrightarrow> intv_elem x u I \<Longrightarrow> intv_elem x u I' \<Longrightarrow> I = I'"
by (cases I; cases I'; auto)

text \<open>From this we show that all valid regions are distinct.\<close>

lemma valid_regions_distinct:
  "valid_region X k I r \<Longrightarrow> valid_region X k I' r' \<Longrightarrow> v \<in> region X I r \<Longrightarrow> v \<in> region X I' r'
  \<Longrightarrow> region X I r = region X I' r'"
proof goal_cases
  case A: 1
  { fix x assume x: "x \<in> X"
    with A(1) have "valid_intv (k x) (I x)" by auto
    moreover from A(2) x have "valid_intv (k x) (I' x)" by auto
    moreover from A(3) x have "intv_elem x v (I x)" by auto
    moreover from A(4) x have "intv_elem x v (I' x)" by auto
    ultimately have "I x = I' x" using valid_intv_distinct by fastforce
  } note * = this
  from A show ?thesis
  proof (safe, goal_cases)
    case A: (1 u)
    have "intv_elem x u (I' x)" if "x \<in> X" for x using A(5) * that by auto
    then have B: "\<forall> x \<in> X. intv_elem x u (I' x)" by auto
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
    from region.intros[OF this B _ *] show ?case by auto
  next
    case A: (2 u)
    have "intv_elem x u (I x)" if "x \<in> X" for x using * A(5) that by auto
    then have B: "\<forall> x \<in> X. intv_elem x u (I x)" by auto
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
    from region.intros[OF this B _ *] show ?case by auto
  qed
qed

lemma \<R>_regions_distinct:
  "\<lbrakk>\<R> = {region X I r | I r. valid_region X k I r}; R \<in> \<R>; v \<in> R; R' \<in> \<R>; R \<noteq> R'\<rbrakk> \<Longrightarrow> v \<notin> R'"
using valid_regions_distinct by blast

text \<open>
  Secondly, we also need to show that every valuations belongs to a region which is part of
  the partition.
\<close>

definition intv_of :: "nat \<Rightarrow> t \<Rightarrow> intv" where
  "intv_of k c \<equiv>
    if (c > k) then Greater k
    else if (\<exists> x :: nat. x = c) then (Const (nat (floor c)))
    else (Intv (nat (floor c)))"

lemma region_cover:
  "\<forall> x \<in> X. u x \<ge> 0 \<Longrightarrow> \<exists> R. R \<in> {region X I r | I r. valid_region X k I r} \<and> u \<in> R"
proof (standard, standard)
  assume assm: "\<forall> x \<in> X. 0 \<le> u x"
  let ?I = "\<lambda> x. intv_of (k x) (u x)"
  let ?X\<^sub>0 = "{x \<in> X. \<exists> d. ?I x = Intv d}"
  let ?r = "{(x,y). x \<in> ?X\<^sub>0 \<and> y \<in> ?X\<^sub>0 \<and> frac (u x) \<le> frac (u y)}"
  show "u \<in> region X ?I ?r"
  proof (standard, auto simp: assm, goal_cases)
    case (1 x)
    thus ?case unfolding intv_of_def
    proof (auto, goal_cases)
      case A: (1 a)
      from A(2) have "\<lfloor>u x\<rfloor> = u x" by (metis of_int_floor_cancel of_int_of_nat_eq) 
      with assm A(1) have "u x = real (nat \<lfloor>u x\<rfloor>)" by auto
      then show ?case by auto
    next
      case A: 2
      from A(1,2) have "real (nat \<lfloor>u x\<rfloor>) < u x"
      by (metis assm floor_less_iff int_nat_eq less_eq_real_def less_irrefl not_less
                of_int_of_nat_eq of_nat_0)
      moreover from assm have "u x < real (nat (\<lfloor>u x\<rfloor>) + 1)" by linarith
      ultimately show ?case by auto
    qed
  qed
  have "valid_intv (k x) (intv_of (k x) (u x))" if "x \<in> X" for x using that
  proof (auto simp: intv_of_def, goal_cases)
    case 1 then show ?case by (intro valid_intv.intros(1)) (auto, linarith)
  next
    case 2
    then show ?case using assm floor_less_iff nat_less_iff
    by (intro valid_intv.intros(2)) fastforce+
  qed
  then have "valid_region X k ?I ?r"
  by (intro valid_region.intros) (auto simp: refl_on_def trans_def total_on_def)
  then show "region X ?I ?r \<in> {region X I r | I r. valid_region X k I r}" by auto
qed

lemma intv_not_empty:
  obtains d where "intv_elem x (v(x := d)) (I x)"
proof (cases "I x", goal_cases)
  case (1 d)
  then have "intv_elem x (v(x := d)) (I x)" by auto
  with 1 show ?case by auto
next
  case (2 d)
  then have "intv_elem x (v(x := d + 0.5)) (I x)" by auto
  with 2 show ?case by auto
next
  case (3 d)
  then have "intv_elem x (v(x := d + 0.5)) (I x)" by auto
  with 3 show ?case by auto
qed

fun get_intv_val :: "intv \<Rightarrow> real \<Rightarrow> real"
where
  "get_intv_val (Const d)   _ = d" |
  "get_intv_val (Intv d)    f = d + f"  |
  "get_intv_val (Greater d) _ = d + 1"

lemma region_not_empty_aux:
  assumes "0 < f" "f < 1" "0 < g" "g < 1"
  shows "frac (get_intv_val (Intv d) f) \<le> frac (get_intv_val (Intv d') g) \<longleftrightarrow> f \<le> g"
using assms by (simp, metis frac_eq frac_nat_add_id less_eq_real_def) 

lemma region_not_empty:
  assumes "finite X" "valid_region X k I r"
  shows "\<exists> u. u \<in> region X I r"
proof -
  let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
  obtain f :: "'a \<Rightarrow> nat" where f:
    "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. f x \<le> f y \<longleftrightarrow> (x, y) \<in> r"
     apply (rule finite_total_preorder_enumeration)
         apply (subgoal_tac "finite ?X\<^sub>0")
          apply assumption
  using assms by auto
  let ?M = "if ?X\<^sub>0 \<noteq> {} then Max {f x | x. x \<in> ?X\<^sub>0} else 1"
  let ?f = "\<lambda> x. (f x + 1) / (?M + 2)"
  let ?v = "\<lambda> x. get_intv_val (I x) (if x \<in> ?X\<^sub>0 then ?f x else 1)"
  have frac_intv: "\<forall>x\<in>?X\<^sub>0. 0 < ?f x \<and> ?f x < 1"
  proof (standard, goal_cases)
    case (1 x)
    then have *: "?X\<^sub>0 \<noteq> {}" by auto
    have "f x \<le> Max {f x | x. x \<in> ?X\<^sub>0}" apply (rule Max_ge) using \<open>finite X\<close> 1 by auto
    with 1 show ?case by auto
  qed
  with region_not_empty_aux have *:
    "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. frac (?v x) \<le> frac (?v y) \<longleftrightarrow> ?f x \<le> ?f y"
  by force
  have "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. ?f x \<le> ?f y \<longleftrightarrow> f x \<le> f y" by (simp add: divide_le_cancel)+
  with f have "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. ?f x \<le> ?f y \<longleftrightarrow> (x, y) \<in> r" by auto
  with * have frac_order: "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. frac (?v x) \<le> frac (?v y) \<longleftrightarrow> (x, y) \<in> r" by auto
  have "?v \<in> region X I r"
  proof standard
    show "\<forall>x\<in>X. intv_elem x ?v (I x)"
    proof (standard, case_tac "I x", goal_cases)
      case (2 x d)
      then have *: "x \<in> ?X\<^sub>0" by auto
      with frac_intv have "0 < ?f x" "?f x < 1" by auto
      moreover from 2 have "?v x = d + ?f x" by auto
      ultimately have "?v x < d + 1 \<and> d < ?v x" by linarith
      then show "intv_elem x ?v (I x)" by (subst 2(2)) (intro intv_elem.intros(2), auto)
    qed auto
  next
    show "\<forall>x\<in>X. 0 \<le> get_intv_val (I x) (if x \<in> ?X\<^sub>0 then ?f x else 1)"
    by (standard, case_tac "I x") auto
  next
    show "{x \<in> X. \<exists>d. I x = Intv d} = {x \<in> X. \<exists>d. I x = Intv d}" ..
  next  
    from frac_order show "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. ((x, y) \<in> r) = (frac (?v x) \<le> frac (?v y))" by blast
  qed
  then show ?thesis by auto
qed

text \<open>
  Now we can show that there is always exactly one region a valid valuation belongs to.
\<close>

lemma regions_partition:
  "\<R> = {region X I r | I r. valid_region X k I r} \<Longrightarrow> \<forall>x \<in> X. 0 \<le> u x \<Longrightarrow> \<exists>! R \<in> \<R>. u \<in> R"
proof (goal_cases)
  case 1
  note A = this
  with region_cover[OF A(2)] obtain R where R: "R \<in> \<R> \<and> u \<in> R" by fastforce
  moreover have "R' = R" if "R' \<in> \<R> \<and> u \<in> R'" for R'
  using that R valid_regions_distinct unfolding A(1) by blast
  ultimately show ?thesis by auto
qed

lemma region_unique:
  "\<R> = {region X I r | I r. valid_region X k I r} \<Longrightarrow> u \<in> R \<Longrightarrow> R \<in> \<R> \<Longrightarrow> [u]\<^sub>\<R> = R"
proof (goal_cases)
  case 1
  note A = this
  from A obtain I r where *: "valid_region X k I r" "R = region X I r" "u \<in> region X I r" by auto
  from this(3) have "\<forall>x\<in>X. 0 \<le> u x" by auto
  from theI'[OF regions_partition[OF A(1) this]] A(1) obtain I' r' where
    v: "valid_region X k I' r'" "[u]\<^sub>\<R> = region X I' r'" "u \<in> region X I' r'"
  unfolding part_def by auto
  from valid_regions_distinct[OF *(1) v(1) *(3) v(3)] v(2) *(2) show ?case by auto
qed

lemma regions_partition':
  "\<R> = {region X I r | I r. valid_region X k I r} \<Longrightarrow> \<forall>x\<in>X. 0 \<le> v x \<Longrightarrow> \<forall>x\<in>X. 0 \<le> v' x \<Longrightarrow> v' \<in> [v]\<^sub>\<R>
  \<Longrightarrow> [v']\<^sub>\<R> = [v]\<^sub>\<R>"
proof (goal_cases)
  case 1
  note A = this
  from theI'[OF regions_partition[OF A(1,2)]] A(1,4) obtain I r where
    v: "valid_region X k I r" "[v]\<^sub>\<R> = region X I r" "v' \<in> region X I r"
  unfolding part_def by auto
  from theI'[OF regions_partition[OF A(1,3)]] A(1) obtain I' r' where
    v': "valid_region X k I' r'" "[v']\<^sub>\<R> = region X I' r'" "v' \<in> region X I' r'"
  unfolding part_def by auto
  from valid_regions_distinct[OF v'(1) v(1) v'(3) v(3)] v(2) v'(2) show ?case by simp
qed

lemma regions_closed:
  "\<R> = {region X I r | I r. valid_region X k I r} \<Longrightarrow> R \<in> \<R> \<Longrightarrow> v \<in> R \<Longrightarrow> t \<ge> 0 \<Longrightarrow> [v \<oplus> t]\<^sub>\<R> \<in> \<R>"
proof goal_cases
  case A: 1
  then obtain I r where "v \<in> region X I r" by auto
  from this(1) have "\<forall> x \<in> X. v x \<ge> 0" by auto
  with A(4) have "\<forall> x \<in> X. (v \<oplus> t) x \<ge> 0" unfolding cval_add_def by simp
  from regions_partition[OF A(1) this] obtain R' where "R' \<in> \<R>" "(v \<oplus> t) \<in> R'" by auto
  with region_unique[OF A(1) this(2,1)] show ?case by auto
qed

lemma regions_closed':
  "\<R> = {region X I r | I r. valid_region X k I r} \<Longrightarrow> R \<in> \<R> \<Longrightarrow> v \<in> R \<Longrightarrow> t \<ge> 0 \<Longrightarrow> (v \<oplus> t) \<in> [v \<oplus> t]\<^sub>\<R>"
proof goal_cases
  case A: 1
  then obtain I r where "v \<in> region X I r" by auto
  from this(1) have "\<forall> x \<in> X. v x \<ge> 0" by auto
  with A(4) have "\<forall> x \<in> X. (v \<oplus> t) x \<ge> 0" unfolding cval_add_def by simp
  from regions_partition[OF A(1) this] obtain R' where "R' \<in> \<R>" "(v \<oplus> t) \<in> R'" by auto
  with region_unique[OF A(1) this(2,1)] show ?case by auto
qed

lemma valid_regions_I_cong:
  "valid_region X k I r \<Longrightarrow> \<forall> x \<in> X. I x = I' x \<Longrightarrow> region X I r = region X I' r \<and> valid_region X k I' r"
proof (safe, goal_cases)
  case (1 v)
  note A = this
  then have [simp]:"\<And> x. x \<in> X \<Longrightarrow> I' x = I x" by metis
  show ?case
  proof (standard, goal_cases)
    case 1
    from A(3) show ?case by auto
  next
    case 2
    from A(3) show ?case by auto
  next
    case 3
    show "{x \<in> X. \<exists>d. I x = Intv d} = {x \<in> X. \<exists>d. I' x = Intv d}" by auto
  next
    case 4
    let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
    from A(3) show "\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. ((x, y) \<in> r) = (frac (v x) \<le> frac (v y))" by auto
  qed
next
  case (2 v)
  note A = this
  then have [simp]:"\<And> x. x \<in> X \<Longrightarrow> I' x = I x" by metis
  show ?case
  proof (standard, goal_cases)
    case 1
    from A(3) show ?case by auto
  next
    case 2
    from A(3) show ?case by auto
  next
    case 3
    show "{x \<in> X. \<exists>d. I' x = Intv d} = {x \<in> X. \<exists>d. I x = Intv d}" by auto
  next
    case 4
    let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I' x = Intv d}"
    from A(3) show "\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. ((x, y) \<in> r) = (frac (v x) \<le> frac (v y))" by auto
  qed
next
  case 3
  note A = this
  then have [simp]:"\<And> x. x \<in> X \<Longrightarrow> I' x = I x" by metis
  show ?case
   apply rule
       apply (subgoal_tac "{x \<in> X. \<exists>d. I x = Intv d} = {x \<in> X. \<exists>d. I' x = Intv d}")
        apply assumption
  using A by auto
qed

fun intv_const :: "intv \<Rightarrow> nat"
where
  "intv_const (Const d) = d" |
  "intv_const (Intv d) = d"  |
  "intv_const (Greater d) = d"

lemma finite_\<R>:
  notes [[simproc add: finite_Collect]] finite_subset[intro]
  fixes X k
  defines "\<R> \<equiv> {region X I r | I r. valid_region X k I r}"
  assumes "finite X"
  shows "finite \<R>"
proof -
  { fix I r assume A: "valid_region X k I r"
    let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
    from A have "refl_on ?X\<^sub>0 r" by auto
    then have "r \<subseteq> X \<times> X" by (auto simp: refl_on_def)
    then have "r \<in> Pow (X \<times> X)" by auto
  }
  then have "{r. \<exists>I. valid_region X k I r} \<subseteq> Pow (X \<times> X)" by auto
  with \<open>finite X\<close> have fin: "finite {r. \<exists>I. valid_region X k I r}" by auto
  let ?m = "Max {k x | x. x \<in> X}"
  let ?I = "{intv. intv_const intv \<le> ?m}"
  let ?fin_map = "\<lambda> I. \<forall>x. (x \<in> X \<longrightarrow> I x \<in> ?I) \<and> (x \<notin> X \<longrightarrow> I x = Const 0)"
  let ?\<R> = "{region X I r | I r. valid_region X k I r \<and> ?fin_map I}"
  have "?I = (Const ` {d. d \<le> ?m}) \<union> (Intv ` {d. d \<le> ?m}) \<union> (Greater ` {d. d \<le> ?m})"
  by auto (case_tac x, auto)
  then have "finite ?I" by auto
  from finite_set_of_finite_funs[OF \<open>finite X\<close> this] have "finite {I. ?fin_map I}" .
  with fin have "finite {(I, r). valid_region X k I r \<and> ?fin_map I}"
  by (fastforce intro: pairwise_finiteI finite_ex_and1 frac_add_le_preservation del: finite_subset)
  then have "finite ?\<R>" by fastforce
  moreover have "\<R> \<subseteq> ?\<R>"
  proof
    fix R assume R: "R \<in> \<R>"
    then obtain I r where I: "R = region X I r" "valid_region X k I r" unfolding \<R>_def by auto
    let ?I = "\<lambda> x. if x \<in> X then I x else Const 0"
    let ?R = "region X ?I r"
    from valid_regions_I_cong[OF I(2)] I have "R = ?R" "valid_region X k ?I r" by auto
    moreover have "\<forall>x. x \<notin> X \<longrightarrow> ?I x = Const 0" by auto
    moreover have "\<forall>x. x \<in> X \<longrightarrow> intv_const (I x) \<le> ?m"
    proof auto
      fix x assume x: "x \<in> X"
      with I(2) have "valid_intv (k x) (I x)" by auto
      moreover from \<open>finite X\<close> x have "k x \<le> ?m" by (auto intro: Max_ge)
      ultimately  show "intv_const (I x) \<le> Max {k x |x. x \<in> X}" by (cases "I x") auto
    qed
    ultimately show "R \<in> ?\<R>" by force
  qed
  ultimately show "finite \<R>" by blast
qed

lemma SuccI2:
  "\<R> = {region X I r | I r. valid_region X k I r} \<Longrightarrow> v \<in> R \<Longrightarrow> R \<in> \<R> \<Longrightarrow> t \<ge> 0 \<Longrightarrow> R' = [v \<oplus> t]\<^sub>\<R>
  \<Longrightarrow> R' \<in> Succ \<R> R"
proof goal_cases
  case A: 1
  from Succ.intros[OF A(2) A(3) regions_closed[OF A(1,3,2,4)] A(4)] A(5) show ?case by auto
qed


section \<open>Set of Regions\<close>

text \<open>
  The first property Bouyer shows is that these regions form a 'set of regions'.
\<close>

text \<open>
  For the unbounded region in the upper right corner, the set of successors only
  contains itself.
\<close>

lemma Succ_refl:
  "\<R> = {region X I r |I r. valid_region X k I r} \<Longrightarrow> finite X \<Longrightarrow> R \<in> \<R> \<Longrightarrow> R \<in> Succ \<R> R"
proof goal_cases
  case A: 1
  then obtain I r where R: "valid_region X k I r" "R = region X I r" by auto
  with A region_not_empty obtain v where v: "v \<in> region X I r" by metis
  with R have *: "(v \<oplus> 0) \<in> R" unfolding cval_add_def by auto
  from regions_closed'[OF A(1,3-)] v R have "(v \<oplus> 0) \<in> [v \<oplus> 0]\<^sub>\<R>" by auto
  from region_unique[OF A(1) * A(3)] A(3) v[unfolded R(2)[symmetric]] show ?case by auto
qed

lemma Succ_refl':
  "\<R> = {region X I r |I r. valid_region X k I r} \<Longrightarrow> finite X \<Longrightarrow> \<forall> x \<in> X. \<exists> c. I x = Greater c
  \<Longrightarrow> region X I r \<in> \<R> \<Longrightarrow> Succ \<R> (region X I r) = {region X I r}"
proof goal_cases
  case A: 1
  have *: "(v \<oplus> t) \<in> region X I r" if v: "v \<in> region X I r" and t: "t \<ge> 0" for v and t :: t
  proof ((rule region.intros), auto, goal_cases)
    case 1
    with v t show ?case unfolding cval_add_def by auto
  next
    case (2 x)
    with A obtain c where c: "I x = Greater c" by auto
    with v 2 have "v x > c" by fastforce
    with t have "v x + t > c" by auto
    then have "(v \<oplus> t) x > c" by (simp add: cval_add_def)
    from intv_elem.intros(3)[of c "v \<oplus> t", OF this] c show ?case by auto
  next
    case (3 x)
    from this(1) A obtain c where "I x = Greater c" by auto
    with 3(2) show ?case by auto
  next
    case (4 x)
    from this(1) A obtain c where "I x = Greater c" by auto
    with 4(2) show ?case by auto
  qed
  show ?case
  proof (standard, standard)
    fix R assume R: "R \<in> Succ \<R> (region X I r)"
    then obtain v t where v:
      "v \<in> region X I r" "R = [v \<oplus> t]\<^sub>\<R>" "R \<in> \<R>" "t \<ge> 0"
    by (cases rule: Succ.cases) auto
    from v(1) have **: "\<forall>x \<in> X. 0 \<le> v x" by auto
    with v(4) have "\<forall>x \<in> X. 0 \<le> (v \<oplus> t) x" unfolding cval_add_def by auto
    from *[OF v(1,4)] regions_partition'[OF A(1) ** this] region_unique[OF A(1) v(1) A(4)] v(2)
    show "R \<in> {region X I r}" by auto
  next
    from A(4) obtain I' r' where R': "region X I r = region X I' r'" "valid_region X k I' r'"
    unfolding A(1) by auto
    with region_not_empty[OF A(2) this(2)] obtain v where v: "v \<in> region X I r" by auto
    from region_unique[OF A(1) this A(4)] have *: "[v \<oplus> 0]\<^sub>\<R> = region X I r"
    unfolding cval_add_def by auto
    with v A(4) have "[v \<oplus> 0]\<^sub>\<R> \<in> Succ \<R> (region X I r)" by (intro Succ.intros; auto)
    with * show "{region X I r} \<subseteq> Succ \<R> (region X I r)" by auto
  qed
qed

text \<open>
  Defining the closest successor of a region. Only exists if at least one interval is upper-bounded.
\<close>

definition
  "succ \<R> R =
  (SOME R'. R' \<in> Succ \<R> R \<and> (\<forall> u \<in> R. \<forall> t \<ge> 0. (u \<oplus> t) \<notin> R \<longrightarrow> (\<exists> t' \<le> t. (u \<oplus> t') \<in> R' \<and> 0 \<le> t')))"

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

text \<open>
  What Bouyer states at the end. However, we have to be a bit more precise than in her statement.
\<close>

lemma closest_prestable_1:
  fixes I X k r
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  defines "R \<equiv> region X I r"
  defines "Z \<equiv> {x \<in> X . \<exists> c. I x = Const c}"
  assumes "Z \<noteq> {}"
  defines "I'\<equiv> \<lambda> x. if x \<notin> Z then I x else if intv_const (I x) = k x then Greater (k x) else Intv (intv_const (I x))"
  defines "r' \<equiv> r \<union> {(x,y) . x \<in> Z \<and> y \<in> X \<and> intv_const (I x) < k x \<and> isIntv (I' y)}"
  assumes "finite X"
  assumes "valid_region X k I r"
  shows   "\<forall> v \<in> R. \<forall> t>0. \<exists>t'\<le>t. (v \<oplus> t') \<in> region X I' r' \<and> t' \<ge> 0"
  and     "\<forall> v \<in> region X I' r'. \<forall> t\<ge>0. (v \<oplus> t) \<notin> R"
  and     "\<forall> x \<in> X. \<not> isConst (I' x)"
  and     "\<forall> v \<in> R. \<forall> t < 1. \<forall> t' \<ge> 0. (v \<oplus> t') \<in> region X I' r'
           \<longrightarrow> {x. x \<in> X \<and> (\<exists> c. I x = Intv c \<and> v x + t \<ge> c + 1)}
                = {x. x \<in> X \<and> (\<exists> c. I' x = Intv c \<and> (v \<oplus> t') x + (t - t') \<ge> c + 1)}"
proof (safe, goal_cases)
  fix v assume v: "v \<in> R" fix t :: t assume t: "0 < t"
  have elem: "intv_elem x v (I x)" if x: "x \<in> X" for x using v x unfolding R_def by auto
  have *: "(v \<oplus> t) \<in> region X I' r'" if A: "\<forall> x \<in> X. \<not> isIntv (I x)" and t: "t > 0" "t < 1" for t
  proof (standard, goal_cases)
    case 1
    from v have "\<forall> x \<in> X. v x \<ge> 0" unfolding R_def by auto
    with t show ?case unfolding cval_add_def by auto
  next
    case 2
    show ?case
    proof (standard, case_tac "I x", goal_cases)
      case (1 x c)
      with elem[OF \<open>x \<in> X\<close>] have "v x = c" by auto
      show ?case
      proof (cases "intv_const (I x) = k x", auto simp: 1 I'_def Z_def, goal_cases)
        case 1
        with \<open>v x = c\<close> have "v x = k x" by auto
        with t show ?case by (auto simp: cval_add_def)
      next
        case 2
        from assms(8) 1 have "c \<le> k x" by (cases rule: valid_region.cases) auto
        with 2 have "c < k x" by linarith
        from t \<open>v x = c\<close> show ?case by (auto simp: cval_add_def)
      qed
    next
      case (2 x c)
      with A show ?case by auto
    next
      case (3 x c)
      then have "I' x = Greater c" unfolding I'_def Z_def by auto
      with t 3 elem[OF \<open>x \<in> X\<close>] show ?case by (auto simp: cval_add_def)
    qed
  next
    case 3 show "{x \<in> X. \<exists>d. I' x = Intv d} = {x \<in> X. \<exists>d. I' x = Intv d}" ..
  next
    case 4
    let ?X\<^sub>0' = "{x \<in> X. \<exists>d. I' x = Intv d}"
    show "\<forall>x\<in>?X\<^sub>0'. \<forall>y\<in>?X\<^sub>0'. ((x, y) \<in> r') = (frac ((v \<oplus> t) x) \<le> frac ((v \<oplus> t) y))"
    proof (safe, goal_cases)
      case (1 x y d d')
      note B = this
      have "x \<in> Z" apply (rule ccontr) using A B by (auto simp: I'_def)
      with elem[OF B(1)] have "frac (v x) = 0 " unfolding Z_def by auto
      with frac_distr[of t "v x"] t have *: "frac (v x + t) = t" by auto
      have "y \<in> Z" apply (rule ccontr) using A B by (auto simp: I'_def)
      with elem[OF B(3)] have "frac (v y) = 0 " unfolding Z_def by auto
      with frac_distr[of t "v y"] t have "frac (v y + t) = t" by auto
      with * show ?case unfolding cval_add_def by auto
    next
      case B: (2 x)
      have "x \<in> Z" apply (rule ccontr) using A B by (auto simp: I'_def)
      with B have "intv_const (I x) \<noteq> k x" unfolding I'_def by auto
      with B(1) assms(8) have "intv_const (I x) < k x" by (fastforce elim!: valid_intv.cases)
      with B \<open>x \<in> Z\<close> show ?case unfolding r'_def by auto
    qed
  qed
  let ?S = "{1 - frac (v x) | x. x \<in> X \<and> isIntv (I x)}"
  let ?t = "Min ?S"
  { assume A: "\<exists> x \<in> X. isIntv (I x)"
    from \<open>finite X\<close> have "finite ?S" by auto
    from A have "?S \<noteq> {}" by auto
    from Min_in[OF \<open>finite ?S\<close> this] obtain x where
      x: "x \<in> X" "isIntv (I x)" "?t = 1 - frac (v x)"
    by force
    have "frac (v x) < 1" by (simp add: frac_lt_1)
    then have "?t > 0" by (simp add: x(3))
    then have "?t / 2 > 0" by auto
    from x(2) obtain c where "I x = Intv c" by (auto)
    with elem[OF x(1)] have v_x: "c < v x" "v x < c + 1" by auto
    from nat_intv_frac_gt0[OF this] have "frac (v x) > 0" .
    with x(3) have "?t < 1" by auto
    { fix t :: t assume t: "0 < t" "t \<le> ?t / 2"
      { fix y assume "y \<in> X" "isIntv (I y)"
        then have "1 - frac (v y) \<in> ?S" by auto
        from Min_le[OF \<open>finite ?S\<close> this] \<open>?t > 0\<close> t have "t  < 1 - frac (v y)" by linarith
      } note frac_bound = this
      have "(v \<oplus> t) \<in> region X I' r'"
      proof (standard, goal_cases)
        case 1
        from v have "\<forall> x \<in> X. v x \<ge> 0" unfolding R_def by auto
        with \<open>?t > 0\<close> t show ?case unfolding cval_add_def by auto
      next
        case 2
        show ?case
        proof (standard, case_tac "I x", goal_cases)
          case A: (1 x c)
          with elem[OF \<open>x \<in> X\<close>] have "v x = c" by auto
          show ?case
          proof (cases "intv_const (I x) = k x", auto simp: A I'_def Z_def, goal_cases)
            case 1
            with \<open>v x = c\<close> have "v x = k x" by auto
            with \<open>?t > 0\<close> t show ?case by (auto simp: cval_add_def)
          next
            case 2
            from assms(8) A have "c \<le> k x" by (cases rule: valid_region.cases) auto
            with 2 have "c < k x" by linarith
            from \<open>v x = c\<close> \<open>?t < 1\<close> t show ?case
            by (auto simp: cval_add_def)
          qed
        next
          case (2 x c)
          with elem[OF \<open>x \<in> X\<close>] have v: "c < v x" "v x < c + 1" by auto
          with \<open>?t > 0\<close> have "c < v x + (?t / 2)" by auto
          from 2 have "I' x = I x" unfolding I'_def Z_def by auto
          from frac_bound[OF 2(1)] 2(2) have "t  < 1 - frac (v x)" by auto
          from frac_add_le_preservation[OF v(2) this] t v(1) 2 show ?case
          unfolding cval_add_def \<open>I' x = I x\<close> by auto
        next
          case (3 x c)
          then have "I' x = Greater c" unfolding I'_def Z_def by auto
          with 3 elem[OF \<open>x \<in> X\<close>] t show ?case
          by (auto simp: cval_add_def)
        qed
      next
        case 3 show "{x \<in> X. \<exists>d. I' x = Intv d} = {x \<in> X. \<exists>d. I' x = Intv d}" ..
      next
        case 4
        let ?X\<^sub>0  = "{x \<in> X. \<exists>d. I x = Intv d}"
        let ?X\<^sub>0' = "{x \<in> X. \<exists>d. I' x = Intv d}"
        show "\<forall>x\<in>?X\<^sub>0'. \<forall>y\<in>?X\<^sub>0'. ((x, y) \<in> r') = (frac ((v \<oplus> t) x) \<le> frac ((v \<oplus> t) y))"
        proof (safe, goal_cases)
          case (1 x y d d')
          note B = this
          show ?case
          proof (cases "x \<in> Z")
            case False
            note F = this
            show ?thesis
            proof (cases "y \<in> Z")
              case False
              with F B have *: "x \<in> ?X\<^sub>0" "y \<in> ?X\<^sub>0" unfolding I'_def by auto
              from B(5) show ?thesis unfolding r'_def
              proof (safe, goal_cases)
                case 1
                with v * have le: "frac (v x) <= frac (v y)" unfolding R_def by auto
                from frac_bound * have "t < 1 - frac (v x)" "t < 1 - frac (v y)" by fastforce+
                with frac_distr t have
                  "frac (v x) + t = frac (v x + t)" "frac (v y) + t = frac (v y + t)"
                by simp+
                with le show ?case unfolding cval_add_def by fastforce
              next
                case 2
                from this(1) elem have **: "frac (v x) = 0" unfolding Z_def by force
                from 2(4) obtain c where "I' y = Intv c" by (auto )
                then have "y \<in> Z \<or> I y = Intv c" unfolding I'_def by presburger
                then show ?case
                proof
                  assume "y \<in> Z"
                  with elem[OF 2(2)] have ***: "frac (v y) = 0" unfolding Z_def by force
                  show ?thesis by (simp add: ** *** frac_add cval_add_def)
                next
                  assume A: "I y = Intv c"
                  have le: "frac (v x) <= frac (v y)" by (simp add: **)
                  from frac_bound * have "t < 1 - frac (v x)" "t < 1 - frac (v y)" by fastforce+
                  with 2 t have 
                    "frac (v x) + t = frac (v x + t)" "frac (v y) + t = frac (v y + t)"
                  using F by blast+
                  with le show ?case unfolding cval_add_def by fastforce
                qed
              qed
            next
              case True
              then obtain d' where d': "I y = Const d'" unfolding Z_def by auto
              from B(5) show ?thesis unfolding r'_def
              proof (safe, goal_cases)
                case 1
                from d' have "y \<notin> ?X\<^sub>0" by auto
                moreover from assms(8) have "refl_on ?X\<^sub>0 r" by auto
                ultimately show ?case unfolding refl_on_def using 1 by auto
              next
                case 2
                with F show ?case by simp
              qed
            qed
          next
            case True
            with elem have **: "frac (v x) = 0" unfolding Z_def by force
            from B(4) have "y \<in> Z \<or> I y = Intv d'" unfolding I'_def by presburger
            then show ?thesis
            proof
              assume "y \<in> Z"
              with elem[OF B(3)] have ***: "frac (v y) = 0" unfolding Z_def by force
              show ?thesis by (simp add: ** *** frac_add cval_add_def)
            next
              assume A: "I y = Intv d'"
              with B(3) have "y \<in> ?X\<^sub>0" by auto
              with frac_bound have "t < 1 - frac (v y)" by fastforce+
              moreover from ** \<open>?t < 1\<close> have "?t / 2 < 1 - frac (v x)" by linarith
              ultimately have
                "frac (v x) + t = frac (v x + t)" "frac (v y) + t = frac (v y + t)"
              using frac_distr t by simp+
              moreover have "frac (v x) <= frac (v y)" by (simp add: **)
              ultimately show ?thesis unfolding cval_add_def by fastforce
            qed
          qed
        next
          case B: (2 x y d d')
          show ?case
          proof (cases "x \<in> Z", goal_cases)
            case True
            with B(1,2) have "intv_const (I x) \<noteq> k x" unfolding I'_def by auto
            with B(1) assms(8) have "intv_const (I x) < k x" by (fastforce elim!: valid_intv.cases)
            with B True show ?thesis unfolding r'_def by auto
          next
            case (False)
            with B(1,2) have x_intv: "isIntv (I x)" unfolding Z_def I'_def by auto
            show ?thesis
            proof (cases "y \<in> Z")
              case False
              with B(3,4) have y_intv: "isIntv (I y)" unfolding Z_def I'_def by auto
              with frac_bound x_intv B(1,3) have "t < 1 - frac (v x)" "t < 1 - frac (v y)" by auto
              from frac_add_leD[OF _ this] B(5) t have
                "frac (v x) \<le> frac (v y)"
              by (auto simp: cval_add_def)
              with v assms(2) B(1,3) x_intv y_intv have "(x, y) \<in> r" by (auto )
              then show ?thesis by (simp add: r'_def)
            next
              case True
              from frac_bound x_intv B(1) have b: "t < 1 - frac (v x)" by auto
              from x_intv obtain c where "I x = Intv c" by auto
              with elem[OF \<open>x \<in> X\<close>] have v: "c < v x" "v x < c + 1" by auto
              from True elem[OF \<open>y \<in> X\<close>] have *: "frac (v y) = 0" unfolding Z_def by auto
              with t \<open>?t < 1\<close> floor_frac_add_preservation'[of t "v y"] have
                "floor (v y + t) = floor (v y)"
              by auto
              then have "frac (v y + t) = t"
              by (metis * add_diff_cancel_left' diff_add_cancel diff_self frac_def)
              moreover from nat_intv_frac_gt0[OF v] have "0 < frac (v x)" .
              moreover from frac_distr[OF _ b] t have "frac (v x + t) = frac (v x) + t" by auto
              ultimately show ?thesis using B(5) unfolding cval_add_def by auto
            qed
          qed
        qed
      qed
    }
    with \<open>?t/2 > 0\<close> have "0 < ?t/2 \<and> (\<forall> t. 0 < t \<and> t \<le> ?t/2 \<longrightarrow> (v \<oplus> t) \<in> region X I' r')" by auto
  } note ** = this
  show "\<exists>t'\<le>t. (v \<oplus> t') \<in> region X I' r' \<and> 0 \<le> t'"
  proof (cases "\<exists> x \<in> X. isIntv (I x)")
    case True
    note T = this
    show ?thesis
    proof (cases "t \<le> ?t/2")
      case True with T t ** show ?thesis by auto
    next
      case False
      then have "?t/2 \<le> t" by auto
      moreover from T ** have "(v \<oplus> ?t/2) \<in> region X I' r'" "?t/2 > 0" by auto
      ultimately show ?thesis by (fastforce del: region.cases)
    qed
  next
    case False
    note F = this
    show ?thesis
    proof (cases "t < 1")
      case True with F t * show ?thesis by auto
    next
      case False
      then have "0.5 \<le> t" by auto
      moreover from F * have "(v \<oplus> 0.5) \<in> region X I' r'" by auto
      ultimately show ?thesis by (fastforce del: region.cases)
    qed
  qed
next
  fix v t assume A: "v \<in> region X I' r'" "0 \<le> t" "(v \<oplus> t) \<in> R"
  from assms(3,4) obtain x c where x: "I x = Const c" "x \<in> Z" "x \<in> X" by auto
  with A(1) have "intv_elem x v (I' x)" by auto
  with x have "v x > c" unfolding I'_def
    apply (auto elim: intv_elem.cases)
    apply (cases "c = k x")
  by auto
  moreover from A(3) x(1,3) have "v x + t = c"
  by (fastforce elim!: intv_elem.cases simp: cval_add_def R_def)
  ultimately show False using A(2) by auto
next
  fix x c assume "x \<in> X" "I' x = Const c"
  then show False
    apply (auto simp: I'_def Z_def)
    apply (cases "\<forall>c. I x \<noteq> Const c")
     apply auto
    apply (rename_tac c')
    apply (case_tac "c' = k x")
  by auto
next
  case (4 v t t' x c)
  note A = this
  then have "I' x = Intv c" unfolding I'_def Z_def by auto
  moreover from A have "real (c + 1) \<le> (v \<oplus> t') x + (t - t')" unfolding cval_add_def by auto
  ultimately show ?case by blast
next
  case A: (5 v t t' x c)
  show ?case
  proof (cases "x \<in> Z")
    case False
    with A have "I x = Intv c" unfolding I'_def by auto
    with A show ?thesis unfolding cval_add_def by auto
  next
    case True
    with A(6) have "I x = Const c"
      apply (auto simp: I'_def)
      apply (cases "intv_const (I x) = k x")
    by (auto simp: Z_def)
    with A(1,5) R_def have "v x = c" by fastforce
    with A(2,7) show ?thesis by (auto simp: cval_add_def)
  qed
qed

lemma closest_valid_1:
  fixes I X k r
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  defines "R \<equiv> region X I r"
  defines "Z \<equiv> {x \<in> X . \<exists> c. I x = Const c}"
  assumes "Z \<noteq> {}"
  defines "I'\<equiv> \<lambda> x. if x \<notin> Z then I x else if intv_const (I x) = k x then Greater (k x) else Intv (intv_const (I x))"
  defines "r' \<equiv> r \<union> {(x,y) . x \<in> Z \<and> y \<in> X \<and> intv_const (I x) < k x \<and> isIntv (I' y)}"
  assumes "finite X"
  assumes "valid_region X k I r"
  shows "valid_region X k I' r'"
proof
  let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
  let ?X\<^sub>0' = "{x \<in> X. \<exists>d. I' x = Intv d}"
  let ?S = "{(x, y). x \<in> Z \<and> y \<in> X \<and> intv_const (I x) < k x \<and> isIntv (I' y)}"
  show "?X\<^sub>0' = ?X\<^sub>0'" ..
  from assms(8) have refl: "refl_on ?X\<^sub>0 r" and total: "total_on ?X\<^sub>0 r" and trans: "trans r"
    and valid: "\<And> x. x \<in> X \<Longrightarrow> valid_intv (k x) (I x)"
  by auto
  then have "r \<subseteq> ?X\<^sub>0 \<times> ?X\<^sub>0" unfolding refl_on_def by auto
  then have "r \<subseteq> ?X\<^sub>0' \<times> ?X\<^sub>0'" unfolding I'_def Z_def by auto
  moreover have "?S \<subseteq> ?X\<^sub>0' \<times> ?X\<^sub>0'"
    apply (auto)
    apply (auto simp: Z_def)[]
    apply (auto simp: I'_def)[]
  done
  ultimately have "r'\<subseteq> ?X\<^sub>0' \<times> ?X\<^sub>0'" unfolding r'_def by auto
  then show "refl_on ?X\<^sub>0' r'" unfolding refl_on_def
  proof auto
    fix x d assume A: "x \<in> X" "I' x = Intv d"
    show "(x, x) \<in> r'"
    proof (cases "x \<in> Z")
      case True
      with A have "intv_const (I x) \<noteq> k x" unfolding I'_def by auto
      with assms(8) A(1) have "intv_const (I x) < k x" by (fastforce elim!: valid_intv.cases)
      with True A show "(x,x) \<in> r'" by (auto simp: r'_def)
    next
      case False
      with A refl show "(x,x) \<in> r'" by (auto simp: I'_def refl_on_def r'_def)
    qed
  qed
  show "total_on ?X\<^sub>0' r'" unfolding total_on_def
  proof (standard, standard, standard)
    fix x y assume "x \<in> ?X\<^sub>0'" "y \<in> ?X\<^sub>0'" "x \<noteq> y"
    then obtain d d' where A: "x\<in>X""y\<in>X""I' x = (Intv d)" "I' y = (Intv d')" "x \<noteq> y" by auto
    let ?thesis = "(x, y) \<in> r' \<or> (y, x) \<in> r'"
    show ?thesis
    proof (cases "x \<in> Z")
      case True
      with A have "intv_const (I x) \<noteq> k x" unfolding I'_def by auto
      with assms(8) A(1) have "intv_const (I x) < k x" by (fastforce elim!: valid_intv.cases)
      with True A show ?thesis by (auto simp: r'_def)
    next
      case F: False
      show ?thesis
      proof (cases "y \<in> Z")
        case True
        with A have "intv_const (I y) \<noteq> k y" unfolding I'_def by auto
        with assms(8) A(2) have "intv_const (I y) < k y" by (fastforce elim!: valid_intv.cases)
        with True A show ?thesis by (auto simp: r'_def)
      next
        case False
        with A F have "I x = Intv d" "I y = Intv d'" by (auto simp: I'_def)
        with A(1,2,5) total show ?thesis unfolding total_on_def r'_def by auto
      qed
    qed
  qed
  show "trans r'" unfolding trans_def
  proof safe
    fix x y z assume A: "(x, y) \<in> r'" "(y, z) \<in> r'"
    show "(x, z) \<in> r'"
    proof (cases "(x,y) \<in> r")
      case True
      then have "y \<notin> Z" using refl unfolding Z_def refl_on_def by auto
      then have "(y, z) \<in> r" using A unfolding r'_def by auto
      with trans True show ?thesis unfolding trans_def r'_def by blast
    next
      case False
      with A(1) have F: "x \<in> Z" "intv_const (I x) < k x" unfolding r'_def by auto
      moreover from A(2) refl have "z \<in> X" "isIntv (I' z)"
      by (auto simp: r'_def refl_on_def) (auto simp: I'_def Z_def)
      ultimately show ?thesis unfolding r'_def by auto
    qed
  qed
  show "\<forall>x\<in>X. valid_intv (k x) (I' x)"
  proof (auto simp: I'_def intro: valid, goal_cases)
    case (1 x)
    with assms(8) have "intv_const (I x) < k x" by (fastforce elim!: valid_intv.cases)
    then show ?case by auto
  qed
qed

lemma closest_prestable_2:
  fixes I X k r
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  defines "R \<equiv> region X I r"
  assumes "\<forall> x \<in> X. \<not> isConst (I x)"
  defines "X\<^sub>0 \<equiv> {x \<in> X. isIntv (I x)}"
  defines "M \<equiv> {x \<in> X\<^sub>0. \<forall> y \<in> X\<^sub>0. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r}"
  defines "I'\<equiv> \<lambda> x. if x \<notin> M then I x else Const (intv_const (I x) + 1)"
  defines "r' \<equiv> {(x,y) \<in> r. x \<notin> M \<and> y \<notin> M}"
  assumes "finite X"
  assumes "valid_region X k I r"
  assumes "M \<noteq> {}"
  shows   "\<forall> v \<in> R. \<forall> t\<ge>0. (v \<oplus> t) \<notin> R \<longrightarrow> (\<exists>t'\<le>t. (v \<oplus> t') \<in> region X I' r' \<and> t' \<ge> 0)"
  and     "\<forall> v \<in> region X I' r'. \<forall> t\<ge>0. (v \<oplus> t) \<notin> R"
  and     "\<forall> v \<in> R. \<forall> t'. {x. x \<in> X \<and> (\<exists> c. I' x = Intv c \<and> (v \<oplus> t') x + (t - t') \<ge> real (c + 1))}
                  = {x. x \<in> X \<and> (\<exists> c. I x  = Intv c \<and> v x + t \<ge> real (c + 1))} - M"
  and     "\<exists> x \<in> X. isConst (I' x)"
proof (safe, goal_cases)
  fix v assume v: "v \<in> R" fix t :: t assume t: "t \<ge> 0" "(v \<oplus> t) \<notin> R"
  note M = assms(10)
  then obtain x c where x: "x \<in> M" "I x = Intv c" "x \<in> X" "x \<in> X\<^sub>0" unfolding M_def X\<^sub>0_def by force
  let ?t = "1 - frac (v x)"
  let ?v = "v \<oplus> ?t"
  have elem: "intv_elem x v (I x)" if "x \<in> X" for x using that v unfolding R_def by auto
  from assms(9) have *: "trans r" "total_on {x \<in> X. \<exists>d. I x = Intv d} r" by auto
  then have trans[intro]: "\<And>x y z. (x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r" unfolding trans_def
  by blast
  have "{x \<in> X. \<exists>d. I x = Intv d} = X\<^sub>0" unfolding X\<^sub>0_def by auto
  with *(2) have total: "total_on X\<^sub>0 r" by auto
  { fix y assume y: "y \<notin> M" "y \<in> X\<^sub>0"
    have "\<not> (x, y) \<in> r" using x y unfolding M_def by auto
    moreover with total x y have "(y, x) \<in> r" unfolding total_on_def by auto
    ultimately have "\<not> (x, y) \<in> r \<and> (y, x) \<in> r" ..
  } note M_max = this
  { fix y assume T1: "y \<in> M" "x \<noteq> y"
    then have T2: "y \<in> X\<^sub>0" unfolding M_def by auto
    with total x T1 have "(x, y) \<in> r \<or> (y, x) \<in> r" by (auto simp: total_on_def)
    with T1(1) x(1) have "(x, y) \<in> r" "(y, x) \<in> r" unfolding M_def by auto
  } note M_eq = this
  { fix y assume y: "y \<notin> M" "y \<in> X\<^sub>0"
    with M_max have "\<not> (x, y) \<in> r" "(y, x) \<in> r" by auto
    with v[unfolded R_def] X\<^sub>0_def x(4) y(2) have "frac (v y) < frac (v x)" by auto
    then have "?t < 1 - frac (v y)" by auto
  } note t_bound' = this
  { fix y assume y: "y \<in> X\<^sub>0"
    have "?t \<le> 1 - frac (v y)"
    proof (cases "x = y")
      case True thus ?thesis by simp
    next
      case False
      have "(y, x) \<in> r"
      proof (cases "y \<in> M")
        case False with M_max y show ?thesis by auto
      next
        case True with False M_eq y show ?thesis by auto
      qed
      with v[unfolded R_def] X\<^sub>0_def x(4) y have "frac (v y) \<le> frac (v x)" by auto
      then show "?t \<le> 1 - frac (v y)" by auto
    qed
  } note t_bound''' = this
  have "frac (v x) < 1" by (simp add: frac_lt_1)
  then have "?t > 0" by (simp add: x(3))
  { fix c y fix t :: t assume y: "y \<notin> M" "I y = Intv c" "y \<in> X" and t: "t \<ge> 0" "t \<le> ?t"
    then have "y \<in> X\<^sub>0" unfolding X\<^sub>0_def by auto
    with t_bound' y have "?t < 1 - frac (v y)" by auto
    with t have "t < 1 - frac (v y)" by auto
    moreover from elem[OF \<open>y \<in> X\<close>] y have "c < v y" "v y < c + 1" by auto
    ultimately have "(v y + t) < c + 1" using frac_add_le_preservation by blast
    with \<open>c < v y\<close> t have "intv_elem y (v \<oplus> t) (I y)" by (auto simp: cval_add_def y)
  } note t_bound = this
  from elem[OF x(3)] x(2) have v_x: "c < v x" "v x < c + 1" by auto
  then have "floor (v x) = c" by linarith
  then have shift: "v x + ?t = c + 1" unfolding frac_def by auto
  have "v x + t \<ge> c + 1"
  proof (rule ccontr, goal_cases)
    case 1
    then have AA: "v x + t < c + 1" by simp
    with shift have lt: "t < ?t" by auto
    let ?v = "v \<oplus> t"
    have "?v \<in> region X I r"
    proof (standard, goal_cases)
      case 1
      from v have "\<forall> x \<in> X. v x \<ge> 0" unfolding R_def by auto
      with t show ?case unfolding cval_add_def by auto
    next
      case 2
      show ?case
      proof (safe, goal_cases)
        case (1 y)
        note A = this
        with elem have e: "intv_elem y v (I y)" by auto
        show ?case
        proof (cases "y \<in> M")
          case False
          then have [simp]: "I' y = I y" by (auto simp: I'_def)
          show ?thesis
          proof (cases "I y", goal_cases)
            case 1 with assms(3) A show ?case by auto
          next
            case (2 c)
            from t_bound[OF False this A t(1)] lt show ?case by (auto simp: cval_add_def 2)
          next
            case (3 c)
            with e have "v y > c" by auto
            with 3 t(1) show ?case by (auto simp: cval_add_def)
          qed
        next
          case True
          then have "y \<in> X\<^sub>0" by (auto simp: M_def)
          note T = this True
          show ?thesis
          proof (cases "x = y")
            case False
            with M_eq T have "(x, y) \<in> r" "(y, x) \<in> r" by presburger+
            with v[unfolded R_def] X\<^sub>0_def x(4) T(1) have *: "frac (v y) = frac (v x)" by auto
            from T(1) obtain c where c: "I y = Intv c" by (auto simp: X\<^sub>0_def)
            with elem T(1) have "c < v y" "v y < c + 1" by (fastforce simp: X\<^sub>0_def)+
            then have "floor (v y) = c" by linarith
            with * lt have "(v y + t) < c + 1" unfolding frac_def by auto
            with \<open>c < v y\<close> t show ?thesis by (auto simp: c cval_add_def)
          next
            case True with \<open>c < v x\<close> t AA x show ?thesis by (auto simp: cval_add_def)
          qed
        qed
      qed
    next
      show "X\<^sub>0 = {x \<in> X. \<exists>d. I x = Intv d}" by (auto simp add: X\<^sub>0_def)
    next
      have "t > 0"
      proof (rule ccontr, goal_cases)
        case 1 with t v show False unfolding cval_add_def by auto
      qed 
      show "\<forall>y\<in>X\<^sub>0. \<forall>z\<in>X\<^sub>0. ((y, z) \<in> r) = (frac ((v \<oplus> t)y) \<le> frac ((v \<oplus> t) z))"
      proof (auto simp: X\<^sub>0_def, goal_cases)
        case (1 y z d d')
        note A = this
        from A have [simp]: "y \<in> X\<^sub>0" "z \<in> X\<^sub>0" unfolding X\<^sub>0_def I'_def by auto
        from A v[unfolded R_def] have le: "frac (v y) \<le> frac (v z)" by (auto simp: r'_def)
        from t_bound''' have "?t \<le> 1 - frac (v y)" "?t \<le> 1 - frac (v z)" by auto
        with lt have "t < 1 - frac (v y)" "t < 1 - frac (v z)" by auto
        with frac_distr[OF \<open>t > 0\<close>] have
          "frac (v y) + t = frac (v y + t)" "frac (v z) + t = frac (v z + t)"
        by auto
        with le show ?case by (auto simp: cval_add_def)
      next
        case (2 y z d d')
        note A = this
        from A have [simp]: "y \<in> X\<^sub>0" "z \<in> X\<^sub>0" unfolding X\<^sub>0_def by auto
        from t_bound''' have "?t \<le> 1 - frac (v y)" "?t \<le> 1 - frac (v z)" by auto
        with lt have "t < 1 - frac (v y)" "t < 1 - frac (v z)" by auto
        from frac_add_leD[OF \<open>t > 0\<close> this] A(5) have
          "frac (v y) \<le> frac (v z)"
        by (auto simp: cval_add_def)
        with v[unfolded R_def] A show ?case by auto
      qed
    qed
    with t R_def show False by simp
  qed
  with shift have "t \<ge> ?t" by simp
  let ?R = "region X I' r'"
  let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I' x = Intv d}"
  have "(v \<oplus> ?t) \<in> ?R"
  proof (standard, goal_cases)
    case 1
    from v have "\<forall> x \<in> X. v x \<ge> 0" unfolding R_def by auto
    with \<open>?t > 0\<close> t show ?case unfolding cval_add_def by auto
  next
    case 2
    show ?case
    proof (safe, goal_cases)
      case (1 y)
      note A = this
      with elem have e: "intv_elem y v (I y)" by auto
      show ?case
      proof (cases "y \<in> M")
        case False
        then have [simp]: "I' y = I y" by (auto simp: I'_def)
        show ?thesis
        proof (cases "I y", goal_cases)
          case 1 with assms(3) A show ?case by auto
        next
          case (2 c)
          from t_bound[OF False this A] \<open>?t > 0\<close> show ?case by (auto simp: cval_add_def 2)
        next
          case (3 c)
          with e have "v y > c" by auto
          with 3 \<open>?t > 0\<close> show ?case by (auto simp: cval_add_def)
        qed
      next
        case True
        then have "y \<in> X\<^sub>0" by (auto simp: M_def)
        note T = this True
        show ?thesis
        proof (cases "x = y")
          case False
          with M_eq T(2) have "(x, y) \<in> r" "(y, x) \<in> r" by auto
          with v[unfolded R_def] X\<^sub>0_def x(4) T(1) have *: "frac (v y) = frac (v x)" by auto
          from T(1) obtain c where c: "I y = Intv c" by (auto simp: X\<^sub>0_def)
          with elem T(1) have "c < v y" "v y < c + 1" by (fastforce simp: X\<^sub>0_def)+
          then have "floor (v y) = c" by linarith
          with * have "(v y + ?t) = c + 1" unfolding frac_def by auto
          with T(2) show ?thesis by (auto simp: c cval_add_def I'_def)
        next
          case True with shift x show ?thesis by (auto simp: cval_add_def I'_def)
        qed
      qed
    qed
  next
    show "?X\<^sub>0 = ?X\<^sub>0" ..
  next
    show "\<forall>y\<in>?X\<^sub>0. \<forall>z\<in>?X\<^sub>0. ((y, z) \<in> r') = (frac ((v \<oplus> 1 - frac (v x))y) \<le> frac ((v \<oplus> 1 - frac (v x)) z))"
    proof (safe, goal_cases)
      case (1 y z d d')
      note A = this
      then have "y \<notin> M" "z \<notin> M" unfolding I'_def by auto
      with A have [simp]: "I' y = I y" "I' z = I z" "y \<in> X\<^sub>0" "z \<in> X\<^sub>0" unfolding X\<^sub>0_def I'_def by auto
      from A v[unfolded R_def] have le: "frac (v y) \<le> frac (v z)" by (auto simp: r'_def)
      from t_bound' \<open>y \<notin> M\<close> \<open>z \<notin> M\<close> have "?t < 1 - frac (v y)" "?t < 1 - frac (v z)" by auto
      with frac_distr[OF \<open>?t > 0\<close>] have
        "frac (v y) + ?t = frac (v y + ?t)" "frac (v z) + ?t = frac (v z + ?t)"
      by auto
      with le show ?case by (auto simp: cval_add_def)
    next
      case (2 y z d d')
      note A = this
      then have M: "y \<notin> M" "z \<notin> M" unfolding I'_def by auto
      with A have [simp]: "I' y = I y" "I' z = I z" "y \<in> X\<^sub>0" "z \<in> X\<^sub>0" unfolding X\<^sub>0_def I'_def by auto
      from t_bound' \<open>y \<notin> M\<close> \<open>z \<notin> M\<close> have "?t < 1 - frac (v y)" "?t < 1 - frac (v z)" by auto
      from frac_add_leD[OF \<open>?t > 0\<close> this] A(5) have
        "frac (v y) \<le> frac (v z)"
      by (auto simp: cval_add_def)
      with v[unfolded R_def] A M show ?case by (auto simp: r'_def)
    qed
  qed
  with \<open>?t > 0\<close> \<open>?t \<le> t\<close> show "\<exists>t'\<le>t. (v \<oplus> t') \<in> region X I' r' \<and> 0 \<le> t'" by auto
next
  fix v t assume A: "v \<in> region X I' r'" "0 \<le> t" "(v \<oplus> t) \<in> R"
  from assms(10) obtain x c where x:
    "x \<in> X\<^sub>0" "I x = Intv c" "x \<in> X" "x \<in> M"
  unfolding M_def X\<^sub>0_def by force
  with A(1) have "intv_elem x v (I' x)" by auto
  with x have "v x = c + 1" unfolding I'_def by auto
  moreover from A(3) x(2,3) have "v x + t < c + 1" by (fastforce simp: cval_add_def R_def)
  ultimately show False using A(2) by auto
next
  case A: (3 v t' x c)
  from A(3) have "I x = Intv c" by (auto simp: I'_def) (cases "x \<in> M", auto)
  with A(4) show ?case by (auto simp: cval_add_def)
next
  case 4
  then show ?case unfolding I'_def by auto
next
  case A: (5 v t' x c)
  then have "I' x = Intv c" unfolding I'_def by auto
  moreover from A have "real (c + 1) \<le> (v \<oplus> t') x + (t - t')" by (auto simp: cval_add_def)
  ultimately show ?case by blast
next
  from assms(5,10) obtain x where x: "x \<in> M" by blast
  then have "isConst (I' x)" by (auto simp: I'_def)
  with x show "\<exists>x\<in>X. isConst (I' x)" unfolding M_def X\<^sub>0_def by force
qed

lemma closest_valid_2:
  fixes I X k r
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  defines "R \<equiv> region X I r"
  assumes "\<forall> x \<in> X. \<not> isConst (I x)"
  defines "X\<^sub>0 \<equiv> {x \<in> X. isIntv (I x)}"
  defines "M \<equiv> {x \<in> X\<^sub>0. \<forall> y \<in> X\<^sub>0. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r}"
  defines "I'\<equiv> \<lambda> x. if x \<notin> M then I x else Const (intv_const (I x) + 1)"
  defines "r' \<equiv> {(x,y) \<in> r. x \<notin> M \<and> y \<notin> M}"
  assumes "finite X"
  assumes "valid_region X k I r"
  assumes "M \<noteq> {}"
  shows "valid_region X k I' r'"
proof
  let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
  let ?X\<^sub>0' = "{x \<in> X. \<exists>d. I' x = Intv d}"
  show "?X\<^sub>0' = ?X\<^sub>0'" ..
  from assms(9) have refl: "refl_on ?X\<^sub>0 r" and total: "total_on ?X\<^sub>0 r" and trans: "trans r"
    and valid: "\<And> x. x \<in> X \<Longrightarrow> valid_intv (k x) (I x)"
  by auto
  have subs: "r' \<subseteq> r" unfolding r'_def by auto
  from refl have "r \<subseteq> ?X\<^sub>0 \<times> ?X\<^sub>0" unfolding refl_on_def by auto
  then have "r'\<subseteq> ?X\<^sub>0' \<times> ?X\<^sub>0'" unfolding r'_def I'_def by auto
  then show "refl_on ?X\<^sub>0' r'" unfolding refl_on_def
  proof auto
    fix x d assume A: "x \<in> X" "I' x = Intv d"
    then have "x \<notin> M" by (force simp: I'_def)
    with A have "I x = Intv d" by (force simp: I'_def)
    with A refl have "(x,x) \<in> r" by (auto simp: refl_on_def)
    then show "(x, x) \<in> r'" by (auto simp: r'_def \<open>x \<notin> M\<close>)
  qed
  show "total_on ?X\<^sub>0' r'" unfolding total_on_def
  proof (safe, goal_cases)
    case (1 x y d d')
    note A = this
    then have *: "x \<notin> M" "y \<notin> M" by (force simp: I'_def)+
    with A have "I x = Intv d" "I y = Intv d'" by (force simp: I'_def)+
    with A total have "(x, y) \<in> r \<or> (y, x) \<in> r" by (auto simp: total_on_def)
    with A(6) * show ?case unfolding r'_def by auto
  qed
  show "trans r'" unfolding trans_def
  proof safe
    fix x y z assume A: "(x, y) \<in> r'" "(y, z) \<in> r'"
    from trans have [intro]:
      "\<And> x y z. (x,y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r"
    unfolding trans_def by blast
    from A show "(x, z) \<in> r'" by (auto simp: r'_def)
  qed
  show "\<forall>x\<in>X. valid_intv (k x) (I' x)"
  using valid  unfolding I'_def
  proof (auto simp: I'_def intro: valid, goal_cases)
    case (1 x)
    with assms(9) have "intv_const (I x) < k x" by (fastforce simp: M_def X\<^sub>0_def)
    then show ?case by auto
  qed
qed

subsection \<open>Putting the Proof for the 'Set of Regions' Property Together\<close>

subsubsection \<open>Misc\<close>

lemma total_finite_trans_max:
  "X \<noteq> {} \<Longrightarrow> finite X \<Longrightarrow> total_on X r \<Longrightarrow> trans r \<Longrightarrow> \<exists> x \<in> X. \<forall> y \<in> X. x \<noteq> y \<longrightarrow> (y, x) \<in> r"
proof (induction "card X" arbitrary: X)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain x where x: "x \<in> X" by blast
  show ?case
  proof (cases "n = 0")
    case True
    with Suc.hyps(2) \<open>finite X\<close> x have "X = {x}" by (metis card_Suc_eq empty_iff insertE)
    then show ?thesis by auto
  next
    case False
    show ?thesis
    proof (cases "\<forall>y\<in>X. x \<noteq> y \<longrightarrow> (y, x) \<in> r")
      case True with x show ?thesis by auto
    next
      case False
      then obtain y where y: "y \<in> X" "x \<noteq> y" "\<not> (y, x) \<in> r" by auto
      with x Suc.prems(3) have "(x, y) \<in> r" unfolding total_on_def by blast
      let ?X = "X - {x}"
      have tot: "total_on ?X r" using \<open>total_on X r\<close> unfolding total_on_def by auto
      from x Suc.hyps(2) \<open>finite X\<close> have card: "n = card ?X" by auto
      with \<open>finite X\<close> \<open>n \<noteq> 0\<close> have "?X \<noteq> {}" by auto
      from Suc.hyps(1)[OF card this _ tot \<open>trans r\<close>] \<open>finite X\<close> obtain x' where
        IH: "x' \<in> ?X" "\<forall> y \<in> ?X. x' \<noteq> y \<longrightarrow> (y, x') \<in> r"
      by auto
      have "(x', x) \<notin> r"
      proof (rule ccontr, auto)
        assume A: "(x', x) \<in> r"
        with y(3) have "x' \<noteq> y" by auto
        with y IH have "(y, x') \<in> r" by auto
        with \<open>trans r\<close> A have "(y, x) \<in> r" unfolding trans_def by blast
        with y show False by auto
      qed
      with \<open>x \<in> X\<close> \<open>x' \<in> ?X\<close> \<open>total_on X r\<close> have "(x, x') \<in> r" unfolding total_on_def by auto
      with IH show ?thesis by auto
    qed
  qed
qed

lemma card_mono_strict_subset:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> finite C \<Longrightarrow> A \<inter> B \<noteq> {} \<Longrightarrow> C = A - B \<Longrightarrow> card C < card A"
by (metis Diff_disjoint Diff_subset inf_commute less_le psubset_card_mono)

subsubsection \<open>Proof\<close>

text \<open>
  First we show that a shift by a non-negative integer constant means that any two valuations from 
  the same region are being shifted to the same region.
\<close>

lemma int_shift_equiv:
  fixes X k fixes t :: int
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "v \<in> R" "v' \<in> R" "R \<in> \<R>" "t \<ge> 0"
  shows "(v' \<oplus> t) \<in> [v \<oplus> t]\<^sub>\<R>" using assms
proof -
  from assms obtain I r where A: "R = region X I r" "valid_region X k I r" by auto
  from regions_closed[OF _ assms(4,2), of X k t] assms(1,5) obtain I' r' where RR:
    "[v \<oplus> t]\<^sub>\<R> = region X I' r'" "valid_region X k I' r'"
  by auto
  from regions_closed'[OF _ assms(4,2), of X k t] assms(1,5) have RR': "(v \<oplus> t) \<in> [v \<oplus> t]\<^sub>\<R>" by auto
  show ?thesis
  proof (simp add: RR(1), rule, goal_cases)
    case 1
    from \<open>v' \<in> R\<close> A(1) have "\<forall>x\<in>X. 0 \<le> v' x" by auto
    with \<open>t \<ge> 0\<close> show ?case unfolding cval_add_def by auto
  next
    case 2
    show ?case
    proof safe
      fix x assume x: "x \<in> X"
      with \<open>v' \<in> R\<close> \<open>v \<in> R\<close> A(1) have I: "intv_elem x v (I x)" "intv_elem x v' (I x)" by auto
      from x RR RR' have I': "intv_elem x (v \<oplus> t) (I' x)" by auto
      show "intv_elem x (v' \<oplus> t) (I' x)"
      proof (cases "I' x")
        case (Const c)
        from Const I' have "v x + t = c" unfolding cval_add_def by auto
        with x A(1) \<open>v \<in> R\<close> \<open>t \<ge> 0\<close> have *: "v x = c - nat t" "t \<le> c" by fastforce+
        with \<open>t \<ge> 0\<close> I(1) have "I x = Const (c - nat t)"
        proof (cases "I x", auto)
          case (Greater c')
          from RR(2) Const \<open>x \<in> X\<close> have "c \<le> k x" by fastforce
          with Greater * \<open>t \<ge> 0\<close> have *: "v x \<le> k x" by auto
          from Greater A(2) \<open>x \<in> X\<close> have "c' = k x" by fastforce
          moreover from I(1) Greater have "v x > c'" by auto
          ultimately show False using \<open>c \<le> k x\<close> * by auto
        qed
        with I \<open>t \<ge> 0\<close> *(2) have "v' x + t = c" by auto
        with Const show ?thesis unfolding cval_add_def by auto
      next
        case (Intv c)
        with I' have "c < v x + t" "v x + t < c + 1" unfolding cval_add_def by auto
        with x A(1) \<open>v \<in> R\<close> \<open>t \<ge> 0\<close> have
          *: "c - nat t < v x" "v x < c - nat t + 1" "t \<le> c"
        by fastforce+
        with I have "I x = Intv (c - nat t)"
        proof (cases "I x", auto)
          case (Greater c')
          from RR(2) Intv \<open>x \<in> X\<close> have "c < k x" by fastforce
          with Greater * have *: "v x \<le> k x" by auto
          from Greater A(2) \<open>x \<in> X\<close> have "c' = k x" by fastforce
          moreover from I(1) Greater have "v x > c'" by auto
          ultimately show False using \<open>c < k x\<close> * by auto
        qed
        with I \<open>t \<le> c\<close> have "c < v' x + nat t" "v' x + t < c + 1" by auto
        with Intv \<open>t \<ge> 0\<close> show ?thesis unfolding cval_add_def by auto
      next
        case (Greater c)
        with I' have *: "c < v x + t" unfolding cval_add_def by auto
        show ?thesis
        proof (cases "I x")
          case (Const c')
          with x A(1) I(2) \<open>v \<in> R\<close> \<open>v' \<in> R\<close> have "v x = v' x" by fastforce
          with Greater * show ?thesis unfolding cval_add_def by auto
        next
          case (Intv c')
          with x A(1) I(2) \<open>v \<in> R\<close> \<open>v' \<in> R\<close> have **: "c' < v x" "v x < c' + 1" "c' < v' x"
          by fastforce+
          then have "c' + t < v x + t" "v x + t < c' + t + 1" by auto
          with * have "c \<le> c' + t" by auto
          with **(3) have "v' x + t > c" by auto
          with Greater * show ?thesis unfolding cval_add_def by auto
        next
          fix c' assume c': "I x = Greater c'"
          with x A(1) I(2) \<open>v \<in> R\<close> \<open>v' \<in> R\<close> have **: "c' < v x" "c' < v' x" by fastforce+
          from Greater RR(2) c' A(2) \<open>x \<in> X\<close> have "c' = k x" "c = k x" by fastforce+
          with \<open>t \<ge> 0\<close> **(2) Greater show "intv_elem x (v' \<oplus> real_of_int t) (I' x)"
          unfolding cval_add_def by auto
        qed
      qed
    qed
  next
    show "{x \<in> X. \<exists>d. I' x = Intv d} = {x \<in> X. \<exists>d. I' x = Intv d}" ..
  next
    let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I' x = Intv d}"
    { fix x y :: real
      have "frac (x + t) \<le> frac (y + t) \<longleftrightarrow> frac x \<le> frac y" by (simp add: frac_def)
    } note frac_equiv = this
    { fix x y
      have "frac ((v \<oplus> t) x) \<le> frac ((v \<oplus> t) y) \<longleftrightarrow> frac (v x) \<le> frac (v y)"
      unfolding cval_add_def using frac_equiv by auto
    } note frac_equiv' = this
    { fix x y
      have "frac ((v' \<oplus> t) x) \<le> frac ((v' \<oplus> t) y) \<longleftrightarrow> frac (v' x) \<le> frac (v' y)"
      unfolding cval_add_def using frac_equiv by auto
    } note frac_equiv'' = this
    { fix x y assume x: "x \<in> X" and y: "y \<in> X" and B: "\<not> isGreater(I x)" "\<not> isGreater(I y)"
      have "frac (v x) \<le> frac (v y) \<longleftrightarrow> frac (v' x) \<le> frac (v' y)"
      proof (cases "I x")
        case (Const c)
        with x \<open>v \<in> R\<close> \<open>v' \<in> R\<close> A(1) have "v x = c" "v' x = c" by fastforce+
        then have "frac (v x) \<le> frac (v y)" "frac (v' x) \<le> frac (v' y)" by(simp add: frac_def)+
        then show ?thesis by auto
      next
        case (Intv c)
        with x \<open>v \<in> R\<close> A(1) have v: "c < v x" "v x < c + 1" by fastforce+
        from Intv x \<open>v' \<in> R\<close> A(1) have v':"c < v' x" "v' x < c + 1" by fastforce+
        show ?thesis
        proof (cases "I y", goal_cases)
          case (Const c')
          with y \<open>v \<in> R\<close> \<open>v' \<in> R\<close> A(1) have "v y = c'" "v' y = c'" by fastforce+
          then have "frac (v y) = 0" "frac (v' y) = 0" by auto
          with nat_intv_frac_gt0[OF v] nat_intv_frac_gt0[OF v']
          have "\<not> frac (v x) \<le> frac (v y)" "\<not> frac (v' x) \<le> frac (v' y)" by linarith+
          then show ?thesis by auto
        next
          case 2: (Intv c')
          with x y Intv \<open>v \<in> R\<close> \<open>v' \<in> R\<close> A(1) have
            "(x, y) \<in> r \<longleftrightarrow> frac (v x) \<le> frac (v y)"
            "(x, y) \<in> r \<longleftrightarrow> frac (v' x) \<le> frac (v' y)"
          by auto
          then show ?thesis by auto
        next
          case Greater
          with B show ?thesis by auto
        qed
      next
        case Greater with B show ?thesis by auto
      qed
    } note frac_cong = this
    have not_greater: "\<not> isGreater (I x)" if x: "x \<in> X" "\<not> isGreater (I' x)" for x
    proof (rule ccontr, auto, goal_cases)
      case (1 c)
      with x \<open>v \<in> R\<close> A(1,2) have "c < v x" by fastforce+
      moreover from x A(2) 1 have "c = k x" by fastforce+
      ultimately have *: "k x < v x + t" using \<open>t \<ge> 0\<close> by simp
      from RR(1,2) RR' x have I': "intv_elem x (v \<oplus> t) (I' x)" "valid_intv (k x) (I' x)" by auto
      from x show False
      proof (cases "I' x", auto)
        case (Const c')
        with I' * show False by (auto simp: cval_add_def)
      next
        case (Intv c')
        with I' * show False by (auto simp: cval_add_def)
      qed
    qed
    show "\<forall> x \<in> ?X\<^sub>0. \<forall>y \<in> ?X\<^sub>0. ((x, y) \<in> r') = (frac ((v' \<oplus> t) x) \<le> frac ((v' \<oplus> t) y))"
    proof (standard, standard)
      fix x y assume x: "x \<in> ?X\<^sub>0" and y: "y \<in> ?X\<^sub>0"
      then have B: "\<not> isGreater (I' x)" "\<not> isGreater (I' y)" by auto
      with x y not_greater have "\<not> isGreater (I x)" "\<not> isGreater (I y)" by auto
      with x y frac_cong have "frac (v x) \<le> frac (v y) \<longleftrightarrow> frac (v' x) \<le> frac (v' y)" by auto
      moreover from x y RR(1) RR' have "(x, y) \<in> r' \<longleftrightarrow> frac ((v \<oplus> t) x) \<le> frac ((v \<oplus> t) y)"
      by fastforce
      ultimately show "(x, y) \<in> r' \<longleftrightarrow> frac ((v' \<oplus> t) x) \<le> frac ((v' \<oplus> t) y)"
      using frac_equiv' frac_equiv'' by blast
    qed
  qed
qed

text \<open>
  Now, we can use the 'immediate' induction proposed by P. Bouyer for shifts smaller than one.
  The induction principle is not at all obvious: the induction is over the set of clocks for
  which the valuation is shifted beyond the current interval boundaries.
  Using the two successor operations, we can see that either the set of these clocks remains the
  same (Z ~= {}) or strictly decreases (Z = {}).
\<close>

lemma set_of_regions_lt_1:
  fixes X k I r t v
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  defines "C \<equiv> {x. x \<in> X \<and> (\<exists> c. I x = Intv c \<and> v x + t \<ge> c + 1)}"
  assumes "valid_region X k I r" "v \<in> region X I r" "v' \<in> region X I r" "finite X" "0 \<le> t" "t < 1"
  shows "\<exists> t'\<ge>0. (v' \<oplus> t') \<in> [v \<oplus> t]\<^sub>\<R>" using assms
proof (induction "card C" arbitrary: C I r v v' t rule: less_induct)
  case less
  let ?R = "region X I r"
  let ?C = "{x \<in> X. \<exists>c. I x = Intv c \<and> real (c + 1) \<le> v x + t}"
  from less have R: "?R \<in> \<R>" by auto
  { fix v I k r fix t :: t
    assume no_consts: "\<forall>x\<in>X. \<not>isConst (I x)"
    assume v: "v \<in> region X I r"
    assume t: "t \<ge> 0"
    let ?C = "{x \<in> X. \<exists>c. I x = Intv c \<and> real (c + 1) \<le> v x + t}"
    assume C: "?C = {}"
    let ?R = "region X I r"
    have "(v \<oplus> t) \<in> ?R"
    proof (rule, goal_cases)
      case 1
      with \<open>t \<ge> 0\<close> \<open>v \<in> ?R\<close> show ?case by (auto simp: cval_add_def)
    next
      case 2
      show ?case
      proof (standard, case_tac "I x", goal_cases)
        case (1 x c)
        with no_consts show ?case by auto
      next
        case (2 x c)
        with \<open>v \<in> ?R\<close> have "c < v x" by fastforce
        with \<open>t \<ge> 0\<close> have "c < v x + t" by auto
        moreover from 2 C have "v x + t < c + 1" by fastforce
        ultimately show ?case by (auto simp: 2 cval_add_def)
      next
        case (3 x c)
        with \<open>v \<in> ?R\<close> have "c < v x" by fastforce
        with \<open>t \<ge> 0\<close> have "c < v x + t" by auto
        then show ?case by (auto simp: 3 cval_add_def)
      qed
    next
        show "{x \<in> X. \<exists>d. I x = Intv d} = {x \<in> X. \<exists>d. I x = Intv d}" ..
    next
      let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
      { fix x d :: real fix c:: nat assume A: "c < x" "x + d < c + 1" "d \<ge> 0"
        then have "d < 1 - frac x" unfolding frac_def using floor_eq3 of_nat_Suc by fastforce
      } note intv_frac = this
      { fix x assume x: "x \<in> ?X\<^sub>0"
        then obtain c where x: "x \<in> X" "I x = Intv c" by auto
        with \<open>v \<in> ?R\<close> have *: "c < v x" by fastforce
        with \<open>t \<ge> 0\<close> have "c < v x + t" by auto
        from x C have "v x + t < c + 1" by auto
        from intv_frac[OF * this \<open>t \<ge> 0\<close>] have "t < 1 - frac (v x) " by auto
      } note intv_frac = this
      { fix x y assume x: "x \<in> ?X\<^sub>0" and y: "y \<in> ?X\<^sub>0"
        from frac_add_leIFF[OF \<open>t \<ge> 0\<close> intv_frac[OF x] intv_frac[OF y]]
        have "frac (v x) \<le> frac (v y) \<longleftrightarrow> frac ((v \<oplus> t) x) \<le> frac ((v \<oplus> t) y)"
        by (auto simp: cval_add_def)
      } note frac_cong = this
      show "\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac ((v  \<oplus> t) x) \<le> frac ((v \<oplus> t) y)"
      proof (standard, standard, goal_cases)
        case (1 x y)
        with \<open>v \<in> ?R\<close> have "(x, y) \<in> r \<longleftrightarrow> frac (v x) \<le> frac (v y)" by auto
        with frac_cong[OF 1] show ?case by simp
      qed
    qed
  } note critical_empty_intro = this
  { assume const: "\<exists>x\<in>X. isConst (I x)"
    assume t: "t > 0"
    from const have "{x \<in> X. \<exists>c. I x = Const c} \<noteq> {}" by auto
    from closest_prestable_1[OF this less.prems(4) less(3)] R closest_valid_1[OF this less.prems(4) less(3)]
    obtain I'' r''
      where   stability: "\<forall> v \<in> ?R. \<forall> t>0. \<exists>t'\<le>t. (v \<oplus> t') \<in> region X I'' r'' \<and> t' \<ge> 0"
      and succ_not_refl: "\<forall> v \<in> region X I'' r''. \<forall> t\<ge>0. (v \<oplus> t) \<notin> ?R"
      and no_consts:     "\<forall> x \<in> X. \<not> isConst (I'' x)"
      and crit_mono:     "\<forall> v \<in> ?R. \<forall> t < 1. \<forall> t' \<ge> 0. (v \<oplus> t') \<in> region X I'' r''
                          \<longrightarrow> {x. x \<in> X \<and> (\<exists> c. I x = Intv c \<and> v x + t \<ge> c + 1)}
                            = {x. x \<in> X \<and> (\<exists> c. I'' x = Intv c \<and> (v \<oplus> t') x + (t - t') \<ge> c + 1)}"
      and succ_valid:    "valid_region X k I'' r''"
    by auto
    let ?R'' = "region X I'' r''"
    from stability less(4) \<open>t > 0\<close> obtain t1 where t1: "t1 \<ge> 0" "t1 \<le> t" "(v \<oplus> t1) \<in> ?R''" by auto
    from stability less(5) \<open>t > 0\<close> obtain t2 where t2: "t2 \<ge> 0" "t2 \<le> t" "(v' \<oplus> t2) \<in> ?R''" by auto
    let ?v = "v \<oplus> t1"
    let ?t = "t - t1"
    let ?C' = "{x \<in> X. \<exists>c. I'' x = Intv c \<and> real (c + 1) \<le> ?v x + ?t}"
    from t1 \<open>t < 1\<close> have tt: "0 \<le> ?t" "?t < 1" by auto
    from crit_mono \<open>t < 1\<close> t1(1,3) \<open>v \<in> ?R\<close> have crit:
      "?C = ?C'"
    by auto
    with t1 t2 succ_valid no_consts have
      "\<exists> t1 \<ge> 0. \<exists> t2 \<ge> 0. \<exists> I' r'. t1 \<le> t \<and> (v \<oplus> t1) \<in> region X I' r'
       \<and> t2 \<le> t \<and> (v' \<oplus> t2) \<in> region X I' r'
       \<and> valid_region X k I' r'
       \<and> (\<forall> x \<in> X. \<not> isConst (I' x))
       \<and> ?C = {x \<in> X. \<exists>c. I' x = Intv c \<and> real (c + 1) \<le> (v \<oplus> t1) x + (t - t1)}"
    by blast
  } note const_dest = this
  { fix t :: real fix v I r x c v'
    let ?R = "region X I r"
    assume v: "v \<in> ?R"
    assume v': "v' \<in> ?R"
    assume valid: "valid_region X k I r"
    assume t: "t > 0" "t < 1"
    let ?C = "{x \<in> X. \<exists>c. I x = Intv c \<and> real (c + 1) \<le> v x + t}"
    assume C: "?C = {}"
    assume const: "\<exists> x \<in> X. isConst (I x)"
    then have "{x \<in> X. \<exists>c. I x = Const c} \<noteq> {}" by auto
    from closest_prestable_1[OF this less.prems(4) valid] R closest_valid_1[OF this less.prems(4) valid]
    obtain I'' r''
      where   stability: "\<forall> v \<in> ?R. \<forall> t>0. \<exists>t'\<le>t. (v \<oplus> t') \<in> region X I'' r'' \<and> t' \<ge> 0"
      and succ_not_refl: "\<forall> v \<in> region X I'' r''. \<forall> t\<ge>0. (v \<oplus> t) \<notin> ?R"
      and no_consts:     "\<forall> x \<in> X. \<not> isConst (I'' x)"
      and crit_mono:     "\<forall> v \<in> ?R. \<forall> t < 1. \<forall> t' \<ge> 0. (v \<oplus> t') \<in> region X I'' r''
                          \<longrightarrow> {x. x \<in> X \<and> (\<exists> c. I x = Intv c \<and> v x + t \<ge> c + 1)}
                            = {x. x \<in> X \<and> (\<exists> c. I'' x = Intv c \<and> (v \<oplus> t') x + (t - t') \<ge> c + 1)}"
      and succ_valid:    "valid_region X k I'' r''"
    by auto
    let ?R'' = "region X I'' r''"
    from stability v \<open>t > 0\<close> obtain t1 where t1: "t1 \<ge> 0" "t1 \<le> t" "(v \<oplus> t1) \<in> ?R''" by auto
    from stability v' \<open>t > 0\<close> obtain t2 where t2: "t2 \<ge> 0" "t2 \<le> t" "(v' \<oplus> t2) \<in> ?R''" by auto
    let ?v = "v \<oplus> t1"
    let ?t = "t - t1"
    let ?C' = "{x \<in> X. \<exists>c. I'' x = Intv c \<and> real (c + 1) \<le> ?v x + ?t}"
    from t1 \<open>t < 1\<close> have tt: "0 \<le> ?t" "?t < 1" by auto
    from crit_mono \<open>t < 1\<close> t1(1,3) \<open>v \<in> ?R\<close> have crit:
      "{x \<in> X. \<exists>c. I x = Intv c \<and> real (c + 1) \<le> v x + t}
        = {x \<in> X. \<exists>c. I'' x = Intv c \<and> real (c + 1) \<le> (v \<oplus> t1) x + (t - t1)}"
    by auto
    with C have C: "?C' = {}" by blast
    from critical_empty_intro[OF no_consts t1(3) tt(1) this] have "((v \<oplus> t1) \<oplus> ?t) \<in> ?R''" .
    from region_unique[OF less(2) this] less(2) succ_valid t2 have "\<exists>t'\<ge>0. (v' \<oplus> t') \<in> [v \<oplus> t]\<^sub>\<R>"
    by (auto simp: cval_add_def)
  } note intro_const = this
  { fix v I r t x c v'
    let ?R = "region X I r"
    assume v: "v \<in> ?R"
    assume v': "v' \<in> ?R"
    assume F2: "\<forall>x\<in>X. \<not>isConst (I x)"
    assume x: "x \<in> X" "I x = Intv c" "v x + t \<ge> c + 1"
    assume valid: "valid_region X k I r"
    assume t: "t \<ge> 0" "t < 1"
    let ?C' = "{x \<in> X. \<exists>c. I x = Intv c \<and> real (c + 1) \<le> v x + t}"
    assume C: "?C = ?C'"
    have not_in_R: "(v \<oplus> t) \<notin> ?R"
    proof (rule ccontr, auto)
      assume "(v \<oplus> t) \<in> ?R"
      with x(1,2) have "v x + t < c + 1" by (fastforce simp: cval_add_def)
      with x(3) show False by simp
    qed
    have not_in_R': "(v' \<oplus> 1) \<notin> ?R"
    proof (rule ccontr, auto)
      assume "(v' \<oplus> 1) \<in> ?R"
      with x have "v' x + 1 < c + 1" by (fastforce simp: cval_add_def)
      moreover from x v' have "c < v' x" by fastforce
      ultimately show False by simp
    qed
    let ?X\<^sub>0 = "{x \<in> X. isIntv (I x)}"
    let ?M = "{x \<in> ?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r}"
    from x have x: "x \<in> X" "\<not> isGreater (I x)" and c: "I x = Intv c" by auto
    with \<open>x \<in> X\<close> have *: "?X\<^sub>0 \<noteq> {}" by auto
    have "?X\<^sub>0 = {x \<in> X. \<exists>d. I x = Intv d}" by auto
    with valid have r: "total_on ?X\<^sub>0 r" "trans r" by auto
    from total_finite_trans_max[OF * _ this] \<open>finite X\<close>
    obtain x' where x': "x' \<in> ?X\<^sub>0" "\<forall> y \<in> ?X\<^sub>0. x' \<noteq> y \<longrightarrow> (y, x') \<in> r" by fastforce
    from this(2) have "\<forall>y\<in>?X\<^sub>0. (x', y) \<in> r \<longrightarrow> (y, x') \<in> r" by auto
    with x'(1) have "?M \<noteq> {}" by fastforce
    from closest_prestable_2[OF F2 less.prems(4) valid this] closest_valid_2[OF F2 less.prems(4) valid this] 
    obtain I' r'
      where   stability:
        "\<forall> v \<in> region X I r. \<forall> t\<ge>0. (v \<oplus> t) \<notin> region X I r \<longrightarrow> (\<exists>t'\<le>t. (v \<oplus> t') \<in> region X I' r' \<and> t' \<ge> 0)"
      and succ_not_refl: "\<forall> v \<in> region X I' r'. \<forall> t\<ge>0. (v \<oplus> t) \<notin> region X I r"
      and critical_mono: "\<forall> v \<in> region X I r. \<forall>t. \<forall> t'.
                            {x. x \<in> X \<and> (\<exists> c. I' x = Intv c \<and> (v \<oplus> t') x + (t - t') \<ge> real (c + 1))}
                            = {x. x \<in> X \<and> (\<exists> c. I x  = Intv c \<and> v x + t \<ge> real (c + 1))} - ?M"
      and const_ex:      "\<exists>x\<in>X. isConst (I' x)"
      and succ_valid:    "valid_region X k I' r'"
    by auto
    let ?R' = "region X I' r'"
    from not_in_R stability \<open>t \<ge> 0\<close> v obtain t' where
      t': "t' \<ge> 0" "t' \<le> t" "(v \<oplus> t') \<in> ?R'"
    by blast
    have "(1::t) \<ge> 0" by auto
    with not_in_R' stability v' obtain t1 where
      t1: "t1 \<ge> 0" "t1 \<le> 1" "(v' \<oplus> t1) \<in> ?R'"
    by blast
    let ?v = "v \<oplus> t'"
    let ?t = "t - t'"
    let ?C'' = "{x \<in> X. \<exists>c. I' x = Intv c \<and> real (c + 1) \<le> ?v x + ?t}"
    have "\<exists>t'\<ge>0. (v' \<oplus> t') \<in> [v \<oplus> t]\<^sub>\<R>"
    proof (cases "t = t'")
      case True
      with t' have "(v \<oplus> t) \<in> ?R'" by auto
      from region_unique[OF less(2) this] succ_valid \<R>_def have "[v \<oplus> t]\<^sub>\<R> = ?R'" by blast
      with t1(1,3) show ?thesis by auto
    next
      case False
      with \<open>t < 1\<close> t' have tt: "0 \<le> ?t" "?t < 1" "?t > 0" by auto
      from critical_mono \<open>v \<in> ?R\<close> have C_eq: "?C'' = ?C' - ?M" by auto
      show "\<exists>t'\<ge>0. (v' \<oplus> t') \<in> [v \<oplus> t]\<^sub>\<R>"
      proof (cases "?C' \<inter> ?M = {}")
        case False
        from \<open>finite X\<close> have "finite ?C''" "finite ?C'" "finite ?M" by auto
        then have "card ?C'' < card ?C" using C_eq C False by (intro card_mono_strict_subset) auto
        from less(1)[OF this less(2) succ_valid t'(3) t1(3) \<open>finite X\<close> tt(1,2)]
        obtain t2 where "t2 \<ge> 0" "((v' \<oplus> t1) \<oplus> t2) \<in> [(v \<oplus> t)]\<^sub>\<R>" by (auto simp: cval_add_def)
        moreover have "(v' \<oplus> (t1 + t2)) = ((v' \<oplus> t1) \<oplus> t2)" by (auto simp: cval_add_def)
        moreover have "t1 + t2 \<ge> 0" using \<open>t2 \<ge> 0\<close> t1(1) by auto
        ultimately show ?thesis by metis
      next
        case True
        { fix x c assume x: "x \<in> X" "I x = Intv c" "real (c + 1) \<le> v x + t"
          with True have "x \<notin> ?M" by force
          from x have "x \<in> ?X\<^sub>0" by auto
          from x(1,2) \<open>v \<in> ?R\<close> have *: "c < v x" "v x < c + 1" by fastforce+
          with \<open>t < 1\<close> have "v x + t < c + 2" by auto
          have ge_1: "frac (v x) + t \<ge> 1"
          proof (rule ccontr, goal_cases)
            case 1
            then have A: "frac (v x) + t < 1" by auto
            from * have "floor (v x) + frac (v x) < c + 1" unfolding frac_def by auto
            with nat_intv_frac_gt0[OF *] have "floor (v x) \<le> c" by linarith
            with A have "v x + t < c + 1" by (auto simp: frac_def)
            with x(3) show False by auto
          qed
          from \<open>?M \<noteq> {}\<close> obtain y where "y \<in> ?M" by force
          with \<open>x \<in> ?X\<^sub>0\<close> have y: "y \<in> ?X\<^sub>0" "(y, x) \<in> r \<longrightarrow> (x, y) \<in> r" by auto
          from y obtain c' where c': "y \<in> X" "I y = Intv c'" by auto
          with \<open>v \<in> ?R\<close> have "c' < v y" by fastforce
          from \<open>y \<in> ?M\<close> \<open>x \<notin> ?M\<close> have "x \<noteq> y" by auto
          with y r(1) x(1,2) have "(x, y) \<in> r" unfolding total_on_def by fastforce
          with \<open>v \<in> ?R\<close> c' x have "frac (v x) \<le> frac (v y)" by fastforce
          with ge_1 have frac: "frac (v y) + t \<ge> 1" by auto
          have "real (c' + 1) \<le> v y + t"
          proof (rule ccontr, goal_cases)
            case 1
            from \<open>c' < v y\<close> have "floor (v y) \<ge> c'" by linarith
            with frac have "v y + t \<ge> c' + 1" unfolding frac_def by linarith
            with 1 show False by simp
          qed
          with c' True \<open>y \<in> ?M\<close> have False by auto
        }
        then have C: "?C' = {}" by auto
        with C_eq have C'': "?C'' = {}" by auto
        from intro_const[OF t'(3) t1(3) succ_valid tt(3) tt(2) C'' const_ex]
        obtain t2 where "t2 \<ge> 0" "((v' \<oplus> t1) \<oplus> t2) \<in> [v \<oplus> t]\<^sub>\<R>" by (auto simp: cval_add_def)
        moreover have "(v' \<oplus> (t1 + t2)) = ((v' \<oplus> t1) \<oplus> t2)" by (auto simp: cval_add_def)
        moreover have "t1 + t2 \<ge> 0" using \<open>t2 \<ge> 0\<close> t1(1) by auto
        ultimately show ?thesis by metis
      qed
    qed
  } note intro_intv = this
  from regions_closed[OF less(2) R less(4,7)] less(2) obtain I' r' where R':
      "[v \<oplus> t]\<^sub>\<R> = region X I' r'" "valid_region X k I' r'"
  by auto
  with regions_closed'[OF less(2) R less(4,7)] assms(1) have
    R'2: "(v \<oplus> t) \<in> [v \<oplus> t]\<^sub>\<R>" "(v \<oplus> t) \<in> region X I' r'"
  by auto
  let ?R' = "region X I' r'"
  from less(2) R' have "?R' \<in> \<R>" by auto
  show ?case
  proof (cases "?R' = ?R")
    case True with less(3,5) R'(1) have "(v' \<oplus> 0) \<in> [v \<oplus> t]\<^sub>\<R>" by (auto simp: cval_add_def)
    then show ?thesis by auto
  next
    case False
    have "t > 0"
    proof (rule ccontr)
      assume "\<not> 0 < t"
      with R' \<open>t \<ge> 0\<close> have "[v]\<^sub>\<R> = ?R'" by (simp add: cval_add_def)
      with region_unique[OF less(2) less(4) R] \<open>?R' \<noteq> ?R\<close> show False by auto
    qed
    show ?thesis
    proof (cases "?C = {}")
      case True
      show ?thesis
      proof (cases "\<exists> x \<in> X. isConst (I x)")
        case False
        then have no_consts: "\<forall>x\<in>X. \<not>isConst (I x)" by auto
        from critical_empty_intro[OF this \<open>v \<in> ?R\<close> \<open>t \<ge> 0\<close> True] have "(v \<oplus> t) \<in> ?R" .
        from region_unique[OF less(2) this R] less(5) have "(v' \<oplus> 0) \<in> [v \<oplus> t]\<^sub>\<R>"
        by (auto simp: cval_add_def)
        then show ?thesis by blast
      next
        case True
        from const_dest[OF this \<open>t > 0\<close>] obtain t1 t2 I' r'
          where t1:  "t1 \<ge> 0" "t1 \<le> t" "(v \<oplus> t1) \<in> region X I' r'"
          and   t2:  "t2 \<ge> 0" "t2 \<le> t" "(v' \<oplus> t2) \<in> region X I' r'"
          and valid: "valid_region X k I' r'"
          and no_consts: "\<forall> x \<in> X. \<not> isConst (I' x)"
          and   C:   "?C = {x \<in> X. \<exists>c. I' x = Intv c \<and> real (c + 1) \<le> (v \<oplus> t1) x + (t - t1)}"
        by auto
        let ?v = "v \<oplus> t1"
        let ?t = "t - t1"
        let ?C' = "{x \<in> X. \<exists>c. I' x = Intv c \<and> real (c + 1) \<le> ?v x + ?t}"
        let ?R' = "region X I' r'"
        from C \<open>?C = {}\<close> have "?C' = {}" by blast
        from critical_empty_intro[OF no_consts t1(3) _ this] t1 have "(?v \<oplus> ?t) \<in> ?R'" by auto
        from region_unique[OF less(2) this] less(2) valid t2 show ?thesis
        by (auto simp: cval_add_def)
      qed
    next
      case False
      then obtain x c where x: "x \<in> X" "I x = Intv c" "v x + t \<ge> c + 1" by auto
      then have F: "\<not> (\<forall> x \<in> X. \<exists> c. I x = Greater c)" by force
      show ?thesis
      proof (cases "\<exists> x \<in> X. isConst (I x)")
        case False
        then have "\<forall>x\<in>X. \<not>isConst (I x)" by auto
        from intro_intv[OF \<open>v \<in> ?R\<close> \<open>v' \<in> ?R\<close> this x less(3,7,8)] show ?thesis by auto
      next
        case True
        then have "{x \<in> X. \<exists>c. I x = Const c} \<noteq> {}" by auto
        from const_dest[OF True \<open>t > 0\<close>] obtain t1 t2 I' r'
          where t1:  "t1 \<ge> 0" "t1 \<le> t" "(v \<oplus> t1) \<in> region X I' r'"
          and   t2:  "t2 \<ge> 0" "t2 \<le> t" "(v' \<oplus> t2) \<in> region X I' r'"
          and valid: "valid_region X k I' r'"
          and no_consts: "\<forall> x \<in> X. \<not> isConst (I' x)"
          and   C:   "?C = {x \<in> X. \<exists>c. I' x = Intv c \<and> real (c + 1) \<le> (v \<oplus> t1) x + (t - t1)}"
        by auto
        let ?v = "v \<oplus> t1"
        let ?t = "t - t1"
        let ?C' = "{x \<in> X. \<exists>c. I' x = Intv c \<and> real (c + 1) \<le> ?v x + ?t}"
        let ?R' = "region X I' r'"
        show ?thesis
        proof (cases "?C' = {}")
          case False
          with intro_intv[OF t1(3) t2(3) no_consts _ _ _ valid _ _ C] \<open>t < 1\<close> t1 obtain t' where
            "t' \<ge> 0" "((v' \<oplus> t2) \<oplus> t') \<in> [(v \<oplus> t)]\<^sub>\<R>"
          by (auto simp: cval_add_def)
          moreover have "((v' \<oplus> t2) \<oplus> t') = (v' \<oplus> (t2 + t'))" by (auto simp: cval_add_def)
          moreover have "t2 + t' \<ge> 0" using \<open>t' \<ge> 0\<close> \<open>t2 \<ge> 0\<close> by auto
          ultimately show ?thesis by metis
        next
          case True
          from critical_empty_intro[OF no_consts t1(3) _ this] t1 have "((v \<oplus> t1) \<oplus> ?t) \<in> ?R'" by auto
          from region_unique[OF less(2) this] less(2) valid t2 show ?thesis
          by (auto simp: cval_add_def)
        qed
      qed
    qed
  qed
qed

text \<open>
  Finally, we can put the two pieces together: for a non-negative shift @{term t}, we first shift
  @{term "floor t"} and then @{term "frac t"}.
\<close>

lemma set_of_regions:
  fixes X k
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "R \<in> \<R>" "v \<in> R" "R' \<in> Succ \<R> R" "finite X"
  shows "\<exists> t\<ge>0. [v \<oplus> t]\<^sub>\<R> = R'" using assms
proof -
  from assms(4) obtain v' t where v': "v' \<in> R" "R' \<in> \<R>" "0 \<le> t" "R' = [v' \<oplus> t]\<^sub>\<R>" by fastforce
  obtain t1 :: int where t1: "t1 = floor t" by auto
  with v'(3) have "t1 \<ge> 0" by auto
  from int_shift_equiv[OF v'(1) \<open>v \<in> R\<close> assms(2)[unfolded \<R>_def] this] \<R>_def
  have *: "(v \<oplus> t1) \<in> [v' \<oplus> t1]\<^sub>\<R>" by auto
  let ?v = "(v \<oplus> t1)"
  let ?t2 = "frac t"
  have frac: "0 \<le> ?t2" "?t2 < 1" by (auto simp: frac_lt_1)
  let ?R = "[v' \<oplus> t1]\<^sub>\<R>"
  from regions_closed[OF _ assms(2) v'(1)] \<open>t1 \<ge> 0\<close> \<R>_def have "?R \<in> \<R>" by auto
  with assms obtain I r where R: "?R = region X I r" "valid_region X k I r" by auto
  with * have v: "?v \<in> region X I r" by auto
  from R regions_closed'[OF _ assms(2) v'(1)] \<open>t1 \<ge> 0\<close> \<R>_def have "(v' \<oplus> t1) \<in> region X I r" by auto
  from set_of_regions_lt_1[OF R(2) this v assms(5) frac] \<R>_def obtain t2 where
    "t2 \<ge> 0" "(?v \<oplus> t2) \<in> [(v' \<oplus> t1) \<oplus> ?t2]\<^sub>\<R>"
  by auto
  moreover from t1 have "(v \<oplus> (t1 + t2)) = (?v \<oplus> t2)" "v' \<oplus> t = ((v' \<oplus> t1) \<oplus> ?t2)"
  by (auto simp: frac_def cval_add_def)
  ultimately have "(v \<oplus> (t1 + t2)) \<in> [v' \<oplus> t]\<^sub>\<R>" "t1 + t2 \<ge> 0" using \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> by auto
  with region_unique[OF _ this(1)] v'(2,4) \<R>_def show ?thesis by blast
qed


section \<open>Compability With Clock Constraints\<close>

definition ccval ("\<lbrace>_\<rbrace>" [100]) where "ccval cc \<equiv> {v. v \<turnstile> cc}"

definition ccompatible
where
  "ccompatible \<R> cc \<equiv> \<forall> R \<in> \<R>. R \<subseteq> ccval cc \<or> ccval cc \<inter> R = {}"

lemma ccompatible1:
  fixes X k fixes c :: real
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "c \<le> k x" "c \<in> \<nat>" "x \<in> X"
  shows "ccompatible \<R> (EQ x c)" using assms unfolding ccompatible_def
proof (auto, goal_cases)
  case A: (1 I r v u)
  from A(3) obtain d where d: "c = of_nat d" unfolding Nats_def by auto
  with A(8) have u: "u x = c" "u x = d" unfolding ccval_def by auto
  have "I x = Const d"
  proof (cases "I x", goal_cases)
    case (1 c')
    with A(4,9) have "u x = c'" by fastforce
    with 1 u show ?case by auto
  next
    case (2 c')
    with A(4,9) have "c' < u x" "u x < c' + 1" by fastforce+
    with 2 u show ?case by auto
  next
    case (3 c')
    with A(4,9) have "c' < u x" by fastforce
    moreover from 3 A(4,5) have "c' \<ge> k x" by fastforce
    ultimately show ?case using u A(2) by auto
  qed
  with A(4,6) d have "v x = c" by fastforce
  with A(3,5) have "v \<turnstile> EQ x c" by auto
  with A(7) show False unfolding ccval_def by auto
qed

lemma ccompatible2:
  fixes X k fixes c :: real
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "c \<le> k x" "c \<in> \<nat>" "x \<in> X"
  shows "ccompatible \<R> (LT x c)" using assms unfolding ccompatible_def
proof (auto, goal_cases)
  case A: (1 I r v u)
  from A(3) obtain d :: nat where d: "c = of_nat d" unfolding Nats_def by blast
  with A(8) have u: "u x < c" "u x < d" unfolding ccval_def by auto
  have "v x < c"
  proof (cases "I x", goal_cases)
    case (1 c')
    with A(4,6,9) have "u x = c'" "v x = c'" by fastforce+
    with u show "v x < c" by auto
  next
    case (2 c')
    with A(4,6,9) have B: "c' < u x" "u x < c' + 1" "c' < v x" "v x < c' + 1" by fastforce+
    with u A(3) have "c' + 1 \<le> d" by auto
    with d have "c' + 1 \<le> c" by auto
    with B u show "v x < c" by auto
  next
    case (3 c')
    with A(4,9) have "c' < u x" by fastforce
    moreover from 3 A(4,5) have "c' \<ge> k x" by fastforce
    ultimately show ?case using u A(2) by auto
  qed
  with A(4,6) have "v \<turnstile> LT x c" by auto
  with A(7) show False unfolding ccval_def by auto
qed

lemma ccompatible3:
  fixes X k fixes c :: real
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "c \<le> k x" "c \<in> \<nat>" "x \<in> X"
  shows "ccompatible \<R> (LE x c)" using assms unfolding ccompatible_def
proof (auto, goal_cases)
  case A: (1 I r v u)
  from A(3) obtain d :: nat where d: "c = of_nat d" unfolding Nats_def by blast
  with A(8) have u: "u x \<le> c" "u x \<le> d" unfolding ccval_def by auto
  have "v x \<le> c"
  proof (cases "I x", goal_cases)
    case (1 c') with A(4,6,9) u show ?case by fastforce
  next
    case (2 c')
    with A(4,6,9) have B: "c' < u x" "u x < c' + 1" "c' < v x" "v x < c' + 1" by fastforce+
    with u A(3) have "c' + 1 \<le> d" by auto
    with d u A(3) have "c' + 1 \<le> c" by auto
    with B u show "v x \<le> c" by auto
  next
    case (3 c')
    with A(4,9) have "c' < u x" by fastforce
    moreover from 3 A(4,5) have "c' \<ge> k x" by fastforce
    ultimately show ?case using u A(2) by auto
  qed
  with A(4,6) have "v \<turnstile> LE x c" by auto
  with A(7) show False unfolding ccval_def by auto
qed

lemma ccompatible4:
  fixes X k fixes c :: real
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "c \<le> k x" "c \<in> \<nat>" "x \<in> X"
  shows "ccompatible \<R> (GT x c)" using assms unfolding ccompatible_def
proof (auto, goal_cases)
  case A: (1 I r v u)
  from A(3) obtain d :: nat where d: "c = of_nat d" unfolding Nats_def by blast
  with A(8) have u: "u x > c" "u x > d" unfolding ccval_def by auto
  have "v x > c"
  proof (cases "I x", goal_cases)
    case (1 c') with A(4,6,9) u show ?case by fastforce
  next
    case (2 c')
    with A(4,6,9) have B: "c' < u x" "u x < c' + 1" "c' < v x" "v x < c' + 1" by fastforce+
    with d u have "c' \<ge> c" by auto
    with B u show "v x > c" by auto
  next
    case (3 c')
    with A(4,6) have "c' < v x" by fastforce
    moreover from 3 A(4,5) have "c' \<ge> k x" by fastforce
    ultimately show ?case using A(2) u(1) by auto
  qed
  with A(4,6) have "v \<turnstile> GT x c" by auto
  with A(7) show False unfolding ccval_def by auto
qed

lemma ccompatible5:
  fixes X k fixes c :: real
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "c \<le> k x" "c \<in> \<nat>" "x \<in> X"
  shows "ccompatible \<R> (GE x c)" using assms unfolding ccompatible_def
proof (auto, goal_cases)
  case A: (1 I r v u)
  from A(3) obtain d :: nat where d: "c = of_nat d" unfolding Nats_def by blast
  with A(8) have u: "u x \<ge> c" "u x \<ge> d" unfolding ccval_def by auto
  have "v x \<ge> c"
  proof (cases "I x", goal_cases)
    case (1 c') with A(4,6,9) u show ?case by fastforce
  next
    case (2 c')
    with A(4,6,9) have B: "c' < u x" "u x < c' + 1" "c' < v x" "v x < c' + 1" by fastforce+
    with d u have "c' \<ge> c" by auto
    with B u show "v x \<ge> c" by auto
  next
    case (3 c')
    with A(4,6) have "c' < v x" by fastforce
    moreover from 3 A(4,5) have "c' \<ge> k x" by fastforce
    ultimately show ?case using A(2) u(1) by auto
  qed
  with A(4,6) have "v \<turnstile> GE x c" by auto
  with A(7) show False unfolding ccval_def by auto
qed

lemma ccompatible:
  fixes X k fixes c :: nat
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "\<forall>(x,m) \<in> collect_clock_pairs cc. m \<le> k x \<and> x \<in> X \<and> m \<in> \<nat>"
  shows "ccompatible \<R> cc" using assms
proof (induction cc)
  case (AND cc1 cc2)
  then have IH: "ccompatible \<R> cc1" "ccompatible \<R> cc2" by auto
  moreover have "\<lbrace>AND cc1 cc2\<rbrace> = \<lbrace>cc1\<rbrace> \<inter> \<lbrace>cc2\<rbrace>" unfolding ccval_def by auto
  ultimately show ?case unfolding ccompatible_def by auto
qed (auto intro: ccompatible1 ccompatible2 ccompatible3 ccompatible4 ccompatible5)


section \<open>Compability with Resets\<close>

definition region_set
where
  "region_set R x c = {v(x := c) | v. v \<in> R}"

lemma region_set_id:
  fixes X k
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "R \<in> \<R>" "v \<in> R" "finite X" "0 \<le> c" "c \<le> k x" "x \<in> X"
  shows "[v(x := c)]\<^sub>\<R> = region_set R x c" "[v(x := c)]\<^sub>\<R> \<in> \<R>" "v(x := c) \<in> [v(x := c)]\<^sub>\<R>"
proof -
  from assms obtain I r where R: "R = region X I r" "valid_region X k I r" "v \<in> region X I r" by auto
  let ?I = "\<lambda> y. if x = y then Const c else I y"
  let ?r = "{(y,z) \<in> r. x \<noteq> y \<and> x \<noteq> z}"
  let ?X\<^sub>0 = "{x \<in> X. \<exists> c. I x = Intv c}"
  let ?X\<^sub>0' = "{x \<in> X. \<exists> c. ?I x = Intv c}"

  from R(2) have refl: "refl_on ?X\<^sub>0 r" and trans: "trans r" and total: "total_on ?X\<^sub>0 r" by auto

  have valid: "valid_region X k ?I ?r"
  proof
    show "?X\<^sub>0 - {x} = ?X\<^sub>0'" by auto
  next
    from refl show "refl_on (?X\<^sub>0 - {x}) ?r" unfolding refl_on_def by auto
  next
    from trans show "trans ?r" unfolding trans_def by blast
  next
    from total show "total_on (?X\<^sub>0 - {x}) ?r" unfolding total_on_def by auto
  next
    from R(2) have "\<forall> x \<in> X. valid_intv (k x) (I x)" by auto
    with \<open>c \<le> k x\<close> show "\<forall> x \<in> X. valid_intv (k x) (?I x)" by auto
  qed

  { fix v assume v: "v \<in> region_set R x c"
    with R(1) obtain v' where v': "v' \<in> region X I r" "v = v'(x := c)" unfolding region_set_def by auto
    have "v \<in> region X ?I ?r"
    proof (standard, goal_cases)
      case 1
      from v' \<open>0 \<le> c\<close> show ?case by auto
    next
      case 2
      from v' show ?case
      proof (auto, goal_cases)
        case (1 y)
        then have "intv_elem y v' (I y)" by auto
        with \<open>x \<noteq> y\<close> show "intv_elem y (v'(x := c)) (I y)" by (cases "I y") auto
      qed
    next
      show "?X\<^sub>0 - {x} = ?X\<^sub>0'" by auto
    next
      from v' show "\<forall> y \<in> ?X\<^sub>0 - {x}. \<forall> z \<in> ?X\<^sub>0 - {x}. (y,z) \<in> ?r \<longleftrightarrow> frac (v y) \<le> frac (v z)" by auto
    qed
  } moreover
  { fix v assume v: "v \<in> region X ?I ?r"
    have "\<exists> c. v(x := c) \<in> region X I r"
    proof (cases "I x")
      case (Const c)
      from R(2) have "c \<ge> 0" by auto
      let ?v = "v(x := c)"
      have "?v \<in> region X I r"
      proof (standard, goal_cases)
        case 1
        from \<open>c\<ge>0\<close> v show ?case by auto
      next
        case 2
        show ?case
        proof (auto, goal_cases)
          case (1 y)
          with v have "intv_elem y v (?I y)" by fast
          with Const show "intv_elem y ?v (I y)" by (cases "x = y", auto) (cases "I y", auto)
        qed
      next
        from Const show "?X\<^sub>0' = ?X\<^sub>0" by auto
        with refl have "r \<subseteq> ?X\<^sub>0' \<times> ?X\<^sub>0'" unfolding refl_on_def by auto
        then have r: "?r = r" by auto
        from v have "\<forall> y \<in> ?X\<^sub>0'. \<forall> z \<in> ?X\<^sub>0'. (y,z) \<in> ?r \<longleftrightarrow> frac (v y) \<le> frac (v z)" by fastforce
        with r show "\<forall> y \<in> ?X\<^sub>0'. \<forall> z \<in> ?X\<^sub>0'. (y,z) \<in> r \<longleftrightarrow> frac (?v y) \<le> frac (?v z)"
        by auto
      qed
      then show ?thesis by auto
    next
      case (Greater c)
      from R(2) have "c \<ge> 0" by auto
      let ?v = "v(x := c + 1)"
      have "?v \<in> region X I r"
      proof (standard, goal_cases)
        case 1
        from \<open>c\<ge>0\<close> v show ?case by auto
      next
        case 2
        show ?case
        proof (standard, goal_cases)
          case (1 y)
          with v have "intv_elem y v (?I y)" by fast
          with Greater show "intv_elem y ?v (I y)" by (cases "x = y", auto) (cases "I y", auto)
        qed
      next
        from Greater show "?X\<^sub>0' = ?X\<^sub>0" by auto
        with refl have "r \<subseteq> ?X\<^sub>0' \<times> ?X\<^sub>0'" unfolding refl_on_def by auto
        then have r: "?r = r" by auto
        from v have "\<forall> y \<in> ?X\<^sub>0'. \<forall> z \<in> ?X\<^sub>0'. (y,z) \<in> ?r \<longleftrightarrow> frac (v y) \<le> frac (v z)" by fastforce
        with r show "\<forall> y \<in> ?X\<^sub>0'. \<forall> z \<in> ?X\<^sub>0'. (y,z) \<in> r \<longleftrightarrow> frac (?v y) \<le> frac (?v z)"
        by auto
      qed
      then show ?thesis by auto
    next
      case (Intv c)
      from R(2) have "c \<ge> 0" by auto
      let ?L = "{frac (v y) | y. y \<in> ?X\<^sub>0 \<and> x \<noteq> y \<and> (y,x) \<in> r}"
      let ?U = "{frac (v y) | y. y \<in> ?X\<^sub>0 \<and> x \<noteq> y \<and> (x,y) \<in> r}"
      let ?l = "if ?L \<noteq> {} then c + Max ?L else if ?U \<noteq> {} then c else c + 0.5"
      let ?u = "if ?U \<noteq> {} then c + Min ?U else if ?L \<noteq> {} then c + 1 else c + 0.5"
      from \<open>finite X\<close> have fin: "finite ?L" "finite ?U" by auto
      { fix y assume y: "y \<in> ?X\<^sub>0" "x \<noteq> y" "(y, x) \<in> r"
        then have L: "frac (v y) \<in> ?L" by auto
        with Max_in[OF fin(1)] have In: "Max ?L \<in> ?L" by auto
        then have "frac (Max ?L) = (Max ?L)" using frac_idempotent by fastforce
        from Max_ge[OF fin(1) L] have "frac (v y) \<le> Max ?L" .
        also have "\<dots> = frac (Max ?L)" using In frac_idempotent[symmetric] by fastforce
        also have "\<dots> = frac (c + Max ?L)" by (auto simp: frac_nat_add_id)
        finally have "frac (v y) \<le> frac ?l" using L by auto
      } note L_bound = this
      { fix y assume y: "y \<in> ?X\<^sub>0" "x \<noteq> y" "(x,y) \<in> r"
        then have U: "frac (v y) \<in> ?U" by auto
        with Min_in[OF fin(2)] have In: "Min ?U \<in> ?U" by auto
        then have "frac (Min ?U) = (Min ?U)" using frac_idempotent by fastforce
        have "frac (c + Min ?U) = frac (Min ?U)" by (auto simp: frac_nat_add_id)
        also have "\<dots> = Min ?U" using In frac_idempotent by fastforce
        also from Min_le[OF fin(2) U] have "Min ?U \<le> frac (v y)" .
        finally have "frac ?u \<le> frac (v y)" using U by auto
      } note U_bound = this
      { assume "?L \<noteq> {}"
        from Max_in[OF fin(1) this] obtain l d where l:
          "Max ?L = frac (v l)" "l \<in> X" "x \<noteq> l" "I l = Intv d"
        by auto
        with v have "d < v l" "v l < d + 1" by fastforce+
        with nat_intv_frac_gt0[OF this] frac_lt_1 l(1) have "0 < Max ?L" "Max ?L < 1" by auto
        then have "c < c + Max ?L" "c + Max ?L < c + 1" by simp+
      } note L_intv = this
      { assume "?U \<noteq> {}"
        from Min_in[OF fin(2) this] obtain u d where u:
          "Min ?U = frac (v u)" "u\<in> X" "x \<noteq> u" "I u = Intv d"
        by auto
        with v have "d < v u" "v u < d + 1" by fastforce+
        with nat_intv_frac_gt0[OF this] frac_lt_1 u(1) have "0 < Min ?U" "Min ?U < 1" by auto
        then have "c < c + Min ?U" "c + Min ?U < c + 1" by simp+
      } note U_intv = this
      have l_bound: "c \<le> ?l"
      proof (cases "?L = {}")
        case True
        note T = this
        show ?thesis
        proof (cases "?U = {}")
          case True
          with T show ?thesis by simp
        next
          case False
          with U_intv T show ?thesis by simp
        qed
      next
        case False
        with L_intv show ?thesis by simp
      qed
      have l_bound': "c < ?u"
      proof (cases "?L = {}")
        case True
        note T = this
        show ?thesis
        proof (cases "?U = {}")
          case True
          with T show ?thesis by simp
        next
          case False
          with U_intv T show ?thesis by simp
        qed
      next
        case False
        with U_intv show ?thesis by simp
      qed
      have u_bound: "?u \<le> c + 1"
      proof (cases "?U = {}")
        case True
        note T = this
        show ?thesis
        proof (cases "?L = {}")
          case True
          with T show ?thesis by simp
        next
          case False
          with L_intv T show ?thesis by simp
        qed
      next
        case False
        with U_intv show ?thesis by simp
      qed
      have u_bound': "?l < c + 1"
      proof (cases "?U = {}")
        case True
        note T = this
        show ?thesis
        proof (cases "?L = {}")
          case True
          with T show ?thesis by simp
        next
          case False
          with L_intv T show ?thesis by simp
        qed
      next
        case False
        with L_intv show ?thesis by simp
      qed
      have frac_c: "frac c = 0" "frac (c+1) = 0" by auto
      have l_u: "?l \<le> ?u"
      proof (cases "?L = {}")
        case True
        note T = this
        show ?thesis
        proof (cases "?U = {}")
          case True
          with T show ?thesis by simp
        next
          case False
          with T show ?thesis using Min_in[OF fin(2) False] by (auto simp: frac_c)
        qed
      next
        case False
        with Max_in[OF fin(1) this] have l: "?l = c + Max ?L" "Max ?L \<in> ?L" by auto
        note F = False
        from l(1) have *: "Max ?L < 1" using False L_intv(2) by linarith
        show ?thesis
        proof (cases "?U = {}")
          case True
          with F l * show ?thesis by simp
        next
          case False
          from Min_in[OF fin(2) this] l(2) obtain l u where l_u:
            "Max ?L = frac (v l)" "Min ?U = frac (v u)" "l \<in> ?X\<^sub>0" "u \<in> ?X\<^sub>0" "(l,x) \<in> r" "(x,u) \<in> r"
            "x \<noteq> l" "x \<noteq> u"
          by auto
          from trans l_u(5-) have "(l,u) \<in> ?r" unfolding trans_def by blast
          with l_u(1-4) v have *: "Max ?L \<le> Min ?U" by fastforce
          with l_u(1,2) have "frac (Max ?L) \<le> frac (Min ?U)" by (simp add: frac_idempotent)
          with frac_nat_add_id l(1) False have "frac ?l \<le> frac ?u" by simp
          with l(1) * False show ?thesis by simp
        qed
      qed
      obtain d where d: "d = (?l + ?u) / 2" by blast
      with l_u have d2: "?l \<le> d" "d \<le> ?u" by simp+
      from d l_bound l_bound' u_bound u_bound' have d3: "c < d" "d < c + 1" "d \<ge> 0" by simp+
      have "floor ?l = c"
      proof (cases "?L = {}")
        case False
        from L_intv[OF False] have "0 \<le> Max ?L" "Max ?L < 1" by auto
        from floor_nat_add_id[OF this] False show ?thesis by simp
      next
        case True
        note T = this
        show ?thesis
        proof (cases "?U = {}")
          case True
          with T show ?thesis by (simp)
        next
          case False
          from U_intv[OF False] have "0 \<le> Min ?U" "Min ?U < 1" by auto
          from floor_nat_add_id[OF this] T False show ?thesis by simp
        qed
      qed
      have floor_u: "floor ?u = (if ?U = {} \<and> ?L \<noteq> {} then c + 1 else c)"
      proof (cases "?U = {}")
        case False
        from U_intv[OF False] have "0 \<le> Min ?U" "Min ?U < 1" by auto
        from floor_nat_add_id[OF this] False show ?thesis by simp
      next
        case True
        note T = this
        show ?thesis
        proof (cases "?L = {}")
          case True
          with T show ?thesis by (simp)
        next
          case False
          from L_intv[OF False] have "0 \<le> Max ?L" "Max ?L < 1" by auto
          from floor_nat_add_id[OF this] T False show ?thesis by (auto)
        qed
      qed
      { assume "?L \<noteq> {}" "?U \<noteq> {}"
        from Max_in[OF fin(1) \<open>?L \<noteq> {}\<close>] obtain w where w:
          "w \<in> ?X\<^sub>0" "x \<noteq> w" "(w,x) \<in> r" "Max ?L = frac (v w)"
        by auto
        from Min_in[OF fin(2) \<open>?U \<noteq> {}\<close>] obtain z where z:
          "z \<in> ?X\<^sub>0" "x \<noteq> z" "(x,z) \<in> r" "Min ?U = frac (v z)"
        by auto
        from w z trans have "(w,z) \<in> r" unfolding trans_def by blast
        with v w z have "Max ?L \<le> Min ?U" by fastforce
      } note l_le_u = this
      { fix y assume y: "y \<in> ?X\<^sub>0" "x \<noteq> y"
        from total y \<open>x \<in> X\<close> Intv have total: "(x,y) \<in> r \<or> (y,x) \<in> r" unfolding total_on_def by auto
        have "frac (v y) = frac d \<longleftrightarrow> (y,x) \<in> r \<and> (x,y) \<in> r"
        proof safe
          assume A: "(y,x) \<in> r" "(x,y) \<in> r"
          from L_bound[OF y A(1)] U_bound[OF y A(2)] have *:
            "frac (v y) \<le> frac ?l" "frac ?u \<le> frac (v y)"
          by auto
          from A y have **: "?L \<noteq> {}" "?U \<noteq> {}" by auto
          with L_intv[OF this(1)] U_intv[OF this(2)] have "frac ?l = Max ?L" "frac ?u = Min ?U"
          by (auto simp: frac_nat_add_id frac_eq)
          with * ** l_le_u have "frac ?l = frac ?u" "frac (v y) = frac ?l" by auto
          with d have "d = ((floor ?l + floor ?u) + (frac (v y) + frac (v y))) / 2"
          unfolding frac_def by auto
          also have "\<dots> = c + frac (v y)" using \<open>floor ?l = c\<close> floor_u \<open>?U \<noteq> {}\<close> by auto
          finally show "frac (v y) = frac d" using frac_nat_add_id frac_idempotent by metis
        next
          assume A: "frac (v y) = frac d"
          show "(y, x) \<in> r"
          proof (rule ccontr)
            assume B: "(y,x) \<notin> r"
            with total have B': "(x,y) \<in> r" by auto
            from U_bound[OF y this] have u_y:"frac ?u \<le> frac (v y)" by auto
            from y B' have U: "?U \<noteq> {}" and "frac (v y) \<in> ?U" by auto
            then have u: "frac ?u = Min ?U" using Min_in[OF fin(2) \<open>?U \<noteq> {}\<close>]
            by (auto simp: frac_nat_add_id frac_idempotent)
            show False
            proof (cases "?L = {}")
              case True
              from U_intv[OF U] have "0 < Min ?U" "Min ?U < 1" by auto
              then have *: "frac (Min ?U / 2) = Min ?U / 2" unfolding frac_eq by simp
              from d U True have "d = ((c + c) + Min ?U) / 2" by auto
              also have "\<dots> = c + Min ?U / 2" by simp
              finally have "frac d = Min ?U / 2" using * by (simp add: frac_nat_add_id)
              also have "\<dots> < Min ?U" using \<open>0 < Min ?U\<close> by auto
              finally have "frac d < frac ?u" using u by auto
              with u_y A show False by auto
            next
              case False
              then have l:  "?l = c + Max ?L" by simp
              from Max_in[OF fin(1) \<open>?L \<noteq> {}\<close>]
              obtain w where w:
                "w \<in> ?X\<^sub>0" "x \<noteq> w" "(w,x) \<in> r" "Max ?L = frac (v w)"
              by auto
              with \<open>(y,x) \<notin> r\<close> trans have **: "(y,w) \<notin> r" unfolding trans_def by blast
              from Min_in[OF fin(2) \<open>?U \<noteq> {}\<close>] Max_in[OF fin(1) \<open>?L \<noteq> {}\<close>] frac_lt_1
              have "0 \<le> Max ?L" "Max ?L < 1" "0 \<le> Min ?U" "Min ?U < 1" by auto
              then have "0 \<le> (Max ?L + Min ?U) / 2" "(Max ?L + Min ?U) / 2 < 1" by auto
              then have ***: "frac ((Max ?L + Min ?U) / 2) = (Max ?L + Min ?U) / 2" unfolding frac_eq ..
              from y w have "y \<in> ?X\<^sub>0'" "w \<in> ?X\<^sub>0'" by auto
              with v ** have lt: "frac (v y) > frac (v w)" by fastforce
              from d U l have "d = ((c + c) + (Max ?L + Min ?U))/2" by auto
              also have "\<dots> = c + (Max ?L + Min ?U) / 2" by simp
              finally have "frac d = frac ((Max ?L + Min ?U) / 2)" by (simp add: frac_nat_add_id)
              also have "\<dots> = (Max ?L + Min ?U) / 2" using *** by simp
              also have "\<dots> < (frac (v y) + Min ?U) / 2" using lt w(4) by auto
              also have "\<dots> \<le> frac (v y)" using Min_le[OF fin(2) \<open>frac (v y) \<in> ?U\<close>] by auto
              finally show False using A by auto
            qed
          qed
        next
          assume A: "frac (v y) = frac d"
          show "(x, y) \<in> r"
          proof (rule ccontr)
            assume B: "(x,y) \<notin> r"
            with total have B': "(y,x) \<in> r" by auto
            from L_bound[OF y this] have l_y:"frac ?l \<ge> frac (v y)" by auto
            from y B' have L: "?L \<noteq> {}" and "frac (v y) \<in> ?L" by auto
            then have l: "frac ?l = Max ?L" using Max_in[OF fin(1) \<open>?L \<noteq> {}\<close>]
            by (auto simp: frac_nat_add_id frac_idempotent)
            show False
            proof (cases "?U = {}")
              case True
              from L_intv[OF L] have *: "0 < Max ?L" "Max ?L < 1" by auto
              from d L True have "d = ((c + c) + (1 + Max ?L)) / 2" by auto
              also have "\<dots> = c + (1 + Max ?L) / 2" by simp
              finally have "frac d = frac ((1 + Max ?L) / 2)" by (simp add: frac_nat_add_id)
              also have "\<dots> = (1 + Max ?L) / 2" using * unfolding frac_eq by auto
              also have "\<dots> > Max ?L" using * by auto
              finally have "frac d > frac ?l" using l by auto
              with l_y A show False by auto
            next
              case False
              then have u: "?u = c + Min ?U" by simp
              from Min_in[OF fin(2) \<open>?U \<noteq> {}\<close>]
              obtain w where w:
                "w \<in> ?X\<^sub>0" "x \<noteq> w" "(x,w) \<in> r" "Min ?U = frac (v w)"
              by auto
              with \<open>(x,y) \<notin> r\<close> trans have **: "(w,y) \<notin> r" unfolding trans_def by blast
              from Min_in[OF fin(2) \<open>?U \<noteq> {}\<close>] Max_in[OF fin(1) \<open>?L \<noteq> {}\<close>] frac_lt_1
              have "0 \<le> Max ?L" "Max ?L < 1" "0 \<le> Min ?U" "Min ?U < 1" by auto
              then have "0 \<le> (Max ?L + Min ?U) / 2" "(Max ?L + Min ?U) / 2 < 1" by auto
              then have ***: "frac ((Max ?L + Min ?U) / 2) = (Max ?L + Min ?U) / 2" unfolding frac_eq ..
              from y w have "y \<in> ?X\<^sub>0'" "w \<in> ?X\<^sub>0'" by auto
              with v ** have lt: "frac (v y) < frac (v w)" by fastforce
              from d L u have "d = ((c + c) + (Max ?L + Min ?U))/2" by auto
              also have "\<dots> = c + (Max ?L + Min ?U) / 2" by simp
              finally have "frac d = frac ((Max ?L + Min ?U) / 2)" by (simp add: frac_nat_add_id)
              also have "\<dots> = (Max ?L + Min ?U) / 2" using *** by simp
              also have "\<dots> > (Max ?L + frac (v y)) / 2" using lt w(4) by auto
              finally have "frac d > frac (v y)" using Max_ge[OF fin(1) \<open>frac (v y) \<in> ?L\<close>] by auto
              then show False using A by auto
            qed
          qed
        qed
      } note d_frac_equiv = this
      have frac_l: "frac ?l \<le> frac d"
      proof (cases "?L = {}")
        case True
        note T = this
        show ?thesis
        proof (cases "?U = {}")
          case True
          with T have "?l = ?u" by auto
          with d have "d = ?l" by auto
          then show ?thesis by auto
        next
          case False
          with T have "frac ?l = 0" by auto
          moreover have "frac d \<ge> 0" by auto
          ultimately show ?thesis by linarith
        qed
      next
        case False
        note F = this
        then have l: "?l = c + Max ?L" "frac ?l = Max ?L" using Max_in[OF fin(1) \<open>?L \<noteq> {}\<close>]
        by (auto simp: frac_nat_add_id frac_idempotent)
        from L_intv[OF F] have *: "0 < Max ?L" "Max ?L < 1" by auto
        show ?thesis
        proof (cases "?U = {}")
          case True
          from True F have "?u = c + 1" by auto
          with l d have "d = ((c + c) + (Max ?L + 1)) / 2" by auto
          also have "\<dots> = c + (1 + Max ?L) / 2" by simp
          finally have "frac d = frac ((1 + Max ?L) / 2)" by (simp add: frac_nat_add_id)
          also have "\<dots> = (1 + Max ?L) / 2" using * unfolding frac_eq by auto
          also have "\<dots> > Max ?L" using * by auto
          finally show "frac d \<ge> frac ?l" using l by auto
        next
          case False
          then have u: "?u = c + Min ?U" "frac ?u = Min ?U" using Min_in[OF fin(2) False]
          by (auto simp: frac_nat_add_id frac_idempotent)
          from U_intv[OF False] have **: "0 < Min ?U" "Min ?U < 1" by auto
          from l u d have "d = ((c + c) + (Max ?L + Min ?U)) / 2" by auto
          also have "\<dots> = c + (Max ?L + Min ?U) / 2" by simp
          finally have "frac d = frac ((Max ?L + Min ?U) / 2)" by (simp add: frac_nat_add_id)
          also have "\<dots> = (Max ?L + Min ?U) / 2" using * ** unfolding frac_eq by auto
          also have "\<dots> \<ge> Max ?L" using l_le_u[OF F False] by auto
          finally show ?thesis using l by auto
        qed
      qed
      have frac_u: "?U \<noteq> {} \<or> ?L = {} \<longrightarrow> frac d \<le> frac ?u"
      proof (cases "?U = {}")
        case True
        note T = this
        show ?thesis
        proof (cases "?L = {}")
          case True
          with T have "?l = ?u" by auto
          with d have "d = ?u" by auto
          then show ?thesis by auto
        next
          case False
          with T show ?thesis by auto
        qed
      next
        case False
        note F = this
        then have u: "?u = c + Min ?U" "frac ?u = Min ?U" using Min_in[OF fin(2) \<open>?U \<noteq> {}\<close>]
        by (auto simp: frac_nat_add_id frac_idempotent)
        from U_intv[OF F] have *: "0 < Min ?U" "Min ?U < 1" by auto
        show ?thesis
        proof (cases "?L = {}")
          case True
          from True F have "?l = c" by auto
          with u d have "d = ((c + c) + Min ?U) / 2" by auto
          also have "\<dots> = c + Min ?U / 2" by simp
          finally have "frac d = frac (Min ?U / 2)" by (simp add: frac_nat_add_id)
          also have "\<dots> = Min ?U / 2" unfolding frac_eq using * by auto
          also have "\<dots> \<le> Min ?U" using \<open>0 < Min ?U\<close> by auto
          finally have "frac d \<le> frac ?u" using u by auto
          then show ?thesis by auto
        next
          case False
          then have l: "?l = c + Max ?L" "frac ?l = Max ?L" using Max_in[OF fin(1) False]
          by (auto simp: frac_nat_add_id frac_idempotent)
          from L_intv[OF False] have **: "0 < Max ?L" "Max ?L < 1" by auto
          from l u d have "d = ((c + c) + (Max ?L + Min ?U)) / 2" by auto
          also have "\<dots> = c + (Max ?L + Min ?U) / 2" by simp
          finally have "frac d = frac ((Max ?L + Min ?U) / 2)" by (simp add: frac_nat_add_id)
          also have "\<dots> = (Max ?L + Min ?U) / 2" using * ** unfolding frac_eq by auto
          also have "\<dots> \<le> Min ?U" using l_le_u[OF False F] by auto
          finally show ?thesis using u by auto
        qed
      qed
      have "\<forall> y \<in> ?X\<^sub>0 - {x}. (y,x) \<in> r \<longleftrightarrow> frac (v y) \<le> frac d"
      proof (safe, goal_cases)
        case (1 y k)
        with L_bound[of y] frac_l show ?case by auto
      next
        case (2 y k)
        show ?case
        proof (rule ccontr, goal_cases)
          case 1
          with total 2 \<open>x \<in> X\<close> Intv have "(x,y) \<in> r" unfolding total_on_def by auto
          with 2 U_bound[of y] have "?U \<noteq> {}" "frac ?u \<le> frac (v y)" by auto
          with frac_u have "frac d \<le> frac (v y)" by auto
          with 2 d_frac_equiv 1 show False by auto
        qed
      qed
      moreover have "\<forall> y \<in> ?X\<^sub>0 - {x}. (x,y) \<in> r \<longleftrightarrow> frac d \<le> frac (v y)"
      proof (safe, goal_cases)
        case (1 y k)
        then have "?U \<noteq> {}" by auto
        with 1 U_bound[of y] frac_u show ?case by auto
      next
        case (2 y k)
        show ?case
        proof (rule ccontr, goal_cases)
          case 1
          with total 2 \<open>x \<in> X\<close> Intv have "(y,x) \<in> r" unfolding total_on_def by auto
          with 2 L_bound[of y] have "frac (v y) \<le> frac ?l" by auto
          with frac_l have "frac (v y) \<le> frac d" by auto
          with 2 d_frac_equiv 1 show False by auto
        qed
      qed
      ultimately have d:
        "c < d" "d < c + 1" "\<forall> y \<in> ?X\<^sub>0 - {x}. (y,x) \<in> r \<longleftrightarrow> frac (v y) \<le> frac d"
        "\<forall> y \<in> ?X\<^sub>0 - {x}. (x,y) \<in> r \<longleftrightarrow> frac d \<le> frac (v y)"
      using d3 by auto
      let ?v = "v(x := d)"
      have "?v \<in> region X I r"
      proof (standard, goal_cases)
        case 1
        from \<open>d\<ge>0\<close> v show ?case by auto
      next
        case 2
        show ?case
        proof (safe, goal_cases)
          case (1 y)
          with v have "intv_elem y v (?I y)" by fast
          with Intv d(1,2) show "intv_elem y ?v (I y)" by (cases "x = y", auto) (cases "I y", auto)
        qed
      next
        from \<open>x \<in> X\<close> Intv show "?X\<^sub>0' \<union> {x} = ?X\<^sub>0" by auto
        with refl have "r \<subseteq> (?X\<^sub>0' \<union> {x}) \<times> (?X\<^sub>0' \<union> {x})" unfolding refl_on_def by auto
        have "\<forall> x \<in> ?X\<^sub>0'. \<forall> y \<in> ?X\<^sub>0'. (x,y) \<in> r \<longleftrightarrow> (x,y) \<in> ?r" by auto
        with v have "\<forall> x \<in> ?X\<^sub>0'. \<forall> y \<in> ?X\<^sub>0'. (x,y) \<in> r \<longleftrightarrow> frac (v x) \<le> frac (v y)" by fastforce
        then have "\<forall> x \<in> ?X\<^sub>0'. \<forall> y \<in> ?X\<^sub>0'. (x,y) \<in> r \<longleftrightarrow> frac (?v x) \<le> frac (?v y)" by auto
        with d(3,4) show "\<forall> y \<in> ?X\<^sub>0' \<union> {x}. \<forall> z \<in> ?X\<^sub>0' \<union> {x}. (y,z) \<in> r \<longleftrightarrow> frac (?v y) \<le> frac (?v z)"
        proof (auto, goal_cases)
          case 1
          from refl \<open>x \<in> X\<close> Intv show ?case by (auto simp: refl_on_def)
        qed
      qed
      then show ?thesis by auto
    qed
    then obtain d where "v(x := d) \<in> R" using R by auto
    then have "(v(x := d))(x := c) \<in> region_set R x c" unfolding region_set_def by blast
    moreover from v \<open>x \<in> X\<close> have "(v(x := d))(x := c) = v" by fastforce
    ultimately have "v \<in> region_set R x c" by simp
  }

  ultimately have "region_set R x c = region X ?I ?r" by blast
  with valid \<R>_def have *: "region_set R x c \<in> \<R>" by auto
  moreover from assms have **: "v (x := c) \<in> region_set R x c" unfolding region_set_def by auto
  ultimately show "[v(x := c)]\<^sub>\<R> = region_set R x c" "[v(x := c)]\<^sub>\<R> \<in> \<R>" "v(x := c) \<in> [v(x := c)]\<^sub>\<R>"
  using region_unique[OF _ ** *] \<R>_def by auto
qed

definition region_set'
where
  "region_set' R r c = {[r \<rightarrow> c]v | v. v \<in> R}"

lemma region_set'_id:
  fixes X k and c :: nat
  defines "\<R> \<equiv> {region X I r |I r. valid_region X k I r}"
  assumes "R \<in> \<R>" "v \<in> R" "finite X" "0 \<le> c" "\<forall> x \<in> set r. c \<le> k x" "set r \<subseteq> X"
  shows "[[r \<rightarrow> c]v]\<^sub>\<R> = region_set' R r c \<and> [[r \<rightarrow> c]v]\<^sub>\<R> \<in> \<R> \<and> [r \<rightarrow> c]v \<in> [[r \<rightarrow> c]v]\<^sub>\<R>" using assms
proof (induction r)
  case Nil
  from regions_closed[OF _ Nil(2,3)] regions_closed'[OF _ Nil(2,3)] region_unique[OF _ Nil(3,2)] Nil(1)
  have "[v]\<^sub>\<R> = R" "[v \<oplus> 0]\<^sub>\<R> \<in> \<R>" "(v \<oplus> 0) \<in> [v \<oplus> 0]\<^sub>\<R>" by auto
  then show ?case unfolding region_set'_def cval_add_def by simp
next
  case (Cons x xs)
  then have "[[xs\<rightarrow>c]v]\<^sub>\<R> = region_set' R xs c" "[[xs\<rightarrow>c]v]\<^sub>\<R> \<in> \<R>" "[xs\<rightarrow>c]v \<in> [[xs\<rightarrow>c]v]\<^sub>\<R>" by force+
  note IH = this[unfolded \<R>_def]
  let ?v = "([xs\<rightarrow>c]v)(x := c)"
  from region_set_id[OF IH(2,3) \<open>finite X\<close> \<open>c \<ge> 0\<close>, of x] \<R>_def Cons.prems(5,6)
  have "[?v]\<^sub>\<R> = region_set ([[xs\<rightarrow>real c]v]\<^sub>\<R>) x c" "[?v]\<^sub>\<R> \<in> \<R>" "?v \<in> [?v]\<^sub>\<R>" by auto
  moreover have "region_set' R (x # xs) (real c) = region_set ([[xs\<rightarrow>real c]v]\<^sub>\<R>) x c"
  unfolding region_set_def region_set'_def
  proof (safe, goal_cases)
    case (1 y u)
    let ?u = "[xs\<rightarrow>real c]u"
    have "[x # xs\<rightarrow>real c]u = ?u(x := real c)" by auto
    moreover from IH(1) 1 have "?u \<in> [[xs\<rightarrow>real c]v]\<^sub>\<R>" unfolding \<R>_def region_set'_def by auto
    ultimately show ?case by auto
  next
    case (2 y u)
    with IH(1)[unfolded region_set'_def \<R>_def[symmetric]] show ?case by auto
  qed
  moreover have "[x # xs\<rightarrow>real c]v = ?v" by simp
  ultimately show ?case by presburger
qed

section \<open>A Semantics Based on Regions\<close>

subsection \<open>Single step\<close>

inductive step_r ::
  "('a, 'c, t, 's) ta \<Rightarrow> ('c, t) zone set \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_,_ \<turnstile> \<langle>_, _\<rangle> \<leadsto> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  step_t_r:
  "\<lbrakk>\<R> = {region X I r |I r. valid_region X k I r}; valid_abstraction A X k; R \<in> \<R>; R' \<in> Succ \<R> R;
    R \<subseteq> \<lbrace>inv_of A l\<rbrace>; R' \<subseteq> \<lbrace>inv_of A l\<rbrace>\<rbrakk> \<Longrightarrow> A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto> \<langle>l,R'\<rangle>" |
  step_a_r:
  "\<lbrakk>\<R> = {region X I r |I r. valid_region X k I r}; valid_abstraction A X k; A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'; R \<in> \<R>\<rbrakk>
    \<Longrightarrow> A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto> \<langle>l',region_set' (R \<inter> {u. u \<turnstile> g}) r 0 \<inter> {u. u \<turnstile> inv_of A l'}\<rangle>"

inductive_cases[elim!]: "A,\<R> \<turnstile> \<langle>l, u\<rangle> \<leadsto> \<langle>l', u'\<rangle>"

declare step_r.intros[intro]

lemma region_cover':
  assumes "\<R> = {region X I r |I r. valid_region X k I r}" and "\<forall>x\<in>X. 0 \<le> v x"
  shows "v \<in> [v]\<^sub>\<R>" "[v]\<^sub>\<R> \<in> \<R>"
proof -
  from region_cover[OF assms(2), of k] assms obtain R where R: "R \<in> \<R>" "v \<in> R" by auto
  from regions_closed'[OF assms(1) R, of 0] show "v \<in> [v]\<^sub>\<R>" unfolding cval_add_def by auto
  from regions_closed[OF assms(1) R, of 0] show "[v]\<^sub>\<R> \<in> \<R>" unfolding cval_add_def by auto
qed

lemma step_r_complete_aux:
  fixes R r A l' g
  defines "R' \<equiv> region_set' (R \<inter> {u. u \<turnstile> g}) r 0 \<inter> {u. u \<turnstile> inv_of A l'}"
  assumes "\<R> = {region X I r |I r. valid_region X k I r}"
    and "valid_abstraction A X k"
    and "u \<in> R"
    and "R \<in> \<R>"
    and "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
    and "u \<turnstile> g"
    and "[r\<rightarrow>0]u \<turnstile> inv_of A l'"
  shows "R = R \<inter> {u. u \<turnstile> g} \<and> R' = region_set' R r 0 \<and> R' \<in> \<R>"
proof -
  note A = assms(2-)
  from A(2) have *:
    "\<forall>(x, m)\<in>clkp_set A. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
    "collect_clkvt (trans_of A) \<subseteq> X"
    "finite X"
  by (fastforce elim: valid_abstraction.cases)+
  from A(5) *(2) have r: "set r \<subseteq> X" unfolding collect_clkvt_def by fastforce
  from *(1) A(5) have "\<forall>(x, m)\<in>collect_clock_pairs g. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
  unfolding clkp_set_def collect_clkt_def by fastforce
  from ccompatible[OF this, folded A(1)] A(3,4,6) have "R \<subseteq> \<lbrace>g\<rbrace>"
  unfolding ccompatible_def ccval_def by blast
  then have R_id: "R \<inter> {u. u \<turnstile> g} = R" unfolding ccval_def by auto
  from region_set'_id[OF A(4)[unfolded A(1)] A(3) *(3) _ _ r, of 0, folded A(1)]
  have **:
    "[[r\<rightarrow>0]u]\<^sub>\<R> = region_set' R r 0" "[[r\<rightarrow>0]u]\<^sub>\<R> \<in> \<R>" "[r\<rightarrow>0]u \<in> [[r\<rightarrow>0]u]\<^sub>\<R>"
  by auto
  let ?R = "[[r\<rightarrow>0]u]\<^sub>\<R>"
  from *(1) A(5) have ***:
    "\<forall>(x, m) \<in> collect_clock_pairs (inv_of A l'). m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
  unfolding inv_of_def clkp_set_def collect_clki_def by fastforce
  from ccompatible[OF this, folded A(1)] **(2-) A(7) have "?R \<subseteq> \<lbrace>inv_of A l'\<rbrace>"
  unfolding ccompatible_def ccval_def by blast
  then have ***: "?R \<inter> {u. u \<turnstile> inv_of A l'} = ?R" unfolding ccval_def by auto
  with **(1,2) R_id show ?thesis by (auto simp: R'_def)
qed

lemma step_r_complete:
  "\<lbrakk>A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>; \<R> = {region X I r |I r. valid_region X k I r}; valid_abstraction A X k;
    \<forall> x \<in> X. u x \<ge> 0\<rbrakk> \<Longrightarrow> \<exists> R'. A,\<R> \<turnstile> \<langle>l, ([u]\<^sub>\<R>)\<rangle> \<leadsto> \<langle>l',R'\<rangle> \<and> u' \<in> R' \<and> R' \<in> \<R>"
proof (induction rule: step.induct, goal_cases)
  case (1 A l u a l' u')
  note A = this
  then obtain g r where u': "u' = [r\<rightarrow>0]u" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "u \<turnstile> g" "u' \<turnstile> inv_of A l'"
  by (cases rule: step_a.cases) auto
  let ?R'= "region_set' (([u]\<^sub>\<R>) \<inter> {u. u \<turnstile> g}) r 0 \<inter> {u. u \<turnstile> inv_of A l'}"
  from region_cover'[OF A(2,4)] have R: "[u]\<^sub>\<R> \<in> \<R>" "u \<in> [u]\<^sub>\<R>" by auto
  from step_r_complete_aux[OF A(2,3) this(2,1) u'(2,3)] u'
  have *: "[u]\<^sub>\<R> = ([u]\<^sub>\<R>) \<inter> {u. u \<turnstile> g}" "?R' = region_set' ([u]\<^sub>\<R>) r 0" "?R' \<in> \<R>" by auto
  from 1(2,3) have "collect_clkvt (trans_of A) \<subseteq> X" "finite X" by (auto elim: valid_abstraction.cases)
  with u'(2) have r: "set r \<subseteq> X" unfolding collect_clkvt_def by fastforce
  from * u'(1) R(2) have "u' \<in> ?R'" unfolding region_set'_def by auto
  moreover have "A,\<R> \<turnstile> \<langle>l,([u]\<^sub>\<R>)\<rangle> \<leadsto> \<langle>l',?R'\<rangle>" using R(1) A(2,3) u'(2) by auto
  ultimately show ?case using *(3) by meson
next
  case (2 A l u d l' u')
  hence u': "u' = (u \<oplus> d)" "u \<turnstile> inv_of A l" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d" and "l = l'" by auto
  from region_cover'[OF 2(2,4)] have R: "[u]\<^sub>\<R> \<in> \<R>" "u \<in> [u]\<^sub>\<R>" by auto
  from SuccI2[OF 2(2) this(2,1) u'(4), of "[u']\<^sub>\<R>"] u'(1) have u'1:
    "[u']\<^sub>\<R> \<in> Succ \<R> ([u]\<^sub>\<R>)" "[u']\<^sub>\<R> \<in> \<R>"
  by auto
  from regions_closed'[OF 2(2) R(1,2) u'(4)] u'(1) have u'2: "u' \<in> [u']\<^sub>\<R>" by simp
  from 2(3) have *:
    "\<forall>(x, m)\<in>clkp_set A. m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
    "collect_clkvt (trans_of A) \<subseteq> X"
    "finite X"
  by (fastforce elim: valid_abstraction.cases)+
  from *(1) u'(2) have "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l). m \<le> real (k x) \<and> x \<in> X \<and> m \<in> \<nat>"
  unfolding clkp_set_def collect_clki_def inv_of_def by fastforce
  from ccompatible[OF this, folded 2(2)] u'1(2) u'2 u'(1,2,3) R have
    "[u']\<^sub>\<R> \<subseteq> \<lbrace>inv_of A l\<rbrace>" "([u]\<^sub>\<R>) \<subseteq> \<lbrace>inv_of A l\<rbrace>"
  unfolding ccompatible_def ccval_def by auto
  with 2 u'1 R(1) have "A,\<R> \<turnstile> \<langle>l, ([u]\<^sub>\<R>)\<rangle> \<leadsto> \<langle>l,([u']\<^sub>\<R>)\<rangle>" by auto
  with u'1(2) u'2 \<open>l = l'\<close> show ?case by meson
qed

text \<open>
  Compare this to lemma \<open>step_z_sound\<close>. This version is weaker because for regions we may very well
  arrive at a successor for which not every valuation can be reached by the predecessor.
  This is the case for e.g. the region with only Greater (k x) bounds.
\<close>

lemma step_r_sound:
  "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto> \<langle>l',R'\<rangle> \<Longrightarrow> \<R> = {region X I r |I r. valid_region X k I r}
  \<Longrightarrow> R' \<noteq> {} \<Longrightarrow> (\<forall> u \<in> R. \<exists> u' \<in> R'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)"
proof (induction rule: step_r.induct)
  case (step_t_r \<R> X k A R R' l)
  note A = this[unfolded this(1)]
  show ?case
  proof
    fix u assume u: "u \<in> R"
    from set_of_regions[OF A(3) this A(4), folded step_t_r(1)] A(2)
    obtain t where t: "t \<ge> 0" "[u \<oplus> t]\<^sub>\<R> = R'" by (auto elim: valid_abstraction.cases)
    with regions_closed'[OF A(1,3) u this(1)] step_t_r(1) have *: "(u \<oplus> t) \<in> R'" by auto
    with u t(1) A(5,6) have "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l,(u \<oplus> t)\<rangle>" unfolding ccval_def by auto
    with t * show "\<exists>u'\<in>R'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l,u'\<rangle>" by meson
  qed
next
  case A: (step_a_r \<R> X k A l g a r l' R)
  show ?case
  proof
    fix u assume u: "u \<in> R"
    from A(6) obtain v where v: "v \<in> R" "v \<turnstile> g" "[r\<rightarrow>0]v \<turnstile> inv_of A l'" unfolding region_set'_def by auto
    let ?R' = "region_set' (R \<inter> {u. u \<turnstile> g}) r 0 \<inter> {u. u \<turnstile> inv_of A l'}"
    from step_r_complete_aux[OF A(1,2) v(1) A(4,3) v(2-)] have R:
      "R = R \<inter> {u. u \<turnstile> g}" "?R' = region_set' R r 0"
    by auto
    from A have "collect_clkvt (trans_of A) \<subseteq> X" by (auto elim: valid_abstraction.cases)
    with A(3) have r: "set r \<subseteq> X" unfolding collect_clkvt_def by fastforce
    from u R have *: "[r\<rightarrow>0]u \<in> ?R'" "u \<turnstile> g" "[r\<rightarrow>0]u \<turnstile> inv_of A l'" unfolding region_set'_def by auto
    with A(3) have "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',[r\<rightarrow>0]u\<rangle>" apply (intro step.intros(1)) apply rule by auto
    with * show "\<exists>a\<in>?R'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',a\<rangle>" by meson
  qed
qed

subsection \<open>Multi Step\<close>

inductive
  steps_r :: "('a, 'c, t, 's) ta \<Rightarrow> ('c, t) zone set \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_,_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>* \<langle>_, _\<rangle>" [61,61,61,61,61,61] 61)
where
  refl: "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>* \<langle>l, R\<rangle>" |
  step: "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>* \<langle>l', R'\<rangle> \<Longrightarrow> A,\<R> \<turnstile> \<langle>l', R'\<rangle> \<leadsto> \<langle>l'', R''\<rangle> \<Longrightarrow> A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>* \<langle>l'', R''\<rangle>"

declare steps_r.intros[intro]

lemma steps_alt:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l',u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow> \<langle>l'',u''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'',u''\<rangle>"
by (induction rule: steps.induct) auto

lemma emptiness_preservance: "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto> \<langle>l',R'\<rangle> \<Longrightarrow> R = {} \<Longrightarrow> R' = {}"
by (induction rule: step_r.cases) (auto simp: region_set'_def)

lemma emptiness_preservance_steps: "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>* \<langle>l',R'\<rangle> \<Longrightarrow> R = {} \<Longrightarrow> R' = {}"
 apply (induction rule: steps_r.induct)
  apply blast
 apply (subst emptiness_preservance)
by blast+

text \<open>
  Note how it is important to define the multi-step semantics "the right way round".
  This also the direction Bouyer implies for her implicit induction.
\<close>

lemma steps_r_sound:
  "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>* \<langle>l', R'\<rangle> \<Longrightarrow> \<R> = {region X I r |I r. valid_region X k I r}
  \<Longrightarrow> R' \<noteq> {} \<Longrightarrow> u \<in> R \<Longrightarrow> \<exists> u' \<in> R'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
proof (induction rule: steps_r.induct)
  case refl then show ?case by auto
next
  case (step A \<R> l R l' R' l'' R'')
  from emptiness_preservance[OF step.hyps(2)] step.prems have "R' \<noteq> {}" by fastforce
  with step obtain u' where u': "u' \<in> R'" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l',u'\<rangle>" by auto
  with step_r_sound[OF step(2,4,5)] obtain u'' where "u'' \<in> R''" "A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow> \<langle>l'',u''\<rangle>" by blast
  with u' show ?case by (auto intro: steps_alt)
qed

lemma steps_r_sound':
  "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>* \<langle>l', R'\<rangle> \<Longrightarrow> \<R> = {region X I r |I r. valid_region X k I r}
  \<Longrightarrow> R' \<noteq> {} \<Longrightarrow> (\<exists> u' \<in> R'. \<exists> u \<in> R.  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>)"
proof goal_cases
  case 1
  with emptiness_preservance_steps[OF this(1)] obtain u where "u \<in> R" by auto
  with steps_r_sound[OF 1 this] show ?case by auto
qed

lemma single_step_r:
  "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto> \<langle>l', R'\<rangle> \<Longrightarrow> A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>* \<langle>l', R'\<rangle>"
by (metis steps_r.refl steps_r.step)

lemma steps_r_alt:
  "A,\<R> \<turnstile> \<langle>l', R'\<rangle> \<leadsto>* \<langle>l'', R''\<rangle> \<Longrightarrow> A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto> \<langle>l', R'\<rangle> \<Longrightarrow> A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>* \<langle>l'', R''\<rangle>"
 apply (induction rule: steps_r.induct)
  apply (rule single_step_r)
by auto

lemma single_step:
  "x1 \<turnstile> \<langle>x2, x3\<rangle> \<rightarrow> \<langle>x4,x5\<rangle> \<Longrightarrow> x1 \<turnstile> \<langle>x2, x3\<rangle> \<rightarrow>* \<langle>x4,x5\<rangle>"
by (metis steps.intros)

lemma steps_r_complete:
  "\<lbrakk>A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l',u'\<rangle>; \<R> = {region X I r |I r. valid_region X k I r}; valid_abstraction A X k;
    \<forall> x \<in> X. u x \<ge> 0\<rbrakk> \<Longrightarrow> \<exists> R'. A,\<R> \<turnstile> \<langle>l, ([u]\<^sub>\<R>)\<rangle> \<leadsto>* \<langle>l',R'\<rangle> \<and> u' \<in> R'"
proof (induction rule: steps.induct)
  case (refl A l u)
  from region_cover'[OF refl(1,3)] show ?case by auto
next
  case (step A l u l' u' l'' u'')
  from step_r_complete[OF step(1,4-6)] obtain R' where R':
    "A,\<R> \<turnstile> \<langle>l, ([u]\<^sub>\<R>)\<rangle> \<leadsto> \<langle>l',R'\<rangle>" "u' \<in> R'" "R' \<in> \<R>"
  by auto
  with step(4) \<open>u' \<in> R'\<close> have "\<forall>x\<in>X. 0 \<le> u' x" by auto
  with step obtain R'' where R'': "A,\<R> \<turnstile> \<langle>l', ([u']\<^sub>\<R>)\<rangle> \<leadsto>* \<langle>l'',R''\<rangle>" "u'' \<in> R''" by auto
  with region_unique[OF step(4) R'(2,3)] R'(1) have "A,\<R> \<turnstile> \<langle>l, ([u]\<^sub>\<R>)\<rangle> \<leadsto>* \<langle>l'',R''\<rangle>"
  by (subst steps_r_alt) auto
  with R'' region_cover'[OF step(4,6)] show ?case by auto
qed

end
