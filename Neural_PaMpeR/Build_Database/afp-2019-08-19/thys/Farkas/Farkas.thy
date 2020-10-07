(* Authors: R. Bottesch, M. W. Haslbeck, R. Thiemann *)

section \<open>Farkas Coefficients via the Simplex Algorithm of Duterte and de~Moura\<close>

text \<open>Let $c_1,\dots,c_n$ be a finite list of linear inequalities. 
  Let $C$ be a list of pairs $(r_i,c_i)$ where $r_i$ is a rational number.
  We say that $C$ is a list of \emph{Farkas coefficients} if
  the sum of all products $r_i \cdot c_i$ results in an inequality that is 
  trivially unsatisfiable.

  Farkas' Lemma  
  states that a finite set of non-strict linear inequalities is
  unsatisfiable if and only if Farkas coefficients exist. We will prove this lemma
  with the help of the simplex algorithm of Dutertre and de~Moura's.

  Note that the simplex implementation works on four layers, and we will formulate and prove 
  a variant of Farkas' Lemma for each of these layers.\<close>

theory Farkas
  imports Simplex.Simplex
begin

subsection \<open>Linear Inequalities\<close>

text \<open>Both Farkas' Lemma and Motzkin's Transposition Theorem require linear combinations 
  of inequalities. To this end we define one type that permits strict and non-strict 
  inequalities which are always of the form ``polynomial R constant'' where R is either 
  $\leq$ or $<$. On this type we can then define a commutative monoid.\<close>

text \<open>A type for the two relations: less-or-equal and less-than.\<close>

datatype le_rel = Leq_Rel | Lt_Rel

primrec rel_of :: "le_rel \<Rightarrow> 'a :: lrv \<Rightarrow> 'a \<Rightarrow> bool" where 
  "rel_of Leq_Rel = (\<le>)" 
| "rel_of Lt_Rel = (<)" 

instantiation le_rel :: comm_monoid_add begin
definition "zero_le_rel = Leq_Rel"
fun plus_le_rel where 
  "plus_le_rel Leq_Rel Leq_Rel = Leq_Rel" 
| "plus_le_rel _ _ = Lt_Rel" 
instance
proof
  fix a b c :: le_rel
  show "a + b + c = a + (b + c)" by (cases a; cases b; cases c, auto)
  show "a + b = b + a" by (cases a; cases b, auto)
  show "0 + a = a" unfolding zero_le_rel_def by (cases a, auto)
qed
end

lemma Leq_Rel_0: "Leq_Rel = 0" unfolding zero_le_rel_def by simp

datatype 'a le_constraint = Le_Constraint (lec_rel: le_rel) (lec_poly: linear_poly) (lec_const: 'a)

abbreviation (input) "Leqc \<equiv> Le_Constraint Leq_Rel" 

instantiation le_constraint :: (lrv) comm_monoid_add begin
fun plus_le_constraint :: "'a le_constraint \<Rightarrow> 'a le_constraint \<Rightarrow> 'a le_constraint" where
  "plus_le_constraint (Le_Constraint r1 p1 c1) (Le_Constraint r2 p2 c2) = 
    (Le_Constraint (r1 + r2) (p1 + p2) (c1 + c2))"

definition zero_le_constraint :: "'a le_constraint" where
  "zero_le_constraint = Leqc 0 0"

instance proof
  fix a b c :: "'a le_constraint"
  show "0 + a = a"
    by (cases a, auto simp: zero_le_constraint_def Leq_Rel_0)
  show "a + b = b + a" by (cases a; cases b, auto simp: ac_simps)
  show "a + b + c = a + (b + c)" by (cases a; cases b; cases c, auto simp: ac_simps)
qed
end 

primrec satisfiable_le_constraint :: "'a::lrv valuation \<Rightarrow> 'a le_constraint \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>l\<^sub>e" 100) where
  "(v \<Turnstile>\<^sub>l\<^sub>e (Le_Constraint rel l r)) \<longleftrightarrow> (rel_of rel (l\<lbrace>v\<rbrace>) r)"

lemma satisfies_zero_le_constraint: "v \<Turnstile>\<^sub>l\<^sub>e 0"
  by (simp add: valuate_zero zero_le_constraint_def)

lemma satisfies_sum_le_constraints:
  assumes "v \<Turnstile>\<^sub>l\<^sub>e c" "v \<Turnstile>\<^sub>l\<^sub>e d"
  shows "v \<Turnstile>\<^sub>l\<^sub>e (c + d)"
proof -
  obtain lc rc ld rd rel1 rel2 where cd: "c = Le_Constraint rel1 lc rc" "d = Le_Constraint rel2 ld rd" 
    by (cases c; cases d, auto)
  have 1: "rel_of rel1 (lc\<lbrace>v\<rbrace>) rc" using assms cd by auto
  have 2: "rel_of rel2 (ld\<lbrace>v\<rbrace>) rd" using assms cd by auto
  from 1 have le1: "lc\<lbrace>v\<rbrace> \<le> rc" by (cases rel1, auto)
  from 2 have le2: "ld\<lbrace>v\<rbrace> \<le> rd" by (cases rel2, auto)
  from 1 2 le1 le2 have "rel_of (rel1 + rel2) ((lc\<lbrace>v\<rbrace>) + (ld\<lbrace>v\<rbrace>)) (rc + rd)" 
    apply (cases rel1; cases rel2; simp add: add_mono)
    by (metis add.commute le_less_trans order.strict_iff_order plus_less)+
  thus ?thesis by (auto simp: cd valuate_add)
qed

lemma satisfies_sumlist_le_constraints:
  assumes "\<And> c. c \<in> set (cs :: 'a :: lrv le_constraint list) \<Longrightarrow> v \<Turnstile>\<^sub>l\<^sub>e c"
  shows "v \<Turnstile>\<^sub>l\<^sub>e sum_list cs"
  using assms 
  by (induct cs, auto intro: satisfies_zero_le_constraint satisfies_sum_le_constraints)

lemma sum_list_lec:
  "sum_list ls = Le_Constraint 
    (sum_list (map lec_rel ls)) 
    (sum_list (map lec_poly ls)) 
    (sum_list (map lec_const ls))"
proof (induct ls)
  case Nil
  show ?case by (auto simp: zero_le_constraint_def Leq_Rel_0) 
next
  case (Cons l ls)
  show ?case by (cases l, auto simp: Cons)
qed

lemma sum_list_Leq_Rel: "((\<Sum>x\<leftarrow>C. lec_rel (f x)) = Leq_Rel) \<longleftrightarrow> (\<forall> x \<in> set C. lec_rel (f x) = Leq_Rel)" 
proof (induct C)
  case (Cons c C)
  show ?case 
  proof (cases "lec_rel (f c)")
    case Leq_Rel
    show ?thesis using Cons by (simp add: Leq_Rel Leq_Rel_0)
  qed simp
qed (simp add: Leq_Rel_0)


subsection \<open>Farkas' Lemma on Layer 4\<close>

text \<open>On layer 4 the algorithm works on a state containing a tableau, atoms (or bounds), 
  an assignment and a satisfiability flag. Only non-strict inequalities appear at this level.
  In order to even state a variant of Farkas' Lemma on layer 4, we 
  need conversions from atoms to non-strict constraints and then further
  to linear inequalities of type @{type le_constraint}. 
  The latter conversion is a partial operation, since non-strict constraints
  of type @{type ns_constraint} permit greater-or-equal constraints, whereas @{type le_constraint}
  allows only less-or-equal.\<close>

text \<open>The advantage of first going via @{type ns_constraint} is that this type permits a multiplication
  with arbitrary rational numbers (the direction of the inequality must be flipped when
  multiplying by a negative number, which is not possible with @{type le_constraint}).\<close>

instantiation ns_constraint :: (scaleRat) scaleRat
begin
fun scaleRat_ns_constraint :: "rat \<Rightarrow> 'a ns_constraint \<Rightarrow> 'a ns_constraint" where
  "scaleRat_ns_constraint r (LEQ_ns p c) = 
    (if (r < 0) then GEQ_ns (r *R p) (r *R c) else LEQ_ns (r *R p) (r *R c))"
| "scaleRat_ns_constraint r (GEQ_ns p c) = 
    (if (r > 0) then GEQ_ns (r *R p) (r *R c) else LEQ_ns (r *R p) (r *R c))"

instance ..
end

lemma sat_scale_rat_ns: assumes "v \<Turnstile>\<^sub>n\<^sub>s ns"
  shows "v \<Turnstile>\<^sub>n\<^sub>s (f *R ns)"
proof -
  have "f < 0 | f = 0 | f > 0" by auto
  then show ?thesis using assms by (cases ns, auto simp: valuate_scaleRat scaleRat_leq1 scaleRat_leq2)
qed

lemma scaleRat_scaleRat_ns_constraint: assumes "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0" 
  shows "a *R (b *R (c :: 'a :: lrv ns_constraint)) = (a * b) *R c" 
proof - 
  have "b > 0 \<or> b < 0 \<or> b = 0" by linarith
  moreover have "a > 0 \<or> a < 0 \<or> a = 0" by linarith
  ultimately show ?thesis using assms
    by (elim disjE; cases c, auto simp add: not_le not_less
        mult_neg_pos mult_neg_neg mult_nonpos_nonneg mult_nonpos_nonpos mult_nonneg_nonpos mult_pos_neg)
qed

fun lec_of_nsc where
  "lec_of_nsc (LEQ_ns p c) = (Leqc p c)"

fun is_leq_ns where
  "is_leq_ns (LEQ_ns p c) = True"
| "is_leq_ns (GEQ_ns p c) = False"

lemma lec_of_nsc: 
  assumes "is_leq_ns c"
  shows "(v \<Turnstile>\<^sub>l\<^sub>e lec_of_nsc c) \<longleftrightarrow> (v \<Turnstile>\<^sub>n\<^sub>s c)"
  using assms by (cases c, auto)

fun nsc_of_atom where
  "nsc_of_atom (Leq var b) = LEQ_ns (lp_monom 1 var) b"
| "nsc_of_atom (Geq var b) = GEQ_ns (lp_monom 1 var) b"

lemma nsc_of_atom: "v \<Turnstile>\<^sub>n\<^sub>s nsc_of_atom a \<longleftrightarrow> v \<Turnstile>\<^sub>a a"
  by (cases a, auto)


text \<open>We say that $C$ is a list of Farkas coefficients \emph{for a given tableau $t$ and atom set $as$}, if
  it is a list of pairs $(r,a)$ such that $a \in as$, $r$ is non-zero, $r \cdot a$ is a
  `less-than-or-equal'-constraint, and the linear combination
  of inequalities must result in an inequality of the form $p \leq c$, where $c < 0$ and $t \models
  p = 0$.\<close>

definition farkas_coefficients_atoms_tableau where 
  "farkas_coefficients_atoms_tableau (as :: 'a :: lrv atom set) t C = (\<exists> p c. 
    (\<forall>(r,a) \<in> set C. a \<in> as \<and> is_leq_ns (r *R nsc_of_atom a) \<and> r \<noteq> 0) \<and>
    (\<Sum>(r,a) \<leftarrow> C. lec_of_nsc (r *R nsc_of_atom a)) = Leqc p c \<and>
    c < 0 \<and>
    (\<forall> v :: 'a valuation. v \<Turnstile>\<^sub>t t \<longrightarrow>(p\<lbrace>v\<rbrace> = 0)))"

text \<open>We first prove that if the check-function detects a conflict, then 
  Farkas coefficients do exist for the tableau and atom set for which the
  conflict is detected.\<close>

definition bound_atoms :: "('i, 'a) state \<Rightarrow> 'a atom set" ("\<B>\<^sub>A") where
  "bound_atoms s = (\<lambda>(v,x). Geq v x) ` (set_of_map (\<B>\<^sub>l s)) \<union> 
                   (\<lambda>(v,x). Leq v x) ` (set_of_map (\<B>\<^sub>u s))"

context PivotUpdateMinVars
begin

lemma farkas_check: 
  assumes check: "check s' = s" and U: "\<U> s" "\<not> \<U> s'"
    and inv: "\<nabla> s'" "\<triangle> (\<T> s')" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s'" "\<diamond> s'" 
    and index: "index_valid as s'" 
  shows "\<exists> C. farkas_coefficients_atoms_tableau (snd ` as) (\<T> s') C"
proof -
  let ?Q = "\<lambda> s f p c C. set C \<subseteq> \<B>\<^sub>A s \<and>
    distinct C \<and>
    (\<forall>a \<in> set C. is_leq_ns (f (atom_var a) *R nsc_of_atom a) \<and> f (atom_var a) \<noteq> 0) \<and>
    (\<Sum>a \<leftarrow> C. lec_of_nsc (f (atom_var a) *R nsc_of_atom a)) = Leqc p c \<and>
    c < 0 \<and>
    (\<forall> v :: 'a valuation. v \<Turnstile>\<^sub>t \<T> s \<longrightarrow>(p\<lbrace>v\<rbrace> = 0))" 
  let ?P = "\<lambda> s. \<U> s \<longrightarrow> (\<exists> f p c C. ?Q s f p c C)" 
  have "?P (check s')"
  proof (induct rule: check_induct''[OF inv, of ?P])
    case (3 s x\<^sub>i dir I)
    have dir: "dir = Positive \<or> dir = Negative" by fact
    let ?eq = "(eq_for_lvar (\<T> s) x\<^sub>i)"
    define X\<^sub>j where "X\<^sub>j = rvars_eq ?eq"
    define XL\<^sub>j where "XL\<^sub>j = Abstract_Linear_Poly.vars_list (rhs ?eq)"
    have [simp]: "set XL\<^sub>j = X\<^sub>j" unfolding XL\<^sub>j_def X\<^sub>j_def 
      using set_vars_list by blast
    have XL\<^sub>j_distinct: "distinct XL\<^sub>j"
      unfolding XL\<^sub>j_def using distinct_vars_list by simp
    define A where "A = coeff (rhs ?eq)"
    have bounds_id: "\<B>\<^sub>A (set_unsat I s) = \<B>\<^sub>A s" "\<B>\<^sub>u (set_unsat I s) = \<B>\<^sub>u s" "\<B>\<^sub>l (set_unsat I s) = \<B>\<^sub>l s"
      by (auto simp: boundsl_def boundsu_def bound_atoms_def)
    have t_id: "\<T> (set_unsat I s) = \<T> s" by simp
    have u_id: "\<U> (set_unsat I s) = True" by simp
    let ?p = "rhs ?eq - lp_monom 1 x\<^sub>i"
    have p_eval_zero: "?p \<lbrace> v \<rbrace> = 0" if "v \<Turnstile>\<^sub>t \<T> s" for v :: "'a valuation"
    proof -
      have eqT: "?eq \<in> set (\<T> s)" 
        by (simp add: 3(7) eq_for_lvar local.min_lvar_not_in_bounds_lvars)
      have "v \<Turnstile>\<^sub>e ?eq" using that eqT satisfies_tableau_def by blast
      also have "?eq = (lhs ?eq, rhs ?eq)" by (cases ?eq, auto)
      also have "lhs ?eq = x\<^sub>i" by (simp add: 3(7) eq_for_lvar local.min_lvar_not_in_bounds_lvars)
      finally have "v \<Turnstile>\<^sub>e (x\<^sub>i, rhs ?eq)" .
      then show ?thesis by (auto simp: satisfies_eq_iff valuate_minus)
    qed
    have Xj_rvars: "X\<^sub>j \<subseteq> rvars (\<T> s)" unfolding X\<^sub>j_def
      using 3 min_lvar_not_in_bounds_lvars rvars_of_lvar_rvars by blast 
    have xi_lvars: "x\<^sub>i \<in> lvars (\<T> s)" 
      using 3 min_lvar_not_in_bounds_lvars rvars_of_lvar_rvars by blast 
    have "lvars (\<T> s) \<inter> rvars (\<T> s) = {}"
      using 3 normalized_tableau_def by auto
    with xi_lvars Xj_rvars have xi_Xj: "x\<^sub>i \<notin> X\<^sub>j"
      by blast
    have rhs_eval_xi: "(rhs (eq_for_lvar (\<T> s) x\<^sub>i)) \<lbrace>\<langle>\<V> s\<rangle>\<rbrace> = \<langle>\<V> s\<rangle> x\<^sub>i"
    proof -
      have *: "(rhs eq) \<lbrace> v \<rbrace> = v (lhs eq)" if "v \<Turnstile>\<^sub>e eq" for v :: "'a valuation" and eq
        using satisfies_eq_def that by metis
      moreover have "\<langle>\<V> s\<rangle> \<Turnstile>\<^sub>e eq_for_lvar (\<T> s) x\<^sub>i"
        using 3 satisfies_tableau_def eq_for_lvar curr_val_satisfies_no_lhs_def xi_lvars
        by blast
      ultimately show ?thesis
        using eq_for_lvar xi_lvars by simp
    qed
    let ?\<B>\<^sub>l = "Direction.LB dir" 
    let ?\<B>\<^sub>u = "Direction.UB dir" 
    let ?lt = "Direction.lt dir" 
    let ?le = "Simplex.le ?lt" 
    let ?Geq = "Direction.GE dir" 
    let ?Leq = "Direction.LE dir" 

    have 0: "(if A x < 0 then ?\<B>\<^sub>l s x = Some (\<langle>\<V> s\<rangle> x) else ?\<B>\<^sub>u s x = Some (\<langle>\<V> s\<rangle> x)) \<and> A x \<noteq> 0"
      if x: "x \<in> X\<^sub>j" for x
    proof -
      have "Some (\<langle>\<V> s\<rangle> x) = (?\<B>\<^sub>l s x)" if "A x < 0" 
      proof -
        have cmp: "\<not> \<rhd>\<^sub>l\<^sub>b ?lt (\<langle>\<V> s\<rangle> x) (?\<B>\<^sub>l s x)" 
          using x that dir min_rvar_incdec_eq_None[OF 3(9)] unfolding X\<^sub>j_def A_def by auto
        then obtain c where c: "?\<B>\<^sub>l s x = Some c"
          by (cases "?\<B>\<^sub>l s x", auto simp: bound_compare_defs)
        also have "c = \<langle>\<V> s\<rangle> x"
        proof -
          have "x \<in> rvars (\<T> s)" using that x Xj_rvars by blast
          then have "x \<in> (- lvars (\<T> s))"
            using 3 unfolding normalized_tableau_def by auto
          moreover have "\<forall>x\<in>(- lvars (\<T> s)). in_bounds x \<langle>\<V> s\<rangle> (\<B>\<^sub>l s, \<B>\<^sub>u s)"
            using 3 unfolding curr_val_satisfies_no_lhs_def 
            by (simp add: satisfies_bounds_set.simps)
          ultimately have "in_bounds x \<langle>\<V> s\<rangle> (\<B>\<^sub>l s, \<B>\<^sub>u s)"
            by blast
          moreover have "?le (\<langle>\<V> s\<rangle> x) c"
            using cmp c dir unfolding bound_compare_defs by auto
          ultimately show ?thesis
            using c dir by auto
        qed
        then show ?thesis
          using c by simp
      qed
      moreover have "Some (\<langle>\<V> s\<rangle> x) = (?\<B>\<^sub>u s x)" if "0 < A x" 
      proof -
        have cmp: "\<not> \<lhd>\<^sub>u\<^sub>b ?lt (\<langle>\<V> s\<rangle> x) (?\<B>\<^sub>u s x)" 
          using x that min_rvar_incdec_eq_None[OF 3(9)] unfolding X\<^sub>j_def A_def by auto
        then obtain c where c: "?\<B>\<^sub>u s x = Some c"
          by (cases "?\<B>\<^sub>u s x", auto simp: bound_compare_defs)
        also have "c = \<langle>\<V> s\<rangle> x"
        proof -
          have "x \<in> rvars (\<T> s)" using that x Xj_rvars by blast
          then have "x \<in> (- lvars (\<T> s))"
            using 3 unfolding normalized_tableau_def by auto
          moreover have "\<forall>x\<in>(- lvars (\<T> s)). in_bounds x \<langle>\<V> s\<rangle> (\<B>\<^sub>l s, \<B>\<^sub>u s)"
            using 3 unfolding curr_val_satisfies_no_lhs_def 
            by (simp add: satisfies_bounds_set.simps)
          ultimately have "in_bounds x \<langle>\<V> s\<rangle> (\<B>\<^sub>l s, \<B>\<^sub>u s)"
            by blast
          moreover have "?le c (\<langle>\<V> s\<rangle> x)"
            using cmp c dir unfolding bound_compare_defs by auto
          ultimately show ?thesis
            using c dir by auto
        qed
        then show ?thesis
          using c by simp
      qed
      moreover have "A x \<noteq> 0"
        using that coeff_zero unfolding A_def X\<^sub>j_def by auto
      ultimately show ?thesis
        using that by auto
    qed

    have l_Ba: "l \<in> \<B>\<^sub>A s" if "l \<in> {?Geq x\<^sub>i (the (?\<B>\<^sub>l s x\<^sub>i))}" for l 
    proof -
      from that have l: "l = ?Geq x\<^sub>i (the (?\<B>\<^sub>l s x\<^sub>i))" by simp
      from 3(8) obtain c where bl': "?\<B>\<^sub>l s x\<^sub>i = Some c" 
        by (cases "?\<B>\<^sub>l s x\<^sub>i", auto simp: bound_compare_defs)
      hence bl: "(x\<^sub>i, c) \<in> set_of_map (?\<B>\<^sub>l s)" unfolding set_of_map_def by auto
      show "l \<in> \<B>\<^sub>A s" unfolding l bound_atoms_def using bl bl' dir by auto
    qed

    let ?negA = "filter (\<lambda> x. A x < 0) XL\<^sub>j" 
    let ?posA = "filter (\<lambda> x. \<not> A x < 0) XL\<^sub>j"

    define neg where "neg = (if dir = Positive then (\<lambda> x :: rat. x) else uminus)" 
    define negP where "negP = (if dir = Positive then (\<lambda> x :: linear_poly. x) else uminus)" 
    define nega where "nega = (if dir = Positive then (\<lambda> x :: 'a. x) else uminus)" 
    from dir have dirn: "dir = Positive \<and> neg = (\<lambda> x. x) \<and> negP = (\<lambda> x. x) \<and> nega = (\<lambda> x. x)
      \<or> dir = Negative \<and> neg = uminus \<and> negP = uminus \<and> nega = uminus" 
      unfolding neg_def negP_def nega_def by auto

    define C where "C = map (\<lambda>x. ?Geq x (the (?\<B>\<^sub>l s x))) ?negA 
                        @ map (\<lambda> x. ?Leq x (the (?\<B>\<^sub>u s x)))  ?posA
                        @ [?Geq x\<^sub>i (the (?\<B>\<^sub>l s x\<^sub>i))]"  
    define f where "f = (\<lambda>x. if x = x\<^sub>i then neg (-1) else neg (A x))"
    define c where "c = (\<Sum>x\<leftarrow>C. lec_const (lec_of_nsc (f (atom_var x) *R nsc_of_atom x)))"
    let ?q = "negP ?p" 

    show ?case unfolding bounds_id t_id u_id
    proof (intro exI impI conjI allI)
      show "v \<Turnstile>\<^sub>t \<T> s \<Longrightarrow> ?q \<lbrace> v \<rbrace> = 0" for v :: "'a valuation" using dirn p_eval_zero[of v] 
        by (auto simp: valuate_minus)

      show "set C \<subseteq> \<B>\<^sub>A s"
        unfolding C_def set_append set_map set_filter list.simps using 0 l_Ba dir
        by (intro Un_least subsetI) (force simp: bound_atoms_def set_of_map_def)+

      show is_leq: "\<forall>a\<in>set C. is_leq_ns (f (atom_var a) *R nsc_of_atom a) \<and> f (atom_var a) \<noteq> 0"
        using dirn xi_Xj 0 unfolding C_def f_def 
        by (elim disjE, auto)

      show "(\<Sum>a \<leftarrow> C. lec_of_nsc (f (atom_var a) *R nsc_of_atom a)) = Leqc ?q c"
        unfolding sum_list_lec le_constraint.simps map_map o_def
      proof (intro conjI)
        define scale_poly :: "'a atom \<Rightarrow> linear_poly" where 
          "scale_poly = (\<lambda>x. lec_poly (lec_of_nsc (f (atom_var x) *R nsc_of_atom x)))"
        have "(\<Sum>x\<leftarrow>C. scale_poly x) =
            (\<Sum>x\<leftarrow>?negA. scale_poly (?Geq x (the (?\<B>\<^sub>l s x))))
          + (\<Sum>x\<leftarrow>?posA. scale_poly (?Leq x (the (?\<B>\<^sub>u s x))))
          - negP (lp_monom 1 x\<^sub>i)"
          unfolding C_def using dirn by (auto simp add: comp_def scale_poly_def f_def)
        also have "(\<Sum>x\<leftarrow>?negA. scale_poly (?Geq x (the (?\<B>\<^sub>l s x))))
          =  (\<Sum>x\<leftarrow> ?negA. negP (A x *R lp_monom 1 x))"
          unfolding scale_poly_def f_def using dirn xi_Xj by (subst map_cong) auto
        also have "(\<Sum>x\<leftarrow>?posA. scale_poly (?Leq x (the (?\<B>\<^sub>u s x))))
          =  (\<Sum>x\<leftarrow> ?posA. negP (A x *R lp_monom 1 x))"
          unfolding scale_poly_def f_def using dirn xi_Xj by (subst map_cong) auto
        also have "(\<Sum>x\<leftarrow> ?negA. negP (A x *R lp_monom 1 x)) +
              (\<Sum>x\<leftarrow> ?posA. negP (A x *R lp_monom 1 x))
             = negP (rhs (eq_for_lvar (\<T> s) x\<^sub>i))"
          using dirn XL\<^sub>j_distinct coeff_zero            
          by (elim disjE; intro poly_eqI, auto intro!: poly_eqI simp add: coeff_sum_list A_def X\<^sub>j_def 
              uminus_sum_list_map[unfolded o_def, symmetric])
        finally show "(\<Sum>x\<leftarrow>C. lec_poly (lec_of_nsc (f (atom_var x) *R nsc_of_atom x))) = ?q"
          unfolding scale_poly_def using dirn by auto
        show "(\<Sum>x\<leftarrow>C. lec_rel (lec_of_nsc (f (atom_var x) *R nsc_of_atom x))) = Leq_Rel"  
          unfolding sum_list_Leq_Rel 
        proof
          fix c
          assume c: "c \<in> set C" 
          show "lec_rel (lec_of_nsc (f (atom_var c) *R nsc_of_atom c)) = Leq_Rel" 
            using is_leq[rule_format, OF c] by (cases "f (atom_var c) *R nsc_of_atom c", auto)
        qed
      qed (simp add: c_def)

      show "c < 0"
      proof -
        define scale_const_f :: "'a atom \<Rightarrow> 'a" where
          "scale_const_f x = lec_const (lec_of_nsc (f (atom_var x) *R nsc_of_atom x))" for x
        obtain d where bl': "?\<B>\<^sub>l s x\<^sub>i = Some d" 
          using 3 by (cases "?\<B>\<^sub>l s x\<^sub>i", auto simp: bound_compare_defs)
        have "c = (\<Sum>x\<leftarrow>map (\<lambda>x. ?Geq x (the (?\<B>\<^sub>l s x))) ?negA. scale_const_f x)
                     + (\<Sum>x\<leftarrow> map (\<lambda>x. ?Leq x (the (?\<B>\<^sub>u s x))) ?posA. scale_const_f x) 
                   - nega d"
          unfolding c_def C_def f_def scale_const_f_def using dirn rhs_eval_xi bl' by auto
        also have "(\<Sum>x\<leftarrow>map (\<lambda>x. ?Geq x (the (?\<B>\<^sub>l s x))) ?negA. scale_const_f x) =
              (\<Sum>x\<leftarrow> ?negA. nega (A x *R the (?\<B>\<^sub>l s x)))"
          using xi_Xj dirn by (subst map_cong) (auto simp add: f_def scale_const_f_def)
        also have "\<dots> = (\<Sum>x\<leftarrow>?negA. nega (A x *R \<langle>\<V> s\<rangle> x))"
          using 0 by (subst map_cong) auto
        also have "(\<Sum>x\<leftarrow>map (\<lambda>x. ?Leq x (the (?\<B>\<^sub>u s x))) ?posA. scale_const_f x) =
              (\<Sum>x\<leftarrow> ?posA. nega (A x *R the (?\<B>\<^sub>u s x)))"
          using xi_Xj dirn by (subst map_cong) (auto simp add: f_def scale_const_f_def)
        also have "\<dots> = (\<Sum>x\<leftarrow> ?posA. nega (A x *R \<langle>\<V> s\<rangle> x))"
          using 0 by (subst map_cong) auto
        also have "(\<Sum>x\<leftarrow>?negA. nega (A x *R \<langle>\<V> s\<rangle> x)) + (\<Sum>x\<leftarrow>?posA. nega (A x *R \<langle>\<V> s\<rangle> x))
             = (\<Sum>x\<leftarrow>?negA @ ?posA. nega (A x *R \<langle>\<V> s\<rangle> x))"
          by auto
        also have "\<dots> = (\<Sum>x\<in> X\<^sub>j. nega (A x *R \<langle>\<V> s\<rangle> x))"
          using XL\<^sub>j_distinct by (subst sum_list_distinct_conv_sum_set) (auto intro!: sum.cong)
        also have "\<dots> = nega (\<Sum>x\<in> X\<^sub>j. (A x *R \<langle>\<V> s\<rangle> x))" using dirn by (auto simp: sum_negf) 
        also have "(\<Sum>x\<in> X\<^sub>j. (A x *R \<langle>\<V> s\<rangle> x)) = ((rhs ?eq) \<lbrace>\<langle>\<V> s\<rangle>\<rbrace>)"
          unfolding A_def X\<^sub>j_def by (subst linear_poly_sum) (auto simp add: sum_negf)
        also have "\<dots> = \<langle>\<V> s\<rangle> x\<^sub>i"
          using rhs_eval_xi by blast
        also have "nega (\<langle>\<V> s\<rangle> x\<^sub>i) - nega d < 0"
        proof -
          have "?lt (\<langle>\<V> s\<rangle> x\<^sub>i) d" 
            using dirn 3(2-) bl' by (elim disjE, auto simp: bound_compare_defs)   
          thus ?thesis using dirn unfolding minus_lt[symmetric] by auto
        qed
        finally show ?thesis .
      qed

      show "distinct C"
        unfolding C_def using XL\<^sub>j_distinct xi_Xj dirn by (auto simp add: inj_on_def distinct_map)
    qed
  qed (insert U, blast+)
  then obtain f p c C where Qs: "?Q s f p c C" using U unfolding check by blast
  from index[folded check_tableau_index_valid[OF U(2) inv(3,4,2,1)]] check 
  have index: "index_valid as s" by auto
  from check_tableau_equiv[OF U(2) inv(3,4,2,1), unfolded check]
  have id: "v \<Turnstile>\<^sub>t \<T> s = v \<Turnstile>\<^sub>t \<T> s'" for v :: "'a valuation" by auto
  let ?C = "map (\<lambda> a. (f (atom_var a), a)) C"
  have "set C \<subseteq> \<B>\<^sub>A s" using Qs by blast
  also have "\<dots> \<subseteq> snd ` as" using index 
    unfolding bound_atoms_def index_valid_def set_of_map_def boundsl_def boundsu_def o_def by force
  finally have sub: "snd ` set ?C \<subseteq> snd ` as" by force
  show ?thesis unfolding farkas_coefficients_atoms_tableau_def
    by (intro exI[of _ p] exI[of _ c] exI[of _ ?C] conjI,
        insert Qs[unfolded id] sub, (force simp: o_def)+)
qed

end

text \<open>Next, we show that a conflict found by the assert-bound function also gives rise to
  Farkas coefficients.\<close>

context Update
begin

lemma farkas_assert_bound: assumes inv: "\<not> \<U> s" "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s s" "\<triangle> (\<T> s)" "\<nabla> s" "\<diamond> s"
  and index: "index_valid as s" 
  and U: "\<U> (assert_bound ia s)" 
shows "\<exists> C. farkas_coefficients_atoms_tableau (snd ` (insert ia as)) (\<T> s) C"
proof -
  obtain i a where ia[simp]: "ia = (i,a)" by force
  let ?A = "snd ` insert ia as" 
  have "\<exists> x c d. Leq x c \<in> ?A \<and> Geq x d \<in> ?A \<and> c < d" 
  proof (cases a)
    case (Geq x d)
    let ?s = "update\<B>\<I> (Direction.UBI_upd (Direction (\<lambda>x y. y < x) \<B>\<^sub>i\<^sub>u \<B>\<^sub>i\<^sub>l \<B>\<^sub>u \<B>\<^sub>l \<I>\<^sub>u \<I>\<^sub>l \<B>\<^sub>i\<^sub>l_update Geq Leq (\<le>)))
                        i x d s" 
    have id: "\<U> ?s = \<U> s" by auto
    have norm: "\<triangle> (\<T> ?s)" using inv by auto
    have val: "\<nabla> ?s" using inv(4) unfolding tableau_valuated_def by simp
    have idd: "x \<notin> lvars (\<T> ?s) \<Longrightarrow> \<U> (update x d ?s) = \<U> ?s"
      by (rule update_unsat_id[OF norm val])
    from U[unfolded ia Geq] inv(1) id idd 
    have "\<lhd>\<^sub>l\<^sub>b (\<lambda>x y. y < x) d (\<B>\<^sub>u s x)" by (auto split: if_splits simp: Let_def)
    then obtain c where Bu: "\<B>\<^sub>u s x = Some c" and lt: "c < d" 
      by (cases "\<B>\<^sub>u s x", auto simp: bound_compare_defs)
    from Bu obtain j where "Mapping.lookup (\<B>\<^sub>i\<^sub>u s) x = Some (j,c)"  
      unfolding boundsu_def by auto
    with index[unfolded index_valid_def] have "(j, Leq x c) \<in> as" by auto
    hence xc: "Leq x c \<in> ?A" by force
    have xd: "Geq x d \<in> ?A" unfolding ia Geq by force
    from xc xd lt show ?thesis by auto
  next
    case (Leq x c)
    let ?s = "update\<B>\<I> (Direction.UBI_upd (Direction (<) \<B>\<^sub>i\<^sub>l \<B>\<^sub>i\<^sub>u \<B>\<^sub>l \<B>\<^sub>u \<I>\<^sub>l \<I>\<^sub>u \<B>\<^sub>i\<^sub>u_update Leq Geq (\<ge>))) i x c s" 
    have id: "\<U> ?s = \<U> s" by auto
    have norm: "\<triangle> (\<T> ?s)" using inv by auto
    have val: "\<nabla> ?s" using inv(4) unfolding tableau_valuated_def by simp
    have idd: "x \<notin> lvars (\<T> ?s) \<Longrightarrow> \<U> (update x c ?s) = \<U> ?s"
      by (rule update_unsat_id[OF norm val])
    from U[unfolded ia Leq] inv(1) id idd 
    have "\<lhd>\<^sub>l\<^sub>b (<) c (\<B>\<^sub>l s x)" by (auto split: if_splits simp: Let_def)
    then obtain d where Bl: "\<B>\<^sub>l s x = Some d" and lt: "c < d" 
      by (cases "\<B>\<^sub>l s x", auto simp: bound_compare_defs)
    from Bl obtain j where "Mapping.lookup (\<B>\<^sub>i\<^sub>l s) x = Some (j,d)"  
      unfolding boundsl_def by auto
    with index[unfolded index_valid_def] have "(j, Geq x d) \<in> as" by auto
    hence xd: "Geq x d \<in> ?A" by force
    have xc: "Leq x c \<in> ?A" unfolding ia Leq by force
    from xc xd lt show ?thesis by auto
  qed
  then obtain x c d where c: "Leq x c \<in> ?A" and d: "Geq x d \<in> ?A" and cd: "c < d" by blast
  show ?thesis unfolding farkas_coefficients_atoms_tableau_def
  proof (intro exI conjI allI)
    let ?C = "[(-1, Geq x d), (1,Leq x c)]" 
    show "\<forall>(r,a)\<in>set ?C. a \<in> ?A \<and> is_leq_ns (r *R nsc_of_atom a) \<and> r \<noteq> 0" using c d by auto
    show "c - d < 0" using cd using minus_lt by auto
  qed (auto simp: valuate_zero)
qed
end


text \<open>Moreover, we prove that all other steps of the simplex algorithm on layer~4, such as pivoting,
  asserting bounds without conflict, etc., preserve Farkas coefficients.\<close>

lemma farkas_coefficients_atoms_tableau_mono: assumes "as \<subseteq> bs" 
  shows "farkas_coefficients_atoms_tableau as t C \<Longrightarrow> farkas_coefficients_atoms_tableau bs t C" 
  using assms unfolding farkas_coefficients_atoms_tableau_def by force

locale AssertAllState''' = AssertAllState'' init ass_bnd chk + Update update + 
  PivotUpdateMinVars eq_idx_for_lvar min_lvar_not_in_bounds min_rvar_incdec_eq pivot_and_update
  for init and ass_bnd :: "'i \<times> 'a :: lrv atom \<Rightarrow> _" and chk :: "('i, 'a) state \<Rightarrow> ('i, 'a) state" and update :: "nat \<Rightarrow> 'a :: lrv \<Rightarrow> ('i, 'a) state \<Rightarrow> ('i, 'a) state" 
    and eq_idx_for_lvar :: "tableau \<Rightarrow> var \<Rightarrow> nat" and
    min_lvar_not_in_bounds :: "('i,'a::lrv) state \<Rightarrow> var option" and
    min_rvar_incdec_eq :: "('i,'a) Direction \<Rightarrow> ('i,'a) state \<Rightarrow> eq \<Rightarrow> 'i list + var" and
    pivot_and_update :: "var \<Rightarrow> var \<Rightarrow> 'a \<Rightarrow> ('i,'a) state \<Rightarrow> ('i,'a) state"
    + assumes ass_bnd: "ass_bnd = Update.assert_bound update" and
    chk: "chk = PivotUpdateMinVars.check eq_idx_for_lvar min_lvar_not_in_bounds min_rvar_incdec_eq pivot_and_update"

context AssertAllState'''
begin

lemma farkas_assert_bound_loop: assumes "\<U> (assert_bound_loop as (init t))" 
  and norm: "\<triangle> t" 
shows "\<exists> C. farkas_coefficients_atoms_tableau (snd ` set as) t C" 
proof -
  let ?P = "\<lambda> as s. \<U> s \<longrightarrow> (\<exists> C. farkas_coefficients_atoms_tableau (snd ` as) (\<T> s) C)" 
  let ?s = "assert_bound_loop as (init t)" 
  have "\<not> \<U> (init t)" by (rule init_unsat_flag)
  have "\<T> (assert_bound_loop as (init t)) = t \<and> 
    (\<U> (assert_bound_loop as (init t)) \<longrightarrow> (\<exists> C. farkas_coefficients_atoms_tableau (snd ` set as) (\<T> (init t)) C))" 
  proof (rule AssertAllState''Induct[OF norm], unfold ass_bnd, goal_cases)
    case 1
    have "\<not> \<U> (init t)" by (rule init_unsat_flag)
    moreover have "\<T> (init t) = t" by (rule init_tableau_id)
    ultimately show ?case by auto
  next
    case (2 as bs s)
    hence "snd ` as \<subseteq> snd ` bs" by auto
    from farkas_coefficients_atoms_tableau_mono[OF this] 2(2) show ?case by auto
  next
    case (3 s a ats)
    let ?s = "assert_bound a s" 
    have tab: "\<T> ?s = \<T> s" unfolding ass_bnd by (rule assert_bound_nolhs_tableau_id, insert 3, auto)
    have t: "t = \<T> s" using 3 by simp
    show ?case unfolding t tab
    proof (intro conjI impI refl)
      assume "\<U> ?s"
      from farkas_assert_bound[OF 3(1,3-6,8) this]
      show "\<exists> C. farkas_coefficients_atoms_tableau (snd ` insert a (set ats)) (\<T> (init (\<T> s))) C" 
        unfolding t[symmetric] init_tableau_id .
    qed
  qed
  thus ?thesis unfolding init_tableau_id using assms by blast
qed

text \<open>Now we get to the main result for layer~4: If the main algorithm returns unsat,
  then there are Farkas coefficients for the tableau and atom set that were given as
  input for this layer.\<close>

lemma farkas_assert_all_state: assumes U: "\<U> (assert_all_state t as)" 
  and norm: "\<triangle> t" 
shows "\<exists> C. farkas_coefficients_atoms_tableau (snd ` set as) t C" 
proof -
  let ?s = "assert_bound_loop as (init t)" 
  show ?thesis
  proof (cases "\<U> (assert_bound_loop as (init t))")
    case True
    from farkas_assert_bound_loop[OF this norm]
    show ?thesis by auto
  next
    case False
    from AssertAllState''_tableau_id[OF norm]
    have T: "\<T> ?s = t" unfolding init_tableau_id .
    from U have U: "\<U> (check ?s)" unfolding chk[symmetric] by simp
    show ?thesis
    proof (rule farkas_check[OF refl U False, unfolded T, OF _ norm])
      from AssertAllState''_precond[OF norm, unfolded Let_def] False
      show "\<Turnstile>\<^sub>n\<^sub>o\<^sub>l\<^sub>h\<^sub>s ?s" "\<diamond> ?s" "\<nabla> ?s" by blast+
      from AssertAllState''_index_valid[OF norm]
      show "index_valid (set as) ?s" .
    qed
  qed
qed

subsection \<open>Farkas' Lemma on Layer 3\<close>

text \<open>There is only a small difference between layers 3 and 4, namely that there is no 
  simplex algorithm (@{const assert_all_state}) on layer 3, but just a tableau and atoms.\<close>

text \<open>Hence, one task is to link the unsatisfiability flag 
  on layer 4 with unsatisfiability of the original tableau and atoms (layer 3). This can
  be done via the existing soundness results of the simplex algorithm.
  Moreover, we give an easy proof that the existence of Farkas coefficients for a tableau and 
  set of atoms implies unsatisfiability.\<close>

end

lemma farkas_coefficients_atoms_tableau_unsat: 
  assumes "farkas_coefficients_atoms_tableau as t C" 
  shows "\<nexists> v. v \<Turnstile>\<^sub>t t \<and> v \<Turnstile>\<^sub>a\<^sub>s as"
proof
  assume "\<exists> v. v \<Turnstile>\<^sub>t t \<and> v \<Turnstile>\<^sub>a\<^sub>s as"  
  then obtain v where *: "v \<Turnstile>\<^sub>t t \<and> v \<Turnstile>\<^sub>a\<^sub>s as" by auto
  then obtain p c where isleq: "(\<forall>(r,a) \<in> set C. a \<in> as \<and> is_leq_ns (r *R nsc_of_atom a) \<and> r \<noteq> 0)"
    and leq: "(\<Sum>(r,a) \<leftarrow> C. lec_of_nsc (r *R nsc_of_atom a)) = Leqc p c" 
    and cltz: "c < 0"
    and p0: "p\<lbrace>v\<rbrace> = 0"
    using assms farkas_coefficients_atoms_tableau_def by blast 
  have fa: "\<forall>(r,a) \<in> set C. v \<Turnstile>\<^sub>a a" using * isleq leq
      satisfies_atom_set_def by force
  {
    fix r a
    assume a: "(r,a) \<in> set C" 
    from a fa have va: "v \<Turnstile>\<^sub>a a" unfolding satisfies_atom_set_def by auto 
    hence v: "v \<Turnstile>\<^sub>n\<^sub>s (r *R nsc_of_atom a)" by (auto simp: nsc_of_atom sat_scale_rat_ns)
    from a isleq have "is_leq_ns (r *R nsc_of_atom a)" by auto
    from lec_of_nsc[OF this] v have "v \<Turnstile>\<^sub>l\<^sub>e lec_of_nsc (r *R nsc_of_atom a)" by blast
  } note v = this
  have "v \<Turnstile>\<^sub>l\<^sub>e Leqc p c" unfolding leq[symmetric]
    by (rule satisfies_sumlist_le_constraints, insert v, auto)
  then have "0 \<le> c" using p0 by auto
  then show False using cltz by auto
qed

text \<open>Next is the main result for layer~3: a tableau and a finite set of atoms are unsatisfiable
  if and only if there is a list of Farkas coefficients for the set of atoms and the tableau.\<close>

lemma farkas_coefficients_atoms_tableau: assumes norm: "\<triangle> t"
  and fin: "finite as"
shows "(\<exists> C. farkas_coefficients_atoms_tableau as t C) \<longleftrightarrow> (\<nexists> v. v \<Turnstile>\<^sub>t t \<and> v \<Turnstile>\<^sub>a\<^sub>s as)"
proof 
  from finite_list[OF fin] obtain bs where as: "as = set bs" by auto
  assume unsat: "\<nexists> v. v \<Turnstile>\<^sub>t t \<and> v \<Turnstile>\<^sub>a\<^sub>s as" 
  let ?as = "map (\<lambda> x. ((),x)) bs" 
  interpret AssertAllState''' init_state assert_bound_code check_code update_code
    eq_idx_for_lvar min_lvar_not_in_bounds min_rvar_incdec_eq pivot_and_update_code
    by (unfold_locales, auto simp: assert_bound_code_def check_code_def)
  let ?call = "assert_all t ?as" 
  have id: "snd ` set ?as = as" unfolding as by force
  from assert_all_sat[OF norm, of ?as, unfolded id] unsat
  obtain I where "?call = Inl I" by (cases ?call, auto)
  from this[unfolded assert_all_def Let_def]
  have "\<U> (assert_all_state_code t ?as)" 
    by (auto split: if_splits simp: assert_all_state_code_def)
  from farkas_assert_all_state[OF this[unfolded assert_all_state_code_def] norm, unfolded id]
  show "\<exists> C. farkas_coefficients_atoms_tableau as t C" .
qed (insert farkas_coefficients_atoms_tableau_unsat, auto)



subsection \<open>Farkas' Lemma on Layer 2\<close>

text \<open>The main difference between layers 2 and 3 is the introduction of slack-variables in layer 3
  via the preprocess-function. Our task here is to show that Farkas coefficients at layer 3 (where 
  slack-variables are used) can be converted into Farkas coefficients for layer 2 (before the
  preprocessing).\<close>


text \<open>We also need to adapt the previos notion of Farkas coefficients, which was used in 
  @{const farkas_coefficients_atoms_tableau}, for layer~2. At layer 3, Farkas coefficients
  are the coefficients in a linear combination of atoms that evaluates to an inequality of
  the form $p \leq c$, where $p$ is a linear polynomial, $c < 0$, and $t \models p = 0$ holds.
  At layer 2, the atoms are replaced by non-strict constraints where the left-hand side is a
  polynomial in the original variables, but the corresponding linear combination (with Farkas
  coefficients) evaluates directly to the inequality $0 \leq c$, with $c < 0$. The implication
  $t \models p = 0$ is no longer possible in this layer, since there is no tableau $t$, nor is it
  needed, since $p$ is $0$. Thus, the statement defining Farkas coefficients must be changed
  accordingly.\<close>

definition farkas_coefficients_ns where 
  "farkas_coefficients_ns ns C = (\<exists> c.
    (\<forall>(r, n) \<in> set C. n \<in> ns \<and> is_leq_ns (r *R n) \<and> r \<noteq> 0) \<and>
    (\<Sum>(r, n) \<leftarrow> C. lec_of_nsc (r *R n)) = Leqc 0 c \<and>
    c < 0)"

text \<open>The easy part is to prove that Farkas coefficients imply unsatisfiability.\<close>

lemma farkas_coefficients_ns_unsat: 
  assumes "farkas_coefficients_ns ns C" 
  shows "\<nexists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ns" 
proof
  assume "\<exists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ns"
  then obtain v where *: "v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ns" by auto
  obtain c where
    isleq: "(\<forall>(a,n) \<in> set C. n \<in> ns \<and> is_leq_ns (a *R n) \<and> a \<noteq> 0)" and
    leq: "(\<Sum>(a,n) \<leftarrow> C. lec_of_nsc (a *R n)) = Leqc 0 c" and
    cltz: "c < 0" using assms farkas_coefficients_ns_def by blast
  {
    fix a n
    assume n: "(a,n) \<in> set C" 
    from n * isleq have "v \<Turnstile>\<^sub>n\<^sub>s n" by auto
    hence v: "v \<Turnstile>\<^sub>n\<^sub>s (a *R n)" by (rule sat_scale_rat_ns)
    from n isleq have "is_leq_ns (a *R n)" by auto
    from lec_of_nsc[OF this] v 
    have "v \<Turnstile>\<^sub>l\<^sub>e lec_of_nsc (a *R n)" by blast
  } note v = this
  have "v \<Turnstile>\<^sub>l\<^sub>e Leqc 0 c" unfolding leq[symmetric]
    by (rule satisfies_sumlist_le_constraints, insert v, auto)
  then show False using cltz
    by (metis leD satisfiable_le_constraint.simps valuate_zero rel_of.simps(1))
qed

text \<open>In order to eliminate the need for a tableau, we require the notion of an arbitrary substitution
  on polynomials, where all variables can be replaced at once. The existing simplex formalization 
  provides only a function to replace one variable at a time.\<close>

definition subst_poly :: "(var \<Rightarrow> linear_poly) \<Rightarrow> linear_poly \<Rightarrow> linear_poly" where
  "subst_poly \<sigma> p = (\<Sum> x \<in> vars p. coeff p x *R \<sigma> x)"

lemma subst_poly_0[simp]: "subst_poly \<sigma> 0 = 0" unfolding subst_poly_def by simp

lemma valuate_subst_poly: "(subst_poly \<sigma> p) \<lbrace> v \<rbrace> = (p \<lbrace> (\<lambda> x. ((\<sigma> x) \<lbrace> v \<rbrace>)) \<rbrace>)"
  by (subst (2) linear_poly_sum, unfold subst_poly_def valuate_sum valuate_scaleRat, simp)

lemma subst_poly_add: "subst_poly \<sigma> (p + q) = subst_poly \<sigma> p + subst_poly \<sigma> q"
  by (rule linear_poly_eqI, unfold valuate_add valuate_subst_poly, simp)

fun subst_poly_lec :: "(var \<Rightarrow> linear_poly) \<Rightarrow> 'a le_constraint \<Rightarrow> 'a le_constraint" where
  "subst_poly_lec \<sigma> (Le_Constraint rel p c) = Le_Constraint rel (subst_poly \<sigma> p) c" 

lemma subst_poly_lec_0[simp]: "subst_poly_lec \<sigma> 0 = 0" unfolding zero_le_constraint_def by simp

lemma subst_poly_lec_add: "subst_poly_lec \<sigma> (c1 + c2) = subst_poly_lec \<sigma> c1 + subst_poly_lec \<sigma> c2" 
  by (cases c1; cases c2, auto simp: subst_poly_add)

lemma subst_poly_lec_sum_list: "subst_poly_lec \<sigma> (sum_list ps) = sum_list (map (subst_poly_lec \<sigma>) ps)" 
  by (induct ps, auto simp: subst_poly_lec_add)

lemma subst_poly_lp_monom[simp]: "subst_poly \<sigma> (lp_monom r x) = r *R \<sigma> x"
  unfolding subst_poly_def by (simp add: vars_lp_monom)

lemma subst_poly_scaleRat: "subst_poly \<sigma> (r *R p) = r *R (subst_poly \<sigma> p)"
  by (rule linear_poly_eqI, unfold valuate_scaleRat valuate_subst_poly, simp)

text \<open>We need several auxiliary properties of the preprocess-function which are not present
  in the simplex formalization.\<close>

lemma Tableau_is_monom_preprocess':
  assumes "(x, p) \<in> set (Tableau (preprocess' cs start))"
  shows "\<not> is_monom p"
  using assms 
  by(induction cs start rule: preprocess'.induct)
    (auto simp add: Let_def split: if_splits option.splits)

lemma preprocess'_atoms_to_constraints': assumes "preprocess' cs start = S" 
  shows "set (Atoms S) \<subseteq> {(i,qdelta_constraint_to_atom c v) | i c v. (i,c) \<in> set cs \<and> 
     (\<not> is_monom (poly c) \<longrightarrow> Poly_Mapping S (poly c) = Some v)}"
  unfolding assms(1)[symmetric]
  by (induct cs start rule: preprocess'.induct, auto simp: Let_def split: option.splits, force+) 

lemma monom_of_atom_coeff:
  assumes "is_monom (poly ns)" "a = qdelta_constraint_to_atom ns v"
  shows "(monom_coeff (poly ns)) *R nsc_of_atom a = ns"
  using assms is_monom_monom_coeff_not_zero 
  by(cases a; cases ns)
    (auto split: atom.split ns_constraint.split simp add: monom_poly_assemble field_simps)

text \<open>The next lemma provides the functionality that is required to convert an
  atom back to a non-strict constraint, i.e., it is a kind of inverse of the preprocess-function.\<close>

lemma preprocess'_atoms_to_constraints: assumes S: "preprocess' cs start = S" 
  and start: "start = start_fresh_variable cs" 
  and ns: "ns = (case a of Leq v c \<Rightarrow> LEQ_ns q c | Geq v c \<Rightarrow> GEQ_ns q c)" 
  and "a \<in> snd ` set (Atoms S)" 
shows "(atom_var a \<notin> fst ` set (Tableau S) \<longrightarrow> (\<exists> r. r \<noteq> 0 \<and> r *R nsc_of_atom a \<in> snd ` set cs))
    \<and>  ((atom_var a, q) \<in> set (Tableau S) \<longrightarrow> ns \<in> snd ` set cs)" 
proof -
  let ?S = "preprocess' cs start" 
  from assms(4) obtain i where ia: "(i,a) \<in> set (Atoms S)" by auto
  with preprocess'_atoms_to_constraints'[OF assms(1)] obtain c v 
    where a: "a = qdelta_constraint_to_atom c v" and c: "(i,c) \<in> set cs" 
      and nmonom: "\<not> is_monom (poly c) \<Longrightarrow> Poly_Mapping S (poly c) = Some v" by blast
  hence c': "c \<in> snd ` set cs" by force
  let ?p = "poly c" 
  show ?thesis
  proof (cases "is_monom ?p")
    case True
    hence av: "atom_var a = monom_var ?p" unfolding a by (cases c, auto)
    from Tableau_is_monom_preprocess'[of _ ?p cs start] True 
    have "(x, ?p) \<notin> set (Tableau ?S)" for x by blast
    {
      assume "(atom_var a, q) \<in> set (Tableau S)" 
      hence "(monom_var ?p, q) \<in> set (Tableau S)" unfolding av by simp
      hence "monom_var ?p \<in> lvars (Tableau S)" unfolding lvars_def by force
      from lvars_tableau_ge_start[rule_format, OF this[folded S]]
      have "monom_var ?p \<ge> start" unfolding S .
      moreover have "monom_var ?p \<in> vars_constraints (map snd cs)" using True c
        by (auto intro!: bexI[of _ "(i,c)"] simp: monom_var_in_vars)
      ultimately have False using start_fresh_variable_fresh[of cs, folded start] by force
    } 
    moreover 
    from monom_of_atom_coeff[OF True a] True
    have "\<exists>r. r \<noteq> 0 \<and> r *R nsc_of_atom a = c" 
      by (intro exI[of _ "monom_coeff ?p"], auto, cases a, auto)
    ultimately show ?thesis using c' by auto
  next
    case False
    hence av: "atom_var a = v" unfolding a by (cases c, auto)
    from nmonom[OF False] have "Poly_Mapping S ?p = Some v" .
    from preprocess'_Tableau_Poly_Mapping_Some[OF this[folded S]]
    have tab: "(atom_var a, ?p) \<in> set (Tableau (preprocess' cs start))" unfolding av by simp
    hence "atom_var a \<in> fst ` set (Tableau S)" unfolding S by force
    moreover
    {
      assume "(atom_var a, q) \<in> set (Tableau S)"
      from tab this have qp: "q = ?p" unfolding S using lvars_distinct[of cs start, unfolded S lhs_def]
        by (simp add: case_prod_beta' eq_key_imp_eq_value)
      have "ns = c" unfolding ns qp using av a False by (cases c, auto)
      hence "ns \<in> snd ` set cs" using c' by blast
    }
    ultimately show ?thesis by blast
  qed
qed

text \<open>Next follows the major technical lemma of this part, 
  namely that Farkas coefficients on layer~3 for preprocessed constraints can
  be converted into Farkas coefficients on layer~2.\<close>

lemma farkas_coefficients_preprocess': 
  assumes pp: "preprocess' cs (start_fresh_variable cs) = S" and
    ft: "farkas_coefficients_atoms_tableau (snd ` set (Atoms S)) (Tableau S) C"
  shows "\<exists> C. farkas_coefficients_ns (snd ` set cs) C"
proof -
  note ft[unfolded farkas_coefficients_atoms_tableau_def]
  obtain p c where 0: "\<forall> (r,a) \<in> set C. a \<in> snd ` set (Atoms S) \<and> is_leq_ns (r *R nsc_of_atom a) \<and> r \<noteq> 0"
    "(\<Sum>(r,a)\<leftarrow>C. lec_of_nsc (r *R nsc_of_atom a)) = Leqc p c"
    "c < 0"
    "\<And>v :: QDelta valuation. v \<Turnstile>\<^sub>t Tableau S \<Longrightarrow> p \<lbrace> v \<rbrace> = 0"
    using ft unfolding farkas_coefficients_atoms_tableau_def by blast
  note 0 = 0(1)[rule_format, of "(a, b)" for a b, unfolded split] 0(2-)
  let ?T = "Tableau S"
  define \<sigma> :: "var \<Rightarrow> linear_poly" where "\<sigma> = (\<lambda> x. case map_of ?T x of Some p \<Rightarrow> p | None \<Rightarrow> lp_monom 1 x)"
  let ?P = "(\<lambda>r a s ns. ns \<in> (snd ` set cs) \<and> is_leq_ns (s *R ns) \<and> s \<noteq> 0 \<and>
      subst_poly_lec \<sigma> (lec_of_nsc (r *R nsc_of_atom a)) = lec_of_nsc (s *R ns))"
  have "\<exists>s ns. ?P r a s ns" if ra: "(r,a) \<in> set C" for r a
  proof -
    have a: "a \<in> snd ` set (Atoms S)"
      using ra 0 by force
    from 0 ra have is_leq: "is_leq_ns (r *R nsc_of_atom a)" and r0: "r \<noteq> 0" by auto
    let ?x = "atom_var a" 
    show ?thesis
    proof (cases "map_of ?T ?x")
      case (Some q)
      hence \<sigma>: "\<sigma> ?x = q" unfolding \<sigma>_def by auto
      from Some have xqT: "(?x, q) \<in> set ?T" by (rule map_of_SomeD)
      define ns where "ns = (case a of Leq v c \<Rightarrow> LEQ_ns q c
                                     | Geq v c \<Rightarrow> GEQ_ns q c)"
      from preprocess'_atoms_to_constraints[OF pp refl ns_def a] xqT
      have ns_mem: "ns \<in> snd ` set cs" by blast
      have id: "subst_poly_lec \<sigma> (lec_of_nsc (r *R nsc_of_atom a))
               = lec_of_nsc (r *R ns)" using is_leq \<sigma>
        by (cases a, auto simp: ns_def subst_poly_scaleRat)
      from id is_leq \<sigma> have is_leq: "is_leq_ns (r *R ns)" by (cases a, auto simp: ns_def)  
      show ?thesis by (intro exI[of _ r] exI[of _ ns] conjI ns_mem id is_leq conjI r0)
    next
      case None
      hence "?x \<notin> fst ` set ?T" by (meson map_of_eq_None_iff)
      from preprocess'_atoms_to_constraints[OF pp refl refl a] this
      obtain rr where rr: "rr *R nsc_of_atom a \<in> (snd ` set cs)" and rr0: "rr \<noteq> 0" 
        by blast
      from None have \<sigma>: "\<sigma> ?x = lp_monom 1 ?x" unfolding \<sigma>_def by simp
      define ns where "ns = rr *R nsc_of_atom a"
      define s where "s = r / rr"
      from rr0 r0 have s0: "s \<noteq> 0" unfolding s_def by auto
      from is_leq \<sigma>
      have "subst_poly_lec \<sigma> (lec_of_nsc (r *R nsc_of_atom a)) 
        = lec_of_nsc (r *R nsc_of_atom a)"
        by (cases a, auto simp: subst_poly_scaleRat)
      moreover have "r *R nsc_of_atom a = s *R ns" unfolding ns_def s_def
          scaleRat_scaleRat_ns_constraint[OF rr0] using rr0 by simp
      ultimately have "subst_poly_lec \<sigma> (lec_of_nsc (r *R nsc_of_atom a))
            = lec_of_nsc (s *R ns)" "is_leq_ns (s *R ns)" using is_leq by auto
      then show ?thesis
        unfolding ns_def using rr s0 by blast
    qed
  qed
  hence "\<forall> ra. \<exists> s ns. (fst ra, snd ra) \<in> set C \<longrightarrow> ?P (fst ra) (snd ra) s ns" by blast
  from choice[OF this] obtain s where s: "\<forall> ra. \<exists> ns. (fst ra, snd ra) \<in> set C \<longrightarrow> ?P (fst ra) (snd ra) (s ra) ns" by blast
  from choice[OF this] obtain ns where ns: "\<And> r a. (r,a) \<in> set C \<Longrightarrow> ?P r a (s (r,a)) (ns (r,a))" by force
  define NC where "NC = map (\<lambda>(r,a). (s (r,a), ns (r,a))) C"
  have "(\<Sum>(s, ns)\<leftarrow>map (\<lambda>(r,a). (s (r,a), ns (r,a))) C'. lec_of_nsc (s *R ns)) =
        (\<Sum>(r, a)\<leftarrow>C'. subst_poly_lec \<sigma> (lec_of_nsc (r *R nsc_of_atom a)))"
    if "set C' \<subseteq> set C" for C'
    using that proof (induction C')
    case Nil
    then show ?case by simp
  next
    case (Cons a C')
    have "(\<Sum>x\<leftarrow>a # C'. lec_of_nsc (s x *R ns x)) = 
          lec_of_nsc (s a *R ns a) + (\<Sum>x\<leftarrow>C'. lec_of_nsc (s x *R ns x))"
      by simp
    also have "(\<Sum>x\<leftarrow>C'. lec_of_nsc (s x *R ns x)) = (\<Sum>(r, a)\<leftarrow>C'. subst_poly_lec \<sigma> (lec_of_nsc (r *R nsc_of_atom a)))"
      using Cons by (auto simp add: case_prod_beta' comp_def)
    also have "lec_of_nsc (s a *R ns a) = subst_poly_lec \<sigma> (lec_of_nsc (fst a *R nsc_of_atom (snd a)))"
    proof -
      have "a \<in> set C"
        using Cons by simp
      then show ?thesis
        using ns by auto
    qed
    finally show ?case
      by (auto simp add: case_prod_beta' comp_def)
  qed
  also have "(\<Sum>(r, a)\<leftarrow>C. subst_poly_lec \<sigma> (lec_of_nsc (r *R nsc_of_atom a)))
             = subst_poly_lec \<sigma> (\<Sum>(r, a)\<leftarrow>C. (lec_of_nsc (r *R nsc_of_atom a)))"
    by (auto simp add: subst_poly_lec_sum_list case_prod_beta' comp_def)
  also have "(\<Sum>(r, a)\<leftarrow>C. (lec_of_nsc (r *R nsc_of_atom a))) = Leqc p c"
    using 0 by blast
  also have "subst_poly_lec \<sigma> (Leqc p c) = Leqc (subst_poly \<sigma> p) c" by simp
  also have "subst_poly \<sigma> p = 0" 
  proof (rule all_valuate_zero)
    fix v :: "QDelta valuation" 
    have "(subst_poly \<sigma> p) \<lbrace> v \<rbrace> = (p \<lbrace> \<lambda>x. ((\<sigma> x) \<lbrace> v \<rbrace>) \<rbrace>)" by (rule valuate_subst_poly)
    also have "\<dots> = 0" 
    proof (rule 0(4))
      have "(\<sigma> a) \<lbrace> v \<rbrace> = (q \<lbrace> \<lambda>x. ((\<sigma> x) \<lbrace> v \<rbrace>) \<rbrace>)" if "(a, q) \<in> set (Tableau S)" for a q
      proof -
        have "distinct (map fst ?T)"
          using normalized_tableau_preprocess' assms unfolding normalized_tableau_def lhs_def
          by (auto simp add: case_prod_beta')
        then have 0: "\<sigma> a = q"
          unfolding \<sigma>_def using that by auto
        have "q \<lbrace> v \<rbrace> = (q \<lbrace> \<lambda>x. ((\<sigma> x) \<lbrace> v \<rbrace>) \<rbrace>)"
        proof -
          have "vars q \<subseteq> rvars ?T"
            unfolding rvars_def using that by force
          moreover have "(\<sigma> x) \<lbrace> v \<rbrace> = v x" if "x \<in> rvars ?T" for x
          proof -
            have "x \<notin> lvars (Tableau S)"
              using that normalized_tableau_preprocess' assms
              unfolding normalized_tableau_def by blast
            then have "x \<notin> fst ` set (Tableau S)"
              unfolding lvars_def by force
            then have "map_of ?T x = None"
              using map_of_eq_None_iff by metis
            then have "\<sigma> x = lp_monom 1 x"
              unfolding \<sigma>_def by auto
            also have "(lp_monom 1 x) \<lbrace> v \<rbrace> = v x"
              by auto
            finally show ?thesis .
          qed
          ultimately show ?thesis
            by (auto intro!: valuate_depend)
        qed
        then show ?thesis
          using 0 by blast
      qed
      then show "(\<lambda>x. ((\<sigma> x) \<lbrace> v \<rbrace>)) \<Turnstile>\<^sub>t ?T" 
        using 0 by (auto simp add: satisfies_tableau_def satisfies_eq_def)
    qed
    finally show "(subst_poly \<sigma> p) \<lbrace> v \<rbrace> = 0" .
  qed
  finally have "(\<Sum>(s, n)\<leftarrow>NC. lec_of_nsc (s *R n)) = Le_Constraint Leq_Rel 0 c"
    unfolding NC_def by blast
  moreover have "ns (r,a) \<in> snd ` set cs" "is_leq_ns (s (r, a) *R ns (r, a))" "s (r, a) \<noteq> 0" if "(r, a) \<in> set C" for r a
    using ns that by force+
  ultimately have "farkas_coefficients_ns (snd ` set cs) NC"
    unfolding farkas_coefficients_ns_def NC_def using 0 by force
  then show ?thesis
    by blast
qed

lemma preprocess'_unsat_indexD: "i \<in> set (UnsatIndices (preprocess' ns j)) \<Longrightarrow> 
  \<exists> c. poly c = 0 \<and> \<not> zero_satisfies c \<and> (i,c) \<in> set ns" 
  by (induct ns j rule: preprocess'.induct, auto simp: Let_def split: if_splits option.splits)

lemma preprocess'_unsat_index_farkas_coefficients_ns: 
  assumes "i \<in> set (UnsatIndices (preprocess' ns j))" 
  shows "\<exists> C. farkas_coefficients_ns (snd ` set ns) C" 
proof -
  from preprocess'_unsat_indexD[OF assms]
  obtain c where contr: "poly c = 0" "\<not> zero_satisfies c" and mem: "(i,c) \<in> set ns" by auto
  from mem have mem: "c \<in> snd ` set ns" by force
  let ?c = "ns_constraint_const c" 
  define r where "r = (case c of LEQ_ns _ _ \<Rightarrow> 1 | _ \<Rightarrow> (-1 :: rat))" 
  define d where "d = (case c of LEQ_ns _ _ \<Rightarrow> ?c | _ \<Rightarrow> - ?c)" 
  have [simp]: "(- x < 0) = (0 < x)" for x :: QDelta using uminus_less_lrv[of _ 0] by simp
  show ?thesis unfolding farkas_coefficients_ns_def 
    by (intro exI[of _ "[(r,c)]"] exI[of _ d], insert mem contr, cases "c", 
        auto simp: r_def d_def)
qed

text \<open>The combination of the previous results easily provides the main result of this section:
  a finite set of non-strict constraints on layer~2 is unsatisfiable if and only if there are Farkas coefficients.
  Again, here we use results from the simplex formalization, namely soundness of the preprocess-function.\<close>

lemma farkas_coefficients_ns: assumes "finite (ns :: QDelta ns_constraint set)" 
  shows "(\<exists> C. farkas_coefficients_ns ns C) \<longleftrightarrow> (\<nexists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ns)" 
proof 
  assume "\<exists> C. farkas_coefficients_ns ns C" 
  from farkas_coefficients_ns_unsat this show "\<nexists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ns" by blast
next
  assume unsat: "\<nexists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ns" 
  from finite_list[OF assms] obtain nsl where ns: "ns = set nsl" by auto
  let ?cs = "map (Pair ()) nsl" 
  obtain I t ias where part1: "preprocess_part_1 ?cs = (t,ias,I)" by (cases "preprocess_part_1 ?cs", auto)
  let ?as = "snd ` set ias" 
  let ?s = "start_fresh_variable ?cs" 
  have fin: "finite ?as" by auto
  have id: "ias = Atoms (preprocess' ?cs ?s)" "t = Tableau (preprocess' ?cs ?s)" 
    "I = UnsatIndices (preprocess' ?cs ?s)" 
    using part1 unfolding preprocess_part_1_def Let_def by auto
  have norm: "\<triangle> t" using normalized_tableau_preprocess'[of ?cs] unfolding  id .
  {
    fix v
    assume "v \<Turnstile>\<^sub>a\<^sub>s ?as" "v \<Turnstile>\<^sub>t t" 
    from preprocess'_sat[OF this[unfolded id], folded id] unsat[unfolded ns] 
    have "set I \<noteq> {}" by auto
    then obtain i where "i \<in> set I" using all_not_in_conv by blast
    from preprocess'_unsat_index_farkas_coefficients_ns[OF this[unfolded id]]
    have "\<exists>C. farkas_coefficients_ns (snd ` set ?cs) C" by simp
  }    
  with farkas_coefficients_atoms_tableau[OF norm fin]
  obtain C where "farkas_coefficients_atoms_tableau ?as t C
     \<or> (\<exists>C. farkas_coefficients_ns (snd ` set ?cs) C)" by blast
  from farkas_coefficients_preprocess'[of ?cs, OF refl] this
  have "\<exists> C. farkas_coefficients_ns (snd ` set ?cs) C" 
    using part1 unfolding preprocess_part_1_def Let_def by auto
  also have "snd ` set ?cs = ns" unfolding ns by force
  finally show "\<exists> C. farkas_coefficients_ns ns C" .
qed

subsection \<open>Farkas' Lemma on Layer 1\<close>

text \<open>The main difference of layers 1 and 2 is the restriction to non-strict constraints via delta-rationals.
  Since we now work with another constraint type, @{type constraint}, we again need translations into
  linear inequalities of type @{type le_constraint}. Moreover, we also need to define scaling of constraints
  where flipping the comparison sign may be required.\<close>

fun is_le :: "constraint \<Rightarrow> bool" where
  "is_le (LT _ _) = True" 
| "is_le (LEQ _ _) = True" 
| "is_le _ = False" 

fun lec_of_constraint where
  "lec_of_constraint (LEQ p c) = (Le_Constraint Leq_Rel p c)"
| "lec_of_constraint (LT p c) = (Le_Constraint Lt_Rel p c)" 

lemma lec_of_constraint: 
  assumes "is_le c"
  shows "(v \<Turnstile>\<^sub>l\<^sub>e (lec_of_constraint c)) \<longleftrightarrow> (v \<Turnstile>\<^sub>c c)"
  using assms by (cases c, auto)

instantiation constraint :: scaleRat
begin
fun scaleRat_constraint :: "rat \<Rightarrow> constraint \<Rightarrow> constraint" where
  "scaleRat_constraint r cc = (if r = 0 then LEQ 0 0 else 
  (case cc of 
    LEQ p c \<Rightarrow>
     (if (r < 0) then GEQ (r *R p) (r *R c) else LEQ (r *R p) (r *R c))
  | LT p c \<Rightarrow>
     (if (r < 0) then GT (r *R p) (r *R c) else LT (r *R p) (r *R c))
  | GEQ p c \<Rightarrow> 
    (if (r > 0) then GEQ (r *R p) (r *R c) else LEQ (r *R p) (r *R c))
  | GT p c \<Rightarrow> 
    (if (r > 0) then GT (r *R p) (r *R c) else LT (r *R p) (r *R c))
  | LTPP p q \<Rightarrow>
     (if (r < 0) then GT (r *R (p - q)) 0 else LT (r *R (p - q)) 0)
  | LEQPP p q \<Rightarrow>
     (if (r < 0) then GEQ (r *R (p - q)) 0 else LEQ (r *R (p - q)) 0)
  | GTPP p q \<Rightarrow>
     (if (r > 0) then GT (r *R (p - q)) 0 else LT (r *R (p - q)) 0)
  | GEQPP p q \<Rightarrow>
     (if (r > 0) then GEQ (r *R (p - q)) 0 else LEQ (r *R (p - q)) 0)
  | EQPP p q \<Rightarrow> LEQ (r *R (p - q)) 0 \<comment> \<open>We do not keep equality, since the aim is 
        to convert the scaled constraints into inequalities, which will then be summed up.\<close>
  | EQ p c \<Rightarrow> LEQ (r *R p) (r *R c) 
))"

instance ..
end

lemma sat_scale_rat: assumes "(v :: rat valuation) \<Turnstile>\<^sub>c c"
  shows "v \<Turnstile>\<^sub>c (r *R c)"
proof -
  have "r < 0 \<or> r = 0 \<or> r > 0" by auto
  then show ?thesis using assms by (cases c, auto simp: right_diff_distrib 
        valuate_minus valuate_scaleRat scaleRat_leq1 scaleRat_leq2 valuate_zero)
qed

text \<open>In the following definition of Farkas coefficients (for layer 1), the main difference to
  @{const farkas_coefficients_ns} is that the linear combination evaluates either to
  a strict inequality where the constant must be non-positive, or to a non-strict inequality where
  the constant must be negative.\<close>

definition farkas_coefficients where 
  "farkas_coefficients cs C = (\<exists> d rel. 
    (\<forall> (r,c) \<in> set C. c \<in> cs \<and> is_le (r *R c) \<and> r \<noteq> 0) \<and>
    (\<Sum> (r,c) \<leftarrow> C. lec_of_constraint (r *R c)) = Le_Constraint rel 0 d \<and> 
    (rel = Leq_Rel \<and> d < 0 \<or> rel = Lt_Rel \<and> d \<le> 0))"

text \<open>Again, the existence Farkas coefficients immediately implies unsatisfiability.\<close>

lemma farkas_coefficients_unsat: 
  assumes "farkas_coefficients cs C" 
  shows "\<nexists> v. v \<Turnstile>\<^sub>c\<^sub>s cs" 
proof
  assume "\<exists> v. v \<Turnstile>\<^sub>c\<^sub>s cs"
  then obtain v where *: "v \<Turnstile>\<^sub>c\<^sub>s cs" by auto
  obtain d rel where
    isleq: "(\<forall>(r,c) \<in> set C. c \<in> cs \<and> is_le (r *R c) \<and> r \<noteq> 0)" and
    leq: "(\<Sum> (r,c) \<leftarrow> C. lec_of_constraint (r *R c)) = Le_Constraint rel 0 d" and
    choice: "rel = Lt_Rel \<and> d \<le> 0 \<or> rel = Leq_Rel \<and> d < 0" using assms farkas_coefficients_def by blast
  {
    fix r c
    assume c: "(r,c) \<in> set C" 
    from c * isleq have "v \<Turnstile>\<^sub>c c" by auto
    hence v: "v \<Turnstile>\<^sub>c (r *R c)" by (rule sat_scale_rat)
    from c isleq have "is_le (r *R c)" by auto
    from lec_of_constraint[OF this] v 
    have "v \<Turnstile>\<^sub>l\<^sub>e lec_of_constraint (r *R c)" by blast
  } note v = this
  have "v \<Turnstile>\<^sub>l\<^sub>e Le_Constraint rel 0 d" unfolding leq[symmetric]
    by (rule satisfies_sumlist_le_constraints, insert v, auto)
  then show False using choice
    by (cases rel, auto simp: valuate_zero)
qed

text \<open>Now follows the difficult implication. 
  The major part is proving that the translation @{const constraint_to_qdelta_constraint} 
  preserves the existence of Farkas coefficients via pointwise compatibility of the sum.
  Here, compatibility links a strict or non-strict inequality from the input constraint to
  a translated non-strict inequality over delta-rationals.\<close>

fun compatible_cs where 
  "compatible_cs (Le_Constraint Leq_Rel p c) (Le_Constraint Leq_Rel q d) = (q = p \<and> d = QDelta c 0)" 
| "compatible_cs (Le_Constraint Lt_Rel p c) (Le_Constraint Leq_Rel q d) = (q = p \<and> qdfst d = c)" 
| "compatible_cs _ _ = False" 

lemma compatible_cs_0_0: "compatible_cs 0 0" by code_simp

lemma compatible_cs_plus: "compatible_cs c1 d1 \<Longrightarrow> compatible_cs c2 d2 \<Longrightarrow> compatible_cs (c1 + c2) (d1 + d2)" 
  by (cases c1; cases d1; cases c2; cases d2; cases "lec_rel c1"; cases "lec_rel d1"; cases "lec_rel c2"; 
      cases "lec_rel d2"; auto simp: plus_QDelta_def)

lemma unsat_farkas_coefficients: assumes "\<nexists> v. v \<Turnstile>\<^sub>c\<^sub>s cs" 
  and fin: "finite cs" 
shows "\<exists> C. farkas_coefficients cs C" 
proof -
  from finite_list[OF fin] obtain csl where cs: "cs = set csl" by blast
  let ?csl = "map (Pair ()) csl" 
  let ?ns = "(snd ` set (to_ns ?csl))" 
  let ?nsl = "concat (map constraint_to_qdelta_constraint csl)" 
  have id: "snd ` set ?csl = cs" unfolding cs by force
  have id2: "?ns = set ?nsl" unfolding to_ns_def set_concat by force
  from SolveExec'Default.to_ns_sat[of ?csl, unfolded id] assms
  have unsat: "\<nexists> v. \<langle>v\<rangle> \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ?ns" by metis
  have fin: "finite ?ns" by auto
  have "\<nexists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ?ns" 
  proof
    assume "\<exists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ?ns" 
    then obtain v where model: "v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ?ns" by blast
    let ?v = "Mapping.Mapping (\<lambda> x. Some (v x))" 
    have "v = \<langle>?v\<rangle>" by (intro ext, auto simp: map2fun_def Mapping.lookup.abs_eq) 
    from model this unsat show False by metis
  qed    
  from farkas_coefficients_ns[OF fin] this id2 obtain N where
    farkas: "farkas_coefficients_ns (set ?nsl) N" by metis
  from this[unfolded farkas_coefficients_ns_def]
  obtain d where 
    is_leq: "\<And> a n. (a,n) \<in> set N \<Longrightarrow> n \<in> set ?nsl \<and> is_leq_ns (a *R n) \<and> a \<noteq> 0" and 
    sum: "(\<Sum>(a,n)\<leftarrow>N. lec_of_nsc (a *R n)) = Le_Constraint Leq_Rel 0 d" and
    d0: "d < 0" by blast
  let ?prop = "\<lambda> NN C. (\<forall> (a,c) \<in> set C. c \<in> cs \<and> is_le (a *R c) \<and> a \<noteq> 0)
      \<and> compatible_cs (\<Sum> (a,c) \<leftarrow> C. lec_of_constraint (a *R c)) 
          (\<Sum>(a,n)\<leftarrow>NN. lec_of_nsc (a *R n))" 
  have "set NN \<subseteq> set N \<Longrightarrow> \<exists> C. ?prop NN C" for NN
  proof (induct NN)
    case Nil
    have "?prop Nil Nil" by (simp add: compatible_cs_0_0)
    thus ?case by blast
  next
    case (Cons an NN)
    obtain a n where an: "an = (a,n)" by force
    from Cons an obtain C where IH: "?prop NN C" and n: "(a,n) \<in> set N" by auto
    have compat_CN: "compatible_cs (\<Sum>(f, c)\<leftarrow>C. lec_of_constraint (f *R c)) 
      (\<Sum>(a,n)\<leftarrow>NN. lec_of_nsc (a *R n))" 
      using IH by blast
    from n is_leq obtain c where c: "c \<in> cs" and nc: "n \<in> set (constraint_to_qdelta_constraint c)" 
      unfolding cs by force
    from is_leq[OF n] have is_leq: "is_leq_ns (a *R n) \<and> a \<noteq> 0" by blast
    have is_less: "is_le (a *R c)" and 
      a0: "a \<noteq> 0" and
      compat_cn: "compatible_cs (lec_of_constraint (a *R c)) (lec_of_nsc (a *R n))" 
      by (atomize(full), cases c, insert is_leq nc, auto simp: QDelta_0_0 scaleRat_QDelta_def qdsnd_0 qdfst_0)
    let ?C = "Cons (a, c) C" 
    let ?N = "Cons (a, n) NN" 
    have "?prop ?N ?C" unfolding an
    proof (intro conjI)
      show "\<forall> (a,c) \<in> set ?C. c \<in> cs \<and> is_le (a *R c) \<and> a \<noteq> 0" using IH is_less a0 c by auto
      show "compatible_cs (\<Sum>(a, c)\<leftarrow>?C. lec_of_constraint (a *R c)) (\<Sum>(a,n)\<leftarrow>?N. lec_of_nsc (a *R n))" 
        using compatible_cs_plus[OF compat_cn compat_CN] by simp
    qed
    thus ?case unfolding an by blast
  qed
  from this[OF subset_refl, unfolded sum]
  obtain C where 
    is_less: "(\<forall>(a, c)\<in>set C. c \<in> cs \<and> is_le (a *R c) \<and> a \<noteq> 0)" and
    compat: "compatible_cs (\<Sum>(f, c)\<leftarrow>C. lec_of_constraint (f *R c)) (Le_Constraint Leq_Rel 0 d)" 
    (is "compatible_cs ?sum _")
    by blast
  obtain rel p e where "?sum = Le_Constraint rel p e" by (cases ?sum)
  with compat have sum: "?sum = Le_Constraint rel 0 e" by (cases rel, auto)
  have e: "(rel = Leq_Rel \<and> e < 0 \<or> rel = Lt_Rel \<and> e \<le> 0)" using compat[unfolded sum] d0
    by (cases rel, auto simp: less_QDelta_def qdfst_0 qdsnd_0) 
  show ?thesis unfolding farkas_coefficients_def
    by (intro exI conjI, rule is_less, rule sum, insert e, auto)
qed

text \<open>Finally we can prove on layer 1 that a finite set of constraints is 
  unsatisfiable if and only if there are Farkas coefficients.\<close>

lemma farkas_coefficients: assumes "finite cs" 
  shows "(\<exists> C. farkas_coefficients cs C) \<longleftrightarrow> (\<nexists> v. v \<Turnstile>\<^sub>c\<^sub>s cs)" 
  using farkas_coefficients_unsat unsat_farkas_coefficients[OF _ assms] by blast

section \<open>Corollaries from the Literature\<close>

text \<open>In this section, we convert the previous variations of Farkas' Lemma into more 
  well-known forms of this result.
  Moreover, instead of referring to the various constraint types of the simplex formalization, we
  now speak solely about constraints of type @{type le_constraint}.\<close>

subsection \<open>Farkas' Lemma on Delta-Rationals\<close>

text \<open>We start with Lemma~2 of \cite{Bromberger2017}, a
  variant of Farkas' Lemma for delta-rationals. To be more precise, it states
  that a set of non-strict inequalities over delta-rationals is unsatisfiable
  if and only if there is a linear combination of the inequalities that results
  in a trivial unsatisfiable constraint $0 < const$ for some negative constant $const$.
  We can easily prove this statement via the lemma @{thm [source] farkas_coefficients_ns} 
  and some conversions between the 
  different constraint types.\<close>

lemma Farkas'_Lemma_Delta_Rationals: fixes cs :: "QDelta le_constraint set"
  assumes only_non_strict: "lec_rel ` cs \<subseteq> {Leq_Rel}"  
    and fin: "finite cs" 
  shows "(\<nexists> v. \<forall> c \<in> cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> 
       (\<exists> C const. (\<forall> (r, c) \<in> set C. r > 0 \<and> c \<in> cs)
         \<and> (\<Sum> (r,c) \<leftarrow> C. Leqc (r *R lec_poly c) (r *R lec_const c)) = Leqc 0 const
         \<and> const < 0)" 
    (is "?lhs = ?rhs")
proof -
  {
    fix c
    assume "c \<in> cs" 
    with only_non_strict have "lec_rel c = Leq_Rel" by auto
    then have "\<exists> p const. c = Leqc p const" by (cases c, auto)
  } note leqc = this
  let ?to_ns = "\<lambda> c. LEQ_ns (lec_poly c) (lec_const c)" 
  let ?ns = "?to_ns ` cs" 
  from fin have fin: "finite ?ns" by auto
  have "v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ?ns \<longleftrightarrow> (\<forall> c \<in> cs. v \<Turnstile>\<^sub>l\<^sub>e c)" for v using leqc by fastforce
  hence "?lhs = (\<nexists> v. v \<Turnstile>\<^sub>n\<^sub>s\<^sub>s ?ns)" by simp
  also have "\<dots> = (\<exists>C. farkas_coefficients_ns ?ns C)" unfolding farkas_coefficients_ns[OF fin] ..
  also have "\<dots> = ?rhs" 
  proof
    assume "\<exists> C. farkas_coefficients_ns ?ns C" 
    then obtain C const where is_leq: "\<forall> (s, n) \<in> set C. n \<in> ?ns \<and> is_leq_ns (s *R n) \<and> s \<noteq> 0" 
      and sum: "(\<Sum>(s, n)\<leftarrow>C. lec_of_nsc (s *R n)) = Leqc 0 const"
      and c0: "const < 0" unfolding farkas_coefficients_ns_def by blast
    let ?C = "map (\<lambda> (s,n). (s,lec_of_nsc n)) C" 
    show ?rhs 
    proof (intro exI[of _ ?C] exI[of _ const] conjI c0, unfold sum[symmetric] map_map o_def set_map, 
        intro ballI, clarify)
      {
        fix s n 
        assume sn: "(s, n) \<in> set C" 
        with is_leq
        have n_ns: "n \<in> ?ns" and is_leq: "is_leq_ns (s *R n)" "s \<noteq> 0" by force+
        from n_ns obtain c where c: "c \<in> cs" and n: "n = LEQ_ns (lec_poly c) (lec_const c)" by auto
        with leqc[OF c] obtain p d where cs: "Leqc p d \<in> cs" and n: "n = LEQ_ns p d" by auto
        from is_leq[unfolded n] have s0: "s > 0" by (auto split: if_splits) 
        let ?n = "lec_of_nsc n" 
        from cs n have mem: "?n \<in> cs" by auto
        show "0 < s \<and> ?n \<in> cs" using s0 mem by blast        
        have "Leqc (s *R lec_poly ?n) (s *R lec_const ?n) = lec_of_nsc (s *R n)" 
          unfolding n using s0 by simp
      } note id = this
      show "(\<Sum>x\<leftarrow>C. case case x of (s, n) \<Rightarrow> (s, lec_of_nsc n) of
             (r, c) \<Rightarrow> Leqc (r *R lec_poly c) (r *R lec_const c)) =
             (\<Sum>(s, n)\<leftarrow>C. lec_of_nsc (s *R n))" (is "sum_list (map ?f C) = sum_list (map ?g C)")
      proof (rule arg_cong[of _ _ sum_list], rule map_cong[OF refl])
        fix pair
        assume mem: "pair \<in> set C" 
        then obtain s n where pair: "pair = (s,n)" by force
        show "?f pair = ?g pair" unfolding pair split using id[OF mem[unfolded pair]] .
      qed
    qed
  next
    assume ?rhs
    then obtain C const 
      where C: "\<And> r c. (r,c) \<in> set C \<Longrightarrow> 0 < r \<and> c \<in> cs" 
        and sum: "(\<Sum>(r, c)\<leftarrow>C. Leqc (r *R lec_poly c) (r *R lec_const c)) = Leqc 0 const"
        and const: "const < 0" 
      by blast
    let ?C = "map (\<lambda> (r,c). (r, ?to_ns c)) C"  
    show "\<exists> C. farkas_coefficients_ns ?ns C" unfolding farkas_coefficients_ns_def
    proof (intro exI[of _ ?C] exI[of _ const] conjI const, unfold sum[symmetric])
      show "\<forall>(s, n)\<in>set ?C. n \<in> ?ns \<and> is_leq_ns (s *R n) \<and> s \<noteq> 0" using C by fastforce
      show "(\<Sum>(s, n)\<leftarrow>?C. lec_of_nsc (s *R n)) 
        = (\<Sum>(r, c)\<leftarrow>C. Leqc (r *R lec_poly c) (r *R lec_const c))"
        unfolding map_map o_def
        by (rule arg_cong[of _ _ sum_list], rule map_cong[OF refl], insert C, force)
    qed
  qed
  finally show ?thesis .
qed



subsection \<open>Motzkin's Transposition Theorem or the Kuhn-Fourier Theorem\<close>

text \<open>Next, we prove a generalization of Farkas' Lemma that permits arbitrary combinations
  of strict and non-strict inequalities: Motzkin's Transposition Theorem
  which is also known as the Kuhn--Fourier Theorem.

  The proof is mainly based on the lemma @{thm [source] farkas_coefficients}, 
  again requiring conversions between constraint types.\<close>

theorem Motzkin's_transposition_theorem: fixes cs :: "rat le_constraint set"
  assumes fin: "finite cs" 
  shows "(\<nexists> v. \<forall> c \<in> cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> 
       (\<exists> C const rel. (\<forall> (r, c) \<in> set C. r > 0 \<and> c \<in> cs)
         \<and> (\<Sum> (r,c) \<leftarrow> C. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)) 
               = Le_Constraint rel 0 const
         \<and> (rel = Leq_Rel \<and> const < 0 \<or> rel = Lt_Rel \<and> const \<le> 0))" 
    (is "?lhs = ?rhs")
proof -
  let ?to_cs = "\<lambda> c. (case lec_rel c of Leq_Rel \<Rightarrow> LEQ | _ \<Rightarrow> LT) (lec_poly c) (lec_const c)" 
  have to_cs: "v \<Turnstile>\<^sub>c ?to_cs c \<longleftrightarrow> v \<Turnstile>\<^sub>l\<^sub>e c" for v c by (cases c, cases "lec_rel c", auto)
  let ?cs = "?to_cs ` cs" 
  from fin have fin: "finite ?cs" by auto
  have "v \<Turnstile>\<^sub>c\<^sub>s ?cs \<longleftrightarrow> (\<forall> c \<in> cs. v \<Turnstile>\<^sub>l\<^sub>e c)" for v using to_cs by auto
  hence "?lhs = (\<nexists> v. v \<Turnstile>\<^sub>c\<^sub>s ?cs)" by simp
  also have "\<dots> = (\<exists>C. farkas_coefficients ?cs C)" unfolding farkas_coefficients[OF fin] ..
  also have "\<dots> = ?rhs" 
  proof
    assume "\<exists> C. farkas_coefficients ?cs C" 
    then obtain C const rel where is_leq: "\<forall> (s, n) \<in> set C. n \<in> ?cs \<and> is_le (s *R n) \<and> s \<noteq> 0" 
      and sum: "(\<Sum>(s, n)\<leftarrow>C. lec_of_constraint (s *R n)) = Le_Constraint rel 0 const"
      and c0: "(rel = Leq_Rel \<and> const < 0 \<or> rel = Lt_Rel \<and> const \<le> 0)" 
      unfolding farkas_coefficients_def by blast
    let ?C = "map (\<lambda> (s,n). (s,lec_of_constraint n)) C" 
    show ?rhs 
    proof (intro exI[of _ ?C] exI[of _ const] exI[of _ rel] conjI c0, unfold map_map o_def set_map sum[symmetric], 
        intro ballI, clarify)
      {
        fix s n 
        assume sn: "(s, n) \<in> set C" 
        with is_leq 
        have n_ns: "n \<in> ?cs" and is_leq: "is_le (s *R n)" and s0: "s \<noteq> 0" by force+
        from n_ns obtain c where c: "c \<in> cs" and n: "n = ?to_cs c" by auto
        from is_leq[unfolded n] have "s \<ge> 0" by (cases "lec_rel c", auto split: if_splits) 
        with s0 have s0: "s > 0" by auto
        let ?c = "lec_of_constraint n" 
        from c n have mem: "?c \<in> cs" by (cases c, cases "lec_rel c", auto)
        show "0 < s \<and> ?c \<in> cs" using s0 mem by blast        
        have "lec_of_constraint (s *R n) = Le_Constraint (lec_rel ?c) (s *R lec_poly ?c) (s *R lec_const ?c)" 
          unfolding n using s0 by (cases c, cases "lec_rel c", auto)
      } note id = this
      show "(\<Sum>x\<leftarrow>C. case case x of (s, n) \<Rightarrow> (s, lec_of_constraint n) of
             (r, c) \<Rightarrow> Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)) =
            (\<Sum>(s, n)\<leftarrow>C. lec_of_constraint (s *R n))" 
        (is "sum_list (map ?f C) = sum_list (map ?g C)")  
      proof (rule arg_cong[of _ _ sum_list], rule map_cong[OF refl])
        fix pair
        assume mem: "pair \<in> set C" 
        obtain r c where pair: "pair = (r,c)" by force
        show "?f pair = ?g pair" unfolding pair split id[OF mem[unfolded pair]] ..
      qed
    qed
  next
    assume ?rhs
    then obtain C const rel 
      where C: "\<And> r c. (r,c) \<in> set C \<Longrightarrow> 0 < r \<and> c \<in> cs" 
        and sum: "(\<Sum>(r, c)\<leftarrow>C. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)) 
           = Le_Constraint rel 0 const"
        and const: "rel = Leq_Rel \<and> const < 0 \<or> rel = Lt_Rel \<and> const \<le> 0" 
      by blast
    let ?C = "map (\<lambda> (r,c). (r, ?to_cs c)) C"  
    show "\<exists> C. farkas_coefficients ?cs C" unfolding farkas_coefficients_def
    proof (intro exI[of _ ?C] exI[of _ const] exI[of _ rel] conjI const, unfold sum[symmetric])
      show "\<forall>(s, n)\<in>set ?C. n \<in> ?cs \<and> is_le (s *R n) \<and> s \<noteq> 0" using C by (fastforce split: le_rel.splits) 
      show "(\<Sum>(s, n)\<leftarrow>?C. lec_of_constraint (s *R n)) 
        = (\<Sum>(r, c)\<leftarrow>C. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c))"
        unfolding map_map o_def
        by (rule arg_cong[of _ _ sum_list], rule map_cong[OF refl], insert C, fastforce split: le_rel.splits)
    qed
  qed
  finally show ?thesis .
qed

subsection \<open>Farkas' Lemma\<close>

text \<open>Finally we derive the commonly used form of Farkas' Lemma,
  which easily follows from @{thm [source] Motzkin's_transposition_theorem}. 
  It only permits non-strict inequalities and, as a result, 
  the sum of inequalities will always be non-strict.\<close>

lemma Farkas'_Lemma: fixes cs :: "rat le_constraint set"
  assumes only_non_strict: "lec_rel ` cs \<subseteq> {Leq_Rel}"  
    and fin: "finite cs" 
  shows "(\<nexists> v. \<forall> c \<in> cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> 
       (\<exists> C const. (\<forall> (r, c) \<in> set C. r > 0 \<and> c \<in> cs)
         \<and> (\<Sum> (r,c) \<leftarrow> C. Leqc (r *R lec_poly c) (r *R lec_const c)) = Leqc 0 const
         \<and> const < 0)" 
    (is "_ = ?rhs")
proof -
  {
    fix c
    assume "c \<in> cs" 
    with only_non_strict have "lec_rel c = Leq_Rel" by auto
    then have "\<exists> p const. c = Leqc p const" by (cases c, auto)
  } note leqc = this
  let ?lhs = "\<exists>C const rel.
       (\<forall>(r, c)\<in>set C. 0 < r \<and> c \<in> cs) \<and>
       (\<Sum>(r, c)\<leftarrow>C. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)) 
           = Le_Constraint rel 0 const \<and>
       (rel = Leq_Rel \<and> const < 0 \<or> rel = Lt_Rel \<and> const \<le> 0)" 
  show ?thesis unfolding Motzkin's_transposition_theorem[OF fin]
  proof
    assume ?rhs
    then obtain C const where C: "\<And> r c. (r, c)\<in>set C \<Longrightarrow> 0 < r \<and> c \<in> cs" and
      sum: "(\<Sum>(r, c)\<leftarrow>C. Leqc (r *R lec_poly c) (r *R lec_const c)) = Leqc 0 const"  and
      const: "const < 0" by blast
    show ?lhs 
    proof (intro exI[of _ C] exI[of _ const] exI[of _ Leq_Rel] conjI)
      show "\<forall> (r,c) \<in> set C. 0 < r \<and> c \<in> cs" using C by force
      show "(\<Sum>(r, c)\<leftarrow> C. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)) =
        Leqc 0 const" unfolding sum[symmetric]
        by (rule arg_cong[of _ _ sum_list], rule map_cong[OF refl], insert C, force dest!: leqc)
    qed (insert const, auto)
  next
    assume ?lhs
    then obtain C const rel where C: "\<And> r c. (r, c)\<in>set C \<Longrightarrow> 0 < r \<and> c \<in> cs" and
      sum: "(\<Sum>(r, c)\<leftarrow>C. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)) 
        = Le_Constraint rel 0 const"  and
      const: "rel = Leq_Rel \<and> const < 0 \<or> rel = Lt_Rel \<and> const \<le> 0" by blast
    have id: "(\<Sum>(r, c)\<leftarrow>C. Le_Constraint (lec_rel c) (r *R lec_poly c) (r *R lec_const c)) = 
          (\<Sum>(r, c)\<leftarrow>C. Leqc (r *R lec_poly c) (r *R lec_const c))" (is "_  = ?sum")
      by (rule arg_cong[of _ _ sum_list], rule map_cong, auto dest!: C leqc)
    have "lec_rel ?sum = Leq_Rel" unfolding sum_list_lec by (auto simp add: sum_list_Leq_Rel o_def)
    with sum[unfolded id] have rel: "rel = Leq_Rel" by auto
    with const have const: "const < 0" by auto
    show ?rhs
      by (intro exI[of _ C] exI[of _ const] conjI const, insert sum id C rel, force+)
  qed
qed

text \<open>We also present slightly modified versions\<close>

lemma sum_list_map_filter_sum: fixes f :: "'a \<Rightarrow> 'b :: comm_monoid_add" 
  shows "sum_list (map f (filter g xs)) + sum_list (map f (filter (Not o g) xs)) = sum_list (map f xs)" 
  by (induct xs, auto simp: ac_simps)

text \<open>A version where every constraint obtains exactly one coefficient and where 0 coefficients are allowed.\<close>

lemma Farkas'_Lemma_set_sum: fixes cs :: "rat le_constraint set"
  assumes only_non_strict: "lec_rel ` cs \<subseteq> {Leq_Rel}"  
    and fin: "finite cs" 
  shows "(\<nexists> v. \<forall> c \<in> cs. v \<Turnstile>\<^sub>l\<^sub>e c) \<longleftrightarrow> 
       (\<exists> C const. (\<forall> c \<in> cs. C c \<ge> 0)
         \<and> (\<Sum> c \<in> cs. Leqc ((C c) *R lec_poly c) ((C c) *R lec_const c)) = Leqc 0 const
         \<and> const < 0)" 
  unfolding Farkas'_Lemma[OF only_non_strict fin] 
proof ((standard; elim exE conjE), goal_cases)
  case (2 C const)
  from finite_distinct_list[OF fin] obtain csl where csl: "set csl = cs" and dist: "distinct csl" 
    by auto
  let ?list = "filter (\<lambda> c. C c \<noteq> 0) csl" 
  let ?C = "map (\<lambda> c. (C c, c)) ?list" 
  show ?case
  proof (intro exI[of _ ?C] exI[of _ const] conjI)
    have "(\<Sum>(r, c)\<leftarrow>?C. Le_Constraint Leq_Rel (r *R lec_poly c) (r *R lec_const c))
      = (\<Sum>(r, c)\<leftarrow>map (\<lambda>c. (C c, c)) csl. Le_Constraint Leq_Rel (r *R lec_poly c) (r *R lec_const c))" 
      unfolding map_map
      by (rule sum_list_map_filter, auto simp: zero_le_constraint_def)
    also have "\<dots> = Le_Constraint Leq_Rel 0 const" unfolding 2(2)[symmetric] csl[symmetric]
      unfolding sum.distinct_set_conv_list[OF dist] map_map o_def split ..
    finally 
    show "(\<Sum>(r, c)\<leftarrow>?C. Le_Constraint Leq_Rel (r *R lec_poly c) (r *R lec_const c)) = Le_Constraint Leq_Rel 0 const"  
      by auto
    show "const < 0" by fact
    show "\<forall>(r, c)\<in>set ?C. 0 < r \<and> c \<in> cs" using 2(1) unfolding set_map set_filter csl by auto
  qed
next
  case (1 C const)
  define CC where "CC = (\<lambda> c. sum_list (map fst (filter (\<lambda> rc. snd rc = c) C)))" 
  show "(\<exists> C const. (\<forall> c \<in> cs. C c \<ge> 0)
         \<and> (\<Sum> c \<in> cs. Leqc ((C c) *R lec_poly c) ((C c) *R lec_const c)) = Leqc 0 const
         \<and> const < 0)" 
  proof (intro exI[of _ CC] exI[of _ const] conjI)
    show "\<forall>c\<in>cs. 0 \<le> CC c" unfolding CC_def using 1(1) 
      by (force intro!: sum_list_nonneg)
    show "const < 0" by fact
    from 1 have snd: "snd ` set C \<subseteq> cs" by auto
    show "(\<Sum>c\<in>cs. Le_Constraint Leq_Rel (CC c *R lec_poly c) (CC c *R lec_const c)) = Le_Constraint Leq_Rel 0 const" 
      unfolding 1(2)[symmetric] using fin snd unfolding CC_def
    proof (induct cs arbitrary: C rule: finite_induct)
      case empty
      hence C: "C = []" by auto
      thus ?case by simp
    next
      case *: (insert c cs C)
      let ?D = "filter (Not \<circ> (\<lambda>rc. snd rc = c)) C" 
      from * have "snd ` set ?D \<subseteq> cs" by auto
      note IH = *(3)[OF this]
      have id: "(\<Sum>a\<leftarrow> ?D. case a of (r, c) \<Rightarrow> Le_Constraint Leq_Rel (r *R lec_poly c) (r *R lec_const c)) = 
        (\<Sum>(r, c)\<leftarrow>?D. Le_Constraint Leq_Rel (r *R lec_poly c) (r *R lec_const c))" 
        by (induct C, force+)
      show ?case
        unfolding sum.insert[OF *(1,2)]
        unfolding sum_list_map_filter_sum[of _ "\<lambda> rc. snd rc = c" C, symmetric]
      proof (rule arg_cong2[of _ _ _ _ "(+)"], goal_cases)
        case 2
        show ?case unfolding IH[symmetric] 
          by (rule sum.cong, insert *(2,1), auto intro!: arg_cong[of _ _ "\<lambda> xs. sum_list (map _ xs)"], (induct C, auto)+)
      next
        case 1
        show ?case
        proof (rule sym, induct C)
          case (Cons rc C)
          thus ?case by (cases "rc", cases "snd rc = c", auto simp: field_simps scaleRat_left_distrib)
        qed (auto simp: zero_le_constraint_def)
      qed
    qed
  qed
qed

text \<open>A version with indexed constraints, i.e., in particular where constraints may occur several
  times.\<close>

lemma Farkas'_Lemma_indexed: fixes c :: "nat \<Rightarrow> rat le_constraint"
  assumes only_non_strict: "lec_rel ` c ` Is \<subseteq> {Leq_Rel}"  
  and fin: "finite Is" 
  shows "(\<nexists> v. \<forall> i \<in> Is. v \<Turnstile>\<^sub>l\<^sub>e c i) \<longleftrightarrow> 
       (\<exists> C const. (\<forall> i \<in> Is. C i \<ge> 0)
         \<and> (\<Sum> i \<in> Is. Leqc ((C i) *R lec_poly (c i)) ((C i) *R lec_const (c i))) = Leqc 0 const
         \<and> const < 0)" 
proof -
  let ?C = "c ` Is" 
  have fin: "finite ?C" using fin by auto
  have "(\<nexists> v. \<forall> i \<in> Is. v \<Turnstile>\<^sub>l\<^sub>e c i) = (\<nexists> v. \<forall> cc \<in> ?C. v \<Turnstile>\<^sub>l\<^sub>e cc)" by force
  also have "\<dots> = (\<exists> C const. (\<forall> i \<in> Is. C i \<ge> 0)
         \<and> (\<Sum> i \<in> Is. Leqc ((C i) *R lec_poly (c i)) ((C i) *R lec_const (c i))) = Leqc 0 const
         \<and> const < 0)" (is "?l = ?r")
  proof
    assume ?r
    then obtain C const where r: "(\<forall> i \<in> Is. C i \<ge> 0)" 
         and eq: "(\<Sum> i \<in> Is. Leqc ((C i) *R lec_poly (c i)) ((C i) *R lec_const (c i))) = Leqc 0 const" 
         and "const < 0" by auto
    from finite_distinct_list[OF `finite Is`] 
      obtain Isl where isl: "set Isl = Is" and dist: "distinct Isl" by auto
    let ?CC = "filter (\<lambda> rc. fst rc \<noteq> 0) (map (\<lambda> i. (C i, c i)) Isl)" 
    show ?l unfolding Farkas'_Lemma[OF only_non_strict fin]
    proof (intro exI[of _ ?CC] exI[of _ const] conjI)
      show "const < 0" by fact
      show "\<forall> (r, ca) \<in> set ?CC. 0 < r \<and> ca \<in> ?C" using r(1) isl by auto
      show "(\<Sum>(r, c)\<leftarrow>?CC. Le_Constraint Leq_Rel (r *R lec_poly c) (r *R lec_const c)) =
        Le_Constraint Leq_Rel 0 const" unfolding eq[symmetric]
        by (subst sum_list_map_filter, force simp: zero_le_constraint_def,
          unfold map_map o_def, subst sum_list_distinct_conv_sum_set[OF dist], rule sum.cong, auto simp: isl)
    qed
  next
    assume ?l
    from this[unfolded Farkas'_Lemma_set_sum[OF only_non_strict fin]]
    obtain C const where nonneg: "(\<forall>c\<in> ?C. 0 \<le> C c)" 
     and sum: "(\<Sum>c\<in> ?C. Le_Constraint Leq_Rel (C c *R lec_poly c) (C c *R lec_const c)) =
        Le_Constraint Leq_Rel 0 const" 
     and const: "const < 0" 
      by blast
    define I where "I = (\<lambda> i. (C (c i) / rat_of_nat (card (Is \<inter> { j. c i = c j}))))" 
    show ?r
    proof (intro exI[of _ I] exI[of _ const] conjI const)
      show "\<forall>i \<in> Is. 0 \<le> I i" using nonneg unfolding I_def by auto
      show "(\<Sum> i \<in> Is. Le_Constraint Leq_Rel (I i *R lec_poly (c i)) (I i *R lec_const (c i))) =
        Le_Constraint Leq_Rel 0 const" unfolding sum[symmetric]
        unfolding sum.image_gen[OF \<open>finite Is\<close>, of _ c]
      proof (rule sum.cong[OF refl], goal_cases)
        case (1 cc)
        define II where "II = (Is \<inter> {j. cc = c j})" 
        from 1 have "II \<noteq> {}" unfolding II_def by auto
        moreover have finII: "finite II" using \<open>finite Is\<close> unfolding II_def by auto
        ultimately have card: "card II \<noteq> 0" by auto
        let ?C = "\<lambda> II. rat_of_nat (card II)" 
        define ii where "ii = C cc / rat_of_nat (card II)" 
        have "(\<Sum>i\<in>{x \<in> Is. c x = cc}. Le_Constraint Leq_Rel (I i *R lec_poly (c i)) (I i *R lec_const (c i)))
          = (\<Sum> i\<in> II. Le_Constraint Leq_Rel (ii *R lec_poly cc) (ii *R lec_const cc))"
          unfolding I_def ii_def II_def by (rule sum.cong, auto)
        also have "\<dots> = Le_Constraint Leq_Rel ((?C II * ii) *R lec_poly cc) ((?C II * ii) *R lec_const cc)" 
          using finII by (induct II rule: finite_induct, auto simp: zero_le_constraint_def field_simps
            scaleRat_left_distrib)
        also have "?C II * ii = C cc" unfolding ii_def using card by auto
        finally show ?case .
      qed
    qed
  qed
  finally show ?thesis .
qed


end