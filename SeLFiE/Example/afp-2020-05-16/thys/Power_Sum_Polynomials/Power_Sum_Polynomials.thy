section \<open>Power sum polynomials\<close>
(*
  File:     Power_Sum_Polynomials.thy
  Author:   Manuel Eberl, TU München
*)
theory Power_Sum_Polynomials
imports
  "Symmetric_Polynomials.Symmetric_Polynomials"
  "HOL-Computational_Algebra.Field_as_Ring"
  Power_Sum_Polynomials_Library
begin

subsection \<open>Definition\<close>

text \<open>
  For $n$ indeterminates $X_1,\ldots,X_n$, we define the $k$-th power sum polynomial as
  \[p_k(X_1, \ldots, X_n) = X_1^k + \ldots + X_n^k\ .\]
\<close>
lift_definition powsum_mpoly_aux :: "nat set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a :: {semiring_1,zero_neq_one}" is
  "\<lambda>X k mon. if infinite X \<or> k = 0 \<and> mon \<noteq> 0 then 0
             else if k = 0 \<and> mon = 0 then of_nat (card X)
             else if finite X \<and> (\<exists>x\<in>X. mon = Poly_Mapping.single x k) then 1 else 0"
  by auto

lemma lookup_powsum_mpoly_aux:
  "Poly_Mapping.lookup (powsum_mpoly_aux X k) mon =
     (if infinite X \<or> k = 0 \<and> mon \<noteq> 0 then 0
             else if k = 0 \<and> mon = 0 then of_nat (card X)
             else if finite X \<and> (\<exists>x\<in>X. mon = Poly_Mapping.single x k) then 1 else 0)"
  by transfer' simp

lemma lookup_sym_mpoly_aux_monom_singleton [simp]:
  assumes "finite X" "x \<in> X" "k > 0"
  shows   "Poly_Mapping.lookup (powsum_mpoly_aux X k) (Poly_Mapping.single x k) = 1"
  using assms by (auto simp: lookup_powsum_mpoly_aux)

lemma lookup_sym_mpoly_aux_monom_singleton':
  assumes "finite X" "k > 0"
  shows   "Poly_Mapping.lookup (powsum_mpoly_aux X k) (Poly_Mapping.single x k) = (if x \<in> X then 1 else 0)"
  using assms by (auto simp: lookup_powsum_mpoly_aux)

lemma keys_powsum_mpoly_aux: "m \<in> keys (powsum_mpoly_aux A k) \<Longrightarrow> keys m \<subseteq> A"
  by transfer' (auto split: if_splits simp: keys_monom_of_set)


lift_definition powsum_mpoly :: "nat set \<Rightarrow> nat \<Rightarrow> 'a :: {semiring_1,zero_neq_one} mpoly" is
  "powsum_mpoly_aux" .

lemma vars_powsum_mpoly_subset: "vars (powsum_mpoly A k) \<subseteq> A"
  using keys_powsum_mpoly_aux by (auto simp: vars_def powsum_mpoly.rep_eq)

lemma powsum_mpoly_infinite: "\<not>finite A \<Longrightarrow> powsum_mpoly A k = 0"
  by (transfer, transfer) auto

lemma coeff_powsum_mpoly:
  "MPoly_Type.coeff (powsum_mpoly X k) mon =
     (if infinite X \<or> k = 0 \<and> mon \<noteq> 0 then 0
             else if k = 0 \<and> mon = 0 then of_nat (card X)
             else if finite X \<and> (\<exists>x\<in>X. mon = Poly_Mapping.single x k) then 1 else 0)"
  by transfer' (simp add: lookup_powsum_mpoly_aux)

lemma coeff_powsum_mpoly_0_right:
  "MPoly_Type.coeff (powsum_mpoly X 0) mon = (if mon = 0 then of_nat (card X) else 0)"
  by transfer' (auto simp add: lookup_powsum_mpoly_aux)

lemma coeff_powsum_mpoly_singleton:
  assumes "finite X" "k > 0"
  shows   "MPoly_Type.coeff (powsum_mpoly X k) (Poly_Mapping.single x k) = (if x \<in> X then 1 else 0)"
  using assms by transfer' (simp add: lookup_powsum_mpoly_aux)

lemma coeff_powsum_mpoly_singleton_eq_1 [simp]:
  assumes "finite X" "x \<in> X" "k > 0"
  shows   "MPoly_Type.coeff (powsum_mpoly X k) (Poly_Mapping.single x k) = 1"
  using assms by (simp add: coeff_powsum_mpoly_singleton)

lemma coeff_powsum_mpoly_singleton_eq_0 [simp]:
  assumes "finite X" "x \<notin> X" "k > 0"
  shows   "MPoly_Type.coeff (powsum_mpoly X k) (Poly_Mapping.single x k) = 0"
  using assms by (simp add: coeff_powsum_mpoly_singleton)

lemma powsum_mpoly_0 [simp]: "powsum_mpoly X 0 = of_nat (card X)"
  by (intro mpoly_eqI ext) (auto simp: coeff_powsum_mpoly_0_right of_nat_mpoly_eq mpoly_coeff_Const)

lemma powsum_mpoly_empty [simp]: "powsum_mpoly {} k = 0"
  by (intro mpoly_eqI) (auto simp: coeff_powsum_mpoly)

lemma powsum_mpoly_altdef: "powsum_mpoly X k = (\<Sum>x\<in>X. monom (Poly_Mapping.single x k) 1)"
proof (cases "finite X")
  case [simp]: True
  show ?thesis
  proof (cases "k = 0")
    case True
    thus ?thesis by auto
  next
    case False
    show ?thesis
    proof (intro mpoly_eqI, goal_cases)
      case (1 mon)
      show ?case using False
        by (cases "\<exists>x\<in>X. mon = Poly_Mapping.single x k")
           (auto simp: coeff_powsum_mpoly coeff_monom when_def)
    qed
  qed
qed (auto simp: powsum_mpoly_infinite)

text \<open>
  Power sum polynomials are symmetric:
\<close>
lemma symmetric_powsum_mpoly [intro]:
  assumes "A \<subseteq> B"
  shows   "symmetric_mpoly A (powsum_mpoly B k)"
  unfolding powsum_mpoly_altdef
proof (rule symmetric_mpoly_symmetric_sum)
  fix x \<pi>
  assume "x \<in> B" "\<pi> permutes A"
  thus "mpoly_map_vars \<pi> (MPoly_Type.monom (Poly_Mapping.single x k) 1) =
        MPoly_Type.monom (Poly_Mapping.single (\<pi> x) k) 1"
    using assms by (auto simp: mpoly_map_vars_monom permutes_bij permutep_single
                               bij_imp_bij_inv permutes_inv_inv)
qed (use assms in \<open>auto simp: permutes_subset\<close>)

lemma insertion_powsum_mpoly [simp]: "insertion f (powsum_mpoly X k) = (\<Sum>i\<in>X. f i ^ k)"
  unfolding powsum_mpoly_altdef insertion_sum insertion_single by simp

lemma powsum_mpoly_nz:
  assumes "finite X" "X \<noteq> {}" "k > 0"
  shows   "(powsum_mpoly X k :: 'a :: {semiring_1, zero_neq_one} mpoly) \<noteq> 0"
proof -
  from assms obtain x where "x \<in> X" by auto
  hence "coeff (powsum_mpoly X k) (Poly_Mapping.single x k) = (1 :: 'a)"
    using assms by (auto simp: coeff_powsum_mpoly)
  thus ?thesis by auto
qed

lemma powsum_mpoly_eq_0_iff:
  assumes "k > 0"
  shows   "powsum_mpoly X k = 0 \<longleftrightarrow> infinite X \<or> X = {}"
  using assms powsum_mpoly_nz[of X k] by (auto simp: powsum_mpoly_infinite)


subsection \<open>The Girard--Newton Theorem\<close>

text \<open>
  The following is a nice combinatorial proof of the Girard--Newton Theorem due to
  Doron Zeilberger~\cite{zeilberger}.

  The precise statement is this:

  Let $e_k$ denote the $k$-th elementary symmetric polynomial in $X_1,\ldots,X_n$.
  This is the sum of all monomials that can be formed by taking the product of $k$ 
  distinct variables.

  Next, let $p_k = X_1^k + \ldots + X_n^k$ denote that $k$-th symmetric power sum polynomial
  in $X_1,\ldots,X_n$.

  Then the following equality holds:
  \[(-1)^k k e_k + \sum_{i=0}^{k-1} (-1)^i e_i p_{k-i}\]
\<close>
theorem Girard_Newton:
  assumes "finite X"
  shows   "(-1) ^ k * of_nat k * sym_mpoly X k +
           (\<Sum>i<k. (-1) ^ i * sym_mpoly X i * powsum_mpoly X (k - i)) =
             (0 :: 'a :: comm_ring_1 mpoly)"
  (is "?lhs = 0")
proof -
  write Poly_Mapping.single ("sng")

  define n where "n = card X"
  define \<A> :: "(nat set \<times> nat) set"
    where "\<A> = {(A, j). A \<subseteq> X \<and> card A \<le> k \<and> j \<in> X \<and> (card A = k \<longrightarrow> j \<in> A)}"
  define \<A>1 :: "(nat set \<times> nat) set"
    where "\<A>1 = {A\<in>Pow X. card A < k} \<times> X"
  define \<A>2 :: "(nat set \<times> nat) set"
    where "\<A>2 = (SIGMA A:{A\<in>Pow X. card A = k}. A)"

  have \<A>_split: "\<A> = \<A>1 \<union> \<A>2" "\<A>1 \<inter> \<A>2 = {}"
    by (auto simp: \<A>_def \<A>1_def \<A>2_def)
  have [intro]: "finite \<A>1" "finite \<A>2"
    using assms finite_subset[of _ X] by (auto simp: \<A>1_def \<A>2_def intro!: finite_SigmaI)
  have [intro]: "finite \<A>"
    by (subst \<A>_split) auto

  \<comment> \<open>
    We define a `weight' function \<open>w\<close> from \<open>\<A>\<close> to the ring of polynomials as
    \[w(A,j) = (-1)^{|A|} x_j^{k-|A|} \prod_{i\in A} x_i\ .\]
  \<close>
  define w :: "nat set \<times> nat \<Rightarrow> 'a mpoly"
    where "w = (\<lambda>(A, j). monom (monom_of_set A + sng j (k - card A)) ((-1) ^ card A))"

  \<comment> \<open>The sum of these weights over all of \<open>\<A>\<close> is precisely the sum that we want to show equals 0:\<close>
  have "?lhs = (\<Sum>x\<in>\<A>. w x)"
  proof -
    have "(\<Sum>x\<in>\<A>. w x) = (\<Sum>x\<in>\<A>1. w x) + (\<Sum>x\<in>\<A>2. w x)"
      by (subst \<A>_split, subst sum.union_disjoint, use \<A>_split(2) in auto)

    also have "(\<Sum>x\<in>\<A>1. w x) = (\<Sum>i<k. (-1) ^ i * sym_mpoly X i * powsum_mpoly X (k - i))"
    proof -
      have "(\<Sum>x\<in>\<A>1. w x) = (\<Sum>A | A \<subseteq> X \<and> card A < k. \<Sum>j\<in>X. w (A, j))"
        using assms by (subst sum.Sigma) (auto simp: \<A>1_def)
      also have "\<dots> = (\<Sum>A | A \<subseteq> X \<and> card A < k. \<Sum>j\<in>X.
                        monom (monom_of_set A) ((-1) ^ card A) * monom (sng j (k - card A)) 1)"
        unfolding w_def by (intro sum.cong) (auto simp: mult_monom)
      also have "\<dots> = (\<Sum>A | A \<subseteq> X \<and> card A < k. monom (monom_of_set A) ((-1) ^ card A) *
                        powsum_mpoly X (k - card A))"
        by (simp add: sum_distrib_left powsum_mpoly_altdef)
      also have "\<dots> = (\<Sum>(i,A) \<in> (SIGMA i:{..<k}. {A. A \<subseteq> X \<and> card A = i}).
                        monom (monom_of_set A) ((-1) ^ i) * powsum_mpoly X (k - i))"
        by (rule sum.reindex_bij_witness[of _ snd "\<lambda>A. (card A, A)"]) auto
      also have "\<dots> = (\<Sum>i<k. \<Sum>A | A \<subseteq> X \<and> card A = i.
                        monom (monom_of_set A) 1 * monom 0 ((-1) ^ i) * powsum_mpoly X (k - i))"
        using assms by (subst sum.Sigma) (auto simp: mult_monom)
      also have "\<dots> = (\<Sum>i<k. (-1) ^ i * sym_mpoly X i * powsum_mpoly X (k - i))"
        by (simp add: sum_distrib_left sum_distrib_right mpoly_monom_0_eq_Const 
                      mpoly_Const_power mpoly_Const_uminus algebra_simps sym_mpoly_altdef)
      finally show ?thesis .
    qed

    also have "(\<Sum>x\<in>\<A>2. w x) = (-1) ^ k * of_nat k * sym_mpoly X k"
    proof -
      have "(\<Sum>x\<in>\<A>2. w x) = (\<Sum>(A,j)\<in>\<A>2. monom (monom_of_set A) ((- 1) ^ k))"
        by (intro sum.cong) (auto simp: \<A>2_def w_def mpoly_monom_0_eq_Const intro!: sum.cong)
      also have "\<dots> = (\<Sum>A | A \<subseteq> X \<and> card A = k. \<Sum>j\<in>A. monom (monom_of_set A) ((- 1) ^ k))"
        using assms finite_subset[of _ X] by (subst sum.Sigma) (auto simp: \<A>2_def)
      also have "(\<lambda>A. monom (monom_of_set A) ((- 1) ^ k) :: 'a mpoly) =
                   (\<lambda>A. monom 0 ((-1) ^ k) * monom (monom_of_set A) 1)"
        by (auto simp: fun_eq_iff mult_monom)
      also have "monom 0 ((-1) ^ k) = (-1) ^ k"
        by (auto simp: mpoly_monom_0_eq_Const mpoly_Const_power mpoly_Const_uminus)
      also have "(\<Sum>A | A \<subseteq> X \<and> card A = k. \<Sum>j\<in>A. (- 1) ^ k * monom (monom_of_set A) 1) =
                   ((-1) ^ k * of_nat k * sym_mpoly X k :: 'a mpoly)"
        by (auto simp: sum_distrib_left sum_distrib_right mult_ac sym_mpoly_altdef)
      finally show ?thesis .
    qed

    finally show ?thesis by (simp add: algebra_simps)
  qed

  \<comment> \<open>Next, we show that the weights sum to 0:\<close>
  also have "(\<Sum>x\<in>\<A>. w x) = 0"
  proof -
    \<comment> \<open>We define a function \<open>T\<close> that is a involutory permutation of \<open>\<A>\<close>.
        To be more precise, it bijectively maps those elements \<open>(A,j)\<close> of \<open>\<A>\<close> with \<open>j \<in> A\<close>
        to those where \<open>j \<notin> A\<close> and the other way round. `Involutory' means that \<open>T\<close> is its
        own inverse function, i.\,e.\ $T(T(x)) = x$.\<close>
    define T :: "nat set \<times> nat \<Rightarrow> nat set \<times> nat"
      where "T = (\<lambda>(A, j). if j \<in> A then (A - {j}, j) else (insert j A, j))"
    have [simp]: "T (T x) = x" for x
      by (auto simp: T_def split: prod.splits)
    have [simp]: "T x \<in> \<A>" if "x \<in> \<A>" for x
    proof -
      have [simp]: "n \<le> n - Suc 0 \<longleftrightarrow> n = 0" for n
        by auto
      show ?thesis using that assms finite_subset[of _ X]
        by (auto simp: T_def \<A>_def split: prod.splits)
    qed
    have "snd (T x) \<in> fst (T x) \<longleftrightarrow> snd x \<notin> fst x" if "x \<in> \<A>" for x
      by (auto simp: T_def split: prod.splits)
    hence bij: "bij_betw T {x\<in>\<A>. snd x \<in> fst x} {x\<in>\<A>. snd x \<notin> fst x}"
      by (intro bij_betwI[of _ _ _ T]) auto

    \<comment>\<open>Crucially, we show that \<^term>\<open>T\<close> flips the weight of each element:\<close>
    have [simp]: "w (T x) = -w x" if "x \<in> \<A>" for x
    proof -
      obtain A j where [simp]: "x = (A, j)" by force
      
      \<comment> \<open>Since \<^term>\<open>T\<close> is an involution, we can assume w.\,l.\,o.\,g.\ that \<open>j \<in> A\<close>:\<close>
      have aux: "w (T (A, j)) = - w (A, j)" if "(A, j) \<in> \<A>" "j \<in> A" for j A
      proof -
        from that have [simp]: "j \<in> A" "A \<subseteq> X" and "k > 0"
          using finite_subset[OF _ assms, of A] by (auto simp: \<A>_def intro!: Nat.gr0I)
        have [simp]: "finite A"
          using finite_subset[OF _ assms, of A] by auto
        from that have "card A \<le> k"
          by (auto simp: \<A>_def)

        have card: "card A = Suc (card (A - {j}))"
          using card.remove[of A j] by auto
        hence card_less: "card (A - {j}) < card A" by linarith

        have "w (T (A, j)) = monom (monom_of_set (A - {j}) + sng j (k - card (A - {j})))
                         ((- 1) ^ card (A - {j}))" by (simp add: w_def T_def)
        also have "(- 1) ^ card (A - {j}) = ((- 1) ^ Suc (Suc (card (A - {j}))) :: 'a)"
          by simp
        also have "Suc (card (A - {j})) = card A"
          using card by simp
        also have "k - card (A - {j}) = Suc (k - card A)"
          using \<open>k > 0\<close> \<open>card A \<le> k\<close> card_less by (subst card) auto
        also have "monom_of_set (A - {j}) + sng j (Suc (k - card A)) =
                   monom_of_set A + sng j (k - card A)"
          by (transfer fixing: A j k) (auto simp: fun_eq_iff)
        also have "monom \<dots> ((-1)^ Suc (card A)) = -w (A, j)"
          by (simp add: w_def monom_uminus)
        finally show ?thesis .
      qed

      show ?thesis
      proof (cases "j \<in> A")
        case True
        with aux[of A j] that show ?thesis by auto
      next
        case False
        hence "snd (T x) \<in> fst (T x)"
          by (auto simp: T_def split: prod.splits)
        with aux[of "fst (T x)" "snd (T x)"] that show ?thesis by auto
      qed
    qed

    text \<open>
      We can now show fairly easily that the sum is equal to zero.
    \<close>
    have *: "\<A> = {x\<in>\<A>. snd x \<in> fst x} \<union> {x\<in>\<A>. snd x \<notin> fst x}"
      by auto
    have "(\<Sum>x\<in>\<A>. w x) = (\<Sum>x | x \<in> \<A> \<and> snd x \<in> fst x. w x) + (\<Sum>x | x \<in> \<A> \<and> snd x \<notin> fst x. w x)"
      using \<open>finite \<A>\<close> by (subst *, subst sum.union_disjoint) auto
    also have "(\<Sum>x | x \<in> \<A> \<and> snd x \<notin> fst x. w x) = (\<Sum>x | x \<in> \<A> \<and> snd x \<in> fst x. w (T x))"
      using sum.reindex_bij_betw[OF bij, of w] by simp
    also have "\<dots> = -(\<Sum>x | x \<in> \<A> \<and> snd x \<in> fst x. w x)"
      by (simp add: sum_negf)
    finally show "(\<Sum>x\<in>\<A>. w x) = 0"
      by simp
  qed

  finally show ?thesis .
qed

text \<open>
  The following variant of the theorem holds for \<open>k > n\<close>. Note that this is now a
  linear recurrence relation with constant coefficients for $p_k$ in terms of
  $e_0, \ldots, e_n$.
\<close>
corollary Girard_Newton':
  assumes "finite X" and "k > card X"
  shows   "(\<Sum>i\<le>card X. (-1) ^ i * sym_mpoly X i * powsum_mpoly X (k - i)) =
             (0 :: 'a :: comm_ring_1 mpoly)"
proof -
  have "(0 :: 'a mpoly) = (\<Sum>i<k. (- 1) ^ i * sym_mpoly X i * powsum_mpoly X (k - i))"
    using Girard_Newton[of X k] assms by simp
  also have "\<dots> = (\<Sum>i\<le>card X. (- 1) ^ i * sym_mpoly X i * powsum_mpoly X (k - i))"
    using assms by (intro sum.mono_neutral_right) auto
  finally show ?thesis ..
qed  

text \<open>
  The following variant is the Newton--Girard Theorem solved for $e_k$, giving us
  an explicit way to determine $e_k$ from $e_0, \ldots, e_{k-1}$ and $p_1, \ldots, p_k$:
\<close>
corollary sym_mpoly_recurrence:
  assumes k: "k > 0" and "finite X"
  shows   "(sym_mpoly X k :: 'a :: field_char_0 mpoly) =
             -smult (1 / of_nat k) (\<Sum>i=1..k. (-1) ^ i * sym_mpoly X (k - i) * powsum_mpoly X i)"
proof -
  define e p :: "nat \<Rightarrow> 'a mpoly" where [simp]: "e = sym_mpoly X" "p = powsum_mpoly X"
  have *: "0 = (-1) ^ k * of_nat k * e k +
              (\<Sum>i<k. (- 1) ^ i * e i * p (k - i) :: 'a mpoly)"
    using Girard_Newton[of X k] assms by simp

  have "0 = (-1) ^ k * smult (1 / of_nat k) (0 :: 'a mpoly)"
    by simp
  also have "\<dots> = smult (1 / of_nat k) (of_nat k) * e k +
                  smult (1 / of_nat k) (\<Sum>i<k. (-1)^(k+i) * e i * p (k - i))"
    unfolding smult_conv_mult
    using k by (subst *) (simp add: power_add sum_distrib_left sum_distrib_right field_simps 
                               del: div_mult_self3 div_mult_self4 div_mult_self2 div_mult_self1)
  also have "smult (1 / of_nat k :: 'a) (of_nat k) = 1"
    using k by (simp add: of_nat_monom smult_conv_mult mult_monom del: monom_of_nat)
  also have "(\<Sum>i<k. (-1) ^ (k+i) * e i * p (k - i)) = (\<Sum>i=1..k. (-1) ^ i * e (k-i) * p i)"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. k - i" "\<lambda>i. k - i"])
       (auto simp: minus_one_power_iff)
  finally show ?thesis unfolding e_p_def by algebra
qed

text \<open>
  Analogously, the following is the theorem solved for $p_k$, giving us a
  way to determine $p_k$ from $e_0, \ldots, e_k$ and $p_1, \ldots, p_{k-1}$:
\<close>
corollary powsum_mpoly_recurrence:
  assumes k: "k > 0" and X: "finite X"
  shows   "(powsum_mpoly X k :: 'a :: comm_ring_1 mpoly) =
             (-1) ^ (k + 1) * of_nat k * sym_mpoly X k -
             (\<Sum>i=1..<k. (-1) ^ i * sym_mpoly X i * powsum_mpoly X (k - i))"
proof -
  define e p :: "nat \<Rightarrow> 'a mpoly" where [simp]: "e = sym_mpoly X" "p = powsum_mpoly X"
  have *: "0 = (-1) ^ k * of_nat k * e k +
                 (\<Sum>i<k. (-1) ^ i * e i * p (k - i) :: 'a mpoly)"
    using Girard_Newton[of X k] assms by simp
  also have "{..<k} = insert 0 {1..<k}"
    using assms by auto
  finally have "(-1) ^ k * of_nat k * e k + (\<Sum>i=1..<k. (-1) ^ i * e i * p (k - i)) + p k = 0"
    using assms by (simp add: algebra_simps)
  from add.inverse_unique[OF this] show ?thesis by simp
qed

text \<open>
  Again, if we assume $k > n$, the above takes a much simpler form and is, in fact,
  a linear recurrence with constant coefficients:
\<close>
lemma powsum_mpoly_recurrence':
  assumes k: "k > card X" and X: "finite X"
  shows   "(powsum_mpoly X k :: 'a :: comm_ring_1 mpoly) =
             -(\<Sum>i=1..card X. (-1) ^ i * sym_mpoly X i * powsum_mpoly X (k - i))"
proof -
  define e p :: "nat \<Rightarrow> 'a mpoly" where [simp]: "e = sym_mpoly X" "p = powsum_mpoly X"
  have "p k = (-1) ^ (k + 1) * of_nat k * e k - (\<Sum>i=1..<k. (-1) ^ i * e i * p (k - i))"
    unfolding e_p_def using assms by (intro powsum_mpoly_recurrence) auto
  also have "\<dots> = -(\<Sum>i=1..<k. (-1) ^ i * e i * p (k - i))"
    using assms by simp
  also have "(\<Sum>i=1..<k. (-1) ^ i * e i * p (k - i)) = (\<Sum>i=1..card X. (-1) ^ i * e i * p (k - i))"
    using assms by (intro sum.mono_neutral_right) auto
  finally show ?thesis by simp
qed

end