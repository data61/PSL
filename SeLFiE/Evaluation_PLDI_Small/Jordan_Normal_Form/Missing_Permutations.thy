(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Permutations\<close>

text \<open>This theory provides some definitions and lemmas on permutations which we did not find in the 
  Isabelle distribution.\<close>

theory Missing_Permutations
imports
  Missing_Ring
  "HOL-Library.Permutations"
begin

definition signof :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a :: ring_1" where
  "signof p = (if sign p = 1 then 1 else - 1)"

lemma signof_id[simp]: "signof id = 1" "signof (\<lambda> x. x) = 1"
  unfolding signof_def sign_id id_def[symmetric] by auto

lemma signof_inv: "finite S \<Longrightarrow> p permutes S \<Longrightarrow> signof (Hilbert_Choice.inv p) = signof p"
  unfolding signof_def using sign_inverse permutation_permutes by metis

lemma signof_pm_one: "signof p \<in> {1, - 1}"
  unfolding signof_def by auto

lemma signof_compose: assumes "p permutes {0..<(n :: nat)}"
  and "q permutes {0 ..<(m :: nat)}"
  shows "signof (p o q) = signof p * signof q"
proof -
  from assms have pp: "permutation p" "permutation q"
    by (auto simp: permutation_permutes)
  show "signof (p o q) = signof p * signof q"
    unfolding signof_def sign_compose[OF pp] 
    by (auto simp: sign_def split: if_splits)
qed

lemma permutes_funcset: "p permutes A \<Longrightarrow> (p ` A \<rightarrow> B) = (A \<rightarrow> B)"
  by (simp add: permutes_image)

context comm_monoid
begin
lemma finprod_permute:
  assumes p: "p permutes S"
  and f: "f \<in> S \<rightarrow> carrier G"
  shows "finprod G f S = finprod G (f \<circ> p) S"
proof -
  from \<open>p permutes S\<close> have "inj p"
    by (rule permutes_inj)
  then have "inj_on p S"
    by (auto intro: subset_inj_on)
  from finprod_reindex[OF _ this, unfolded permutes_image[OF p], OF f]
  show ?thesis unfolding o_def .
qed

lemma finprod_singleton_set[simp]: assumes "f a \<in> carrier G"
  shows "finprod G f {a} = f a"
proof -
  have "finprod G f {a} = f a \<otimes> finprod G f {}"
    by (rule finprod_insert, insert assms, auto)
  also have "\<dots> = f a" using assms by auto
  finally show ?thesis .
qed
end

lemmas (in semiring) finsum_permute = add.finprod_permute
lemmas (in semiring) finsum_singleton_set = add.finprod_singleton_set

lemma permutes_less[simp]: assumes p: "p permutes {0..<(n :: nat)}"
  shows "i < n \<Longrightarrow> p i < n" "i < n \<Longrightarrow> Hilbert_Choice.inv p i < n" 
  "p (Hilbert_Choice.inv p i) = i"
  "Hilbert_Choice.inv p (p i) = i"
proof -
  assume i: "i < n"
  show "p i < n" using permutes_in_image[OF p] i by auto
  let ?inv = "Hilbert_Choice.inv p" 
  have "\<And>n. ?inv (p n) = n"
      using permutes_inverses[OF p] by simp
  thus "?inv i < n" 
      by (metis (no_types) atLeastLessThan_iff f_inv_into_f inv_into_into le0 permutes_image[OF p] i)
qed (insert permutes_inverses[OF p], auto)
    
context cring
begin

lemma finsum_permutations_inverse: 
  assumes f: "f \<in> {p. p permutes S} \<rightarrow> carrier R"
  shows "finsum R f {p. p permutes S} = finsum R (\<lambda>p. f(Hilbert_Choice.inv p)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?inv = "Hilbert_Choice.inv"
  let ?S = "{p . p permutes S}"
  have th0: "inj_on ?inv ?S"
  proof (auto simp add: inj_on_def)
    fix q r
    assume q: "q permutes S"
      and r: "r permutes S"
      and qr: "?inv q = ?inv r"
    then have "?inv (?inv q) = ?inv (?inv r)"
      by simp
    with permutes_inv_inv[OF q] permutes_inv_inv[OF r] show "q = r"
      by metis
  qed
  have th1: "?inv ` ?S = ?S"
    using image_inverse_permutations by blast
  have th2: "?rhs = finsum R (f \<circ> ?inv) ?S"
    by (simp add: o_def)
  from finsum_reindex[OF _ th0, of f] show ?thesis unfolding th1 th2 using f .
qed

lemma finsum_permutations_compose_right: assumes q: "q permutes S"
  and *: "f \<in> {p. p permutes S} \<rightarrow> carrier R"
  shows "finsum R f {p. p permutes S} = finsum R (\<lambda>p. f(p \<circ> q)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{p. p permutes S}"
  let ?inv = "Hilbert_Choice.inv"
  have th0: "?rhs = finsum R (f \<circ> (\<lambda>p. p \<circ> q)) ?S"
    by (simp add: o_def)
  have th1: "inj_on (\<lambda>p. p \<circ> q) ?S"
  proof (auto simp add: inj_on_def)
    fix p r
    assume "p permutes S"
      and r: "r permutes S"
      and rp: "p \<circ> q = r \<circ> q"
    then have "p \<circ> (q \<circ> ?inv q) = r \<circ> (q \<circ> ?inv q)"
      by (simp add: o_assoc)
    with permutes_surj[OF q, unfolded surj_iff] show "p = r"
      by simp
  qed
  have th3: "(\<lambda>p. p \<circ> q) ` ?S = ?S"
    using image_compose_permutations_right[OF q] by auto
  from finsum_reindex[OF _ th1, of f]
  show ?thesis unfolding th0 th1 th3 using * .
qed

end

text \<open>The following lemma is slightly generalized from Determinants.thy in HMA.\<close>

lemma finite_bounded_functions:
  assumes fS: "finite S"
  shows "finite T \<Longrightarrow> finite {f. (\<forall>i \<in> T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)}"
proof (induct T rule: finite_induct)
  case empty
  have th: "{f. \<forall>i. f i = i} = {id}"
    by auto
  show ?case
    by (auto simp add: th)
next
  case (insert a T)
  let ?f = "\<lambda>(y,g) i. if i = a then y else g i"
  let ?S = "?f ` (S \<times> {f. (\<forall>i\<in>T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)})"
  have "?S = {f. (\<forall>i\<in> insert a T. f i \<in> S) \<and> (\<forall>i. i \<notin> insert a T \<longrightarrow> f i = i)}"
    apply (auto simp add: image_iff)
    apply (rule_tac x="x a" in bexI)
    apply (rule_tac x = "\<lambda>i. if i = a then i else x i" in exI)
    apply (insert insert, auto)
    done
  with finite_imageI[OF finite_cartesian_product[OF fS insert.hyps(3)], of ?f]
  show ?case
    by metis
qed

lemma finite_bounded_functions':
  assumes fS: "finite S"
  shows "finite T \<Longrightarrow> finite {f. (\<forall>i \<in> T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = j)}"
proof (induct T rule: finite_induct)
  case empty
  have th: "{f. \<forall>i. f i = j} = {(\<lambda> x. j)}"
    by auto
  show ?case
    by (auto simp add: th)
next
  case (insert a T)
  let ?f = "\<lambda>(y,g) i. if i = a then y else g i"
  let ?S = "?f ` (S \<times> {f. (\<forall>i\<in>T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = j)})"
  have "?S = {f. (\<forall>i\<in> insert a T. f i \<in> S) \<and> (\<forall>i. i \<notin> insert a T \<longrightarrow> f i = j)}"
    apply (auto simp add: image_iff)
    apply (rule_tac x="x a" in bexI)
    apply (rule_tac x = "\<lambda>i. if i = a then j else x i" in exI)
    apply (insert insert, auto)
    done
  with finite_imageI[OF finite_cartesian_product[OF fS insert.hyps(3)], of ?f]
  show ?case
    by metis
qed

context
  fixes A :: "'a set" 
    and B :: "'b set"
    and a_to_b :: "'a \<Rightarrow> 'b"
    and b_to_a :: "'b \<Rightarrow> 'a"
  assumes ab: "\<And> a. a \<in> A \<Longrightarrow> a_to_b a \<in> B"
    and ba: "\<And> b. b \<in> B \<Longrightarrow> b_to_a b \<in> A"
    and ab_ba: "\<And> a. a \<in> A \<Longrightarrow> b_to_a (a_to_b a) = a"
    and ba_ab: "\<And> b. b \<in> B \<Longrightarrow> a_to_b (b_to_a b) = b"
begin

qualified lemma permutes_memb: fixes p :: "'b \<Rightarrow> 'b"
  assumes p: "p permutes B"
  and a: "a \<in> A"
  defines "ip \<equiv> Hilbert_Choice.inv p"
  shows "a \<in> A" "a_to_b a \<in> B" "ip (a_to_b a) \<in> B" "p (a_to_b a) \<in> B" 
    "b_to_a (p (a_to_b a)) \<in> A" "b_to_a (ip (a_to_b a)) \<in> A"
proof -
  let ?b = "a_to_b a"
  from p have ip: "ip permutes B" unfolding ip_def by (rule permutes_inv)
  note in_ip = permutes_in_image[OF ip]
  note in_p = permutes_in_image[OF p]
  show a: "a \<in> A" by fact
  show b: "?b \<in> B" by (rule ab[OF a])
  show pb: "p ?b \<in> B" unfolding in_p by (rule b)
  show ipb: "ip ?b \<in> B" unfolding in_ip by (rule b)
  show "b_to_a (p ?b) \<in> A" by (rule ba[OF pb])
  show "b_to_a (ip ?b) \<in> A" by (rule ba[OF ipb])
qed

lemma permutes_bij_main: 
  "{p . p permutes A} \<supseteq> (\<lambda> p a. if a \<in> A then b_to_a (p (a_to_b a)) else a) ` {p . p permutes B}" 
  (is "?A \<supseteq> ?f ` ?B")
proof 
  note d = permutes_def
  let ?g = "\<lambda> q b. if b \<in> B then a_to_b (q (b_to_a b)) else b"
  let ?inv = "Hilbert_Choice.inv"
  fix p
  assume p: "p \<in> ?f ` ?B"
  then obtain q where q: "q permutes B" and p: "p = ?f q" by auto    
  let ?iq = "?inv q"
  from q have iq: "?iq permutes B" by (rule permutes_inv)
  note in_iq = permutes_in_image[OF iq]
  note in_q = permutes_in_image[OF q]
  have qiB: "\<And> b. b \<in> B \<Longrightarrow> q (?iq b) = b" using q by (rule permutes_inverses)
  have iqB: "\<And> b. b \<in> B \<Longrightarrow> ?iq (q b) = b" using q by (rule permutes_inverses)
  from q[unfolded d] 
  have q1: "\<And> b. b \<notin> B \<Longrightarrow> q b = b" 
   and q2: "\<And> b. \<exists>!b'. q b' = b" by auto
  note memb = permutes_memb[OF q]
  show "p \<in> ?A" unfolding p d
  proof (rule, intro conjI impI allI, force)
    fix a
    show "\<exists>!a'. ?f q a' = a"
    proof (cases "a \<in> A")
      case True
      note a = memb[OF True]
      let ?a = "b_to_a (?iq (a_to_b a))"
      show ?thesis
      proof 
        show "?f q ?a = a" using a by (simp add: ba_ab qiB ab_ba)
      next
        fix a'
        assume id: "?f q a' = a"
        show "a' = ?a"
        proof (cases "a' \<in> A")
          case False
          thus ?thesis using id a by auto
        next
          case True
          note a' = memb[OF this]
          from id True have "b_to_a (q (a_to_b a')) = a" by simp
          from arg_cong[OF this, of "a_to_b"] a' a
          have "q (a_to_b a') = a_to_b a" by (simp add: ba_ab)
          from arg_cong[OF this, of ?iq]
          have "a_to_b a' = ?iq (a_to_b a)" unfolding iqB[OF a'(2)] .
          from arg_cong[OF this, of b_to_a] show ?thesis unfolding ab_ba[OF True] .
        qed
      qed
    next
      case False note a = this
      show ?thesis
      proof
        show "?f q a = a" using a by simp
      next
        fix a'
        assume id: "?f q a' = a"
        show "a' = a"
        proof (cases "a' \<in> A")
          case False
          with id show ?thesis by simp
        next
          case True
          note a' = memb[OF True]
          with id False show ?thesis by auto
        qed
      qed
    qed
  qed
qed
end

lemma  permutes_bij': assumes ab: "\<And> a. a \<in> A \<Longrightarrow> a_to_b a \<in> B"
    and ba: "\<And> b. b \<in> B \<Longrightarrow> b_to_a b \<in> A"
    and ab_ba: "\<And> a. a \<in> A \<Longrightarrow> b_to_a (a_to_b a) = a"
    and ba_ab: "\<And> b. b \<in> B \<Longrightarrow> a_to_b (b_to_a b) = b"
  shows "{p . p permutes A} = (\<lambda> p a. if a \<in> A then b_to_a (p (a_to_b a)) else a) ` {p . p permutes B}" 
  (is "?A = ?f ` ?B")
proof -
  note one_dir = ab ba ab_ba ba_ab
  note other_dir = ba ab ba_ab ab_ba
  let ?g = "(\<lambda> p b. if b \<in> B then a_to_b (p (b_to_a b)) else b)"
  define PA where "PA = ?A"
  define f where "f = ?f"
  define g where "g = ?g"
  {
    fix p
    assume "p \<in> PA"
    hence p: "p permutes A" unfolding PA_def by simp
    from p[unfolded permutes_def] have pnA: "\<And> a. a \<notin> A \<Longrightarrow> p a = a" by auto
    have "?f (?g p) = p"
    proof (rule ext)
      fix a
      show "?f (?g p) a = p a"
      proof (cases "a \<in> A")
        case False
        thus ?thesis by (simp add: pnA)
      next
        case True note a = this
        hence "p a \<in> A" unfolding permutes_in_image[OF p] .
        thus ?thesis using a by (simp add: ab_ba ba_ab ab)
      qed
    qed
    hence "f (g p) = p" unfolding f_def g_def .
  }
  hence "f ` g ` PA = PA" by force
  hence id: "?f ` ?g ` ?A = ?A" unfolding PA_def f_def g_def .
  have "?f ` ?B \<subseteq> ?A" by (rule permutes_bij_main[OF one_dir])
  moreover have "?g ` ?A \<subseteq> ?B" by (rule permutes_bij_main[OF ba ab ba_ab ab_ba])
  hence "?f ` ?g ` ?A \<subseteq> ?f ` ?B" by auto
  hence "?A \<subseteq> ?f ` ?B" unfolding id .
  ultimately show ?thesis by blast
qed    

lemma inj_on_nat_permutes: assumes i: "inj_on f (S :: nat set)"
  and fS: "f \<in> S \<rightarrow> S"
  and fin: "finite S"
  and f: "\<And> i. i \<notin> S \<Longrightarrow> f i = i"
  shows "f permutes S"
  unfolding permutes_def
proof (intro conjI allI impI, rule f)
  fix y
  from endo_inj_surj[OF fin _ i] fS have fs: "f ` S = S" by auto
  show "\<exists>!x. f x = y"
  proof (cases "y \<in> S")
    case False
    thus ?thesis by (intro ex1I[of _ y], insert fS f, auto)
  next
    case True
    with fs obtain x where x: "x \<in> S" and fx: "f x = y" by force
    show ?thesis
    proof (rule ex1I, rule fx)
      fix x'
      assume fx': "f x' = y"
      with True f[of x'] have "x' \<in> S" by metis
      from inj_onD[OF i fx[folded fx'] x this]
      show "x' = x" by simp
    qed
  qed
qed


lemma permutes_pair_eq:
  assumes p: "p permutes S"
  shows "{ (p s, s) | s. s \<in> S } = { (s, Hilbert_Choice.inv p s) | s. s \<in> S }"
    (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix x assume "x \<in> ?L"
    then obtain s where x: "x = (p s, s)" and s: "s \<in> S" by auto
    note x
    also have "(p s, s) = (p s, Hilbert_Choice.inv p (p s))"
      using permutes_inj[OF p] inv_f_f by auto
    also have "... \<in> ?R" using s permutes_in_image[OF p] by auto
    finally show "x \<in> ?R".
  qed
  show "?R \<subseteq> ?L"
  proof
    fix x assume "x \<in> ?R"
    then obtain s
      where x: "x = (s, Hilbert_Choice.inv p s)" (is "_ = (s, ?ips)")
        and s: "s \<in> S" by auto
    note x
    also have "(s, ?ips) = (p ?ips, ?ips)"
      using inv_f_f[OF permutes_inj[OF permutes_inv[OF p]]]
      using inv_inv_eq[OF permutes_bij[OF p]] by auto
    also have "... \<in> ?L"
      using s permutes_in_image[OF permutes_inv[OF p]] by auto
    finally show "x \<in> ?L".
  qed
qed

lemma inj_on_finite[simp]:
  assumes inj: "inj_on f A" shows "finite (f ` A) = finite A"
proof
  assume fin: "finite (f ` A)"
  show "finite A"
  proof (cases "card (f ` A) = 0")
    case True thus ?thesis using fin by auto
    next case False 
      hence "card A > 0" unfolding card_image[OF inj] by auto
      thus ?thesis using card_infinite by force
  qed
qed auto

lemma permutes_prod:
  assumes p: "p permutes S"
  shows "(\<Prod>s\<in>S. f (p s) s) = (\<Prod>s\<in>S. f s (Hilbert_Choice.inv p s))"
    (is "?l = ?r")
proof -
  let ?f = "\<lambda>(x,y). f x y"
  let ?ps = "\<lambda>s. (p s, s)"
  let ?ips = "\<lambda>s. (s, Hilbert_Choice.inv p s)"
  have inj1: "inj_on ?ps S" by (rule inj_onI;auto)
  have inj2: "inj_on ?ips S" by (rule inj_onI;auto)
  have "?l = prod ?f (?ps ` S)"
    using prod.reindex[OF inj1, of ?f] by simp
  also have "?ps ` S = {(p s, s) |s. s \<in> S}" by auto
  also have "... = {(s, Hilbert_Choice.inv p s) | s. s \<in> S}"
    unfolding permutes_pair_eq[OF p] by simp
  also have "... = ?ips ` S" by auto
  also have "prod ?f ... = ?r"
    using prod.reindex[OF inj2, of ?f] by simp
  finally show ?thesis.
qed

lemma permutes_sum:
  assumes p: "p permutes S"
  shows "(\<Sum>s\<in>S. f (p s) s) = (\<Sum>s\<in>S. f s (Hilbert_Choice.inv p s))"
    (is "?l = ?r")
proof -
  let ?f = "\<lambda>(x,y). f x y"
  let ?ps = "\<lambda>s. (p s, s)"
  let ?ips = "\<lambda>s. (s, Hilbert_Choice.inv p s)"
  have inj1: "inj_on ?ps S" by (rule inj_onI;auto)
  have inj2: "inj_on ?ips S" by (rule inj_onI;auto)
  have "?l = sum ?f (?ps ` S)"
    using sum.reindex[OF inj1, of ?f] by simp
  also have "?ps ` S = {(p s, s) |s. s \<in> S}" by auto
  also have "... = {(s, Hilbert_Choice.inv p s) | s. s \<in> S}"
    unfolding permutes_pair_eq[OF p] by simp
  also have "... = ?ips ` S" by auto
  also have "sum ?f ... = ?r"
    using sum.reindex[OF inj2, of ?f] by simp
  finally show ?thesis.
qed

lemma inv_inj_on_permutes: "inj_on Hilbert_Choice.inv { p. p permutes S }"
proof (intro inj_onI, unfold mem_Collect_eq)
  let ?i = "Hilbert_Choice.inv"
  fix p q
  assume p: "p permutes S" and q: "q permutes S" and eq: "?i p = ?i q"
  have "?i (?i p) = ?i (?i q)" using eq by simp
  thus "p = q"
    using inv_inv_eq[OF permutes_bij] p q by metis
qed

lemma permutes_others:
  assumes p: "p permutes S" and x: "x \<notin> S" shows "p x = x"
  using p unfolding permutes_def using x by simp

end