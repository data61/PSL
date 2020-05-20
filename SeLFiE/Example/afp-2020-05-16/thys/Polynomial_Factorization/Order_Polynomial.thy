(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
subsection \<open>Order of Polynomial Roots\<close>

text \<open>We extend the collection of results on the order of roots of polynomials.
  Moreover, we provide code-equations to compute the order for a given root and
polynomial.\<close>

theory Order_Polynomial
imports 
  Polynomial_Interpolation.Missing_Polynomial
begin

lemma order_linear[simp]: "order a [:- a, 1:] = Suc 0" unfolding order_def
proof (rule Least_equality, intro notI)
  assume "[:- a, 1:] ^ Suc (Suc 0) dvd [:- a, 1:]"
  from dvd_imp_degree_le[OF this] show False by auto
next
  fix n
  assume *: "\<not> [:- a, 1:] ^ Suc n dvd [:- a, 1:]"
  thus "Suc 0 \<le> n" 
    by (cases n, auto)
qed

declare order_power_n_n[simp]

lemma linear_power_nonzero: "[: a, 1 :] ^ n \<noteq> 0"
proof
  assume "[: a, 1 :]^n = 0"
  with arg_cong[OF this, of degree, unfolded degree_linear_power]
  show False by auto
qed

lemma order_linear_power': "order a ([: b, 1:]^Suc n) = (if b = -a then Suc n else 0)"
proof (cases "b = -a")
  case True
  thus ?thesis unfolding True order_power_n_n by simp
next
  case False
  let ?p = "[: b, 1:]^Suc n"
  from linear_power_nonzero have "?p \<noteq> 0" .
  have p: "?p = (\<Prod>a\<leftarrow> replicate (Suc n) b. [:a, 1:])" by auto
  {
    assume "order a ?p \<noteq> 0"
    then obtain m where ord: "order a ?p = Suc m" by (cases "order a ?p", auto)
    from order[OF \<open>?p \<noteq> 0\<close>, of a, unfolded ord] have dvd: "[:- a, 1:] ^ Suc m dvd ?p" by auto        
    from poly_linear_exp_linear_factors[OF dvd[unfolded p]] False have False by auto
  }
  hence "order a ?p = 0" by auto
  with False show ?thesis by simp
qed

lemma order_linear_power: "order a ([: b, 1:]^n) = (if b = -a then n else 0)" 
proof (cases n)
  case (Suc m)
  show ?thesis unfolding Suc order_linear_power' by simp
qed simp


lemma order_linear': "order a [: b, 1:] = (if b = -a then 1 else 0)"
  using order_linear_power'[of a b 0] by simp

lemma degree_div_less:
  assumes p: "(p::'a::field poly) \<noteq> 0" and dvd: "r dvd p" and deg: "degree r \<noteq> 0" 
  shows "degree (p div r) < degree p"
proof -
  from dvd obtain q where prq: "p = r * q" unfolding dvd_def by auto
  have "degree p = degree r + degree q"
    unfolding prq
    by (rule degree_mult_eq, insert p prq, auto)
  with deg have deg: "degree q < degree p" by auto
  from prq have "q = p div r"
    using deg p by auto
  with deg show ?thesis by auto
qed


lemma order_sum_degree: assumes "p \<noteq> 0"
  shows "sum (\<lambda> a. order a p) { a. poly p a = 0 } \<le> degree p"
proof -
  define n where "n = degree p"
  have "degree p \<le> n" unfolding n_def by auto
  thus ?thesis using \<open>p \<noteq> 0\<close>
  proof (induct n arbitrary: p)
    case (0 p)
    define a where "a = coeff p 0"
    from 0 have "degree p = 0" by auto
    hence p: "p = [: a :]" unfolding a_def
      by (metis degree_0_id)
    with 0 have "a \<noteq> 0" by auto
    thus ?case unfolding p by auto 
  next
    case (Suc m p)
    note order = order[OF \<open>p \<noteq> 0\<close>]
    show ?case
    proof (cases "\<exists> a. poly p a = 0")
      case True
      then obtain a where root: "poly p a = 0" by auto
      with order_root[of p a] Suc obtain n where orda: "order a p = Suc n" 
        by (cases "order a p", auto)
      let ?a = "[: -a, 1 :] ^ Suc n"
      from order_decomp[OF \<open>p \<noteq> 0\<close>, of a, unfolded orda]
        obtain q where p: "p = ?a * q" and ndvd: "\<not> [:- a, 1:] dvd q" by auto
      from \<open>p \<noteq> 0\<close>[unfolded p] have nz: "?a \<noteq> 0" "q \<noteq> 0" by auto
      hence deg: "degree p = degree ?a + degree q" unfolding p
        by (subst degree_mult_eq, auto)
      have ord: "\<And> a. order a p = order a ?a + order a q"
        unfolding p
        by (subst order_mult, insert nz, auto)
      have roots: "{ a. poly p a = 0 } = insert a ({ a. poly q a = 0} - {a})" using root
        unfolding p poly_mult by auto
      have fin: "finite {a. poly q a = 0}" by (rule poly_roots_finite[OF \<open>q \<noteq> 0\<close>])
      have "Suc n = order a p" using orda by simp
      also have "\<dots> = Suc n + order a q" unfolding ord order_linear_power' by simp
      finally have "order a q = 0" by auto
      with order_root[of q a] \<open>q \<noteq> 0\<close> have qa: "poly q a \<noteq> 0" by auto
      have "(\<Sum>a\<in>{a. poly q a = 0} - {a}. order a p) = (\<Sum>a\<in>{a. poly q a = 0} - {a}. order a q)"
      proof (rule sum.cong[OF refl])
        fix b
        assume "b \<in> {a. poly q a = 0} - {a}"
        hence "b \<noteq> a" by auto
        hence "order b ?a = 0" unfolding order_linear_power' by simp
        thus "order b p = order b q" unfolding ord by simp
      qed
      also have "\<dots> = (\<Sum>a\<in>{a. poly q a = 0}. order a q)" using qa by auto
      also have "\<dots> \<le> degree q"
        by (rule Suc(1)[OF _ \<open>q \<noteq> 0\<close>], 
        insert deg[unfolded degree_linear_power] Suc(2), auto)
      finally have "(\<Sum>a\<in>{a. poly q a = 0} - {a}. order a p) \<le> degree q" .      
      thus ?thesis unfolding roots deg using fin
        by (subst sum.insert, simp_all only: degree_linear_power, auto simp: orda)
    qed auto
  qed
qed 

lemma order_code[code]: "order (a::'a::idom_divide) p = 
  (if p = 0 then Code.abort (STR ''order of polynomial 0 undefined'') (\<lambda> _. order a p) 
   else if poly p a \<noteq> 0 then 0 else Suc (order a (p div [: -a, 1 :])))"
proof (cases "p = 0")
  case False note p = this
  note order = order[OF p]
  show ?thesis 
  proof (cases "poly p a = 0")
    case True
    with order_root[of p a] p obtain n where ord: "order a p = Suc n" 
      by (cases "order a p", auto)
    from this(1) have "[: -a, 1 :] dvd p" 
      using True poly_eq_0_iff_dvd by blast
    then obtain q where p: "p = [: -a, 1 :] * q" unfolding dvd_def by auto
    have ord: "order a p = order a [: -a, 1 :] + order a q"
      using p False order_mult[of "[: -a, 1 :]" q] by auto
    have q: "p div [: -a, 1 :] = q" using False p 
      by (metis mult_zero_left nonzero_mult_div_cancel_left)
    show ?thesis unfolding ord q using False True by auto
  next
    case False
    with order_root[of p a] p show ?thesis by auto
  qed
qed auto

end
