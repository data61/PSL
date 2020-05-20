section \<open>Real Factorization\<close>

text \<open>This theory contains an algorithm to completely factorize real polynomials with rational
  coefficients. It internally does a complex polynomial factorization, and then combines 
  all non-real roots with their conjugates.\<close>

theory Real_Factorization
imports 
  Complex_Algebraic_Numbers
begin

fun delete_cnj :: "complex \<Rightarrow> nat \<Rightarrow> (complex \<times> nat) list \<Rightarrow> (complex \<times> nat) list" where
  "delete_cnj x i ((y,j) # yjs) = (if x = y then if Suc j = i then yjs else if Suc j > i then
    ((y,j - i) # yjs) else delete_cnj x (i - Suc j) yjs else (y,j) # delete_cnj x i yjs)"
| "delete_cnj _ _ [] = []"

lemma delete_cnj_length[termination_simp]: "length (delete_cnj x i yjs) \<le> length yjs"
  by (induct x i yjs rule: delete_cnj.induct, auto)

fun complex_roots_to_real_factorization :: "(complex \<times> nat) list \<Rightarrow> (real poly \<times> nat)list" where
  "complex_roots_to_real_factorization [] = []"
| "complex_roots_to_real_factorization ((x,i) # xs) = (if x \<in> \<real> then 
    ([:-(Re x),1:],Suc i) # complex_roots_to_real_factorization xs else 
    let xx = cnj x; ys = delete_cnj xx (Suc i) xs; p = map_poly Re ([:-x,1:] * [:-xx,1:])
    in (p,Suc i) # complex_roots_to_real_factorization ys)"

definition factorize_real_poly :: "real poly \<Rightarrow> (real \<times> (real poly \<times> nat) list) option" where
  "factorize_real_poly p \<equiv> map_option 
    (\<lambda> (c,ris). (Re c, complex_roots_to_real_factorization ris)) 
    (factorize_complex_main (map_poly of_real p))"


lemma monic_imp_nonzero: "monic x \<Longrightarrow> x \<noteq> 0" for x :: "'a :: semiring_1 poly" by auto

lemma delete_cnj: assumes 
  "order x (\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i) \<ge> si" "si \<noteq> 0"
  shows "(\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i) =
    [:- x, 1:] ^ si * (\<Prod>(x, i)\<leftarrow>delete_cnj x si xis. [:- x, 1:] ^ Suc i)"
using assms
proof (induct x si xis rule: delete_cnj.induct)
  case (2 x si)
  hence "order x 1 \<ge> 1" by auto
  hence "[:-x,1:]^1 dvd 1" unfolding order_divides by simp
  from power_le_dvd[OF this, of 1] \<open>si \<noteq> 0\<close> have "[:- x, 1:] dvd 1" by simp
  from divides_degree[OF this] 
  show ?case by auto
next
  case (1 x i y j yjs)
  note IH = 1(1-2)
  let ?yj = "[:-y,1:]^Suc j"
  let ?yjs = "(\<Prod>(x,i)\<leftarrow>yjs. [:- x, 1:] ^ Suc i)"
  let ?x = "[: - x, 1 :]"
  let ?xi = "?x ^ i"
  have "monic (\<Prod>(x,i)\<leftarrow>(y, j) # yjs. [:- x, 1:] ^ Suc i)"
    by (rule monic_prod_list_pow) then have "monic (?yj * ?yjs)" by simp
  from monic_imp_nonzero[OF this] have yy0: "?yj * ?yjs \<noteq> 0" by auto
  have id: "(\<Prod>(x,i)\<leftarrow>(y, j) # yjs. [:- x, 1:] ^ Suc i) = ?yj * ?yjs" by simp
  from 1(3-) have ord: "i \<le> order x (?yj * ?yjs)" and i: "i \<noteq> 0" unfolding id by auto
  from ord[unfolded order_mult[OF yy0]] have ord: "i \<le> order x ?yj + order x ?yjs" .
  from this[unfolded order_linear_power'] 
  have ord: "i \<le> (if y = x then Suc j else 0) + order x ?yjs" by simp
  show ?case 
  proof (cases "x = y")
    case False
    from ord False have "i \<le> order x ?yjs" by simp
    note IH = IH(2)[OF False this i]
    from False have del: "delete_cnj x i ((y, j) # yjs) = (y,j) # delete_cnj x i yjs" by simp    
    show ?thesis unfolding del id IH
      by (simp add: ac_simps)
  next
    case True note xy = this
    note IH = IH(1)[OF True]
    show ?thesis 
    proof (cases "Suc j \<ge> i")
      case False
      from ord have ord: "i - Suc j \<le> order x ?yjs" unfolding xy by simp
      have "?xi = ?x ^ (Suc j + (i - Suc j))" using False by simp
      also have "\<dots> = ?x ^ Suc j * ?x ^ (i - Suc j)"
        unfolding power_add by simp
      finally have xi: "?xi = ?x ^ Suc j * ?x ^ (i - Suc j)" .
      from False have "Suc j \<noteq> i" "\<not> i < Suc j" "i - Suc j \<noteq> 0" by auto
      note IH = IH[OF this(1,2) ord this(3)]
      from xy False have del: "delete_cnj x i ((y, j) # yjs) = delete_cnj x (i - Suc j) yjs" by auto
      show ?thesis unfolding del id unfolding IH xi unfolding xy by simp
    next
      case True
      hence "Suc j = i \<or> i < Suc j" by auto
      thus ?thesis
      proof
        assume i: "Suc j = i"
        from xy i have del: "delete_cnj x i ((y, j) # yjs) = yjs" by simp
        show ?thesis unfolding id del unfolding xy i by simp
      next
        assume ij: "i < Suc j"
        with xy i have del: "delete_cnj x i ((y, j) # yjs) = (y, j - i) # yjs" by simp
        from ij have idd: "Suc j = i + Suc (j - i)" by simp
        show ?thesis unfolding id del unfolding xy idd power_add by simp
      qed
    qed
  qed
qed


lemma factorize_real_poly: assumes fp: "factorize_real_poly p = Some (c,qis)"
  shows 
  "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" 
  "(q,j) \<in> set qis \<Longrightarrow> irreducible q \<and> j \<noteq> 0 \<and> monic q \<and> degree q \<in> {1,2}"
proof -
  interpret map_poly_inj_idom_hom of_real..
  have "(p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)) \<and> ((q,j) \<in> set qis \<longrightarrow> irreducible q \<and> j \<noteq> 0 \<and> monic q \<and> degree q \<in> {1,2})"
  proof (cases "p = 0")
    case True
    have "factorize_real_poly p = Some (0,[])" unfolding True
      by (simp add: factorize_real_poly_def factorize_complex_main_def yun_factorization_def)
    with fp have id: "c = 0" "qis = []" by auto
    thus ?thesis unfolding True by simp
  next
    case False note p0 = this
    let ?c = complex_of_real
    let ?rp = "map_poly Re"
    let ?cp = "map_poly ?c"
    let ?p = "?cp p"
    from fp[unfolded factorize_real_poly_def]
      obtain d xis where fp: "factorize_complex_main ?p = Some (d,xis)"
      and c: "c = Re d" and qis: "qis = complex_roots_to_real_factorization xis" by auto
    from factorize_complex_main[OF fp] have p: "?p = smult d (\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)" 
      (is "_ = smult d ?q") .
    from arg_cong[OF this, of "\<lambda> p. coeff p (degree p)"]
    have "coeff ?p (degree ?p) = coeff (smult d ?q) (degree (smult d ?q))" .
    also have "coeff ?p (degree ?p) = ?c (coeff p (degree p))" by simp
    also have "coeff (smult d ?q) (degree (smult d ?q)) = d * coeff ?q (degree ?q)"
      by simp
    also have "monic ?q" by (rule monic_prod_list_pow)
    finally have d: "d = ?c (coeff p (degree p))" by auto
    from arg_cong[OF this, of Re, folded c] have c: "c = coeff p (degree p)" by auto
    have "set (coeffs ?p) \<subseteq> \<real>" by auto
    with p have q': "set (coeffs (smult d ?q)) \<subseteq> \<real>" by auto
    from d p0 have d0: "d \<noteq> 0" by auto
    have "smult d ?q = [:d:] * ?q" by auto
    from real_poly_factor[OF q'[unfolded this]] d0 d
    have q: "set (coeffs ?q) \<subseteq> \<real>" by auto 
    have "p = ?rp ?p"
      by (rule sym, subst map_poly_map_poly, force, rule map_poly_idI, auto)
    also have "\<dots> = ?rp (smult d ?q)" unfolding p ..
    also have "?q = ?cp (?rp ?q)"
      by (rule sym, rule map_poly_of_real_Re, insert q, auto)
    also have "d = ?c c" unfolding d c ..
    also have "smult (?c c) (?cp (?rp ?q)) = ?cp (smult c (?rp ?q))" by (simp add: hom_distribs)
    also have "?rp \<dots> = smult c (?rp ?q)" 
      by (subst map_poly_map_poly, force, rule map_poly_idI, auto)
    finally have p: "p = smult c (?rp ?q)" .
    let ?fact = complex_roots_to_real_factorization
    have "?rp ?q = (\<Prod>(q, i)\<leftarrow>qis. q ^ i) \<and>
      ((q, j) \<in> set qis \<longrightarrow> irreducible q \<and> j \<noteq> 0 \<and> monic q \<and> degree q \<in> {1, 2})"
      using q unfolding qis
    proof (induct xis rule: complex_roots_to_real_factorization.induct)
      case 1
      show ?case by simp
    next
      case (2 x i xis)
      note IH = 2(1-2)
      note prems = 2(3)
      let ?xi = "[:- x, 1:] ^ Suc i"
      let ?xis = "(\<Prod>(x, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)"
      have id: "(\<Prod>(x, i)\<leftarrow>((x,i) # xis). [:- x, 1:] ^ Suc i) = ?xi * ?xis"
        by simp
      show ?case
      proof (cases "x \<in> \<real>")
        case True
        have xi: "set (coeffs ?xi) \<subseteq> \<real>"
          by (rule real_poly_power, insert True, auto)
        have xis: "set (coeffs ?xis) \<subseteq> \<real>" 
          by (rule real_poly_factor[OF prems[unfolded id] xi], rule linear_power_nonzero)
        note IH = IH(1)[OF True xis]
        have "?rp (?xi * ?xis) = ?rp ?xi * ?rp ?xis"
          by (rule map_poly_Re_mult[OF xi xis])
        also have "?rp ?xi = (?rp [: -x,1 :])^Suc i"
          by (rule map_poly_Re_power, insert True, auto)
        also have "?rp [: -x,1 :] = [:-(Re x),1:]" by auto
        also have "?rp ?xis = (\<Prod> (a,b) \<leftarrow> ?fact xis. a ^ b)"
          using IH by auto        
        also have "[:- Re x, 1:] ^ Suc i * (\<Prod> (a,b) \<leftarrow> ?fact xis. a ^ b) = 
          (\<Prod> (a,b) \<leftarrow> ?fact ((x,i) # xis). a ^ b)" using True by simp
        finally have idd: "?rp (?xi * ?xis) = (\<Prod> (a,b) \<leftarrow> ?fact ((x,i) # xis). a ^ b)" .
        show ?thesis unfolding id idd
        proof (intro conjI, force, intro impI)
          assume "(q, j) \<in> set (?fact ((x, i) # xis))"
          hence "(q,j) \<in> set (?fact xis) \<or> (q = [:- Re x, 1:] \<and> j = Suc i)"
            using True by auto
          thus "irreducible q \<and> j \<noteq> 0 \<and> monic q \<and> degree q \<in> {1, 2}"
          proof
            assume "(q,j) \<in> set (?fact xis)"
            with IH show ?thesis by auto
          next
            assume "q = [:- Re x, 1:] \<and> j = Suc i"
            with linear_irreducible_field[of "[:- Re x, 1:]"] show ?thesis by auto
          qed
        qed
      next
        case False
        define xi where "xi = [:Re x * Re x + Im x * Im x, - (2 * Re x), 1:]"
        obtain xx where xx: "xx = cnj x" by auto
        have xi: "xi = ?rp ([:-x,1:] * [:-xx,1:])" unfolding xx xi_def by auto
        have cpxi: "?cp xi = [:-x,1:] * [:-xx,1:]" unfolding xi_def
          by (cases x, auto simp: xx legacy_Complex_simps)
        obtain yis where yis: "yis = delete_cnj xx (Suc i) xis" by auto
        from False have fact: "?fact ((x,i) # xis) = ((xi,Suc i) # ?fact yis)"
          unfolding xi_def xx yis by simp
        note IH = IH(2)[OF False xx yis xi]
        have "irreducible xi"
          apply (fold irreducible_connect_field)
        proof (rule irreducible\<^sub>dI)
          show "degree xi > 0" unfolding xi by auto
          fix q p :: "real poly" 
          assume "degree q > 0" "degree q < degree xi" and qp: "xi = q * p"
          hence dq: "degree q = 1" unfolding xi by auto
          have dxi: "degree xi = 2" "xi \<noteq> 0" unfolding xi by auto
          with qp have "q \<noteq> 0" "p \<noteq> 0" by auto
          hence "degree xi = degree q + degree p" unfolding qp
            by (rule degree_mult_eq)
          with dq have dp: "degree p = 1" unfolding dxi by simp
          {
            fix c :: complex
            assume rt: "poly (?cp xi) c = 0"
            hence "poly (?cp q * ?cp p) c = 0" by (simp add: qp hom_distribs)
            hence "(poly (?cp q) c = 0 \<or> poly (?cp p) c = 0)" by auto
            hence "c = roots1 (?cp q) \<or> c = roots1 (?cp p)"
              using roots1[of "?cp q"] roots1[of "?cp p"] dp dq by auto
            hence "c \<in> \<real>" unfolding roots1_def by auto
            hence "c \<noteq> x" using False by auto
          }
          hence "poly (?cp xi) x \<noteq> 0" by auto
          thus False unfolding cpxi by simp
        qed
        hence xi': "irreducible xi" "monic xi" "degree xi = 2"
          unfolding xi by auto
        let ?xxi = "[:- xx, 1:] ^ Suc i"
        let ?yis = "(\<Prod>(x, i)\<leftarrow>yis. [:- x, 1:] ^ Suc i)"
        let ?yi = "(?cp xi)^Suc i"
        have yi: "set (coeffs ?yi) \<subseteq> \<real>"
          by (rule real_poly_power, auto simp: xi)
        have mon: "monic (\<Prod>(x, i)\<leftarrow>(x, i) # xis. [:- x, 1:] ^ Suc i)"
          by (rule monic_prod_list_pow)
        from monic_imp_nonzero[OF this] have xixis: "?xi * ?xis \<noteq> 0" unfolding id by auto
        from False have xxx: "xx \<noteq> x" unfolding xx by (cases x, auto simp: legacy_Complex_simps Reals_def)
        from prems[unfolded id] have prems: "set (coeffs (?xi * ?xis)) \<subseteq> \<real>" .
        from id have "[:- x, 1:] ^ Suc i dvd ?xi * ?xis" by auto
        from xixis this[unfolded order_divides] 
        have "order x (?xi * ?xis) \<ge> Suc i" by auto
        with complex_conjugate_order[OF prems xixis, of x, folded xx]
        have "order xx (?xi * ?xis) \<ge> Suc i" by auto
        hence "order xx ?xi + order xx ?xis \<ge> Suc i" unfolding order_mult[OF xixis] .
        also have "order xx ?xi = 0" unfolding order_linear_power' using xxx by simp
        finally have "order xx ?xis \<ge> Suc i" by simp
        hence yis: "?xis = ?xxi * ?yis" unfolding yis 
          by (rule delete_cnj, simp)
        hence "?xi * ?xis = (?xi * ?xxi) * ?yis" by (simp only: ac_simps)
        also have "?xi * ?xxi = ([:- x, 1:] * [:- xx, 1:])^Suc i"
          by (metis power_mult_distrib)
        also have "[:- x, 1:] * [:- xx, 1:] = ?cp xi" unfolding cpxi ..
        finally have idd: "?xi * ?xis = (?cp xi)^Suc i * ?yis" by simp
        from prems[unfolded idd] have R: "set (coeffs ((?cp xi)^Suc i * ?yis)) \<subseteq> \<real>" .
        have yis: "set (coeffs ?yis) \<subseteq> \<real>"
          by (rule real_poly_factor[OF R yi], auto, auto simp: xi_def)
        note IH = IH[OF yis] 
        have "?rp (?xi * ?xis) = ?rp ?yi * ?rp ?yis" unfolding idd
          by (rule map_poly_Re_mult[OF yi yis])
        also have "?rp ?yi = xi^Suc i" by (fold hom_distribs, rule map_poly_Re_of_real)
        also have "?rp ?yis = (\<Prod> (a,b) \<leftarrow> ?fact yis. a ^ b)"
          using IH by auto
        also have "xi ^ Suc i * (\<Prod> (a,b) \<leftarrow> ?fact yis. a ^ b) = 
          (\<Prod> (a,b) \<leftarrow> ?fact ((x,i) # xis). a ^ b)" unfolding fact by simp
        finally have idd: "?rp (?xi * ?xis) = (\<Prod> (a,b) \<leftarrow> ?fact ((x,i) # xis). a ^ b)" .
        show ?thesis unfolding id idd fact using IH xi' by auto
      qed
    qed
    thus ?thesis unfolding p by simp
  qed
  thus "p = smult c (\<Prod>(q, i)\<leftarrow>qis. q ^ i)" 
  "(q,j) \<in> set qis \<Longrightarrow> irreducible q \<and> j \<noteq> 0 \<and> monic q \<and> degree q \<in> {1,2}" by blast+
qed
end
