(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Rational Factorization\<close>

text \<open>We combine the rational root test, the
  formulas for explicit roots, and the Kronecker's factorization algorithm to provide a
  basic factorization algorithm for polynomial over rational numbers. Moreover, also the roots
  of a rational polynomial can be determined.\<close>
  
theory Rational_Factorization
imports
  Explicit_Roots
  Kronecker_Factorization
  Square_Free_Factorization
  Rational_Root_Test
  Gcd_Rat_Poly
  Show.Show_Poly
begin

function roots_of_rat_poly_main :: "rat poly \<Rightarrow> rat list" where 
  "roots_of_rat_poly_main p = (let n = degree p in if n = 0 then [] else if n = 1 then [roots1 p]
  else if n = 2 then rat_roots2 p else 
  case rational_root_test p of None \<Rightarrow> [] | Some x \<Rightarrow> x # roots_of_rat_poly_main (p div [:-x,1:]))"
  by pat_completeness auto

termination by (relation "measure degree", 
  auto dest: rational_root_test(1) intro!: degree_div_less simp: poly_eq_0_iff_dvd)

lemma roots_of_rat_poly_main_code[code]: "roots_of_rat_poly_main p = (let n = degree p in if n = 0 then [] else if n = 1 then [roots1 p]
  else if n = 2 then rat_roots2 p else 
  case rational_root_test p of None \<Rightarrow> [] | Some x \<Rightarrow> x # roots_of_rat_poly_main (p div [:-x,1:]))"
proof -
  note d = roots_of_rat_poly_main.simps[of p] Let_def
  show ?thesis
  proof (cases "rational_root_test p")
    case (Some x)
    let ?x = "[:-x,1:]"
    from rational_root_test(1)[OF Some] have  "?x dvd p" 
      by (simp add: poly_eq_0_iff_dvd)
    from dvd_mult_div_cancel[OF this]
    have pp: "p div ?x = ?x * (p div ?x) div ?x" by simp
    then show ?thesis unfolding d Some by auto
  qed (simp add: d)
qed

lemma roots_of_rat_poly_main: "p \<noteq> 0 \<Longrightarrow> set (roots_of_rat_poly_main p) = {x. poly p x = 0}"
proof (induct p rule: roots_of_rat_poly_main.induct)
  case (1 p)
  note IH = 1(1)
  note p = 1(2)
  let ?n = "degree p"
  let ?rr = "roots_of_rat_poly_main"
  show ?case
  proof (cases "?n = 0")
    case True
    from roots0[OF p True] True show ?thesis by simp
  next
    case False note 0 = this
    show ?thesis
    proof (cases "?n = 1")
      case True
      from roots1[OF True] True show ?thesis by simp
    next
      case False note 1 = this
      show ?thesis
      proof (cases "?n = 2")
        case True
        from rat_roots2[OF True] True show ?thesis by simp
      next
        case False note 2 = this
        from 0 1 2 have id: "?rr p = (case rational_root_test p of None \<Rightarrow> [] | Some x \<Rightarrow> 
          x # ?rr (p div [: -x, 1 :]))" by simp
        show ?thesis
        proof (cases "rational_root_test p")
          case None
          from rational_root_test(2)[OF None] None id show ?thesis by simp
        next
          case (Some x)
          from rational_root_test(1)[OF Some] have "[: -x, 1:] dvd p"         
            by (simp add: poly_eq_0_iff_dvd)
          from dvd_mult_div_cancel[OF this]
          have pp: "p = [: -x, 1:] * (p div [: -x, 1:])" by simp
          with p have p: "p div [:- x, 1:] \<noteq> 0" by auto
          from arg_cong[OF pp, of "\<lambda> p. {x. poly p x = 0}"]
             rational_root_test(1)[OF Some] IH[OF refl 0 1 2 Some p]  show ?thesis
            unfolding id Some by auto
        qed
      qed
    qed
  qed
qed

declare roots_of_rat_poly_main.simps[simp del]

definition roots_of_rat_poly :: "rat poly \<Rightarrow> rat list" where
  "roots_of_rat_poly p \<equiv> let (c,pis) = yun_factorization gcd_rat_poly p in
    concat (map (roots_of_rat_poly_main o fst) pis)"

lemma roots_of_rat_poly: assumes p: "p \<noteq> 0"
  shows "set (roots_of_rat_poly p) = {x. poly p x = 0}"
proof -
  obtain c pis where yun: "yun_factorization gcd p = (c,pis)" by force
  from yun
  have res: "roots_of_rat_poly p = concat (map (roots_of_rat_poly_main \<circ> fst) pis)"
    by (auto simp: roots_of_rat_poly_def split: if_splits)
  note yun = square_free_factorizationD(1,2,4)[OF yun_factorization(1)[OF yun]]
  from yun(1) p have c: "c \<noteq> 0" by auto
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  have "{x. poly p x = 0} = {x. poly (\<Prod>(a, i)\<in>set pis. a ^ Suc i) x = 0}"
    unfolding p using c by auto
  also have "\<dots> = \<Union> ((\<lambda> p. {x. poly p x = 0}) ` fst ` set pis)" (is "_ = ?r")
    by (subst poly_prod_0, force+)
  finally have r: "{x. poly p x = 0} = ?r" .
  {
    fix p i
    assume p: "(p,i) \<in> set pis"
    have "set (roots_of_rat_poly_main p) = {x. poly p x = 0}"
      by (rule roots_of_rat_poly_main, insert yun(2) p, force)
  } note main = this
  have "set (roots_of_rat_poly p) = \<Union> ((\<lambda> (p, i). set (roots_of_rat_poly_main p)) ` set pis)" 
    unfolding res o_def by auto
  also have "\<dots> = ?r" using main by auto
  finally show ?thesis unfolding r by simp
qed

definition root_free :: "'a :: comm_semiring_0 poly \<Rightarrow> bool" where
  "root_free p = (degree p = 1 \<or> (\<forall> x. poly p x \<noteq> 0))"

lemma irreducible_root_free:
  fixes p :: "'a :: idom poly"
  assumes "irreducible p" shows "root_free p"
proof-
  from assms have p0: "p \<noteq> 0" by auto
  {
    fix x
    assume "poly p x = 0" and degp: "degree p \<noteq> 1"
    hence "[:-x,1:] dvd p" using poly_eq_0_iff_dvd by blast
    then obtain q where p: "p = [:-x,1:] * q" by (elim dvdE)
    with p0 have q0: "q \<noteq> 0" by auto
    from irreducibleD[OF assms p]
    have "q dvd 1" by (metis one_neq_zero poly_1 poly_eq_0_iff_dvd)
    then have "degree q = 0" by (simp add: poly_dvd_1)
    with degree_mult_eq[of "[:-x,1:]" q, folded p] q0 degp
    have False by auto
  }
  thus ?thesis unfolding root_free_def by auto
qed

partial_function (tailrec) factorize_root_free_main :: "rat poly \<Rightarrow> rat list \<Rightarrow> rat poly list \<Rightarrow> rat \<times> rat poly list" where
  [code]: "factorize_root_free_main p xs fs = (case xs of Nil \<Rightarrow> 
     let l = coeff p (degree p); q = smult (inverse l) p in (l, (if q = 1 then fs else q # fs) )
  | x # xs \<Rightarrow> 
    if poly p x = 0 then factorize_root_free_main (p div [:-x,1:]) (x # xs) ([:-x,1:] # fs)
    else factorize_root_free_main p xs fs)"

definition factorize_root_free :: "rat poly \<Rightarrow> rat \<times> rat poly list" where
  "factorize_root_free p = (if degree p = 0 then (coeff p 0,[]) else
     factorize_root_free_main p (roots_of_rat_poly p) [])"

lemma factorize_root_free_0[simp]: "factorize_root_free 0 = (0,[])" 
  unfolding factorize_root_free_def by simp

lemma factorize_root_free: assumes res: "factorize_root_free p = (c,qs)" 
  shows "p = smult c (prod_list qs)" 
  "\<And> q. q \<in> set qs \<Longrightarrow> root_free q \<and> monic q \<and> degree q \<noteq> 0"
proof -
  have "p = smult c (prod_list qs) \<and> (\<forall> q \<in> set qs. root_free q \<and> monic q \<and> degree q \<noteq> 0)"
  proof (cases "degree p = 0")
    case True
    thus ?thesis using res unfolding factorize_root_free_def by (auto dest: degree0_coeffs) 
  next
    case False
    hence p0: "p \<noteq> 0" by auto
    define fs where "fs = ([] :: rat poly list)" 
    define xs where "xs = roots_of_rat_poly p"
    define q where "q = p"
    obtain n  where n: "n = degree q + length xs" by auto 
    have prod: "p = q * prod_list fs" unfolding q_def fs_def by auto
    have sub: "{x. poly q x = 0} \<subseteq> set xs" using roots_of_rat_poly[OF p0] unfolding q_def xs_def by auto
    have fs: "\<And> q. q \<in> set fs \<Longrightarrow> root_free q \<and> monic q \<and> degree q \<noteq> 0" unfolding fs_def by auto
    have res: "factorize_root_free_main q xs fs = (c,qs)" using res False 
      unfolding xs_def fs_def q_def factorize_root_free_def by auto
    from False have "q \<noteq> 0" unfolding q_def by auto
    from prod sub fs res n this show ?thesis
    proof (induct n arbitrary: q fs xs rule: wf_induct[OF wf_less])
      case (1 n q fs xs)
      note simp = factorize_root_free_main.simps[of q xs fs]
      note IH = 1(1)[rule_format]
      note 0 = 1(2-)[unfolded simp]
      show ?case
      proof (cases xs)
        case Nil
        note 0 = 0[unfolded Nil Let_def]
        hence no_rt: "\<And> x. poly q x \<noteq> 0" by auto
        hence q: "q \<noteq> 0" by auto
        let ?r = "smult (inverse c) q"
        define r where "r = ?r"
        from 0(4-5) have c: "c = coeff q (degree q)" and qs: "qs = (if r = 1 then fs else r # fs)" by (auto simp: r_def)
        from q c qs 0(1) have c0: "c \<noteq> 0" and p: "p = smult c (prod_list (r # fs))" by (auto simp: r_def)
        from p have p: "p = smult c (prod_list qs)" unfolding qs by auto 
        from 0(2,5) c0 c have "root_free ?r" "monic ?r" 
          unfolding root_free_def by auto
        with 0(3) have "\<And> q. q \<in> set qs \<Longrightarrow> root_free q \<and> monic q \<and> degree q \<noteq> 0" unfolding qs 
          by (cases "degree q = 0", insert degree0_coeffs[of q], auto split: if_splits simp: r_def)
        with p show ?thesis by auto
      next
        case (Cons x xs)
        note 0 = 0[unfolded Cons]
        show ?thesis
        proof (cases "poly q x = 0")
          case True
          let ?q = "q div [:-x,1:]"
          let ?x = "[:-x,1:]" 
          let ?fs = "?x # fs"
          let ?xs = "x # xs"
          from True have q: "q = ?q * ?x"
            by (metis dvd_mult_div_cancel mult.commute poly_eq_0_iff_dvd)
          with 0(6) have q': "?q \<noteq> 0" by auto
          have deg: "degree q = Suc (degree ?q)" unfolding arg_cong[OF q, of degree] 
            by (subst degree_mult_eq[OF q'], auto)
          hence n: "degree ?q + length ?xs < n" unfolding 0(5) by auto
          from arg_cong[OF q, of poly] 0(2) have rt: "{x. poly ?q x = 0} \<subseteq> set ?xs" by auto
          have p: "p = ?q * prod_list ?fs" unfolding prod_list.Cons 0(1) mult.assoc[symmetric] q[symmetric] ..
          have "root_free ?x" unfolding root_free_def by auto
          with 0(3) have rf: "\<And> f. f \<in> set ?fs \<Longrightarrow> root_free f \<and> monic f \<and> degree f \<noteq> 0" by auto
          from True 0(4) have res: "factorize_root_free_main ?q ?xs ?fs = (c,qs)" by simp
          show ?thesis
            by (rule IH[OF _ p rt rf res refl q'], insert n, auto)
        next
          case False
          with 0(4) have res: "factorize_root_free_main q xs fs = (c,qs)" by simp
          from 0(5) obtain m where m: "m = degree q + length xs" and n: "n = Suc m" by auto
          from False 0(2) have rt: "{x. poly q x = 0} \<subseteq> set xs" by auto
          show ?thesis by (rule IH[OF _ 0(1) rt 0(3) res m 0(6)], unfold n, auto)
        qed
      qed
    qed
  qed
  thus "p = smult c (prod_list qs)" 
    "\<And> q. q \<in> set qs \<Longrightarrow> root_free q \<and> monic q \<and> degree q \<noteq> 0" by auto
qed


definition rational_proper_factor :: "rat poly \<Rightarrow> rat poly option" where
  "rational_proper_factor p = (if degree p \<le> 1 then None
    else if degree p = 2 then (case rat_roots2 p of Nil \<Rightarrow> None | Cons x xs \<Rightarrow> Some [:-x,1 :])
    else if degree p = 3 then (case rational_root_test p of None \<Rightarrow> None | Some x \<Rightarrow> Some [:-x,1:])
    else kronecker_factorization_rat p)"

lemma degree_1_dvd_root: assumes q: "degree (q :: 'a :: field poly) = 1"
  and rt: "\<And> x. poly p x \<noteq> 0"
  shows "\<not> q dvd p"
proof -
  from degree1_coeffs[OF q] obtain a b where q: "q = [: b, a :]" and a: "a \<noteq> 0" by auto
  have q: "q = smult a [: - (- b / a), 1 :]" unfolding q 
    by (rule poly_eqI, unfold coeff_smult, insert a, auto simp: field_simps coeff_pCons
      split: nat.splits)
  show ?thesis unfolding q smult_dvd_iff poly_eq_0_iff_dvd[symmetric, of _ p] using a rt by auto
qed




lemma rational_proper_factor: 
  "degree p > 0 \<Longrightarrow> rational_proper_factor p = None \<Longrightarrow> irreducible\<^sub>d p" 
  "rational_proper_factor p = Some q \<Longrightarrow> q dvd p \<and> degree q \<ge> 1 \<and> degree q < degree p"
proof -
  let ?rp = "rational_proper_factor p"
  let ?rr = "rational_root_test"
  note d = rational_proper_factor_def[of p]
  have "(degree p > 0 \<longrightarrow> ?rp = None \<longrightarrow> irreducible\<^sub>d p) \<and> 
        (?rp = Some q \<longrightarrow> q dvd p \<and> degree q \<ge> 1 \<and> degree q < degree p)"
  proof (cases "degree p = 0")
    case True
    thus ?thesis unfolding d by auto
  next
    case False note 0 = this
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence "?rp = None" unfolding d by auto
      with linear_irreducible\<^sub>d[OF True] show ?thesis by auto
    next
      case False note 1 = this
      show ?thesis
      proof (cases "degree p = 2")
        case True
        hence rp: "?rp = (case rat_roots2 p of Nil \<Rightarrow> None | Cons x xs \<Rightarrow> Some [:-x,1 :])" unfolding d by auto
        show ?thesis
        proof (cases "rat_roots2 p")
          case Nil
          with rp have rp: "?rp = None" by auto
          from Nil rat_roots2[OF True] have nex: "\<not> (\<exists> x. poly p x = 0)" by auto
          have "irreducible\<^sub>d p"
          proof (rule irreducible\<^sub>dI)
            fix q r :: "rat poly"
            assume "degree q > 0" "degree q < degree p" and p: "p = q * r"
            with True have dq: "degree q = 1" by auto
            have "\<not> q dvd p" by (rule degree_1_dvd_root[OF dq], insert nex, auto)
            with p show False by auto
          qed (insert True, auto)
          with rp show ?thesis by auto
        next
          case (Cons x xs)
          from Cons rat_roots2[OF True] have "poly p x = 0" by auto
          from this[unfolded poly_eq_0_iff_dvd] have x: "[: -x , 1 :] dvd p" by auto
          from Cons rp have rp: "?rp = Some ([: - x, 1 :])" by auto
          show ?thesis using True x unfolding rp by auto
        qed
      next
        case False note 2 = this
        show ?thesis
        proof (cases "degree p = 3")
          case True
          hence rp: "?rp = (case ?rr p of None \<Rightarrow> None | Some x \<Rightarrow> Some [:- x, 1:])" unfolding d by auto
          show ?thesis
          proof (cases "?rr p")
            case None
            from rational_root_test(2)[OF None] have nex: "\<not> (\<exists> x. poly p x = 0)" by auto
            from rp[unfolded None] have rp: "?rp = None" by auto
            have "irreducible\<^sub>d p"
            proof (rule irreducible\<^sub>dI2)
              fix q :: "rat poly"
              assume "degree q > 0" "degree q \<le> degree p div 2"
              with True have dq: "degree q = 1" by auto
              show "\<not> q dvd p" 
                by (rule degree_1_dvd_root[OF dq], insert nex, auto)
            qed (insert True, auto)
            with rp show ?thesis by auto
          next
            case (Some x)
            from rational_root_test(1)[OF Some] have "poly p x = 0" .
            from this[unfolded poly_eq_0_iff_dvd] have x: "[: -x , 1 :] dvd p" by auto
            from Some rp have rp: "?rp = Some ([: - x, 1 :])" by auto
            show ?thesis using True x unfolding rp by auto
          qed
        next
          case False note 3 = this
          let ?kp = "kronecker_factorization_rat p"
          from 0 1 2 3 have d4: "degree p \<ge> 4" and d1: "degree p \<ge> 1" by auto
          hence rp: "?rp = ?kp" using d4 d by auto
          show ?thesis
          proof (cases ?kp)
            case None
            with rp kronecker_factorization_rat(2)[OF None d1] show ?thesis by auto
          next
            case (Some q)
            with rp kronecker_factorization_rat(1)[OF Some] show ?thesis by auto
          qed
        qed
      qed
    qed
  qed
  thus "degree p > 0 \<Longrightarrow> rational_proper_factor p = None \<Longrightarrow> irreducible\<^sub>d p" 
    "rational_proper_factor p = Some q \<Longrightarrow> q dvd p \<and> degree q \<ge> 1 \<and> degree q < degree p" by auto
qed

function factorize_rat_poly_main :: "rat \<Rightarrow> rat poly list \<Rightarrow> rat poly list \<Rightarrow> rat \<times> rat poly list" where
  "factorize_rat_poly_main c irr [] = (c,irr)"
| "factorize_rat_poly_main c irr (p # ps) = (if degree p = 0 
    then factorize_rat_poly_main (c * coeff p 0) irr ps 
    else (case rational_proper_factor p of 
      None \<Rightarrow> factorize_rat_poly_main c (p # irr) ps
    | Some q \<Rightarrow> factorize_rat_poly_main c irr (q # p div q # ps)))"
  by pat_completeness auto

definition "factorize_rat_poly_main_wf_rel = inv_image (mult1 {(x, y). x < y}) (\<lambda>(c, irr, ps). mset (map degree ps))"

lemma wf_factorize_rat_poly_main_wf_rel: "wf factorize_rat_poly_main_wf_rel"
  unfolding factorize_rat_poly_main_wf_rel_def using wf_mult1[OF wf_less] by auto

lemma factorize_rat_poly_main_wf_rel_sub:
  "((a, b, ps), (c, d, p # ps)) \<in> factorize_rat_poly_main_wf_rel"
  unfolding factorize_rat_poly_main_wf_rel_def
  by (auto intro: mult1I [of _ _ _ _ "{#}"])

lemma factorize_rat_poly_main_wf_rel_two: assumes "degree q < degree p" "degree r < degree p"
  shows "((a,b,q # r # ps), (c,d,p # ps)) \<in> factorize_rat_poly_main_wf_rel"
  unfolding factorize_rat_poly_main_wf_rel_def mult1_def
  using add_eq_conv_ex assms ab_semigroup_add_class.add_ac
    by fastforce

termination 
proof (relation factorize_rat_poly_main_wf_rel,
  rule wf_factorize_rat_poly_main_wf_rel, rule factorize_rat_poly_main_wf_rel_sub, 
  rule factorize_rat_poly_main_wf_rel_sub, rule factorize_rat_poly_main_wf_rel_two)
  fix p q
  assume rf: "rational_proper_factor p = Some q" and dp: "degree p \<noteq> 0"
  from rational_proper_factor(2)[OF rf] 
  have dvd: "q dvd p" and deg: "1 \<le> degree q" "degree q < degree p" by auto
  show "degree q < degree p" by fact
  from dvd have "p = q * (p div q)" by auto
  from arg_cong[OF this, of degree]
  have "degree p = degree q + degree (p div q)"
    by (subst degree_mult_eq[symmetric], insert dp, auto)
  with deg
  show "degree (p div q) < degree p" by simp
qed  

declare factorize_rat_poly_main.simps[simp del]

lemma factorize_rat_poly_main:
  assumes "factorize_rat_poly_main c irr ps = (d,qs)"
    and "Ball (set irr) irreducible\<^sub>d"
  shows "Ball (set qs) irreducible\<^sub>d" (is ?g1)
    and "smult c (prod_list (irr @ ps)) = smult d (prod_list qs)" (is ?g2)
proof (atomize(full), insert assms, induct c irr ps rule: factorize_rat_poly_main.induct)
  case (1 c irr)
  thus ?case by (auto simp: factorize_rat_poly_main.simps)
next
  case (2 c irr p ps)
  note IH = 2(1-3)
  note res = 2(4)[unfolded factorize_rat_poly_main.simps(2)[of c irr p ps]]
  note irr = 2(5)
  let ?f = factorize_rat_poly_main
  show ?case
  proof (cases "degree p = 0")
    case True
    with res have res: "?f (c * coeff p 0) irr ps = (d,qs)" by simp
    from degree0_coeffs[OF True] obtain a where p: "p = [: a :]" by auto
    from IH(1)[OF True res irr]
    show ?thesis using p by simp
  next
    case False
    note IH = IH(2-)[OF False]
    from False have "(degree p = 0) = False" by auto
    note res = res[unfolded this if_False]
    let ?rf = "rational_proper_factor p"
    show ?thesis
    proof (cases ?rf)
      case None
      with res have res: "?f c (p # irr) ps = (d,qs)" by auto
      from rational_proper_factor(1)[OF _ None] False
      have irp: "irreducible\<^sub>d p" by auto
      note IH(1)[OF None res, unfolded atomize_imp imp_conjR, simplified]
      note 1 = conjunct1[OF this, rule_format] conjunct2[OF this, rule_format]
      from irr irp show ?thesis by (auto intro:1 simp: ac_simps)
    next
      case (Some q)
      define pq where "pq = p div q" 
      from Some res have res: "?f c irr (q # pq # ps) = (d,qs)" unfolding pq_def by auto
      from rational_proper_factor(2)[OF Some] have "q dvd p" by auto
      hence p: "p = q * pq" unfolding pq_def by auto
      from IH(2)[OF Some, folded pq_def, OF res irr] show ?thesis unfolding p 
        by (auto simp: ac_simps)
    qed
  qed
qed

definition "factorize_rat_poly_basic p = factorize_rat_poly_main 1 [] [p]" 

lemma factorize_rat_poly_basic: assumes res: "factorize_rat_poly_basic p = (c,qs)" 
  shows "p = smult c (prod_list qs)" 
  "\<And> q. q \<in> set qs \<Longrightarrow> irreducible\<^sub>d q"
  using factorize_rat_poly_main[OF res[unfolded factorize_rat_poly_basic_def]] by auto

text \<open>We removed the factorize-rat-poly function from this theory, since the one in 
  Berlekamp-Zassenhaus is easier to use and implements a more efficient algorithm.\<close>

end
