(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Real Roots\<close>

text \<open>This theory contains an algorithm to determine the set of real roots of a 
  rational polynomial. It further contains an algorithm which tries to determine the
  real roots of real-valued polynomial, which incorporates Yun-factorization and 
  closed formulas for polynomials of degree 2.\<close>

theory Real_Roots
imports 
  Real_Algebraic_Numbers
begin

text \<open>Division of integers, rounding to the upper value.\<close>
definition div_ceiling :: "int \<Rightarrow> int \<Rightarrow> int" where
  "div_ceiling x y = (let q = x div y in if q * y = x then q else q + 1)" 

definition root_bound :: "int poly \<Rightarrow> rat" where 
  "root_bound p \<equiv> let 
     n = degree p;
     m = 1 + div_ceiling (max_list_non_empty (map (\<lambda>i. abs (coeff p i)) [0..<n])) 
          (abs (lead_coeff p))
     \<comment> \<open>round to the next higher number \<open>2^n\<close>, so that bisection will\<close>
     \<comment> \<open>stay on integers for as long as possible\<close>
   in of_int (2 ^ (log_ceiling 2 m))"
  
partial_function (tailrec) roots_of_2_main :: 
  "int poly \<Rightarrow> root_info \<Rightarrow> (rat \<Rightarrow> rat \<Rightarrow> nat) \<Rightarrow> (rat \<times> rat)list \<Rightarrow> real_alg_2 list \<Rightarrow> real_alg_2 list" where
  [code]: "roots_of_2_main p ri cr lrs rais = (case lrs of Nil \<Rightarrow> rais
  | (l,r) # lrs \<Rightarrow> let c = cr l r in 
    if c = 0 then roots_of_2_main p ri cr lrs rais
    else if c = 1 then roots_of_2_main p ri cr lrs (real_alg_2'' ri p l r # rais)
    else let m = (l + r) / 2 in roots_of_2_main p ri cr ((m,r) # (l,m) # lrs) rais)"
  
definition roots_of_2_irr :: "int poly \<Rightarrow> real_alg_2 list" where
  "roots_of_2_irr p = (if degree p = 1
    then [Rational (Rat.Fract (- coeff p 0) (coeff p 1)) ] else 
    let ri = root_info p;
        cr = root_info.l_r ri;
        B = root_bound p
      in (roots_of_2_main p ri cr [(-B,B)] []))"
  
lemma root_imp_deg_nonzero: assumes "p \<noteq> 0" "poly p x = 0"
  shows "degree p \<noteq> 0" 
proof
  assume "degree p = 0" 
  from degree0_coeffs[OF this] assms show False by auto
qed
  
lemma cauchy_root_bound: fixes x :: "'a :: real_normed_field"
  assumes x: "poly p x = 0" and p: "p \<noteq> 0" 
  shows "norm x \<le> 1 + max_list_non_empty (map (\<lambda> i. norm (coeff p i)) [0 ..< degree p]) 
    / norm (lead_coeff p)" (is "_ \<le> _ + ?max / ?nlc")
proof -
  let ?n = "degree p" 
  let ?p = "coeff p" 
  let ?lc = "lead_coeff p" 
  define ml where "ml = ?max / ?nlc" 
  from p have lc: "?lc \<noteq> 0" by auto
  hence nlc: "norm ?lc > 0" by auto
  from root_imp_deg_nonzero[OF p x] have *: "0 \<in> set [0 ..< degree p]" by auto
  have "0 \<le> norm (?p 0)" by simp
  also have "\<dots> \<le> ?max" 
    by (rule max_list_non_empty, insert *, auto)
  finally have max0: "?max \<ge> 0" .
  with nlc have ml0: "ml \<ge> 0" unfolding ml_def by auto
  hence easy: "norm x \<le> 1 \<Longrightarrow> ?thesis" unfolding ml_def[symmetric] by auto
  show ?thesis
  proof (cases "norm x \<le> 1")
    case True
    thus ?thesis using easy by auto
  next
    case False
    hence nx: "norm x > 1" by simp 
    hence x0: "x \<noteq> 0" by auto
    hence xn0: "0 < norm x ^ ?n" by auto
    from x[unfolded poly_altdef] have "x ^ ?n * ?lc = x ^ ?n * ?lc - (\<Sum>i\<le>?n. x ^ i * ?p i)" 
      unfolding poly_altdef by (simp add: ac_simps)    
    also have "(\<Sum>i\<le>?n. x ^ i * ?p i) = x ^ ?n * ?lc + (\<Sum>i < ?n. x ^ i * ?p i)" 
      by (subst sum.remove[of _ ?n], auto intro: sum.cong)
    finally have "x ^ ?n * ?lc = - (\<Sum>i < ?n. x ^ i * ?p i)" by simp
    with lc have "x ^ ?n = - (\<Sum>i < ?n. x ^ i * ?p i) / ?lc" by (simp add: field_simps)
    from arg_cong[OF this, of norm]
    have "norm x ^ ?n = norm ((\<Sum>i < ?n. x ^ i * ?p i) / ?lc)" unfolding norm_power by simp
    also have "(\<Sum>i < ?n. x ^ i * ?p i) / ?lc = (\<Sum>i < ?n. x ^ i * ?p i / ?lc)" 
      by (rule sum_divide_distrib)
    also have "norm \<dots> \<le> (\<Sum>i < ?n. norm (x ^ i * (?p i / ?lc)))" 
      by (simp add: field_simps, rule norm_sum)
    also have "\<dots> = (\<Sum>i < ?n. norm x ^ i * norm (?p i / ?lc))" 
      unfolding norm_mult norm_power ..
    also have "\<dots> \<le> (\<Sum>i < ?n. norm x ^ i * ml)" 
    proof (rule sum_mono)
      fix i
      assume "i \<in> {..<?n}" 
      hence i: "i < ?n" by simp
      show "norm x ^ i * norm (?p i / ?lc) \<le> norm x ^ i * ml" 
      proof (rule mult_left_mono)
        show "0 \<le> norm x ^ i" using nx by auto
        show "norm (?p i / ?lc) \<le> ml" unfolding norm_divide ml_def
          by (rule divide_right_mono[OF max_list_non_empty], insert nlc i, auto)
      qed
    qed
    also have "\<dots> = ml * (\<Sum>i < ?n. norm x ^ i)" 
      unfolding sum_distrib_right[symmetric] by simp
    also have "(\<Sum>i < ?n. norm x ^ i) = (norm x ^ ?n - 1) / (norm x - 1)" 
      by (rule geometric_sum, insert nx, auto)
    finally have "norm x ^ ?n \<le> ml * (norm x ^ ?n - 1) / (norm x - 1)" by simp        
    from mult_left_mono[OF this, of "norm x - 1"]
    have "(norm x - 1) * (norm x ^ ?n) \<le> ml * (norm x ^ ?n - 1)" using nx by auto
    also have "\<dots> = (ml * (1 - 1 / (norm x ^ ?n))) * norm x ^ ?n" 
      using nx False x0 by (simp add: field_simps)
    finally have "(norm x - 1) * (norm x ^ ?n) \<le> (ml * (1 - 1 / (norm x ^ ?n))) * norm x ^ ?n" .
    from mult_right_le_imp_le[OF this xn0]
    have "norm x - 1 \<le> ml * (1 - 1 / (norm x ^ ?n))" by simp
    hence "norm x \<le> 1 + ml - ml / (norm x ^ ?n)" by (simp add: field_simps)
    also have "\<dots> \<le> 1 + ml" using ml0 xn0 by auto
    finally show ?thesis unfolding ml_def .
  qed
qed
      
lemma div_le_div_ceiling: "x div y \<le> div_ceiling x y" 
  unfolding div_ceiling_def Let_def by auto
    
lemma div_ceiling: assumes q: "q \<noteq> 0"  
  shows "(of_int x :: 'a :: floor_ceiling) / of_int q \<le> of_int (div_ceiling x q)" 
proof (cases "q dvd x")
  case True
  then obtain k where xqk: "x = q * k" unfolding dvd_def by auto
  hence id: "div_ceiling x q = k" unfolding div_ceiling_def Let_def using q by auto
  show ?thesis unfolding id unfolding xqk using q by simp
next
  case False
  {
    assume "x div q * q = x" 
    hence "x = q * (x div q)" by (simp add: ac_simps)
    hence "q dvd x" unfolding dvd_def by auto
    with False have False by simp
  }
  hence id: "div_ceiling x q = x div q + 1" 
    unfolding div_ceiling_def Let_def using q by auto
  show ?thesis unfolding id
    by (metis floor_divide_of_int_eq le_less add1_zle_eq floor_less_iff)
qed
  
lemma max_list_non_empty_map: assumes hom: "\<And> x y. max (f x) (f y) = f (max x y)"  
  shows "xs \<noteq> [] \<Longrightarrow> max_list_non_empty (map f xs) = f (max_list_non_empty xs)" 
  by (induct xs rule: max_list_non_empty.induct, auto simp: hom)

lemma root_bound: assumes "root_bound p = B" and deg: "degree p > 0"
  shows "ipoly p (x :: real) = 0 \<Longrightarrow> norm x \<le> of_rat B" "B \<ge> 0" 
proof -
  let ?r = real_of_rat
  let ?i = real_of_int
  let ?p = "real_of_int_poly p"
  define n where "n = degree p"
  let ?lc = "coeff p n" 
  let ?list = "map (\<lambda>i. abs (coeff p i)) [0..<n]" 
  let ?list' = "(map (\<lambda>i. ?i (abs ((coeff p i)))) [0..<n])" 
  define m where "m = max_list_non_empty ?list"
  define m_up where "m_up = 1 + div_ceiling m (abs ?lc)"
  define C where "C = rat_of_int (2^(log_ceiling 2 m_up))"
  from deg have p0: "p \<noteq> 0" by auto
  from p0 have alc0: "abs ?lc \<noteq> 0" unfolding n_def by auto
  from deg have mem: "abs (coeff p 0) \<in> set ?list" unfolding n_def by auto
  from max_list_non_empty[OF this, folded m_def]    
  have m0: "m \<ge> 0" by auto
  have "div_ceiling m (abs ?lc) \<ge> 0" 
    by (rule order_trans[OF _ div_le_div_ceiling[of m "abs ?lc"]], subst
    pos_imp_zdiv_nonneg_iff, insert p0 m0, auto simp: n_def)
  hence mup: "m_up \<ge> 1" unfolding m_up_def by auto
  have "m_up \<le> 2 ^ (log_ceiling 2 m_up)" using  mup log_ceiling_sound(1) by auto
  hence Cmup: "C \<ge> of_int m_up" unfolding C_def by linarith
  with mup have C: "C \<ge> 1" by auto      
  from assms(1)[unfolded root_bound_def Let_def]
  have B: "C = of_rat B" unfolding C_def m_up_def n_def m_def by auto
  note dc = div_le_div_ceiling[of m "abs ?lc"] 
  with C show "B \<ge> 0" unfolding B by auto
  assume "ipoly p x = 0" 
  hence rt: "poly ?p x = 0" by simp
  from root_imp_deg_nonzero[OF _ this] p0 have n0: "n \<noteq> 0" unfolding n_def by auto
  from cauchy_root_bound[OF rt] p0
  have "norm x \<le> 1 + max_list_non_empty ?list' / ?i (abs ?lc)" 
    by (simp add: n_def)
  also have "?list' = map ?i ?list" by simp
  also have "max_list_non_empty \<dots> = ?i m" unfolding m_def
    by (rule max_list_non_empty_map, insert mem, auto)
  also have "1 + m / ?i (abs ?lc) \<le> ?i m_up" 
    unfolding m_up_def using div_ceiling[OF alc0, of m] by auto
  also have "\<dots> \<le> ?r C" using Cmup using of_rat_less_eq by force
  finally have "norm x \<le> ?r C" .
  thus "norm x \<le> ?r B" unfolding B by simp
qed
  
fun pairwise_disjoint :: "'a set list \<Rightarrow> bool" where
  "pairwise_disjoint [] = True" 
| "pairwise_disjoint (x # xs) = ((x \<inter> (\<Union> y \<in> set xs. y) = {}) \<and> pairwise_disjoint xs)" 

lemma roots_of_2_irr: assumes pc: "poly_cond p" and deg: "degree p > 0"
  shows "real_of_2 ` set (roots_of_2_irr p) = {x. ipoly p x = 0}" (is ?one)
    "Ball (set (roots_of_2_irr p)) invariant_2" (is ?two)
    "distinct (map real_of_2 (roots_of_2_irr p))" (is ?three)
proof -
  note d = roots_of_2_irr_def
  from poly_condD[OF pc] have mon: "lead_coeff p > 0" and irr: "irreducible p" by auto
  let ?norm = "real_alg_2'"
  have "?one \<and> ?two \<and> ?three"
  proof (cases "degree p = 1")
    case True
    define c where "c = coeff p 0"
    define d where "d = coeff p 1" 
    from True have rr: "roots_of_2_irr p = [Rational (Rat.Fract (- c) (d))]" unfolding d d_def c_def by auto
    from degree1_coeffs[OF True] have p: "p = [:c,d:]" and d: "d \<noteq> 0" unfolding c_def d_def by auto
    have *: "real_of_int c + x * real_of_int d = 0 \<Longrightarrow> x = - (real_of_int c / real_of_int d)" for x
      using d by (simp add: field_simps)
    show ?thesis unfolding rr using d * unfolding p using of_rat_1[of "Rat.Fract (- c) (d)"]
      by (auto simp: Fract_of_int_quotient hom_distribs)
  next
    case False
    let ?r = real_of_rat
    let ?rp = "map_poly ?r"
    let ?rr = "set (roots_of_2_irr p)"
    define ri where "ri = root_info p"
    define cr where "cr = root_info.l_r ri"
    define bnds where "bnds = [(-root_bound p, root_bound p)]"
    define empty where "empty = (Nil :: real_alg_2 list)"
    have empty: "Ball (set empty) invariant_2 \<and> distinct (map real_of_2 empty)" unfolding empty_def by auto
    from mon have p: "p \<noteq> 0" by auto
    from root_info[OF irr deg] have ri: "root_info_cond ri p" unfolding ri_def .    
    from False 
    have rr: "roots_of_2_irr p = roots_of_2_main p ri cr bnds empty"
      unfolding d ri_def cr_def Let_def bnds_def empty_def by auto
    note root_bound = root_bound[OF refl deg]
    from root_bound(2)
    have bnds: "\<And> l r. (l,r) \<in> set bnds \<Longrightarrow> l \<le> r" unfolding bnds_def by auto
    have "ipoly p x = 0 \<Longrightarrow> ?r (- root_bound p) \<le> x \<and> x \<le> ?r (root_bound p)" for x
      using root_bound(1)[of x] by (auto simp: hom_distribs)
    hence rts: "{x. ipoly p x = 0} 
      = real_of_2 ` set empty \<union> {x. \<exists> l r. root_cond (p,l,r) x \<and> (l,r) \<in> set bnds}" 
      unfolding empty_def bnds_def by (force simp: root_cond_def)
    define rts where "rts lr = Collect (root_cond (p,lr))" for lr 
    have disj: "pairwise_disjoint (real_of_2 ` set empty # map rts bnds)" 
      unfolding empty_def bnds_def by auto
    from deg False have deg1: "degree p > 1" by auto
    define delta where "delta = ipoly_root_delta p"
    note delta = ipoly_root_delta[OF p, folded delta_def]
    define rel' where "rel' = ({(x, y). 0 \<le> y \<and> delta_gt delta x y})^-1"
    define mm where "mm = (\<lambda>bnds. mset (map (\<lambda> (l,r). ?r r - ?r l) bnds))"
    define rel where "rel = inv_image (mult1 rel') mm"
    have wf: "wf rel" unfolding rel_def rel'_def
      by (rule wf_inv_image[OF wf_mult1[OF SN_imp_wf[OF delta_gt_SN[OF delta(1)]]]])
    let ?main = "roots_of_2_main p ri cr"    
    have "real_of_2 ` set (?main bnds empty) =
      real_of_2 ` set empty \<union>
      {x. \<exists>l r. root_cond (p, l, r) x \<and> (l, r) \<in> set bnds} \<and>
      Ball (set (?main bnds empty)) invariant_2 \<and> distinct (map real_of_2 (?main bnds empty))" (is "?one' \<and> ?two' \<and> ?three'")
      using empty bnds disj
    proof (induct bnds arbitrary: empty rule: wf_induct[OF wf])
      case (1 lrss rais)
      note rais = 1(2)[rule_format]
      note lrs = 1(3)
      note disj = 1(4)
      note IH = 1(1)[rule_format]
      note simp = roots_of_2_main.simps[of p ri cr lrss rais]
      show ?case
      proof (cases lrss)
        case Nil
        with rais show ?thesis unfolding simp by auto
      next
        case (Cons lr lrs)
        obtain l r where lr': "lr = (l,r)" by force
        {
          fix lr'
          assume lt: "\<And> l' r'. (l',r') \<in> set lr' \<Longrightarrow> 
            l' \<le> r' \<and> delta_gt delta (?r r - ?r l) (?r r' - ?r l')"
          have l: "mm (lr' @ lrs) = mm lrs + mm lr'" unfolding mm_def by (auto simp: ac_simps)
          have r: "mm lrss = mm lrs + {# ?r r - ?r l #}" unfolding Cons lr' rel_def mm_def
            by auto
          have "(mm (lr' @ lrs), mm lrss) \<in> mult1 rel'" unfolding l r mult1_def
          proof (rule, unfold split, intro exI conjI, unfold add_mset_add_single[symmetric], rule refl, rule refl, intro allI impI)
            fix d
            assume "d \<in># mm lr'"
            then obtain l' r' where d: "d = ?r r' - ?r l'" and lr': "(l',r') \<in> set lr'"
              unfolding mm_def in_multiset_in_set by auto
            from lt[OF lr']
            show "(d, ?r r - ?r l) \<in> rel'"  unfolding d rel'_def 
              by (auto simp: of_rat_less_eq)
          qed
          hence "(lr' @ lrs, lrss) \<in> rel" unfolding rel_def by auto
        } note rel = this
        from rel[of Nil] have easy_rel: "(lrs,lrss) \<in> rel" by auto
        define c where "c = cr l r"
        from simp Cons lr' have simp: "?main lrss rais = 
          (if c = 0 then ?main lrs rais else if c = 1 then 
             ?main lrs (real_alg_2' ri p l r # rais)
               else let m = (l + r) / 2 in ?main ((m, r) # (l, m) # lrs) rais)"
          unfolding c_def simp Cons lr' using real_alg_2''[OF False] by auto
        note lrs = lrs[unfolded Cons lr']        
        from lrs have lr: "l \<le> r" by auto
        from root_info_condD(1)[OF ri lr, folded cr_def] 
        have c: "c = card {x. root_cond (p,l,r) x}" unfolding c_def by auto
        let ?rt = "\<lambda> lrs. {x. \<exists>l r. root_cond (p, l, r) x \<and> (l, r) \<in> set lrs}"
        have rts: "?rt lrss = ?rt lrs \<union> {x. root_cond (p,l,r) x}" (is "?rt1 = ?rt2 \<union> ?rt3")
          unfolding Cons lr' by auto
        show ?thesis 
        proof (cases "c = 0")
          case True          
          with simp have simp: "?main lrss rais = ?main lrs rais" by simp
          from disj have disj: "pairwise_disjoint (real_of_2 ` set rais # map rts lrs)" 
            unfolding Cons by auto
          from finite_ipoly_roots[OF p] True[unfolded c] have empty: "?rt3 = {}"
            unfolding root_cond_def[abs_def] split by simp
          with rts have rts: "?rt1 = ?rt2" by auto
          show ?thesis unfolding simp rts 
            by (rule IH[OF easy_rel rais lrs disj], auto)
        next
          case False
          show ?thesis
          proof (cases "c = 1")
            case True
            let ?rai = "real_alg_2' ri p l r"
            from True simp have simp: "?main lrss rais = ?main lrs (?rai # rais)" by auto
            from card_1_Collect_ex1[OF c[symmetric, unfolded True]] 
            have ur: "unique_root (p,l,r)"  .            
            from real_alg_2'[OF ur pc ri]
            have rai: "invariant_2 ?rai" "real_of_2 ?rai = the_unique_root (p, l, r)" by auto
            with rais have rais: "\<And> x. x \<in> set (?rai # rais) \<Longrightarrow> invariant_2 x" 
              and dist: "distinct (map real_of_2 rais)" by auto
            have rt3: "?rt3 = {real_of_2 ?rai}" 
              using rc1 ur rai by (auto intro: the_unique_root_eqI theI')            
            have "real_of_2 ` set (roots_of_2_main p ri cr lrs (?rai # rais)) =
              real_of_2 ` set (?rai # rais) \<union> ?rt2 \<and>
              Ball (set (roots_of_2_main p ri cr lrs (?rai # rais))) invariant_2 \<and>
              distinct (map real_of_2 (roots_of_2_main p ri cr lrs (?rai # rais)))"
              (is "?one \<and> ?two \<and> ?three")
            proof (rule IH[OF easy_rel, of "?rai # rais", OF conjI lrs])
              show "Ball (set (real_alg_2' ri p l r # rais)) invariant_2" using rais by auto
              have "real_of_2 (real_alg_2' ri p l r) \<notin> set (map real_of_2 rais)"
                using disj rt3 unfolding Cons lr' rts_def by auto
              thus "distinct (map real_of_2 (real_alg_2' ri p l r # rais))" using dist by auto
              show "pairwise_disjoint (real_of_2 ` set (real_alg_2' ri p l r # rais) # map rts lrs)"
                using disj rt3 unfolding Cons lr' rts_def by auto
            qed auto
            hence ?one ?two ?three by blast+
            show ?thesis unfolding simp rts rt3 
              by (rule conjI[OF _ conjI[OF \<open>?two\<close> \<open>?three\<close>]], unfold \<open>?one\<close>, auto)
          next
            case False
            let ?m = "(l+r)/2"
            let ?lrs = "[(?m,r),(l,?m)] @ lrs"
            from False \<open>c \<noteq> 0\<close> have simp: "?main lrss rais = ?main ?lrs rais"
              unfolding simp by (auto simp: Let_def)
            from False \<open>c \<noteq> 0\<close> have "c \<ge> 2" by auto
            from delta(2)[OF this[unfolded c]] have delta: "delta \<le> ?r (r - l) / 4" by auto
            have lrs: "\<And> l r. (l,r) \<in> set ?lrs \<Longrightarrow> l \<le> r"
              using lr lrs by (fastforce simp: field_simps)
            have "?r ?m \<in> \<rat>" unfolding Rats_def by blast
            with poly_cond_degree_gt_1[OF pc deg1, of "?r ?m"]
            have disj1: "?r ?m \<notin> rts lr" for lr unfolding rts_def root_cond_def by auto
            have disj2: "rts (?m, r) \<inter> rts (l, ?m) = {}" using disj1[of "(l,?m)"] disj1[of "(?m,r)"] 
              unfolding rts_def root_cond_def by auto
            have disj3: "(rts (l,?m) \<union> rts (?m,r)) = rts (l,r)"
              unfolding rts_def root_cond_def by (auto simp: hom_distribs)
            have disj4: "real_of_2 ` set rais \<inter> rts (l,r) = {}" using disj unfolding Cons lr' by auto
            have disj: "pairwise_disjoint (real_of_2 ` set rais # map rts ([(?m, r), (l, ?m)] @ lrs))" 
              using disj disj2 disj3 disj4 by (auto simp: Cons lr')
            have "(?lrs,lrss) \<in> rel"
            proof (rule rel, intro conjI)
              fix l' r'
              assume mem: "(l', r') \<in> set [(?m,r),(l,?m)]"
              from mem lr show "l' \<le> r'" by auto
              from mem have diff: "?r r' - ?r l' = (?r r - ?r l) / 2" by auto 
               (metis eq_diff_eq minus_diff_eq mult_2_right of_rat_add of_rat_diff,
                metis of_rat_add of_rat_mult of_rat_numeral_eq)
              show "delta_gt delta (?r r - ?r l) (?r r' - ?r l')" unfolding diff
                delta_gt_def by (rule order.trans[OF delta], insert lr, 
                auto simp: field_simps of_rat_diff of_rat_less_eq)
            qed
            note IH = IH[OF this, of rais, OF rais lrs disj]
            have "real_of_2 ` set (?main ?lrs rais) =
              real_of_2 ` set rais \<union> ?rt ?lrs \<and>
              Ball (set (?main ?lrs rais)) invariant_2 \<and> distinct (map real_of_2 (?main ?lrs rais))"
              (is "?one \<and> ?two")
              by (rule IH)
            hence ?one ?two by blast+
            have cong: "\<And> a b c. b = c \<Longrightarrow> a \<union> b = a \<union> c" by auto
            have id: "?rt ?lrs = ?rt lrs \<union> ?rt [(?m,r),(l,?m)]" by auto
            show ?thesis unfolding rts simp \<open>?one\<close> id
            proof (rule conjI[OF cong[OF cong] conjI])
              have "\<And> x. root_cond (p,l,r) x = (root_cond (p,l,?m) x \<or> root_cond (p,?m,r) x)"
                unfolding root_cond_def by (auto simp:hom_distribs)
              hence id: "Collect (root_cond (p,l,r)) = {x. (root_cond (p,l,?m) x \<or> root_cond (p,?m,r) x)}" 
                by auto
              show "?rt [(?m,r),(l,?m)] = Collect (root_cond (p,l,r))" unfolding id list.simps by blast
              show "\<forall> a \<in> set (?main ?lrs rais). invariant_2 a" using \<open>?two\<close> by auto
              show "distinct (map real_of_2 (?main ?lrs rais))" using \<open>?two\<close> by auto
            qed
          qed
        qed
      qed
    qed
    hence idd: "?one'" and cond: ?two' ?three' by blast+
    define res where "res = roots_of_2_main p ri cr bnds empty"
    have e: "set empty = {}" unfolding empty_def by auto
    from idd[folded res_def] e have idd: "real_of_2 ` set res = {} \<union> {x. \<exists>l r. root_cond (p, l, r) x \<and> (l, r) \<in> set bnds}"
      by auto
    show ?thesis
      unfolding rr unfolding rts id e norm_def using cond 
      unfolding res_def[symmetric] image_empty e idd[symmetric] by auto
  qed
  thus ?one ?two ?three by blast+
qed
 
definition roots_of_2 :: "int poly \<Rightarrow> real_alg_2 list" where
  "roots_of_2 p = concat (map roots_of_2_irr 
     (factors_of_int_poly p))"
    
lemma roots_of_2:
  shows "p \<noteq> 0 \<Longrightarrow> real_of_2 ` set (roots_of_2 p) = {x. ipoly p x = 0}"
    "Ball (set (roots_of_2 p)) invariant_2"
    "distinct (map real_of_2 (roots_of_2 p))" 
proof -
  let ?rr = "roots_of_2 p"
  note d = roots_of_2_def
  note frp1 = factors_of_int_poly
  {
    fix q r
    assume "q \<in> set ?rr"
    then obtain s where 
      s: "s \<in> set (factors_of_int_poly p)" and
      q: "q \<in> set (roots_of_2_irr s)"
      unfolding d by auto
    from frp1(1)[OF refl s] have "poly_cond s" "degree s > 0" by (auto simp: poly_cond_def)
    from roots_of_2_irr[OF this] q
    have "invariant_2 q" by auto
  }
  thus "Ball (set ?rr) invariant_2" by auto
  {  
    assume p: "p \<noteq> 0" 
    have "real_of_2 ` set ?rr = (\<Union> ((\<lambda> p. real_of_2 ` set (roots_of_2_irr p)) ` 
      (set (factors_of_int_poly p))))"
      (is "_ = ?rrr")
      unfolding d set_concat set_map by auto
    also have "\<dots> = {x. ipoly p x = 0}"
    proof -
      {
        fix x
        assume "x \<in> ?rrr"
        then obtain q s where 
          s: "s \<in> set (factors_of_int_poly p)" and
          q: "q \<in> set (roots_of_2_irr s)" and
          x: "x = real_of_2 q" by auto
        from frp1(1)[OF refl s] have s0: "s \<noteq> 0" and pt: "poly_cond s" "degree s > 0"
          by (auto simp: poly_cond_def)
        from roots_of_2_irr[OF pt] q have rt: "ipoly s x = 0" unfolding x by auto
        from frp1(2)[OF refl p, of x] rt s have rt: "ipoly p x = 0" by auto
      }
      moreover
      {
        fix x :: real
        assume rt: "ipoly p x = 0"
        from rt frp1(2)[OF refl p, of x] obtain s where s: "s \<in> set (factors_of_int_poly p)" 
          and rt: "ipoly s x = 0" by auto
        from frp1(1)[OF refl s] have s0: "s \<noteq> 0" and ty: "poly_cond s" "degree s > 0"
          by (auto simp: poly_cond_def)
        from roots_of_2_irr(1)[OF ty] rt obtain q where 
          q: "q \<in> set (roots_of_2_irr s)" and
          x: "x = real_of_2 q" by blast
        have "x \<in> ?rrr" unfolding x using q s by auto
      }
      ultimately show ?thesis by auto
    qed
    finally show "real_of_2 ` set ?rr = {x. ipoly p x = 0}" by auto
  }
  show "distinct (map real_of_2 (roots_of_2 p))"
  proof (cases "p = 0")
    case True
    from factors_of_int_poly_const[of 0] True show ?thesis unfolding roots_of_2_def by auto
  next
    case p: False
    note frp1 = frp1[OF refl]
    let ?fp = "factors_of_int_poly p" 
    let ?cc = "concat (map roots_of_2_irr ?fp)" 
    show ?thesis unfolding roots_of_2_def distinct_conv_nth length_map
    proof (intro allI impI notI)
      fix i j
      assume ij: "i < length ?cc" "j < length ?cc" "i \<noteq> j" and id: "map real_of_2 ?cc ! i = map real_of_2 ?cc ! j"       
      from ij id have id: "real_of_2 (?cc ! i) = real_of_2 (?cc ! j)" by auto
      from nth_concat_diff[OF ij, unfolded length_map] obtain j1 k1 j2 k2 where 
        *: "(j1,k1) \<noteq> (j2,k2)"
        "j1 < length ?fp" "j2 < length ?fp" and
        "k1 < length (map roots_of_2_irr ?fp ! j1)"
        "k2 < length (map roots_of_2_irr ?fp ! j2)"
        "?cc ! i = map roots_of_2_irr ?fp ! j1 ! k1" 
        "?cc ! j = map roots_of_2_irr ?fp ! j2 ! k2" by blast
      hence **: "k1 < length (roots_of_2_irr (?fp ! j1))" 
        "k2 < length (roots_of_2_irr (?fp ! j2))" 
        "?cc ! i = roots_of_2_irr (?fp ! j1) ! k1"
        "?cc ! j = roots_of_2_irr (?fp ! j2) ! k2"
        by auto
      from * have mem: "?fp ! j1 \<in> set ?fp" "?fp ! j2 \<in> set ?fp" by auto
      from frp1(1)[OF mem(1)] frp1(1)[OF mem(2)]
      have pc1: "poly_cond (?fp ! j1)" "degree (?fp ! j1) > 0" and pc10: "?fp ! j1 \<noteq> 0" 
        and pc2: "poly_cond (?fp ! j2)" "degree (?fp ! j2) > 0" 
        by (auto simp: poly_cond_def)
      show False
      proof (cases "j1 = j2")
        case True
        with * have neq: "k1 \<noteq> k2" by auto
        from **[unfolded True] id *
        have "map real_of_2 (roots_of_2_irr (?fp ! j2)) ! k1 = real_of_2 (?cc ! j)" 
          "map real_of_2 (roots_of_2_irr (?fp ! j2)) ! k1 = real_of_2 (?cc ! j)"
          by auto
        hence "\<not> distinct (map real_of_2 (roots_of_2_irr (?fp ! j2)))" 
          unfolding distinct_conv_nth using * ** True by auto
        with roots_of_2_irr(3)[OF pc2] show False by auto
      next
        case neq: False
        with frp1(4)[of p] * have neq: "?fp ! j1 \<noteq> ?fp ! j2" unfolding distinct_conv_nth by auto
        let ?x = "real_of_2 (?cc ! i)" 
        define x where "x = ?x" 
        from ** have "x \<in> real_of_2 ` set (roots_of_2_irr (?fp ! j1))" unfolding x_def by auto
        with roots_of_2_irr(1)[OF pc1] have x1: "ipoly (?fp ! j1) x = 0" by auto
        from ** id have "x \<in> real_of_2 ` set (roots_of_2_irr (?fp ! j2))" unfolding x_def
          by (metis image_eqI nth_mem)
        with roots_of_2_irr(1)[OF pc2] have x2: "ipoly (?fp ! j2) x = 0" by auto
        have "ipoly p x = 0" using x1 mem unfolding roots_of_2_def by (metis frp1(2) p)
        from frp1(3)[OF p this] x1 x2 neq mem show False by blast
      qed
    qed
  qed
qed      

lift_definition roots_of_3 :: "int poly \<Rightarrow> real_alg_3 list" is roots_of_2
  by (insert roots_of_2, auto simp: list_all_iff)

lemma roots_of_3: 
  shows "p \<noteq> 0 \<Longrightarrow> real_of_3 ` set (roots_of_3 p) = {x. ipoly p x = 0}"
    "distinct (map real_of_3 (roots_of_3 p))" 
proof -
  show "p \<noteq> 0 \<Longrightarrow> real_of_3 ` set (roots_of_3 p) = {x. ipoly p x = 0}"
    by (transfer; intro roots_of_2, auto)
  show "distinct (map real_of_3 (roots_of_3 p))" 
    by (transfer; insert roots_of_2, auto)
qed

lift_definition roots_of_real_alg :: "int poly \<Rightarrow> real_alg list" is roots_of_3 . 

lemma roots_of_real_alg: 
  "p \<noteq> 0 \<Longrightarrow> real_of ` set (roots_of_real_alg p) = {x. ipoly p x = 0}" 
  "distinct (map real_of (roots_of_real_alg p))"
proof -
  show "p \<noteq> 0 \<Longrightarrow> real_of ` set (roots_of_real_alg p) = {x. ipoly p x = 0}"
    by (transfer', insert roots_of_3, auto)
  show "distinct (map real_of (roots_of_real_alg p))"      
    by (transfer, insert roots_of_3(2), auto)
qed

text \<open>It follows an implementation for @{const roots_of_3}, 
  since the current definition does not provide a code equation.\<close>
context
begin
private typedef real_alg_2_list = "{xs. Ball (set xs) invariant_2}" by (intro exI[of _ Nil], auto)

setup_lifting type_definition_real_alg_2_list

private lift_definition roots_of_2_list :: "int poly \<Rightarrow> real_alg_2_list" is roots_of_2
  by (insert roots_of_2, auto)
private lift_definition real_alg_2_list_nil :: "real_alg_2_list \<Rightarrow> bool" is "\<lambda> xs. case xs of Nil \<Rightarrow> True | _ \<Rightarrow> False" .

private fun real_alg_2_list_hd_intern :: "real_alg_2 list \<Rightarrow> real_alg_2" where
  "real_alg_2_list_hd_intern (Cons x xs) = x"
| "real_alg_2_list_hd_intern Nil = of_rat_2 0"

private lift_definition real_alg_2_list_hd :: "real_alg_2_list \<Rightarrow> real_alg_3" is real_alg_2_list_hd_intern
proof (goal_cases)
  case (1 xs)
  thus ?case using of_rat_2[of 0] by (cases xs, auto)
qed

private lift_definition real_alg_2_list_tl :: "real_alg_2_list \<Rightarrow> real_alg_2_list" is tl 
proof (goal_cases)
  case (1 xs)
  thus ?case by (cases xs, auto)
qed

private lift_definition real_alg_2_list_length :: "real_alg_2_list \<Rightarrow> nat" is length .

private lemma real_alg_2_list_length[simp]: "\<not> real_alg_2_list_nil xs \<Longrightarrow> real_alg_2_list_length (real_alg_2_list_tl xs) < real_alg_2_list_length xs"
  by (transfer, auto split: list.splits)

private function real_alg_2_list_convert :: "real_alg_2_list \<Rightarrow> real_alg_3 list" where
  "real_alg_2_list_convert xs = (if real_alg_2_list_nil xs then [] else real_alg_2_list_hd xs 
    # real_alg_2_list_convert (real_alg_2_list_tl xs))" by pat_completeness auto

termination by (relation "measure real_alg_2_list_length", auto)

private definition roots_of_3_impl :: "int poly \<Rightarrow> real_alg_3 list" where
  "roots_of_3_impl p = real_alg_2_list_convert (roots_of_2_list p)"

private lift_definition real_alg_2_list_convert_id :: "real_alg_2_list \<Rightarrow> real_alg_3 list" is id
  by (auto simp: list_all_iff)

lemma real_alg_2_list_convert: "real_alg_2_list_convert xs = real_alg_2_list_convert_id xs"
proof (induct xs rule: wf_induct[OF wf_measure[of real_alg_2_list_length], rule_format])
  case (1 xs)
  show ?case
  proof (cases "real_alg_2_list_nil xs")
    case True
    hence "real_alg_2_list_convert xs = []" by auto
    also have "[] = real_alg_2_list_convert_id xs" using True
      by (transfer', auto split: list.splits)
    finally show ?thesis .
  next
    case False
    hence "real_alg_2_list_convert xs = real_alg_2_list_hd xs # real_alg_2_list_convert (real_alg_2_list_tl xs)" by simp
    also have "real_alg_2_list_convert (real_alg_2_list_tl xs) = real_alg_2_list_convert_id (real_alg_2_list_tl xs)"
      by (rule 1, insert False, simp)
    also have "real_alg_2_list_hd xs # \<dots> = real_alg_2_list_convert_id xs" using False
      by (transfer', auto split: list.splits)
    finally show ?thesis .
  qed
qed

lemma roots_of_3_code[code]: "roots_of_3 p = roots_of_3_impl p" 
  unfolding roots_of_3_impl_def real_alg_2_list_convert
  by (transfer, simp)
end

definition real_roots_of_int_poly :: "int poly \<Rightarrow> real list" where
  "real_roots_of_int_poly p = map real_of (roots_of_real_alg p)"

definition real_roots_of_rat_poly :: "rat poly \<Rightarrow> real list" where
  "real_roots_of_rat_poly p = map real_of (roots_of_real_alg (snd (rat_to_int_poly p)))"

abbreviation rpoly :: "rat poly \<Rightarrow> 'a :: field_char_0 \<Rightarrow> 'a"
where "rpoly f \<equiv> poly (map_poly of_rat f)"

lemma real_roots_of_int_poly: "p \<noteq> 0 \<Longrightarrow> set (real_roots_of_int_poly p) = {x. ipoly p x = 0}" 
  "distinct (real_roots_of_int_poly p)" 
  unfolding real_roots_of_int_poly_def using roots_of_real_alg[of p] by auto

lemma real_roots_of_rat_poly: "p \<noteq> 0 \<Longrightarrow> set (real_roots_of_rat_poly p) = {x. rpoly p x = 0}" 
  "distinct (real_roots_of_rat_poly p)"
proof -
  obtain c q where cq: "rat_to_int_poly p = (c,q)" by force
  from rat_to_int_poly[OF this]
  have pq: "p = smult (inverse (of_int c)) (of_int_poly q)" 
    and c: "c \<noteq> 0" by auto
  have id: "{x. rpoly p x = (0 :: real)} = {x. ipoly q x = 0}" 
    unfolding pq by (simp add: c of_rat_of_int_poly hom_distribs)
  show "distinct (real_roots_of_rat_poly p)" unfolding real_roots_of_rat_poly_def cq snd_conv 
    using roots_of_real_alg(2)[of q] .
  assume "p \<noteq> 0" 
  with pq c have q: "q \<noteq> 0" by auto
  show "set (real_roots_of_rat_poly p) = {x. rpoly p x = 0}" unfolding id
    unfolding real_roots_of_rat_poly_def cq snd_conv using roots_of_real_alg(1)[OF q]
    by auto
qed

text \<open>The upcoming functions no longer demand an integer or rational polynomial as input.\<close>

definition roots_of_real_main :: "real poly \<Rightarrow> real list" where 
  "roots_of_real_main p \<equiv> let n = degree p in 
    if n = 0 then [] else if n = 1 then [roots1 p] else if n = 2 then rroots2 p
    else (real_roots_of_rat_poly (map_poly to_rat p))"
  
definition roots_of_real_poly :: "real poly \<Rightarrow> real list option" where
  "roots_of_real_poly p \<equiv> let (c,pis) = yun_factorization gcd p in
    if (c \<noteq> 0 \<and> (\<forall> (p,i) \<in> set pis. degree p \<le> 2 \<or> (\<forall> x \<in> set (coeffs p). x \<in> \<rat>))) then 
    Some (concat (map (roots_of_real_main o fst) pis)) else None"

lemma roots_of_real_main: assumes p: "p \<noteq> 0" and deg: "degree p \<le> 2 \<or> set (coeffs p) \<subseteq> \<rat>"
  shows "set (roots_of_real_main p) = {x. poly p x = 0}" (is "?l = ?r")
proof -
  note d = roots_of_real_main_def Let_def
  show ?thesis 
  proof (cases "degree p = 0")
    case True
    hence "?l = {}" unfolding d by auto
    with roots0[OF p True] show ?thesis by auto
  next
    case False note 0 = this
    show ?thesis
    proof (cases "degree p = 1")
      case True
      hence "?l = {roots1 p}" unfolding d by auto
      with roots1[OF True] show ?thesis by auto
    next
      case False note 1 = this
      show ?thesis
      proof (cases "degree p = 2")
        case True
        hence "?l = set (rroots2 p)" unfolding d by auto
        with rroots2[OF True] show ?thesis by auto
      next
        case False note 2 = this
        let ?q = "map_poly to_rat p"
        from 0 1 2 have l: "?l = set (real_roots_of_rat_poly ?q)" unfolding d by auto
        from deg 0 1 2 have rat: "set (coeffs p) \<subseteq> \<rat>" by auto
        have "p = map_poly (of_rat o to_rat) p"
          by (rule sym, rule map_poly_idI, insert rat, auto)
        also have "\<dots> = real_of_rat_poly ?q"
          by (subst map_poly_map_poly, auto simp: to_rat)
        finally have id: "{x. poly p x = 0} = {x. poly (real_of_rat_poly ?q) x = 0}" and q: "?q \<noteq> 0" 
          using p by auto
        from real_roots_of_rat_poly(1)[OF q, folded id l] show ?thesis by simp
      qed
    qed
  qed
qed
  
lemma roots_of_real_poly: assumes rt: "roots_of_real_poly p = Some xs"
  shows "set xs = {x. poly p x = 0}"
proof -
  obtain c pis where yun: "yun_factorization gcd p = (c,pis)" by force
  from rt[unfolded roots_of_real_poly_def yun split Let_def]
  have c: "c \<noteq> 0" and pis: "\<And> p i. (p, i)\<in>set pis \<Longrightarrow> degree p \<le> 2 \<or> (\<forall>x\<in>set (coeffs p). x \<in> \<rat>)"
    and xs: "xs = concat (map (roots_of_real_main \<circ> fst) pis)"
    by (auto split: if_splits)
  note yun = square_free_factorizationD(1,2,4)[OF yun_factorization(1)[OF yun]]
  from yun(1) have p: "p = smult c (\<Prod>(a, i)\<in>set pis. a ^ Suc i)" .
  have "{x. poly p x = 0} = {x. poly (\<Prod>(a, i)\<in>set pis. a ^ Suc i) x = 0}"
    unfolding p using c by auto
  also have "\<dots> = \<Union> ((\<lambda> p. {x. poly p x = 0}) ` fst ` set pis)" (is "_ = ?r")
    by (subst poly_prod_0, force+)
  finally have r: "{x. poly p x = 0} = ?r" .
  {
    fix p i
    assume p: "(p,i) \<in> set pis"
    have "set (roots_of_real_main p) = {x. poly p x = 0}"
      by (rule roots_of_real_main, insert yun(2)[OF p] pis[OF p], auto)
  } note main = this
  have "set xs = \<Union> ((\<lambda> (p, i). set (roots_of_real_main p)) ` set pis)" unfolding xs o_def
    by auto
  also have "\<dots> = ?r" using main by auto
  finally show ?thesis unfolding r by simp
qed

end
