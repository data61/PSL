(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Reconstruction of Integer Factorization\<close>

text \<open>We implemented Zassenhaus reconstruction-algorithm, i.e., given a factorization of $f$ mod $p^n$,
  the aim is to reconstruct a factorization of $f$ over the integers.\<close>

theory Reconstruction
imports 
  Berlekamp_Hensel
  Polynomial_Factorization.Gauss_Lemma
  Polynomial_Factorization.Dvd_Int_Poly
  Polynomial_Factorization.Gcd_Rat_Poly
  Degree_Bound
  Factor_Bound
  Sublist_Iteration
  Poly_Mod
begin

hide_const coeff monom

paragraph \<open>Misc lemmas\<close>

lemma foldr_of_Cons[simp]: "foldr Cons xs ys = xs @ ys" by (induct xs, auto)

lemma foldr_map_prod[simp]:
  "foldr (\<lambda>x. map_prod (f x) (g x)) xs base = (foldr f xs (fst base), foldr g xs (snd base))"
  by (induct xs, auto)

paragraph \<open>The main part\<close>

context poly_mod
begin

definition inv_M :: "int \<Rightarrow> int" where
  "inv_M = (\<lambda> x. if x + x \<le> m then x else x - m)" 

definition inv_Mp :: "int poly \<Rightarrow> int poly" where
  "inv_Mp = map_poly inv_M"
  
definition mul_const :: "int poly \<Rightarrow> int \<Rightarrow> int" where
  "mul_const p c = (coeff p 0 * c) mod m"

fun prod_list_m :: "int poly list \<Rightarrow> int poly" where
  "prod_list_m (f # fs) = Mp (f * prod_list_m fs)" 
| "prod_list_m [] = 1" 

context
  fixes sl_impl :: "(int poly, int \<times> int poly list, 'state)subseqs_foldr_impl" 
  and m2 :: "int" 
begin
definition inv_M2 :: "int \<Rightarrow> int" where
  "inv_M2 = (\<lambda> x. if x \<le> m2 then x else x - m)"

definition inv_Mp2 :: "int poly \<Rightarrow> int poly" where
  "inv_Mp2 = map_poly inv_M2"
  
partial_function (tailrec) reconstruction :: "'state \<Rightarrow> int poly \<Rightarrow> int poly 
  \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int poly list \<Rightarrow> int poly list 
  \<Rightarrow> (int \<times> (int poly list)) list \<Rightarrow> int poly list" where
  "reconstruction state u luu lu d r vs res cands = (case cands of Nil
    \<Rightarrow> let d' = Suc d
      in if d' + d' > r then (u # res) else 
      (case next_subseqs_foldr sl_impl state of (cands,state') \<Rightarrow>
        reconstruction state' u luu lu d' r vs res cands)
   | (lv',ws) # cands' \<Rightarrow> let
       lv = inv_M2 lv' \<comment> \<open>\<open>lv\<close> is last coefficient of \<open>vb\<close> below\<close>
     in if lv dvd coeff luu 0 then let
       vb = inv_Mp2 (Mp (smult lu (prod_list_m ws))) 
    in if vb dvd luu then 
      let pp_vb = primitive_part vb;
          u' = u div pp_vb;
          r' = r - length ws;
          res' = pp_vb # res
        in if d + d > r' 
          then u' # res'
          else let 
              lu' = lead_coeff u';
              vs' = fold remove1 ws vs;
              (cands'', state') = subseqs_foldr sl_impl (lu',[]) vs' d
            in reconstruction state' u' (smult lu' u') lu' d r' vs' res' cands''
     else reconstruction state u luu lu d r vs res cands'
     else reconstruction state u luu lu d r vs res cands')"
  end
end


declare poly_mod.reconstruction.simps[code]
declare poly_mod.prod_list_m.simps[code]
declare poly_mod.mul_const_def[code]
declare poly_mod.inv_M2_def[code]
declare poly_mod.inv_M_def[code]
declare poly_mod.inv_Mp2_def[code_unfold]
declare poly_mod.inv_Mp_def[code_unfold]

definition zassenhaus_reconstruction_generic :: 
  "(int poly, int \<times> int poly list, 'state) subseqs_foldr_impl
  \<Rightarrow> int poly list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> int poly list" where
  "zassenhaus_reconstruction_generic sl_impl vs p n f = (let
     lf = lead_coeff f;
     pn = p^n;
     (_, state) = subseqs_foldr sl_impl (lf,[]) vs 0
   in 
     poly_mod.reconstruction pn sl_impl (pn div 2) state f (smult lf f) lf 0 (length vs) vs [] [])"
  
lemma coeff_mult_0: "coeff (f * g) 0 = coeff f 0 * coeff g 0"
  by (metis poly_0_coeff_0 poly_mult)

lemma (in poly_mod) M_inv_M_id[simp]: "M (inv_M x) = M x" 
  unfolding inv_M_def M_def by simp

lemma lead_coeff_factor: assumes u: "u = v * (w :: 'a ::idom poly)"
  shows "smult (lead_coeff u) u = (smult (lead_coeff w) v) * (smult (lead_coeff v) w)"
  "lead_coeff (smult (lead_coeff w) v) = lead_coeff u" "lead_coeff (smult (lead_coeff v) w) = lead_coeff u" 
  unfolding u by (auto simp: lead_coeff_mult lead_coeff_smult)

lemma not_irreducible\<^sub>d_lead_coeff_factors: assumes "\<not> irreducible\<^sub>d (u :: 'a :: idom poly)" "degree u \<noteq> 0" 
  shows "\<exists> f g. smult (lead_coeff u) u = f * g \<and> lead_coeff f = lead_coeff u \<and> lead_coeff g = lead_coeff u
  \<and> degree f < degree u \<and> degree g < degree u" 
proof -
  from assms[unfolded irreducible\<^sub>d_def, simplified] 
  obtain v w where deg: "degree v < degree u" "degree w < degree u" and u: "u = v * w" by auto
  define f where "f = smult (lead_coeff w) v" 
  define g where "g = smult (lead_coeff v) w" 
  note lf = lead_coeff_factor[OF u, folded f_def g_def]
  show ?thesis
  proof (intro exI conjI, (rule lf)+)
    show "degree f < degree u" "degree g < degree u" unfolding f_def g_def using deg u by auto
  qed
qed
  
lemma mset_subseqs_size: "mset ` {ys. ys \<in> set (subseqs xs) \<and> length ys = n} = 
  {ws. ws \<subseteq># mset xs \<and> size ws = n}" 
proof (induct xs arbitrary: n)
  case (Cons x xs n)
  show ?case (is "?l = ?r")
  proof (cases n)
    case 0
    thus ?thesis by (auto simp: Let_def)
  next
    case (Suc m)
    have "?r = {ws. ws \<subseteq># mset (x # xs)} \<inter> {ps. size ps = n}" by auto
    also have "{ws. ws \<subseteq># mset (x # xs)} = {ps. ps \<subseteq># mset xs} \<union> ((\<lambda> ps. ps + {#x#}) ` {ps. ps \<subseteq># mset xs})"
      by (simp add: multiset_subset_insert)
    also have "\<dots> \<inter> {ps. size ps = n} = {ps. ps \<subseteq># mset xs \<and> size ps = n} 
      \<union> ((\<lambda> ps. ps + {#x#}) ` {ps. ps \<subseteq># mset xs \<and> size ps = m})" unfolding Suc by auto
    finally have id: "?r =
      {ps. ps \<subseteq># mset xs \<and> size ps = n} \<union> (\<lambda>ps. ps + {#x#}) ` {ps. ps \<subseteq># mset xs \<and> size ps = m}" .
    have "?l = mset ` {ys \<in> set (subseqs xs). length ys = Suc m}
      \<union> mset ` {ys \<in> (#) x ` set (subseqs xs). length ys = Suc m}"
      unfolding Suc by (auto simp: Let_def)
    also have "mset ` {ys \<in> (#) x ` set (subseqs xs). length ys = Suc m}
      = (\<lambda>ps. ps + {#x#}) ` mset ` {ys \<in> set (subseqs xs). length ys = m}" by force
    finally have id': "?l = mset ` {ys \<in> set (subseqs xs). length ys = Suc m} \<union>
      (\<lambda>ps. ps + {#x#}) ` mset ` {ys \<in> set (subseqs xs). length ys = m}" .
    show ?thesis unfolding id id' Cons[symmetric] unfolding Suc by simp
  qed
qed auto

context poly_mod_2
begin
lemma prod_list_m[simp]: "prod_list_m fs = Mp (prod_list fs)" 
  by (induct fs, auto)

lemma inv_Mp_coeff: "coeff (inv_Mp f) n = inv_M (coeff f n)" 
  unfolding inv_Mp_def
  by (rule coeff_map_poly, insert m1, auto simp: inv_M_def)

lemma Mp_inv_Mp_id[simp]: "Mp (inv_Mp f) = Mp f" 
  unfolding poly_eq_iff Mp_coeff inv_Mp_coeff by simp

lemma inv_M_rev: assumes bnd: "2 * abs c < m" 
  shows "inv_M (M c) = c"
proof (cases "c \<ge> 0")
  case True
  with bnd show ?thesis unfolding M_def inv_M_def by auto
next
  case False
  have 2: "\<And> v :: int. 2 * v = v + v" by auto
  from False have c: "c < 0" by auto
  from bnd c have "c + m > 0" "c + m < m" by auto
  with c have cm: "c mod m = c + m"
    by (metis le_less mod_add_self2 mod_pos_pos_trivial)
  from c bnd have "2 * (c mod m) > m" unfolding cm by auto
  with bnd c show ?thesis unfolding M_def inv_M_def cm by auto
qed

lemma inv_Mp_rev: assumes bnd: "\<And> n. 2 * abs (coeff f n) < m" 
  shows "inv_Mp (Mp f) = f" 
proof (rule poly_eqI)
  fix n
  define c where "c = coeff f n" 
  from bnd[of n, folded c_def] have bnd: "2 * abs c < m" by auto
  show "coeff (inv_Mp (Mp f)) n = coeff f n" unfolding inv_Mp_coeff Mp_coeff c_def[symmetric]
    using inv_M_rev[OF bnd] .
qed

lemma mul_const_commute_below: "mul_const x (mul_const y z) = mul_const y (mul_const x z)" 
    unfolding mul_const_def by (metis mod_mult_right_eq mult.left_commute)

context
  fixes p n 
    and sl_impl :: "(int poly, int \<times> int poly list, 'state)subseqs_foldr_impl" 
    and sli :: "int \<times> int poly list \<Rightarrow> int poly list \<Rightarrow> nat \<Rightarrow> 'state \<Rightarrow> bool" 
  assumes prime: "prime p" 
  and m: "m = p^n" 
  and n: "n \<noteq> 0" 
  and sl_impl: "correct_subseqs_foldr_impl (\<lambda>x. map_prod (mul_const x) (Cons x)) sl_impl sli"
begin
private definition "test_dvd_exec lu u ws = (\<not> inv_Mp (Mp (smult lu (prod_mset ws))) dvd smult lu u)" 

private definition "test_dvd u ws = (\<forall> v l. v dvd u \<longrightarrow> 0 < degree v \<longrightarrow> degree v < degree u
  \<longrightarrow> \<not> v =m smult l (prod_mset ws))"

private definition "large_m u vs = (\<forall> v n. v dvd u \<longrightarrow> degree v \<le> degree_bound vs \<longrightarrow> 2 * abs (coeff v n) < m)" 

lemma large_m_factor: "large_m u vs \<Longrightarrow> v dvd u \<Longrightarrow> large_m v vs"
  unfolding large_m_def using dvd_trans by auto
  

lemma test_dvd_factor: assumes u: "u \<noteq> 0" and test: "test_dvd u ws" and vu: "v dvd u" 
  shows "test_dvd v ws" 
proof -
  from vu obtain w where uv: "u = v * w" unfolding dvd_def by auto
  from u have deg: "degree u = degree v + degree w" unfolding uv
    by (subst degree_mult_eq, auto)
  show ?thesis unfolding test_dvd_def 
  proof (intro allI impI, goal_cases)
    case (1 f l)
    from 1(1) have fu: "f dvd u" unfolding uv by auto
    from 1(3) have deg: "degree f < degree u" unfolding deg by auto
    from test[unfolded test_dvd_def, rule_format, OF fu 1(2) deg]
    show ?case .
  qed
qed

lemma coprime_exp_mod: "coprime lu p \<Longrightarrow> prime p \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> lu mod p ^ n \<noteq> 0"
  by (auto simp add: abs_of_pos prime_gt_0_int)
  
interpretation correct_subseqs_foldr_impl "\<lambda>x. map_prod (mul_const x) (Cons x)" sl_impl sli by fact

lemma reconstruction: assumes
    res: "reconstruction sl_impl m2 state u (smult lu u) lu d r vs res cands = fs"
  and f: "f = u * prod_list res"
  and meas: "meas = (r - d, cands)" 
  and dr: "d + d \<le> r" 
  and r: "r = length vs" 
  and cands: "set cands \<subseteq> S (lu,[]) vs d"
  and d0: "d = 0 \<Longrightarrow> cands = []" 
  and lu: "lu = lead_coeff u" 
  and factors: "unique_factorization_m u (lu,mset vs)" 
  and sf: "poly_mod.square_free_m p u" 
  and cop: "coprime lu p"
  and norm: "\<And> v.  v \<in> set vs \<Longrightarrow> Mp v = v" 
  and tests: "\<And> ws. ws \<subseteq># mset vs \<Longrightarrow> ws \<noteq> {#} \<Longrightarrow> 
    size ws < d \<or> size ws = d \<and> ws \<notin> (mset o snd) ` set cands 
    \<Longrightarrow> test_dvd u ws"
  and irr: "\<And> f. f \<in> set res \<Longrightarrow> irreducible\<^sub>d f" 
  and deg: "degree u > 0" 
  and cands_ne: "cands \<noteq> [] \<Longrightarrow> d < r" 
  and large: "\<forall> v n. v dvd smult lu u \<longrightarrow> degree v \<le> degree_bound vs 
    \<longrightarrow> 2 * abs (coeff v n) < m" 
  and f0: "f \<noteq> 0"
  and state: "sli (lu,[]) vs d state" 
  and m2: "m2 = m div 2" 
  shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible\<^sub>d fi)"
proof -
  from large have large: "large_m (smult lu u) vs" unfolding large_m_def by auto
  interpret p: poly_mod_prime p using prime by unfold_locales  
  define R where "R \<equiv> measures [
    \<lambda> (n :: nat,cds :: (int \<times> int poly list) list). n, 
    \<lambda> (n,cds). length cds]" 
  have wf: "wf R" unfolding R_def by simp
  have mset_snd_S: "\<And> vs lu d. (mset \<circ> snd) ` S (lu,[]) vs d = 
    { ws. ws \<subseteq># mset vs \<and> size ws = d}"
    by (fold mset_subseqs_size image_comp, unfold S_def image_Collect, auto)
  have inv_M2[simp]: "inv_M2 m2 = inv_M" unfolding inv_M2_def m2 inv_M_def
    by (intro ext, auto)
  have inv_Mp2[simp]: "inv_Mp2 m2 = inv_Mp" unfolding inv_Mp2_def inv_Mp_def by simp
  have p_Mp[simp]: "\<And> f. p.Mp (Mp f) = p.Mp f" using m p.m1 n Mp_Mp_pow_is_Mp by blast
  {
    fix u lu vs
    assume eq: "Mp u = Mp (smult lu (prod_mset vs))" and cop: "coprime lu p" and size: "size vs \<noteq> 0"
      and mi: "\<And> v. v \<in># vs \<Longrightarrow> irreducible\<^sub>d_m v \<and> monic v"     
    from cop p.m1 have lu0: "lu \<noteq> 0" by auto
    from size have "vs \<noteq> {#}" by auto
    then obtain v vs' where vs_v: "vs = vs' + {#v#}" by (cases vs, auto)
    have mon: "monic (prod_mset vs)" 
      by (rule monic_prod_mset, insert mi, auto)
    hence vs0: "prod_mset vs \<noteq> 0" by (metis coeff_0 zero_neq_one)
    from mon have l_vs: "lead_coeff (prod_mset vs) = 1" .
    have deg_ws: "degree_m (smult lu (prod_mset vs)) = degree (smult lu (prod_mset vs))"
      by (rule degree_m_eq[OF _ m1], unfold lead_coeff_smult,
      insert cop n p.m1 l_vs, auto simp: m)
    with eq have "degree_m u = degree (smult lu (prod_mset vs))" by auto
    also have "\<dots> = degree (prod_mset vs' * v)" unfolding degree_smult_eq vs_v using lu0 by (simp add:ac_simps)
    also have "\<dots> = degree (prod_mset vs') + degree v" 
      by (rule degree_mult_eq, insert vs0[unfolded vs_v], auto)
    also have "\<dots> \<ge> degree v" by simp
    finally have deg_v: "degree v \<le> degree_m u" .
    from mi[unfolded vs_v, of v] have "irreducible\<^sub>d_m v" by auto
    hence "0 < degree_m v" unfolding irreducible\<^sub>d_m_def by auto
    also have "\<dots> \<le> degree v" by (rule degree_m_le)
    also have "\<dots> \<le> degree_m u" by (rule deg_v)
    also have "\<dots> \<le> degree u" by (rule degree_m_le)
    finally have "degree u > 0" by auto
  } note deg_non_zero = this
  {
    fix u :: "int poly" and vs :: "int poly list" and d :: nat
    assume deg_u: "degree u > 0"
    and cop: "coprime (lead_coeff u) p"
    and uf: "unique_factorization_m u (lead_coeff u, mset vs)" 
    and sf: "p.square_free_m u"
    and norm: "\<And> v. v \<in> set vs \<Longrightarrow> Mp v = v"
    and d: "size (mset vs) < d + d"
    and tests: "\<And> ws. ws \<subseteq># mset vs \<Longrightarrow> ws \<noteq> {#} \<Longrightarrow> size ws < d \<Longrightarrow> test_dvd u ws" 
    from deg_u have u0: "u \<noteq> 0" by auto
    have "irreducible\<^sub>d u"
    proof (rule irreducible\<^sub>dI[OF deg_u])
      fix q q' :: "int poly"
      assume deg: "degree q > 0" "degree q < degree u" "degree q' > 0" "degree q' < degree u"
         and uq: "u = q * q'"
      then have qu: "q dvd u" and q'u: "q' dvd u" by auto
      from u0 have deg_u: "degree u = degree q + degree q'" unfolding uq 
        by (subst degree_mult_eq, auto)
      from coprime_lead_coeff_factor[OF prime cop[unfolded uq]]
      have cop_q: "coprime (lead_coeff q) p" "coprime (lead_coeff q') p" by auto
      from unique_factorization_m_factor[OF prime uf[unfolded uq] _ _ n m, folded uq, 
        OF cop sf]          
      obtain fs gs l where uf_q: "unique_factorization_m q (lead_coeff q, fs)"
        and uf_q': "unique_factorization_m q' (lead_coeff q', gs)"
        and Mf_eq: "Mf (l, mset vs) = Mf (lead_coeff q * lead_coeff q', fs + gs)" 
        and fs_id: "image_mset Mp fs = fs" 
        and gs_id: "image_mset Mp gs = gs" by auto
      from Mf_eq fs_id gs_id have "image_mset Mp (mset vs) = fs + gs" 
        unfolding Mf_def by auto
      also have "image_mset Mp (mset vs) = mset vs" using norm by (induct vs, auto)
      finally have eq: "mset vs = fs + gs" by simp
      from uf_q[unfolded unique_factorization_m_alt_def factorization_m_def split]
      have q_eq: "q =m smult (lead_coeff q) (prod_mset fs)" by auto
      have "degree_m q = degree q" 
        by (rule degree_m_eq[OF _ m1], insert cop_q(1) n p.m1, unfold m, 
          auto simp:)
      with q_eq have degm_q: "degree q = degree (Mp (smult (lead_coeff q) (prod_mset fs)))" by auto
      with deg have fs_nempty: "fs \<noteq> {#}" 
        by (cases fs; cases "lead_coeff q = 0"; auto simp: Mp_def)
      from uf_q'[unfolded unique_factorization_m_alt_def factorization_m_def split]
      have q'_eq: "q' =m smult (lead_coeff q') (prod_mset gs)" by auto
      have "degree_m q' = degree q'" 
        by (rule degree_m_eq[OF _ m1], insert cop_q(2) n p.m1, unfold m, 
          auto simp:)
      with q'_eq have degm_q': "degree q' = degree (Mp (smult (lead_coeff q') (prod_mset gs)))" by auto
      with deg have gs_nempty: "gs \<noteq> {#}" 
        by (cases gs; cases "lead_coeff q' = 0"; auto simp: Mp_def)
  
      from eq have size: "size fs + size gs = size (mset vs)" by auto
      with d have choice: "size fs < d \<or> size gs < d" by auto
      from choice show False
      proof
        assume fs: "size fs < d" 
        from eq have sub: "fs \<subseteq># mset vs" using mset_subset_eq_add_left[of fs gs] by auto
        have "test_dvd u fs"
          by (rule tests[OF sub fs_nempty, unfolded Nil], insert fs, auto)
        from this[unfolded test_dvd_def] uq deg q_eq show False by auto
      next
        assume gs: "size gs < d"
        from eq have sub: "gs \<subseteq># mset vs" using mset_subset_eq_add_left[of fs gs] by auto
        have "test_dvd u gs"
          by (rule tests[OF sub gs_nempty, unfolded Nil], insert gs, auto)
        from this[unfolded test_dvd_def] uq deg q'_eq show False unfolding uq by auto
      qed
    qed
  } note irreducible\<^sub>d_via_tests = this
  show ?thesis using assms(1-16) large state
  proof (induct meas arbitrary: u lu d r vs res cands state rule: wf_induct[OF wf])
    case (1 meas u lu d r vs res cands state)
    note IH = 1(1)[rule_format]
    note res = 1(2)[unfolded reconstruction.simps[where cands = cands]]
    note f = 1(3)
    note meas = 1(4)
    note dr = 1(5)
    note r = 1(6)
    note cands = 1(7)
    note d0 = 1(8)
    note lu = 1(9)
    note factors = 1(10)
    note sf = 1(11)
    note cop = 1(12)
    note norm = 1(13)
    note tests = 1(14)
    note irr = 1(15)
    note deg_u = 1(16)
    note cands_empty = 1(17)
    note large = 1(18)
    note state = 1(19)
    from unique_factorization_m_zero[OF factors] 
    have Mlu0: "M lu \<noteq> 0" by auto
    from Mlu0 have lu0: "lu \<noteq> 0" by auto
    from this[unfolded lu] have u0: "u \<noteq> 0" by auto
    from unique_factorization_m_imp_factorization[OF factors]
    have fact: "factorization_m u (lu,mset vs)" by auto
    from this[unfolded factorization_m_def split] norm
    have vs: "u =m smult lu (prod_list vs)" and 
      vs_mi: "\<And> f. f\<in>#mset vs \<Longrightarrow> irreducible\<^sub>d_m f \<and> monic f" by auto
    let ?luu = "smult lu u" 
    show ?case
    proof (cases cands)
      case Nil
      note res = res[unfolded this]
      let ?d' = "Suc d"
      show ?thesis
      proof (cases "r < ?d' + ?d'")
        case True
        with res have fs: "fs = u # res" by (simp add: Let_def)
        from True[unfolded r] have size: "size (mset vs) < ?d' + ?d'" by auto
        have "irreducible\<^sub>d u" 
          by (rule irreducible\<^sub>d_via_tests[OF deg_u cop[unfolded lu] factors(1)[unfolded lu] 
          sf norm size tests], auto simp: Nil)
        with fs f irr show ?thesis by simp
      next
        case False
        with dr have dr: "?d' + ?d' \<le> r" and dr': "?d' < r" by auto
        obtain state' cands' where sln: "next_subseqs_foldr sl_impl state = (cands',state')" by force
        from next_subseqs_foldr[OF sln state] have state': "sli (lu,[]) vs (Suc d) state'"
          and cands': "set cands' = S (lu,[]) vs (Suc d)" by auto
        let ?new = "subseqs_length mul_const lu ?d' vs" 
        have R: "((r - Suc d, cands'), meas) \<in> R" unfolding meas R_def using False by auto
        from res False sln
        have fact: "reconstruction sl_impl m2 state' u ?luu lu ?d' r vs res cands' = fs" by auto
        show ?thesis 
        proof (rule IH[OF R fact f refl dr r _ _ lu factors sf cop norm _ irr deg_u dr' large state'], goal_cases) 
          case (4 ws)
          show ?case
          proof (cases "size ws = Suc d")
            case False
            with 4 have "size ws < Suc d" by auto
            thus ?thesis by (intro tests[OF 4(1-2)], unfold Nil, auto)
          next
            case True
            from 4(3)[unfolded cands' mset_snd_S] True 4(1) show ?thesis by auto
          qed
        qed (auto simp: cands')
      qed
    next
      case (Cons c cds)
      with d0 have d0: "d > 0" by auto
      obtain lv' ws where c: "c = (lv',ws)" by force
      let ?lv = "inv_M lv'" 
      define vb where "vb \<equiv> inv_Mp (Mp (smult lu (prod_list ws)))" 
      note res = res[unfolded Cons c list.simps split]
      from cands[unfolded Cons c S_def] have ws: "ws \<in> set (subseqs vs)" "length ws = d" 
        and lv'': "lv' = foldr mul_const ws lu" by auto
      from subseqs_sub_mset[OF ws(1)] have ws_vs: "mset ws \<subseteq># mset vs" "set ws \<subseteq> set vs" 
        using set_mset_mono subseqs_length_simple_False by auto fastforce
      have mon_ws: "monic (prod_mset (mset ws))" 
        by (rule monic_prod_mset, insert ws_vs vs_mi, auto) 
      have l_ws: "lead_coeff (prod_mset (mset ws)) = 1" using mon_ws .
      have lv': "M lv' = M (coeff (smult lu (prod_list ws)) 0)" 
        unfolding lv'' coeff_smult
        by (induct ws arbitrary: lu, auto simp: mul_const_def M_def coeff_mult_0)
           (metis mod_mult_right_eq mult.left_commute)
      show ?thesis
      proof (cases "?lv dvd coeff ?luu 0 \<and> vb dvd ?luu")
        case False
        have ndvd: "\<not> vb dvd ?luu" 
        proof
          assume dvd: "vb dvd ?luu" 
          hence "coeff vb 0 dvd coeff ?luu 0" by (metis coeff_mult_0 dvd_def)
          with dvd False have "?lv \<noteq> coeff vb 0" by auto
          also have "lv' = M lv'" using ws(2) d0 unfolding lv''
            by (cases ws, force, simp add: M_def mul_const_def)
          also have "inv_M (M lv') = coeff vb 0" unfolding vb_def inv_Mp_coeff Mp_coeff lv' by simp 
          finally show False by simp
        qed
        from False res 
        have res: "reconstruction sl_impl m2 state u ?luu lu d r vs res cds = fs" 
          unfolding vb_def Let_def by auto
        have R: "((r - d, cds), meas) \<in> R" unfolding meas Cons R_def by auto
        from cands have cands: "set cds \<subseteq> S (lu,[]) vs d" 
          unfolding Cons by auto
        show ?thesis
        proof (rule IH[OF R res f refl dr r cands _ lu factors sf cop norm _ irr deg_u _ large state], goal_cases) 
          case (3 ws')
          show ?case 
          proof (cases "ws' = mset ws")
            case False
            show ?thesis
              by (rule tests[OF 3(1-2)], insert 3(3) False, force simp: Cons c)
          next
            case True
            have test: "test_dvd_exec lu u ws'"
              unfolding True test_dvd_exec_def using ndvd unfolding vb_def by simp
            show ?thesis unfolding test_dvd_def
            proof (intro allI impI notI, goal_cases)
              case (1 v l)
              note deg_v = 1(2-3)
              from 1(1) obtain w where u: "u = v * w" unfolding dvd_def by auto
              from u0 have deg: "degree u = degree v + degree w" unfolding u 
                by (subst degree_mult_eq, auto)
              define v' where "v' = smult (lead_coeff w) v" 
              define w' where "w' = smult (lead_coeff v) w" 
              let ?ws = "smult (lead_coeff w * l) (prod_mset ws')" 
              from arg_cong[OF 1(4), of "\<lambda> f. Mp (smult (lead_coeff w) f)"]
              have v'_ws': "Mp v' = Mp ?ws" unfolding v'_def 
                by simp
              from lead_coeff_factor[OF u, folded v'_def w'_def]
              have prod: "?luu = v' * w'" and lc: "lead_coeff v' = lu" and "lead_coeff w' = lu"
                unfolding lu by auto
              with lu0 have lc0: "lead_coeff v \<noteq> 0" "lead_coeff w \<noteq> 0" unfolding v'_def w'_def by auto
              from deg_v have deg_w: "0 < degree w" "degree w < degree u" unfolding deg by auto
              from deg_v deg_w lc0 
              have deg: "0 < degree v'" "degree v' < degree u" "0 < degree w'" "degree w' < degree u" 
                unfolding v'_def w'_def by auto
              from prod have v_dvd: "v' dvd ?luu" by auto
              with test[unfolded test_dvd_exec_def] 
              have neq: "v' \<noteq> inv_Mp (Mp (smult lu (prod_mset ws')))" by auto
              have deg_m_v': "degree_m v' = degree v'" 
                by (rule degree_m_eq[OF _ m1], unfold lc m, 
                insert cop prime n coprime_exp_mod, auto)
              with v'_ws' have "degree v' = degree_m ?ws" by simp
              also have "\<dots> \<le> degree_m (prod_mset ws')" by (rule degree_m_smult_le)
              also have "\<dots> = degree_m (prod_list ws)" unfolding True by simp
              also have "\<dots> \<le> degree (prod_list ws)" by (rule degree_m_le)
              also have "\<dots> \<le> degree_bound vs" 
                using ws_vs(1) ws(2) dr[unfolded r] degree_bound by auto
              finally have "degree v' \<le> degree_bound vs" .
              from inv_Mp_rev[OF large[unfolded large_m_def, rule_format, OF v_dvd this]]
              have inv: "inv_Mp (Mp v') = v'" by simp
              from arg_cong[OF v'_ws', of inv_Mp, unfolded inv]
              have v': "v' = inv_Mp (Mp ?ws)" by auto
              have deg_ws: "degree_m ?ws = degree ?ws" 
              proof (rule degree_m_eq[OF _ m1], 
                unfold lead_coeff_smult True l_ws, rule)
                assume "lead_coeff w * l * 1 mod m = 0" 
                hence 0: "M (lead_coeff w * l) = 0" unfolding M_def by simp
                have "Mp ?ws = Mp (smult (M (lead_coeff w * l)) (prod_mset ws'))" by simp
                also have "\<dots> = 0" unfolding 0 by simp
                finally have "Mp ?ws = 0" by simp
                hence "v' = 0" unfolding v' by (simp add: inv_Mp_def)
                with deg show False by auto
              qed
              from arg_cong[OF v', of "\<lambda> f. lead_coeff (Mp f)", simplified] 
              have "M lu = M (lead_coeff v')" using lc by simp
              also have "\<dots> = lead_coeff (Mp v')" 
                by (rule degree_m_eq_lead_coeff[OF deg_m_v', symmetric])
              also have "\<dots> = lead_coeff (Mp ?ws)" 
                using arg_cong[OF v', of "\<lambda> f. lead_coeff (Mp f)"] by simp
              also have "\<dots> = M (lead_coeff ?ws)"
                by (rule degree_m_eq_lead_coeff[OF deg_ws])
              also have "\<dots> = M (lead_coeff w * l)" unfolding lead_coeff_smult True l_ws by simp
              finally have id: "M lu = M (lead_coeff w * l)" .
              note v'
              also have "Mp ?ws = Mp (smult (M (lead_coeff w * l)) (prod_mset ws'))" by simp
              also have "\<dots> = Mp (smult lu (prod_mset ws'))" unfolding id[symmetric] by simp
              finally show False using neq by simp 
            qed
          qed
        qed (insert d0 Cons cands_empty, auto)
      next
        case True
        define pp_vb where "pp_vb \<equiv> primitive_part vb" 
        define u' where "u' \<equiv> u div pp_vb"
        define lu' where "lu' \<equiv> lead_coeff u'" 
        let ?luu' = "smult lu' u'" 
        define vs' where "vs' \<equiv> fold remove1 ws vs" 
        obtain state' cands' where slc: "subseqs_foldr sl_impl (lu',[]) vs' d = (cands', state')" by force
        from subseqs_foldr[OF slc] have state': "sli (lu',[]) vs' d state'"
          and cands': "set cands' = S (lu',[]) vs' d" by auto
        let ?res' = "pp_vb # res" 
        let ?r' = "r - length ws" 
        note defs = vb_def pp_vb_def u'_def lu'_def vs'_def slc
        from fold_remove1_mset[OF subseqs_sub_mset[OF ws(1)]]
        have vs_split: "mset vs = mset vs' + mset ws" unfolding vs'_def by auto
        hence vs'_diff: "mset vs' = mset vs - mset ws" and ws_sub: "mset ws \<subseteq># mset vs" by auto
        from arg_cong[OF vs_split, of size]
        have r': "?r' = length vs'" unfolding defs r by simp
        from arg_cong[OF vs_split, of prod_mset] 
        have prod_vs: "prod_list vs = prod_list vs' * prod_list ws" by simp
        from arg_cong[OF vs_split, of set_mset] have set_vs: "set vs = set vs' \<union> set ws" by auto
        note inv = inverse_mod_coprime_exp[OF m prime n]
        note p_inv = p.inverse_mod_coprime[OF prime]
        from True res slc
        have res: "(if ?r' < d + d then u' # ?res' else reconstruction sl_impl m2 state'
          u' ?luu' lu' d ?r' vs' ?res' cands') = fs" 
           unfolding Let_def defs by auto
        from True have dvd: "vb dvd ?luu" by simp
        from dvd_smult_int[OF lu0 this] have ppu: "pp_vb dvd u" unfolding defs by simp
        hence u: "u = pp_vb * u'" unfolding u'_def
          by (metis dvdE mult_eq_0_iff nonzero_mult_div_cancel_left)
        hence uu': "u' dvd u" unfolding dvd_def by auto
        have f: "f = u' * prod_list ?res'" using f u by auto
        let ?fact = "smult lu (prod_mset (mset ws))" 
        have Mp_vb: "Mp vb = Mp (smult lu (prod_list ws))"  unfolding vb_def by simp
        have pp_vb_vb: "smult (content vb) pp_vb = vb" unfolding pp_vb_def by (rule content_times_primitive_part)
        {
          have "smult (content vb) u = (smult (content vb) pp_vb) * u'" unfolding u by simp
          also have "smult (content vb) pp_vb = vb" by fact
          finally have "smult (content vb) u = vb * u'" by simp
          from arg_cong[OF this, of Mp]
          have "Mp (Mp vb * u') = Mp (smult (content vb) u)" by simp
          hence "Mp (smult (content vb) u) = Mp (?fact * u')" unfolding Mp_vb by simp
        } note prod = this
        from arg_cong[OF this, of p.Mp]
        have prod': "p.Mp (smult (content vb) u) = p.Mp (?fact * u')" by simp
        from dvd have "lead_coeff vb dvd lead_coeff (smult lu u)" 
          by (metis dvd_def lead_coeff_mult)
        hence ldvd: "lead_coeff vb dvd lu * lu" unfolding lead_coeff_smult lu by simp
        from cop have cop_lu: "coprime (lu * lu) p"
          by simp
        from coprime_divisors [OF ldvd dvd_refl] cop_lu
        have cop_lvb: "coprime (lead_coeff vb) p" by simp
        then have cop_vb: "coprime (content vb) p" 
          by (auto intro: coprime_divisors[OF content_dvd_coeff dvd_refl])
        from u have "u' dvd u" unfolding dvd_def by auto
        hence "lead_coeff u' dvd lu" unfolding lu by (metis dvd_def lead_coeff_mult)
        from coprime_divisors[OF this dvd_refl] cop
        have "coprime (lead_coeff u') p" by simp
        hence "coprime (lu * lead_coeff u') p" and cop_lu': "coprime lu' p" 
          using cop by (auto simp: lu'_def)
        hence cop': "coprime (lead_coeff (?fact * u')) p" 
          unfolding lead_coeff_mult lead_coeff_smult l_ws by simp
        have "p.square_free_m (smult (content vb) u)" using cop_vb sf p_inv
          by (auto intro!: p.square_free_m_smultI)
        from p.square_free_m_cong[OF this prod']
        have sf': "p.square_free_m (?fact * u')" by simp
        from p.square_free_m_factor[OF this] 
        have sf_u': "p.square_free_m u'" by simp
        have "unique_factorization_m (smult (content vb) u) (lu * content vb, mset vs)"
          using cop_vb factors inv by (auto intro: unique_factorization_m_smult)
        from unique_factorization_m_cong[OF this prod]
        have uf: "unique_factorization_m (?fact * u') (lu * content vb, mset vs)" .
        {
          from unique_factorization_m_factor[OF prime uf cop' sf' n m] 
          obtain fs gs where uf1: "unique_factorization_m ?fact (lu, fs)"
            and uf2: "unique_factorization_m u' (lu', gs)"
            and eq: "Mf (lu * content vb, mset vs) = Mf (lu * lead_coeff u', fs + gs)" 
            unfolding lead_coeff_smult l_ws lu'_def
            by auto
          have "factorization_m ?fact (lu, mset ws)"
            unfolding factorization_m_def split using set_vs vs_mi norm by auto
          with uf1[unfolded unique_factorization_m_alt_def] have "Mf (lu,mset ws) = Mf (lu, fs)"
            by blast
          hence fs_ws: "image_mset Mp fs = image_mset Mp (mset ws)" unfolding Mf_def split by auto
          from eq[unfolded Mf_def split] 
          have "image_mset Mp (mset vs) = image_mset Mp fs + image_mset Mp gs" by auto
          from this[unfolded fs_ws vs_split] have gs: "image_mset Mp gs = image_mset Mp (mset vs')"
            by (simp add: ac_simps)
          from uf1 have uf1: "unique_factorization_m ?fact (lu, mset ws)" 
            unfolding unique_factorization_m_def Mf_def split fs_ws by simp
          from uf2 have uf2: "unique_factorization_m u' (lu', mset vs')" 
            unfolding unique_factorization_m_def Mf_def split gs by simp
          note uf1 uf2
        }
        hence factors: "unique_factorization_m u' (lu', mset vs')" 
          "unique_factorization_m ?fact (lu, mset ws)" by auto
        have lu': "lu' = lead_coeff u'" unfolding lu'_def by simp
        have vb0: "vb \<noteq> 0" using dvd lu0 u0 by auto        
        from ws(2) have size_ws: "size (mset ws) = d" by auto
        with d0 have size_ws0: "size (mset ws) \<noteq> 0" by auto
        then obtain w ws' where ws_w: "ws = w # ws'" by (cases ws, auto)
        from Mp_vb have Mp_vb': "Mp vb = Mp (smult lu (prod_mset (mset ws)))" by auto
        have deg_vb: "degree vb > 0"
          by (rule deg_non_zero[OF Mp_vb' cop size_ws0 vs_mi], insert vs_split, auto)
        also have "degree vb = degree pp_vb" using arg_cong[OF pp_vb_vb, of degree]
          unfolding degree_smult_eq using vb0 by auto
        finally have deg_pp: "degree pp_vb > 0" by auto
        hence pp_vb0: "pp_vb \<noteq> 0" by auto
        from factors(1)[unfolded unique_factorization_m_alt_def factorization_m_def]
        have eq_u': "Mp u' = Mp (smult lu' (prod_mset (mset vs')))" by auto 
        from r'[unfolded ws(2)] dr have "length vs' + d = r" by auto
        from this cands_empty[unfolded Cons] have "size (mset vs') \<noteq> 0" by auto
        from deg_non_zero[OF eq_u' cop_lu' this vs_mi] 
        have deg_u': "degree u' > 0" unfolding vs_split by auto
        have irr_pp: "irreducible\<^sub>d pp_vb" 
        proof (rule irreducible\<^sub>dI[OF deg_pp])
          fix q r :: "int poly"
          assume deg_q: "degree q > 0" "degree q < degree pp_vb"
            and deg_r:  "degree r > 0" "degree r < degree pp_vb"
            and pp_qr: "pp_vb = q * r"
          then have qvb: "q dvd pp_vb" by auto
          from dvd_trans[OF qvb ppu] have qu: "q dvd u" .
          have "degree pp_vb = degree q + degree r" unfolding pp_qr
            by (subst degree_mult_eq, insert pp_qr pp_vb0, auto)
          have uf: "unique_factorization_m (smult (content vb) pp_vb) (lu, mset ws)" 
            unfolding pp_vb_vb
            by (rule unique_factorization_m_cong[OF factors(2)], insert Mp_vb, auto)
          from unique_factorization_m_smultD[OF uf inv] cop_vb
          have uf: "unique_factorization_m pp_vb (lu * inverse_mod (content vb) m, mset ws)" by auto
          from ppu have "lead_coeff pp_vb dvd lu" unfolding lu by (metis dvd_def lead_coeff_mult)
          from coprime_divisors[OF this dvd_refl] cop
          have cop_pp: "coprime (lead_coeff pp_vb) p" by simp
          from coprime_lead_coeff_factor[OF prime cop_pp[unfolded pp_qr]]
          have cop_qr: "coprime (lead_coeff q) p" "coprime (lead_coeff r) p" by auto
          from p.square_free_m_factor[OF sf[unfolded u]]
          have sf_pp: "p.square_free_m pp_vb" by simp
          from unique_factorization_m_factor[OF prime uf[unfolded pp_qr] _ _ n m, 
            folded pp_qr, OF cop_pp sf_pp]
          obtain fs gs l where uf_q: "unique_factorization_m q (lead_coeff q, fs)"
            and uf_r: "unique_factorization_m r (lead_coeff r, gs)"
            and Mf_eq: "Mf (l, mset ws) = Mf (lead_coeff q * lead_coeff r, fs + gs)" 
            and fs_id: "image_mset Mp fs = fs" 
            and gs_id: "image_mset Mp gs = gs" by auto
          from Mf_eq have "image_mset Mp (mset ws) = image_mset Mp fs + image_mset Mp gs" 
            unfolding Mf_def by auto
          also have "image_mset Mp (mset ws) = mset ws" using norm ws_vs(2) by (induct ws, auto)
          finally have eq: "mset ws = image_mset Mp fs + image_mset Mp gs" by simp
          from arg_cong[OF this, of size, unfolded size_ws] have size: "size fs + size gs = d" by auto
          from uf_q[unfolded unique_factorization_m_alt_def factorization_m_def split]
          have q_eq: "q =m smult (lead_coeff q) (prod_mset fs)" by auto
          have "degree_m q = degree q" 
            by (rule degree_m_eq[OF _ m1], insert cop_qr(1) n p.m1, unfold m, 
              auto simp:)
          with q_eq have degm_q: "degree q = degree (Mp (smult (lead_coeff q) (prod_mset fs)))" by auto
          with deg_q have fs_nempty: "fs \<noteq> {#}" 
            by (cases fs; cases "lead_coeff q = 0"; auto simp: Mp_def)
          from uf_r[unfolded unique_factorization_m_alt_def factorization_m_def split]
          have r_eq: "r =m smult (lead_coeff r) (prod_mset gs)" by auto
          have "degree_m r = degree r" 
            by (rule degree_m_eq[OF _ m1], insert cop_qr(2) n p.m1, unfold m, 
              auto simp:)
          with r_eq have degm_r: "degree r = degree (Mp (smult (lead_coeff r) (prod_mset gs)))" by auto
          with deg_r have gs_nempty: "gs \<noteq> {#}" 
            by (cases gs; cases "lead_coeff r = 0"; auto simp: Mp_def)
          from gs_nempty have "size gs \<noteq> 0" by auto
          with size have size_fs: "size fs < d" by linarith
          note * = tests[unfolded test_dvd_def, rule_format, OF _ fs_nempty _ qu, of "lead_coeff q"]
          from ppu have "degree pp_vb \<le> degree u"
            using dvd_imp_degree_le u0 by blast
          with deg_q q_eq size_fs
          have "\<not> fs \<subseteq># mset vs" by (auto dest!:*)
          thus False unfolding vs_split eq fs_id gs_id using mset_subset_eq_add_left[of fs "mset vs' + gs"] 
            by (auto simp: ac_simps)
        qed
        {
          fix ws'
          assume *: "ws' \<subseteq># mset vs'" "ws' \<noteq> {#}" 
            "size ws' < d \<or> size ws' = d \<and> ws' \<notin> (mset \<circ> snd) ` set cands'"
          from *(1) have "ws' \<subseteq># mset vs" unfolding vs_split 
            by (simp add: subset_mset.add_increasing2)
          from tests[OF this *(2)] *(3)[unfolded cands' mset_snd_S] *(1)
          have "test_dvd u ws'" by auto
          from test_dvd_factor[OF u0 this[unfolded lu] uu']
          have "test_dvd u' ws'" .
        } note tests' = this
        show ?thesis
        proof (cases "?r' < d + d")
          case True
          with res have res: "fs = u' # ?res'" by auto
          from True r' have size: "size (mset vs') < d + d" by auto
          have "irreducible\<^sub>d u'" 
            by (rule irreducible\<^sub>d_via_tests[OF deg_u' cop_lu'[unfolded lu'] factors(1)[unfolded lu'] 
            sf_u' norm size tests'], insert set_vs, auto)
          with f res irr irr_pp show ?thesis by auto
        next
          case False
          have res: "reconstruction sl_impl m2 state' u' ?luu' lu' d ?r' vs' ?res' cands' = fs" 
            using False res by auto
          from False have dr: "d + d \<le> ?r'" by auto
          from False dr r r' d0 ws Cons have le: "?r' - d < r - d" by (cases ws, auto)
          hence R: "((?r' - d, cands'), meas) \<in> R" unfolding meas R_def by simp
          have dr': "d < ?r'" using le False ws(2) by linarith 
          have luu': "lu' dvd lu" using \<open>lead_coeff u' dvd lu\<close> unfolding lu' .
          have "large_m (smult lu' u') vs" 
            by (rule large_m_factor[OF large dvd_dvd_smult], insert uu' luu') 
          moreover have "degree_bound vs' \<le> degree_bound vs" 
            unfolding vs'_def degree_bound_def by (rule max_factor_degree_mono)
          ultimately have large': "large_m (smult lu' u') vs'" unfolding large_m_def by auto
          show ?thesis   
            by (rule IH[OF R res f refl dr r' _ _ lu' factors(1) sf_u' cop_lu' norm tests' _ deg_u' 
            dr' large' state'], insert irr irr_pp d0 Cons set_vs, auto simp: cands')
        qed
      qed
    qed
  qed
qed
end
end

(* select implementation of subseqs *)
definition zassenhaus_reconstruction :: 
  "int poly list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> int poly list" where
  "zassenhaus_reconstruction vs p n f = (let
     mul = poly_mod.mul_const (p^n);
     sl_impl = my_subseqs.impl (\<lambda>x. map_prod (mul x) (Cons x))
     in zassenhaus_reconstruction_generic sl_impl vs p n f)" 

context
  fixes p n f hs
  assumes prime: "prime p" 
  and cop: "coprime (lead_coeff f) p"
  and sf: "poly_mod.square_free_m p f"
  and deg: "degree f > 0" 
  and bh: "berlekamp_hensel p n f = hs" 
  and bnd: "2 * \<bar>lead_coeff f\<bar> * factor_bound f (degree_bound hs) < p ^ n" 
begin

private lemma n: "n \<noteq> 0" 
proof
  assume n: "n = 0" 
  hence pn: "p^n = 1" by auto  
  let ?f = "smult (lead_coeff f) f" 
  let ?d = "degree_bound hs" 
  have f: "f \<noteq> 0" using deg by auto
  hence "lead_coeff f \<noteq> 0" by auto
  hence lf: "abs (lead_coeff f) > 0" by auto
  obtain c d where c: "factor_bound f (degree_bound hs) = c" "abs (lead_coeff f) = d" by auto
  {
    assume *: "1 \<le> c" "2 * d * c < 1" "0 < d" 
    hence "1 \<le> d" by auto
    from mult_mono[OF this *(1)] * have "1 \<le> d * c" by auto
    hence "2 * d * c \<ge> 2" by auto
    with * have False by auto
  } note tedious = this 
  have "1 \<le> factor_bound f ?d" 
    using factor_bound[OF f, of 1 ?d 0] by auto
  also have "\<dots> = 0" using bnd unfolding pn 
    using factor_bound_ge_0[of f "degree_bound hs", OF f] lf unfolding c
    by (cases "c \<ge> 1"; insert tedious, auto)
  finally show False by simp
qed

interpretation p: poly_mod_prime p using prime by unfold_locales

lemma zassenhaus_reconstruction_generic:
  assumes sl_impl: "correct_subseqs_foldr_impl (\<lambda>v. map_prod (poly_mod.mul_const (p^n) v) (Cons v)) sl_impl sli"
  and res: "zassenhaus_reconstruction_generic sl_impl hs p n f = fs" 
  shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible\<^sub>d fi)"
proof -
  let ?lc = "lead_coeff f" 
  let ?ff = "smult ?lc f" 
  let ?q = "p^n" 
  have p1: "p > 1" using prime unfolding prime_int_iff by simp
  interpret poly_mod_2 "p^n" using p1 n unfolding poly_mod_2_def by simp
  obtain cands state where slc: "subseqs_foldr sl_impl (lead_coeff f, []) hs 0 = (cands, state)" by force
  interpret correct_subseqs_foldr_impl "\<lambda>x. map_prod (mul_const x) (Cons x)" sl_impl sli by fact
  from subseqs_foldr[OF slc] have state: "sli (lead_coeff f, []) hs 0 state" by auto
  from res[unfolded zassenhaus_reconstruction_generic_def bh split Let_def slc fst_conv]
  have res: "reconstruction sl_impl (?q div 2) state f ?ff ?lc 0 (length hs) hs [] [] = fs" by auto
  from p.berlekamp_hensel_unique[OF cop sf bh n]
  have ufact: "unique_factorization_m f (?lc, mset hs)" by simp
  note bh = p.berlekamp_hensel[OF cop sf bh n]
  from deg have f0: "f \<noteq> 0" and lf0: "?lc \<noteq> 0" by auto
  hence ff0: "?ff \<noteq> 0" by auto
  have bnd: "\<forall>g k. g dvd ?ff \<longrightarrow> degree g \<le> degree_bound hs \<longrightarrow> 2 * \<bar>coeff g k\<bar> < p ^ n"
  proof (intro allI impI, goal_cases)
    case (1 g k)
    from factor_bound_smult[OF f0 lf0 1, of k] 
    have "\<bar>coeff g k\<bar> \<le> \<bar>?lc\<bar> * factor_bound f (degree_bound hs)" .
    hence "2 * \<bar>coeff g k\<bar> \<le> 2 * \<bar>?lc\<bar> * factor_bound f (degree_bound hs)" by auto
    also have "\<dots> < p^n" using bnd .
    finally show ?case .
  qed
  note bh' = bh[unfolded factorization_m_def split]
  have deg_f: "degree_m f = degree f"
    using cop unique_factorization_m_zero [OF ufact] n
    by (auto simp add: M_def intro: degree_m_eq [OF _ m1])
  have mon_hs: "monic (prod_list hs)" using bh' by (auto intro: monic_prod_list)
  have Mlc: "M ?lc \<in> {1 ..< p^n}" 
    by (rule prime_cop_exp_poly_mod[OF prime cop n])
  hence "?lc \<noteq> 0" by auto
  hence f0: "f \<noteq> 0" by auto
  have degm: "degree_m (smult ?lc (prod_list hs)) = degree (smult ?lc (prod_list hs))" 
    by (rule degree_m_eq[OF _ m1], insert n bh mon_hs Mlc, auto simp: M_def)
  from reconstruction[OF prime refl n sl_impl res _ refl _ refl _ refl refl ufact sf 
      cop _ _ _ deg _ bnd f0] bh(2) state
  show ?thesis by simp
qed

lemma zassenhaus_reconstruction_irreducible\<^sub>d:
  assumes res: "zassenhaus_reconstruction hs p n f = fs"
  shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible\<^sub>d fi)" 
  by (rule zassenhaus_reconstruction_generic[OF my_subseqs.impl_correct 
      res[unfolded zassenhaus_reconstruction_def Let_def]])

corollary zassenhaus_reconstruction:
  assumes pr: "primitive f"
  assumes res: "zassenhaus_reconstruction hs p n f = fs"
  shows "f = prod_list fs \<and> (\<forall> fi \<in> set fs. irreducible fi)"
  using zassenhaus_reconstruction_irreducible\<^sub>d[OF res] pr
    irreducible_primitive_connect[OF primitive_prod_list]
    by auto
end

end
