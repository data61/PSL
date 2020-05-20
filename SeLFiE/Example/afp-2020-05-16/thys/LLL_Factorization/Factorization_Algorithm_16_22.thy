(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Implementation and soundness of a modified version of Algorithm 16.22\<close>

text \<open>Algorithm 16.22 is quite similar to the LLL factorization algorithm that was verified
in the previous section. Its main difference is that it has an inner loop where each inner loop
iteration has one invocation of the LLL basis reduction algorithm. Algorithm 16.22 of the textbook
is therefore closer to the factorization algorithm as it is described by Lenstra, Lenstra, and
Lov{\'a}sz \cite{LLL}, which also uses an inner loop.

The advantage of the inner loop is that it can find factors earlier, 
and then small lattices suffice where without the inner loop one
invokes the basis reduction algorithm on a large lattice. The disadvantage of the inner loop
is that if the input is irreducible, then one cannot find any factor early, so that all but the
last iteration have been useless: only the last iteration will prove irreducibility.\<close>

text \<open>We will describe the modifications w.r.t.\ the original Algorithm 16.22 of the textbook
later in this theory.\<close>
theory Factorization_Algorithm_16_22
  imports 
    LLL_Factorization
    Sub_Sums
begin

subsection \<open>Previous lemmas obtained using local type definitions\<close>

context poly_mod_prime_type
begin                           

lemma irreducible_m_dvdm_prod_list_connect:
  assumes irr: "irreducible_m a"
  and dvd: "a dvdm (prod_list xs)"
shows "\<exists> b \<in> set xs. a dvdm b"
proof -
  let ?A="(of_int_poly a)::'a mod_ring poly"
  let ?XS="(map of_int_poly xs)::'a mod_ring poly list"
  let ?XS1 = "(of_int_poly (prod_list xs))::'a mod_ring poly"
  have [transfer_rule]: "MP_Rel a ?A"
    by (simp add: MP_Rel_def Mp_f_representative)
  have [transfer_rule]: "MP_Rel (prod_list xs) ?XS1"
    by (simp add: MP_Rel_def Mp_f_representative)
  have [transfer_rule]: "list_all2 MP_Rel xs ?XS"
    by (simp add: MP_Rel_def Mp_f_representative list_all2_conv_all_nth)
  have A: "?A dvd ?XS1" using dvd by transfer
  have "\<exists> b \<in> set ?XS. ?A dvd b" 
    by (rule irreducible_dvd_prod_list, insert irr, transfer, auto simp add: A)
  from this[untransferred] show ?thesis .
qed

end

lemma (in poly_mod_prime) irreducible_m_dvdm_prod_list:
  assumes irr: "irreducible_m a"
  and dvd: "a dvdm (prod_list xs)"
  shows "\<exists> b \<in> set xs. a dvdm b"
  by (rule poly_mod_prime_type.irreducible_m_dvdm_prod_list_connect[unfolded poly_mod_type_simps, 
        internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, 
        cancel_type_definition, OF non_empty irr dvd])


subsection \<open>The modified version of Algorithm 16.22\<close>

    (* Implementation of the for loop of step 8. The loop will finishes in two cases:
      - If j>n'
      - If a divisor is found *)

definition B2_LLL :: "int poly \<Rightarrow> int" where
  "B2_LLL f = 2 ^ (2 * degree f) * \<parallel>f\<parallel>\<^sup>2" 

hide_const (open) factors
hide_const (open) factors
hide_const (open) factor
hide_const (open) factor

context
  fixes p :: int and l :: nat
begin

context
  fixes gs :: "int poly list" 
    and f :: "int poly"
    and u :: "int poly"
    and Degs :: "nat set" 
begin

text \<open>This is the critical inner loop.

  In the textbook there is a bug, namely that the filter
  is applied to $g'$ and not to the primitive part of $g'$. (Problems occur if the content
  of $g'$ is divisible by $p$.) We have fixed this problem in the obvious way.

  However, there also is a second problem,
  namely it is only guaranteed that $g'$ is divisible by $u$ modulo $p^l$. However, for soundness
  we need to know that then also the primitive part of $g'$ is divisible by $u$ modulo $p^l$. 
  This is not necessary true, e.g., if $g' = p^l$, then the primitive part is $1$ which is not
  divisible by $u$ modulo $p^l$. 
  It is open, whether such a large $g'$ can actually occur. Therefore, the current fix
  is to manually test whether the leading coefficient of $g'$ is strictly smaller than $p^l$.

  With these two modifications, Algorithm 16.22 will become sound as proven below.\<close>

definition "LLL_reconstruction_inner j \<equiv>
  let j' = j - 1 in
  \<comment> \<open>optimization: check whether degree j' is possible\<close>
  if j' \<notin> Degs then None else
  \<comment> \<open>short vector computation\<close>
  let 
      ll = (let n = sqrt_int_ceiling (\<parallel>f\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (5 * j' * j')); 
      ll' = find_exponent p n in if ll' < l then ll' else l);
  \<comment> \<open>optimization: dynamically adjust the modulus\<close>
      pl = p^ll;
      g' = LLL_short_polynomial pl j u 
  \<comment> \<open>fix: forbid multiples of $p^l$ as short vector, unclear whether this is really required\<close>
  in if abs (lead_coeff g') \<ge> pl then None else 
  let ppg = primitive_part g'
  in
  \<comment> \<open>slight deviation from textbook: we check divisibility instead of norm-inequality\<close>
  case div_int_poly f ppg of Some f' \<Rightarrow>
    \<comment> \<open>fix: consider modular factors of ppg and not of g'\<close>
    Some (filter (\<lambda>gi. \<not> poly_mod.dvdm p gi ppg) gs, lead_coeff f', f', ppg)  
  | None \<Rightarrow> None"


function LLL_reconstruction_inner_loop where
 "LLL_reconstruction_inner_loop j =
  (if j > degree f then ([],1,1,f)
   else case LLL_reconstruction_inner j
     of Some tuple \<Rightarrow> tuple
     |  None \<Rightarrow> LLL_reconstruction_inner_loop (j+1))"
  by auto
termination by (relation "measure (\<lambda> j. Suc (degree f) - j)", auto)

end
(*The main loop (line 6)*)

partial_function (tailrec) LLL_reconstruction'' where [code]:
 "LLL_reconstruction'' gs b f factors =
  (if gs = [] then factors
   else
     let u = choose_u gs;
         d = degree u;
         gs' = remove1 u gs;
         degs = map degree gs';
         Degs = ((+) d) ` sub_mset_sums degs;
         (gs', b', f', factor) = LLL_reconstruction_inner_loop gs f u Degs (d+1)
     in LLL_reconstruction'' gs' b' f' (factor#factors)
   )"

definition "reconstruction_of_algorithm_16_22 gs f \<equiv>
  let G = [];
      b = lead_coeff f
  in LLL_reconstruction'' gs b f G"

end

definition factorization_algorithm_16_22 :: "int poly \<Rightarrow> int poly list" where
  "factorization_algorithm_16_22 f = (let 
     \<comment> \<open>find suitable prime\<close>
     p = suitable_prime_bz f;
     \<comment> \<open>compute finite field factorization\<close>
     (_, fs) = finite_field_factorization_int p f;
     \<comment> \<open>determine l and B\<close>
     n = degree f;
     \<comment> \<open>bound improved according to textbook, which uses $no = (n + 1) * (max-norm f)^2$\<close>
     no = \<parallel>f\<parallel>\<^sup>2;
     \<comment> \<open>possible improvement: $B = sqrt (2 ^{5 * n * (n - 1)} * no ^ {2 * n - 1}$, cf. @{const LLL_factorization}\<close>
     B = sqrt_int_ceiling (2 ^ (5 * n * n) * no ^ (2 * n));
     l = find_exponent p B;
     \<comment> \<open>perform hensel lifting to lift factorization to mod $p^l$\<close>
     vs = hensel_lifting p l f fs
     \<comment> \<open>reconstruct integer factors\<close>
   in reconstruction_of_algorithm_16_22 p l vs f)"


subsection \<open>Soundness proof\<close>

subsubsection \<open>Starting the proof\<close>

text \<open>Key lemma to show that forbidding values of $p^l$ or larger suffices to find correct factors.\<close>

lemma (in poly_mod_prime) Mp_smult_p_removal: "poly_mod.Mp (p * p ^ k) (smult p f) = 0 \<Longrightarrow> poly_mod.Mp (p^k) f = 0"
  by (smt add.left_neutral m1 poly_mod.Dp_Mp_eq poly_mod.Mp_smult_m_0 sdiv_poly_smult smult_smult)

lemma (in poly_mod_prime) eq_m_smult_p_removal: "poly_mod.eq_m (p * p ^ k) (smult p f) (smult p g) 
  \<Longrightarrow> poly_mod.eq_m (p^k) f g" using Mp_smult_p_removal[of k "f - g"]
  by (metis add_diff_cancel_left' diff_add_cancel diff_self poly_mod.Mp_0 poly_mod.minus_Mp(2) smult_diff_right)

lemma content_le_lead_coeff: "abs (content (f :: int poly)) \<le> abs (lead_coeff f)"
proof (cases "f = 0")
  case False
  from content_dvd_coeff[of f "degree f"] have "abs (content f) dvd abs (lead_coeff f)" by auto
  moreover have "abs (lead_coeff f) \<noteq> 0" using False by auto
  ultimately show ?thesis by (smt dvd_imp_le_int)
qed auto

lemma poly_mod_dvd_drop_smult: assumes u: "monic u" and p: "prime p" and c: "c \<noteq> 0" "\<bar>c\<bar> < p^l"
  and dvd: "poly_mod.dvdm (p^l) u (smult c f)" 
shows "poly_mod.dvdm p u f" 
  using c dvd
proof (induct l arbitrary: c rule: less_induct)
  case (less l c)
  interpret poly_mod_prime p by (unfold_locales, insert p, auto)
  note c = less(2-3)
  note dvd = less(4)
  note IH = less(1)
  show ?case
  proof (cases "l = 0")
    case True
    thus ?thesis using c dvd by auto
  next
    case l0: False
    interpret pl: poly_mod_2 "p^l" by (unfold_locales, insert m1 l0, auto)
    show ?thesis
    proof (cases "p dvd c")
      case False
      let ?i = "inverse_mod c (p ^ l)" 
      have "gcd c p = 1" using p False
        by (metis Primes.prime_int_iff gcd_ge_0_int semiring_gcd_class.gcd_dvd1 semiring_gcd_class.gcd_dvd2)
      hence "coprime c p" by (metis dvd_refl gcd_dvd_1)
      from pl.inverse_mod_coprime_exp[OF refl p l0 this] 
      have id: "pl.M (?i * c) = 1" .
      have "pl.Mp (smult ?i (smult c f)) = pl.Mp (smult (pl.M (?i * c)) f)" by simp
      also have "\<dots> = pl.Mp f" unfolding id by simp
      finally have "pl.dvdm u f" using pl.dvdm_smult[OF dvd, of ?i] unfolding pl.dvdm_def by simp
      thus "u dvdm f" using l0 pl_dvdm_imp_p_dvdm by blast 
    next
      case True
      then obtain d where cpd: "c = p * d" unfolding dvd_def by auto
      from cpd c have d0: "d \<noteq> 0" by auto
      note to_p = Mp_Mp_pow_is_Mp[OF l0 m1]
      from dvd obtain v where eq: "pl.eq_m (u * v) (smult p (smult d f))" 
        unfolding pl.dvdm_def cpd by auto
      from arg_cong[OF this, of Mp, unfolded to_p] 
      have "Mp (u * v) = 0" unfolding Mp_smult_m_0 .
      with u have "Mp v = 0"
        by (metis Mp_0 add_eq_0_iff_both_eq_0 degree_0 
            degree_m_mult_eq monic_degree_0 monic_degree_m mult_cancel_right2)
      from Mp_0_smult_sdiv_poly[OF this]
      obtain w where v: "v = smult p w" by metis
      with eq have eq: "pl.eq_m (smult p (u * w)) (smult p (smult d f))" by simp
      from l0 obtain ll where "l = Suc ll" by (cases l, auto)
      hence pl: "p^l = p * p^ll" and ll: "ll < l" by auto
      from c(2) have d_small: "\<bar>d\<bar> < p^ll" unfolding pl cpd abs_mult
        using mult_less_cancel_left_pos[of p d "p^ll"] m1 by auto
      from eq_m_smult_p_removal[OF eq[unfolded pl]] 
      have "poly_mod.eq_m (p^ll) (u * w) (smult d f)" .
      hence dvd: "poly_mod.dvdm (p^ll) u (smult d f)" unfolding poly_mod.dvdm_def by metis
      show ?thesis by (rule IH[OF ll d0 d_small dvd])
    qed
  qed
qed

context
  fixes p :: int
    and F :: "int poly"
    and N :: nat
    and l :: nat
  defines [simp]: "N \<equiv> degree F"
  assumes p: "prime p"
      and N0: "N > 0"
      and bound_l: "2 ^ N\<^sup>2 * B2_LLL F ^ (2 * N) \<le> (p^l)\<^sup>2"
begin

private lemma F0: "F\<noteq>0" using N0 
  by fastforce

private lemma p1: "p > 1" using p prime_gt_1_int by auto

interpretation p: poly_mod_prime p using p by unfold_locales

interpretation pl: poly_mod "p^l".

lemma B2_2: "2 \<le> B2_LLL F" 
proof -
  from F0 have "\<parallel>F\<parallel>\<^sup>2 \<noteq> 0" by simp
  hence F1: "\<parallel>F\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of F] F0 by linarith  
  have "(2 :: int) = 2^1 * 1" by simp
  also have "\<dots> \<le> B2_LLL F" unfolding B2_LLL_def
    by (intro mult_mono power_increasing F1, insert N0, auto)  
  finally show "2 \<le> B2_LLL F" .
qed

lemma l_gt_0: "l > 0"
proof (cases l)
  case 0  
  have "1 * 2 \<le> 2 ^ N\<^sup>2 * B2_LLL F ^ (2 * N)" 
  proof (rule mult_mono)
    have "2 * 1 \<le> (2 :: int) * (2 ^ (2*N - 1))" by (rule mult_left_mono, auto) 
    also have "\<dots> = 2 ^ (2 * N)" using N0 by (cases N, auto)
    also have "\<dots> \<le> B2_LLL F ^ (2 * N)" 
      by (rule power_mono[OF B2_2], force)
    finally show "2 \<le> B2_LLL F ^ (2 * N)" by simp
  qed auto
  also have "\<dots> \<le> 1" using bound_l[unfolded 0] by auto 
  finally show ?thesis by auto
qed auto

lemma l0: "l \<noteq> 0" using l_gt_0 by auto

lemma pl_not0: "p ^ l \<noteq> 0" using p1 l0 by auto

interpretation pl: poly_mod_2 "p^l" 
  by (standard, insert p1 l0, auto)

private lemmas pl_dvdm_imp_p_dvdm = p.pl_dvdm_imp_p_dvdm[OF l0]

lemma p_Mp_pl_Mp[simp]: "p.Mp (pl.Mp k) = p.Mp k" 
  using Mp_Mp_pow_is_Mp[OF l0 p.m1] .

context
  fixes u :: "int poly"
    and d and f and n
    and gs :: "int poly list" 
    and Degs :: "nat set" 
  defines [simp]: "d \<equiv> degree u"
  assumes d0: "d > 0"
      and u: "monic u"
      and irred_u: "p.irreducible_m u"
      and u_f: "p.dvdm u f"
      and f_dvd_F: "f dvd F"
      and [simp]: "n == degree f"
      and f_gs: "pl.unique_factorization_m f (lead_coeff f, mset gs)" 
      and cop: "coprime (lead_coeff f) p" 
      and sf: "p.square_free_m f"
      and sf_F: "square_free f" 
      and u_gs: "u \<in> set gs" 
      and norm_gs: "map pl.Mp gs = gs" 
      and Degs: "\<And> factor. factor dvd f \<Longrightarrow> p.dvdm u factor \<Longrightarrow> degree factor \<in> Degs" 
begin
interpretation pl: poly_mod_2 "p^l" using l0 p1 by (unfold_locales, auto)

private lemma f0: "f \<noteq> 0" using sf_F unfolding square_free_def by fastforce

private lemma Mpf0: "pl.Mp f \<noteq> 0"
  by (metis p.square_free_m_def p_Mp_pl_Mp sf)

private lemma pMpf0: "p.Mp f \<noteq> 0"
  using p.square_free_m_def sf by auto

private lemma dn: "d \<le> n" using p.dvdm_imp_degree_le[OF u_f u pMpf0 p1] by auto

private lemma n0: "n > 0" using d0 dn by auto

private lemma B2_0[intro!]: "B2_LLL F > 0" using B2_2 by auto
private lemma deg_u: "degree u > 0" using d0 d_def by auto

private lemma n_le_N: "n\<le>N" by (simp add: dvd_imp_degree_le[OF f_dvd_F F0])

lemma dvdm_power: assumes "g dvd f" 
  shows "p.dvdm u g \<longleftrightarrow> pl.dvdm u g"
proof 
  assume "pl.dvdm u g" 
  thus "p.dvdm u g" by (rule pl_dvdm_imp_p_dvdm)
next
  assume dvd: "p.dvdm u g"
  from norm_gs have norm_gsp: "\<And> f. f \<in> set gs \<Longrightarrow> pl.Mp f = f" by (induct gs, auto)
  with f_gs[unfolded pl.unique_factorization_m_alt_def pl.factorization_m_def split] 
  have gs_irred_mon: "\<And> f. f \<in># mset gs \<Longrightarrow> pl.irreducible\<^sub>d_m f \<and> monic f" by auto   
  from norm_gs have norm_gs: "image_mset pl.Mp (mset gs) = mset gs" by (induct gs, auto) 
  from assms obtain h where f: "f = g * h" unfolding dvd_def by auto
  from pl.unique_factorization_m_factor[OF p.prime f_gs[unfolded f] _ _ l0 refl, folded f, 
      OF cop sf, unfolded pl.Mf_def split] norm_gs
  obtain hs fs where uf: "pl.unique_factorization_m h (lead_coeff h, hs)" 
      "pl.unique_factorization_m g (lead_coeff g, fs)" 
     and id: "mset gs = fs + hs" 
     and norm: "image_mset pl.Mp fs = fs" "image_mset pl.Mp hs = hs" by auto
  from p.square_free_m_prod_imp_coprime_m[OF sf[unfolded f]] 
  have cop_h_f: "p.coprime_m g h" by auto  
  show "pl.dvdm u g"
  proof (cases "u \<in># fs")
    case True
    hence "pl.Mp u \<in># image_mset pl.Mp fs" by auto
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf(2)] this]
    show ?thesis .
  next
    case False
    from u_gs have "u \<in># mset gs" by auto
    from this[unfolded id] False have "u \<in># hs" by auto
    hence "pl.Mp u \<in># image_mset pl.Mp hs" by auto
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf(1)] this]
    have "pl.dvdm u h" by auto
    from pl_dvdm_imp_p_dvdm[OF this] 
    have "p.dvdm u h" by auto
    from cop_h_f[unfolded p.coprime_m_def, rule_format, OF dvd this]
    have "p.dvdm u 1" .
    from p.dvdm_imp_degree_le[OF this u _ p.m1] have "degree u = 0" by auto
    with deg_u show ?thesis by auto
  qed
qed

private lemma uf: "pl.dvdm u f" using dvdm_power[OF dvd_refl] u_f by simp

lemma exists_reconstruction: "\<exists>h0. irreducible\<^sub>d h0 \<and> p.dvdm u h0 \<and> h0 dvd f"
proof -   
  have deg_f: "degree f > 0" using \<open>n \<equiv> degree f\<close> n0 by blast
  from berlekamp_zassenhaus_factorization_irreducible\<^sub>d[OF refl sf_F deg_f]
  obtain fs where f_fs: "f = prod_list fs"
    and c: "(\<forall>fi\<in>set fs. irreducible\<^sub>d fi \<and> 0 < degree fi )" by blast 
  have "pl.dvdm u (prod_list fs)" using uf f_fs by simp
  hence "p.dvdm u (prod_list fs)" by (rule pl_dvdm_imp_p_dvdm)
  from this obtain h0 where h0: "h0 \<in> set fs" and dvdm_u_h0: "p.dvdm u h0" 
    using p.irreducible_m_dvdm_prod_list[OF irred_u] by auto
  moreover have "h0 dvd f" by (unfold f_fs, rule prod_list_dvd[OF h0])  
  moreover have "irreducible\<^sub>d h0" using c h0 by auto
  ultimately show ?thesis by blast
qed

lemma factor_dvd_f_0: assumes "factor dvd f" 
  shows "pl.Mp factor \<noteq> 0"
proof -
  from assms obtain h where f: "f = factor * h" unfolding dvd_def ..
  from arg_cong[OF this, of pl.Mp] have "0 \<noteq> pl.Mp (pl.Mp factor * h)" 
    using Mpf0 by auto
  thus ?thesis by fastforce
qed

lemma degree_factor_ge_degree_u:
  assumes u_dvdm_factor: "p.dvdm u factor" 
    and factor_dvd: "factor dvd f" shows "degree u \<le> degree factor"
proof - 
  from factor_dvd_f_0[OF factor_dvd] have factor0: "pl.Mp factor \<noteq> 0" .  
  from u_dvdm_factor[unfolded dvdm_power[OF factor_dvd] pl.dvdm_def] obtain v where
    *: "pl.Mp factor = pl.Mp (u * pl.Mp v)" by auto
  with factor0 have v0: "pl.Mp v \<noteq> 0" by fastforce
  hence "0 \<noteq> lead_coeff (pl.Mp v)" by auto
  also have "lead_coeff (pl.Mp v) = pl.M (lead_coeff (pl.Mp v))" 
    by (auto simp: pl.Mp_def coeff_map_poly)
  finally have **: "lead_coeff (pl.Mp v) \<noteq> p ^ l * r" for r by (auto simp: pl.M_def) 
  from * have "degree factor \<ge> pl.degree_m (u * pl.Mp v)" using pl.degree_m_le[of factor] by auto
  also have "pl.degree_m (u * pl.Mp v) = degree (u * pl.Mp v)" 
    by (rule pl.degree_m_eq, unfold lead_coeff_mult, insert u pl.m1 **, auto)
  also have "\<dots> = degree u + degree (pl.Mp v)" 
    by (rule degree_mult_eq, insert v0 u, auto)
  finally show ?thesis by auto
qed

subsubsection \<open>Inner loop\<close>

context
  fixes j' :: nat
  assumes dj': "d \<le> j'"
      and j'n: "j' < n"
      and deg: "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> degree factor \<ge> j'"
begin

private abbreviation (input) "j \<equiv> Suc j'"

private lemma jn: "j \<le> n" using j'n by auto
    
private lemma factor_irreducible\<^sub>dI: assumes hf: "h dvd f" 
  and puh: "p.dvdm u h" 
  and degh: "degree h > 0" 
  and degh_j: "degree h \<le> j'"
shows "irreducible\<^sub>d h" 
proof -
  from dvdm_power[OF hf] puh have pluh: "pl.dvdm u h" by simp
  note uf_partition = p.unique_factorization_m_factor_partition[OF l0]
  obtain gs1 gs2 where part: "List.partition (\<lambda>gi. p.dvdm gi h) gs = (gs1, gs2)" by force
  from part u_gs puh 
  have u_gs1: "u \<in> set gs1" unfolding p by auto
  have gs1: "gs1 = filter (\<lambda> gi. p.dvdm gi h) gs" using part by auto
  obtain k where f: "f = h * k" using hf unfolding dvd_def by auto
  from uf_partition[OF f_gs f cop sf part] 
  have uf_h: "pl.unique_factorization_m h (lead_coeff h, mset gs1)" by auto
  show ?thesis
  proof (intro irreducible\<^sub>dI degh)
    fix q r
    assume deg_q: "degree q > 0" "degree q < degree h"
      and deg_r: "degree r > 0" "degree r < degree h"
      and h: "h = q * r"
    then have "r dvd h" by auto
    with h dvd_trans[OF _ hf] have 1: "q dvd f" "r dvd f" by auto
    from cop[unfolded f] have cop: "coprime (lead_coeff h) p"
      using p.prime pl.coprime_lead_coeff_factor(1) by blast
    from sf[unfolded f] have sf: "p.square_free_m h" using p.square_free_m_factor by metis
    have norm_gs1: "image_mset pl.Mp (mset gs1) = mset gs1" using norm_gs unfolding gs1
      by (induct gs, auto)
    from pl.unique_factorization_m_factor[OF p uf_h[unfolded h], folded h, OF cop sf l0 refl]
    obtain fs gs where uf_q: "pl.unique_factorization_m q (lead_coeff q, fs)"
     and uf_r: "pl.unique_factorization_m r (lead_coeff r, gs)"
     and id: "mset gs1 = fs + gs"
      unfolding pl.Mf_def split using norm_gs1 by auto
    from degh degh_j deg_q deg_r have qj': "degree q < j'" and rj': "degree r < j'" by auto
    have intro: "u \<in># r \<Longrightarrow> pl.Mp u \<in># image_mset pl.Mp r" for r by auto 
    note dvdI = pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization intro]
    from u_gs1 id have "u \<in># fs \<or> u \<in># gs" unfolding in_multiset_in_set[symmetric] by auto
    with dvdI[OF uf_q] dvdI[OF uf_r] have "pl.dvdm u q \<or> pl.dvdm u r" by auto
    hence "p.dvdm u q \<or> p.dvdm u r" using pl_dvdm_imp_p_dvdm by blast
    with 1 qj' rj' show False
      by (elim disjE, auto dest!: deg)
  qed
qed

private definition "ll = (let n = sqrt_int_ceiling (\<parallel>f\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (5 * j' * j')); 
    ll' = find_exponent p n in if ll' < l then ll' else l)" 

lemma ll: "ll \<le> l" unfolding ll_def Let_def by auto

lemma ll0: "ll \<noteq> 0" using l0 find_exponent[OF p.m1] 
  unfolding ll_def Let_def by auto

lemma pll1: "p^ll > 1" using ll0 p.m1 by auto

interpretation pll: poly_mod_2 "p^ll" 
  using ll0 p.m1 by (unfold_locales, auto) 

lemma pll0: "p^ll \<noteq> 0" using p by auto

lemma dvdm_l_ll: assumes "pl.dvdm a b"
  shows "pll.dvdm a b" 
proof -
  have id: "p^l = p^ll * p ^ (l - ll)" using ll unfolding power_add[symmetric] by auto
  from assms[unfolded pl.dvdm_def] obtain c where eq: "pl.eq_m b (a * c)" by blast
  from pll.Mp_shrink_modulus[OF eq[unfolded id]] p have "pll.eq_m b (a * c)" by auto
  thus ?thesis unfolding pll.dvdm_def ..
qed

private definition "g \<equiv> LLL_short_polynomial (p^ll) j u"

lemma deg_g_j: "degree g < j" 
    and g0: "g \<noteq> 0" 
    and ug :"pll.dvdm u g" 
    and short_g: "h \<noteq> 0 \<Longrightarrow> pll.dvdm u h \<Longrightarrow> degree h \<le> j' \<Longrightarrow> \<parallel>g\<parallel>\<^sup>2 \<le> 2 ^ j' * \<parallel>h\<parallel>\<^sup>2" 
proof (atomize(full), goal_cases)
  case 1
  from deg_u have degu0: "degree u \<noteq> 0" by auto
  have ju: "j \<ge> degree u" using d_def dj' le_Suc_eq by blast 
  have ju': "j > degree u" using d_def dj' by auto 
  note short = LLL_short_polynomial[OF degu0 ju pll1 u, folded g_def]
  from short(1-3) short(4)[OF ju'] show ?case by auto
qed

lemma LLL_reconstruction_inner_simps: "LLL_reconstruction_inner p l gs f u Degs j
  = (if j' \<notin> Degs then None else if p ^ ll \<le> \<bar>lead_coeff g\<bar> then None
   else case div_int_poly f (primitive_part g) of None \<Rightarrow> None
        | Some f' \<Rightarrow> Some ([gi\<leftarrow>gs . \<not> p.dvdm gi (primitive_part g)], lead_coeff f', f', primitive_part g))" 
proof -
  have Suc: "Suc j' - 1 = j'" by simp
  show ?thesis unfolding LLL_reconstruction_inner_def Suc Let_def ll_def[unfolded Let_def, symmetric]
     g_def[unfolded Let_def, symmetric] by simp
qed
  
lemma LLL_reconstruction_inner_complete:
  assumes ret: "LLL_reconstruction_inner p l gs f u Degs j = None"
  shows "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> degree factor \<ge> j"
proof (rule ccontr)
  fix factor
  assume pu_factor: "p.dvdm u factor"
     and factor_f: "factor dvd f"
     and deg_factor2: "\<not> j \<le> degree factor" 
  with deg[OF this(1,2)] have deg_factor_j [simp]: "degree factor = j'" and deg_factor_lt_j: "degree factor < j" by auto
  from Degs[OF factor_f pu_factor] have Degs: "(j' \<notin> Degs) = False" by auto
  from dvdm_power[OF factor_f] pu_factor have u_factor: "pl.dvdm u factor" by auto  
  from dvdm_l_ll[OF u_factor] have pll_u_factor: "pll.dvdm u factor" by auto
  have deg_factor: "degree factor > 0"
    using d0 deg_factor_j dj' by linarith 
  from f0 deg_factor divides_degree[OF factor_f] have deg_f: "degree f > 0" by auto
  from deg_factor have j'0: "j' > 0" by simp
  from factor_f f0 have factor0: "factor \<noteq> 0" by auto
  from factor_f obtain f2 where f: "f = factor * f2" unfolding dvd_def by auto
  from deg_u have deg_u0: "degree u \<noteq> 0" by auto
  from pu_factor u have u_j': "degree u \<le> j'" unfolding deg_factor_j[symmetric]
    using d_def deg_factor_j dj' by blast
  hence u_j: "degree u \<le> j" "degree u < j" by auto
  note LLL = LLL_short_polynomial[OF deg_u0 u_j(1) pll1 u, folded g_def]
  note ret = ret[unfolded LLL_reconstruction_inner_simps Degs if_False]   
  note LLL = LLL(1-3) LLL(4)[OF u_j(2) factor0 pll_u_factor deg_factor_lt_j]
  hence deg_g: "degree g \<le> j'" by simp
  from LLL(2) have normg: "\<parallel>g\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of g] by presburger
  from f0 have normf: "\<parallel>f\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of f] by presburger
  from factor0 have normf1: "\<parallel>factor\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of factor] by presburger
  from F0 have normF: "\<parallel>F\<parallel>\<^sup>2 \<ge> 1" using sq_norm_poly_pos[of F] by presburger
  from factor_f \<open>f dvd F\<close> have factor_F: "factor dvd F" by (rule dvd_trans)
  have "\<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree factor \<le> \<parallel>factor\<parallel>\<^sup>2 ^ j' * \<parallel>g\<parallel>\<^sup>2 ^ j'"
    by (rule mult_mono[OF power_increasing], insert normg normf1 deg_g, auto)
  also have "\<dots> = (\<parallel>factor\<parallel>\<^sup>2 * \<parallel>g\<parallel>\<^sup>2)^j'" by (simp add: power_mult_distrib)
  also have "\<dots> \<le> (\<parallel>factor\<parallel>\<^sup>2 * (2 ^ j' * \<parallel>factor\<parallel>\<^sup>2))^j'"
    by (rule power_mono[OF mult_left_mono], insert LLL(4), auto)
  also have "\<dots> = \<parallel>factor\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (j' * j')" 
    unfolding power_mult_distrib power_mult power_add mult_2 by simp
  finally have approx_part_1: "\<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree factor \<le> \<parallel>factor\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (j' * j')" .
  {
    fix f :: "int poly" 
    assume *: "factor dvd f" "f \<noteq> 0" 
    note approx_part_1
    also have "\<parallel>factor\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (j' * j') \<le> (2^(2*j') * \<parallel>f\<parallel>\<^sup>2) ^ (2 * j') * 2 ^ (j' * j')" 
      by (rule mult_right_mono[OF power_mono], insert sq_norm_factor_bound[OF *], auto)
    also have "\<dots> = \<parallel>f\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (2*j' * 2*j' + j' * j')" 
      unfolding power_mult_distrib power_add by (simp add: power_mult[symmetric])
    also have "2*j' * 2*j' + j' * j' = 5 * j' * j'" by simp
    finally have "\<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree factor \<le> \<parallel>f\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (5 * j' * j')" .
  } note approx = this
  note approx_1 = approx[OF factor_f f0]
  note approx_2_part = approx[OF factor_F F0]
  have large: "\<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree factor < (p^ll)\<^sup>2" 
  proof (cases "ll = l")
    case False
    let ?n = "\<parallel>f\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (5 * j' * j')" 
    have n: "?n \<ge> 0" by auto
    let ?s = "sqrt_int_ceiling ?n" 
    from False have "ll = find_exponent p ?s" unfolding ll_def Let_def by auto
    hence spll: "?s < p^ll" using find_exponent(1)[OF p.m1] by auto
    have "sqrt ?n \<ge> 0" by auto
    hence sqrt: "sqrt ?n > -1" by linarith    
    have ns: "?n \<le> ?s^2" using sqrt_int_ceiling_bound[OF n] .
    also have "\<dots> < (p^ll)^2" 
      by (rule power_strict_mono[OF spll], insert sqrt, auto)
    finally show ?thesis using approx_1 by auto
  next
    case True
    hence ll: "p^ll = p^l" by simp
    show ?thesis unfolding ll
    proof (rule less_le_trans[OF le_less_trans[OF approx_2_part] bound_l])
      have "\<parallel>F\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (5 * j' * j') 
          = 2 ^ (2 * j' * j' + 3 * j' * j') * \<parallel>F\<parallel>\<^sup>2 ^ (j' + j')" 
        unfolding mult_2 by simp 
      also have "\<dots> < 2 ^ (N\<^sup>2 + 4 * N*N) * \<parallel>F\<parallel>\<^sup>2 ^ (2 * N)" 
      proof (rule mult_less_le_imp_less[OF power_strict_increasing pow_mono_exp])
        show "1 \<le> \<parallel>F\<parallel>\<^sup>2" by (rule normF) 
        have jN': "j' < N" and jN: "j' \<le> N" using jn divides_degree[OF \<open>f dvd F\<close>] F0 by auto
        have "j' + j' \<le> j' + j'" using deg_g j'n by auto
        also have "\<dots> = 2 * j'" by auto
        also have "\<dots> \<le> 2 * N" using jN by auto
        finally show "j' + j' \<le> 2 * N" .
        show "0 < \<parallel>F\<parallel>\<^sup>2 ^ (j' + j')" 
          by (rule zero_less_power, insert normF, auto) 
        have "2 * j' * j' + 3 * j' * j' \<le> 2 * j' * j' + 3 * j' * j'" by auto
        also have "\<dots> = 5 * (j' * j')" by auto
        also have "\<dots> < 5 * (N * N)"
          by (rule mult_strict_left_mono[OF mult_strict_mono], insert jN', auto)
        also have "\<dots> = N\<^sup>2 + 4 * N * N" by (simp add: power2_eq_square) 
        finally show "2 * j' * j' + 3 * j' * j' < N\<^sup>2 + 4 * N * N" .
      qed auto
      also have "\<dots> = 2 ^ N\<^sup>2 * (2 ^ (2 * N) * \<parallel>F\<parallel>\<^sup>2) ^ (2 * N)"
        unfolding power_mult_distrib power_add by (simp add: power_mult[symmetric])
      finally show "\<parallel>F\<parallel>\<^sup>2 ^ (2 * j') * 2 ^ (5 * j' * j') < 2 ^ N\<^sup>2 * B2_LLL F ^ (2 * N)" 
        unfolding B2_LLL_def by simp
    qed
  qed
  have "(\<bar>lead_coeff g\<bar>)^2 < (p^ll)^2" 
  proof (rule le_less_trans[OF _ large])
    have "1 * (\<bar>lead_coeff g\<bar>\<^sup>2)^1 \<le> \<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree factor"
      by (rule mult_mono[OF _ order.trans[OF power_mono pow_mono_exp]], 
      insert normg normf1 deg_f g0 coeff_le_sq_norm[of g] j'0, 
      auto intro: pow_mono_one) 
    thus "\<bar>lead_coeff g\<bar>\<^sup>2 \<le> \<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree factor" by simp
  qed
  hence "(lead_coeff g)^2 < (p^ll)^2" by simp
  hence "\<bar>lead_coeff g\<bar> < p^ll" using p.m1 abs_le_square_iff[of "p^ll" "lead_coeff g"] by auto 
  hence "(p^ll \<le> \<bar>lead_coeff g\<bar>) = False" by auto
  note ret = ret[unfolded this if_False]
  have deg_f: "degree f > 0" using n0 by auto
  have deg_ug: "degree u \<le> degree g" 
  proof (rule pll.dvdm_degree[OF u LLL(3)], standard)
    assume "pll.Mp g = 0" 
    from arg_cong[OF this, of "\<lambda> p. coeff p (degree g)"]
    have "pll.M (coeff g (degree g)) = 0" by (auto simp: pll.Mp_def coeff_map_poly)
    from this[unfolded pll.M_def] obtain c where lg: "lead_coeff g = p^ll * c" by auto
    with LLL(2) have c0: "c \<noteq> 0" by auto
    hence "(p^ll)^2 \<le> (lead_coeff g)^2" unfolding lg abs_le_square_iff[symmetric]
      by (rule aux_abs_int)
    also have "\<dots> \<le> \<parallel>g\<parallel>\<^sup>2" using coeff_le_sq_norm[of g] by auto 
    also have "\<dots> = \<parallel>g\<parallel>\<^sup>2 ^ 1" by simp
    also have "\<dots> \<le> \<parallel>g\<parallel>\<^sup>2 ^ degree factor" 
      by (rule pow_mono_exp, insert deg_f normg j'0, auto)
    also have "\<dots> = 1 * \<dots>" by simp
    also have "\<dots> \<le> \<parallel>factor\<parallel>\<^sup>2 ^ degree g * \<parallel>g\<parallel>\<^sup>2 ^ degree factor" 
      by (rule mult_right_mono, insert normf1, auto)
    also have "\<dots> < (p^ll)\<^sup>2" by (rule large)
    finally show False by auto
  qed
  with deg_u have deg_g: "degree g > 0" by simp
  from j'0 have deg_factor: "degree factor > 0" by simp
  let ?g = "gcd factor g" 
  from common_factor_via_short[OF deg_factor deg_g u deg_u pll_u_factor LLL(3) large] pll.m1
  have gcd: "0 < degree ?g" by auto
  have gcd_factor: "?g dvd factor" by auto
  from dvd_trans[OF this factor_f] have gcd_f: "?g dvd f" .
  from deg_g have g0: "g \<noteq> 0" by auto
  have gcd_g: "degree ?g \<le> degree g" using g0 using divides_degree by blast
  from gcd_g LLL(1) have hj': "degree ?g \<le> j'" by auto
  let ?pp = "primitive_part g" 
  from ret have "div_int_poly f ?pp = None" by (auto split: option.splits)
  from div_int_poly[of f ?pp, unfolded this] g0 
  have ppf: "\<not> ?pp dvd f" unfolding dvd_def by (auto simp: ac_simps)
  have irr_f1: "irreducible\<^sub>d factor" 
    by (rule factor_irreducible\<^sub>dI[OF factor_f pu_factor deg_factor], simp)
  from gcd_factor obtain h where factor: "factor = ?g * h" unfolding dvd_def by auto
  from irreducible\<^sub>dD(2)[OF irr_f1, of ?g h, folded factor] have "\<not> (degree ?g < j' \<and> degree h < j')" 
    by auto
  moreover have "j' = degree ?g + degree h" using factor0 arg_cong[OF factor, of degree] 
    by (subst (asm) degree_mult_eq, insert j'0, auto)
  ultimately have "degree h = 0" using gcd by linarith
  from degree0_coeffs[OF this] factor factor0
  obtain c where h: "h = [:c:]" and c: "c \<noteq> 0" by fastforce
  from arg_cong[OF factor, of degree] have id: "degree ?g = degree factor" 
    unfolding h using c by auto
  moreover have "degree ?g \<le> degree g" 
    by (subst gcd.commute, rule degree_gcd1[OF g0])
  ultimately have "degree g \<ge> degree factor" by auto
  with id deg_factor2 deg_g_j have deg: "degree ?g = degree g" 
    and "degree g = degree factor" by auto
  have "?g dvd g" by auto
  then obtain q where g: "g = ?g * q" unfolding dvd_def by auto
  from arg_cong[OF this, of degree] deg
  have "degree q = 0" 
    by (subst (asm) degree_mult_eq, insert g g0, force, force) simp
  from degree0_coeffs[OF this] g g0
  obtain d where p: "q = [:d:]" and d: "d \<noteq> 0" by fastforce
  from arg_cong[OF factor, of "(*) q"] 
  have "q * factor = h * g"
    by (subst g, auto simp: ac_simps)
  hence "smult d factor = h * g" unfolding p h by auto
  hence "g dvd smult d factor" by simp
  from dvd_smult_int[OF d this]
  have "primitive_part g dvd factor" .
  from dvd_trans[OF this factor_f] ppf show False by auto
qed  

lemma LLL_reconstruction_inner_sound:
  assumes ret: "LLL_reconstruction_inner p l gs f u Degs j = Some (gs',b',f',h)" 
  shows "f = f' * h" (is "?g1")
    and "irreducible\<^sub>d h" (is "?g2")
    and "b' = lead_coeff f'" (is "?g3")
    and "pl.unique_factorization_m f' (lead_coeff f', mset gs')" (is "?g4")
    and "p.dvdm u h" (is ?g5)
    and "degree h = j'" (is ?g6)
    and "length gs' < length gs" (is ?g7)
    and "set gs' \<subseteq> set gs" (is ?g8)
    and "gs' \<noteq> []" (is ?g9) 
proof -
  let ?ppg = "primitive_part g" 
  note ret = ret[unfolded LLL_reconstruction_inner_simps]   
  from ret have lc: "abs (lead_coeff g) < p^ll" by (auto split: if_splits)
  from ret obtain rest where rest: "div_int_poly f (primitive_part g) = Some rest" 
    by (auto split: if_splits option.splits)
  from ret[unfolded this] div_int_then_rqp[OF this] lc
  have out [simp]: "h = ?ppg" "gs' = filter (\<lambda> gi. \<not> p.dvdm gi ?ppg) gs" 
    "f' = rest" "b' = lead_coeff rest"
   and f: "f = ?ppg * rest" by (auto split: if_splits)
  with div_int_then_rqp[OF rest] show ?g1 ?g3 by auto
  from \<open>?g1\<close> f0 have h0: "h \<noteq> 0" by auto
  let ?c = "content g" 
  from g0 have ct0: "?c \<noteq> 0" by auto
  have "\<bar>?c\<bar> \<le> \<bar>lead_coeff g\<bar>" by (rule content_le_lead_coeff)
  also have "\<dots> < p^ll" by fact
  finally have ct_pl: "\<bar>?c\<bar> < p^ll" .
  from ug have "pll.dvdm u (smult ?c ?ppg)" by simp
  from poly_mod_dvd_drop_smult[OF u p ct0 ct_pl this]
  show puh: "p.dvdm u h" by simp
  with dvdm_power[of h] f
  have uh: "pl.dvdm u h" by (auto simp: dvd_def)
  from f have hf: "h dvd f" by (auto intro:dvdI)
  have degh: "degree h > 0"
    by (metis d_def deg deg_u puh dj' hf le_neq_implies_less not_less0 neq0_conv)
  show irr_h: ?g2
    by (intro factor_irreducible\<^sub>dI degh hf puh, insert deg_g_j, simp)
  show deg_h: ?g6 using deg deg_g_j g_def hf le_less_Suc_eq puh degree_primitive_part by force
  show ?g7 unfolding out 
    by (rule length_filter_less[of u], insert pl_dvdm_imp_p_dvdm[OF uh] u_gs, auto)
  show ?g8 by auto
  from f out have fh: "f = h * f'" and gs': "gs' = [gi \<leftarrow> gs. \<not> p.dvdm gi h]" by auto
  note [simp del] = out
  let ?fs = "filter (\<lambda>gi. p.dvdm gi h) gs" 
  have part: "List.partition (\<lambda>gi. p.dvdm gi h) gs = (?fs, gs')" 
    unfolding gs' by (auto simp: o_def)
  from p.unique_factorization_m_factor_partition[OF l0 f_gs fh cop sf part]
  show uf: "pl.unique_factorization_m f' (lead_coeff f', mset gs')" by auto
  show ?g9
  proof
    assume "gs' = []" 
    with pl.unique_factorization_m_imp_factorization[OF uf, unfolded pl.factorization_m_def]
    have "pl.Mp f' = pl.Mp (smult (lead_coeff f') 1)" by auto
    from arg_cong[OF this, of degree] pl.degree_m_le[of "smult (lead_coeff f') 1"] 
    have "pl.degree_m f' = 0" by simp 
    also have "pl.degree_m f' = degree f'" 
    proof (rule poly_mod.degree_m_eq[OF _ pl.m1])
      have "coprime (lead_coeff f') p" 
        by (rule  p.coprime_lead_coeff_factor[OF p.prime cop[unfolded fh]])
      thus "lead_coeff f' mod p ^ l \<noteq> 0" using l0 p.prime by fastforce
    qed
    finally have degf': "degree f' = 0" by auto
    from degree0_coeffs[OF this] f0 fh obtain c where "f' = [:c:]" and c: "c \<noteq> 0" and fch: "f = smult c h"
      by auto
    from \<open>irreducible\<^sub>d h\<close> have irr_f: "irreducible\<^sub>d f" 
      using irreducible\<^sub>d_smult_int[OF c, of h] unfolding fch by auto
    have "degree f = j'" using hf irr_h deg_h
      using irr_f \<open>n \<equiv> degree f\<close> degh j'n
      by (metis add.right_neutral degf' degree_mult_eq f0 fh mult_not_zero)
    thus "False" using j'n by auto    
  qed
qed
end
  
interpretation LLL d .

lemma LLL_reconstruction_inner_None_upt_j':
  assumes ij: "\<forall>i\<in>{d+1..j}. LLL_reconstruction_inner p l gs f u Degs i = None" 
    and dj: "d<j" and "j\<le>n"
  shows "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> degree factor \<ge> j"
  using assms
proof (induct j)
  case (Suc j)
  show ?case 
  proof (rule LLL_reconstruction_inner_complete)
    show "\<And>factor2. p.dvdm u factor2 \<Longrightarrow> factor2 dvd f \<Longrightarrow> j \<le> degree factor2"
    proof (cases "d = j")
       case False
       show "\<And>factor2. p.dvdm u factor2 \<Longrightarrow> factor2 dvd f \<Longrightarrow> j \<le> degree factor2"
         by (rule Suc.hyps, insert Suc.prems False, auto)
     next
       case True
       then show "\<And>factor2. p.dvdm u factor2 \<Longrightarrow> factor2 dvd f \<Longrightarrow> j \<le> degree factor2"
         using degree_factor_ge_degree_u by auto
    qed
  qed (insert Suc.prems, auto)
qed auto

corollary LLL_reconstruction_inner_None_upt_j:
  assumes ij: "\<forall>i\<in>{d+1..j}. LLL_reconstruction_inner p l gs f u Degs i = None" 
    and dj: "d\<le>j" and jn: "j\<le>n"
  shows "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> degree factor \<ge> j"
proof (cases "d=j")
  case True
  then show "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> d = j \<Longrightarrow> j \<le> degree factor" 
    using degree_factor_ge_degree_u by auto 
next
  case False
  hence dj2: "d<j" using dj by auto
  then show "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> d \<noteq> j \<Longrightarrow> j \<le> degree factor" 
    using LLL_reconstruction_inner_None_upt_j'[OF ij dj2 jn] by auto
qed

lemma LLL_reconstruction_inner_all_None_imp_irreducible:
  assumes i: "\<forall>i\<in>{d+1..n}. LLL_reconstruction_inner p l gs f u Degs i = None"
  shows "irreducible\<^sub>d f" 
proof - 
  obtain factor 
    where irreducible_factor: "irreducible\<^sub>d factor" 
      and dvdp_u_factor: "p.dvdm u factor" and factor_dvd_f: "factor dvd f"
    using exists_reconstruction by blast
  have f0: "f \<noteq> 0" using n0 by auto
  have deg_factor1: "degree u \<le> degree factor" 
    by (rule degree_factor_ge_degree_u[OF dvdp_u_factor factor_dvd_f])
  hence factor_not0: "factor \<noteq> 0" using d0 by auto
  hence deg_factor2: "degree factor \<le> degree f" using divides_degree[OF factor_dvd_f] f0 by auto
  let ?j = "degree factor"  
  show ?thesis
  proof (cases "degree factor = degree f")
    case True
    from factor_dvd_f obtain g where f_factor: "f = factor * g" unfolding dvd_def by auto
    from True[unfolded f_factor] f0[unfolded f_factor] have "degree g = 0" "g \<noteq> 0" 
      by (subst (asm) degree_mult_eq, auto)
    from degree0_coeffs[OF this(1)] this(2) obtain c where "g = [:c:]" and c: "c \<noteq> 0" by auto
    with f_factor have fc: "f = smult c factor" by auto
    from irreducible_factor irreducible\<^sub>d_smult_int[OF c, of factor, folded fc]
    show ?thesis by simp
  next
    case False
    hence Suc_j: "Suc ?j \<le> degree f" using deg_factor2 by auto
    have "Suc ?j \<le> degree factor"
    proof (rule LLL_reconstruction_inner_None_upt_j[OF _ _ _ dvdp_u_factor factor_dvd_f])
      show "d \<le> Suc ?j" using deg_factor1 by auto
      show "\<forall>i\<in>{d + 1..(Suc ?j)}. LLL_reconstruction_inner p l gs f u Degs i = None"
        using Suc_j i by auto
      show "Suc ?j \<le> n" using Suc_j by simp
    qed
    then show ?thesis by auto
  qed
qed

lemma irreducible_imp_LLL_reconstruction_inner_all_None:
  assumes irr_f: "irreducible\<^sub>d f"
  shows "\<forall>i\<in>{d+1..n}. LLL_reconstruction_inner p l gs f u Degs i = None"   
proof (rule ccontr)
  let ?LLL_inner = "\<lambda>i. LLL_reconstruction_inner p l gs f u Degs i"
  let ?G ="{j. j \<in> {d + 1..n} \<and> ?LLL_inner j \<noteq> None}"
  assume "\<not> (\<forall>i\<in>{d + 1..n}. ?LLL_inner i = None)"
  hence G_not_empty: "?G \<noteq> {}" by auto
  define j where "j = Min ?G"
  have j_in_G: "j \<in> ?G" by (unfold j_def, rule Min_in[OF _ G_not_empty], simp)
  hence j: "j \<in> {d + 1..n}" and LLL_not_None: "?LLL_inner j \<noteq> None" using j_in_G by auto
  have "\<forall>i\<in>{d+1..<j}. ?LLL_inner i = None"
  proof (rule ccontr)
    assume "\<not> (\<forall>i\<in>{d + 1..<j}. ?LLL_inner i = None)"
    from this obtain i where i: "i \<in> {d + 1..<j}" and LLL_i: "?LLL_inner i \<noteq> None" by auto
    hence iG: "i \<in> ?G" using j_def G_not_empty by auto
    have "i<j" using i by auto
    moreover have "j\<le>i" using iG j_def by auto
    ultimately show False by linarith    
  qed
  hence all_None: "\<forall>i\<in>{d+1..j-1}. ?LLL_inner i = None" by auto
  obtain gs' b' f' factor where LLL_inner_eq: "?LLL_inner j = Some (gs', b', f', factor)" 
    using LLL_not_None by force
  have Suc_j1_eq: "Suc (j - 1) = j" using j d0 by auto
  have jn: "j - 1 < n"  using j by auto
  have dj: "d \<le> j-1" using j d0 by auto
  have degree: "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> j - 1 \<le> degree factor" 
    by (rule LLL_reconstruction_inner_None_upt_j[OF all_None dj], insert jn, auto)  
  have LLL_inner_Some: "?LLL_inner (Suc (j - 1)) = Some (gs', b', f', factor)" 
    using LLL_inner_eq Suc_j1_eq by auto  
  have deg_factor: "degree factor = j-1" 
    and ff': "f = f' * factor"
    and irreducible_factor: "irreducible\<^sub>d factor"
    using LLL_reconstruction_inner_sound[OF dj jn degree LLL_inner_Some] by (metis+)
  have "degree f' = n - (j - 1)"  using arg_cong[OF ff', of degree]
    by (subst (asm) degree_mult_eq, insert f0 ff' deg_factor, auto)
  also have "\<dots> < n" using irreducible_factor jn unfolding irreducible\<^sub>d_def deg_factor by auto
  finally have deg_f': "degree f' < degree f" by auto
  from ff' have factor_dvd_f: "factor dvd f" by auto
  have "\<not> irreducible\<^sub>d f" 
    by (rule reducible\<^sub>dI, rule exI[of _ f'], rule exI[of _ factor], 
        intro conjI ff', insert deg_factor jn deg_f', auto)
  thus False using irr_f by contradiction  
qed

lemma LLL_reconstruction_inner_all_None:
  assumes i: "\<forall>i\<in>{d+1..n}. LLL_reconstruction_inner p l gs f u Degs i = None"
  and dj: "d<j"
shows "LLL_reconstruction_inner_loop p l gs f u Degs j = ([],1,1,f)"
  using dj                             
proof (induct j rule: LLL_reconstruction_inner_loop.induct[of f p l gs u Degs])
  case (1 j)
  let ?innerl = "LLL_reconstruction_inner_loop p l gs f u Degs" 
  let ?inner = "LLL_reconstruction_inner p l gs f u Degs" 
  note hyp = "1.hyps"
  note dj = "1.prems"(1)
  show ?case 
  proof (cases "j\<le>n")
    case True note jn = True
    have step: "?inner j = None"
      by (cases "d=j", insert  i jn dj, auto)     
    have "?innerl j = ?innerl (j+1)" 
      using jn step by auto
    also have "... = ([], 1, 1, f)"
      by (rule hyp[OF _ step], insert jn dj, auto simp add: jn dj)      
    finally show ?thesis .
  qed auto
qed

corollary irreducible_imp_LLL_reconstruction_inner_loop_f:
  assumes irr_f: "irreducible\<^sub>d f" and dj: "d<j" 
shows "LLL_reconstruction_inner_loop p l gs f u Degs j = ([],1,1,f)"
  using irreducible_imp_LLL_reconstruction_inner_all_None[OF irr_f]
  using LLL_reconstruction_inner_all_None[OF _ dj] by auto
  
lemma exists_index_LLL_reconstruction_inner_Some:
  assumes inner_loop: "LLL_reconstruction_inner_loop p l gs f u Degs j = (gs',b',f',factor)"
    and i: "\<forall>i\<in>{d+1..<j}. LLL_reconstruction_inner p l gs f u Degs i = None"
    and dj: "d<j" and jn: "j\<le>n" and f: "\<not> irreducible\<^sub>d f"
  shows "\<exists>j'. j \<le> j' \<and> j'\<le>n \<and> d<j'
    \<and> (LLL_reconstruction_inner p l gs f u Degs j' = Some (gs', b', f', factor))
    \<and> (\<forall>i\<in>{d+1..<j'}. LLL_reconstruction_inner p l gs f u Degs i = None)"
  using inner_loop i dj jn
proof (induct j rule: LLL_reconstruction_inner_loop.induct[of f p l gs u Degs])
  case (1 j)
  let ?innerl = "LLL_reconstruction_inner_loop p l gs f u Degs" 
  let ?inner = "LLL_reconstruction_inner p l gs f u Degs" 
  note hyp = "1.hyps"  
  note 1 = "1.prems"(1)
  note 2 = "1.prems"(2)
  note dj = "1.prems"(3)
  note jn = "1.prems"(4)
  show ?case
  proof (cases "?inner j = None")
    case True
    show ?thesis
    proof (cases "j=n")
      case True note j_eq_n = True
      show ?thesis
      proof (cases "?inner n = None")
        case True
        have i2: "\<forall>i\<in>{d + 1..n}. ?inner i = None" 
          using 2 j_eq_n True by auto
        have "irreducible\<^sub>d f"
          by(rule LLL_reconstruction_inner_all_None_imp_irreducible[OF i2])
        thus ?thesis using f by simp
      next
        case False
        have "?inner n = Some (gs', b', f', factor)" 
          using False 1 j_eq_n by auto
        moreover have "\<forall>i\<in>{d + 1..<n}. ?inner i = None" 
          using 2 j_eq_n by simp
        moreover have "d < n" using 1 2 jn j_eq_n
          using False  dn nat_less_le
          using d_def dj by auto
        ultimately show ?thesis using j_eq_n by fastforce
      qed    
    next
      case False
      have "\<exists>j'\<ge>j + 1. j' \<le> n \<and> d < j' \<and>
                 ?inner j' = Some (gs', b', f', factor) \<and>
                 (\<forall>i\<in>{d + 1..<j'}. ?inner i = None)"
      proof (rule hyp)
        show "\<not> degree f < j" using jn by auto
        show "?inner j = None" using True by auto
        show "?innerl (j + 1) = (gs', b', f', factor)" 
          using 1 True jn by auto
        show "\<forall>i\<in>{d + 1..<j + 1}. ?inner i = None"        
          by (metis "2" One_nat_def True add.comm_neutral add_Suc_right atLeastLessThan_iff 
              le_neq_implies_less less_Suc_eq_le)      
        show "d < j + 1" using dj by auto
        show " j + 1 \<le> n" using jn False by auto
      qed
      from this obtain j' where a1: "j'\<ge>j + 1" and a2: "j' \<le> n" and a3: "d < j'"
        and a4: "?inner j' = Some (gs', b', f', factor)"
        and a5: "(\<forall>i\<in>{d + 1..<j'}. ?inner i = None)" by auto
      moreover have "j'\<ge>j" using a1 by auto
      ultimately show ?thesis by fastforce
    qed
  next
    case False    
    have 1: "?inner j = Some (gs', b', f', factor)" 
      using False 1 jn by auto
    moreover have 2: "(\<forall>i\<in>{d + 1..<j}. ?inner i = None)" 
      by (rule 2)
    moreover have 3: "j \<le> n" using jn by auto
    moreover have 4: "d < j" using 2 False dj jn
      using le_neq_implies_less by fastforce
    ultimately show ?thesis by auto
  qed
qed  

(* TODO: move *)
lemma unique_factorization_m_1: "pl.unique_factorization_m 1 (1, {#})"
proof (intro pl.unique_factorization_mI)
  fix d gs
  assume pl: "pl.factorization_m 1 (d,gs)" 
  from pl.factorization_m_degree[OF this] have deg0: "\<And> g. g \<in># gs \<Longrightarrow> pl.degree_m g = 0" by auto
  {
    assume "gs \<noteq> {#}" 
    then obtain g hs where gs: "gs = {# g #} + hs" by (cases gs, auto)
    with pl have *: "pl.irreducible\<^sub>d_m (pl.Mp g)" 
      "monic (pl.Mp g)" by (auto simp: pl.factorization_m_def)
    with deg0[of g, unfolded gs] have False by (auto simp: pl.irreducible\<^sub>d_m_def)
  }
  hence "gs = {#}" by auto
  with pl show "pl.Mf (d, gs) = pl.Mf (1, {#})" by (cases "d = 0", 
    auto simp: pl.factorization_m_def pl.Mf_def pl.Mp_def)
qed (auto simp: pl.factorization_m_def)

lemma LLL_reconstruction_inner_loop_j_le_n:
  assumes ret: "LLL_reconstruction_inner_loop p l gs f u Degs j = (gs',b',f',factor)"
    and ij: "\<forall>i\<in>{d+1..<j}. LLL_reconstruction_inner p l gs f u Degs i = None"
    and n: "n = degree f"
    and jn: "j \<le> n"
    and dj: "d < j"
  shows "f = f' * factor" (is "?g1")
    and "irreducible\<^sub>d factor" (is "?g2")
    and "b' = lead_coeff f'" (is "?g3")
    and "pl.unique_factorization_m f' (b', mset gs')" (is "?g4")
    and "p.dvdm u factor" (is ?g5)
    and "gs \<noteq> [] \<longrightarrow> length gs' < length gs" (is ?g6)
    and "factor dvd f" (is ?g7)
    and "f' dvd f" (is ?g8)
    and "set gs' \<subseteq> set gs" (is ?g9)
    and "gs' = [] \<longrightarrow> f' = 1" (is ?g10)
  using ret ij jn dj
proof (atomize(full), induct j)
  case 0
  then show ?case using deg_u by auto
next
  case (Suc j)
  let ?innerl = "LLL_reconstruction_inner_loop p l gs f u Degs" 
  let ?inner = "LLL_reconstruction_inner p l gs f u Degs" 
  have ij: "\<forall>i\<in>{d+1..j}. ?inner i = None" 
    using Suc.prems by auto  
  have dj: "d \<le> j" using Suc.prems by auto
  have jn: "j<n" using Suc.prems by auto
  have deg: "Suc j \<le> degree f" using Suc.prems by auto
  have c: "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> j \<le> degree factor" 
    by (rule LLL_reconstruction_inner_None_upt_j[OF ij dj], insert n jn, auto)
  have 1: "?innerl (Suc j) = (gs', b', f', factor)"
    using Suc.prems by auto
  show ?case
  proof (cases "?inner (Suc j) = None")
    case False
    have LLL_rw: "?inner (Suc j) = Some (gs', b', f', factor)"
      using False deg Suc.prems by auto
    show ?thesis using LLL_reconstruction_inner_sound[OF dj jn c LLL_rw] by fastforce
  next    
    case True note Suc_j_None = True
    show ?thesis
    proof (cases "d = j")
      case False
      have nj: "j \<le> degree f" using Suc.prems False by auto
      moreover have dj2: "d < j" using Suc.prems False by auto
      ultimately show ?thesis using Suc.prems Suc.hyps by fastforce
    next
      case True note d_eq_j = True
      show ?thesis
      proof (cases "irreducible\<^sub>d f")
        case True
        have pl_Mp_1: "pl.Mp 1 = 1" by auto
        have d_Suc_j: "d < Suc j" using Suc.prems by auto
        have "?innerl (Suc j) = ([],1,1,f)" 
          by (rule irreducible_imp_LLL_reconstruction_inner_loop_f[OF True d_Suc_j])
        hence result_eq: "([],1,1,f) = (gs', b', f', factor)" using Suc.prems by auto
        moreover have thesis1: "p.dvdm u factor" using u_f result_eq by auto
        moreover have thesis2: "f' = pl.Mp (Polynomial.smult b' (prod_list gs'))" 
          using result_eq pl_Mp_1 by auto
        ultimately show ?thesis using True by (auto simp: unique_factorization_m_1)
      next
        case False note irreducible_f = False
        have "\<exists>j'. Suc j \<le> j' \<and> j'\<le>n \<and> d<j'
        \<and> (?inner j' = Some (gs', b', f', factor))
        \<and> (\<forall>i\<in>{d+1..<j'}. ?inner i = None)"
        proof (rule exists_index_LLL_reconstruction_inner_Some[OF _ _ _ _ False])        
          show "?innerl (Suc j) = (gs', b', f', factor)" 
            using Suc.prems by auto       
          show "\<forall>i \<in> {d + 1..<Suc j}. ?inner i = None" 
            using Suc.prems by auto
          show "Suc j \<le> n" using jn by auto
          show "d < Suc j " using Suc.prems by auto
        qed
        from this obtain a where da: "d < a" and an: "a \<le> n" and ja: "j \<le> a"
          and a1: "?inner a = Some (gs', b', f', factor)"
          and a2: "\<forall>i\<in>{d+1..<a}. ?inner i = None" by auto
        define j' where j'[simp]: "j'\<equiv>a-1"
        have dj': "d \<le> j'" using da by auto
        have j': "j' \<noteq> 0" using dj' d0 by auto
        hence j'n: "j' < n" using an by auto
        have LLL: "?inner (Suc j') = Some (gs', b', f', factor)" 
          using a1 j' by auto
        have prev_None: "\<forall>i\<in>{d+1..j'}. ?inner i = None" 
          using a2 j' by auto
        have Suc_rw: "Suc (j'- 1) = j'" using j' by auto
        have c: "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> Suc (j' - 1) \<le> degree factor"        
          by (rule LLL_reconstruction_inner_None_upt_j, insert dj' Suc_rw j'n prev_None, auto)
        hence c2: "\<And>factor. p.dvdm u factor \<Longrightarrow> factor dvd f \<Longrightarrow> j' \<le> degree factor"
          using j' by force
        show ?thesis using LLL_reconstruction_inner_sound[OF dj' j'n c2 LLL] by fastforce
      qed
    qed
  qed
qed

lemma LLL_reconstruction_inner_loop_j_ge_n:
  assumes ret: "LLL_reconstruction_inner_loop p l gs f u Degs j = (gs',b',f',factor)"
    and ij: "\<forall>i\<in>{d+1..n}. LLL_reconstruction_inner p l gs f u Degs i = None"
    and dj: "d < j"
    and jn: "j>n"
  shows "f = f' * factor" (is "?g1")
    and "irreducible\<^sub>d factor" (is "?g2")
    and "b' = lead_coeff f'" (is "?g3")
    and "pl.unique_factorization_m f' (b', mset gs')" (is "?g4") 
    and "p.dvdm u factor" (is ?g5)
    and "gs \<noteq> [] \<longrightarrow> length gs' < length gs" (is ?g6)
    and "factor dvd f" (is ?g7)
    and "f' dvd f" (is ?g8)
    and "set gs' \<subseteq> set gs" (is ?g9)
    and "f' = 1" (is ?g10)
proof -
  have "LLL_reconstruction_inner_loop p l gs f u Degs j = ([],1,1,f)" using jn by auto
  hence gs': "gs'=[]" and b': "b'=1" and f': "f' = 1" and factor: "factor = f" using ret by auto
  have "irreducible\<^sub>d f"
    by (rule LLL_reconstruction_inner_all_None_imp_irreducible[OF ij])
  thus ?g1 ?g2 ?g3 ?g4 ?g5 ?g6 ?g7 ?g8 ?g9 ?g10 using f' factor b' gs' u_f 
    by (auto simp: unique_factorization_m_1)
qed

lemma LLL_reconstruction_inner_loop:
  assumes ret: "LLL_reconstruction_inner_loop p l gs f u Degs j = (gs',b',f',factor)"
    and ij: "\<forall>i\<in>{d+1..<j}. LLL_reconstruction_inner p l gs f u Degs i = None"
    and n: "n = degree f"
    and dj: "d < j"
  shows "f = f' * factor" (is "?g1")
    and "irreducible\<^sub>d factor" (is "?g2")
    and "b' = lead_coeff f'" (is "?g3")
    and "pl.unique_factorization_m f' (b', mset gs')" (is "?g4") 
    and "p.dvdm u factor" (is ?g5)
    and "gs \<noteq> [] \<longrightarrow> length gs' < length gs" (is ?g6)
    and "factor dvd f" (is ?g7)
    and "f' dvd f" (is ?g8)
    and "set gs' \<subseteq> set gs" (is ?g9)
    and "gs' = [] \<longrightarrow> f' = 1" (is ?g10)
proof (atomize(full),(cases "j>n"; intro conjI))
  case True
  have ij2: "\<forall>i\<in>{d + 1..n}. LLL_reconstruction_inner p l gs f u Degs i = None" 
    using ij True by auto
  show ?g1 ?g2 ?g3 ?g4 ?g5 ?g6 ?g7 ?g8 ?g9 ?g10
    using LLL_reconstruction_inner_loop_j_ge_n[OF ret ij2 dj True] by blast+
next
  case False
  hence jn: "j\<le>n" by simp
  show ?g1 ?g2 ?g3 ?g4 ?g5 ?g6 ?g7 ?g8 ?g9 ?g10
    using LLL_reconstruction_inner_loop_j_le_n[OF ret ij n jn dj] by blast+
qed
end

subsubsection \<open>Outer loop\<close>

lemma LLL_reconstruction'':
  assumes 1: "LLL_reconstruction'' p l gs b f G = G'"
    and irreducible_G: "\<And>factor. factor \<in> set G \<Longrightarrow> irreducible\<^sub>d factor" 
    and 3: "F = f * prod_list G"
    and 4: "pl.unique_factorization_m f (lead_coeff f, mset gs)"
    and 5: "gs \<noteq> []"
    and 6: "\<And> gi. gi \<in> set gs \<Longrightarrow> pl.Mp gi = gi"
    and 7: "\<And> gi. gi \<in> set gs \<Longrightarrow> p.irreducible\<^sub>d_m gi" 
    and 8: "p.square_free_m f" 
    and 9: "coprime (lead_coeff f) p" 
    and sf_F: "square_free F" 
  shows "(\<forall>g \<in> set G'. irreducible\<^sub>d g) \<and> F = prod_list G'"
  using 1 irreducible_G 3 4 5 6 7 8 9
proof (induction gs arbitrary: b f G G' rule: length_induct)
  case (1 gs)  
  note LLL_f' = "1.prems"(1)  
  note irreducible_G = "1.prems"(2)
  note F_f_G = "1.prems" (3)
  note f_gs_factor = "1.prems" (4)
  note gs_not_empty = "1.prems" (5)
  note norm = "1.prems"(6)
  note irred_p = "1.prems"(7)
  note sf = "1.prems"(8)
  note cop = "1.prems"(9)
  obtain u where choose_u_result: "choose_u gs = u" by auto
  from choose_u_member[OF  gs_not_empty, unfolded choose_u_result]
  have u_gs: "u \<in> set gs" by auto
  define d n where [simp]: "d = degree u" "n = degree f"
  hence n_def: "n = degree f" "n \<equiv> degree f" by auto
  define gs'' where "gs'' = remove1 u gs" 
  define degs where "degs = map degree gs''" 
  define Degs where "Degs = (+) d ` sub_mset_sums degs" 
  obtain gs' b' h factor where inner_loop_result: 
    "LLL_reconstruction_inner_loop p l gs f u Degs (d+1) = (gs',b',h,factor)"
    by (metis prod_cases4)
  have a1: 
    "LLL_reconstruction_inner_loop p l gs f u Degs (d+1) = (gs', b', h, factor)" 
    using inner_loop_result by auto
  have a2: 
    "\<forall>i\<in>{degree u + 1..<(d+1)}. LLL_reconstruction_inner p l gs f u Degs i = None"
    by auto
  have "LLL_reconstruction'' p l gs b f G = LLL_reconstruction'' p l gs' b' h (factor # G)" 
    unfolding LLL_reconstruction''.simps[of p l gs] using gs_not_empty
    unfolding Let_def using choose_u_result inner_loop_result unfolding Degs_def degs_def gs''_def by auto
  hence LLL_eq: "LLL_reconstruction'' p l gs' b' h (factor # G) = G'" using LLL_f' by auto
  from pl.unique_factorization_m_imp_factorization[OF f_gs_factor, 
    unfolded pl.factorization_m_def] norm
  have f_gs: "pl.eq_m f (smult (lead_coeff f) (prod_mset (mset gs)))" and 
    mon: "g \<in> set gs \<Longrightarrow> monic g" and irred: "g \<in> set gs \<Longrightarrow> pl.irreducible\<^sub>d_m g" for g by auto
  {
    from split_list[OF u_gs] obtain gs1 gs2 where gs: "gs = gs1 @ u # gs2" by auto
    from f_gs[unfolded gs] have "pl.dvdm u f" unfolding pl.dvdm_def
      by (intro exI[of  _ "smult (lead_coeff f) (prod_mset (mset (gs1 @ gs2)))"], auto)
  } note pl_uf = this
  hence p_uf: "p.dvdm u f" by (rule pl_dvdm_imp_p_dvdm)
  have monic_u: "monic u" using mon[OF u_gs] .
  have irred_u: "p.irreducible_m u" using irred_p[OF u_gs] by auto
  have degree_m_u: "p.degree_m u = degree u" using monic_u by simp
  have degree_u[simp]: "0 < degree u" 
    using irred_u by (fold degree_m_u, auto simp add: p.irreducible_degree)
  have deg_u_d: "degree u < d + 1" by auto 
  from F_f_G have f_dvd_F: "f dvd F" by auto
  from square_free_factor[OF f_dvd_F sf_F] have sf_f: "square_free f" . 
  from norm have norm_map: "map pl.Mp gs = gs" by (induct gs, auto)
  {
    fix factor
    assume factor_f: "factor dvd f" and u_factor: "p.dvdm u factor" 
    from factor_f obtain h where f: "f = factor * h" unfolding dvd_def by auto
    obtain gs1 gs2 where part: "List.partition (\<lambda>gi. p.dvdm gi factor) gs = (gs1, gs2)" by force
    from p.unique_factorization_m_factor_partition[OF l0 f_gs_factor f cop sf part]
    have factor: "pl.unique_factorization_m factor (lead_coeff factor, mset gs1)" by auto
    from u_factor part u_gs have u_gs1: "u \<in> set gs1" by auto
    define gs1' where "gs1' = remove1 u gs1" 
    from remove1_mset[OF u_gs1, folded gs1'_def] 
    have gs1: "mset gs1 = add_mset u (mset gs1')" by auto
    from remove1_mset[OF u_gs, folded gs''_def] 
    have gs: "mset gs = add_mset u (mset gs'')" by auto
    from part have filter: "gs1 = [gi\<leftarrow>gs . p.dvdm gi factor]" by auto 
    have "mset gs1 \<subseteq># mset gs" unfolding filter mset_filter by simp
    hence sub: "mset gs1' \<subseteq># mset gs''" unfolding gs gs1 by auto 
    from p.coprime_lead_coeff_factor[OF \<open>prime p\<close> cop[unfolded f]]
    have cop': "coprime (lead_coeff factor) p" by auto
    have p_factor0: "p.Mp factor \<noteq> 0"
      by (metis f p.Mp_0 p.square_free_m_def poly_mod.square_free_m_factor(1) sf)
    have pl_factor0: "pl.Mp factor \<noteq> 0" using p_factor0 l0
      by (metis p.Mp_0 p_Mp_pl_Mp)
    from pl.factorization_m_degree[OF pl.unique_factorization_m_imp_factorization[OF factor] pl_factor0]
    have "pl.degree_m factor = sum_mset (image_mset pl.degree_m (mset gs1))" .
    also have "image_mset pl.degree_m (mset gs1) = image_mset degree (mset gs1)" 
      by (rule image_mset_cong, rule pl.monic_degree_m[OF mon], insert part, auto)
    also have "pl.degree_m factor = degree factor"
      by (rule pl.degree_m_eq[OF p.coprime_exp_mod[OF cop' l0] pl.m1])
    finally have "degree factor = d + sum_mset (image_mset degree (mset gs1'))" unfolding gs1 by auto
    moreover have "sum_mset (image_mset degree (mset gs1')) \<in> sub_mset_sums degs" unfolding degs_def
      sub_mset_sums mset_map
      by (intro imageI CollectI image_mset_subseteq_mono[OF sub])
    ultimately have "degree factor \<in> Degs" unfolding Degs_def by auto
  } note Degs = this
  have length_less: "length gs' < length gs" 
    and irreducible_factor: "irreducible\<^sub>d factor"
    and h_dvd_f: "h dvd f"
    and f_h_factor: "f = h * factor" 
    and h_eq: "pl.unique_factorization_m h (b', mset gs')"
    and gs'_gs: "set gs' \<subseteq> set gs"
    and b': "b' = lead_coeff h" 
    and h1: "gs' = [] \<longrightarrow> h = 1"
    using LLL_reconstruction_inner_loop[OF degree_u monic_u irred_u p_uf f_dvd_F n_def(2)
      f_gs_factor cop sf sf_f u_gs norm_map Degs
      a1 a2 n_def(1)] deg_u_d gs_not_empty by metis+
  have F_h_factor_G: "F = h * prod_list (factor # G)"
    using F_f_G f_h_factor by auto
  hence h_dvd_F: "h dvd F" using f_dvd_F dvd_trans by auto
  have irreducible_factor_G: "\<And> x. x \<in> set (factor # G) \<Longrightarrow> irreducible\<^sub>d x"
    using irreducible_factor irreducible_G by auto
  from p.coprime_lead_coeff_factor[OF \<open>prime p\<close> cop[unfolded f_h_factor]] 
  have cop': "coprime (lead_coeff h) p" by auto
  have lc': "lead_coeff (smult (lead_coeff h) (prod_list gs')) = lead_coeff h" 
    by (insert gs'_gs, auto intro!: monic_prod_list intro: mon)
  have lc: "lead_coeff (pl.Mp (smult (lead_coeff h) (prod_list gs'))) = pl.M (lead_coeff h)"
  proof (subst pl.degree_m_eq_lead_coeff[OF pl.degree_m_eq[OF _ pl.m1]]; unfold lc')
    show "lead_coeff h mod p^l \<noteq> 0" using p.coprime_exp_mod[OF cop' l0] by auto
  qed auto
  have uh: "pl.unique_factorization_m h (lead_coeff h, mset gs')" using h_eq unfolding b' .
  from p.square_free_m_factor[OF sf[unfolded f_h_factor]] have sf': "p.square_free_m h" by auto
  show ?case
  proof (cases "gs' \<noteq> []")
    case gs'_not_empty: True 
    show ?thesis 
      by (rule "1.IH"[rule_format, OF length_less LLL_eq irreducible_factor_G F_h_factor_G 
        uh gs'_not_empty norm irred_p sf' cop'], insert gs'_gs, auto)
  next
    case False
    have pl_ge0: "p^l > 0" using p1 by auto
    have G'_eq: "G' = factor # G" using LLL_eq False using LLL_reconstruction''.simps by auto
    have condition1: "(\<forall>a\<in>set G'. irreducible\<^sub>d a)" using irreducible_factor_G G'_eq by auto
    have h_eq2: "pl.Mp h = pl.Mp [:b':]" using h_eq False 
      unfolding pl.unique_factorization_m_alt_def pl.factorization_m_def by auto
    have Mp_const_rw[simp]: "pl.Mp [:b':] = [:b' mod p^l:]" using pl.Mp_const_poly by blast
    have condition2: "F = prod_list G'" using h1 False f_h_factor G'_eq F_h_factor_G by auto
    show ?thesis using condition1 condition2 by auto
  qed
qed

context
  fixes gs :: "int poly list" 
  assumes gs_hen: "berlekamp_hensel p l F = gs" 
   and cop: "coprime (lead_coeff F) p" 
   and sf: "poly_mod.square_free_m p F" 
   and sf_F: "square_free F" 
begin

lemma gs_not_empty: "gs \<noteq> []"
proof (rule ccontr, simp)
  assume gs: "gs = []"
  obtain c fs where c_fs: "finite_field_factorization_int p F = (c, fs)" by force
  have "sort (map degree fs) = sort (map degree gs)" 
    by (rule p.berlekamp_hensel_main(2)[OF _ gs_hen cop sf c_fs], simp add: l0)    
  hence fs_empty: "fs = []" using gs by (cases fs, auto)
  hence fs: "mset fs = {#}" by auto
  have "p.unique_factorization_m F (c, mset fs)" and c: "c \<in> {0..<p}"
    using p.finite_field_factorization_int[OF sf c_fs] by auto
  hence "p.factorization_m F (c, mset fs)"
    using p.unique_factorization_m_imp_factorization by auto    
  hence eq_m_F: "p.eq_m F [:c:]" unfolding fs p.factorization_m_def by auto
  hence "0 = p.degree_m F" by (simp add: p.Mp_const_poly)
  also have "... = degree F" by (rule p.degree_m_eq[OF _ p1], insert cop p1, auto)
  finally have "degree F = 0" ..
  thus False using N0 by simp
qed

lemma reconstruction_of_algorithm_16_22:   
  assumes 1: "reconstruction_of_algorithm_16_22 p l gs F = G"
  shows "(\<forall>g\<in>set G. irreducible\<^sub>d g) \<and> F = prod_list G"
proof -
  note * = p.berlekamp_hensel_unique[OF cop sf gs_hen l0]
  obtain c fs where "finite_field_factorization_int p F = (c, fs)" by force
  from p.berlekamp_hensel_main[OF l0 gs_hen cop sf this]
  show ?thesis
    using 1 unfolding reconstruction_of_algorithm_16_22_def Let_def
    by (intro LLL_reconstruction''[OF _ _ _ _ gs_not_empty], insert * sf sf_F cop, auto)
qed
end
end

subsubsection \<open>Final statement\<close>

lemma factorization_algorithm_16_22:
  assumes res: "factorization_algorithm_16_22 f = G"
  and sff: "square_free f"
  and deg: "degree f > 0" 
  shows "(\<forall>g\<in>set G. irreducible\<^sub>d g) \<and> f = prod_list G"
proof -
  let ?lc = "lead_coeff f" 
  define p where "p \<equiv> suitable_prime_bz f" 
  obtain c gs where fff: "finite_field_factorization_int p f = (c,gs)" by force
  let ?degs = "map degree gs" 
  note res = res[unfolded factorization_algorithm_16_22_def Let_def, folded p_def,
    unfolded fff split, folded]
  from suitable_prime_bz[OF sff refl]
  have prime: "prime p" and cop: "coprime ?lc p" and sf: "poly_mod.square_free_m p f" 
    unfolding p_def by auto
  note res
  from prime interpret poly_mod_prime p by unfold_locales
  define K where "K = 2 ^ (5 * degree f * degree f) *
            \<parallel>f\<parallel>\<^sup>2 ^ (2 * degree f)"
  define N where "N = sqrt_int_ceiling K" 
  have K0: "K \<ge> 0" unfolding K_def by auto
  have N0: "N \<ge> 0" unfolding N_def sqrt_int_ceiling using K0 
    by (smt of_int_nonneg real_sqrt_ge_0_iff zero_le_ceiling)
  define n where "n = find_exponent p N" 
  note res = res[folded n_def[unfolded N_def K_def]]
  note n = find_exponent[OF m1, of N, folded n_def]
  note bh = berlekamp_and_hensel_separated[OF cop sf refl fff n(2)]
  note res = res[folded bh(1)]
  show ?thesis
  proof (rule reconstruction_of_algorithm_16_22[OF prime deg _ refl cop sf sff res])
    from n(1) have "N \<le> p ^ n" by simp
    hence *: "N^2 \<le> (p^n)^2" 
      by (intro power_mono N0, auto)        
    show "2 ^ (degree f)\<^sup>2 * B2_LLL f ^ (2 * degree f) \<le> (p ^ n)\<^sup>2" 
    proof (rule order.trans[OF _ *])
      have "2 ^ (degree f)\<^sup>2 * B2_LLL f ^ (2 * degree f) = K"
        unfolding K_def B2_LLL_def by (simp add: ac_simps 
          power_mult_distrib power2_eq_square power_mult[symmetric] power_add[symmetric])
      also have "\<dots> \<le> N\<^sup>2" unfolding N_def by (rule sqrt_int_ceiling_bound[OF K0])
      finally show "2 ^ (degree f)\<^sup>2 * B2_LLL f ^ (2 * degree f) \<le> N\<^sup>2" .
    qed
  qed
qed

lift_definition increasing_lattices_LLL_factorization :: int_poly_factorization_algorithm
  is factorization_algorithm_16_22 using factorization_algorithm_16_22 by auto

thm factorize_int_poly[of increasing_lattices_LLL_factorization]

end
