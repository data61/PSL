(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Polynomials in a Finite Field\<close>
text \<open>We connect polynomials in a prime field with integer polynomials modulo some prime.\<close>

theory Poly_Mod_Finite_Field
  imports
  Finite_Field
  Polynomial_Interpolation.Ring_Hom_Poly
  "HOL-Types_To_Sets.Types_To_Sets"
  Missing_Multiset2
  Poly_Mod
begin

(* TODO: Move -- General transfer rule *)
declare rel_mset_Zero[transfer_rule]

lemma mset_transfer[transfer_rule]: "(list_all2 rel ===> rel_mset rel) mset mset"
proof (intro rel_funI)
  show "list_all2 rel xs ys \<Longrightarrow> rel_mset rel (mset xs) (mset ys)" for xs ys
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by auto
  next
    case IH: (Cons x xs)
    then show ?case by (auto dest!:msed_rel_invL simp: list_all2_Cons1 intro!:rel_mset_Plus)
  qed
qed


abbreviation to_int_poly :: "'a :: finite mod_ring poly \<Rightarrow> int poly" where
  "to_int_poly \<equiv> map_poly to_int_mod_ring"

interpretation to_int_poly_hom: map_poly_inj_zero_hom to_int_mod_ring ..

lemma irreducible\<^sub>d_def_0:
  fixes f :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  shows "irreducible\<^sub>d f = (degree f \<noteq> 0 \<and> 
  (\<forall> g h. degree g \<noteq> 0 \<longrightarrow> degree h \<noteq> 0 \<longrightarrow> f \<noteq> g * h))"
proof-
  have "degree g \<noteq> 0 \<Longrightarrow> g \<noteq> 0" for g :: "'a poly" by auto
  note 1 = degree_mult_eq[OF this this, simplified]
  then show ?thesis by (force elim!: irreducible\<^sub>dE)
qed

subsection \<open>Transferring to class-based mod-ring\<close>

locale poly_mod_type = poly_mod m
  for m and ty :: "'a :: nontriv itself" +
  assumes m: "m = CARD('a)"
begin

lemma m1: "m > 1" using nontriv[where 'a = 'a] by (auto simp:m)

sublocale poly_mod_2 using m1 by unfold_locales

definition MP_Rel :: "int poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> bool"
  where "MP_Rel f f' \<equiv> (Mp f = to_int_poly f')"

definition M_Rel :: "int \<Rightarrow> 'a mod_ring \<Rightarrow> bool"
  where "M_Rel x x' \<equiv> (M x = to_int_mod_ring x')"

definition "MF_Rel \<equiv> rel_prod M_Rel (rel_mset MP_Rel)"

lemma to_int_mod_ring_plus: "to_int_mod_ring ((x :: 'a mod_ring) + y) = M (to_int_mod_ring x + to_int_mod_ring y)"
  unfolding M_def using m by (transfer, auto)

lemma to_int_mod_ring_times: "to_int_mod_ring ((x :: 'a mod_ring) * y) = M (to_int_mod_ring x * to_int_mod_ring y)"
  unfolding M_def using m by (transfer, auto)

lemma degree_MP_Rel [transfer_rule]: "(MP_Rel ===> (=)) degree_m degree"
  unfolding MP_Rel_def rel_fun_def 
  by (auto intro!: degree_map_poly)

lemma eq_M_Rel[transfer_rule]: "(M_Rel ===> M_Rel ===> (=)) (\<lambda> x y. M x = M y) (=)"
  unfolding M_Rel_def rel_fun_def by auto

interpretation to_int_mod_ring_hom: map_poly_inj_zero_hom to_int_mod_ring..

lemma eq_MP_Rel[transfer_rule]: "(MP_Rel ===> MP_Rel ===> (=)) (=m) (=)"
  unfolding MP_Rel_def rel_fun_def by auto

lemma eq_Mf_Rel[transfer_rule]: "(MF_Rel ===> MF_Rel ===> (=)) (\<lambda> x y. Mf x = Mf y) (=)"
proof (intro rel_funI, goal_cases)
  case (1 cfs Cfs dgs Dgs)
  obtain c fs where cfs: "cfs = (c,fs)" by force
  obtain C Fs where Cfs: "Cfs = (C,Fs)" by force
  obtain d gs where dgs: "dgs = (d,gs)" by force
  obtain D Gs where Dgs: "Dgs = (D,Gs)" by force
  note pairs = cfs Cfs dgs Dgs
  from 1[unfolded pairs MF_Rel_def rel_prod.simps]
  have *[transfer_rule]: "M_Rel c C" "M_Rel d D" "rel_mset MP_Rel fs Fs" "rel_mset MP_Rel gs Gs" 
    by auto  
  have eq1: "(M c = M d) = (C = D)" by transfer_prover
  from *(3)[unfolded rel_mset_def] obtain fs' Fs' where fs_eq: "mset fs' = fs" "mset Fs' = Fs"
    and rel_f: "list_all2 MP_Rel fs' Fs'" by auto
  from *(4)[unfolded rel_mset_def] obtain gs' Gs' where gs_eq: "mset gs' = gs" "mset Gs' = Gs"
    and rel_g: "list_all2 MP_Rel gs' Gs'" by auto
  have eq2: "(image_mset Mp fs = image_mset Mp gs) = (Fs = Gs)" 
    using *(3-4)
  proof (induct fs arbitrary: Fs gs Gs)
    case (empty Fs gs Gs)
    from empty(1) have Fs: "Fs = {#}" unfolding rel_mset_def by auto
    with empty show ?case by (cases gs; cases Gs; auto simp: rel_mset_def)
  next
    case (add f fs Fs' gs' Gs')
    note [transfer_rule] = add(3)
    from msed_rel_invL[OF add(2)]
    obtain Fs F where Fs': "Fs' = Fs + {#F#}" and rel[transfer_rule]: 
      "MP_Rel f F" "rel_mset MP_Rel fs Fs" by auto      
    note IH = add(1)[OF rel(2)]
    {      
      from add(3)[unfolded rel_mset_def] obtain gs Gs where id: "mset gs = gs'" "mset Gs = Gs'" 
        and rel: "list_all2 MP_Rel gs Gs" by auto
      have "Mp f \<in># image_mset Mp gs' \<longleftrightarrow> F \<in># Gs'" 
      proof -
        have "?thesis = ((Mp f \<in> Mp ` set gs) = (F \<in> set Gs))" 
          unfolding id[symmetric] by simp
        also have \<dots> using rel
        proof (induct gs Gs rule: list_all2_induct)
          case (Cons g gs G Gs)
          note [transfer_rule] = Cons(1-2)
          have id: "(Mp g = Mp f) = (F = G)" by (transfer, auto)
          show ?case using id Cons(3) by auto
        qed auto
        finally show ?thesis by simp
      qed
    } note id = this
    show ?case
    proof (cases "Mp f \<in># image_mset Mp gs'")
      case False
      have "Mp f \<in># image_mset Mp (fs + {#f#})" by auto
      with False have F: "image_mset Mp (fs + {#f#}) \<noteq> image_mset Mp gs'" by metis
      with False[unfolded id] show ?thesis unfolding Fs' by auto
    next
      case True
      then obtain g where fg: "Mp f = Mp g" and g: "g \<in># gs'" by auto
      from g obtain gs where gs': "gs' = add_mset g gs" by (rule mset_add)
      from msed_rel_invL[OF add(3)[unfolded gs']]
      obtain Gs G where Gs': "Gs' = Gs + {# G #}" and gG[transfer_rule]: "MP_Rel g G" and 
        gsGs: "rel_mset MP_Rel gs Gs" by auto
      have FG: "F = G" by (transfer, simp add: fg)
      note IH = IH[OF gsGs]
      show ?thesis unfolding gs' Fs' Gs' by (simp add: fg IH FG)
    qed
  qed
  show "(Mf cfs = Mf dgs) = (Cfs = Dgs)" unfolding pairs Mf_def split
    by (simp add: eq1 eq2)
qed

lemmas coeff_map_poly_of_int = coeff_map_poly[of of_int, OF of_int_0]

lemma plus_MP_Rel[transfer_rule]: "(MP_Rel ===> MP_Rel ===> MP_Rel) (+) (+)"
  unfolding MP_Rel_def 
proof (intro rel_funI, goal_cases)
  case (1 x f y g)
  have "Mp (x + y) = Mp (Mp x + Mp y)" by simp
  also have "\<dots> = Mp (map_poly to_int_mod_ring f + map_poly to_int_mod_ring g)" unfolding 1 ..
  also have "\<dots> = map_poly to_int_mod_ring (f + g)" unfolding poly_eq_iff Mp_coeff 
       by (auto simp: to_int_mod_ring_plus)
  finally show ?case .
qed

lemma times_MP_Rel[transfer_rule]: "(MP_Rel ===> MP_Rel ===> MP_Rel) ((*)) ((*))"
  unfolding MP_Rel_def
proof (intro rel_funI, goal_cases)
  case (1 x f y g)
  have "Mp (x * y) = Mp (Mp x * Mp y)" by simp
  also have "\<dots> = Mp (map_poly to_int_mod_ring f * map_poly to_int_mod_ring g)" unfolding 1 ..
  also have "\<dots> = map_poly to_int_mod_ring (f * g)"
  proof -
    { fix n :: nat
      define A where "A = {.. n}" 
      have "finite A" unfolding A_def by auto
      then have "M (\<Sum>i\<le>n. to_int_mod_ring (coeff f i) * to_int_mod_ring (coeff g (n - i))) =
           to_int_mod_ring (\<Sum>i\<le>n. coeff f i * coeff g (n - i))"
        unfolding A_def[symmetric]
      proof (induct A)
        case (insert a A)
        have "?case = ?case" (is "(?l = ?r) = _") by simp
        have "?r = to_int_mod_ring (coeff f a * coeff g (n - a) + (\<Sum>i\<in> A. coeff f i * coeff g (n - i)))" 
          using insert(1-2) by auto
        note r = this[unfolded to_int_mod_ring_plus to_int_mod_ring_times]
        from insert(1-2) have "?l = M (to_int_mod_ring (coeff f a) * to_int_mod_ring (coeff g (n - a)) 
          + M (\<Sum>i\<in>A. to_int_mod_ring (coeff f i) * to_int_mod_ring (coeff g (n - i))))" 
          by simp
        also have "M (\<Sum>i\<in>A. to_int_mod_ring (coeff f i) * to_int_mod_ring (coeff g (n - i))) = to_int_mod_ring (\<Sum>i\<in>A. coeff f i * coeff g (n - i))"
          unfolding insert ..
        finally
        show ?case unfolding r by simp
      qed auto
    }
    then show ?thesis by (auto intro!:poly_eqI simp: coeff_mult  Mp_coeff)
  qed
  finally show ?case .
qed

lemma smult_MP_Rel[transfer_rule]: "(M_Rel ===> MP_Rel ===> MP_Rel) smult smult"
  unfolding MP_Rel_def M_Rel_def
proof (intro rel_funI, goal_cases)
  case (1 x x' f f')
  thus ?case unfolding poly_eq_iff coeff Mp_coeff
    coeff_smult M_def
  proof (intro allI, goal_cases)
    case (1 n)
    have "x * coeff f n mod m = (x mod m) * (coeff f n mod m) mod m" 
      by (simp add: mod_simps)
    also have "\<dots> = to_int_mod_ring x' * (to_int_mod_ring (coeff f' n)) mod m" 
      using 1 by auto
    also have " \<dots> = to_int_mod_ring (x' * coeff f' n)" 
      unfolding to_int_mod_ring_times M_def by simp
    finally show ?case by auto
  qed
qed

lemma one_M_Rel[transfer_rule]: "M_Rel 1 1"
  unfolding M_Rel_def M_def
  unfolding m by auto

lemma one_MP_Rel[transfer_rule]: "MP_Rel 1 1"
  unfolding MP_Rel_def poly_eq_iff Mp_coeff M_def 
  unfolding m by auto

lemma zero_M_Rel[transfer_rule]: "M_Rel 0 0"
  unfolding M_Rel_def M_def 
  unfolding m by auto

lemma zero_MP_Rel[transfer_rule]: "MP_Rel 0 0"
  unfolding MP_Rel_def poly_eq_iff Mp_coeff M_def
  unfolding m by auto

lemma listprod_MP_Rel[transfer_rule]: "(list_all2 MP_Rel ===> MP_Rel) prod_list prod_list"
proof (intro rel_funI, goal_cases)
  case (1 xs ys)
  thus ?case 
  proof (induct xs ys rule: list_all2_induct)
    case (Cons x xs y ys)
    note [transfer_rule] = this
    show ?case by simp transfer_prover
  qed (simp add: one_MP_Rel)
qed

lemma prod_mset_MP_Rel[transfer_rule]: "(rel_mset MP_Rel ===> MP_Rel) prod_mset prod_mset"
proof (intro rel_funI, goal_cases)
  case (1 xs ys)
  have "(MP_Rel ===> MP_Rel ===> MP_Rel) ((*)) ((*))" "MP_Rel 1 1" by transfer_prover+
  from 1 this show ?case
  proof (induct xs ys rule: rel_mset_induct)
    case (add R x xs y ys)
    note [transfer_rule] = this
    show ?case by simp transfer_prover
  qed (simp add: one_MP_Rel)
qed

lemma right_unique_MP_Rel[transfer_rule]: "right_unique MP_Rel"
  unfolding right_unique_def MP_Rel_def by auto

lemma M_to_int_mod_ring: "M (to_int_mod_ring (x :: 'a mod_ring)) = to_int_mod_ring x"
  unfolding M_def unfolding m by (transfer, auto)

lemma Mp_to_int_poly: "Mp (to_int_poly (f :: 'a mod_ring poly)) = to_int_poly f"
  by (auto simp: poly_eq_iff Mp_coeff M_to_int_mod_ring)

lemma right_total_M_Rel[transfer_rule]: "right_total M_Rel"
  unfolding right_total_def M_Rel_def using M_to_int_mod_ring by blast

lemma left_total_M_Rel[transfer_rule]: "left_total M_Rel"
  unfolding left_total_def M_Rel_def[abs_def] 
proof
  fix x
  show "\<exists> x' :: 'a mod_ring. M x = to_int_mod_ring x'"  unfolding M_def unfolding m
    by (rule exI[of _ "of_int x"], transfer, simp)
qed

lemma bi_total_M_Rel[transfer_rule]: "bi_total M_Rel" 
  using right_total_M_Rel left_total_M_Rel by (metis bi_totalI)

lemma right_total_MP_Rel[transfer_rule]: "right_total MP_Rel"
  unfolding right_total_def MP_Rel_def
proof
  fix f :: "'a mod_ring poly"
  show "\<exists>x. Mp x = to_int_poly f"
    by (intro exI[of _ "to_int_poly f"], simp add: Mp_to_int_poly)
qed

lemma to_int_mod_ring_of_int_M: "to_int_mod_ring (of_int x :: 'a mod_ring) = M x" unfolding M_def
  unfolding m by transfer auto

lemma Mp_f_representative: "Mp f = to_int_poly (map_poly of_int f :: 'a mod_ring poly)"
  unfolding Mp_def by (auto intro: poly_eqI simp: coeff_map_poly to_int_mod_ring_of_int_M)

lemma left_total_MP_Rel[transfer_rule]: "left_total MP_Rel"
  unfolding left_total_def MP_Rel_def[abs_def] using Mp_f_representative by blast

lemma bi_total_MP_Rel[transfer_rule]: "bi_total MP_Rel"
  using right_total_MP_Rel left_total_MP_Rel by (metis bi_totalI)

lemma bi_total_MF_Rel[transfer_rule]: "bi_total MF_Rel"
  unfolding MF_Rel_def[abs_def] 
  by (intro prod.bi_total_rel multiset.bi_total_rel bi_total_MP_Rel bi_total_M_Rel)

lemma right_total_MF_Rel[transfer_rule]: "right_total MF_Rel"
  using bi_total_MF_Rel unfolding bi_total_alt_def by auto

lemma left_total_MF_Rel[transfer_rule]: "left_total MF_Rel"
  using bi_total_MF_Rel unfolding bi_total_alt_def by auto

lemma domain_RT_rel[transfer_domain_rule]: "Domainp MP_Rel = (\<lambda> f. True)"
proof
  fix f :: "int poly"
  show "Domainp MP_Rel f = True" unfolding MP_Rel_def[abs_def] Domainp.simps
    by (auto simp: Mp_f_representative)
qed

lemma mem_MP_Rel[transfer_rule]: "(MP_Rel ===> rel_set MP_Rel ===> (=)) (\<lambda> x Y. \<exists>y \<in> Y. eq_m x y) (\<in>)"
proof (intro rel_funI iffI)
  fix x y X Y assume xy: "MP_Rel x y" and XY: "rel_set MP_Rel X Y"
  { assume "\<exists>x' \<in> X. x =m x'"
    then obtain x' where x'X: "x' \<in> X" and xx': "x =m x'" by auto
    with xy have x'y: "MP_Rel x' y" by (auto simp: MP_Rel_def)
    from rel_setD1[OF XY x'X] obtain y' where "MP_Rel x' y'" and "y' \<in> Y" by auto
    with x'y
    show "y \<in> Y" by (auto simp: MP_Rel_def)
  }
  assume "y \<in> Y"
  from rel_setD2[OF XY this] obtain x' where x'X: "x' \<in> X" and x'y: "MP_Rel x' y" by auto
  from xy x'y have "x =m x'" by (auto simp: MP_Rel_def)
  with x'X show "\<exists>x' \<in> X. x =m x'" by auto
qed

lemma conversep_MP_Rel_OO_MP_Rel [simp]: "MP_Rel\<inverse>\<inverse> OO MP_Rel = (=)"
  using Mp_to_int_poly by (intro ext, auto simp: OO_def MP_Rel_def)

lemma MP_Rel_OO_conversep_MP_Rel [simp]: "MP_Rel OO MP_Rel\<inverse>\<inverse> = eq_m"
  by (intro ext, auto simp: OO_def MP_Rel_def Mp_f_representative)

lemma conversep_MP_Rel_OO_eq_m [simp]: "MP_Rel\<inverse>\<inverse> OO eq_m = MP_Rel\<inverse>\<inverse>"
  by (intro ext, auto simp: OO_def MP_Rel_def)

lemma eq_m_OO_MP_Rel [simp]: "eq_m OO MP_Rel = MP_Rel"
  by (intro ext, auto simp: OO_def MP_Rel_def)

lemma eq_mset_MP_Rel [transfer_rule]: "(rel_mset MP_Rel ===> rel_mset MP_Rel ===> (=)) (rel_mset eq_m) (=)"
proof (intro rel_funI iffI)
  fix A B X Y
  assume AX: "rel_mset MP_Rel A X" and BY: "rel_mset MP_Rel B Y"
  {
    assume AB: "rel_mset eq_m A B"
    from AX have "rel_mset MP_Rel\<inverse>\<inverse> X A" by (simp add: multiset.rel_flip)
    note rel_mset_OO[OF this AB]
    note rel_mset_OO[OF this BY]
    then show "X = Y" by (simp add: multiset.rel_eq)
  }
  assume "X = Y"
  with BY have "rel_mset MP_Rel\<inverse>\<inverse> X B" by (simp add: multiset.rel_flip)
  from rel_mset_OO[OF AX this]
  show "rel_mset eq_m A B" by simp
qed

lemma dvd_MP_Rel[transfer_rule]: "(MP_Rel ===> MP_Rel ===> (=)) (dvdm) (dvd)"
  unfolding dvdm_def[abs_def] dvd_def[abs_def]
  by transfer_prover

lemma irreducible_MP_Rel [transfer_rule]: "(MP_Rel ===> (=)) irreducible_m irreducible"
  unfolding irreducible_m_def irreducible_def
  by transfer_prover

lemma irreducible\<^sub>d_MP_Rel [transfer_rule]: "(MP_Rel ===> (=)) irreducible\<^sub>d_m irreducible\<^sub>d"
  unfolding irreducible\<^sub>d_m_def[abs_def] irreducible\<^sub>d_def[abs_def]
  by transfer_prover

lemma UNIV_M_Rel[transfer_rule]: "rel_set M_Rel {0..<m} UNIV"
  unfolding rel_set_def M_Rel_def[abs_def] M_def 
  by (auto simp: M_def m, goal_cases, metis to_int_mod_ring_of_int_mod_ring, (transfer, auto)+)

lemma coeff_MP_Rel [transfer_rule]: "(MP_Rel ===> (=) ===> M_Rel) coeff coeff"
  unfolding rel_fun_def M_Rel_def MP_Rel_def Mp_coeff[symmetric] by auto

lemma M_1_1: "M 1 = 1" unfolding M_def unfolding m by simp

lemma square_free_MP_Rel [transfer_rule]: "(MP_Rel ===> (=)) square_free_m square_free"
  unfolding square_free_m_def[abs_def] square_free_def[abs_def]
  by (transfer_prover_start, transfer_step+, auto)

lemma mset_factors_m_MP_Rel [transfer_rule]: "(rel_mset MP_Rel ===> MP_Rel ===> (=)) mset_factors_m mset_factors"
  unfolding mset_factors_def mset_factors_m_def
  by (transfer_prover_start, transfer_step+, auto dest:eq_m_irreducible_m)

lemma coprime_MP_Rel [transfer_rule]: "(MP_Rel ===> MP_Rel ===> (=)) coprime_m coprime"
  unfolding coprime_m_def[abs_def] coprime_def' [abs_def]
  by (transfer_prover_start, transfer_step+, auto)

lemma prime_elem_MP_Rel [transfer_rule]: "(MP_Rel ===> (=)) prime_elem_m prime_elem"
  unfolding prime_elem_m_def prime_elem_def by transfer_prover

end

context poly_mod_2 begin

lemma non_empty: "{0..<m} \<noteq> {}" using m1 by auto

lemma type_to_set:
  assumes type_def: "\<exists>(Rep :: 'b \<Rightarrow> int) Abs. type_definition Rep Abs {0 ..< m :: int}"
  shows "class.nontriv (TYPE('b))" (is ?a) and "m = int CARD('b)" (is ?b)
proof -
  from type_def obtain rep :: "'b \<Rightarrow> int" and abs :: "int \<Rightarrow> 'b" where t: "type_definition rep abs {0 ..< m}" by auto
  have "card (UNIV :: 'b set) = card {0 ..< m}" using t by (rule type_definition.card)
  also have "\<dots> = m" using m1 by auto
  finally show ?b ..
  then show ?a unfolding class.nontriv_def using m1 by auto
qed

end

locale poly_mod_prime_type = poly_mod_type m ty for m :: int and
  ty :: "'a :: prime_card itself"
begin 

lemma factorization_MP_Rel [transfer_rule]:
  "(MP_Rel ===> MF_Rel ===> (=)) factorization_m (factorization Irr_Mon)"
  unfolding rel_fun_def
proof (intro allI impI, goal_cases)
  case (1 f F cfs Cfs)
  note [transfer_rule] = 1(1)
  obtain c fs where cfs: "cfs = (c,fs)" by force
  obtain C Fs where Cfs: "Cfs = (C,Fs)" by force
  from 1(2)[unfolded rel_prod.simps cfs Cfs MF_Rel_def] 
  have tr[transfer_rule]: "M_Rel c C" "rel_mset MP_Rel fs Fs" by auto
  have eq: "(f =m smult c (prod_mset fs) = (F = smult C (prod_mset Fs)))" 
    by transfer_prover
  have "set_mset Fs \<subseteq> Irr_Mon = (\<forall> x \<in># Fs. irreducible\<^sub>d x \<and> monic x)" unfolding Irr_Mon_def by auto
  also have "\<dots> = (\<forall>f\<in>#fs. irreducible\<^sub>d_m f \<and> monic (Mp f))"
  proof (rule sym, transfer_prover_start, transfer_step+)
    {
      fix f
      assume "f \<in># fs" 
      have "monic (Mp f) \<longleftrightarrow> M (coeff f (degree_m f)) = M 1"
        unfolding Mp_coeff[symmetric] by simp
    }
    thus "(\<forall>f\<in>#fs. irreducible\<^sub>d_m f \<and> monic (Mp f)) = 
      (\<forall>x\<in>#fs. irreducible\<^sub>d_m x \<and> M (coeff x (degree_m x)) = M 1)" by auto
  qed
  finally
  show "factorization_m f cfs = factorization Irr_Mon F Cfs" unfolding cfs Cfs
    factorization_m_def factorization_def split eq by simp
qed

lemma unique_factorization_MP_Rel [transfer_rule]: "(MP_Rel ===> MF_Rel ===> (=))
  unique_factorization_m (unique_factorization Irr_Mon)"
  unfolding rel_fun_def
proof (intro allI impI, goal_cases)
  case (1 f F cfs Cfs)
  note [transfer_rule] = 1(1,2)
  let ?F = "factorization Irr_Mon F" 
  let ?f = "factorization_m f" 
  let ?R = "Collect ?F" 
  let ?L = "Mf ` Collect ?f"
  note X_to_x = right_total_MF_Rel[unfolded right_total_def, rule_format]
  {
    fix X
    assume "X \<in> ?R" 
    hence F: "?F X" by simp
    from X_to_x[of X] obtain x where rel[transfer_rule]: "MF_Rel x X" by blast
    from F[untransferred] have "Mf x \<in> ?L" by blast
    with rel have "\<exists> x. Mf x \<in> ?L \<and> MF_Rel x X" by blast
  } note R_to_L = this
  show "unique_factorization_m f cfs = unique_factorization Irr_Mon F Cfs" unfolding 
    unique_factorization_m_def unique_factorization_def  
  proof -
    have fF: "?F Cfs = ?f cfs" by transfer simp
    have "(?L = {Mf cfs}) = (?L \<subseteq> {Mf cfs} \<and> Mf cfs \<in> ?L)" by blast
    also have "?L \<subseteq> {Mf cfs} = (\<forall> dfs. ?f dfs \<longrightarrow> Mf dfs = Mf cfs)" by blast
    also have "\<dots> = (\<forall> y. ?F y \<longrightarrow> y = Cfs)" (is "?left = ?right")
    proof (rule; intro allI impI)
      fix Dfs
      assume *: ?left and F: "?F Dfs" 
      from X_to_x[of Dfs] obtain dfs where [transfer_rule]: "MF_Rel dfs Dfs" by auto
      from F[untransferred] have f: "?f dfs" .
      from *[rule_format, OF f] have eq: "Mf dfs = Mf cfs" by simp
      have "(Mf dfs = Mf cfs) = (Dfs = Cfs)" by (transfer_prover_start, transfer_step+, simp) 
      thus "Dfs = Cfs" using eq by simp
    next
      fix dfs
      assume *: ?right and f: "?f dfs" 
      from left_total_MF_Rel obtain Dfs where 
        rel[transfer_rule]: "MF_Rel dfs Dfs" unfolding left_total_def by blast
      have "?F Dfs" by (transfer, rule f)
      from *[rule_format, OF this] have eq: "Dfs = Cfs" .
      have "(Mf dfs = Mf cfs) = (Dfs = Cfs)" by (transfer_prover_start, transfer_step+, simp) 
      thus "Mf dfs = Mf cfs" using eq by simp
    qed    
    also have "Mf cfs \<in> ?L = (\<exists> dfs. ?f dfs \<and> Mf cfs = Mf dfs)" by auto
    also have "\<dots> = ?F Cfs"  unfolding fF
    proof
      assume "\<exists> dfs. ?f dfs \<and> Mf cfs  = Mf dfs" 
      then obtain dfs where f: "?f dfs" and id: "Mf dfs = Mf cfs" by auto
      from f have "?f (Mf dfs)" by simp
      from this[unfolded id] show "?f cfs" by simp
    qed blast
    finally show "(?L = {Mf cfs}) = (?R = {Cfs})" by auto
  qed
qed

end

context begin
private lemma 1: "poly_mod_type TYPE('a :: nontriv) m = (m = int CARD('a))"
  and 2: "class.nontriv TYPE('a) = (CARD('a) \<ge> 2)"
  unfolding poly_mod_type_def class.prime_card_def class.nontriv_def poly_mod_prime_type_def by auto

private lemma 3: "poly_mod_prime_type TYPE('b) m = (m = int CARD('b))"
  and 4: "class.prime_card TYPE('b :: prime_card) = prime CARD('b :: prime_card)" 
  unfolding poly_mod_type_def class.prime_card_def class.nontriv_def poly_mod_prime_type_def by auto

lemmas poly_mod_type_simps = 1 2 3 4
end


lemma remove_duplicate_premise: "(PROP P \<Longrightarrow> PROP P \<Longrightarrow> PROP Q) \<equiv> (PROP P \<Longrightarrow> PROP Q)" (is "?l \<equiv> ?r")
proof (intro Pure.equal_intr_rule)
  assume p: "PROP P" and ppq: "PROP ?l"
  from ppq[OF p p] show "PROP Q".
next
  assume p: "PROP P" and pq: "PROP ?r"
  from pq[OF p] show "PROP Q".
qed

context poly_mod_prime begin

lemma type_to_set:
  assumes type_def: "\<exists>(Rep :: 'b \<Rightarrow> int) Abs. type_definition Rep Abs {0 ..< p :: int}"
  shows "class.prime_card (TYPE('b))" (is ?a) and "p = int CARD('b)" (is ?b)
proof -
  from prime have p2: "p \<ge> 2" by (rule prime_ge_2_int)
  from type_def obtain rep :: "'b \<Rightarrow> int" and abs :: "int \<Rightarrow> 'b" where t: "type_definition rep abs {0 ..< p}" by auto
  have "card (UNIV :: 'b set) = card {0 ..< p}" using t by (rule type_definition.card)
  also have "\<dots> = p" using p2 by auto
  finally show ?b ..
  then show ?a unfolding class.prime_card_def using prime p2 by auto
qed
end

(* it will be nice to be able to automate this *)

lemmas (in poly_mod_type) prime_elem_m_dvdm_multD = prime_elem_dvd_multD
  [where 'a = "'a mod_ring poly",untransferred]
lemmas (in poly_mod_2) prime_elem_m_dvdm_multD = poly_mod_type.prime_elem_m_dvdm_multD
  [unfolded poly_mod_type_simps, internalize_sort "'a :: nontriv", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas(in poly_mod_prime_type) degree_m_mult_eq = degree_mult_eq
  [where 'a = "'a mod_ring", untransferred]
lemmas(in poly_mod_prime) degree_m_mult_eq = poly_mod_prime_type.degree_m_mult_eq
  [unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemma(in poly_mod_prime) irreducible\<^sub>d_lifting:
  assumes n: "n \<noteq> 0"
    and deg: "poly_mod.degree_m (p^n) f = degree_m f"
    and irr: "irreducible\<^sub>d_m f"
  shows "poly_mod.irreducible\<^sub>d_m (p^n) f"
proof -
  interpret q: poly_mod_2 "p^n" unfolding poly_mod_2_def using n m1 by auto
  show "q.irreducible\<^sub>d_m f"
  proof (rule q.irreducible\<^sub>d_mI)
    from deg irr show "q.degree_m f > 0" by (auto elim: irreducible\<^sub>d_mE)
    then have pdeg_f: "degree_m f \<noteq> 0" by (simp add: deg)
    note pMp_Mp = Mp_Mp_pow_is_Mp[OF n m1]
    fix g h
    assume deg_g: "degree g < q.degree_m f" and deg_h: "degree h < q.degree_m f"
      and eq: "q.eq_m f (g * h)"
    from eq have p_f: "f =m (g * h)" using pMp_Mp by metis
    have "\<not>g =m 0" and "\<not>h =m 0"
      apply (metis degree_0 mult_zero_left Mp_0 p_f pdeg_f poly_mod.mult_Mp(1))
      by (metis degree_0 mult_eq_0_iff Mp_0 mult_Mp(2) p_f pdeg_f)
    note [simp] = degree_m_mult_eq[OF this]
    from degree_m_le[of g] deg_g
    have 2: "degree_m g < degree_m f" by (fold deg, auto)
    from degree_m_le[of h] deg_h
    have 3: "degree_m h < degree_m f" by (fold deg, auto)
    from irreducible\<^sub>d_mD(2)[OF irr 2 3] p_f
    show False by auto
  qed
qed

(* Lifting UFD properties *)
lemmas (in poly_mod_prime_type) mset_factors_exist =
  mset_factors_exist[where 'a = "'a mod_ring poly",untransferred]
lemmas (in poly_mod_prime) mset_factors_exist = poly_mod_prime_type.mset_factors_exist
  [unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas (in poly_mod_prime_type) mset_factors_unique =
  mset_factors_unique[where 'a = "'a mod_ring poly",untransferred]
lemmas (in poly_mod_prime) mset_factors_unique = poly_mod_prime_type.mset_factors_unique
  [unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas (in poly_mod_prime_type) prime_elem_iff_irreducible =
  prime_elem_iff_irreducible[where 'a = "'a mod_ring poly",untransferred]
lemmas (in poly_mod_prime) prime_elem_iff_irreducible[simp] = poly_mod_prime_type.prime_elem_iff_irreducible
  [unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas (in poly_mod_prime_type) irreducible_connect =
  irreducible_connect_field[where 'a = "'a mod_ring", untransferred]
lemmas (in poly_mod_prime) irreducible_connect[simp] = poly_mod_prime_type.irreducible_connect
  [unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]

lemmas (in poly_mod_prime_type) irreducible_degree =
  irreducible_degree_field[where 'a = "'a mod_ring", untransferred]
lemmas (in poly_mod_prime) irreducible_degree = poly_mod_prime_type.irreducible_degree
  [unfolded poly_mod_type_simps, internalize_sort "'a :: prime_card", OF type_to_set, unfolded remove_duplicate_premise, cancel_type_definition, OF non_empty]


end
