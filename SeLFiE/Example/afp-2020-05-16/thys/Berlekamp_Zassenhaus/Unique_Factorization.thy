theory Unique_Factorization
  imports
    Polynomial_Interpolation.Ring_Hom_Poly
    Polynomial_Factorization.Polynomial_Divisibility
    "HOL-Library.Permutations" 
    "HOL-Computational_Algebra.Euclidean_Algorithm"
    Containers.Containers_Auxiliary (* only for a lemma *)
    Missing_Multiset2
    "HOL-Algebra.Divisibility"
begin

hide_const(open)
  Divisibility.prime
  Divisibility.irreducible

hide_fact(open)
  Divisibility.irreducible_def
  Divisibility.irreducibleI
  Divisibility.irreducibleD
  Divisibility.irreducibleE

hide_const (open) Rings.coprime

lemma irreducible_uminus [simp]:
  fixes a::"'a::idom"
  shows "irreducible (-a) \<longleftrightarrow> irreducible a"
  using irreducible_mult_unit_left[of "-1::'a"] by auto

context comm_monoid_mult begin

  definition coprime :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    where coprime_def': "coprime p q \<equiv> \<forall>r. r dvd p \<longrightarrow> r dvd q \<longrightarrow> r dvd 1"

  lemma coprimeI:
    assumes "\<And>r. r dvd p \<Longrightarrow> r dvd q \<Longrightarrow> r dvd 1"
    shows "coprime p q" using assms by (auto simp: coprime_def')

  lemma coprimeE:
    assumes "coprime p q"
        and "(\<And>r. r dvd p \<Longrightarrow> r dvd q \<Longrightarrow> r dvd 1) \<Longrightarrow> thesis"
    shows thesis using assms by (auto simp: coprime_def')

  lemma coprime_commute [ac_simps]:
    "coprime p q \<longleftrightarrow> coprime q p"
    by (auto simp add: coprime_def')

  lemma not_coprime_iff_common_factor:
    "\<not> coprime p q \<longleftrightarrow> (\<exists>r. r dvd p \<and> r dvd q \<and> \<not> r dvd 1)"
    by (auto simp add: coprime_def')

end

lemma (in algebraic_semidom) coprime_iff_coprime [simp, code]:
  "coprime = Rings.coprime"
  by (simp add: fun_eq_iff coprime_def coprime_def')

lemma (in comm_semiring_1) coprime_0 [simp]:
  "coprime p 0 \<longleftrightarrow> p dvd 1" "coprime 0 p \<longleftrightarrow> p dvd 1"
  by (auto intro: coprimeI elim: coprimeE dest: dvd_trans)

(**** until here ****)


(* TODO: move or...? *)
lemma dvd_rewrites: "dvd.dvd ((*)) = (dvd)" by (unfold dvd.dvd_def dvd_def, rule)


subsection \<open>Interfacing UFD properties\<close>
hide_const (open) Divisibility.irreducible

context comm_monoid_mult_isom begin
  lemma coprime_hom[simp]: "coprime (hom x) y' \<longleftrightarrow> coprime x (Hilbert_Choice.inv hom y')"
  proof-
    show ?thesis by (unfold coprime_def', fold ball_UNIV, subst surj[symmetric], simp)
  qed
  lemma coprime_inv_hom[simp]: "coprime (Hilbert_Choice.inv hom x') y \<longleftrightarrow> coprime x' (hom y)"
  proof-
    interpret inv: comm_monoid_mult_isom "Hilbert_Choice.inv hom"..
    show ?thesis by simp
  qed
end

subsubsection \<open>Original part\<close>

lemma dvd_dvd_imp_smult:
  fixes p q :: "'a :: idom poly"
  assumes pq: "p dvd q" and qp: "q dvd p" shows "\<exists>c. p = smult c q"
proof (cases "p = 0")
  case True then show ?thesis by auto
next
  case False
  from qp obtain r where r: "p = q * r" by (elim dvdE, auto)
  with False qp have r0: "r \<noteq> 0" and q0: "q \<noteq> 0" by auto
  with divides_degree[OF pq] divides_degree[OF qp] False
  have "degree p = degree q" by auto
  with r degree_mult_eq[OF q0 r0] have "degree r = 0" by auto
  from degree_0_id[OF this] obtain c where "r = [:c:]" by metis
  from r[unfolded this] show ?thesis by auto
qed

lemma dvd_const:
  assumes pq: "(p::'a::semidom poly) dvd q" and q0: "q \<noteq> 0" and degq: "degree q = 0"
  shows "degree p = 0"
proof-
  from dvdE[OF pq] obtain r where *: "q = p * r".
  with q0 have "p \<noteq> 0" "r \<noteq> 0" by auto
  from degree_mult_eq[OF this] degq * show "degree p = 0" by auto
qed

context Rings.dvd begin
  abbreviation ddvd (infix "ddvd" 40) where "x ddvd y \<equiv> x dvd y \<and> y dvd x"
  lemma ddvd_sym[sym]: "x ddvd y \<Longrightarrow> y ddvd x" by auto
end

context comm_monoid_mult begin
  lemma ddvd_trans[trans]: "x ddvd y \<Longrightarrow> y ddvd z \<Longrightarrow> x ddvd z" using dvd_trans by auto
  lemma ddvd_transp: "transp (ddvd)" by (intro transpI, fact ddvd_trans)
end

context comm_semiring_1 begin

definition mset_factors where "mset_factors F p \<equiv>
  F \<noteq> {#} \<and> (\<forall>f. f \<in># F \<longrightarrow> irreducible f) \<and> p = prod_mset F"

lemma mset_factorsI[intro!]:
  assumes "\<And>f. f \<in># F \<Longrightarrow> irreducible f" and "F \<noteq> {#}" and "prod_mset F = p"
  shows "mset_factors F p"
  unfolding mset_factors_def using assms by auto

lemma mset_factorsD:
  assumes "mset_factors F p"
  shows "f \<in># F \<Longrightarrow> irreducible f" and "F \<noteq> {#}" and "prod_mset F = p"
  using assms[unfolded mset_factors_def] by auto

lemma mset_factorsE[elim]:
  assumes "mset_factors F p"
      and "(\<And>f. f \<in># F \<Longrightarrow> irreducible f) \<Longrightarrow> F \<noteq> {#} \<Longrightarrow> prod_mset F = p \<Longrightarrow> thesis"
  shows thesis
  using assms[unfolded mset_factors_def] by auto

lemma mset_factors_imp_not_is_unit:
  assumes "mset_factors F p"
  shows "\<not> p dvd 1"
proof(cases F)
  case empty with assms show ?thesis by auto
next
  case (add f F)
  with assms have "\<not> f dvd 1" "p = f * prod_mset F" by (auto intro!: irreducible_not_unit)
  then show ?thesis by auto
qed

definition primitive_poly where "primitive_poly f \<equiv> \<forall>d. (\<forall>i. d dvd coeff f i) \<longrightarrow> d dvd 1"

end

lemma(in semidom) mset_factors_imp_nonzero:
  assumes "mset_factors F p"
  shows "p \<noteq> 0"
proof
  assume "p = 0"
  moreover from assms have "prod_mset F = p" by auto
  ultimately obtain f where "f \<in># F" "f = 0" by auto
  with assms show False by auto
qed

class ufd = idom +
  assumes mset_factors_exist: "\<And>x. x \<noteq> 0 \<Longrightarrow> \<not> x dvd 1 \<Longrightarrow> \<exists>F. mset_factors F x"
    and mset_factors_unique: "\<And>x F G. mset_factors F x \<Longrightarrow> mset_factors G x \<Longrightarrow> rel_mset (ddvd) F G"

subsubsection \<open>Connecting to HOL/Divisibility\<close>

context comm_semiring_1 begin

  abbreviation "mk_monoid \<equiv> \<lparr>carrier = UNIV - {0}, mult = (*), one = 1\<rparr>"

  lemma carrier_0[simp]: "x \<in> carrier mk_monoid \<longleftrightarrow> x \<noteq> 0" by auto

  lemmas mk_monoid_simps = carrier_0 monoid.simps

  abbreviation irred where "irred \<equiv> Divisibility.irreducible mk_monoid"
  abbreviation factor where "factor \<equiv> Divisibility.factor mk_monoid"
  abbreviation factors where "factors \<equiv> Divisibility.factors mk_monoid"
  abbreviation properfactor where "properfactor \<equiv> Divisibility.properfactor mk_monoid"

  lemma factors: "factors fs y \<longleftrightarrow> prod_list fs = y \<and> Ball (set fs) irred"
  proof -
    have "prod_list fs = foldr (*) fs 1" by (induct fs, auto)
    thus ?thesis unfolding factors_def by auto
  qed

  lemma factor: "factor x y \<longleftrightarrow> (\<exists>z. z \<noteq> 0 \<and> x * z = y)" unfolding factor_def by auto

  lemma properfactor_nz:
    shows "(y :: 'a) \<noteq> 0 \<Longrightarrow> properfactor x y \<longleftrightarrow> x dvd y \<and> \<not> y dvd x"
    by (auto simp: properfactor_def factor_def dvd_def)

  lemma mem_Units[simp]: "y \<in> Units mk_monoid \<longleftrightarrow> y dvd 1"
    unfolding dvd_def Units_def by (auto simp: ac_simps)

end

context idom begin
  lemma irred_0[simp]: "irred (0::'a)" by (unfold Divisibility.irreducible_def, auto simp: factor properfactor_def)
  lemma factor_idom[simp]: "factor (x::'a) y \<longleftrightarrow> (if y = 0 then x = 0 else x dvd y)"
    by (cases "y = 0"; auto intro: exI[of _ 1] elim: dvdE simp: factor)

  lemma associated_connect[simp]: "(\<sim>\<^bsub>mk_monoid\<^esub>) = (ddvd)" by (intro ext, unfold associated_def, auto)

  lemma essentially_equal_connect[simp]:
    "essentially_equal mk_monoid fs gs \<longleftrightarrow> rel_mset (ddvd) (mset fs) (mset gs)"
    by (auto simp: essentially_equal_def rel_mset_via_perm)

  lemma irred_idom_nz:
    assumes x0: "(x::'a) \<noteq> 0"
    shows "irred x \<longleftrightarrow> irreducible x"
    using x0 by (auto simp: irreducible_altdef Divisibility.irreducible_def properfactor_nz)


  lemma dvd_dvd_imp_unit_mult:
    assumes xy: "x dvd y" and yx: "y dvd x"
    shows "\<exists>z. z dvd 1 \<and> y = x * z"
  proof(cases "x = 0")
    case True with xy show ?thesis by (auto intro: exI[of _ 1])
  next
    case x0: False
    from xy obtain z where z: "y = x * z" by (elim dvdE, auto)
    from yx obtain w where w: "x = y * w" by (elim dvdE, auto)
    from z w have "x * (z * w) = x" by (auto simp: ac_simps)
    then have "z * w = 1" using x0 by auto
    with z show ?thesis by (auto intro: exI[of _ z])
  qed

  lemma irred_inner_nz:
    assumes x0: "x \<noteq> 0"
    shows "(\<forall>b. b dvd x \<longrightarrow> \<not> x dvd b \<longrightarrow> b dvd 1) \<longleftrightarrow> (\<forall>a b. x = a * b \<longrightarrow> a dvd 1 \<or> b dvd 1)" (is "?l \<longleftrightarrow> ?r")
  proof (intro iffI allI impI)
    assume l: ?l
    fix a b
    assume xab: "x = a * b"
    then have ax: "a dvd x" and bx: "b dvd x" by auto
    { assume a1: "\<not> a dvd 1"
      with l ax have xa: "x dvd a" by auto
      from dvd_dvd_imp_unit_mult[OF ax xa] obtain z where z1: "z dvd 1" and xaz: "x = a * z" by auto
      from xab x0 have "a \<noteq> 0" by auto
      with xab xaz have "b = z" by auto
      with z1 have "b dvd 1" by auto
    }
    then show "a dvd 1 \<or> b dvd 1" by auto
  next
    assume r: ?r
    fix b assume bx: "b dvd x" and xb: "\<not> x dvd b"
    then obtain a where xab: "x = a * b" by (elim dvdE, auto simp: ac_simps)
    with r consider "a dvd 1" | "b dvd 1" by auto
    then show "b dvd 1"
    proof(cases)
      case 2 then show ?thesis by auto
    next
      case 1
      then obtain c where ac1: "a * c = 1" by (elim dvdE, auto)
      from xab have "x * c = b * (a * c)" by (auto simp: ac_simps)
      with ac1 have "x * c = b" by auto
      then have "x dvd b" by auto
      with xb show ?thesis by auto
    qed
  qed

  lemma irred_idom[simp]: "irred x \<longleftrightarrow> x = 0 \<or> irreducible x"
  by (cases "x = 0"; simp add: irred_idom_nz irred_inner_nz irreducible_def)

  lemma assumes "x \<noteq> 0" and "factors fs x" and "f \<in> set fs" shows "f \<noteq> 0"
    using assms by (auto simp: factors)

  lemma factors_as_mset_factors:
    assumes x0: "x \<noteq> 0" and x1: "x \<noteq> 1"
    shows "factors fs x \<longleftrightarrow> mset_factors (mset fs) x" using assms
    by (auto simp: factors prod_mset_prod_list)


end

context ufd begin
  interpretation comm_monoid_cancel: comm_monoid_cancel "mk_monoid::'a monoid"
    apply (unfold_locales)
    apply simp_all
    using mult_left_cancel
    apply (auto simp: ac_simps)
    done
  lemma factors_exist:
    assumes "a \<noteq> 0"
    and "\<not> a dvd 1"
    shows "\<exists>fs. set fs \<subseteq> UNIV - {0} \<and> factors fs a"
  proof-
    from mset_factors_exist[OF assms]
    obtain F where "mset_factors F a" by auto
    also from ex_mset obtain fs where "F = mset fs" by metis
    finally have fs: "mset_factors (mset fs) a".
    then have "factors fs a" using assms by (subst factors_as_mset_factors, auto)
    moreover have "set fs \<subseteq> UNIV - {0}" using fs by (auto elim!: mset_factorsE)
    ultimately show ?thesis by auto
  qed

  lemma factors_unique:
    assumes fs: "factors fs a"
       and gs: "factors gs a"
       and a0: "a \<noteq> 0"
       and a1: "\<not> a dvd 1"
    shows "rel_mset (ddvd) (mset fs) (mset gs)"
  proof-
    from a1 have "a \<noteq> 1" by auto
    with a0 fs gs have "mset_factors (mset fs) a" "mset_factors (mset gs) a" by (unfold factors_as_mset_factors)
    from mset_factors_unique[OF this] show ?thesis.
  qed

  lemma factorial_monoid: "factorial_monoid (mk_monoid :: 'a monoid)"
    by (unfold_locales; auto simp add: factors_exist factors_unique)

end

lemma (in idom) factorial_monoid_imp_ufd:
  assumes "factorial_monoid (mk_monoid :: 'a monoid)"
  shows "class.ufd ((*) :: 'a \<Rightarrow> _) 1 (+) 0 (-) uminus"
proof (unfold_locales)
  interpret factorial_monoid "mk_monoid :: 'a monoid" by (fact assms)
  {
    fix x assume x: "x \<noteq> 0" "\<not> x dvd 1"
    note * = factors_exist[simplified, OF this]
    with x show "\<exists>F. mset_factors F x" by (subst(asm) factors_as_mset_factors, auto)
  }
  fix x F G assume FG: "mset_factors F x" "mset_factors G x"
  with mset_factors_imp_not_is_unit have x1: "\<not> x dvd 1" by auto
  from FG(1) have x0: "x \<noteq> 0" by (rule mset_factors_imp_nonzero)
  obtain fs gs where fsgs: "F = mset fs" "G = mset gs" using ex_mset by metis
  note FG = FG[unfolded this]
  then have 0: "0 \<notin> set fs" "0 \<notin> set gs" by (auto elim!: mset_factorsE)
  from x1 have "x \<noteq> 1" by auto
  note FG[folded factors_as_mset_factors[OF x0 this]]
  from factors_unique[OF this, simplified, OF x0 x1, folded fsgs] 0
  show "rel_mset (ddvd) F G" by auto
qed




subsection \<open>Preservation of Irreducibility\<close>


locale comm_semiring_1_hom = comm_monoid_mult_hom hom + zero_hom hom
  for hom :: "'a :: comm_semiring_1 \<Rightarrow> 'b :: comm_semiring_1"

locale irreducibility_hom = comm_semiring_1_hom +
  assumes irreducible_imp_irreducible_hom: "irreducible a \<Longrightarrow> irreducible (hom a)"
begin
  lemma hom_mset_factors:
    assumes F: "mset_factors F p"
    shows "mset_factors (image_mset hom F) (hom p)"
  proof (unfold mset_factors_def, intro conjI allI impI)
    from F show "hom p = prod_mset (image_mset hom F)" "image_mset hom F \<noteq> {#}" by (auto simp: hom_distribs)
    fix f' assume "f' \<in># image_mset hom F"
    then obtain f where f: "f \<in># F" and f'f: "f' = hom f" by auto
    with F irreducible_imp_irreducible_hom show "irreducible f'" unfolding f'f by auto
  qed
end

locale unit_preserving_hom = comm_semiring_1_hom +
  assumes is_unit_hom_if: "\<And>x. hom x dvd 1 \<Longrightarrow> x dvd 1"
begin
  lemma is_unit_hom_iff[simp]: "hom x dvd 1 \<longleftrightarrow> x dvd 1" using is_unit_hom_if hom_dvd by force

  lemma irreducible_hom_imp_irreducible:
    assumes irr: "irreducible (hom a)" shows "irreducible a"
  proof (intro irreducibleI)
    from irr show "a \<noteq> 0" by auto
    from irr show "\<not> a dvd 1" by (auto dest: irreducible_not_unit)
    fix b c assume "a = b * c"
    then have "hom a = hom b * hom c" by (simp add: hom_distribs)
    with irr have "hom b dvd 1 \<or> hom c dvd 1" by (auto dest: irreducibleD)
    then show "b dvd 1 \<or> c dvd 1" by simp
  qed
end

locale factor_preserving_hom = unit_preserving_hom + irreducibility_hom
begin
  lemma irreducible_hom[simp]: "irreducible (hom a) \<longleftrightarrow> irreducible a"
    using irreducible_hom_imp_irreducible irreducible_imp_irreducible_hom by metis
end

lemma factor_preserving_hom_comp:
  assumes f: "factor_preserving_hom f" and g: "factor_preserving_hom g"
  shows "factor_preserving_hom (f o g)"
proof-
  interpret f: factor_preserving_hom f by (rule f)
  interpret g: factor_preserving_hom g by (rule g)
  show ?thesis by (unfold_locales, auto simp: hom_distribs)
qed

context comm_semiring_isom begin
  sublocale unit_preserving_hom by (unfold_locales, auto)
  sublocale factor_preserving_hom
  proof (standard)
    fix a :: 'a
    assume "irreducible a"
    note a = this[unfolded irreducible_def]
    show "irreducible (hom a)"
    proof (rule ccontr)
      assume "\<not> irreducible (hom a)"
      from this[unfolded Factorial_Ring.irreducible_def,simplified] a
      obtain hb hc where eq: "hom a = hb * hc" and nu: "\<not> hb dvd 1" "\<not> hc dvd 1" by auto
      from bij obtain b where hb: "hb = hom b" by (elim bij_pointE)
      from bij obtain c where hc: "hc = hom c" by (elim bij_pointE)
      from eq[unfolded hb hc, folded hom_mult] have "a = b * c" by auto
      with nu hb hc have "a = b * c" "\<not> b dvd 1" "\<not> c dvd 1" by auto
      with a show False by auto
    qed
  qed
end


subsubsection\<open>Back to divisibility\<close>

lemma(in comm_semiring_1) mset_factors_mult:
  assumes F: "mset_factors F a"
      and G: "mset_factors G b"
  shows "mset_factors (F+G) (a*b)"
proof(intro mset_factorsI)
  fix f assume "f \<in># F + G"
  then consider "f \<in># F" | "f \<in># G" by auto
  then show "irreducible f" by(cases, insert F G, auto)
qed (insert F G, auto)

lemma(in ufd) dvd_imp_subset_factors:
  assumes ab: "a dvd b"
      and F: "mset_factors F a"
      and G: "mset_factors G b"
  shows "\<exists>G'. G' \<subseteq># G \<and> rel_mset (ddvd) F G'"
proof-
  from F G have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" by (simp_all add: mset_factors_imp_nonzero)
  from ab obtain c where c: "b = a * c" by (elim dvdE, auto)
  with b0 have c0: "c \<noteq> 0" by auto
  show ?thesis
  proof(cases "c dvd 1")
    case True
    show ?thesis
      proof(cases F)
        case empty with F show ?thesis by auto
      next
        case (add f F')
          with F
          have a: "f * prod_mset F' = a"
           and F': "\<And>f. f \<in># F' \<Longrightarrow> irreducible f"
           and irrf: "irreducible f" by auto
          from irrf have f0: "f \<noteq> 0" and f1: "\<not>f dvd 1" by (auto dest: irreducible_not_unit)
          from a c have "(f * c) * prod_mset F' = b" by (auto simp: ac_simps)
          moreover {
            have "irreducible (f * c)" using True irrf by (subst irreducible_mult_unit_right)
            with F' irrf have "\<And>f'. f' \<in># F' + {#f * c#} \<Longrightarrow> irreducible f'" by auto
          }
          ultimately have "mset_factors (F' + {#f * c#}) b" by (intro mset_factorsI, auto)
          from mset_factors_unique[OF this G]
          have F'G: "rel_mset (ddvd) (F' + {#f * c#}) G".
          from True add have FF': "rel_mset (ddvd) F (F' + {#f * c#})"
            by (auto simp add: multiset.rel_refl intro!: rel_mset_Plus)
          have "rel_mset (ddvd) F G"
            apply(rule transpD[OF multiset.rel_transp[OF transpI] FF' F'G])
            using ddvd_trans.
          then show ?thesis by auto
      qed
  next
    case False
      from mset_factors_exist[OF c0 this] obtain H where H: "mset_factors H c" by auto
      from c mset_factors_mult[OF F H] have "mset_factors (F + H) b" by auto
      note mset_factors_unique[OF this G]
      from rel_mset_split[OF this] obtain G1 G2
        where "G = G1 + G2" "rel_mset (ddvd) F G1" "rel_mset (ddvd) H G2" by auto
      then show ?thesis by (intro exI[of _ "G1"], auto)
  qed
qed

lemma(in idom) irreducible_factor_singleton:
  assumes a: "irreducible a"
  shows "mset_factors F a \<longleftrightarrow> F = {#a#}"
proof(cases F)
  case empty with mset_factorsD show ?thesis by auto
next
  case (add f F')
  show ?thesis
  proof
    assume F: "mset_factors F a"
    from add mset_factorsD[OF F] have *: "a = f * prod_mset F'" by auto
    then have fa: "f dvd a" by auto
    from * a have f0: "f \<noteq> 0" by auto
    from add have "f \<in># F" by auto
    with F have f: "irreducible f" by auto
    from add have "F' \<subseteq># F" by auto
    then have unitemp: "prod_mset F' dvd 1 \<Longrightarrow> F' = {#}"
    proof(induct F')
      case empty then show ?case by auto
    next
      case (add f F')
        from add have "f \<in># F" by (simp add: mset_subset_eq_insertD)
        with F irreducible_not_unit have "\<not> f dvd 1" by auto
        then have "\<not> (prod_mset F' * f) dvd 1" by simp
        with add show ?case by auto
    qed
    show "F = {#a#}"
    proof(cases "a dvd f")
      case True
        then obtain r where "f = a * r" by (elim dvdE, auto)
        with * have "f = (r * prod_mset F') * f" by (auto simp: ac_simps)
        with f0 have "r * prod_mset F' = 1" by auto
        then have "prod_mset F' dvd 1" by (metis dvd_triv_right)
        with unitemp * add show ?thesis by auto
    next
      case False with fa a f show ?thesis by (auto simp: irreducible_altdef)
    qed
  qed (insert a, auto)
qed


lemma(in ufd) irreducible_dvd_imp_factor:
  assumes ab: "a dvd b"
      and a: "irreducible a"
      and G: "mset_factors G b"
  shows "\<exists>g \<in># G. a ddvd g"
proof-
  from a have "mset_factors {#a#} a" by auto
  from dvd_imp_subset_factors[OF ab this G]
  obtain G' where G'G: "G' \<subseteq># G" and rel: "rel_mset (ddvd) {#a#} G'" by auto
  with rel_mset_size size_1_singleton_mset size_single
  obtain g where gG': "G' = {#g#}" by fastforce
  from rel[unfolded this rel_mset_def]
  have "a ddvd g" by auto
  with gG' G'G show ?thesis by auto
qed

lemma(in idom) prod_mset_remove_units:
  "prod_mset F ddvd prod_mset {# f \<in># F. \<not>f dvd 1 #}"
proof(induct F)
  case (add f F) then show ?case by (cases "f = 0", auto)
qed auto

lemma(in comm_semiring_1) mset_factors_imp_dvd:
  assumes "mset_factors F x" and "f \<in># F" shows "f dvd x"
  using assms by (simp add: dvd_prod_mset mset_factors_def)

lemma(in ufd) prime_elem_iff_irreducible[iff]:
  "prime_elem x \<longleftrightarrow> irreducible x"
proof (intro iffI, fact prime_elem_imp_irreducible, rule prime_elemI)
  assume r: "irreducible x"
  then show x0: "x \<noteq> 0" and x1: "\<not> x dvd 1" by (auto dest: irreducible_not_unit)
  from irreducible_factor_singleton[OF r]
  have *: "mset_factors {#x#} x" by auto
  fix a b
  assume "x dvd a * b"
  then obtain c where abxc: "a * b = x * c" by (elim dvdE, auto)
  show "x dvd a \<or> x dvd b"
  proof(cases "c = 0 \<or> a = 0 \<or> b = 0")
    case True with abxc show ?thesis by auto
  next
    case False
    then have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" and c0: "c \<noteq> 0" by auto
    from x0 c0 have xc0: "x * c \<noteq> 0" by auto
    from x1 have xc1: "\<not> x * c dvd 1" by auto
    show ?thesis
    proof (cases "a dvd 1 \<or> b dvd 1")
      case False
      then have a1: "\<not> a dvd 1" and b1: "\<not> b dvd 1" by auto
      from mset_factors_exist[OF a0 a1]
      obtain F where Fa: "mset_factors F a" by auto
      then have F0: "F \<noteq> {#}" by auto
      from mset_factors_exist[OF b0 b1]
      obtain G where Gb: "mset_factors G b" by auto
      then have G0: "G \<noteq> {#}" by auto
      from mset_factors_mult[OF Fa Gb]
      have FGxc: "mset_factors (F + G) (x * c)" by (simp add: abxc)
      show ?thesis
      proof (cases "c dvd 1")
        case True
        from r irreducible_mult_unit_right[OF this] have "irreducible (x*c)" by simp
        note irreducible_factor_singleton[OF this] FGxc
        with F0 G0 have False by (cases F; cases G; auto)
        then show ?thesis by auto
      next
        case False
        from mset_factors_exist[OF c0 this] obtain H where "mset_factors H c" by auto
        with * have xHxc: "mset_factors (add_mset x H) (x * c)" by force
        note rel = mset_factors_unique[OF this FGxc]
        obtain hs where "mset hs = H" using ex_mset by auto
        then have "mset (x#hs) = add_mset x H" by auto
        from rel_mset_free[OF rel this]
        obtain jjs where jjsGH: "mset jjs = F + G" and rel: "list_all2 (ddvd) (x # hs) jjs" by auto
        then obtain j js where jjs: "jjs = j # js" by (cases jjs, auto)
        with rel have xj: "x ddvd j" by auto
        from jjs jjsGH have j: "j \<in> set_mset (F + G)" by (intro union_single_eq_member, auto)
        from j consider "j \<in># F" | "j \<in># G" by auto
        then show ?thesis
        proof(cases)
          case 1
          with Fa have "j dvd a" by (auto intro: mset_factors_imp_dvd)
          with xj dvd_trans have "x dvd a" by auto
          then show ?thesis by auto
        next
          case 2
          with Gb have "j dvd b" by (auto intro: mset_factors_imp_dvd)
          with xj dvd_trans have "x dvd b" by auto
          then show ?thesis by auto
        qed
      qed
    next
      case True
      then consider "a dvd 1" | "b dvd 1" by auto
      then show ?thesis
      proof(cases)
        case 1
        then obtain d where ad: "a * d = 1" by (elim dvdE, auto)
        from abxc have "x * (c * d) = a * b * d" by (auto simp: ac_simps)
        also have "... = a * d * b" by (auto simp: ac_simps)
        finally have "x dvd b" by (intro dvdI, auto simp: ad)
        then show ?thesis by auto
      next
        case 2
        then obtain d where bd: "b * d = 1" by (elim dvdE, auto)
        from abxc have "x * (c * d) = a * b * d" by (auto simp: ac_simps)
        also have "... = (b * d) * a" by (auto simp: ac_simps)
        finally have "x dvd a" by (intro dvdI, auto simp:bd)
        then show ?thesis by auto
      qed
    qed
  qed
qed

subsection\<open>Results for GCDs etc.\<close>

lemma prod_list_remove1: "(x :: 'b :: comm_monoid_mult) \<in> set xs \<Longrightarrow> prod_list (remove1 x xs) * x = prod_list xs"
  by (induct xs, auto simp: ac_simps)

(* Isabelle 2015-style and generalized gcd-class without normalization and factors *)
class comm_monoid_gcd = gcd + comm_semiring_1 +
  assumes gcd_dvd1[iff]: "gcd a b dvd a"
      and gcd_dvd2[iff]: "gcd a b dvd b"
      and gcd_greatest: "c dvd a \<Longrightarrow> c dvd b \<Longrightarrow> c dvd gcd a b"
begin

  lemma gcd_0_0[simp]: "gcd 0 0 = 0"
    using gcd_greatest[OF dvd_0_right dvd_0_right, of 0] by auto

  lemma gcd_zero_iff[simp]: "gcd a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  proof
    assume "gcd a b = 0"
    from gcd_dvd1[of a b, unfolded this] gcd_dvd2[of a b, unfolded this]
    show "a = 0 \<and> b = 0" by auto
  qed auto

  lemma gcd_zero_iff'[simp]: "0 = gcd a b \<longleftrightarrow> a = 0 \<and> b = 0"
    using gcd_zero_iff by metis

  lemma dvd_gcd_0_iff[simp]:
    shows "x dvd gcd 0 a \<longleftrightarrow> x dvd a" (is ?g1)
      and "x dvd gcd a 0 \<longleftrightarrow> x dvd a" (is ?g2)
  proof-
    have "a dvd gcd a 0" "a dvd gcd 0 a" by (auto intro: gcd_greatest)
    with dvd_refl show ?g1 ?g2 by (auto dest: dvd_trans)
  qed

  lemma gcd_dvd_1[simp]: "gcd a b dvd 1 \<longleftrightarrow> coprime a b"
    using dvd_trans[OF gcd_greatest[of _ a b], of _ 1]
    by (cases "a = 0 \<and> b = 0") (auto intro!: coprimeI elim: coprimeE)

  lemma dvd_imp_gcd_dvd_gcd: "b dvd c \<Longrightarrow> gcd a b dvd gcd a c"
    by (meson gcd_dvd1 gcd_dvd2 gcd_greatest dvd_trans)

  definition listgcd :: "'a list \<Rightarrow> 'a" where
    "listgcd xs = foldr gcd xs 0"

  lemma listgcd_simps[simp]: "listgcd [] = 0" "listgcd (x # xs) = gcd x (listgcd xs)"
    by (auto simp: listgcd_def)

  lemma listgcd: "x \<in> set xs \<Longrightarrow> listgcd xs dvd x" 
  proof (induct xs)
    case (Cons y ys)
    show ?case
    proof (cases "x = y")
      case False
      with Cons have dvd: "listgcd ys dvd x" by auto
      thus ?thesis unfolding listgcd_simps using dvd_trans by blast
    next
      case True
      thus ?thesis unfolding listgcd_simps using dvd_trans by blast
    qed
  qed simp

  lemma listgcd_greatest: "(\<And> x. x \<in> set xs \<Longrightarrow> y dvd x) \<Longrightarrow> y dvd listgcd xs"
    by (induct xs arbitrary:y, auto intro: gcd_greatest)

end


context Rings.dvd begin

  definition "is_gcd x a b \<equiv> x dvd a \<and> x dvd b \<and> (\<forall>y. y dvd a \<longrightarrow> y dvd b \<longrightarrow> y dvd x)"

  definition "some_gcd a b \<equiv> SOME x. is_gcd x a b"

  lemma is_gcdI[intro!]:
    assumes "x dvd a" "x dvd b" "\<And>y. y dvd a \<Longrightarrow> y dvd b \<Longrightarrow> y dvd x"
    shows "is_gcd x a b" by (insert assms, auto simp: is_gcd_def)

  lemma is_gcdE[elim!]:
    assumes "is_gcd x a b"
        and "x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> (\<And>y. y dvd a \<Longrightarrow> y dvd b \<Longrightarrow> y dvd x) \<Longrightarrow> thesis"
    shows thesis by (insert assms, auto simp: is_gcd_def)

  lemma is_gcd_some_gcdI:
    assumes "\<exists>x. is_gcd x a b" shows "is_gcd (some_gcd a b) a b"
    by (unfold some_gcd_def, rule someI_ex[OF assms])

end

context comm_semiring_1 begin

  lemma some_gcd_0[intro!]: "is_gcd (some_gcd a 0) a 0" "is_gcd (some_gcd 0 b) 0 b"
    by (auto intro!: is_gcd_some_gcdI intro: exI[of _ a] exI[of _ b])

  lemma some_gcd_0_dvd[intro!]:
    "some_gcd a 0 dvd a" "some_gcd 0 b dvd b" using some_gcd_0 by auto

  lemma dvd_some_gcd_0[intro!]:
    "a dvd some_gcd a 0" "b dvd some_gcd 0 b" using some_gcd_0[of a] some_gcd_0[of b] by auto

end

context idom begin

  lemma is_gcd_connect:
    assumes "a \<noteq> 0" "b \<noteq> 0" shows "isgcd mk_monoid x a b \<longleftrightarrow> is_gcd x a b"
    using assms by (force simp: isgcd_def)

  lemma some_gcd_connect:
    assumes "a \<noteq> 0" and "b \<noteq> 0" shows "somegcd mk_monoid a b = some_gcd a b"
    using assms by (auto intro!: arg_cong[of _ _ Eps] simp: is_gcd_connect some_gcd_def somegcd_def)
end

context comm_monoid_gcd
begin
  lemma is_gcd_gcd: "is_gcd (gcd a b) a b" using gcd_greatest by auto
  lemma is_gcd_some_gcd: "is_gcd (some_gcd a b) a b" by (insert is_gcd_gcd, auto intro!: is_gcd_some_gcdI)
  lemma gcd_dvd_some_gcd: "gcd a b dvd some_gcd a b" using is_gcd_some_gcd by auto
  lemma some_gcd_dvd_gcd: "some_gcd a b dvd gcd a b" using is_gcd_some_gcd by (auto intro: gcd_greatest)
  lemma some_gcd_ddvd_gcd: "some_gcd a b ddvd gcd a b" by (auto intro: gcd_dvd_some_gcd some_gcd_dvd_gcd)
  lemma some_gcd_dvd: "some_gcd a b dvd d \<longleftrightarrow> gcd a b dvd d" "d dvd some_gcd a b \<longleftrightarrow> d dvd gcd a b"
    using some_gcd_ddvd_gcd[of a b] by (auto dest:dvd_trans)

end

class idom_gcd = comm_monoid_gcd + idom
begin

  interpretation raw: comm_monoid_cancel "mk_monoid :: 'a monoid"
    by (unfold_locales, auto intro: mult_commute mult_assoc)

  interpretation raw: gcd_condition_monoid "mk_monoid :: 'a monoid"
    by (unfold_locales, auto simp: is_gcd_connect intro!: exI[of _ "gcd _ _"] dest: gcd_greatest)

  lemma gcd_mult_ddvd:
    "d * gcd a b ddvd gcd (d * a) (d * b)"
  proof (cases "d = 0")
    case True then show ?thesis by auto
  next
    case d0: False
    show ?thesis
    proof (cases "a = 0 \<or> b = 0")
      case False
      note some_gcd_ddvd_gcd[of a b]
      with d0 have "d * gcd a b ddvd d * some_gcd a b" by auto
      also have "d * some_gcd a b ddvd some_gcd (d * a) (d * b)"
        using False d0 raw.gcd_mult by (simp add: some_gcd_connect)
      also note some_gcd_ddvd_gcd
      finally show ?thesis.
    next
      case True
      with d0 show ?thesis
        apply (elim disjE)
         apply (rule ddvd_trans[of _ "d * b"]; force)
         apply (rule ddvd_trans[of _ "d * a"]; force)
        done
    qed
  qed

  lemma gcd_greatest_mult: assumes cad: "c dvd a * d" and cbd: "c dvd b * d"
    shows "c dvd gcd a b * d"
  proof-
    from gcd_greatest[OF assms] have c: "c dvd gcd (d * a) (d * b)" by (auto simp: ac_simps)
    note gcd_mult_ddvd[of d a b]
    then have "gcd (d * a) (d * b) dvd gcd a b * d" by (auto simp: ac_simps)
    from dvd_trans[OF c this] show ?thesis .
  qed

  lemma listgcd_greatest_mult: "(\<And> x :: 'a. x \<in> set xs \<Longrightarrow> y dvd x * z) \<Longrightarrow> y dvd listgcd xs * z"
  proof (induct xs)
    case (Cons x xs)
    from Cons have "y dvd x * z" "y dvd listgcd xs * z" by auto
    thus ?case unfolding listgcd_simps by (rule gcd_greatest_mult)
  qed (simp)

  lemma dvd_factor_mult_gcd:
    assumes dvd: "k dvd p * q" "k dvd p * r"
      and q0: "q \<noteq> 0" and r0: "r \<noteq> 0"
    shows "k dvd p * gcd q r" 
  proof -
    from dvd gcd_greatest[of k "p * q" "p * r"]
    have "k dvd gcd (p * q) (p * r)" by simp
    also from gcd_mult_ddvd[of p q r]
    have "... dvd (p * gcd q r)" by auto
    finally show ?thesis .
  qed

  lemma coprime_mult_cross_dvd:
    assumes coprime: "coprime p q" and eq: "p' * p = q' * q"
    shows "p dvd q'" (is ?g1) and "q dvd p'" (is ?g2)
  proof (atomize(full), cases "p = 0 \<or> q = 0")
    case True
    then show "?g1 \<and> ?g2"
    proof
      assume p0: "p = 0" with coprime have "q dvd 1" by auto
      with eq p0 show ?thesis by auto
    next
      assume q0: "q = 0" with coprime have "p dvd 1" by auto
      with eq q0 show ?thesis by auto
    qed
  next
    case False
    {
      fix p q r p' q' :: 'a
      assume cop: "coprime p q" and eq: "p' * p = q' * q" and p: "p \<noteq> 0" and q: "q \<noteq> 0"
         and r: "r dvd p" "r dvd q"
      let ?gcd = "gcd q p"
      from eq have "p' * p dvd q' * q" by auto
      hence d1: "p dvd q' * q" by (rule dvd_mult_right)
      have d2: "p dvd q' * p" by auto
      from dvd_factor_mult_gcd[OF d1 d2 q p] have 1: "p dvd q' * ?gcd" .
      from q p have 2: "?gcd dvd q" by auto
      from q p have 3: "?gcd dvd p" by auto
      from cop[unfolded coprime_def', rule_format, OF 3 2] have "?gcd dvd 1" .
      from 1 dvd_mult_unit_iff[OF this] have "p dvd q'" by auto
    } note main = this
    from main[OF coprime eq,of 1] False coprime coprime_commute main[OF _ eq[symmetric], of 1]
    show "?g1 \<and> ?g2" by auto
  qed

end

subclass (in ring_gcd) idom_gcd by (unfold_locales, auto)

lemma coprime_rewrites: "comm_monoid_mult.coprime ((*)) 1 = coprime"
  apply (intro ext)
  apply (subst comm_monoid_mult.coprime_def')
  apply (unfold_locales)
  apply (unfold dvd_rewrites)
  apply (fold coprime_def') ..

(* TODO: incorporate into the default class hierarchy *)
locale gcd_condition =
  fixes ty :: "'a :: idom itself"
  assumes gcd_exists: "\<And>a b :: 'a. \<exists>x. is_gcd x a b"
begin
  sublocale idom_gcd "(*)" "1 :: 'a" "(+)" 0 "(-)" uminus some_gcd 
    rewrites "dvd.dvd ((*)) = (dvd)"
        and "comm_monoid_mult.coprime ((*) ) 1 = Unique_Factorization.coprime"
  proof-
    have "is_gcd (some_gcd a b) a b" for a b :: 'a by (intro is_gcd_some_gcdI gcd_exists)
    from this[unfolded is_gcd_def]
    show "class.idom_gcd (*) (1 :: 'a) (+) 0 (-) uminus some_gcd" by (unfold_locales, auto simp: dvd_rewrites)
  qed (simp_all add: dvd_rewrites coprime_rewrites)
end

instance semiring_gcd \<subseteq> comm_monoid_gcd by (intro_classes, auto)

lemma listgcd_connect: "listgcd = gcd_list"
proof (intro ext)
  fix xs :: "'a list"
  show "listgcd xs = gcd_list xs" by(induct xs, auto)
qed

interpretation some_gcd: gcd_condition "TYPE('a::ufd)"
proof(unfold_locales, intro exI)
  interpret factorial_monoid "mk_monoid :: 'a monoid" by (fact factorial_monoid)
  note d = dvd.dvd_def some_gcd_def carrier_0
  fix a b :: 'a
  show "is_gcd (some_gcd a b) a b"
  proof (cases "a = 0 \<or> b = 0")
    case True
    thus ?thesis using some_gcd_0 by auto
  next
    case False
    with gcdof_exists[of a b]
    show ?thesis by (auto intro!: is_gcd_some_gcdI simp add: is_gcd_connect some_gcd_connect)
  qed
qed

lemma some_gcd_listgcd_dvd_listgcd: "some_gcd.listgcd xs dvd listgcd xs"
  by (induct xs, auto simp:some_gcd_dvd intro:dvd_imp_gcd_dvd_gcd)

lemma listgcd_dvd_some_gcd_listgcd: "listgcd xs dvd some_gcd.listgcd xs"
  by (induct xs, auto simp:some_gcd_dvd intro:dvd_imp_gcd_dvd_gcd)

context factorial_ring_gcd begin

text \<open>Do not declare the following as subclass, to avoid conflict in
  \<open>field \<subseteq> gcd_condition\<close> vs. \<open>factorial_ring_gcd \<subseteq> gcd_condition\<close>.
\<close>
sublocale as_ufd: ufd
proof(unfold_locales, goal_cases)
  case (1 x)
  from prime_factorization_exists[OF \<open>x \<noteq> 0\<close>]
  obtain F where f: "\<And>f. f \<in># F \<Longrightarrow> prime_elem f" 
             and Fx: "normalize (prod_mset F) = normalize x" by auto
  from associatedE2[OF Fx] obtain u where u: "is_unit u" "x = u * prod_mset F"
    by blast
  from \<open>\<not> is_unit x\<close> Fx have "F \<noteq> {#}" by auto
  then obtain g G where F: "F = add_mset g G" by (cases F, auto)
  then have "g \<in># F" by auto
  with f[OF this]prime_elem_iff_irreducible
    irreducible_mult_unit_left[OF unit_factor_is_unit[OF \<open>x \<noteq> 0\<close>]]
  have g: "irreducible (u * g)" using u(1)
    by (subst irreducible_mult_unit_left) simp_all
  show ?case
  proof (intro exI conjI mset_factorsI)
    show "prod_mset (add_mset (u * g) G) = x"
      using \<open>x \<noteq> 0\<close> by (simp add: F ac_simps u)
    fix f assume "f \<in># add_mset (u * g) G"
    with f[unfolded F] g prime_elem_iff_irreducible
    show "irreducible f" by auto
  qed auto
next
  case (2 x F G)
  note transpD[OF multiset.rel_transp[OF ddvd_transp],trans]
  obtain fs where F: "F = mset fs" by (metis ex_mset)
  have "list_all2 (ddvd) fs (map normalize fs)" by (intro list_all2_all_nthI, auto)
  then have FH: "rel_mset (ddvd) F (image_mset normalize F)" by (unfold rel_mset_def F, force)
  also
  have FG: "image_mset normalize F = image_mset normalize G"
  proof (intro prime_factorization_unique'')
    from 2 have xF: "x = prod_mset F" and xG: "x = prod_mset G" by auto
    from xF have "normalize x = normalize (prod_mset (image_mset normalize F))"
      by (simp add: normalize_prod_mset_normalize)
    with xG have nFG: "\<dots> = normalize (prod_mset (image_mset normalize G))"
      by (simp_all add: normalize_prod_mset_normalize)
    then show "normalize (\<Prod>i\<in>#image_mset normalize F. i) =
               normalize (\<Prod>i\<in>#image_mset normalize G. i)" by auto
  next
    from 2 prime_elem_iff_irreducible have "f \<in># F \<Longrightarrow> prime_elem f" "g \<in># G \<Longrightarrow> prime_elem g" for f g
     by (auto intro: prime_elemI)
    then show " Multiset.Ball (image_mset normalize F) prime"
      "Multiset.Ball (image_mset normalize G) prime" by auto
  qed
  also
    obtain gs where G: "G = mset gs" by (metis ex_mset)
    have "list_all2 ((ddvd)\<inverse>\<inverse>) gs (map normalize gs)" by (intro list_all2_all_nthI, auto)
    then have "rel_mset (ddvd) (image_mset normalize G) G"
      by (subst multiset.rel_flip[symmetric], unfold rel_mset_def G, force)
  finally show ?case.
qed

end

instance int :: ufd by (intro class.ufd.of_class.intro as_ufd.ufd_axioms)
instance int :: idom_gcd by (intro_classes, auto)

instance field \<subseteq> ufd by (intro_classes, auto simp: dvd_field_iff)

end
