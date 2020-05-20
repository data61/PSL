(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>A Combined Factorization Algorithm for Polynomials over GF(p)\<close>

subsection\<open>Type Based Version\<close>
text \<open>We combine Berlekamp's algorithm with the distinct degree factorization
  to obtain an efficient factorization algorithm for square-free polynomials in GF(p).\<close>

theory Finite_Field_Factorization
imports Berlekamp_Type_Based
  Distinct_Degree_Factorization
begin

text \<open>We prove soundness of the finite field factorization,
  indepedendent on whether distinct-degree-factorization is
  applied as preprocessing or not.\<close>
consts use_distinct_degree_factorization :: bool

context
assumes "SORT_CONSTRAINT('a::prime_card)"
begin

definition finite_field_factorization :: "'a mod_ring poly \<Rightarrow> 'a mod_ring \<times> 'a mod_ring poly list" where
  "finite_field_factorization f = (if degree f = 0 then (lead_coeff f,[]) else let
     a = lead_coeff f;
     u = smult (inverse a) f;
     gs = (if use_distinct_degree_factorization then distinct_degree_factorization u else [(1,u)]);
     (irr,hs) = List.partition (\<lambda> (i,f). degree f = i) gs
    in (a,map snd irr @ concat (map (\<lambda> (i,g). berlekamp_monic_factorization i g) hs)))"

lemma finite_field_factorization_explicit:
  fixes f::"'a mod_ring poly"
  assumes sf_f: "square_free f"
    and us: "finite_field_factorization f = (c,us)"
  shows "f = smult c (prod_list us) \<and> (\<forall> u \<in> set us. monic u \<and> irreducible u)"
proof (cases "degree f = 0")
  case False note f = this
  define g where "g = smult (inverse c) f"    
  obtain gs where dist: "(if use_distinct_degree_factorization then distinct_degree_factorization g else [(1,g)]) = gs" by auto
  note us = us[unfolded finite_field_factorization_def Let_def]
  from us f have c: "c = lead_coeff f" by auto
  obtain irr hs where part: "List.partition (\<lambda> (i, f). degree f = i) gs = (irr,hs)" by force
  from arg_cong[OF this, of fst] have irr: "irr = filter (\<lambda> (i, f). degree f = i) gs" by auto
  from us[folded c, folded g_def, unfolded dist part split] f
  have us: "us = map snd irr @ concat (map (\<lambda>(x, y). berlekamp_monic_factorization x y) hs)" by auto
  from f c have c0: "c \<noteq> 0" by auto
  from False c0 have deg_g: "degree g \<noteq> 0" unfolding g_def by auto
  have mon_g: "monic g" unfolding g_def
    by (metis c c0 field_class.field_inverse lead_coeff_smult)
  from sf_f have sf_g: "square_free g" unfolding g_def by (simp add: c0)
  from c0 have f: "f = smult c g" unfolding g_def by auto
  have "g = prod_list (map snd gs) \<and> (\<forall> (i,f) \<in> set gs. degree f > 0 \<and> monic f \<and> (\<forall> h. h dvd f \<longrightarrow> degree h = i \<longrightarrow> irreducible h))" 
  proof (cases use_distinct_degree_factorization)
    case True
    with dist have "distinct_degree_factorization g = gs" by auto
    note dist = distinct_degree_factorization[OF this sf_g mon_g]
    from dist have g: "g = prod_list (map snd gs)" by auto
    show ?thesis
    proof (intro conjI[OF g] ballI, clarify)
      fix i f
      assume "(i,f) \<in> set gs" 
      with dist have "factors_of_same_degree i f" by auto
      from factors_of_same_degreeD[OF this] 
      show "degree f > 0 \<and> monic f \<and> (\<forall>h. h dvd f \<longrightarrow> degree h = i \<longrightarrow> irreducible h)" by auto
    qed
  next
    case False
    with dist have gs: "gs = [(1,g)]" by auto
    show ?thesis unfolding gs using deg_g mon_g linear_irreducible\<^sub>d[where 'a = "'a mod_ring"] by auto
  qed
  hence g_gs: "g = prod_list (map snd gs)" 
    and mon_gs: "\<And> i f. (i, f) \<in> set gs \<Longrightarrow> monic f \<and> degree f > 0" 
    and irrI: "\<And> i f h . (i, f) \<in> set gs \<Longrightarrow> h dvd f \<Longrightarrow> degree h = i \<Longrightarrow> irreducible h" by auto
  have g: "g = prod_list (map snd irr) * prod_list (map snd hs)" unfolding g_gs
    using prod_list_map_partition[OF part] .
  {
    fix f
    assume "f \<in> snd ` set irr" 
    from this[unfolded irr] obtain i where *:  "(i,f) \<in> set gs" "degree f = i" by auto
    have "f dvd f" by auto
    from irrI[OF *(1) this *(2)] mon_gs[OF *(1)] have "monic f" "irreducible f" by auto
  } note irr = this
  let ?berl = "\<lambda> hs. concat (map (\<lambda>(x, y). berlekamp_monic_factorization x y) hs)"
  have "set hs \<subseteq> set gs" using part by auto
  hence "prod_list (map snd hs) = prod_list (?berl hs)
    \<and> (\<forall> f \<in> set (?berl hs). monic f \<and> irreducible\<^sub>d f)" 
  proof (induct hs)
    case (Cons ih hs)
    obtain i h where ih: "ih = (i,h)" by force
    have "?berl (Cons ih hs) = berlekamp_monic_factorization i h @ ?berl hs" unfolding ih by auto
    from Cons(2)[unfolded ih] have mem: "(i,h) \<in> set gs" and sub: "set hs \<subseteq> set gs" by auto
    note IH = Cons(1)[OF sub]
    from mem have "h \<in> set (map snd gs)" by force
    from square_free_factor[OF prod_list_dvd[OF this], folded g_gs, OF sf_g] have sf: "square_free h" .
    from mon_gs[OF mem] irrI[OF mem] have *: "degree h > 0" "monic h" 
      "\<And> g. g dvd h \<Longrightarrow> degree g = i \<Longrightarrow> irreducible g" by auto
    from berlekamp_monic_factorization[OF sf refl *(3) *(1-2), of i]
    have berl: "prod_list (berlekamp_monic_factorization i h) = h" 
      and irr: "\<And> f. f \<in> set (berlekamp_monic_factorization i h) \<Longrightarrow> monic f \<and> irreducible f" by auto
    have "prod_list (map snd (Cons ih hs)) = h * prod_list (map snd hs)" unfolding ih by simp
    also have "prod_list (map snd hs) = prod_list (?berl hs)" using IH by auto
    finally have "prod_list (map snd (Cons ih hs)) = prod_list (?berl (Cons ih hs))" 
      unfolding ih using berl by auto
    thus ?case using IH irr unfolding ih by auto
  qed auto
  with g irr have main: "g = prod_list us \<and> (\<forall> u \<in> set us. monic u \<and> irreducible\<^sub>d u)" unfolding us
    by auto
  thus ?thesis unfolding f using sf_g by auto
next
  case True
  with us[unfolded finite_field_factorization_def] have "c = lead_coeff f" and us: "us = []" by auto
  with degree0_coeffs[OF True] have f: "f = [:c:]" by auto
  show ?thesis unfolding us f by (auto simp: normalize_poly_def)
qed

lemma finite_field_factorization:
  fixes f::"'a mod_ring poly"
  assumes sf_f: "square_free f"
    and us: "finite_field_factorization f = (c,us)"
  shows "unique_factorization Irr_Mon f (c, mset us)"
proof -
  from finite_field_factorization_explicit[OF sf_f us]
  have fact: "factorization Irr_Mon f (c, mset us)"
    unfolding factorization_def split Irr_Mon_def by (auto simp: prod_mset_prod_list)
  from sf_f[unfolded square_free_def] have "f \<noteq> 0" by auto
  from exactly_one_factorization[OF this] fact
  show ?thesis unfolding unique_factorization_def by auto
qed
end

text \<open>Experiments revealed that preprocessing via 
  distinct-degree-factorization slows down the factorization
  algorithm (statement for implementation in AFP 2017)\<close>

overloading use_distinct_degree_factorization \<equiv> use_distinct_degree_factorization
begin
  definition use_distinct_degree_factorization
    where [code_unfold]: "use_distinct_degree_factorization = False"
end
end
