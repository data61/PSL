(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Show for Real (Algebraic) Numbers -- Unique Representation\<close>

text \<open>We implement the show-function for real (algebraic) numbers by printing them
  uniquely via their monic irreducible polynomial with a special cases for polynomials 
  of degree at most 2.\<close>

theory Show_Real_Precise
imports
  Show_Real_Alg
  Show.Show_Instances
begin
  
datatype real_alg_show_info = Rat_Info rat | Sqrt_Info rat rat | Real_Alg_Info "int poly" nat
  
fun convert_info :: "rat + int poly \<times> nat \<Rightarrow> real_alg_show_info" where
  "convert_info (Inl q) = Rat_Info q" 
| "convert_info (Inr (f,n)) = (if degree f = 2 then (let a = coeff f 2; b = coeff f 1; c = coeff f 0;
      b2a = Rat.Fract (-b) (2 * a); 
      below = Rat.Fract (b*b - 4 * a * c) (4 * a * a)
     in Sqrt_Info b2a (if n = 1 then -below else below))
    else Real_Alg_Info f n)"

definition real_alg_show_info :: "real_alg \<Rightarrow> real_alg_show_info" where
  "real_alg_show_info x = convert_info (info_real_alg x)" 

text \<open>We prove that the extracted information for showing an algebraic real number is correct.\<close>
lemma real_alg_show_info: "real_alg_show_info x = Rat_Info r \<Longrightarrow> real_of x = of_rat r" 
  "real_alg_show_info x = Sqrt_Info r sq \<Longrightarrow> real_of x = of_rat r + sqrt (of_rat sq)" 
  "real_alg_show_info x = Real_Alg_Info p n \<Longrightarrow> p represents (real_of x) \<and> n = card {y. y \<le> real_of x \<and> ipoly p y = 0}" 
  (is "?l \<Longrightarrow> ?r")
proof (atomize(full), goal_cases)
  case 1
  note d = real_alg_show_info_def
  show ?case
  proof (cases "info_real_alg x")
    case (Inl q)
    from info_real_alg(2)[OF this] this show ?thesis unfolding d by auto
  next
    case (Inr qm)
    then obtain p n where id: "info_real_alg x = Inr (p,n)" by (cases qm, auto)
    from info_real_alg(1)[OF id]
    have ap: "p represents (real_of x)" and n: "n = card {y. y \<le> real_of x \<and> ipoly p y = 0}" 
      and irr: "irreducible p" by auto
    note id' = real_alg_show_info_def id convert_info.simps Fract_of_int_quotient Let_def
    have last: "?l \<Longrightarrow> ?r" unfolding id' using ap n by (auto split: if_splits)    
    {
      assume *: "real_alg_show_info x = Sqrt_Info r sq" 
      from this[unfolded id'] have deg: "degree p = 2" by (auto split: if_splits)
      from degree2_coeffs[OF this] obtain a b c where p: "p = [:c,b,a:]" and a: "a \<noteq> 0" by auto
      hence coeffs: "coeff p 0 = c" "coeff p 1 = b" "coeff p (Suc (Suc 0)) = a" "2 = Suc (Suc 0)" by auto
      let ?a = "real_of_int a" 
      let ?b = "real_of_int b"     
      let ?c = "real_of_int c" 
      define A where "A = ?a" 
      define B where "B = ?b" 
      define C where "C = ?c"
      let ?r = "- (B / (2 * A))"
      define R where "R = ?r" 
      let ?sq = "(B * B - 4 * A * C) / (4 * A * A)" 
      let ?p = "real_of_int_poly p" 
      let ?disc = "(B / (2 * A)) ^ Suc (Suc 0) - C / A" 
      define D where "D = ?disc" 
      from arg_cong[OF p, of "map_poly real_of_int"] 
      have rp: "?p = [: C, B, A :]" 
        using a by (auto simp: A_def B_def C_def)
      from a have A: "A \<noteq> 0" unfolding A_def by auto
      from *[unfolded id' deg, unfolded coeffs of_int_minus of_int_minus of_int_mult of_int_diff, simplified] 
      have r: "real_of_rat r = R" and sq: "sqrt (of_rat sq) = (if n = 1 then - sqrt ?sq else sqrt ?sq)" 
        by (auto simp: A_def B_def C_def R_def real_sqrt_minus hom_distribs) 
      note sq
      also have "?sq = D" using A by (auto simp: field_simps D_def)
      finally have sq: "sqrt (of_rat sq) = (if n = 1 then - sqrt D else sqrt D)" by simp
      with rp have coeffs': "coeff ?p 0 = C" "coeff ?p 1 = B" "coeff ?p (Suc (Suc 0)) = A" "2 = Suc (Suc 0)" by auto
      from rp A have "degree (real_of_int_poly p) = 2" by auto
      note roots = rroots2[OF this, unfolded rroots2_def Let_def coeffs', folded D_def R_def]
      from ap[unfolded represents_def] have root: "ipoly p (real_of x) = 0" by auto
      from root roots have D: "(D < 0) = False" by auto
      note roots = roots[unfolded this if_False, folded R_def]
      have "real_of x = of_rat r + sqrt (of_rat sq)"
      proof (cases "D = 0")
        case True
        show ?thesis using roots root unfolding sq r True by auto
      next
        case False
        with D have D: "D > 0" by auto
        from roots False have roots: "{x. ipoly p x = 0} = {R + sqrt D, R - sqrt D}" by auto
        let ?Roots = "{y. y \<le> real_of x \<and> ipoly p y = 0}" 
        have x: "real_of x \<in> ?Roots" using root by auto
        from root roots have choice: "real_of x = R + sqrt D \<or> real_of x = R - sqrt D" by auto
        hence small: "R - sqrt D \<in> ?Roots" using roots D by auto
        show ?thesis
        proof (cases "n = 1") 
          case True
          from card_1_singletonE[OF n[symmetric, unfolded this]] obtain y where id: "?Roots = {y}" by auto
          from x small show ?thesis unfolding sq r id using True by auto
        next
          case False
          from x obtain Y where Y: "?Roots = insert (real_of x) (Y - {real_of x})" by auto
          with False[unfolded n] obtain z Z where Z: "Y - {real_of x} = insert z Z" by (cases "Y - {real_of x} = {}", auto)
          from Y[unfolded Z] Z have sub: "{real_of x, z} \<subseteq> ?Roots" and z: "z \<noteq> real_of x" by auto
          with roots choice D have "real_of x = R + sqrt D" by force
          thus ?thesis unfolding sq r id using False by auto
        qed
      qed
    }
    with last show ?thesis unfolding d by (auto simp: id Let_def)
  qed
qed

fun show_rai_info :: "int \<Rightarrow> real_alg_show_info \<Rightarrow> string" where
  "show_rai_info fl (Rat_Info r) = show r" 
| "show_rai_info fl (Sqrt_Info r sq) = (let sqrt = ''sqrt('' @ show (abs sq) @ '')''
      in if r = 0 then (if sq < 0 then '' -'' else []) @ sqrt 
                  else (''('' @ show r @ (if sq < 0 then ''-'' else ''+'') @ sqrt @ '')''))" 
| "show_rai_info fl (Real_Alg_Info p n) = 
    ''(root #'' @ show n @ '' of '' @ show p @ '', in ('' @ show fl @ '','' @ show (fl + 1) @ ''))''" 
  
overloading show_real_alg \<equiv> show_real_alg
begin
  definition show_real_alg[code]:
    "show_real_alg x \<equiv> show_rai_info (floor x) (real_alg_show_info x)"
end 
end
