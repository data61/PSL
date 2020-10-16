(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Strassen's algorithm for matrix multiplication.\<close>

text \<open>We define the algorithm for arbitrary matrices over rings,
  where an alignment of the dimensions to even numbers will 
  be performed throughout the algorithm.\<close>

theory Strassen_Algorithm
imports 
  Matrix
begin

text \<open>With @{const four_block_mat} and @{const split_block} we can define Strassen's 
  multiplication algorithm.\<close>

text \<open>We start with a simple heuristic on when to switch to the basic algorithm.\<close>

definition strassen_constant :: nat where
  [code_unfold]: "strassen_constant = 20"

definition "strassen_too_small A B \<equiv> 
  dim_row A < strassen_constant \<or> 
  dim_col A < strassen_constant \<or> 
  dim_col B < strassen_constant"

text \<open>We have to make a case analysis on whether all dimensions are even.\<close>
definition "strassen_even A B \<equiv> even (dim_row A) \<and> even (dim_col A) \<and> even (dim_col B)"

text \<open>And then we can define the algorithm.\<close>

function strassen_mat_mult :: "'a :: ring mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "strassen_mat_mult A B = (let nr = dim_row A; n = dim_col A; nc = dim_col B in
    if strassen_too_small A B then A * B else 
    if strassen_even A B then let
      nr2 = nr div 2;
      n2 = n div 2;
      nc2 = nc div 2;
      (A1,A2,A3,A4) = split_block A nr2 n2;
      (B1,B2,B3,B4) = split_block B n2 nc2;
      M1 = strassen_mat_mult (A1 + A4) (B1 + B4);
      M2 = strassen_mat_mult (A3 + A4) B1;
      M3 = strassen_mat_mult A1 (B2 - B4);
      M4 = strassen_mat_mult A4 (B3 - B1);
      M5 = strassen_mat_mult (A1 + A2) B4;
      M6 = strassen_mat_mult (A3 - A1) (B1 + B2);
      M7 = strassen_mat_mult (A2 - A4) (B3 + B4);
      C1 = M1 + M4 - M5 + M7;
      C2 = M3 + M5;
      C3 = M2 + M4;
      C4 = M1 - M2 + M3 + M6
    in four_block_mat C1 C2 C3 C4 else 
    let 
     nr' = (nr div 2) * 2;
     n' = (n div 2) * 2;
     nc' = (nc div 2) * 2;
     (A1,A2,A3,A4) = split_block A nr' n';
     (B1,B2,B3,B4) = split_block B n' nc';
     C1 = strassen_mat_mult A1 B1 + A2 * B3;
     C2 = A1 * B2 + A2 * B4;
     C3 = A3 * B1 + A4 * B3;
     C4 = A3 * B2 + A4 * B4
     in four_block_mat C1 C2 C3 C4)"
  by pat_completeness auto

text \<open>For termination, we use the following measure.\<close>

definition "strassen_measure \<equiv> \<lambda> (A,B). (dim_row A + dim_col A + dim_col B)
  + (dim_row A + dim_col A + dim_col B) + (if strassen_even A B then 0 else 1)"

lemma strassen_measure_add[simp]: 
  "strassen_measure (A + B, C) = strassen_measure (B,C)" 
  "strassen_measure (A, B + C) = strassen_measure (A,C)" 
  "strassen_measure (A - B, C) = strassen_measure (B,C)" 
  "strassen_measure (A, B - C) = strassen_measure (A,C)" 
  "strassen_measure (- A, B) = strassen_measure (A,B)"
  "strassen_measure (A, - B) = strassen_measure (A,B)"
  unfolding strassen_measure_def strassen_even_def by auto

lemma strassen_measure_div_2: assumes "(A1, A2, A3, A4) = split_block A (dim_row A div 2) (dim_col A div 2)"
  "(B1, B2, B3, B4) = split_block B (dim_col A div 2) (dim_col B div 2)"  
  and large: "\<not> strassen_too_small A B"
  shows 
  "strassen_measure (A1,B4) < strassen_measure (A,B)"
  "strassen_measure (A1,B2) < strassen_measure (A,B)"
  "strassen_measure (A2,B4) < strassen_measure (A,B)"
  "strassen_measure (A3,B2) < strassen_measure (A,B)"
  "strassen_measure (A4,B1) < strassen_measure (A,B)"
  "strassen_measure (A4,B3) < strassen_measure (A,B)"
  "strassen_measure (A4,B4) < strassen_measure (A,B)"
proof -
  {
    fix Ai Bi
    assume Ai: "Ai \<in> {A1,A2,A3,A4}" and Bi: "Bi \<in> {B1,B2,B3,B4}"
    from large[unfolded strassen_too_small_def strassen_constant_def]
    have "\<not> dim_row A < 2" by auto 
    with assms Ai Bi have Ar:
      "dim_row Ai < dim_row A"
      "dim_col Ai \<le> dim_col A"
      "dim_col Bi \<le> dim_col B" 
      unfolding split_block_def Let_def by auto    
    hence "strassen_measure (Ai,Bi) < strassen_measure (A,B)"
      unfolding strassen_measure_def split by auto
  }
  thus
    "strassen_measure (A1,B2) < strassen_measure (A,B)"
    "strassen_measure (A1,B4) < strassen_measure (A,B)"
    "strassen_measure (A2,B4) < strassen_measure (A,B)"
    "strassen_measure (A3,B2) < strassen_measure (A,B)"
    "strassen_measure (A4,B1) < strassen_measure (A,B)"
    "strassen_measure (A4,B3) < strassen_measure (A,B)"
    "strassen_measure (A4,B4) < strassen_measure (A,B)"
    by auto
qed

lemma strassen_measure_odd: assumes "(A1, A2, A3, A4) = split_block A ((dim_row A div 2) * 2) ((dim_col A div 2) * 2)"  
  and "(B1, B2, B3, B4) = split_block B ((dim_col A div 2) * 2) ((dim_col B div 2) * 2)"
  and odd: "\<not> strassen_even A B"
  shows "strassen_measure (A1,B1) < strassen_measure (A,B)"
proof -
  from assms have Ar:
    "dim_row A1 < dim_row A \<or> dim_row A1 = dim_row A \<and> even (dim_row A)" 
    unfolding split_block_def Let_def by auto presburger
  from assms have Ac:
    "dim_col A1 < dim_col A \<or> dim_col A1 = dim_col A \<and> even (dim_col A)" 
    unfolding split_block_def Let_def by auto presburger
  from assms have Bc:
    "dim_col B1 < dim_col B \<or> dim_col B1 = dim_col B \<and> even (dim_col B)" 
    unfolding split_block_def Let_def by auto presburger
  from Ar Ac Bc odd show ?thesis unfolding strassen_measure_def strassen_even_def split
    by (auto split: if_splits)
qed

termination by (relation "measure strassen_measure", 
   auto elim: strassen_measure_div_2 strassen_measure_odd)


lemma strassen_mat_mult: 
  "dim_col A = dim_row B \<Longrightarrow> strassen_mat_mult A B = A * B"
proof (induct A B rule: strassen_mat_mult.induct)
  case (1 A B)
  let ?nr = "dim_row A"
  let ?nc = "dim_col B"
  let ?n = "dim_col A"
  show ?case
  proof (cases "strassen_too_small A B")
    case False note large = this
    let ?smm = strassen_mat_mult
    note IH = 1(1-8)[OF refl refl refl False _ refl refl refl _ refl refl refl _ refl refl refl]
    show ?thesis
    proof (cases "strassen_even A B")
      case True
      note even = True[unfolded strassen_even_def]
      let ?nr2 = "?nr div 2"
      let ?n2 = "?n div 2"
      let ?nc2 = "?nc div 2"
      from even have nr: "?nr = ?nr2 + ?nr2" by presburger 
      from even have n: "?n = ?n2 + ?n2" by presburger 
      from even have nc: "?nc = ?nc2 + ?nc2" by presburger 
      from 1(9) even have n': "dim_row B = ?n2 + ?n2"
        by auto
      obtain A1 A2 A3 A4 where splitA: 
        "split_block A ?nr2 ?n2 = (A1,A2,A3,A4)" by (rule prod_cases4)
      obtain B1 B2 B3 B4 where splitB: 
        "split_block B ?n2 ?nc2 = (B1,B2,B3,B4)" by (rule prod_cases4)
      note IH = IH(1-7)[OF True splitA[symmetric] splitB[symmetric] ]
      from split_block[OF splitA nr n]
      have blockA: "A = four_block_mat A1 A2 A3 A4"
        and A1: "A1 \<in> carrier_mat ?nr2 ?n2" 
        and A2: "A2 \<in> carrier_mat ?nr2 ?n2" 
        and A3: "A3 \<in> carrier_mat ?nr2 ?n2" 
        and A4: "A4 \<in> carrier_mat ?nr2 ?n2" 
        by blast+
      from split_block[OF splitB n' nc]
      have blockB: "B = four_block_mat B1 B2 B3 B4"
        and B1: "B1 \<in> carrier_mat ?n2 ?nc2" 
        and B2: "B2 \<in> carrier_mat ?n2 ?nc2" 
        and B3: "B3 \<in> carrier_mat ?n2 ?nc2" 
        and B4: "B4 \<in> carrier_mat ?n2 ?nc2" 
        by blast+
      note carr = A1 A2 A3 A4 B1 B2 B3 B4
      let ?M11 = "A1 + A4" let ?M12 = "B1 + B4"
      let ?M21 = "A3 + A4" let ?M22 = "B1"
      let ?M31 = "A1" let ?M32 = "B2 - B4"
      let ?M41 = "A4" let ?M42 = "B3 - B1"
      let ?M51 = "A1 + A2" let ?M52 = "B4"
      let ?M61 = "A3 - A1" let ?M62 = "B1 + B2"
      let ?M71 = "A2 - A4" let ?M72 = "B3 + B4"
      let ?M1 = "?smm ?M11 ?M12"
      let ?M2 = "?smm ?M21 ?M22"
      let ?M3 = "?smm ?M31 ?M32"
      let ?M4 = "?smm ?M41 ?M42"
      let ?M5 = "?smm ?M51 ?M52"
      let ?M6 = "?smm ?M61 ?M62"
      let ?M7 = "?smm ?M71 ?M72"
      let ?C1 = "?M1 + ?M4 - ?M5 + ?M7"
      let ?C2 = "?M3 + ?M5"
      let ?C3 = "?M2 + ?M4"
      let ?C4 = "?M1 - ?M2 + ?M3 + ?M6"
      have res: "?smm A B = four_block_mat ?C1 ?C2 ?C3 ?C4"
        using large True
        unfolding strassen_mat_mult.simps[of A B] Let_def splitA splitB split
        by auto
      have M1: "?M1 = ?M11 * ?M12"
        by (rule IH(1), insert carr, auto)
      note IH = IH(2-)[OF refl]
      have M2: "?M2 = ?M21 * ?M22"
        by (rule IH(1), insert carr, auto)
      note IH = IH(2-)[OF refl]
      have M3: "?M3 = ?M31 * ?M32"
        by (rule IH(1), insert carr, auto)
      note IH = IH(2-)[OF refl]
      have M4: "?M4 = ?M41 * ?M42"
        by (rule IH(1), insert carr, auto)
      note IH = IH(2-)[OF refl]
      have M5: "?M5 = ?M51 * ?M52"
        by (rule IH(1), insert carr, auto)
      note IH = IH(2-)[OF refl]
      have M6: "?M6 = ?M61 * ?M62"
        by (rule IH(1), insert carr, auto)
      note IH = IH(2-)[OF refl]
      have M7: "?M7 = ?M71 * ?M72"
        by (rule IH(1), insert carr, auto)
      note distr = 
        add_mult_distrib_mat[of _ ?nr2 ?n2 _ _ ?nc2]
        minus_mult_distrib_mat[of _ ?nr2 ?n2 _ _ ?nc2]
        mult_add_distrib_mat[of _ ?nr2 ?n2 _ ?nc2]
        mult_minus_distrib_mat[of _ ?nr2 ?n2 _ ?nc2]
      note closed = add_carrier_mat[of _ ?nr2 ?nc2]
         uminus_carrier_iff_mat[of _ ?nr2 ?nc2]
      note ac = assoc_add_mat[of _ ?nr2 ?nc2] comm_add_mat[of _ ?nr2 ?nc2]
      show ?thesis unfolding res M1 M2 M3 M4 M5 M6 M7
        unfolding blockA blockB
          mult_four_block_mat[OF carr]
        by (rule cong_four_block_mat)
           (insert carr, auto simp: distr ac closed)
    next
      case False
      let ?nr2 = "?nr div 2 * 2" let ?nr2' = "?nr - ?nr2"
      let ?n2 = "?n div 2 * 2"   let ?n2' = "?n - ?n2"
      let ?nc2 = "?nc div 2 * 2" let ?nc2' = "?nc - ?nc2"
      have nr: "?nr = ?nr2 + ?nr2'" by presburger 
      have n: "?n = ?n2 + ?n2'" by presburger 
      have nc: "?nc = ?nc2 + ?nc2'" by presburger 
      from 1(9) have n': "dim_row B = ?n2 + ?n2'" by auto   
      obtain A1 A2 A3 A4 where splitA: 
        "split_block A ?nr2 ?n2 = (A1,A2,A3,A4)" by (rule prod_cases4)
      obtain B1 B2 B3 B4 where splitB: 
        "split_block B ?n2 ?nc2 = (B1,B2,B3,B4)" by (rule prod_cases4)
      note IH = IH(8)[OF False splitA[symmetric] splitB[symmetric]]
      from split_block[OF splitA nr n]
      have blockA: "A = four_block_mat A1 A2 A3 A4"
        and A1: "A1 \<in> carrier_mat ?nr2 ?n2" 
        and A2: "A2 \<in> carrier_mat ?nr2 ?n2'" 
        and A3: "A3 \<in> carrier_mat ?nr2' ?n2" 
        and A4: "A4 \<in> carrier_mat ?nr2' ?n2'" 
        by blast+
      from split_block[OF splitB n' nc]
      have blockB: "B = four_block_mat B1 B2 B3 B4"
        and B1: "B1 \<in> carrier_mat ?n2 ?nc2" 
        and B2: "B2 \<in> carrier_mat ?n2 ?nc2'" 
        and B3: "B3 \<in> carrier_mat ?n2' ?nc2" 
        and B4: "B4 \<in> carrier_mat ?n2' ?nc2'" 
        by blast+      
      note carr = A1 A2 A3 A4 B1 B2 B3 B4
      from carr have "dim_col A1 = dim_row B1" by simp
      note IH = IH[OF this]
      have "?smm A B = four_block_mat 
        (A1 * B1 + A2 * B3)
        (A1 * B2 + A2 * B4)
        (A3 * B1 + A4 * B3)
        (A3 * B2 + A4 * B4)"
        unfolding strassen_mat_mult.simps[of A B] Let_def 
          splitA splitB split IH using large False by auto
      also have "\<dots> = A * B"
        unfolding blockA blockB
         mult_four_block_mat[OF carr] by simp
      finally show ?thesis by simp
    qed
  qed simp
qed

end
