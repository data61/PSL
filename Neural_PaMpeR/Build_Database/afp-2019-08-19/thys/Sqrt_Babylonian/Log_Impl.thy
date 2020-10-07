(*  Title:       Computing Square Roots using the Babylonian Method
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)
section \<open>A Fast Logarithm Algorithm\<close>

theory Log_Impl
imports 
  Sqrt_Babylonian_Auxiliary
begin

text \<open>We implement the discrete logarithm function in a manner similar to
  a repeated squaring exponentiation algorithm.\<close>

text \<open>In order to prove termination of the algorithm without intermediate checks 
  we need to ensure that we only use proper bases, 
  i.e., values of at least 2. This will be encoded into a separate type.\<close>

typedef proper_base = "{x :: int. x \<ge> 2}" by auto

setup_lifting type_definition_proper_base

lift_definition get_base :: "proper_base \<Rightarrow> int" is "\<lambda> x. x" .

lift_definition square_base :: "proper_base \<Rightarrow> proper_base" is "\<lambda> x. x * x" 
proof -
  fix i :: int
  assume i: "2 \<le> i"
  have "2 * 2 \<le> i * i" 
    by (rule mult_mono[OF i i], insert i, auto)
  thus "2 \<le> i * i" by auto
qed

lift_definition into_base :: "int \<Rightarrow> proper_base" is "\<lambda> x. if x \<ge> 2 then x else 2" by auto

lemma square_base: "get_base (square_base b) = get_base b * get_base b" 
  by (transfer, auto)

lemma get_base_2: "get_base b \<ge> 2"
  by (transfer, auto)

lemma b_less_square_base_b: "get_base b < get_base (square_base b)" 
  unfolding square_base using get_base_2[of b] by simp

lemma b_less_div_base_b: assumes xb: "\<not> x < get_base b"
  shows "x div get_base b < x"
proof -
  from get_base_2[of b] have b: "get_base b \<ge> 2" .
  with xb have x2: "x \<ge> 2" by auto
  with b int_div_less_self[of x "(get_base b)"] 
  show ?thesis by auto
qed
    
text \<open>We now state the main algorithm.\<close>
    
function log_main :: "proper_base \<Rightarrow> int \<Rightarrow> nat \<times> int" where
  "log_main b x = (if x < get_base b then (0,1) else
    case log_main (square_base b) x of 
      (z, bz) \<Rightarrow> 
    let l = 2 * z; bz1 = bz * get_base b
      in if x < bz1 then (l,bz) else (Suc l,bz1))" 
  by pat_completeness auto

termination by (relation "measure (\<lambda> (b,x). nat (1 + x - get_base b))",
  insert b_less_square_base_b, auto)   

lemma log_main: "x > 0 \<Longrightarrow> log_main b x = (y,by) \<Longrightarrow> by = (get_base b)^y \<and> (get_base b)^y \<le> x \<and> x < (get_base b)^(Suc y)" 
proof (induct b x arbitrary: y "by" rule: log_main.induct)
  case (1 b x y "by")
  note x = 1(2)
  note y = 1(3)
  note IH = 1(1)
  let ?b = "get_base b" 
  show ?case
  proof (cases "x < ?b")
    case True
    with x y show ?thesis by auto
  next
    case False
    obtain z bz where zz: "log_main (square_base b) x = (z,bz)" 
      by (cases "log_main (square_base b) x", auto)
    have id: "get_base (square_base b) ^ k = ?b ^ (2 * k)" for k unfolding square_base
      by (simp add: power_mult semiring_normalization_rules(29))
    from IH[OF False x zz, unfolded id] 
    have z: "?b ^ (2 * z) \<le> x" "x < ?b ^ (2 * Suc z)" and bz: "bz = get_base b ^ (2 * z)" by auto
    from y[unfolded log_main.simps[of b x] Let_def zz split] bz False
    have yy: "(if x < bz * ?b then (2 * z, bz) else (Suc (2 * z), bz * ?b)) =
      (y, by)" by auto
    show ?thesis
    proof (cases "x < bz * ?b")
      case True
      with yy have yz: "y = 2 * z" "by = bz" by auto
      from True z(1) bz show ?thesis unfolding yz by (auto simp: ac_simps)
    next
      case False
      with yy have yz: "y = Suc (2 * z)" "by = ?b * bz" by auto
      from False have "?b ^ Suc (2 * z) \<le> x" by (auto simp: bz ac_simps)
      with z(2) bz show ?thesis unfolding yz by auto
    qed
  qed
qed
    
text \<open>We then derive the floor- and ceiling-log functions.\<close>

definition log_floor :: "int \<Rightarrow> int \<Rightarrow> nat" where
  "log_floor b x = fst (log_main (into_base b) x)" 

definition log_ceiling :: "int \<Rightarrow> int \<Rightarrow> nat" where
  "log_ceiling b x = (case log_main (into_base b) x of
     (y,by) \<Rightarrow> if x = by then y else Suc y)" 

lemma log_floor_sound: assumes "b > 1" "x > 0" "log_floor b x = y"  
  shows "b^y \<le> x" "x < b^(Suc y)" 
proof -
  from assms(1,3) have id: "get_base (into_base b) = b" by transfer auto
  obtain yy bb where log: "log_main (into_base b) x = (yy,bb)" 
    by (cases "log_main (into_base b) x", auto)
  from log_main[OF assms(2) log] assms(3)[unfolded log_floor_def log] id
  show "b^y \<le> x" "x < b^(Suc y)" by auto
qed

lemma log_ceiling_sound: assumes "b > 1" "x > 0" "log_ceiling b x = y"  
  shows "x \<le> b^y" "y \<noteq> 0 \<Longrightarrow> b^(y - 1) < x" 
proof -
  from assms(1,3) have id: "get_base (into_base b) = b" by transfer auto
  obtain yy bb where log: "log_main (into_base b) x = (yy,bb)" 
    by (cases "log_main (into_base b) x", auto)
  from log_main[OF assms(2) log, unfolded id] assms(3)[unfolded log_ceiling_def log split]
  have bnd: "b ^ yy \<le> x" "x < b ^ Suc yy" and
    y: "y = (if x = b ^ yy then yy else Suc yy)" by auto
  have "x \<le> b^y \<and> (y \<noteq> 0 \<longrightarrow> b^(y - 1) < x)"
  proof (cases "x = b ^ yy")
    case True
    with y bnd assms(1) show ?thesis by (cases yy, auto)
  next
    case False
    with y bnd show ?thesis by auto
  qed
  thus "x \<le> b^y" "y \<noteq> 0 \<Longrightarrow> b^(y - 1) < x" by auto
qed

text \<open>Finally, we connect it to the @{const log} function working on real numbers.\<close>

lemma log_floor[simp]: assumes b: "b > 1" and x: "x > 0"
  shows "log_floor b x = \<lfloor>log b x\<rfloor>"
proof -
  obtain y where y: "log_floor b x = y" by auto
  note main = log_floor_sound[OF assms y]
  from b x have *: "1 < real_of_int b" "0 < real_of_int (b ^ y)" "0 < real_of_int x" 
    and **: "1 < real_of_int b" "0 < real_of_int x" "0 < real_of_int (b ^ Suc y)" 
    by auto
  show ?thesis unfolding y
  proof (rule sym, rule floor_unique)
    show "real_of_int (int y) \<le> log (real_of_int b) (real_of_int x)" 
      using main(1)[folded log_le_cancel_iff[OF *, unfolded of_int_le_iff]]
      using log_pow_cancel[of b y] b by auto
    show "log (real_of_int b) (real_of_int x) < real_of_int (int y) + 1" 
      using main(2)[folded log_less_cancel_iff[OF **, unfolded of_int_less_iff]]
      using log_pow_cancel[of b "Suc y"] b by auto
  qed
qed
    
lemma log_ceiling[simp]: assumes b: "b > 1" and x: "x > 0"
  shows "log_ceiling b x = \<lceil>log b x\<rceil>"
proof -
  obtain y where y: "log_ceiling b x = y" by auto
  note main = log_ceiling_sound[OF assms y]
  from b x have *: "1 < real_of_int b" "0 < real_of_int (b ^ (y - 1))" "0 < real_of_int x" 
    and **: "1 < real_of_int b" "0 < real_of_int x" "0 < real_of_int (b ^ y)" 
    by auto
  show ?thesis unfolding y
  proof (rule sym, rule ceiling_unique)
    show "log (real_of_int b) (real_of_int x) \<le> real_of_int (int y)" 
      using main(1)[folded log_le_cancel_iff[OF **, unfolded of_int_le_iff]]
      using log_pow_cancel[of b y] b by auto
    from x have x: "x \<ge> 1" by auto
    show "real_of_int (int y) - 1 < log (real_of_int b) (real_of_int x)" 
    proof (cases "y = 0")
      case False
      thus ?thesis 
        using main(2)[folded log_less_cancel_iff[OF *, unfolded of_int_less_iff]]
        using log_pow_cancel[of b "y - 1"] b x by auto
    next
      case True
      have "real_of_int (int y) - 1 = log b (1/b)" using True b 
        by (subst log_divide, auto)
      also have "\<dots> < log b 1"
        by (subst log_less_cancel_iff, insert b, auto) 
      also have "\<dots> \<le> log b x" 
        by (subst log_le_cancel_iff, insert b x, auto) 
      finally show "real_of_int (int y) - 1 < log (real_of_int b) (real_of_int x)" .
    qed
  qed
qed

end
