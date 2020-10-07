theory Examples_ARCH_COMP
  imports
    "HOL-ODE-Numerics.ODE_Numerics"
begin

lemma continuous_on_floatarith_zero[simp]: "continuous_on_floatarith 0"
  by (auto simp: zero_floatarith_def)

lemma continuous_on_floatarith_minus[simp]:
  "continuous_on_floatarith (a - b) \<longleftrightarrow> continuous_on_floatarith a \<and> continuous_on_floatarith b"
  by (auto simp: minus_floatarith_def)

lemma continuous_on_floatarith_uminus[simp]:
  "continuous_on_floatarith (- b) \<longleftrightarrow> continuous_on_floatarith b"
  by (auto simp: uminus_floatarith_def)

lemma continuous_on_floatarith_times[simp]:
  "continuous_on_floatarith (a * b) \<longleftrightarrow> continuous_on_floatarith a \<and> continuous_on_floatarith b"
  by (auto simp: times_floatarith_def)

lemma continuous_on_floatarith_plus[simp]:
  "continuous_on_floatarith (a + b) \<longleftrightarrow> continuous_on_floatarith a \<and> continuous_on_floatarith b"
  by (auto simp: plus_floatarith_def)

lemmas isDERIV_Power_iff[simp]

lemma isFDERIV_Suc: "isFDERIV (Suc n) (d#ds) (f#fs) xs \<longleftrightarrow>
  isFDERIV n ds fs xs \<and> isDERIV d f xs
  \<and> (\<forall>x2 < n. isDERIV d (fs ! x2) xs)
  \<and> (\<forall>x2 < n. isDERIV (ds ! x2) f xs)"
  unfolding isFDERIV_def
  by (auto simp: isFDERIV_def nth_Cons split: nat.splits)

lemma isFDERIV_SucI: "isFDERIV (Suc n) (d#ds) (f#fs) xs"
  if "isFDERIV n ds fs xs" "isDERIV d f xs"
  "\<And>i. i < n \<Longrightarrow> isDERIV d (fs ! i) xs"
  "\<And>i. i < n \<Longrightarrow> isDERIV (ds ! i) f xs"
  using that
  by (auto simp: isFDERIV_Suc)

lemma isFDERIV_0[simp]: "isFDERIV 0 [] [] zs"
  by (auto simp: isFDERIV_def nth_Cons split: nat.splits)

lemmas [simp] = Basis_list_real_def

subsection \<open>Space Rendezvous\<close>

experiment begin

unbundle floatarith_notation

abbreviation "r \<equiv> 42164000"
abbreviation "mu \<equiv> 3.986*10^14*3600"
abbreviation "m_c \<equiv> 500"
abbreviation "n \<equiv> 0.004375293492336"
abbreviation "K1_11 \<equiv> -28.8287"
abbreviation "K1_12 \<equiv> 0.1005"
abbreviation "K1_13 \<equiv> -1449.9754"
abbreviation "K1_14 \<equiv> 0.0046"
abbreviation "K1_21 \<equiv> -0.087"
abbreviation "K1_22 \<equiv> -33.2562"
abbreviation "K1_23 \<equiv> 0.00462"
abbreviation "K1_24 \<equiv> -1451.5013"
abbreviation "K2_11 \<equiv> -288.0288"
abbreviation "K2_12 \<equiv> 0.1312"
abbreviation "K2_13 \<equiv> -9614.9898"
abbreviation "K2_14 \<equiv> 0"
abbreviation "K2_21 \<equiv> -0.1312"
abbreviation "K2_22 \<equiv> -288 "
abbreviation "K2_23 \<equiv> 0"
abbreviation "K2_24 \<equiv> -9614.9883"


subsubsection \<open>Location P1\<close>

schematic_goal p1_fas:
  fixes X
  defines "t \<equiv> X!0"
    and "x \<equiv> X ! 1"
    and "y \<equiv> X ! 2"
    and "vx \<equiv> X ! 3"
    and "vy \<equiv> X ! 4"
  shows
  "[
  \<comment> \<open>t' = \<close> 1,
  \<comment> \<open>x' = \<close> vx,
  \<comment> \<open>y' = \<close> vy,
  \<comment> \<open>vx' = \<close> (n^2 + K1_11/m_c)*x + (2*n + K1_14/m_c) * vy + K1_12/m_c * y + K1_13/m_c * vx + mu/r^2 - mu/sqrt((r+x)^2-y^2)^3 * (r+x),
  \<comment> \<open>vy' = \<close> (n^2 + K1_22/m_c)*y + (K1_23/m_c -2*n) * vx + K1_21/m_c * x + K1_24/m_c * vy - mu/sqrt((r+x)^2-y^2)^3 * y
] = interpret_floatariths ?fas X"
  unfolding t_def x_def y_def vx_def vy_def
  by (reify_floatariths)

concrete_definition p1_fas uses p1_fas

abbreviation "safe_sqrt \<equiv> (Less 0 ((Num r + Var 1)^\<^sub>e2 - (Var 2) ^\<^sub>e 2)) \<comment> \<open>sqrt defined\<close>"

abbreviation "safe_p1 \<equiv> Conj (Less (Var 0) (Num 125)) \<comment> \<open>abort\<close>
  safe_sqrt"

interpretation p1: ode_interpretation safe_p1
  "{(t, x, y, vx, vy). t < 125 \<and> (r+x)^2-y^2 > 0}" p1_fas
   "\<lambda>(t, x, y, vx, vy).
      (1,
       vx,
       vy,
       (n^2 + K1_11/m_c)*x + (2*n + K1_14/m_c) * vy + K1_12/m_c * y + K1_13/m_c * vx + mu/r^2 - mu/sqrt((r+x)^2-y^2)^3 * (r+x),
       (n^2 + K1_22/m_c)*y + (K1_23/m_c -2*n) * vx + K1_21/m_c * x + K1_24/m_c * vy - mu/sqrt((r+x)^2-y^2)^3 * y
  )::real*real*real*real*real"
  "d::5" for d
  by standard
    (auto simp: p1_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

lemma poincare_section_rep[poincare_tac_theorems]:
              "{(0, -100, -500, -1000, -1000)..(125, -100, 0, 1000, 1000)::real*real*real*real*real} =
  {eucl_of_list [0, -100, -500, -1000, -1000]..eucl_of_list [125, -100, 0, 1000, 1000]}"
  by (auto simp: eucl_of_list_prod)

abbreviation "p1_ro \<equiv> ro 10 10 7 2 2 2"

lemma p1_ro: "TAG_reach_optns p1_ro" by simp

lemma p1_start: "TAG_sctn False" by simp

lemma p1_pi_0: "p1.guards_invar DIM(real \<times> real \<times> real \<times> real \<times> real) []"
  by (auto simp: p1.guards_invar_def)

lemma
  notes [poincare_tac_theorems] = p1_ro p1_start p1_pi_0
  shows "\<forall>x\<in>{(0, -925, -425, 0, 0) .. (0, -875, -375, 0, 0)}.
  p1.returns_to                {(0, -100, -500, -1000, -1000)..(125, -100, 0, 1000, 1000)} x \<and>
  p1.poincare_map_from_outside {(0, -100, -500, -1000, -1000)..(125, -100, 0, 1000, 1000)} x \<in>
      {(108.5, -100, -35.05, 1.993, 0.6489) ..
       (111.8, -100, -28.42, 2.007, 0.8130)}"
  using [[ode_numerics_trace]]
  by (tactic \<open>poincare_bnds_tac @{thms p1_fas_def} 30 50 20 10 [(1, 2, "0x00007f")]
    (* "out_space_p1.out" *) ""  @{context} 1\<close>)


subsubsection \<open>Location P2\<close>

lemma "tan (rad_of 30) \<in> {147 * 2 powr -8 .. 148 * 2 powr -8}"
  unfolding rad_of_def atLeastAtMost_iff
  by (approximation 15)
abbreviation "Tanl \<equiv> Num (Float 147 (-8))"
abbreviation "Tanu \<equiv> Num (Float 148 (-8))"

abbreviation "safe_p2 \<equiv>
  Conj safe_p1
    (Conj (Less (Max (Var 1 * Tanl) (Var 1 * Tanu)) (Var 2))
      (Less (Max (Var 1 * Tanl)(Var 1 * Tanu)) (-(Var 2)))) \<comment> \<open>line of sight\<close>"

schematic_goal p2_fas:
  fixes X
  defines "t \<equiv> X!0"
    and "x \<equiv> X ! 1"
    and "y \<equiv> X ! 2"
    and "vx \<equiv> X ! 3"
    and "vy \<equiv> X ! 4"
  shows
  "[
  \<comment> \<open>t' = \<close> 1,
  \<comment> \<open>x' = \<close> vx,
  \<comment> \<open>y' = \<close> vy,
  \<comment> \<open>vx' = \<close> (n^2 + K2_11/m_c)*x + (2*n + K2_14/m_c)* vy + K2_12/m_c * y + K2_13/m_c * vx + mu/r^2 - mu/sqrt((r+x)^2-y^2)^3 * (r+x),
  \<comment> \<open>vy' = \<close> (n^2 + K2_22/m_c)*y + (K2_23/m_c -2*n)* vx + K2_21/m_c * x + K2_24/m_c * vy - mu/sqrt((r+x)^2-y^2)^3 * y
] = interpret_floatariths ?fas X"
  unfolding t_def x_def y_def vx_def vy_def
  by (reify_floatariths)

concrete_definition p2_fas uses p2_fas


interpretation p2: ode_interpretation safe_p2
  "{(t, x, y, vx, vy). t < 125 \<and>
    (r+x)^2-y^2 > 0 \<and>
    max (x * 147 * 2 powr -8) (x * 147 * 2 powr -8) < y \<and>
    max (x * 147 * 2 powr -8) (x * 147 * 2 powr -8) < -y
  }" p2_fas
  "\<lambda>(t, x, y, vx, vy).
      (1,
       vx,
       vy,
       (n^2 + K2_11/m_c)*x + (2*n + K2_14/m_c) * vy + K2_12/m_c * y + K2_13/m_c * vx + mu/r^2 - mu/sqrt((r+x)^2-y^2)^3 * (r+x),
       (n^2 + K2_22/m_c)*y + (K2_23/m_c -2*n) * vx + K2_21/m_c * x + K2_24/m_c * vy - mu/sqrt((r+x)^2-y^2)^3 * y
  )::real*real*real*real*real"
  "d::5" for d
  by standard
    (auto simp: p2_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

lemma poincare_section2_rep[poincare_tac_theorems]:
  "{(120, -1000, -1000, -1000, -1000)..(120, 1000, 1000, 1000, 1000)::real*real*real*real*real} =
  {eucl_of_list [120, -1000, -1000, -1000, -1000]..eucl_of_list [120, 1000, 1000, 1000, 1000]}"
  by (auto simp: eucl_of_list_prod)

abbreviation "p2_ro \<equiv> ro 10 10 7 10 10 2"

lemma p2_ro: "TAG_reach_optns p2_ro" by simp

lemma p2_start: "TAG_sctn False" by simp

lemma p2_pi_0: "p2.guards_invar DIM(real \<times> real \<times> real \<times> real \<times> real) []"
  by (auto simp: p2.guards_invar_def)

lemma
  notes [poincare_tac_theorems] = p2_ro p2_start p2_pi_0
  shows "\<forall>x\<in>{(108.5, -100, -35.05, 1.993, 0.6489) ..
       (111.8, -100, -28.42, 2.007, 0.8130)}.
  p2.returns_to                {(120, -1000, -1000, -1000, -1000)..(120, 1000, 1000, 1000, 1000)} x \<and>
  p2.poincare_map_from_outside {(120, -1000, -1000, -1000, -1000)..(120, 1000, 1000, 1000, 1000)} x \<in>
    {(120, -78.24, -27.43, 2.125, 0.596) ..
     (120, -70.85, -20.12, 2.348, 0.829)}"
  using [[ode_numerics_trace]]
  by (tactic \<open>poincare_bnds_tac @{thms p2_fas_def} 30 50 20 10 [(1, 2, "0x7f0000"), (3, 4, "0x0000ff")]
    (* "out_space_p2.out" *) ""  @{context} 1\<close>)

(*(1.2e2 -70.8581e1 -2.012131e1 2.347061 8.28834e-1)*)
subsubsection \<open>Location Passive\<close>

schematic_goal passive_fas:
  fixes X
  defines "t \<equiv> X!0"
    and "x \<equiv> X ! 1"
    and "y \<equiv> X ! 2"
    and "vx \<equiv> X ! 3"
    and "vy \<equiv> X ! 4"
  shows
  "[
  \<comment> \<open>t' = \<close> 1,
  \<comment> \<open>x' = \<close> vx,
  \<comment> \<open>y' = \<close> vy,
  \<comment> \<open>vx' = \<close> n^2 * x + 2*n * vy + mu/r^2 - mu/sqrt((r+x)^2-y^2)^3 * (r+x),
  \<comment> \<open>vy' = \<close> n^2*y - 2*n * vx - mu/sqrt((r+x)^2-y^2)^3 * y
] = interpret_floatariths ?fas X"
  unfolding t_def x_def y_def vx_def vy_def
  by (reify_floatariths)

concrete_definition passive_fas uses passive_fas

abbreviation "safe_passive \<equiv> Conj
  safe_sqrt
  (Disj (Disj (Less (Var 1) (Num (-1))) (Less (Num 1) (Var 1)))
    (Disj (Less (Var 2) (Num (-1))) (Less (Num 1) (Var 2))))
    \<comment> \<open>avoiding satellite in box of ``radius'' 1\<close>"

interpretation passive: ode_interpretation safe_passive
  "{(t, x, y, vx, vy). (r+x)^2-y^2 > 0 \<and> (x, y) \<notin> {(-1, -1) .. (1, 1)}}" passive_fas
  "\<lambda>(t, x, y, vx, vy).
      (1,
       vx,
       vy,
       n^2 * x + 2*n * vy + mu/r^2 - mu/sqrt((r+x)^2-y^2)^3 * (r+x),
       n^2*y - 2*n * vx - mu/sqrt((r+x)^2-y^2)^3 * y
  )::real*real*real*real*real"
  "d::5" for d
  by standard
    (auto simp: passive_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

lemma poincare_section3_rep[poincare_tac_theorems]:
              "{(200, -1000, -1000, -1000, -1000)..(200, 1000, 1000, 1000, 1000)::real*real*real*real*real} =
  {eucl_of_list [200, -1000, -1000, -1000, -1000]..eucl_of_list [200, 1000, 1000, 1000, 1000]}"
  by (auto simp: eucl_of_list_prod)

abbreviation "passive_ro \<equiv> ro 10 10 7 10 10 2"

lemma passive_ro: "TAG_reach_optns passive_ro" by simp

lemma passive_start: "TAG_sctn False" by simp

lemma passive_pi_0: "passive.guards_invar DIM(real \<times> real \<times> real \<times> real \<times> real) []"
  by (auto simp: passive.guards_invar_def)

lemma
  notes [poincare_tac_theorems] = passive_ro passive_start passive_pi_0
  shows "\<forall>x\<in>{(120, -78.24, -27.43, 2.125, 0.596) ..
     (120, -70.85, -20.12, 2.348, 0.829)}.
  passive.returns_to                {(200, -1000, -1000, -1000, -1000)..(200, 1000, 1000, 1000, 1000)} x \<and>
  passive.poincare_map_from_outside {(200, -1000, -1000, -1000, -1000)..(200, 1000, 1000, 1000, 1000)} x \<in>
    {(200, 89.95, -46.20, 2.047, -1.050) ..
     (200, 123.9, -14.19, 2.460, -0.701)}"
  using [[ode_numerics_trace]]
  by (tactic \<open>poincare_bnds_tac @{thms passive_fas_def} 30 50 20 10 [(1, 2, "0x000000")] (* "out_space_passive.out" *) ""  @{context} 1\<close>)

end

subsection \<open>Quadrotor\<close>
experiment begin

unbundle floatarith_notation

abbreviation "g \<equiv> 9.81"
abbreviation "R \<equiv> 0.1"
abbreviation "l \<equiv> 0.5"
abbreviation "M\<^sub>r\<^sub>o\<^sub>t\<^sub>o\<^sub>r \<equiv> 0.1"
abbreviation "M \<equiv> 1"
abbreviation "m \<equiv> M + 4 * M\<^sub>r\<^sub>o\<^sub>t\<^sub>o\<^sub>r"
abbreviation "J\<^sub>x \<equiv> 2/5 * M * R\<^sup>2 + 2 * l\<^sup>2 * M\<^sub>r\<^sub>o\<^sub>t\<^sub>o\<^sub>r"
abbreviation "J\<^sub>y \<equiv> J\<^sub>x"
abbreviation "J\<^sub>z \<equiv> 2/5 * M * R\<^sup>2 + 4 * l\<^sup>2 * M\<^sub>r\<^sub>o\<^sub>t\<^sub>o\<^sub>r"

abbreviation "u x i \<equiv> x ! (i + 12)"
abbreviation "F x \<equiv> m * g - 10 * (x!3 - u x 1) + 3 * x!6"
abbreviation "\<tau>\<^sub>\<phi> x \<equiv> - (x ! 7 - u x 2) - x!10"
abbreviation "\<tau>\<^sub>\<theta> x \<equiv> - (x ! 8 - u x 3) - x!11"
abbreviation "\<tau>\<^sub>\<psi> x \<equiv> 0"

schematic_goal quadrot_fas:
  "[\<comment> \<open>\<open>t:\<close>\<close> 1,
    \<comment> \<open>\<open>x\<^sub>1:\<close>\<close> cos (x!8) * cos (x!9)* x ! 4 + (sin(x!7) * sin(x!8) * cos (x!9) - cos(x!7) * sin(x!9))*x!5
              + (cos(x!7) * sin(x!8) * cos(x!9) + sin(x!7) * sin(x!9)) * x!6,
    \<comment> \<open>\<open>x\<^sub>2:\<close>\<close> cos(x!8) * sin (x!9) * x!4 + (sin(x!7) * sin (x!8) * sin(x!9) + cos(x!7) * cos (x!9))*x!5
              + (cos(x!7) * sin(x!8) * sin(x!9) - sin ( x!7) * cos (x!9)) * x!6,
    \<comment> \<open>\<open>x\<^sub>3:\<close>\<close> sin(x!8) * x!4 - sin(x!7) * cos (x!8) * x!5 - cos(x!7) *cos(x!8)*x!6,
    \<comment> \<open>\<open>x\<^sub>4:\<close>\<close> x!12 * x!5- x!11*x!6 - g * sin(x!8),
    \<comment> \<open>\<open>x\<^sub>5:\<close>\<close> x!10 * x!6 - x!12*x!4 + g * cos(x!8 * sin(x!7)),
    \<comment> \<open>\<open>x\<^sub>6:\<close>\<close> x!11 * x!4 - x!10*x!5 + g * cos(x!8 * cos(x!7)) - F x / m,
    \<comment> \<open>\<open>x\<^sub>7:\<close>\<close> x!10 + (sin(x!7)*tan(x!8))*x!11 + (cos(x!7)*tan(x!8))*x!12,
    \<comment> \<open>\<open>x\<^sub>8:\<close>\<close> cos(x!7) * x!11 - sin(x!7)*x!12,
    \<comment> \<open>\<open>x\<^sub>9:\<close>\<close> sin(x!7) / cos(x!8) * x!11 + cos(x!7)/cos(x!8)*x!12,
    \<comment> \<open>\<open>x\<^sub>1\<^sub>0:\<close>\<close> (J\<^sub>y - J\<^sub>z)/J\<^sub>x*x!11*x!12 + \<tau>\<^sub>\<phi> x / J\<^sub>x,
    \<comment> \<open>\<open>x\<^sub>1\<^sub>1:\<close>\<close> (J\<^sub>z - J\<^sub>x)/J\<^sub>y*x!10*x!12 + \<tau>\<^sub>\<theta> x / J\<^sub>y,
    \<comment> \<open>\<open>x\<^sub>1\<^sub>2:\<close>\<close> (J\<^sub>x - J\<^sub>y)/J\<^sub>z*x!10*x!11 + \<tau>\<^sub>\<psi> x / J\<^sub>z,
    \<comment> \<open>\<open>u\<^sub>1:\<close>\<close> 0,
    \<comment> \<open>\<open>u\<^sub>2:\<close>\<close> 0,
    \<comment> \<open>\<open>u\<^sub>3:\<close>\<close> 0]
  = interpret_floatariths ?fas x"
  by (reify_floatariths)
concrete_definition quadrot_fas uses quadrot_fas

abbreviation "Fr x3 x6 u1 \<equiv> m * g - 10 * (x3 - u1) + 3 * x6"

lemma isDERIV_Power_if[simp]:
  "isDERIV x (f ^\<^sub>e n) vs = (if n = 0 then True else isDERIV x f vs)"
  by (cases n) auto

definition "Ne x y = Disj (Less x y) (Less y x)"

lemma Basis_list_16:
  "(Basis_list::(real*real*real*real*real*real*real*real*real*real*real*real*real*real*real*real) list) =
  [
  (1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0),
  (0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0),
  (0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0),
  (0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0),
  (0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0),
  (0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0),
  (0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0),
  (0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0),
  (0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0),
  (0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0),
  (0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0),
  (0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0),
  (0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0),
  (0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0),
  (0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0),
  (0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1)]"
  by (auto simp: Basis_list_prod_def zero_prod_def)

interpretation quadrot: ode_interpretation "Conj (Less (- Half Pi) (Var 8))
  (Conj (Less (Var 8) (Half Pi)) ((Less (Var 3)
  ((Num (Float 89 (- 6)))))))"
  "{(t, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, u1, u2, u3).
    x3 < 89/64 \<and> x8 \<in> {-pi/2<..<pi/2}}"
  quadrot_fas
  "\<lambda>(t::real, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, u1, u2, u3). (1,
    \<comment> \<open>\<open>x\<^sub>1\<close>:\<close> cos (x8) * cos (x9)* x4 + (sin(x7) * sin(x8) * cos (x9) - cos(x7) * sin(x9))*x5
              + (cos(x7) * sin(x8) * cos(x9) + sin(x7) * sin(x9)) * x6,
    \<comment> \<open>\<open>x\<^sub>2\<close>:\<close> cos(x8) * sin (x9) * x4 + (sin(x7) * sin (x8) * sin(x9) + cos(x7) * cos (x9))*x5
              + (cos(x7) * sin(x8) * sin(x9) - sin ( x7) * cos (x9)) * x6,
    \<comment> \<open>\<open>x\<^sub>3\<close>:\<close> sin(x8) * x4 - sin(x7) * cos (x8) * x5 - cos(x7) *cos(x8)*x6,
    \<comment> \<open>\<open>x\<^sub>4\<close>:\<close> x12 * x5- x11*x6 - g * sin(x8),
    \<comment> \<open>\<open>x\<^sub>5\<close>:\<close> x10 * x6 - x12*x4 + g * cos(x8 * sin(x7)),
    \<comment> \<open>\<open>x\<^sub>6\<close>:\<close> x11 * x4 - x10*x5 + g * cos(x8 * cos(x7)) - Fr x3 x6 u1 / m,
    \<comment> \<open>\<open>x\<^sub>7\<close>:\<close> x10 + (sin(x7)*tan(x8))*x11 + (cos(x7)*tan(x8))*x12,
    \<comment> \<open>\<open>x\<^sub>8\<close>:\<close> cos(x7) * x11 - sin(x7)*x12,
    \<comment> \<open>\<open>x\<^sub>9\<close>:\<close> sin(x7) / cos(x8) * x11 + cos(x7)/cos(x8)*x12,
    \<comment> \<open>\<open>x\<^sub>1\<^sub>0\<close>:\<close> (J\<^sub>y - J\<^sub>z)/J\<^sub>x*x11*x12 + (- (x7 - u2) - x10) / J\<^sub>x,
    \<comment> \<open>\<open>x\<^sub>1\<^sub>1\<close>:\<close> (J\<^sub>z - J\<^sub>x)/J\<^sub>y*x10*x12 + (- (x8 - u3) - x11) / J\<^sub>y,
    \<comment> \<open>\<open>x\<^sub>1\<^sub>2\<close>:\<close> (J\<^sub>x - J\<^sub>y)/J\<^sub>z*x10*x11 + 0 / J\<^sub>z,
    \<comment> \<open>\<open>u\<^sub>1\<close>:\<close> 0::real,
    \<comment> \<open>\<open>u\<^sub>2\<close>:\<close> 0::real,
    \<comment> \<open>\<open>u\<^sub>3\<close>:\<close> 0::real)" "sixteen::16"
  apply standard
  subgoal by simp
  subgoal by (simp add: quadrot_fas_def)
  subgoal by (auto simp: Basis_list_16)
  subgoal
    using cos_gt_zero_pi
    apply (simp add: quadrot_fas_def Basis_list_16)
    apply (auto simp: eucl_of_list_prod split: prod.splits)
    apply (auto simp: power2_eq_square quadrot_fas_def)
    by (auto simp: approximation_preproc_floatarith[symmetric])
  subgoal by (auto simp: mk_ode_ops_def quadrot_fas_def Half_def)
  subgoal
    using cos_gt_zero_pi
    by (fastforce simp: quadrot_fas_def less_Suc_eq_0_disj nth_Basis_list_prod isFDERIV_product
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)
  done

lemma quadrot: "t \<in> {5 .. 5} \<longrightarrow>
    (s,   x1,   x2,   x3,   x4,   x5,   x6, x7, x8, x9, x10, x11, x12, u1, u2, u3) \<in>
   {(0, -0.4, -0.4, -0.4, -0.4, -0.4, -0.4,  0,  0,  0,   0,   0,   0,  1,  0,  0) ..
    (0,  0.4,  0.4,  0.4,  0.4,  0.4,  0.4,  0,  0,  0,   0,   0,   0,  1,  0,  0)} \<longrightarrow>
   t \<in> quadrot.existence_ivl0 (s, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, u1, u2, u3) \<and>
    quadrot.flow0 (s, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, u1, u2, u3) t \<in>
      {(4.99, -2.5, 120, 0.98, -0.5, 48, -0.05, 0, 0, 0, 0, 0, 0, 1, 0, 0) ..
       (5.01,  2.5, 126, 1.02,  0.5, 50,  0.05, 0, 0, 0, 0, 0, 0, 1, 0, 0)}
      \<^cancel>\<open>{(4.9, -2.5, 120, 0.99, -0.5, 48, -0.02, 0, 0, 0, 0, 0, 0, 1, 0, 0) ..
       (5.0,  2.5, 126, 1.00,  0.5, 50,  0.02, 0, 0, 0, 0, 0, 0, 1, 0, 0)}\<close>"
  by (tactic \<open>ode_bnds_tac @{thms quadrot_fas_def} 16 25 20 10 [(0, 3, "0x000000")]
    (* "out_quadrot.out" *) ""  @{context} 1\<close>)

end

subsection \<open>Laub Loomis\<close>
experiment begin

unbundle floatarith_notation

schematic_goal laub_fas:
  "[1,
    1.4 * X ! 3 - 0.9 * X ! 1,
    2.5 * X ! 5 - 1.5 * X ! 2,
    0.6 * X ! 7 - 0.8 * X ! 2 * X ! 3,
    2           - 1.3 * X ! 3 * X ! 4,
    0.7 * X ! 1 -       X ! 4 * X ! 5,
    0.3 * X ! 1 - 3.1 * X ! 6,
    1.8 * X ! 6 - 1.5 * X ! 2 * X ! 7]
  = interpret_floatariths ?fas X"
  by (reify_floatariths)

concrete_definition laub_fas uses laub_fas

interpretation ll: ode_interpretation "Less (Var 4) (Num 50)"
  "{(t, x1, x2, x3, x4, x5, x6, x7).
      x4 < 50 \<comment> \<open>modify for safety requirements of ARCH-competition\<close>}"
  laub_fas
  "\<lambda>(t, x1, x2, x3, x4, x5, x6, x7).
    (1,
     1.4 * x3 - 0.9 * x1,
     2.5 * x5 - 1.5 * x2,
     0.6 * x7 - 0.8 * x2 * x3,
     2 - 1.3 * x3 * x4,
     0.7 * x1 - x4 * x5,
     0.3 * x1 - 3.1 * x6,
     1.8 * x6 - 1.5 * x2 * x7)::real*real*real*real*real*real*real*real" "eight::8"
  by standard
    (auto simp: laub_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

theorem ll_001:
  "t \<in> {20 .. 20} \<longrightarrow>
  (s, x1, x2, x3, x4, x5, x6, x7) \<in>
      {(0, 1.19, 1.04, 1.49, 2.39, 0.99, 0.09, 0.44) ..
       (0, 1.21, 1.06, 1.51, 2.41, 1.01, 0.11, 0.46)} \<longrightarrow>
  t \<in> ll.existence_ivl0 (s, x1, x2, x3, x4, x5, x6, x7) \<and>
  ll.flow0 (s, x1, x2, x3, x4, x5, x6, x7) t \<in>
    {(19.99, 0.8, 0.3, 0.5, 2.5, 0.1, 0.0, 0.25) ..
     (20, 1.0, 0.5, 0.7, 3.0, 0.3, 0.1, 0.35)}"
  by (tactic \<open>ode_bnds_tac @{thms laub_fas_def} 30 60 30 13 [(0, 4, "0x7f7f7f")] (* "out_ll_001.out" *) ""  @{context} 1\<close>)

theorem ll_005:
  "t \<in> {20 .. 20} \<longrightarrow>
  (s, x1, x2, x3, x4, x5, x6, x7) \<in>
      {(0, 1.15, 1.00, 1.45, 2.35, 0.95, 0.05, 0.40) ..
       (0, 1.25, 1.10, 1.55, 2.45, 1.05, 0.15, 0.50)} \<longrightarrow>
  t \<in> ll.existence_ivl0 (s, x1, x2, x3, x4, x5, x6, x7) \<and>
  ll.flow0 (s, x1, x2, x3, x4, x5, x6, x7) t \<in>
    {(19.99, 0.8, 0.3, 0.5, 2.4, 0.1, 0.0, 0.25) ..
     (20, 1.0, 0.5, 0.7, 3.0, 0.3, 0.1, 0.35)}"
  by (tactic \<open>ode_bnds_tac  @{thms laub_fas_def} 30 60 30 13 [(0, 4, "0x000000")] (* "out_ll_005.out" *) "" @{context} 1\<close>)

theorem ll_010:
  "t \<in> {10 .. 10} \<longrightarrow>
  (s, x1, x2, x3, x4, x5, x6, x7) \<in>
      {(0, 1.10, 0.95, 1.40, 2.30, 0.90, 0.00, 0.35) ..
       (0, 1.30, 1.15, 1.60, 2.50, 1.10, 0.20, 0.55)} \<longrightarrow>
  t \<in> ll.existence_ivl0 (s, x1, x2, x3, x4, x5, x6, x7) \<and>
  ll.flow0 (s, x1, x2, x3, x4, x5, x6, x7) t \<in>
    {(9.99, 0.2, -0.8, -0.4, -1.3, -1.2, 0.0, -0.5) ..
     (10,   1.8, 1.6, 1.8, 6.2, 1.7, 0.2, 1.2)}"
  by (tactic \<open>ode_bnds_tac  @{thms laub_fas_def} 30 60 30 13 [(0, 4, "0x0000ff")] (* "out_ll_010.out" *) ""  @{context} 1\<close>)

end

subsection \<open>Van der Pol oscillator (with time and ``pseudo-invariant''\<close>
experiment begin

schematic_goal vdp_fas:
  "[1, X!2, X!3 * X!2 * (1 - (X!1)\<^sup>2) - X!1, 0 \<comment> \<open>\<mu>'\<close> ] = interpret_floatariths ?fas X"
  by (reify_floatariths)

concrete_definition vdp_fas uses vdp_fas

interpretation vdp: ode_interpretation true_form UNIV vdp_fas "\<lambda>(t, x, y, \<mu>). (1, y, \<mu> * y * (1 - x\<^sup>2) - x, 0)::real*real*real*real"
  "n::4" for n
  by standard
    (auto simp: vdp_fas_def less_Suc_eq_0_disj nth_Basis_list_prod Basis_list_real_def
      mk_ode_ops_def eucl_of_list_prod power2_eq_square inverse_eq_divide intro!: isFDERIV_I)

abbreviation "vdp_ro \<equiv> ro 2 10 7 2 2 2"

lemma vdp_ro: "TAG_reach_optns vdp_ro" by simp

lemma vdp_start: "TAG_sctn False" by simp

lemma poincare_section_rep1:
  "{(7::real, -3::real, -3::real, -10::real)..(7, 3, 3, 10)} = {eucl_of_list [7, -3, -3, -10]..eucl_of_list [7, 3, 3, 10]}"
  by (auto simp: eucl_of_list_prod)

lemma vdp_pi_1: "vdp.guards_invar DIM(real \<times> real \<times> real \<times> real) [([ysec4' (1,7) (3/2) (-2, 0) (-10, 10)], vdp_ro)]"
  by (auto simp: vdp.guards_invar_def)

lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_1 poincare_section_rep1
  shows "\<forall>x\<in>{(0, 1.25, 2.35, 1) .. (0, 1.55, 2.45, 1)}.
  vdp.returns_to   {(7, -3, -3, -10) .. (7, 3, 3, 10)} x \<and>
  vdp.poincare_map_from_outside {(7, -3, -3, -10) .. (7, 3, 3, 10)} x \<in> {(7, 0, 0, -10) .. (7, 3, 3, 10)}"
  by (tactic \<open>poincare_bnds_tac @{thms vdp_fas_def} 30 20 10 14 [(1, 2, "0x007f00")] (* "out_p1_vdp_mu1_0.out" *) ""  @{context} 1\<close>)


abbreviation "t2 \<equiv> 15/2"
lemma vdp_pi_2: "vdp.guards_invar DIM(real \<times> real \<times> real \<times> real) [([ysec4' (1,t2) (7/2/2) (-2, 0) (-10, 10)], vdp_ro),
  ([ysec4 (1,t2) (-3/2) (-1, 1) (-10, 10)], vdp_ro)]"
  by (auto simp: vdp.guards_invar_def)

lemma poincare_section_rep2:
  "{(t2::real, -30::real, -30::real, -10::real)..(t2, 30, 30, 10)} = {eucl_of_list [t2, -30, -30, -10]..eucl_of_list [t2, 30, 30, 10]}"
  by (auto simp: eucl_of_list_prod)

lemma
  notes [poincare_tac_theorems] = vdp_ro vdp_start vdp_pi_2 poincare_section_rep2
  shows "\<forall>x\<in>{(0, 1.55, 2.35, 2) .. (0, 1.85, 2.45, 2)}.
  vdp.returns_to   {(t2, -30, -30, -10) .. (t2, 30, 30, 10)} x \<and>
  vdp.poincare_map_from_outside {(t2, -30, -30, -10) .. (t2, 30, 30, 10)} x \<in> {(t2, -30, -30, -10) .. (t2, 30, 30, 10)}"
  by (tactic \<open>poincare_bnds_tac @{thms vdp_fas_def} 30 20 10 14 [(1, 2, "0x00007f")] (* "out_p1_vdp_mu2_0.out" *) "" @{context} 1\<close>)

end

end