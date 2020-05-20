section\<open>Examples on Proving Inequalities\<close>
theory Ex_Ineqs
  imports
    Affine_Code
    Print
    Float_Real
begin


definition "plotcolors =
  [[(0, 1, ''0x000000'')],

   [(0, 2, ''0xff0000''),
    (1, 2, ''0x7f0000'')],

   [(0, 3, ''0x00ff00''),
    (1, 3, ''0x00aa00''),
    (2, 3, ''0x005500'')],

   [(1, 4, ''0x0000ff''),
    (2, 4, ''0x0000c0''),
    (3, 4, ''0x00007f''),
    (0, 4, ''0x00003f'')],

   [(0, 5, ''0x00ffff''),
    (1, 5, ''0x00cccc''),
    (2, 5, ''0x009999''),
    (3, 5, ''0x006666''),
    (4, 5, ''0x003333'')],

  [(0, 6, ''0xff00ff''),
    (1, 6, ''0xd500d5''),
    (2, 6, ''0xaa00aa''),
    (3, 6, ''0x800080''),
    (4, 6, ''0x550055''),
    (5, 6, ''0x2a002a'')]]"


primrec prove_pos::"(nat * nat * string) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    (nat \<Rightarrow> real aform list \<Rightarrow> real aform option) \<Rightarrow> real aform list list \<Rightarrow> bool" where
  "prove_pos prnt 0 p F X = (let _ = if prnt \<noteq> [] then print (STR ''# depth limit exceeded\<newline>'') else () in False)"
| "prove_pos prnt (Suc i) p F XXS =
    (case XXS of [] \<Rightarrow> True | (X#XS) \<Rightarrow>
    let
       R = F p X;
       _ = if prnt \<noteq> [] then print (String.implode ((shows ''# '' o shows_box_of_aforms_hr X) ''\<newline>'')) else ();
        _ = fold (\<lambda>(a, b, c) _. print (String.implode (shows_segments_of_aform a b X c ''\<newline>''))) prnt ()
    in
    if R \<noteq> None \<and> 0 < Inf_aform' p (the R)
    then let _ = if prnt \<noteq> [] then print (STR ''# Success\<newline>'') else () in prove_pos prnt i p F XS
    else let _ = if prnt \<noteq> [] then print (STR ''# Split\<newline>'') else () in case split_aforms_largest_uncond X of (a, b) \<Rightarrow>
      prove_pos prnt i p F (a#b#XS))"

definition "prove_pos_slp prnt p fa i xs = (let slp = slp_of_fas [fa] in prove_pos prnt i p (\<lambda>p xs.
  case approx_slp_outer p 1 slp xs of None \<Rightarrow> None | Some [x] \<Rightarrow> Some x | Some _ \<Rightarrow> None) xs)"

text\<open>\label{sec:examples}\<close>

experiment begin

unbundle floatarith_notation

text \<open>The examples below are taken from
  @{url "http://link.springer.com/chapter/10.1007/978-3-642-38088-4_26"},
  ``Formal Verification of Nonlinear Inequalities with Taylor Interval Approximations'',
  Alexey Solovyev, Thomas C. Hales,
  NASA Formal Methods 2013, LNCS 7871
\<close>

definition "schwefel =
  (5.8806 / 10 ^ 10) + (Var 0 - (Var 1)^\<^sub>e2)^\<^sub>e2 + (Var 1 - 1)^\<^sub>e2 + (Var 0 - (Var 2)^\<^sub>e2)^\<^sub>e2 + (Var 2 - 1)^\<^sub>e2"

lemma schwefel:
  "5.8806 / 10 ^ 10 + (x0 - (x1)\<^sup>2)\<^sup>2 + (x1 - 1)\<^sup>2 + (x0 - (x2)\<^sup>2)\<^sup>2 + (x2 - 1)\<^sup>2 =
  interpret_floatarith schwefel [x0, x1, x2]"
  by (simp add: schwefel_def)

lemma "prove_pos_slp [] 30 schwefel 100000 [aforms_of_ivls [-10,-10,-10] [10,10,10]]"
  unfolding schwefel_def
  by eval

definition "delta6 = (Var 0 * Var 3 * (-Var 0 + Var 1 + Var 2 - Var 3 + Var 4 + Var 5) +
    Var 1 * Var 4 * ( Var 0 - Var 1 + Var 2 + Var 3 - Var 4 + Var 5) +
    Var 2 * Var 5 * ( Var 0 + Var 1 - Var 2 + Var 3 + Var 4 - Var 5)
   - Var 1 * Var 2 * Var 3
   - Var 0 * Var 2 * Var 4
   - Var 0 * Var 1 * Var 5
   - Var 3 * Var 4 * Var 5)"

schematic_goal delta6:
  "(x0 * x3 * (-x0 + x1 + x2 - x3 + x4 + x5) +
    x1 * x4 * ( x0 - x1 + x2 + x3 - x4 + x5) +
    x2 * x5 * ( x0 + x1 - x2 + x3 + x4 - x5)
   - x1 * x2 * x3
   - x0 * x2 * x4
   - x0 * x1 * x5
   - x3 * x4 * x5) = interpret_floatarith delta6 [x0, x1, x2, x3, x4, x5]"
  by (simp add: delta6_def)

lemma "prove_pos_slp [] 20 delta6 10000 [aforms_of_ivls (replicate 6 4) (replicate 6 (FloatR 104045 (-14)))]"
  unfolding delta6_def
  by eval

definition "caprasse = (3.1801 + - Var 0 * (Var 2) ^\<^sub>e 3 + 4 * Var 1 * (Var 2)^\<^sub>e2 * Var 3 +
    4 * Var 0 * Var 2 * (Var 3)^\<^sub>e2 + 2 * Var 1 * (Var 3)^\<^sub>e3 + 4 * Var 0 * Var 2 + 4 * (Var 2)^\<^sub>e2 - 10 * Var 1 * Var 3 +
    -10 * (Var 3)^\<^sub>e2 + 2)"

schematic_goal caprasse:
  "(3.1801 + - xs!0 * (xs!2) ^ 3 + 4 * xs!1 * (xs!2)\<^sup>2 * xs!3 +
    4 * xs!0 * xs!2 * (xs!3)\<^sup>2 + 2 * xs!1 * (xs!3)^3 + 4 * xs!0 * xs!2 + 4 * (xs!2)\<^sup>2 - 10 * xs!1 * xs!3 +
    -10 * (xs!3)\<^sup>2 + 2) = interpret_floatarith caprasse xs"
  by (simp add: caprasse_def)

lemma "prove_pos_slp [] 20 caprasse 10000 [aforms_of_ivls (replicate 4 (1/2)) (replicate 4 (1/2))]"
  unfolding caprasse_def
  by eval


definition "magnetism =
  0.25001 + (Var 0)^\<^sub>e2 + 2 * (Var 1)^\<^sub>e2 + 2 * (Var 2)^\<^sub>e2 + 2 * (Var 3)^\<^sub>e2 + 2 * (Var 4)^\<^sub>e2 + 2 * (Var 5)^\<^sub>e2 +
    2 * (Var 6)^\<^sub>e2 - Var 0"
schematic_goal magnetism:
  "0.25001 + (xs!0)\<^sup>2 + 2 * (xs!1)\<^sup>2 + 2 * (xs!2)\<^sup>2 + 2 * (xs!3)\<^sup>2 + 2 * (xs!4)\<^sup>2 + 2 * (xs!5)\<^sup>2 +
    2 * (xs!6)\<^sup>2 - xs!0 = interpret_floatarith magnetism xs"
  by (simp add: magnetism_def)

end

end
