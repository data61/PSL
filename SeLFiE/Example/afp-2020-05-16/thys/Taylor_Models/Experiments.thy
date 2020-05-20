theory Experiments
  imports Taylor_Models
    Affine_Arithmetic.Affine_Arithmetic
begin

instantiation interval::("{show, preorder}") "show" begin

context includes interval.lifting begin
lift_definition shows_prec_interval::
  "nat \<Rightarrow> 'a interval \<Rightarrow> char list \<Rightarrow> char list"
  is "\<lambda>p ivl s. (shows_string ''Interval'' o shows ivl) s" .


lift_definition shows_list_interval::
  "'a interval list \<Rightarrow> char list \<Rightarrow> char list"
  is "\<lambda>ivls s. shows_list ivls s" .

instance
  apply standard
  subgoal by transfer (auto simp: show_law_simps)
  subgoal by transfer (auto simp: show_law_simps)
  done
end

end

definition  split_largest_interval :: "float interval list \<Rightarrow> float interval list \<times> float interval list" where
"split_largest_interval xs = (case sort_key (uminus o snd) (zip [0..<length xs] (map (\<lambda>x. upper x - lower x) xs)) of Nil \<Rightarrow> ([], [])
  | (i, _)#_ \<Rightarrow> let x = xs! i in (xs[i:=Ivl (lower x) ((upper x + lower x)*Float 1 (-1))],
                 xs[i:=Ivl ((upper x + lower x)*Float 1 (-1)) (upper x)]))"

definition "Inf_tm p params tm =
  lower (compute_bound_tm p (replicate params (Ivl (-1) (1))) (replicate params (Ivl 0 0)) tm)"

primrec prove_pos::"bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat \<Rightarrow> nat \<Rightarrow> taylor_model list \<Rightarrow> taylor_model option) \<Rightarrow> float interval list list \<Rightarrow> bool" where
  "prove_pos prnt 0 p ord F X = (let _ = if prnt then print (STR ''# depth limit exceeded\<newline>'') else () in False)"
| "prove_pos prnt (Suc i) p ord F XXS =
    (case XXS of [] \<Rightarrow> True | (X#XS) \<Rightarrow>
    let
       params = length X;
       R = F p ord (tms_of_ivls X);
       _ = if prnt  then print (String.implode ((shows ''# '' o shows (map (\<lambda>ivl. (lower ivl, upper ivl)) X)) ''\<newline>'')) else ()
    in
    if R \<noteq> None \<and> 0 < Inf_tm p params (the R)
    then let _ = if prnt then print (STR ''# Success\<newline>'') else () in prove_pos prnt i p ord F XS
    else let _ = if prnt then print (String.implode ((shows ''# Split ('' o shows ((map_option (Inf_tm p params)) R) o shows '')'') ''\<newline>'')) else () in case split_largest_interval X of (a, b) \<Rightarrow>
      prove_pos prnt i p ord F (a#b#XS))"

hide_const (open) prove_pos_slp

definition "prove_pos_slp prnt prec ord fa i xs = (let slp = slp_of_fas [fa] in prove_pos prnt i prec ord (\<lambda>p ord xs.
  case approx_slp prec ord 1 slp xs of None \<Rightarrow> None | Some [x] \<Rightarrow> Some x | Some _ \<Rightarrow> None) xs)"

experiment begin

unbundle floatarith_notation

abbreviation "schwefel \<equiv>
  (5.8806 / 10 ^ 10) + (Var 0 - (Var 1)^\<^sub>e2)^\<^sub>e2 + (Var 1 - 1)^\<^sub>e2 + (Var 0 - (Var 2)^\<^sub>e2)^\<^sub>e2 + (Var 2 - 1)^\<^sub>e2"

lemma "prove_pos_slp True 30 0 schwefel 100000 [replicate 3 (Ivl (-10) 10)]"
  by eval

abbreviation "delta6 \<equiv> (Var 0 * Var 3 * (-Var 0 + Var 1 + Var 2 - Var 3 + Var 4 + Var 5) +
    Var 1 * Var 4 * ( Var 0 - Var 1 + Var 2 + Var 3 - Var 4 + Var 5) +
    Var 2 * Var 5 * ( Var 0 + Var 1 - Var 2 + Var 3 + Var 4 - Var 5)
   - Var 1 * Var 2 * Var 3
   - Var 0 * Var 2 * Var 4
   - Var 0 * Var 1 * Var 5
   - Var 3 * Var 4 * Var 5)"

lemma "prove_pos_slp True 30 3 delta6 10000 [replicate 6 (Ivl 4 (Float 104045 (-14)))]"
  by eval

abbreviation "caprasse \<equiv> (3.1801 + - Var 0 * (Var 2) ^\<^sub>e 3 + 4 * Var 1 * (Var 2)^\<^sub>e2 * Var 3 +
    4 * Var 0 * Var 2 * (Var 3)^\<^sub>e2 + 2 * Var 1 * (Var 3)^\<^sub>e3 + 4 * Var 0 * Var 2 + 4 * (Var 2)^\<^sub>e2 - 10 * Var 1 * Var 3 +
    -10 * (Var 3)^\<^sub>e2 + 2)"

lemma "prove_pos_slp True 30 2 caprasse 10000 [replicate 4 (Ivl (-Float 1 (-1)) (Float 1 (-1)))]"
  by eval

abbreviation "magnetism \<equiv>
  0.25001 + (Var 0)^\<^sub>e2 + 2 * (Var 1)^\<^sub>e2 + 2 * (Var 2)^\<^sub>e2 + 2 * (Var 3)^\<^sub>e2 + 2 * (Var 4)^\<^sub>e2 + 2 * (Var 5)^\<^sub>e2 +
    2 * (Var 6)^\<^sub>e2 - Var 0"

end

end
