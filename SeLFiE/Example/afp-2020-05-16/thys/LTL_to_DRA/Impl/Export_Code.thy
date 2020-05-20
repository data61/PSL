(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Code Generation\<close>

theory Export_Code
  imports Main LTL_Compat LTL_Rabin_Impl 
    "HOL-Library.AList_Mapping" (* Future, Performance: Replace by LC *) 
    LTL.Rewriting
    "HOL-Library.Code_Target_Numeral" 
begin

subsection \<open>External Interface\<close>

\<comment> \<open>Fix the type to match the type of the LTL parser\<close>

definition 
  "ltlc_to_rabin eager mode (\<phi>\<^sub>c :: String.literal ltlc) \<equiv>
    (let
      \<phi>\<^sub>n = ltlc_to_ltln \<phi>\<^sub>c;
      \<Sigma> = map set (subseqs (atoms_list \<phi>\<^sub>n));
      \<phi> = ltln_to_ltl (simplify mode \<phi>\<^sub>n)
     in
      (if eager then ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU> \<Sigma> \<phi> else ltl_to_generalized_rabin\<^sub>C_af \<Sigma> \<phi>))"

theorem ltlc_to_rabin_exec_correct:
  assumes "range w \<subseteq> Pow (atoms_ltlc \<phi>\<^sub>c)"
  shows "w \<Turnstile>\<^sub>c \<phi>\<^sub>c \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltlc_to_rabin eager mode \<phi>\<^sub>c) w" 
  (is "?lhs = ?rhs")
proof -
  let ?\<phi>\<^sub>n = "ltlc_to_ltln \<phi>\<^sub>c"
  let ?\<Sigma> = "map set (subseqs (atoms_list ?\<phi>\<^sub>n))"
  let ?\<phi> = "ltln_to_ltl (simplify mode ?\<phi>\<^sub>n)"

  have "set ?\<Sigma> = Pow (atoms_ltln ?\<phi>\<^sub>n)"
    unfolding atoms_list_correct[symmetric] subseqs_powset[symmetric] list.set_map ..  
  hence R: "range w \<subseteq> set ?\<Sigma>"
    using assms ltlc_to_ltln_atoms[symmetric] by metis

  have "w \<Turnstile>\<^sub>c \<phi>\<^sub>c \<longleftrightarrow> w \<Turnstile> ?\<phi>"
    by (simp only: ltlc_to_ltln_semantics simplify_correct ltln_to_ltl_semantics)
  also
  have "\<dots> \<longleftrightarrow> ?rhs"
    using ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU>_correct[OF R] ltl_to_generalized_rabin\<^sub>C_af_correct[OF R] 
    unfolding ltlc_to_rabin_def Let_def by auto
  finally
  show ?thesis
    by simp
qed

subsection \<open>Normalize Equivalence Classes During DFS-Search\<close>

fun norm_rep
where
  "norm_rep (i, (q, \<nu>, p)) (q', \<nu>', p') = (
    let 
      eq_q = (q = q'); eq_p = (p = p');
      q'' = if eq_q then q' else if q = p' then p' else q;
      p'' = if eq_p then p' else if p = q' then q' else p
    in 
      (i | (eq_q & eq_p & \<nu> = \<nu>'), q'', \<nu>, p''))"

fun norm_fold :: "('a, 'b) transition \<Rightarrow> ('a, 'b) transition list \<Rightarrow> (bool * 'a * 'b * 'a)"
where
  "norm_fold (q, \<nu>, p) xs = foldl_break norm_rep fst (False, q, \<nu>, if q = p then q else p) xs"

definition norm_insert :: "('a, 'b) transition \<Rightarrow> ('a, 'b) transition list \<Rightarrow> (bool * ('a, 'b) transition list)"
where
  "norm_insert x xs \<equiv> let (i, x') = norm_fold x xs in if i then (i, xs) else (i, x' # xs)" 

lemma norm_fold:
  "norm_fold (q, \<nu>, p) xs = ((q, \<nu>, p) \<in> set xs, q, \<nu>, p)"
proof (induction xs rule: rev_induct)
  case (snoc x xs)
    obtain q' \<nu>' p' where x_def: "x = (q', \<nu>', p')"
      by (blast intro: prod_cases3)
    show ?case
      using snoc by (auto simp add: x_def foldl_break_append)
qed simp  

lemma norm_insert: 
  "norm_insert x xs = (x \<in> set xs, List.insert x xs)"
proof -
  obtain q \<nu> p where x_def: "x = (q, \<nu>, p)"
    by (blast intro: prod_cases3)
  show ?thesis
    unfolding x_def norm_insert_def norm_fold by simp
qed
 
declare list_dfs_def [code del]
declare norm_insert_def [code_unfold]

lemma list_dfs_norm_insert [code]: 
  "list_dfs succ S [] = S"
  "list_dfs succ S (x # xs) = (let (memb, S') = norm_insert x S in list_dfs succ S' (if memb then xs else succ x @ xs))"
  unfolding list_dfs_def Let_def norm_insert by simp+ 

subsection \<open>Register Code Equations\<close>

lemma [code]:
  "\<up>\<Delta>\<^sub>\<times> f (AList_Mapping.Mapping xs) c = AList_Mapping.Mapping (map_ran (\<lambda>a b. f a b c) xs)"
proof -
  have "\<And>x. (\<Delta>\<^sub>\<times> f (map_of xs) c) x = (map_of (map (\<lambda>(k, v). (k, f k v c)) xs)) x"
    by (induction xs) auto
  thus ?thesis
    by (transfer; simp add: map_ran_def)
qed

lemmas ltl_to_rabin_base_code_export [code, code_unfold] =
  ltl_to_rabin_base_code_def.ltl_to_generalized_rabin\<^sub>C.simps
  ltl_to_rabin_base_code_def.reachable_transitions\<^sub>C_def 
  ltl_to_rabin_base_code_def.mappings\<^sub>C_code 
  ltl_to_rabin_base_code_def.delta\<^sub>C.simps
  ltl_to_rabin_base_code_def.initial\<^sub>C.simps 
  ltl_to_rabin_base_code_def.Acc_inf\<^sub>C.simps 
  ltl_to_rabin_base_code_def.Acc_fin\<^sub>C.simps
  ltl_to_rabin_base_code_def.max_rank_of\<^sub>C_def

lemmas M_fin\<^sub>C_lhs [code del, code_unfold] = 
  M_fin\<^sub>C_af\<^sub>\<UU>_lhs_def M_fin\<^sub>C_af_lhs_def 

\<comment> \<open>Test code export\<close>
export_code true\<^sub>c Iff_ltlc Nop true Abs AList_Mapping.Mapping set ltlc_to_rabin checking

\<comment> \<open>Export translator (and also constructors)\<close>
export_code true\<^sub>c Iff_ltlc Nop true Abs AList_Mapping.Mapping set ltlc_to_rabin 
  in SML module_name LTL file \<open>../Code/LTL_to_DRA_Translator.sml\<close>

end
