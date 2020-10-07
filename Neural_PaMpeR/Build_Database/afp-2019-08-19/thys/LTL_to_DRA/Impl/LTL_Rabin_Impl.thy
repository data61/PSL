(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Executable Translation from LTL to Rabin Automata\<close>

theory LTL_Rabin_Impl
  imports Main "../Auxiliary/Map2" "../LTL_Rabin" "../LTL_Rabin_Unfold_Opt" af_Impl Mojmir_Rabin_Impl
begin

subsection \<open>Template\<close>

subsubsection \<open>Definition\<close>

locale ltl_to_rabin_base_code_def = ltl_to_rabin_base_def +
  fixes
    M_fin\<^sub>C :: "'a ltl \<Rightarrow> ('a ltl, nat) mapping \<Rightarrow> ('a ltl\<^sub>P \<times> ('a ltl, 'a ltl\<^sub>P list) mapping, 'a set) transition \<Rightarrow> bool"
begin

\<comment> \<open>Transition Function and Initial State\<close>

fun delta\<^sub>C
where
  "delta\<^sub>C \<Sigma> = \<delta> \<times> \<up>\<Delta>\<^sub>\<times> (nxt \<Sigma> \<delta>\<^sub>M o q\<^sub>0\<^sub>M o theG)"

fun initial\<^sub>C
where
  "initial\<^sub>C \<phi> = (q\<^sub>0 \<phi>, Mapping.tabulate (G_list \<phi>) (init o q\<^sub>0\<^sub>M o theG))"

\<comment> \<open>Acceptance Condition\<close>

definition max_rank_of\<^sub>C
where
  "max_rank_of\<^sub>C \<Sigma> \<psi> = card (Set.filter (Not o semi_mojmir_def.sink (set \<Sigma>) \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<psi>))) (Q\<^sub>L \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<psi>))))"

fun Acc_fin\<^sub>C
where
  "Acc_fin\<^sub>C \<Sigma> \<pi> \<chi> ((_, m'), \<nu>, _) = (
    let 
      t = (the (Mapping.lookup m' \<chi>), \<nu>, []); \<comment> \<open>Third element is unused. Hence it is safe to pass a dummy value.\<close>
      \<G> = Mapping.keys \<pi>
    in 
      fail_filt \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) (ltl_prop_entails_abs \<G>) t 
    \<or> merge_filt \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) (ltl_prop_entails_abs \<G>) (the (Mapping.lookup \<pi> \<chi>)) t)"

fun Acc_inf\<^sub>C
where
  "Acc_inf\<^sub>C \<pi> \<chi> ((_, m'), \<nu>, _) = (
    let 
      t = (the (Mapping.lookup m' \<chi>), \<nu>, []); \<comment> \<open>Third element is unused. Hence it is safe to pass a dummy value.\<close>
      \<G> = Mapping.keys \<pi>
    in 
      succeed_filt \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) (ltl_prop_entails_abs \<G>) (the (Mapping.lookup \<pi> \<chi>)) t)"

definition mappings\<^sub>C :: "'a set list \<Rightarrow> 'a ltl \<Rightarrow> ('a ltl, nat) mapping set"
where
  "mappings\<^sub>C \<Sigma> \<phi> \<equiv> {\<pi>. Mapping.keys \<pi> \<subseteq> \<^bold>G \<phi> \<and> (\<forall>\<chi> \<in> (Mapping.keys \<pi>). the (Mapping.lookup \<pi> \<chi>) < max_rank_of\<^sub>C \<Sigma> \<chi>)}"

definition reachable_transitions\<^sub>C
where
  "reachable_transitions\<^sub>C \<Sigma> \<phi> \<equiv> \<delta>\<^sub>L \<Sigma> (delta\<^sub>C (set \<Sigma>)) (initial\<^sub>C \<phi>)"

fun ltl_to_generalized_rabin\<^sub>C
where
  "ltl_to_generalized_rabin\<^sub>C \<Sigma> \<phi> = (
    let
      \<delta>_LTS = reachable_transitions\<^sub>C \<Sigma> \<phi>; 
      \<alpha>_fin_filter = \<lambda>\<pi> t. M_fin\<^sub>C \<phi> \<pi> t \<or> (\<exists>\<chi> \<in> Mapping.keys \<pi>. Acc_fin\<^sub>C (set \<Sigma>) \<pi> \<chi> t);
      to_pair = \<lambda>\<pi>. (Set.filter (\<alpha>_fin_filter \<pi>) \<delta>_LTS, (\<lambda>\<chi>. Set.filter (Acc_inf\<^sub>C \<pi> \<chi>) \<delta>_LTS) ` Mapping.keys \<pi>);
      \<alpha> = to_pair ` (mappings\<^sub>C \<Sigma> \<phi>) \<comment> \<open>Multi-thread here!, prove \<open>mappings (set \<dots>)\<close> equation\<close>
    in
      (\<delta>_LTS, initial\<^sub>C \<phi>, \<alpha>))"

lemma mappings\<^sub>C_code:
  "mappings\<^sub>C \<Sigma> \<phi> = (
    let 
      Gs = G_list \<phi>; 
      max_rank = Mapping.lookup (Mapping.tabulate Gs (max_rank_of\<^sub>C \<Sigma>))
    in 
      set (concat (map (mapping_generator_list (\<lambda>x. [0 ..< the (max_rank x)])) (subseqs Gs))))"
  (is "?lhs = ?rhs")
proof -
  {
    fix xs :: "'a ltl list"
    have subset_G: "\<And>x. x \<in> set (subseqs (xs)) \<Longrightarrow> set x \<subseteq> set xs"
      apply (induction xs)
      apply (simp)
      by (insert subseqs_powset; blast)
  }
  hence subset_G: "\<And>x. x \<in> set (subseqs (G_list \<phi>)) \<Longrightarrow> set x \<subseteq> \<^bold>G \<phi>"
    unfolding G_eq_G_list by auto

  have "?lhs = \<Union>{{\<pi>. Mapping.keys \<pi> = xs \<and> (\<forall>\<chi>\<in>Mapping.keys \<pi>. the (Mapping.lookup \<pi> \<chi>) < max_rank_of\<^sub>C \<Sigma> \<chi>)} | xs. xs \<in> set ` (set (subseqs (G_list \<phi>)))}"
    unfolding mappings\<^sub>C_def G_eq_G_list subseqs_powset by auto
  also
  have "\<dots> = \<Union>{{\<pi>. Mapping.keys \<pi> = set xs \<and> (\<forall>\<chi> \<in> set xs. the (Mapping.lookup \<pi> \<chi>) < max_rank_of\<^sub>C \<Sigma> \<chi>)} |
       xs. xs \<in> set (subseqs (G_list \<phi>))}"
    by auto
  also
  have "\<dots> = ?rhs"
    using subset_G 
      by (auto simp add: Let_def mapping_generator_code [symmetric]
        lookup_tabulate G_eq_G_list [symmetric] mapping_generator_set_eq
        cong del: SUP_cong_simp; blast)
  finally
  show ?thesis
    by simp
qed

lemma reach_delta_initial:
  assumes "(x, y) \<in> reach \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>)"
  assumes "\<chi> \<in> \<^bold>G \<phi>"
  shows "Mapping.lookup y \<chi> \<noteq> None" (is ?t1)
    and "distinct (the (Mapping.lookup y \<chi>))" (is ?t2)
proof -
  from assms(1) obtain w i where y_def: "y = run (\<up>\<Delta>\<^sub>\<times> (nxt \<Sigma> \<delta>\<^sub>M o q\<^sub>0\<^sub>M o theG)) (Mapping.tabulate (G_list \<phi>) (init o q\<^sub>0\<^sub>M o theG)) w i"
    unfolding reach_def delta\<^sub>C.simps initial\<^sub>C.simps simple_product_run by fast
  from assms(2) nxt_run_distinct show ?t1 
    unfolding y_def using product_abs_run_Some[of "Mapping.tabulate (G_list \<phi>) (init o q\<^sub>0\<^sub>M o theG)" \<chi>] unfolding G_eq_G_list 
    unfolding lookup_tabulate by fastforce
  with nxt_run_distinct show ?t2
    unfolding y_def using lookup_tabulate  
    by (metis (no_types) G_eq_G_list assms(2) comp_eq_dest_lhs option.sel product_abs_run_Some) 
qed

end

subsubsection \<open>Correctness\<close>

fun abstract_state :: "'x \<times> ('y, 'z list) mapping \<Rightarrow> 'x \<times> ('y \<rightharpoonup> 'z \<rightharpoonup> nat)" 
where
  "abstract_state (a, b) = (a, (map_option rk) o (Mapping.lookup b))"

fun abstract_transition
where
  "abstract_transition (q, \<nu>, q') = (abstract_state q, \<nu>, abstract_state q')"

locale ltl_to_rabin_base_code = ltl_to_rabin_base + ltl_to_rabin_base_code_def + 
  assumes 
    M_fin\<^sub>C_correct: "\<lbrakk>t \<in> reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>); dom \<pi> \<subseteq> \<^bold>G \<phi>\<rbrakk> \<Longrightarrow>
      abstract_transition t \<in> M_fin \<pi> = M_fin\<^sub>C \<phi> (Mapping.Mapping \<pi>) t"
begin

lemma finite_reach\<^sub>C:
  "finite (reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>))"
proof -
  note finite_reach'
  moreover
  have "(\<And>x. x \<in> \<^bold>G \<phi> \<Longrightarrow> finite (reach \<Sigma> ((nxt \<Sigma> \<delta>\<^sub>M o q\<^sub>0\<^sub>M o theG) x) ((init o q\<^sub>0\<^sub>M o theG) x)))"
    using semi_mojmir.finite_Q[OF semi_mojmir] unfolding G_eq_G_list semi_mojmir_def.Q\<^sub>E_def by simp 
  hence "finite (reach \<Sigma> (\<up>\<Delta>\<^sub>\<times> (nxt \<Sigma> \<delta>\<^sub>M o q\<^sub>0\<^sub>M o theG)) (Mapping.tabulate (G_list \<phi>) (init o q\<^sub>0\<^sub>M o theG)))"
    by (metis (no_types) finite_reach_product_abs[OF finite_keys_tabulate] G_eq_G_list  keys_tabulate lookup_tabulate_Some)
  ultimately
  have "finite (reach \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>))"
    using finite_reach_simple_product by fastforce 
  thus ?thesis
    using finite_\<Sigma> by (simp add: finite_reach\<^sub>t) 
qed 

lemma max_rank_of\<^sub>C_eq:
  assumes "\<Sigma> = set \<Sigma>'"
  shows "max_rank_of\<^sub>C \<Sigma>' \<psi> = max_rank_of \<Sigma> \<psi>"
proof -
  interpret \<MM>: semi_mojmir "set \<Sigma>'" \<delta>\<^sub>M "q\<^sub>0\<^sub>M (theG \<psi>)" w
    using semi_mojmir assms by force
  show ?thesis
    unfolding max_rank_of_def max_rank_of\<^sub>C_def Q\<^sub>L_reach[OF \<MM>.finite_reach] semi_mojmir_def.max_rank_def
    by (simp add: Set.filter_def set_diff_eq assms)
qed

lemma reachable_transitions\<^sub>C_eq:
  assumes "\<Sigma> = set \<Sigma>'"
  shows "reachable_transitions\<^sub>C \<Sigma>' \<phi> = reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>)"
  by (simp only: reachable_transitions\<^sub>C_def \<delta>\<^sub>L_reach[OF finite_reach\<^sub>C[unfolded assms]] assms)

lemma run_abstraction_correct:
  "run (delta \<Sigma>) (initial \<phi>) w = abstract_state o (run (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>) w)"
proof -
  {
    fix i

    let ?\<delta>\<^sub>2 = "\<Delta>\<^sub>\<times> (\<lambda>\<chi>. semi_mojmir_def.step \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)))"
    let ?q\<^sub>2 = "\<iota>\<^sub>\<times> (\<^bold>G \<phi>) (\<lambda>\<chi>. semi_mojmir_def.initial (q\<^sub>0\<^sub>M (theG \<chi>)))"

    let ?\<delta>\<^sub>2' = "\<up>\<Delta>\<^sub>\<times> (nxt \<Sigma> \<delta>\<^sub>M o q\<^sub>0\<^sub>M o theG)"    
    let ?q\<^sub>2' = "Mapping.tabulate (G_list \<phi>) (init o q\<^sub>0\<^sub>M o theG)"
    
    {
      fix q
      assume "q \<notin> \<^bold>G \<phi>"
      hence "?q\<^sub>2 q = None" and "Mapping.lookup (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i) q = None"
        using G_eq_G_list product_abs_run_None by (simp, metis domIff keys_dom_lookup keys_tabulate)
      hence "run ?\<delta>\<^sub>2 ?q\<^sub>2 w i q = (\<lambda>m. (map_option rk) o (Mapping.lookup m)) (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i) q"
        using product_run_None by (simp del: nxt.simps rk.simps)
    }

    moreover 

    {
      fix q j
      assume "q \<in> \<^bold>G \<phi>"
      hence init: "?q\<^sub>2 q = Some (semi_mojmir_def.initial (q\<^sub>0\<^sub>M (theG q)))" 
        and "Mapping.lookup (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i) q = Some (run ((nxt \<Sigma> \<delta>\<^sub>M \<circ> q\<^sub>0\<^sub>M \<circ> theG) q) ((init \<circ> q\<^sub>0\<^sub>M \<circ> theG) q) w i)"
        apply (simp del: nxt.simps)  
        apply (metis G_eq_G_list \<open>q \<in> \<^bold>G \<phi>\<close> lookup_tabulate product_abs_run_Some) 
        done
      hence "run ?\<delta>\<^sub>2 ?q\<^sub>2 w i q = (\<lambda>m. (map_option rk) o (Mapping.lookup m)) (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i) q"
        unfolding product_run_Some[of "\<iota>\<^sub>\<times> (\<^bold>G \<phi>) (\<lambda>\<chi>. semi_mojmir_def.initial (q\<^sub>0\<^sub>M (theG \<chi>)))" q, OF init] 
        by (simp del: product.simps nxt.simps rk.simps; unfold map_of_map semi_mojmir.nxt_run_step_run[OF semi_mojmir]; simp) 
    }

    ultimately

    have "run ?\<delta>\<^sub>2 ?q\<^sub>2 w i = (\<lambda>m. (map_option rk) o (Mapping.lookup m)) (run ?\<delta>\<^sub>2' ?q\<^sub>2' w i)"
      by blast
  }
  hence "\<And>i. run (delta \<Sigma>) (initial \<phi>) w i = abstract_state (run (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>) w i)"
    using finite_\<Sigma> bounded_w by (simp add: simple_product_run comp_def del: simple_product.simps)
  thus ?thesis
    by auto
qed

lemma 
  assumes "t \<in> reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>)"
  assumes "\<chi> \<in> \<^bold>G \<phi>"
  shows Acc_fin\<^sub>C_correct: 
    "abstract_transition t \<in> Acc_fin \<Sigma> \<pi> \<chi> \<longleftrightarrow> Acc_fin\<^sub>C \<Sigma> (Mapping.Mapping \<pi>) \<chi> t" (is ?t1)
    and Acc_inf\<^sub>C_correct: 
    "abstract_transition t \<in> Acc_inf \<pi> \<chi> \<longleftrightarrow> Acc_inf\<^sub>C (Mapping.Mapping \<pi>) \<chi> t" (is ?t2)
proof -
  obtain x y \<nu> z z' where t_def [simp]: "t = ((x, y), \<nu>, (z, z'))"
    by (metis prod.collapse)
  have "(x, y) \<in> reach \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>)"
    and "(z, z') \<in> reach \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>)"
    using assms(1) unfolding reach\<^sub>t_def reach_def run\<^sub>t.simps t_def by blast+
  then obtain m m' where [simp]: "Mapping.lookup y \<chi> = Some m" 
    and "Mapping.lookup y \<chi> \<noteq> None" 
    and [simp]: "Mapping.lookup z' \<chi> = Some m'"
    using assms(2) by (blast dest: reach_delta_initial)+

  have FF [simp]: "fail_filt \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) (ltl_prop_entails_abs (dom \<pi>)) (the (Mapping.lookup y \<chi>), \<nu>, []) 
    = ((the (map_option rk (Mapping.lookup y \<chi>)), \<nu>, (\<lambda>x. Some 0)) \<in> mojmir_to_rabin_def.fail\<^sub>R \<Sigma> \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q})"
    unfolding option.map_sel[OF \<open>Mapping.lookup y \<chi> \<noteq> None\<close>] fail_filt_eq[where y = "[]", symmetric] by simp  

  have MF [simp]: "\<And>i. merge_filt \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) (ltl_prop_entails_abs (dom \<pi>)) i (the (Mapping.lookup y \<chi>), \<nu>, [])
    = ((the (map_option rk (Mapping.lookup y \<chi>)), \<nu>, (\<lambda>x. Some 0)) \<in> mojmir_to_rabin_def.merge\<^sub>R \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q} i)"
    unfolding option.map_sel[OF \<open>Mapping.lookup y \<chi> \<noteq> None\<close>] merge_filt_eq[where y = "[]", symmetric] by simp  

  have SF [simp]: "\<And>i. succeed_filt \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) (ltl_prop_entails_abs (dom \<pi>)) i (the (Mapping.lookup y \<chi>), \<nu>, [])
    = ((the (map_option rk (Mapping.lookup y \<chi>)), \<nu>, (\<lambda>x. Some 0)) \<in> mojmir_to_rabin_def.succeed\<^sub>R \<delta>\<^sub>M (q\<^sub>0\<^sub>M (theG \<chi>)) {q. dom \<pi> \<up>\<Turnstile>\<^sub>P q} i)"
    unfolding option.map_sel[OF \<open>Mapping.lookup y \<chi> \<noteq> None\<close>] succeed_filt_eq[where y = "[]", symmetric] by simp  

  note mojmir_to_rabin_def.fail\<^sub>R_def [simp] 
  note mojmir_to_rabin_def.merge\<^sub>R_def [simp]
  note mojmir_to_rabin_def.succeed\<^sub>R_def [simp]

  show ?t1 and ?t2 
    by (simp_all add: Let_def keys.abs_eq lookup.abs_eq del: rk.simps) 
       (rule; metis option.distinct(1) option.sel option.collapse rk_facts(1))+
qed


theorem ltl_to_generalized_rabin\<^sub>C_correct:
  assumes "\<Sigma> = set \<Sigma>'"
  shows "accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin \<Sigma> \<phi>) w \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltl_to_generalized_rabin\<^sub>C \<Sigma>' \<phi>) w" 
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  let ?\<delta> = "delta \<Sigma>"
  let ?q\<^sub>0 = "initial \<phi>"
 
  let ?\<delta>\<^sub>C = "delta\<^sub>C \<Sigma>"
  let ?q\<^sub>0\<^sub>C = "initial\<^sub>C \<phi>"
  let ?reach\<^sub>C = "reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>)"

  note reachable_transitions\<^sub>C_simp[simp] = reachable_transitions\<^sub>C_eq[OF assms] 
  note max_rank_of\<^sub>C_simp[simp] = max_rank_of\<^sub>C_eq[OF assms]

  {
    fix \<pi> :: "'a ltl \<Rightarrow> nat option"
    assume \<pi>_wellformed: "dom \<pi> \<subseteq> \<^bold>G \<phi>"
       
    let ?F = "(M_fin \<pi> \<union> \<Union>{Acc_fin \<Sigma> \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>}, {Acc_inf \<pi> \<chi> | \<chi>. \<chi> \<in> dom \<pi>})"
    let ?fin = "{t. M_fin\<^sub>C \<phi> (Mapping.Mapping \<pi>) t} \<union> {t. \<exists>\<chi> \<in> dom \<pi>. Acc_fin\<^sub>C \<Sigma> (Mapping.Mapping \<pi>) \<chi> t}"
    let ?inf = "{{t. Acc_inf\<^sub>C (Mapping.Mapping \<pi>) \<chi> t} | \<chi>. \<chi> \<in> dom \<pi>}"
    
    have finite_reach': "finite (reach\<^sub>t \<Sigma> (delta \<Sigma>) (initial \<phi>))"
      by (meson finite_reach finite_\<Sigma> finite_reach\<^sub>t) 

    have run_abstraction_correct': 
      "run\<^sub>t (delta \<Sigma>) (initial \<phi>) w = abstract_transition o (run\<^sub>t (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>) w)"
      using run_abstraction_correct comp_def by auto

    have "accepting_pair\<^sub>G\<^sub>R ?\<delta> ?q\<^sub>0 ?F w \<longleftrightarrow> accepting_pair\<^sub>G\<^sub>R ?\<delta>\<^sub>C  ?q\<^sub>0\<^sub>C (?fin, ?inf) w" (is "?l \<longleftrightarrow> _")
      by (rule accepting_pair\<^sub>G\<^sub>R_abstract[OF finite_reach' finite_reach\<^sub>C bounded_w];
          insert \<open>dom \<pi> \<subseteq> \<^bold>G \<phi>\<close> M_fin\<^sub>C_correct Acc_fin\<^sub>C_correct Acc_inf\<^sub>C_correct run_abstraction_correct'; blast)
    also 
    have "\<dots> \<longleftrightarrow> accepting_pair\<^sub>G\<^sub>R_LTS ?reach\<^sub>C ?q\<^sub>0\<^sub>C (?fin \<inter> ?reach\<^sub>C, (\<lambda>I. I \<inter> ?reach\<^sub>C) ` ?inf) w" (is "_ \<longleftrightarrow> ?r")
      using bounded_w by (simp only: accepting_pair\<^sub>G\<^sub>R_LTS[symmetric] accepting_pair\<^sub>G\<^sub>R_restrict[symmetric])
    finally
    have "?l \<longleftrightarrow> ?r" .
  }
 
  note X = this

  {
    assume ?lhs
    then obtain \<pi> where 1: "dom \<pi> \<subseteq> \<^bold>G \<phi>" 
      and 2: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> the (\<pi> \<chi>) < max_rank_of \<Sigma> \<chi>"
      and 3: "accepting_pair\<^sub>G\<^sub>R (delta \<Sigma>) (initial \<phi>) (M_fin \<pi> \<union> \<Union>{Acc_fin \<Sigma> \<pi> \<chi> |\<chi>. \<chi> \<in> dom \<pi>}, {Acc_inf \<pi> \<chi> |\<chi>. \<chi> \<in> dom \<pi>}) w" 
      by auto
    
    define \<pi>' where "\<pi>' = Mapping.Mapping \<pi>"
    
    have "dom \<pi> = Mapping.keys \<pi>'" and "\<pi> = Mapping.lookup \<pi>'"
      by (simp_all add: keys.abs_eq lookup.abs_eq \<pi>'_def)

    have acc_pair_LTS: "accepting_pair\<^sub>G\<^sub>R_LTS ?reach\<^sub>C ?q\<^sub>0\<^sub>C (({t. M_fin\<^sub>C \<phi> \<pi>' t} \<union> {t. \<exists>\<chi> \<in> Mapping.keys \<pi>'. Acc_fin\<^sub>C \<Sigma> \<pi>' \<chi> t}) \<inter> ?reach\<^sub>C,
        (\<lambda>I. I \<inter> ?reach\<^sub>C) ` {{t. Acc_inf\<^sub>C \<pi>' \<chi> t} | \<chi>. \<chi> \<in> Mapping.keys \<pi>'}) w"
      using 3 unfolding X[OF 1] unfolding \<open>dom \<pi> = Mapping.keys \<pi>'\<close> \<pi>'_def[symmetric] by simp

    show ?rhs
      apply (unfold ltl_to_generalized_rabin\<^sub>C.simps Let_def)
      apply (intro accept\<^sub>G\<^sub>R_LTS_I)
      apply (insert acc_pair_LTS; auto simp add: assms[symmetric] mappings\<^sub>C_def)
      apply (insert 1 2; unfold  \<open>dom \<pi> = Mapping.keys \<pi>'\<close>; unfold \<open>\<pi> = Mapping.lookup \<pi>'\<close>)
      by (auto simp add: assms[symmetric] Set.filter_def image_def mappings\<^sub>C_def)
  }
  
  moreover 

  {
    assume ?rhs
    obtain Fin Inf where "(Fin, Inf) \<in> snd (snd (ltl_to_generalized_rabin\<^sub>C \<Sigma>' \<phi>))"
      and 4: "accepting_pair\<^sub>G\<^sub>R_LTS ?reach\<^sub>C (initial\<^sub>C \<phi>) (Fin, Inf) w"
       using accept\<^sub>G\<^sub>R_LTS_E[OF \<open>?rhs\<close>] apply (simp add: Let_def assms del: accept\<^sub>G\<^sub>R_LTS.simps) by auto
    
    then obtain \<pi> where Y: "(Fin, Inf) = (Set.filter (\<lambda>t. M_fin\<^sub>C \<phi> \<pi> t \<or> (\<exists>\<chi> \<in> Mapping.keys \<pi>. Acc_fin\<^sub>C \<Sigma> \<pi> \<chi> t)) ?reach\<^sub>C,
        (\<lambda>\<chi>. Set.filter (Acc_inf\<^sub>C \<pi> \<chi>) ?reach\<^sub>C) ` (Mapping.keys \<pi>))"
        and 1: "Mapping.keys \<pi> \<subseteq> \<^bold>G \<phi>" and 2: "\<And>\<chi>. \<chi> \<in> Mapping.keys \<pi> \<Longrightarrow> the (Mapping.lookup \<pi> \<chi>) < max_rank_of \<Sigma> \<chi>"
      unfolding ltl_to_generalized_rabin\<^sub>C.simps Let_def fst_conv snd_conv mappings\<^sub>C_def assms reachable_transitions\<^sub>C_simp max_rank_of\<^sub>C_simp by auto
    define \<pi>' where "\<pi>' = Mapping.rep \<pi>"
    have "dom \<pi>' = Mapping.keys \<pi>" and "Mapping.Mapping \<pi>' = \<pi>"
      by (simp_all add: \<pi>'_def mapping.rep_inverse keys.rep_eq)
    have 1: "dom \<pi>' \<subseteq> \<^bold>G \<phi>" and 2: "\<And>\<chi>. \<chi> \<in> dom \<pi>' \<Longrightarrow> the (\<pi>' \<chi>) < max_rank_of \<Sigma> \<chi>"
      using 1 2 unfolding  \<pi>'_def Mapping.keys.rep_eq Mapping.mapping.rep_inverse by (simp add: lookup.rep_eq)+
    moreover
    have "({a \<in> reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>). M_fin\<^sub>C \<phi> \<pi> a \<or> (\<exists>\<chi>\<in>Mapping.keys \<pi>. Acc_fin\<^sub>C \<Sigma> \<pi> \<chi> a)}, {y. \<exists>x\<in>Mapping.keys \<pi>. y = {a \<in> reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>). Acc_inf\<^sub>C \<pi> x a}})
      = ((Collect (M_fin\<^sub>C \<phi> \<pi>) \<union> {t. \<exists>\<chi>\<in>Mapping.keys \<pi>. Acc_fin\<^sub>C \<Sigma> \<pi> \<chi> t}) \<inter> reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>), {y. \<exists>x\<in>{Collect (Acc_inf\<^sub>C \<pi> \<chi>) |\<chi>. \<chi> \<in> Mapping.keys \<pi>}. y = x \<inter> reach\<^sub>t \<Sigma> (delta\<^sub>C \<Sigma>) (initial\<^sub>C \<phi>)})" 
      by auto
    hence "accepting_pair\<^sub>G\<^sub>R (delta \<Sigma>) (initial \<phi>) (M_fin \<pi>' \<union> \<Union>{Acc_fin \<Sigma> \<pi>' \<chi> | \<chi>. \<chi> \<in> dom \<pi>'}, {Acc_inf \<pi>' \<chi> | \<chi>. \<chi> \<in> dom \<pi>'}) w"
      unfolding X[OF 1] using 4 unfolding Y Set.filter_def unfolding \<open>dom \<pi>' = Mapping.keys \<pi>\<close> \<open>Mapping.Mapping \<pi>' = \<pi>\<close> image_def by simp    
    ultimately
    show ?lhs  
      unfolding ltl_to_generalized_rabin.simps
      by (intro Rabin.accept\<^sub>G\<^sub>R_I, blast; auto) 
  }
qed

end 

subsection \<open>Generalized Deterministic Rabin Automaton (af)\<close>

definition M_fin\<^sub>C_af_lhs :: "'a ltl \<Rightarrow> ('a ltl, nat) mapping \<Rightarrow> ('a ltl, ('a ltl\<^sub>P list)) mapping \<Rightarrow> 'a ltl\<^sub>P"
where
  "M_fin\<^sub>C_af_lhs \<phi> \<pi> m' \<equiv> 
    let
      \<G> = Mapping.keys \<pi>;
      \<G>\<^sub>L = filter (\<lambda>x. x \<in> \<G>) (G_list \<phi>);
      mk_conj = \<lambda>\<chi>. foldl and_abs (Abs \<chi>) (map (\<up>eval\<^sub>G \<G>) (drop (the (Mapping.lookup \<pi> \<chi>)) (the (Mapping.lookup m' \<chi>))))
    in 
      \<up>And (map mk_conj \<G>\<^sub>L)"

fun M_fin\<^sub>C_af :: "'a ltl \<Rightarrow> ('a ltl, nat) mapping \<Rightarrow> ('a ltl\<^sub>P \<times> (('a ltl, ('a ltl\<^sub>P list)) mapping), 'a set) transition \<Rightarrow> bool"
where
  "M_fin\<^sub>C_af \<phi> \<pi> ((\<phi>', m'), _) = Not ((M_fin\<^sub>C_af_lhs \<phi> \<pi> m') \<up>\<longrightarrow>\<^sub>P  \<phi>')"

lemma M_fin\<^sub>C_af_correct:
  assumes "t \<in> reach\<^sub>t \<Sigma> (ltl_to_rabin_base_code_def.delta\<^sub>C \<up>af \<up>af\<^sub>G Abs \<Sigma>) (ltl_to_rabin_base_code_def.initial\<^sub>C Abs Abs \<phi>)"
  assumes "dom \<pi> \<subseteq> \<^bold>G \<phi>"
  shows "abstract_transition t \<in> M_fin \<pi> = M_fin\<^sub>C_af \<phi> (Mapping.Mapping \<pi>) t"
proof -
  let ?delta = "ltl_to_rabin_base_code_def.delta\<^sub>C \<up>af \<up>af\<^sub>G Abs \<Sigma>"
  let ?initial = "ltl_to_rabin_base_code_def.initial\<^sub>C Abs Abs \<phi>"
  
  obtain x y \<nu> z z' where t_def [simp]: "t = ((x, y), \<nu>, (z, z'))"
    by (metis prod.collapse)
  have "(x, y) \<in> reach \<Sigma> ?delta ?initial"
    using assms(1) by (simp add: reach\<^sub>t_def reach_def; blast)
  hence N1: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> Mapping.lookup y \<chi> \<noteq> None"
    and D1: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> distinct (the (Mapping.lookup y \<chi>))"
    using assms(2) by (blast dest: ltl_to_rabin_base_code_def.reach_delta_initial)+

  {
    fix S
    let ?m' = "\<lambda>\<chi>. map_option rk (Mapping.lookup y \<chi>)"
    
    {
      fix \<chi>
      assume "\<chi> \<in> dom \<pi>"
      hence "S \<up>\<Turnstile>\<^sub>P (foldl and_abs (Abs \<chi>) (map (\<up>eval\<^sub>G (dom \<pi>)) (drop (the (\<pi> \<chi>)) (the (Mapping.lookup y \<chi>)))))
         \<longleftrightarrow> S \<up>\<Turnstile>\<^sub>P (Abs \<chi>) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (?m' \<chi>) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) q)"
        using D1[THEN drop_rk, of _ "the (\<pi> \<chi>)"] N1[THEN option.map_sel, of _ rk]
        by (auto simp add: foldl_LTLAnd_prop_entailment_abs)
    }

    hence "S \<up>\<Turnstile>\<^sub>P (M_fin\<^sub>C_af_lhs \<phi> (Mapping.Mapping \<pi>) y)
      \<longleftrightarrow> (\<forall>\<chi> \<in> dom \<pi>. S \<up>\<Turnstile>\<^sub>P (Abs \<chi>) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (?m' \<chi>) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) q))"
      unfolding M_fin\<^sub>C_af_lhs_def Let_def And_prop_entailment_abs set_map Ball_def keys.abs_eq lookup.abs_eq 
      using assms(2) by (simp add: image_def inter_set_filter[symmetric] G_eq_G_list[symmetric]; blast)
  }
  thus ?thesis
    by (simp add: ltl_prop_implies_def ltl_prop_implies_abs_def ltl_prop_entails_abs_def)
qed 

definition 
  "ltl_to_generalized_rabin\<^sub>C_af \<equiv> ltl_to_rabin_base_code_def.ltl_to_generalized_rabin\<^sub>C \<up>af \<up>af\<^sub>G Abs Abs M_fin\<^sub>C_af"

theorem ltl_to_generalized_rabin\<^sub>C_af_correct:
  assumes "range w \<subseteq> set \<Sigma>"
  shows "w \<Turnstile> \<phi> \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltl_to_generalized_rabin\<^sub>C_af \<Sigma> \<phi>) w" 
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have X: "ltl_to_rabin_base_code \<up>af \<up>af\<^sub>G Abs Abs M_fin (set \<Sigma>) w M_fin\<^sub>C_af"
    using ltl_to_generalized_rabin_af_wellformed[OF finite_set assms] M_fin\<^sub>C_af_correct assms
    unfolding ltl_to_rabin_af_def ltl_to_rabin_base_code_def ltl_to_rabin_base_code_axioms_def by blast
  have "?lhs \<longleftrightarrow> accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin_af (set \<Sigma>) \<phi>) w"
    using assms ltl_to_generalized_rabin_af_correct by auto
  also 
  have "\<dots> \<longleftrightarrow> ?rhs"
    using ltl_to_rabin_base_code.ltl_to_generalized_rabin\<^sub>C_correct[OF X]
    unfolding ltl_to_generalized_rabin\<^sub>C_af_def by simp
  finally
  show ?thesis .
qed

subsection \<open>Generalized Deterministic Rabin Automaton (eager af)\<close>

definition M_fin\<^sub>C_af\<^sub>\<UU>_lhs :: "'a ltl \<Rightarrow> ('a ltl, nat) mapping \<Rightarrow> ('a ltl, ('a ltl\<^sub>P list)) mapping \<Rightarrow> 'a set \<Rightarrow> 'a ltl\<^sub>P"
where
  "M_fin\<^sub>C_af\<^sub>\<UU>_lhs \<phi> \<pi> m' \<nu> \<equiv> 
    let
      \<G> = Mapping.keys \<pi>;
      \<G>\<^sub>L = filter (\<lambda>x. x \<in> \<G>) (G_list \<phi>);
      mk_conj = \<lambda>\<chi>. foldl and_abs (and_abs (Abs \<chi>) (\<up>eval\<^sub>G \<G> (Abs (theG \<chi>)))) (map (\<up>eval\<^sub>G \<G> o (\<lambda>q. \<up>step q \<nu>)) (drop (the (Mapping.lookup \<pi> \<chi>)) (the (Mapping.lookup m' \<chi>))))
    in 
      \<up>And (map mk_conj \<G>\<^sub>L)"

fun M_fin\<^sub>C_af\<^sub>\<UU> :: "'a ltl \<Rightarrow> ('a ltl, nat) mapping \<Rightarrow> ('a ltl\<^sub>P \<times> (('a ltl, ('a ltl\<^sub>P list)) mapping), 'a set) transition \<Rightarrow> bool"
where
  "M_fin\<^sub>C_af\<^sub>\<UU> \<phi> \<pi> ((\<phi>', m'), \<nu>, _) = Not ((M_fin\<^sub>C_af\<^sub>\<UU>_lhs \<phi> \<pi> m' \<nu>) \<up>\<longrightarrow>\<^sub>P (\<up>step \<phi>' \<nu>))"

lemma M_fin\<^sub>C_af\<^sub>\<UU>_correct:
  assumes "t \<in> reach\<^sub>t \<Sigma> (ltl_to_rabin_base_code_def.delta\<^sub>C \<up>af\<^sub>\<UU> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<circ> Unf\<^sub>G) \<Sigma>) (ltl_to_rabin_base_code_def.initial\<^sub>C (Abs \<circ> Unf) (Abs \<circ> Unf\<^sub>G) \<phi>)"
  assumes "dom \<pi> \<subseteq> \<^bold>G \<phi>"
  shows "abstract_transition t \<in> M\<^sub>\<UU>_fin \<pi> = M_fin\<^sub>C_af\<^sub>\<UU> \<phi> (Mapping.Mapping \<pi>) t"
proof -
  let ?delta = "ltl_to_rabin_base_code_def.delta\<^sub>C \<up>af\<^sub>\<UU> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<circ> Unf\<^sub>G) \<Sigma>"
  let ?initial = "ltl_to_rabin_base_code_def.initial\<^sub>C (Abs \<circ> Unf) (Abs \<circ> Unf\<^sub>G) \<phi>"
  
  obtain x y \<nu> z z' where t_def [simp]: "t = ((x, y), \<nu>, (z, z'))"
    by (metis prod.collapse)
  have "(x, y) \<in> reach \<Sigma> ?delta ?initial"
    using assms(1) by (simp add: reach\<^sub>t_def reach_def; blast)
  hence N1: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> Mapping.lookup y \<chi> \<noteq> None"
    and D1: "\<And>\<chi>. \<chi> \<in> dom \<pi> \<Longrightarrow> distinct (the (Mapping.lookup y \<chi>))"
    using assms(2) by (blast dest: ltl_to_rabin_base_code_def.reach_delta_initial)+

  {
    fix S
    let ?m' = "\<lambda>\<chi>. map_option rk (Mapping.lookup y \<chi>)"
    
    {
      fix \<chi>
      assume "\<chi> \<in> dom \<pi>"
      hence "S \<up>\<Turnstile>\<^sub>P (foldl and_abs (and_abs (Abs \<chi>) (\<up>eval\<^sub>G (dom \<pi>) (Abs (theG \<chi>)))) (map (\<up>eval\<^sub>G (dom \<pi>) o (\<lambda>q. \<up>step q \<nu>)) (drop (the (\<pi> \<chi>)) (the (Mapping.lookup y \<chi>)))))
         \<longleftrightarrow> S \<up>\<Turnstile>\<^sub>P Abs \<chi> \<and> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) (Abs (theG \<chi>)) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (?m' \<chi>) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) (\<up>step q \<nu>))"
        using D1[THEN drop_rk, of _ "the (\<pi> \<chi>)"] N1[THEN option.map_sel, of _ rk]
        by (auto simp add: foldl_LTLAnd_prop_entailment_abs and_abs_conjunction simp del: rk.simps)
    }

    hence "S \<up>\<Turnstile>\<^sub>P (M_fin\<^sub>C_af\<^sub>\<UU>_lhs \<phi> (Mapping.Mapping \<pi>) y \<nu>)
      \<longleftrightarrow> ((\<forall>\<chi> \<in> dom \<pi>. (S \<up>\<Turnstile>\<^sub>P Abs \<chi> \<and> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) (Abs (theG \<chi>)) \<and> (\<forall>q. (\<exists>j \<ge> the (\<pi> \<chi>). the (?m' \<chi>) q = Some j) \<longrightarrow> S \<up>\<Turnstile>\<^sub>P \<up>eval\<^sub>G (dom \<pi>) (\<up>step q \<nu>)))))"
      unfolding M_fin\<^sub>C_af\<^sub>\<UU>_lhs_def Let_def And_prop_entailment_abs set_map Ball_def keys.abs_eq lookup.abs_eq 
      using assms(2) by (simp add: image_def inter_set_filter[symmetric] G_eq_G_list[symmetric]; blast)
  }
  thus ?thesis
    by (simp add: ltl_prop_implies_def ltl_prop_implies_abs_def ltl_prop_entails_abs_def)
qed 

definition 
  "ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU> \<equiv> ltl_to_rabin_base_code_def.ltl_to_generalized_rabin\<^sub>C \<up>af\<^sub>\<UU> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<circ> Unf) (Abs \<circ> Unf\<^sub>G) M_fin\<^sub>C_af\<^sub>\<UU>"

theorem ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU>_correct:
  assumes "range w \<subseteq> set \<Sigma>"
  shows "w \<Turnstile> \<phi> \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU> \<Sigma> \<phi>) w" 
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have X: "ltl_to_rabin_base_code \<up>af\<^sub>\<UU> \<up>af\<^sub>G\<^sub>\<UU> (Abs \<circ> Unf) (Abs \<circ> Unf\<^sub>G) M\<^sub>\<UU>_fin (set \<Sigma>) w M_fin\<^sub>C_af\<^sub>\<UU>"
    using ltl_to_generalized_rabin_af\<^sub>\<UU>_wellformed[OF finite_set assms] M_fin\<^sub>C_af\<^sub>\<UU>_correct assms
    unfolding ltl_to_rabin_af_unf_def ltl_to_rabin_base_code_def ltl_to_rabin_base_code_axioms_def by blast
  have "?lhs \<longleftrightarrow> accept\<^sub>G\<^sub>R (ltl_to_generalized_rabin_af\<^sub>\<UU> (set \<Sigma>) \<phi>) w"
    using assms ltl_to_generalized_rabin_af\<^sub>\<UU>_correct by auto
  also 
  have "\<dots> \<longleftrightarrow> ?rhs"
    using ltl_to_rabin_base_code.ltl_to_generalized_rabin\<^sub>C_correct[OF X]
    unfolding ltl_to_generalized_rabin\<^sub>C_af\<^sub>\<UU>_def by simp
  finally
  show ?thesis .
qed

end
