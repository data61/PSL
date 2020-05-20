(*
    Authors:    Ralph Bottesch
                Jose Divasón
                Maximilian Haslbeck
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Gram-Schmidt\<close>

theory Gram_Schmidt_2
  imports 
    Jordan_Normal_Form.Gram_Schmidt
    Jordan_Normal_Form.Show_Matrix
    Jordan_Normal_Form.Matrix_Impl
    Norms
    Int_Rat_Operations
begin
(* TODO: Documentation and add references to computer algebra book *)

no_notation Group.m_inv  ("inv\<index> _" [81] 80)

(* TODO: Is a function like this already in the library
   find_index is used to rewrite the sumlists in the lattice_of definition to finsums *)

fun find_index :: "'b list \<Rightarrow> 'b \<Rightarrow> nat" where
  "find_index [] _ = 0" |
  "find_index (x#xs) y = (if x = y then 0 else find_index xs y + 1)"

lemma find_index_not_in_set: "x \<notin> set xs \<longleftrightarrow> find_index xs x = length xs"
  by (induction xs) auto

lemma find_index_in_set: "x \<in> set xs \<Longrightarrow> xs ! (find_index xs x) = x"
  by (induction xs) auto

lemma find_index_inj: "inj_on (find_index xs) (set xs)"
  by (induction xs) (auto simp add: inj_on_def)

lemma find_index_leq_length: "find_index xs x < length xs \<longleftrightarrow> x \<in> set xs"
  by (induction xs) (auto)


(* TODO: move *)

lemma rev_unsimp: "rev xs @ (r # rs) = rev (r#xs) @ rs" by(induct xs,auto)


(* TODO: unify *)

lemma corthogonal_is_orthogonal[simp]: 
  "corthogonal (xs :: 'a :: trivial_conjugatable_ordered_field vec list) = orthogonal xs"
  unfolding corthogonal_def orthogonal_def by simp


(* TODO: move *)

context vec_module begin

definition lattice_of :: "'a vec list \<Rightarrow> 'a vec set" where
  "lattice_of fs = range (\<lambda> c. sumlist (map (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs]))"

lemma lattice_of_finsum:
  assumes "set fs \<subseteq> carrier_vec n"
  shows "lattice_of fs = range (\<lambda> c. finsum V (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) {0 ..< length fs})"
proof -
  have "sumlist (map (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs])
        = finsum V (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) {0 ..< length fs}" for c
    using  assms by (subst sumlist_map_as_finsum) (fastforce)+
  then show ?thesis
    unfolding lattice_of_def by auto
qed

lemma in_latticeE: assumes "f \<in> lattice_of fs" obtains c where
    "f = sumlist (map (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs])" 
  using assms unfolding lattice_of_def by auto
    
lemma in_latticeI: assumes "f = sumlist (map (\<lambda> i. of_int (c i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs])" 
  shows "f \<in> lattice_of fs" 
  using assms unfolding lattice_of_def by auto

lemma finsum_over_indexes_to_vectors:
  assumes "set vs \<subseteq> carrier_vec n" "l = length vs"
  shows "\<exists>c. (\<Oplus>\<^bsub>V\<^esub>x\<in>{0..<l}. of_int (g x) \<cdot>\<^sub>v vs ! x) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (c v) \<cdot>\<^sub>v v)"
  using assms proof (induction l arbitrary: vs)
  case (Suc l)
  then obtain vs' v where vs'_def: "vs = vs' @ [v]"
    by (metis Zero_not_Suc length_0_conv rev_exhaust)
  have c: "\<exists>c. (\<Oplus>\<^bsub>V\<^esub>i\<in>{0..<l}. of_int (g i) \<cdot>\<^sub>v vs' ! i) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c v) \<cdot>\<^sub>v v)"
    using Suc vs'_def by (auto)
  then obtain c 
    where c_def: "(\<Oplus>\<^bsub>V\<^esub>x\<in>{0..<l}. of_int (g x) \<cdot>\<^sub>v vs' ! x) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c v) \<cdot>\<^sub>v v)"
    by blast
  have "(\<Oplus>\<^bsub>V\<^esub>x\<in>{0..<Suc l}. of_int (g x) \<cdot>\<^sub>v vs ! x) 
        = of_int (g l) \<cdot>\<^sub>v vs ! l + (\<Oplus>\<^bsub>V\<^esub>x\<in>{0..<l}. of_int (g x) \<cdot>\<^sub>v vs ! x)"
     using Suc by (subst finsum_insert[symmetric]) (fastforce intro!: finsum_cong')+
  also have "vs = vs' @ [v]"
    using vs'_def by simp
  also have "(\<Oplus>\<^bsub>V\<^esub>x\<in>{0..<l}. of_int (g x) \<cdot>\<^sub>v (vs' @ [v]) ! x) = (\<Oplus>\<^bsub>V\<^esub>x\<in>{0..<l}. of_int (g x) \<cdot>\<^sub>v vs' ! x)"
    using Suc vs'_def by (intro finsum_cong') (auto simp add: in_mono append_Cons_nth_left)
  also note c_def
  also have "(vs' @ [v]) ! l = v"
    using Suc vs'_def by auto
  also have "\<exists>d'. of_int (g l) \<cdot>\<^sub>v v + (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c v) \<cdot>\<^sub>v v) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (d' v) \<cdot>\<^sub>v v)"
  proof (cases "v \<in> set vs'")
    case True
    then have I: "set vs' = insert v (set vs' - {v})"
      by blast
    define c' where "c' x = (if x = v then c x + g l else c x)" for x
    have "of_int (g l) \<cdot>\<^sub>v v + (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c v) \<cdot>\<^sub>v v)
          = of_int (g l) \<cdot>\<^sub>v v + (of_int (c v) \<cdot>\<^sub>v v + (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs' - {v}. of_int (c v) \<cdot>\<^sub>v v))"
      using Suc vs'_def by (subst I, subst finsum_insert) fastforce+
    also have "\<dots> = of_int (g l) \<cdot>\<^sub>v v + of_int (c v) \<cdot>\<^sub>v v + (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs' - {v}. of_int (c v) \<cdot>\<^sub>v v)"
      using Suc vs'_def by (subst a_assoc) (auto intro!: finsum_closed)
    also have "of_int (g l) \<cdot>\<^sub>v v + of_int (c v) \<cdot>\<^sub>v v = of_int (c' v)  \<cdot>\<^sub>v v"
      unfolding c'_def by (auto simp add: add_smult_distrib_vec)
    also have "(\<Oplus>\<^bsub>V\<^esub>v\<in>set vs' - {v}. of_int (c v) \<cdot>\<^sub>v v) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs' - {v}. of_int (c' v) \<cdot>\<^sub>v v)"
      using Suc vs'_def unfolding c'_def by (intro finsum_cong') (auto)
    also have "of_int (c' v) \<cdot>\<^sub>v v + (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs' - {v}. of_int (c' v) \<cdot>\<^sub>v v)
               = (\<Oplus>\<^bsub>V\<^esub>v\<in>insert v (set vs'). of_int (c' v) \<cdot>\<^sub>v v)"
      using Suc vs'_def by (subst finsum_insert[symmetric]) (auto)
    finally show ?thesis
      using vs'_def by force
  next
    case False
    define c' where "c' x = (if x = v then g l else c x)" for x
    have "of_int (g l) \<cdot>\<^sub>v v + (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c v) \<cdot>\<^sub>v v)
          = of_int (c' v) \<cdot>\<^sub>v v + (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c v) \<cdot>\<^sub>v v)"
      unfolding c'_def by simp
    also have "(\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c v) \<cdot>\<^sub>v v) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c' v) \<cdot>\<^sub>v v)"
      unfolding c'_def using Suc False vs'_def by (auto intro!: finsum_cong')
    also have "of_int (c' v) \<cdot>\<^sub>v v + (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c' v) \<cdot>\<^sub>v v)
               = (\<Oplus>\<^bsub>V\<^esub>v\<in>insert v (set vs'). of_int (c' v) \<cdot>\<^sub>v v)"
      using False Suc vs'_def by (subst finsum_insert[symmetric]) (auto)
    also have "(\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c' v) \<cdot>\<^sub>v v) = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs'. of_int (c v) \<cdot>\<^sub>v v)"
      unfolding c'_def using False Suc vs'_def by (auto intro!: finsum_cong')
    finally show ?thesis
      using vs'_def by auto
  qed
  finally show ?case
    unfolding vs'_def by blast
qed (auto)

lemma lattice_of_altdef:
  assumes "set vs \<subseteq> carrier_vec n"
  shows "lattice_of vs = range (\<lambda>c. \<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (c v) \<cdot>\<^sub>v v)"
proof -
  have "v \<in> lattice_of vs" if "v \<in> range (\<lambda>c. \<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (c v) \<cdot>\<^sub>v v)" for v
  proof -
    obtain c where v: "v = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (c v) \<cdot>\<^sub>v v)"
      using \<open>v \<in> range (\<lambda>c. \<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (c v) \<cdot>\<^sub>v v)\<close> by (auto)
    define c' where "c' i = (if find_index vs (vs ! i) = i then c (vs ! i) else 0)" for i
    have "v = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (c' (find_index vs v)) \<cdot>\<^sub>v vs ! (find_index vs v))"
      unfolding v
      using assms by (auto intro!: finsum_cong' simp add: c'_def find_index_in_set in_mono)
    also have "\<dots> = (\<Oplus>\<^bsub>V\<^esub>i\<in>find_index vs ` (set vs). of_int (c' i) \<cdot>\<^sub>v vs ! i)"
      using assms find_index_in_set find_index_inj by (subst finsum_reindex) fastforce+
    also have "\<dots> = (\<Oplus>\<^bsub>V\<^esub>i\<in>set [0..<length vs]. of_int (c' i) \<cdot>\<^sub>v vs ! i)"
    proof -
      have "i \<in> find_index vs ` set vs" if "i < length vs" "find_index vs (vs ! i) = i" for i
        using that by (metis imageI nth_mem)
      then show ?thesis
        unfolding c'_def using find_index_leq_length assms 
        by (intro add.finprod_mono_neutral_cong_left) (auto simp add: in_mono find_index_leq_length)
    qed
    also have "\<dots> = sumlist (map (\<lambda>i. of_int (c' i) \<cdot>\<^sub>v vs ! i) [0..<length vs])"
      using assms by (subst sumlist_map_as_finsum) (fastforce)+
    finally show ?thesis
      unfolding lattice_of_def by blast
  qed
  moreover have "v \<in> range (\<lambda>c. \<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (c v) \<cdot>\<^sub>v v)" if "v \<in> lattice_of vs" for v
  proof -
    obtain c where "v = sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v vs ! i) [0..<length vs])"
      using \<open>v \<in> lattice_of vs\<close> unfolding lattice_of_def by (auto)
    also have "\<dots> = (\<Oplus>\<^bsub>V\<^esub>x\<in>{0..<length vs}. of_int (c x) \<cdot>\<^sub>v vs ! x)"
      using that assms by (subst sumlist_map_as_finsum) fastforce+
    also obtain d where  "\<dots> = (\<Oplus>\<^bsub>V\<^esub>v\<in>set vs. of_int (d v) \<cdot>\<^sub>v v)"
      using finsum_over_indexes_to_vectors assms by blast
    finally show ?thesis
      by blast
  qed
  ultimately show ?thesis
    by fastforce
qed

lemma basis_in_latticeI:
  assumes fs: "set fs \<subseteq> carrier_vec n" and "f \<in> set fs" 
  shows "f \<in> lattice_of fs"
proof -
  define c :: "'a vec \<Rightarrow> int" where "c v = (if v = f then 1 else 0)" for v
  have "f = (\<Oplus>\<^bsub>V\<^esub>v\<in>{f}. of_int (c v) \<cdot>\<^sub>v v)"
    using assms by (auto simp add: c_def)
  also have "\<dots> = (\<Oplus>\<^bsub>V\<^esub>v\<in>set fs. of_int (c v) \<cdot>\<^sub>v v)"
    using assms by (intro add.finprod_mono_neutral_cong_left) (auto simp add: c_def)
  finally show ?thesis
    using assms lattice_of_altdef by blast
qed

lemma lattice_of_eq_set:
  assumes "set fs = set gs" "set fs \<subseteq> carrier_vec n"
  shows "lattice_of fs = lattice_of gs"
  using assms lattice_of_altdef by simp

lemma lattice_of_swap: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and ij: "i < length fs" "j < length fs" "i \<noteq> j" 
  and gs: "gs = fs[ i := fs ! j, j := fs ! i]" 
shows "lattice_of gs = lattice_of fs"
  using assms mset_swap by (intro lattice_of_eq_set) auto

lemma lattice_of_add: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and ij: "i < length fs" "j < length fs" "i \<noteq> j" 
  and gs: "gs = fs[ i := fs ! i + of_int l \<cdot>\<^sub>v fs ! j]" 
shows "lattice_of gs = lattice_of fs"
proof -
  {
    fix i j l and fs :: "'a vec list" 
    assume *: "i < j" "j < length fs" and fs: "set fs \<subseteq> carrier_vec n"
    note * = ij(1) *
    let ?gs = "fs[ i := fs ! i + of_int l \<cdot>\<^sub>v fs ! j]"
    let ?len = "[0..<i] @ [i] @ [Suc i..<j] @ [j] @ [Suc j..<length fs]" 
    have "[0 ..< length fs] = [0 ..< j] @ [j] @ [Suc j ..< length fs]" using *
      by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append 
          upt_conv_Cons zero_less_Suc)
    also have "[0 ..< j] = [0 ..< i] @ [i] @ [Suc i ..< j]" using *
      by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append 
          upt_conv_Cons zero_less_Suc)
    finally have len: "[0..<length fs] = ?len" by simp
    from fs have fs: "\<And> i. i < length fs \<Longrightarrow> fs ! i \<in> carrier_vec n" unfolding set_conv_nth by auto
    from fs have fsd: "\<And> i. i < length fs \<Longrightarrow> dim_vec (fs ! i) = n" by auto
    from fsd[of i] fsd[of j] * have fsd: "dim_vec (fs ! i) = n" "dim_vec (fs ! j) = n" by auto
    {
      fix f
      assume "f \<in> lattice_of fs" 
      from in_latticeE[OF this, unfolded len] obtain c where
        f: "f = sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v fs ! i) ?len)" by auto
      define sc where "sc = (\<lambda> xs. sumlist (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v fs ! i) xs))"
      define d where "d = (\<lambda> k. if k = j then c j - c i * l else c k)"
      define sd where "sd = (\<lambda> xs. sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) xs))"
      have isc: "set is \<subseteq> {0 ..< length fs} \<Longrightarrow> sc is \<in> carrier_vec n" for "is" 
        unfolding sc_def by (intro sumlist_carrier, auto simp: fs)
      have isd: "set is \<subseteq> {0 ..< length fs} \<Longrightarrow> sd is \<in> carrier_vec n" for "is" 
        unfolding sd_def using * by (intro sumlist_carrier, auto, rename_tac k,
        case_tac "k = i", auto simp: fs)
      let ?a = "sc [0..<i]" let ?b = "sc [i]" let ?c = "sc [Suc i ..< j]" let ?d = "sc [j]" 
      let ?e = "sc [Suc j ..< length fs]" 
      let ?A = "sd [0..<i]" let ?B = "sd [i]" let ?C = "sd [Suc i ..< j]" let ?D = "sd [j]" 
      let ?E = "sd [Suc j ..< length fs]" 
      let ?CC = "carrier_vec n" 
      have ae: "?a \<in> ?CC" "?b \<in> ?CC" "?c \<in> ?CC" "?d \<in> ?CC" "?e \<in> ?CC"  
        using * by (auto intro: isc)
      have AE: "?A \<in> ?CC" "?B \<in> ?CC" "?C \<in> ?CC" "?D \<in> ?CC" "?E \<in> ?CC"  
        using * by (auto intro: isd)
      have sc_sd: "{i,j} \<inter> set is \<subseteq> {} \<Longrightarrow> sc is = sd is" for "is" 
        unfolding sc_def sd_def by (rule arg_cong[of _ _ sumlist], rule map_cong, auto simp: d_def,
        rename_tac k, case_tac "i = k", auto)
      have "f = ?a + (?b + (?c + (?d + ?e)))"         
        unfolding f map_append sc_def using fs *
        by ((subst sumlist_append, force, force)+, simp)
      also have "\<dots> = ?a + ((?b + ?d) + (?c + ?e))" using ae by auto          
      also have "\<dots> = ?A + ((?b + ?d) + (?C + ?E))" 
        using * by (auto simp: sc_sd)
      also have "?b + ?d = ?B + ?D" unfolding sd_def sc_def d_def sumlist_def
        by (rule eq_vecI, insert * fsd, auto simp: algebra_simps)
      finally have "f = ?A + (?B + (?C + (?D + ?E)))" using AE by auto
      also have "\<dots> = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) ?len)" 
        unfolding f map_append sd_def using fs *
        by ((subst sumlist_append, force, force)+, simp)
      also have "\<dots> = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) [0 ..< length ?gs])"
        unfolding len[symmetric] by simp
      finally have "f = sumlist (map (\<lambda>i. of_int (d i) \<cdot>\<^sub>v ?gs ! i) [0 ..< length ?gs])" .
      from in_latticeI[OF this] have "f \<in> lattice_of ?gs" .
    }
    hence "lattice_of fs \<subseteq> lattice_of ?gs" by blast
  } note main = this 
  {
    fix i j and fs :: "'a vec list" 
    assume *: "i < j" "j < length fs" and fs: "set fs \<subseteq> carrier_vec n"
    let ?gs = "fs[ i := fs ! i + of_int l \<cdot>\<^sub>v fs ! j]"
    define gs where "gs = ?gs" 
    from main[OF * fs, of l, folded gs_def]
    have one: "lattice_of fs \<subseteq> lattice_of gs" .
    have *: "i < j" "j < length gs" "set gs \<subseteq> carrier_vec n" using * fs unfolding gs_def set_conv_nth
      by (auto, rename_tac k, case_tac "k = i", (force intro!: add_carrier_vec)+)
    from fs have fs: "\<And> i. i < length fs \<Longrightarrow> fs ! i \<in> carrier_vec n" unfolding set_conv_nth by auto
    from fs have fsd: "\<And> i. i < length fs \<Longrightarrow> dim_vec (fs ! i) = n" by auto
    from fsd[of i] fsd[of j] * have fsd: "dim_vec (fs ! i) = n" "dim_vec (fs ! j) = n" by (auto simp: gs_def)
    from main[OF *, of "-l"]
    have "lattice_of gs \<subseteq> lattice_of (gs[i := gs ! i + of_int (- l) \<cdot>\<^sub>v gs ! j])" .
    also have "gs[i := gs ! i + of_int (- l) \<cdot>\<^sub>v gs ! j] = fs" unfolding gs_def
      by (rule nth_equalityI, auto, insert * fsd, rename_tac k, case_tac "k = i", auto)
    ultimately have "lattice_of fs = lattice_of ?gs" using one unfolding gs_def by auto
  } note main = this
  show ?thesis
  proof (cases "i < j")
    case True
    from main[OF this ij(2) fs] show ?thesis unfolding gs by simp
  next
    case False
    with ij have ji: "j < i" by auto
    define hs where "hs = fs[i := fs ! j, j := fs ! i]" 
    define ks where "ks = hs[j := hs ! j + of_int l \<cdot>\<^sub>v hs ! i]" 
    from ij fs have ij': "i < length hs" "set hs \<subseteq> carrier_vec n" unfolding hs_def by auto
    hence ij'': "set ks \<subseteq> carrier_vec n" "i < length ks" "j < length ks" "i \<noteq> j" 
      using ji unfolding ks_def set_conv_nth by (auto, rename_tac k, case_tac "k = i", 
        force, case_tac "k = j", (force intro!: add_carrier_vec)+)
    from lattice_of_swap[OF fs ij refl] 
    have "lattice_of fs = lattice_of hs" unfolding hs_def by auto
    also have "\<dots> = lattice_of ks" 
      using main[OF ji ij'] unfolding ks_def .
    also have "\<dots> = lattice_of (ks[i := ks ! j, j := ks ! i])" 
      by (rule sym, rule lattice_of_swap[OF ij'' refl])
    also have "ks[i := ks ! j, j := ks ! i] = gs" unfolding gs ks_def hs_def
      by (rule nth_equalityI, insert ij, auto, 
       rename_tac k, case_tac "k = i", force, case_tac "k = j", auto)
    finally show ?thesis by simp
  qed
qed

definition "orthogonal_complement W = {x. x \<in> carrier_vec n \<and> (\<forall>y \<in> W. x \<bullet> y = 0)}"

lemma orthogonal_complement_subset:
  assumes "A \<subseteq> B"
  shows "orthogonal_complement B \<subseteq> orthogonal_complement A"
unfolding orthogonal_complement_def using assms by auto

end

context vec_space
begin


lemma in_orthogonal_complement_span[simp]:
  assumes [intro]:"S \<subseteq> carrier_vec n"
  shows "orthogonal_complement (span S) = orthogonal_complement S"
proof
  show "orthogonal_complement (span S) \<subseteq> orthogonal_complement S"
    by(fact orthogonal_complement_subset[OF in_own_span[OF assms]])
  {fix x :: "'a vec"
    fix a fix A :: "'a vec set"
    assume x [intro]:"x \<in> carrier_vec n" and f: "finite A" and S:"A \<subseteq> S"
    assume i0:"\<forall>y\<in>S. x \<bullet> y = 0"
    have "x \<bullet> lincomb a A = 0"
      unfolding comm_scalar_prod[OF x lincomb_closed[OF subset_trans[OF S assms]]]
    proof(insert S,atomize(full),rule finite_induct[OF f],goal_cases)
      case 1 thus ?case using assms x by force
    next
      case (2 f F)
      { assume i:"insert f F \<subseteq> S"
        hence F:"F \<subseteq> S" and f: "f \<in> S" by auto
        from F f assms
        have [intro]:"F \<subseteq> carrier_vec n"
          and fc[intro]:"f \<in> carrier_vec n"
          and [intro]:"x \<in> F \<Longrightarrow> x \<in> carrier_vec n" for x by auto
        have laf:"lincomb a F \<bullet> x = 0" using F 2 by auto
        have [simp]:"(\<Sum>u\<in>F. (a u \<cdot>\<^sub>v u) \<bullet> x) = 0"
          by(insert laf[unfolded lincomb_def],atomize(full),subst finsum_scalar_prod_sum) auto
        from f i0 have [simp]:"f \<bullet> x = 0" by (subst comm_scalar_prod) auto
        from lincomb_closed[OF subset_trans[OF i assms]]
        have "lincomb a (insert f F) \<bullet> x = 0" unfolding lincomb_def
          apply(subst finsum_scalar_prod_sum,force,force)
          using 2(1,2) smult_scalar_prod_distrib[OF fc x] by auto
      } thus ?case by auto
      qed
  }
  thus "orthogonal_complement S \<subseteq> orthogonal_complement (span S)"
    unfolding orthogonal_complement_def span_def by auto
qed

end

context cof_vec_space
begin

definition lin_indpt_list :: "'a vec list \<Rightarrow> bool" where
  "lin_indpt_list fs = (set fs \<subseteq> carrier_vec n \<and> distinct fs \<and> lin_indpt (set fs))" 

definition basis_list :: "'a vec list \<Rightarrow> bool" where
  "basis_list fs = (set fs \<subseteq> carrier_vec n \<and> length fs = n \<and> carrier_vec n \<subseteq> span (set fs))"

lemma upper_triangular_imp_lin_indpt_list:
  assumes A: "A \<in> carrier_mat n n"
    and tri: "upper_triangular A"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "lin_indpt_list (rows A)"
  using upper_triangular_imp_distinct[OF assms]
  using upper_triangular_imp_lin_indpt_rows[OF assms] A
  unfolding lin_indpt_list_def by (auto simp: rows_def)

lemma basis_list_basis: assumes "basis_list fs" 
  shows "distinct fs" "lin_indpt (set fs)" "basis (set fs)" 
proof -
  from assms[unfolded basis_list_def] 
  have len: "length fs = n" and C: "set fs \<subseteq> carrier_vec n" 
    and span: "carrier_vec n \<subseteq> span (set fs)" by auto
  show b: "basis (set fs)" 
  proof (rule dim_gen_is_basis[OF finite_set C])
    show "card (set fs) \<le> dim" unfolding dim_is_n unfolding len[symmetric] by (rule card_length)
    show "span (set fs) = carrier_vec n" using span C by auto
  qed
  thus "lin_indpt (set fs)" unfolding basis_def by auto  
  show "distinct fs" 
  proof (rule ccontr)
    assume "\<not> distinct fs" 
    hence "card (set fs) < length fs" using antisym_conv1 card_distinct card_length by auto
    also have "\<dots> = dim" unfolding len dim_is_n ..
    finally have "card (set fs) < dim" by auto
    also have "\<dots> \<le> card (set fs)" using span finite_set[of fs] 
      using b basis_def gen_ge_dim by auto
    finally show False by simp
  qed
qed

lemma basis_list_imp_lin_indpt_list: assumes "basis_list fs" shows "lin_indpt_list fs" 
  using basis_list_basis[OF assms] assms unfolding lin_indpt_list_def basis_list_def by auto

lemma basis_det_nonzero:
  assumes db:"basis (set G)" and len:"length G = n"
  shows "det (mat_of_rows n G) \<noteq> 0"
proof -
  have M_car1:"mat_of_rows n G \<in> carrier_mat n n" using assms by auto
  hence M_car:"(mat_of_rows n G)\<^sup>T \<in> carrier_mat n n" by auto
  have li:"lin_indpt (set G)"
   and inc_2:"set G \<subseteq> carrier_vec n"
   and issp:"carrier_vec n = span (set G)"
   and RG_in_carr:"\<And>i. i < length G \<Longrightarrow> G ! i \<in> carrier_vec n"
    using assms[unfolded basis_def] by auto
  hence "basis_list G" unfolding basis_list_def using len by auto
  from basis_list_basis[OF this] have di:"distinct G" by auto
  have "det ((mat_of_rows n G)\<^sup>T) \<noteq> 0" unfolding det_0_iff_vec_prod_zero[OF M_car] 
  proof
    assume "\<exists>v. v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> (mat_of_rows n G)\<^sup>T *\<^sub>v v = 0\<^sub>v n"
    then obtain v where v:"v \<in> span (set G)"
                          "v \<noteq> 0\<^sub>v n" "(mat_of_rows n G)\<^sup>T *\<^sub>v v = 0\<^sub>v n"
      unfolding issp by blast
    from finite_in_span[OF finite_set inc_2 v(1)] obtain a
      where aA: "v = lincomb a (set G)" by blast
    from v(1,2)[folded issp] obtain i where i:"v $ i \<noteq> 0" "i < n" by fastforce
    hence inG:"G ! i \<in> set G" using len by auto
    have di2: "distinct [0..<length G]" by auto
    define f where "f = (\<lambda>l. \<Sum>i \<in> set [0..<length G]. if l = G ! i then v $ i else 0)"
    hence f':"f (G ! i) = (\<Sum>ia\<leftarrow>[0..<n]. if G ! ia = G ! i then v $ ia else 0)"
      unfolding f_def sum.distinct_set_conv_list[OF di2] unfolding len by metis
    from v have "mat_of_cols n G *\<^sub>v v = 0\<^sub>v n"
      unfolding transpose_mat_of_rows by auto
    with mat_of_cols_mult_as_finsum[OF v(1)[folded issp len] RG_in_carr]
    have f:"lincomb f (set G) = 0\<^sub>v n" unfolding len f_def by auto
    note [simp] = list_trisect[OF i(2)[folded len],unfolded len]
    note x = i(2)[folded len]
    have [simp]:"(\<Sum>x\<leftarrow>[0..<i]. if G ! x = G ! i then v $ x else 0) = 0"
      by (rule sum_list_0,auto simp: nth_eq_iff_index_eq[OF di less_trans[OF _ x] x])
    have [simp]:"(\<Sum>x\<leftarrow>[Suc i..<n]. if G ! x = G ! i then v $ x else 0) = 0"
      apply (rule sum_list_0) using nth_eq_iff_index_eq[OF di _ x] len by auto
    from i(1) have "f (G ! i) \<noteq> 0" unfolding f' by auto
  from lin_dep_crit[OF finite_set subset_refl TrueI inG this f]
    have "lin_dep (set G)".
    thus False using li by auto
  qed
  thus det0:"det (mat_of_rows n G) \<noteq> 0" by (unfold det_transpose[OF M_car1])
qed

lemma lin_indpt_list_add_vec: assumes  
      i: "j < length us" "i < length us" "i \<noteq> j" 
   and indep: "lin_indpt_list  us" 
shows "lin_indpt_list (us [i := us ! i + c \<cdot>\<^sub>v us ! j])" (is "lin_indpt_list ?V")
proof -
  from indep[unfolded lin_indpt_list_def] have us: "set us \<subseteq> carrier_vec n" 
    and dist: "distinct us" and indep: "lin_indpt (set us)" by auto
  let ?E = "set us - {us ! i}" 
  let ?us = "insert (us ! i) ?E"
  let ?v = "us ! i + c \<cdot>\<^sub>v us ! j"     
  from us i have usi: "us ! i \<in> carrier_vec n" "us ! i \<notin> ?E" "us ! i \<in> set us" 
    and usj: "us ! j \<in> carrier_vec n" by auto
  from usi usj have v: "?v \<in> carrier_vec n" by auto      
  have fin: "finite ?E" by auto
  have id: "set us = insert (us ! i) (set us - {us ! i})" using i(2) by auto
  from dist i have diff': "us ! i \<noteq> us ! j" unfolding distinct_conv_nth by auto
  from subset_li_is_li[OF indep] have indepE: "lin_indpt ?E" by auto
  have Vid: "set ?V = insert ?v ?E" using set_update_distinct[OF dist i(2)] by auto
  have E: "?E \<subseteq> carrier_vec n" using us by auto
  have V: "set ?V \<subseteq> carrier_vec n" using us v unfolding Vid by auto
  from dist i have diff: "us ! i \<noteq> us ! j" unfolding distinct_conv_nth by auto
  have vspan: "?v \<notin> span ?E"
  proof
    assume mem: "?v \<in> span ?E" 
    from diff i have "us ! j \<in> ?E" by auto
    hence "us ! j \<in> span ?E" using E by (metis span_mem)
    hence "- c \<cdot>\<^sub>v us ! j \<in> span ?E" using smult_in_span[OF E] by auto
    from span_add1[OF E mem this] have "?v + (- c \<cdot>\<^sub>v us ! j) \<in> span ?E" .
    also have "?v + (- c \<cdot>\<^sub>v us ! j) = us ! i" using usi usj by auto
    finally have mem: "us ! i \<in> span ?E" .
    from in_spanE[OF this] obtain a A where lc: "us ! i = lincomb a A" and A: "finite A" 
      "A \<subseteq> set us - {us ! i}" 
      by auto
    let ?a = "a (us ! i := -1)" let ?A = "insert (us ! i) A" 
    from A have fin: "finite ?A" by auto
    have lc: "lincomb ?a A = us ! i" unfolding lc
      by (rule lincomb_cong, insert A us lc, auto)
    have "lincomb ?a ?A = 0\<^sub>v n" 
      by (subst lincomb_insert2[OF A(1)], insert A us lc usi diff, auto)
    from not_lindepD[OF indep _ _ _ this] A usi 
    show False by auto
  qed
  hence vmem: "?v \<notin> ?E" using span_mem[OF E, of ?v] by auto
  from lin_dep_iff_in_span[OF E indepE v this] vspan 
  have indep1: "lin_indpt (set ?V)" unfolding Vid by auto
  from vmem dist have "distinct ?V" by (metis distinct_list_update)
  with indep1 V show ?thesis unfolding lin_indpt_list_def by auto
qed

lemma scalar_prod_lincomb_orthogonal: assumes ortho: "orthogonal gs" and gs: "set gs \<subseteq> carrier_vec n"
  shows "k \<le> length gs \<Longrightarrow> sumlist (map (\<lambda> i. g i \<cdot>\<^sub>v gs ! i) [0 ..< k]) \<bullet> sumlist (map (\<lambda> i. h i \<cdot>\<^sub>v gs ! i) [0 ..< k])
  = sum_list (map (\<lambda> i. g i * h i * (gs ! i \<bullet> gs ! i)) [0 ..< k])"
proof (induct k)
  case (Suc k)
  note ortho = orthogonalD[OF ortho]
  let ?m = "length gs" 
  from gs Suc(2) have gsi[simp]: "\<And> i. i \<le> k \<Longrightarrow> gs ! i \<in> carrier_vec n" by auto
  from Suc have kn: "k \<le> ?m" and k: "k < ?m" by auto
  let ?v1 = "sumlist (map (\<lambda>i. g i \<cdot>\<^sub>v gs ! i) [0..<k])" 
  let ?v2 = "(g k \<cdot>\<^sub>v gs ! k)" 
  let ?w1 = "sumlist (map (\<lambda>i. h i \<cdot>\<^sub>v gs ! i) [0..<k])" 
  let ?w2 = "(h k \<cdot>\<^sub>v gs ! k)" 
  from Suc have id: "[0 ..< Suc k] = [0 ..< k] @ [k]" by simp
  have id: "sumlist (map (\<lambda>i. g i \<cdot>\<^sub>v gs ! i) [0..<Suc k]) = ?v1 + ?v2"
     "sumlist (map (\<lambda>i. h i \<cdot>\<^sub>v gs ! i) [0..<Suc k]) = ?w1 + ?w2"
    unfolding id map_append
    by (subst sumlist_append, insert Suc(2), auto)+
  have v1: "?v1 \<in> carrier_vec n" by (rule sumlist_carrier, insert Suc(2), auto)
  have v2: "?v2 \<in> carrier_vec n" by (insert Suc(2), auto)
  have w1: "?w1 \<in> carrier_vec n" by (rule sumlist_carrier, insert Suc(2), auto)
  have w2: "?w2 \<in> carrier_vec n" by (insert Suc(2), auto)
  have gsk: "gs ! k \<in> carrier_vec n" by simp
  have v12: "?v1 + ?v2 \<in> carrier_vec n" using v1 v2 by auto
  have w12: "?w1 + ?w2 \<in> carrier_vec n" using w1 w2 by auto
  have 0: "\<And> g h. i < k \<Longrightarrow> (g \<cdot>\<^sub>v gs ! i) \<bullet> (h \<cdot>\<^sub>v gs ! k) = 0" for i
    by (subst scalar_prod_smult_distrib[OF _ gsk], (insert k, auto)[1],
    subst smult_scalar_prod_distrib[OF _ gsk], (insert k, auto)[1], insert ortho[of i k] k, auto)
  have 1: "?v1 \<bullet> ?w2 = 0" 
    by (subst scalar_prod_left_sum_distrib[OF _ w2], (insert Suc(2), auto)[1], rule sum_list_neutral, 
        insert 0, auto)   
  have 2: "?v2 \<bullet> ?w1 = 0" unfolding comm_scalar_prod[OF v2 w1]
    apply (subst scalar_prod_left_sum_distrib[OF _ v2])
     apply ((insert gs, force)[1])
    apply (rule sum_list_neutral)
    by (insert 0, auto)
  show ?case unfolding id
    unfolding scalar_prod_add_distrib[OF v12 w1 w2]
      add_scalar_prod_distrib[OF v1 v2 w1]
      add_scalar_prod_distrib[OF v1 v2 w2]
      scalar_prod_smult_distrib[OF w2 gsk]
      smult_scalar_prod_distrib[OF gsk gsk]
    unfolding Suc(1)[OF kn]
    by (simp add: 1 2 comm_scalar_prod[OF v2 w1])
qed auto
end


locale gram_schmidt = cof_vec_space n f_ty
  for n :: nat and f_ty :: "'a :: {trivial_conjugatable_linordered_field} itself"
begin

definition Gramian_matrix where
  "Gramian_matrix G k = (let M = mat k n (\<lambda> (i,j). (G ! i) $ j) in M * M\<^sup>T)"

lemma Gramian_matrix_alt_def: "k \<le> length G \<Longrightarrow> 
  Gramian_matrix G k = (let M = mat_of_rows n (take k G) in M * M\<^sup>T)"
  unfolding Gramian_matrix_def Let_def
  by (rule arg_cong[of _ _ "\<lambda> x. x * x\<^sup>T"], unfold mat_of_rows_def, intro eq_matI, auto)

definition Gramian_determinant where
  "Gramian_determinant G k = det (Gramian_matrix G k)"

lemma Gramian_determinant_0 [simp]: "Gramian_determinant G 0 = 1"
  unfolding Gramian_determinant_def Gramian_matrix_def Let_def
  by (simp add: times_mat_def)

lemma orthogonal_imp_lin_indpt_list: 
  assumes ortho: "orthogonal gs" and gs: "set gs \<subseteq> carrier_vec n"
  shows "lin_indpt_list gs" 
proof -
  from corthogonal_distinct[of gs] ortho have dist: "distinct gs" by simp
  show ?thesis unfolding lin_indpt_list_def
  proof (intro conjI gs dist finite_lin_indpt2 finite_set)
    fix lc
    assume 0: "lincomb lc (set gs) = 0\<^sub>v n" (is "?lc = _") 
    have lc: "?lc \<in> carrier_vec n" by (rule lincomb_closed[OF gs])
    let ?m = "length gs" 
    from 0 have "0 = ?lc \<bullet> ?lc" by simp
    also have "?lc = lincomb_list (\<lambda>i. lc (gs ! i)) gs" 
      unfolding lincomb_as_lincomb_list_distinct[OF gs dist] ..
    also have "\<dots> = sumlist (map (\<lambda>i. lc (gs ! i) \<cdot>\<^sub>v gs ! i) [0..< ?m])" 
      unfolding lincomb_list_def by auto 
    also have "\<dots> \<bullet> \<dots> = (\<Sum>i\<leftarrow>[0..<?m]. (lc (gs ! i) * lc (gs ! i)) * sq_norm (gs ! i))" (is "_ = sum_list ?sum")
      unfolding scalar_prod_lincomb_orthogonal[OF ortho gs le_refl]
      by (auto simp: sq_norm_vec_as_cscalar_prod power2_eq_square)
    finally have sum_0: "sum_list ?sum = 0" ..
    have nonneg: "\<And> x. x \<in> set ?sum \<Longrightarrow> x \<ge> 0" 
      using zero_le_square[of "lc (gs ! i)" for i] sq_norm_vec_ge_0[of "gs ! i" for i] by auto  
    {
      fix x
      assume x: "x \<in> set gs" 
      then obtain i where i: "i < ?m" and x: "x = gs ! i" unfolding set_conv_nth 
        by auto
      hence "lc x * lc x * sq_norm x \<in> set ?sum" by auto
      with sum_list_nonneg_eq_0_iff[of ?sum, OF nonneg] sum_0 
      have "lc x = 0 \<or> sq_norm x = 0" by auto
      with orthogonalD[OF ortho, OF i i, folded x]
      have "lc x = 0" by (auto simp: sq_norm_vec_as_cscalar_prod)
    }
    thus "\<forall>v\<in>set gs. lc v = 0" by auto
  qed
qed

lemma orthocompl_span:
  assumes "\<And> x. x \<in> S \<Longrightarrow> v \<bullet> x = 0" "S \<subseteq> carrier_vec n" and [intro]: "v \<in> carrier_vec n"
  and "y \<in> span S" 
  shows "v \<bullet> y = 0"
proof -
  {fix a A
   assume "y = lincomb a A" "finite A" "A \<subseteq> S"
   note assms = assms this
   hence [intro!]:"lincomb a A \<in> carrier_vec n" "(\<lambda>v. a v \<cdot>\<^sub>v v) \<in> A \<rightarrow> carrier_vec n" by auto
   have "\<forall>x\<in>A. (a x \<cdot>\<^sub>v x) \<bullet> v = 0" proof fix x assume "x \<in> A" note assms = assms this
     hence x:"x \<in> S" by auto
     with assms have [intro]:"x \<in> carrier_vec n" by auto
     from assms(1)[OF x] have "x \<bullet> v = 0" by(subst comm_scalar_prod) force+
     thus "(a x \<cdot>\<^sub>v x) \<bullet> v = 0"
       apply(subst smult_scalar_prod_distrib) by force+
   qed
   hence "v \<bullet> lincomb a A = 0" apply(subst comm_scalar_prod) apply force+ unfolding lincomb_def
     apply(subst finsum_scalar_prod_sum) by force+
  }
  thus ?thesis using \<open>y \<in> span S\<close> unfolding span_def by auto
qed

lemma orthogonal_sumlist:
  assumes ortho: "\<And> x. x \<in> set S \<Longrightarrow> v \<bullet> x = 0" and S: "set S \<subseteq> carrier_vec n" and v: "v \<in> carrier_vec n"
  shows "v \<bullet> sumlist S = 0"
  by (rule orthocompl_span[OF ortho S v sumlist_in_span[OF S span_mem[OF S]]])

lemma oc_projection_alt_def:
  assumes carr:"(W::'a vec set) \<subseteq> carrier_vec n" "x \<in> carrier_vec n"
      and alt1:"y1 \<in> W" "x - y1 \<in> orthogonal_complement W"
      and alt2:"y2 \<in> W" "x - y2 \<in> orthogonal_complement W"
  shows  "y1 = y2"
proof -
  have carr:"y1 \<in> carrier_vec n" "y2 \<in> carrier_vec n" "x \<in> carrier_vec n" "- y1 \<in> carrier_vec n" 
    "0\<^sub>v n \<in> carrier_vec n"
    using alt1 alt2 carr by auto
  hence "y1 - y2 \<in> carrier_vec n" by auto
  note carr = this carr
  from alt1 have "ya\<in>W \<Longrightarrow> (x - y1) \<bullet> ya = 0" for ya
    unfolding orthogonal_complement_def by blast
  hence "(x - y1) \<bullet> y2 = 0" "(x - y1) \<bullet> y1 = 0" using alt2 alt1 by auto
  hence eq1:"y1 \<bullet> y2 = x \<bullet> y2" "y1 \<bullet> y1 = x \<bullet> y1" using carr minus_scalar_prod_distrib by force+
  from this(1) have eq2:"y2 \<bullet> y1 = x \<bullet> y2" using carr comm_scalar_prod by force
  from alt2 have "ya\<in>W \<Longrightarrow> (x - y2) \<bullet> ya = 0" for ya
    unfolding orthogonal_complement_def by blast
  hence "(x - y2) \<bullet> y1 = 0" "(x - y2) \<bullet> y2 = 0" using alt2 alt1 by auto
  hence eq3:"y2 \<bullet> y2 = x \<bullet> y2" "y2 \<bullet> y1 = x \<bullet> y1" using carr minus_scalar_prod_distrib by force+
  with eq2 have eq4:"x \<bullet> y1 = x \<bullet> y2" by auto
  have "\<parallel>(y1 - y2)\<parallel>\<^sup>2 = 0" unfolding sq_norm_vec_as_cscalar_prod cscalar_prod_is_scalar_prod using carr
    apply(subst minus_scalar_prod_distrib) apply force+
    apply(subst (0 0) scalar_prod_minus_distrib) apply force+
    unfolding eq1 eq2 eq3 eq4 by auto
  with sq_norm_vec_eq_0[of "(y1 - y2)"] carr have "y1 - y2 = 0\<^sub>v n" by fastforce
  hence "y1 - y2 + y2 = y2" using carr by fastforce
  also have "y1 - y2 + y2 = y1" using carr by auto
  finally show "y1 = y2" .
qed

definition
  "is_oc_projection w S v = (w \<in> carrier_vec n \<and> v - w \<in> span S \<and> (\<forall> u. u \<in> S \<longrightarrow> w \<bullet> u = 0))"

lemma is_oc_projection_sq_norm: assumes "is_oc_projection w S v"
  and S: "S \<subseteq> carrier_vec n" 
  and v: "v \<in> carrier_vec n" 
shows "sq_norm w \<le> sq_norm v" 
proof -
  from assms[unfolded is_oc_projection_def]
  have w: "w \<in> carrier_vec n" 
    and vw: "v - w \<in> span S" and ortho: "\<And> u. u \<in> S \<Longrightarrow> w \<bullet> u = 0" by auto
  have "sq_norm v = sq_norm ((v - w) + w)" using v w 
    by (intro arg_cong[of _ _ sq_norm_vec], auto)
  also have "\<dots> = ((v - w) + w) \<bullet> ((v - w) + w)" unfolding sq_norm_vec_as_cscalar_prod
    by simp
  also have "\<dots> = (v - w) \<bullet> ((v - w) + w) + w \<bullet> ((v - w) + w)" 
    by (rule add_scalar_prod_distrib, insert v w, auto)
  also have "\<dots> = ((v - w) \<bullet> (v - w) + (v - w) \<bullet> w) + (w \<bullet> (v - w) + w \<bullet> w)" 
    by (subst (1 2) scalar_prod_add_distrib, insert v w, auto)
  also have "\<dots> = sq_norm (v - w) + 2 * (w \<bullet> (v - w)) + sq_norm w" 
    unfolding sq_norm_vec_as_cscalar_prod using v w by (auto simp: comm_scalar_prod[of w _ "v - w"])
  also have "\<dots> \<ge> 2 * (w \<bullet> (v - w)) + sq_norm w" using sq_norm_vec_ge_0[of "v - w"] by auto
  also have "w \<bullet> (v - w) = 0" using orthocompl_span[OF ortho S w vw] by auto
  finally show ?thesis by auto
qed

definition oc_projection where
"oc_projection S fi \<equiv> (SOME v. is_oc_projection v S fi)"

lemma inv_in_span:
  assumes incarr[intro]:"U \<subseteq> carrier_vec n" and insp:"a \<in> span U"
  shows "- a \<in> span U"
proof -
  from insp[THEN in_spanE] obtain aa A where a:"a = lincomb aa A" "finite A" "A \<subseteq> U" by auto
  with assms have [intro!]:"(\<lambda>v. aa v \<cdot>\<^sub>v v) \<in> A \<rightarrow> carrier_vec n" by auto
  from a(1) have e1:"- a = lincomb (\<lambda> x. - 1 * aa x) A" unfolding smult_smult_assoc[symmetric] lincomb_def
    by(subst finsum_smult[symmetric]) force+
  show ?thesis using e1 a span_def by blast
qed

lemma non_span_det_zero:
  assumes len: "length G = n"
  and nonb:"\<not> (carrier_vec n \<subseteq> span (set G))"
  and carr:"set G \<subseteq> carrier_vec n"
  shows "det (mat_of_rows n G) = 0" unfolding det_0_iff_vec_prod_zero
proof -
  let ?A = "(mat_of_rows n G)\<^sup>T" let ?B = "1\<^sub>m n"
  from carr have carr_mat:"?A \<in> carrier_mat n n" "?B \<in> carrier_mat n n" "mat_of_rows n G \<in> carrier_mat n n"
    using len mat_of_rows_carrier(1) by auto
  from carr have g_len:"\<And> i. i < length G \<Longrightarrow> G ! i \<in> carrier_vec n" by auto
  from nonb obtain v where v:"v \<in> carrier_vec n" "v \<notin> span (set G)" by fast
  hence "v \<noteq> 0\<^sub>v n" using span_zero by auto
  obtain B C where gj:"gauss_jordan ?A ?B = (B,C)" by force
  note gj = carr_mat(1,2) gj
  hence B:"B = fst (gauss_jordan ?A ?B)" by auto
  from gauss_jordan[OF gj] have BC:"B \<in> carrier_mat n n" by auto
  from gauss_jordan_transform[OF gj] obtain P where
   P:"P\<in>Units (ring_mat TYPE('a) n ?B)"  "B = P * ?A" by fast
  hence PC:"P \<in> carrier_mat n n" unfolding Units_def by (simp add: ring_mat_simps)
  from mat_inverse[OF PC] P obtain PI where "mat_inverse P = Some PI" by fast
  from mat_inverse(2)[OF PC this]
  have PI:"P * PI = 1\<^sub>m n" "PI * P = 1\<^sub>m n" "PI \<in> carrier_mat n n" by auto
  have "B \<noteq> 1\<^sub>m n" proof
    assume "B = ?B"
    hence "?A * P = ?B" unfolding P
      using PC P(2) carr_mat(1) mat_mult_left_right_inverse by blast
    hence "?A * P *\<^sub>v v = v" using v by auto
    hence "?A *\<^sub>v (P *\<^sub>v v) = v" unfolding assoc_mult_mat_vec[OF carr_mat(1) PC v(1)].
    hence v_eq:"mat_of_cols n G *\<^sub>v (P *\<^sub>v v) = v"
      unfolding transpose_mat_of_rows by auto
    have pvc:"P *\<^sub>v v \<in> carrier_vec (length G)" using PC v len by auto
    from mat_of_cols_mult_as_finsum[OF pvc g_len,unfolded v_eq] obtain a where
      "v = lincomb a (set G)" by auto
    hence "v \<in> span (set G)" by (intro in_spanI[OF _ finite_set subset_refl])
    thus False using v by auto
  qed
  with det_non_zero_imp_unit[OF carr_mat(1)] show ?thesis
    unfolding gauss_jordan_check_invertable[OF carr_mat(1,2)] B det_transpose[OF carr_mat(3)]
    by metis
qed

lemma span_basis_det_zero_iff:
assumes "length G = n" "set G \<subseteq> carrier_vec n"
shows "carrier_vec n \<subseteq> span (set G) \<longleftrightarrow> det (mat_of_rows n G) \<noteq> 0" (is ?q1)
      "carrier_vec n \<subseteq> span (set G) \<longleftrightarrow> basis (set G)" (is ?q2)
      "det (mat_of_rows n G) \<noteq> 0 \<longleftrightarrow> basis (set G)" (is ?q3)
proof -
  have dc:"det (mat_of_rows n G) \<noteq> 0 \<Longrightarrow> carrier_vec n \<subseteq> span (set G)"
    using assms non_span_det_zero by auto
  have cb:"carrier_vec n \<subseteq> span (set G) \<Longrightarrow> basis (set G)" using assms basis_list_basis 
    by (auto simp: basis_list_def)
  have bd:"basis (set G) \<Longrightarrow> det (mat_of_rows n G) \<noteq> 0" using assms basis_det_nonzero by auto
  show ?q1 ?q2 ?q3 using dc cb bd by metis+
qed

lemma lin_indpt_list_nonzero:
  assumes "lin_indpt_list G" 
  shows "0\<^sub>v n \<notin> set G"
proof-
  from assms[unfolded lin_indpt_list_def] have "lin_indpt (set G)" by auto
  from vs_zero_lin_dep[OF _ this] assms[unfolded lin_indpt_list_def] show zero: "0\<^sub>v n \<notin> set G" by auto
qed

lemma is_oc_projection_eq:
  assumes ispr:"is_oc_projection a S v" "is_oc_projection b S v" 
    and carr: "S \<subseteq> carrier_vec n" "v \<in> carrier_vec n"
  shows "a = b"
proof -
  from carr have c2:"span S \<subseteq> carrier_vec n" "v \<in> carrier_vec n" by auto
  have a:"v - (v - a) = a" using carr ispr by auto
  have b:"v - (v - b) = b" using carr ispr by auto
  have "(v - a) = (v - b)" 
    apply(rule oc_projection_alt_def[OF c2])
    using ispr a b unfolding in_orthogonal_complement_span[OF carr(1)]
    unfolding orthogonal_complement_def is_oc_projection_def by auto
  hence "v - (v - a) = v - (v - b)" by metis
  thus ?thesis unfolding a b.
qed



fun adjuster_wit :: "'a list \<Rightarrow> 'a vec \<Rightarrow> 'a vec list \<Rightarrow> 'a list \<times> 'a vec"
  where "adjuster_wit wits w [] = (wits, 0\<^sub>v n)"
  |  "adjuster_wit wits w (u#us) = (let a = (w \<bullet> u)/ sq_norm u in 
            case adjuster_wit (a # wits) w us of (wit, v)
         \<Rightarrow> (wit, -a \<cdot>\<^sub>v u + v))"

fun sub2_wit where
    "sub2_wit us [] = ([], [])"
  | "sub2_wit us (w # ws) =
     (case adjuster_wit [] w us of (wit,aw) \<Rightarrow> let u = aw + w in
      case sub2_wit (u # us) ws of (wits, vvs) \<Rightarrow> (wit # wits, u # vvs))"  
    
definition main :: "'a vec list \<Rightarrow> 'a list list \<times> 'a vec list" where 
  "main us = sub2_wit [] us"
end


locale gram_schmidt_fs = 
  fixes n :: nat and fs :: "'a :: {trivial_conjugatable_linordered_field} vec list"
begin

sublocale gram_schmidt n "TYPE('a)" .

fun gso and \<mu> where
  "gso i = fs ! i + sumlist (map (\<lambda> j. - \<mu> i j \<cdot>\<^sub>v gso j) [0 ..< i])" 
| "\<mu> i j = (if j < i then (fs ! i \<bullet> gso j)/ sq_norm (gso j) else if i = j then 1 else 0)" 
    
declare gso.simps[simp del]
declare \<mu>.simps[simp del]


lemma gso_carrier'[intro]:
  assumes "\<And> i. i \<le> j \<Longrightarrow> fs ! i \<in> carrier_vec n"
  shows "gso j \<in> carrier_vec n"
using assms proof(induct j rule:nat_less_induct[rule_format])
  case (1 j)
  then show ?case unfolding gso.simps[of j] by (auto intro!:sumlist_carrier add_carrier_vec)
qed

lemma adjuster_wit: assumes res: "adjuster_wit wits w us = (wits',a)"
  and w: "w \<in> carrier_vec n"
    and us: "\<And> i. i \<le> j \<Longrightarrow> fs ! i \<in> carrier_vec n"
    and us_gs: "us = map gso (rev [0 ..< j])" 
    and wits: "wits = map (\<mu> i) [j ..< i]" 
    and j: "j \<le> n" "j \<le> i" 
    and wi: "w = fs ! i" 
  shows "adjuster n w us = a \<and> a \<in> carrier_vec n \<and> wits' = map (\<mu> i) [0 ..< i] \<and>
      (a = sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<j]))"
  using res us us_gs wits j
proof (induct us arbitrary: wits wits' a j)
  case (Cons u us wits wits' a j)
  note us_gs = Cons(4)
  note wits = Cons(5)
  note jn = Cons(6-7)
  from us_gs obtain jj where j: "j = Suc jj" by (cases j, auto)
  from jn j have jj: "jj \<le> n" "jj < n" "jj \<le> i" "jj < i" by auto
  have zj: "[0 ..< j] = [0 ..< jj] @ [jj]" unfolding j by simp
  have jjn: "[jj ..< i] = jj # [j ..< i]" using jj unfolding j by (metis upt_conv_Cons)
  from us_gs[unfolded zj] have ugs: "u = gso jj" and us: "us = map gso (rev [0..<jj])" by auto
  let ?w = "w \<bullet> u / (u \<bullet> u)" 
  have muij: "?w = \<mu> i jj" unfolding \<mu>.simps[of i jj] ugs wi sq_norm_vec_as_cscalar_prod using jj by auto
  have wwits: "?w # wits = map (\<mu> i) [jj..<i]" unfolding jjn wits muij by simp
  obtain wwits b where rec: "adjuster_wit (?w # wits) w us = (wwits,b)" by force
  from Cons(1)[OF this Cons(3) us wwits jj(1,3),unfolded j] have IH: 
     "adjuster n w us = b" "wwits = map (\<mu> i) [0..<i]"
     "b = sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<jj])"
      and b: "b \<in> carrier_vec n" by auto
  from Cons(2)[simplified, unfolded Let_def rec split sq_norm_vec_as_cscalar_prod 
      cscalar_prod_is_scalar_prod]
  have id: "wits' = wwits" and a: "a = - ?w \<cdot>\<^sub>v u + b" by auto
  have 1: "adjuster n w (u # us) = a" unfolding a IH(1)[symmetric] by auto     
  from id IH(2) have wits': "wits' =  map (\<mu> i) [0..<i]" by simp
  have carr:"set (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<j]) \<subseteq> carrier_vec n"
            "set (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<jj]) \<subseteq> carrier_vec n" and u:"u \<in> carrier_vec n" 
    using Cons j by (auto intro!:gso_carrier')
  from u b a have ac: "a \<in> carrier_vec n" "dim_vec (-?w \<cdot>\<^sub>v u) = n" "dim_vec b = n" "dim_vec u = n" by auto
  show ?case
    apply (intro conjI[OF 1] ac exI conjI wits')
    unfolding carr a IH zj muij ugs[symmetric] map_append
    apply (subst sumlist_append)
    using Cons.prems j apply force
    using b u ugs IH(3) by auto
qed auto

lemma sub2_wit:
  assumes "set us \<subseteq> carrier_vec n" "set ws \<subseteq> carrier_vec n" "length us + length ws = m" 
    and "ws = map (\<lambda> i. fs ! i) [i ..< m]"
    and "us = map gso (rev [0 ..< i])" 
    and us: "\<And> j. j < m \<Longrightarrow> fs ! j \<in> carrier_vec n"
    and mn: "m \<le> n" 
  shows "sub2_wit us ws = (wits,vvs) \<Longrightarrow> gram_schmidt_sub2 n us ws = vvs 
    \<and> vvs = map gso [i ..< m] \<and> wits = map (\<lambda> i. map (\<mu> i) [0..<i]) [i ..< m]"
  using assms(1-6)
proof (induct ws arbitrary: us vvs i wits)
  case (Cons w ws us vs)  
  note us = Cons(3) note wws = Cons(4)
  note wsf' = Cons(6)
  note us_gs = Cons(7)
  from wsf' have "i < m" "i \<le> m" by (cases "i < m", auto)+
  hence i_m: "[i ..< m] = i # [Suc i ..< m]" by (metis upt_conv_Cons)
  from \<open>i < m\<close> mn have "i < n" "i \<le> n" "i \<le> m" by auto
  hence i_n: "[i ..< n] = i # [Suc i ..< n]" by (metis upt_conv_Cons)
  from wsf' i_m have wsf: "ws = map (\<lambda> i. fs ! i) [Suc i ..< m]" 
    and fiw: "fs !  i = w" by auto
  from wws have w: "w \<in> carrier_vec n" and ws: "set ws \<subseteq> carrier_vec n" by auto
  have list: "map (\<mu> i) [i ..< i] = []" by auto
  let ?a = "adjuster_wit [] w us" 
  obtain wit a where a: "?a = (wit,a)" by force
  obtain wits' vv where gs: "sub2_wit ((a + w) # us) ws = (wits',vv)" by force      
  from adjuster_wit[OF a w Cons(8) us_gs list[symmetric] \<open>i \<le> n\<close> _ fiw[symmetric]] us wws \<open>i < m\<close>
  have awus: "set ((a + w) # us) \<subseteq> carrier_vec n"  
     and aa: "adjuster n w us = a" "a \<in> carrier_vec n" 
     and aaa: "a = sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])"  
     and wit: "wit = map (\<mu> i) [0..<i]" 
    by auto
  have aw_gs: "a + w = gso i" unfolding gso.simps[of i] fiw aaa[symmetric] using aa(2) w by auto
  with us_gs have us_gs': "(a + w) # us = map gso (rev [0..<Suc i])" by auto
  from Cons(1)[OF gs awus ws _ wsf us_gs' Cons(8)] Cons(5) 
  have IH: "gram_schmidt_sub2 n ((a + w) # us) ws = vv"  
    and vv: "vv = map gso [Suc i..<m]" 
    and wits': "wits' = map (\<lambda>i. map (\<mu> i) [0..<i]) [Suc i ..< m]" by auto
  from gs a aa IH Cons(5) 
  have gs_vs: "gram_schmidt_sub2 n us (w # ws) = vs" and vs: "vs = (a + w) # vv" using Cons(2)
    by (auto simp add: Let_def snd_def split:prod.splits)
  from Cons(2)[unfolded sub2_wit.simps a split Let_def gs] have wits: "wits = wit # wits'" by auto
  from vs vv aw_gs have vs: "vs = map gso [i ..< m]" unfolding i_m by auto
  with gs_vs show ?case unfolding wits wit wits' by (auto simp: i_m)
qed auto
  
lemma partial_connect: fixes vs
  assumes "length fs = m" "k \<le> m" "m \<le> n" "set us \<subseteq> carrier_vec n" "snd (main us) = vs" 
  "us = take k fs" "set fs \<subseteq> carrier_vec n"
shows "gram_schmidt n us = vs" 
    "vs = map gso [0..<k]" 
proof -
  have [simp]: "map ((!) fs) [0..<k] = take k fs" using assms(1,2) by (intro nth_equalityI, auto)
  have carr: "j < m \<Longrightarrow> fs ! j \<in> carrier_vec n" for j using assms by auto
  note assms(5)[unfolded main_def]
  have "gram_schmidt_sub2 n [] (take k fs) = vvs \<and> vvs = map gso [0..<k] \<and> wits = map (\<lambda>i. map (\<mu> i) [0..<i]) [0..<k]"
    if "vvs = snd (sub2_wit [] (take k fs))" "wits = fst (sub2_wit [] (take k fs))" for vvs wits
    using assms that by (intro sub2_wit) (auto)
  with assms main_def
  show "gram_schmidt n us = vs" "vs = map gso [0..<k]" unfolding gram_schmidt_code
    by (auto simp add: main_def case_prod_beta')
qed

lemma adjuster_wit_small:
  "(adjuster_wit v a xs) = (x1,x2)
  \<longleftrightarrow> (fst (adjuster_wit v a xs) = x1 \<and> x2 = adjuster n a xs)"
proof(induct xs arbitrary: a v x1 x2)
  case (Cons a xs)
  then show ?case
    by (auto simp:Let_def sq_norm_vec_as_cscalar_prod split:prod.splits) 
qed auto

lemma sub2: "rev xs @ snd (sub2_wit xs us) = rev (gram_schmidt_sub n xs us)"
proof -
  have "sub2_wit xs us = (x1, x2) \<Longrightarrow> rev xs @ x2 = rev (gram_schmidt_sub n xs us)"
    for x1 x2 xs us
    apply(induct us arbitrary: xs x1 x2)
    by (auto simp:Let_def rev_unsimp adjuster_wit_small split:prod.splits simp del:rev.simps)
  thus ?thesis 
    apply (cases us)
    by (auto simp:Let_def rev_unsimp adjuster_wit_small split:prod.splits simp del:rev.simps)
qed

lemma gso_connect: "snd (main us) = gram_schmidt n us" unfolding main_def gram_schmidt_def
  using sub2[of Nil us] by auto

definition weakly_reduced :: "'a \<Rightarrow> nat \<Rightarrow> bool" 
  (* for k = n, this is reduced according to "Modern Computer Algebra" *)
  where "weakly_reduced \<alpha> k = (\<forall> i. Suc i < k \<longrightarrow> 
    sq_norm (gso i) \<le> \<alpha> * sq_norm (gso (Suc i)))" 
  
definition reduced :: "'a \<Rightarrow> nat \<Rightarrow> bool" 
  (* this is reduced according to LLL original paper *)
  where "reduced \<alpha> k = (weakly_reduced \<alpha> k \<and> 
    (\<forall> i j. i < k \<longrightarrow> j < i \<longrightarrow> abs (\<mu> i j) \<le> 1/2))"


end (* gram_schmidt_fs *)


locale gram_schmidt_fs_Rn = gram_schmidt_fs +
  assumes fs_carrier: "set fs \<subseteq> carrier_vec n"
begin

abbreviation (input) m where "m \<equiv> length fs"

definition M where "M k = mat k k (\<lambda> (i,j). \<mu> i j)"

lemma f_carrier[simp]: "i < m \<Longrightarrow> fs ! i \<in> carrier_vec n" 
  using fs_carrier unfolding set_conv_nth by force

lemma gso_carrier[simp]: "i < m \<Longrightarrow> gso i \<in> carrier_vec n" 
  using gso_carrier' f_carrier by auto

lemma gso_dim[simp]: "i < m \<Longrightarrow> dim_vec (gso i) = n" by auto
lemma f_dim[simp]: "i < m \<Longrightarrow> dim_vec (fs ! i) = n" by auto

lemma fs0_gso0: "0 < m \<Longrightarrow> fs ! 0 = gso 0" 
  unfolding gso.simps[of 0] using f_dim[of 0] 
  by (cases fs, auto simp add: upt_rec)

lemma fs_by_gso_def : 
assumes i: "i < m"
shows "fs ! i = gso i + M.sumlist (map (\<lambda>ja. \<mu> i ja \<cdot>\<^sub>v gso ja) [0..<i])" (is "_ = _ + ?sum")
proof -
  {
    fix f
    have a: "M.sumlist (map (\<lambda>ja. f ja \<cdot>\<^sub>v gso ja) [0..<i]) \<in> carrier_vec n" 
      using gso_carrier i by (intro M.sumlist_carrier, auto)
    hence "dim_vec (M.sumlist (map (\<lambda>ja. f ja \<cdot>\<^sub>v gso ja) [0..<i])) = n" by auto
    note a this
  } note sum_carrier = this
  note [simp] = sum_carrier(2)
  have f: "fs ! i \<in> carrier_vec n" using i by simp
  have "gso i + ?sum = fs ! i + M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i]) + ?sum " 
    (is "_ = _ + ?minus_sum + _")
    unfolding gso.simps[of i] by simp
  also have "?minus_sum = - ?sum"
    using gso_carrier i sum_carrier
    by (intro eq_vecI, auto simp: sumlist_nth sum_negf)
  also have "fs ! i + (-?sum) + ?sum = fs ! i"
    using sum_carrier fs_carrier f by simp
  finally show ?thesis by auto
qed


lemma main_connect:
  assumes "m \<le> n"
  shows "gram_schmidt n fs = map gso [0..<m]"
proof -
  obtain vs where snd_main: "snd (main fs) = vs" by auto
  have "gram_schmidt_sub2 n [] fs = snd (sub2_wit [] fs) \<and> snd (sub2_wit [] fs) = map gso [0..<length fs]
        \<and> wits = map (\<lambda>i. map (\<mu> i) [0..<i]) [0..<length fs]" 
    if "wits = fst (sub2_wit [] fs)" for wits
    using assms that fs_carrier by (intro  sub2_wit) (auto simp add: map_nth) 
  then have "gram_schmidt_sub2 n [] fs = vs \<and> vs = map gso [0..<m]"
    using snd_main main_def by auto
  thus "gram_schmidt n fs = map gso [0..<m]" by (auto simp: gram_schmidt_code)
qed


lemma reduced_gso_E: "weakly_reduced \<alpha> k \<Longrightarrow> k \<le> m \<Longrightarrow> Suc i < k \<Longrightarrow> 
  sq_norm (gso i) \<le> \<alpha> * sq_norm (gso (Suc i))" 
  unfolding weakly_reduced_def by auto
      
abbreviation (input) FF where "FF \<equiv> mat_of_rows n fs"
abbreviation (input) Fs where "Fs \<equiv> mat_of_rows n (map gso [0..<m])" 
  
lemma FF_dim[simp]: "dim_row FF = m" "dim_col FF = n" "FF \<in> carrier_mat m n" 
  unfolding mat_of_rows_def by (auto)

lemma Fs_dim[simp]: "dim_row Fs = m" "dim_col Fs = n" "Fs \<in> carrier_mat m n" 
  unfolding mat_of_rows_def by (auto simp: main_connect)

lemma M_dim[simp]: "dim_row (M m) = m" "dim_col (M m) = m" "(M m) \<in> carrier_mat m m"
  unfolding M_def by auto
    
lemma FF_index[simp]: "i < m \<Longrightarrow> j < n \<Longrightarrow> FF $$ (i,j) = fs ! i $ j" 
  unfolding mat_of_rows_def by auto

lemma M_index[simp]:"i < m \<Longrightarrow> j < m \<Longrightarrow> (M m) $$ (i,j) = \<mu> i j"
  unfolding M_def by auto
    
(* equation 2 on page 463 of textbook *)      
lemma matrix_equality: "FF = (M m) * Fs" 
proof - 
  let ?P = "(M m) * Fs" 
  have dim: "dim_row FF = m" "dim_col FF = n" "dim_row ?P = m" "dim_col ?P = n" "dim_row (M m) = m" "dim_col (M m) = m" 
      "dim_row Fs = m" "dim_col Fs = n" 
    by (auto simp: mat_of_rows_def mat_of_rows_list_def main_connect)
  show ?thesis 
  proof (rule eq_matI; unfold dim)
    fix i j
    assume i: "i < m" and j: "j < n" 
    from i have split: "[0 ..< m] = [0 ..< i] @ [i] @ [Suc i ..< m]"
      by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append upt_rec zero_less_Suc)
    let ?prod = "\<lambda> k. \<mu> i k * gso k $ j" 
    have dim2: "dim_vec (col Fs j) = m" using j dim by auto
    define idx where "idx = [0..<i]" 
    have idx: "set idx \<subseteq> {0 ..< i}" unfolding idx_def using i by auto
    let ?vec = "sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) idx)" 
    have vec: "?vec \<in> carrier_vec n" by (rule sumlist_carrier, insert idx gso_carrier i, auto)
    hence dimv: "dim_vec ?vec = n" by auto
    have "?P $$ (i,j) = row (M m) i \<bullet> col Fs j" using dim i j by auto
    also have "\<dots> = (\<Sum> k = 0..<m. row (M m) i $ k * col Fs j $ k)" 
      unfolding scalar_prod_def dim2 by auto
    also have "\<dots> = (\<Sum> k = 0..<m. ?prod k)" 
      by (rule sum.cong[OF refl], insert i j dim, auto simp: mat_of_rows_list_def mat_of_rows_def)
    also have "\<dots> = sum_list (map ?prod [0 ..< m])"       
      by (subst sum_list_distinct_conv_sum_set, auto)
    also have "\<dots> = sum_list (map ?prod idx) + ?prod i + sum_list (map ?prod [Suc i ..< m])" 
      unfolding split idx_def by auto
    also have "?prod i = gso i $ j" unfolding \<mu>.simps by simp
    also have "\<dots> = fs ! i $ j + sum_list (map (\<lambda>k. - \<mu> i k * gso k $ j) idx)" unfolding gso.simps[of i] idx_def[symmetric]
      by (subst index_add_vec, unfold dimv, rule j, subst sumlist_vec_index[OF _ j], insert idx gso_carrier i j, 
      auto simp: o_def intro!: arg_cong[OF map_cong])
    also have "sum_list (map (\<lambda>k. - \<mu> i k * gso k $ j) idx) = - sum_list (map (\<lambda>k. \<mu> i k * gso k $ j) idx)" 
      by (induct idx, auto)
    also have "sum_list (map ?prod [Suc i ..< m]) = 0"
      by (rule sum_list_neutral, auto simp: \<mu>.simps)
    finally have "?P $$ (i,j) = fs ! i $ j" by simp
    with FF_index[OF i j]
    show "FF $$ (i,j) = ?P $$ (i,j)" by simp
  qed auto
qed
  
lemma fi_is_sum_of_mu_gso: assumes i: "i < m" 
  shows "fs ! i = sumlist (map (\<lambda> j. \<mu> i j \<cdot>\<^sub>v gso j) [0 ..< Suc i])" 
proof -
  let ?l = "sumlist (map (\<lambda> j. \<mu> i j \<cdot>\<^sub>v gso j) [0 ..< Suc i])" 
  have "?l \<in> carrier_vec n" by (rule sumlist_carrier, insert gso_carrier i, auto)
  hence dim: "dim_vec ?l = n" by (rule carrier_vecD)
  show ?thesis 
  proof (rule eq_vecI, unfold dim f_dim[OF i])
    fix j
    assume j: "j < n"     
    from i have split: "[0 ..< m] = [0 ..< Suc i] @ [Suc i ..< m]"
      by (metis Suc_lessI append.assoc append_same_eq less_imp_add_positive order_refl upt_add_eq_append zero_le)
    let ?prod = "\<lambda> k. \<mu> i k * gso k $ j" 
    have "fs ! i $ j = FF $$ (i,j)" using i j by simp
    also have "\<dots> = ((M m) * Fs) $$ (i,j)" using matrix_equality by simp
    also have "\<dots> = row (M m) i \<bullet> col Fs j" using i j by auto
    also have "\<dots> = (\<Sum> k = 0..<m. row (M m) i $ k * col Fs j $ k)" 
      unfolding scalar_prod_def by auto
    also have "\<dots> = (\<Sum> k = 0..<m. ?prod k)" 
      by (rule sum.cong[OF refl], insert i j dim, auto simp: mat_of_rows_list_def mat_of_rows_def)
    also have "\<dots> = sum_list (map ?prod [0 ..< m])"       
      by (subst sum_list_distinct_conv_sum_set, auto)
    also have "\<dots> = sum_list (map ?prod [0 ..< Suc i]) + sum_list (map ?prod [Suc i ..< m])" 
      unfolding split by auto
    also have "sum_list (map ?prod [Suc i ..< m]) = 0" 
      by (rule sum_list_neutral, auto simp: \<mu>.simps)
    also have "sum_list (map ?prod [0 ..< Suc i]) = ?l $ j" 
      by (subst sumlist_vec_index[OF _ j], (insert i, auto simp: intro!: gso_carrier)[1], 
        rule arg_cong[of _ _ sum_list], insert i j, auto)
    finally show "fs ! i $ j = ?l $ j" by simp
  qed simp
qed

lemma gi_is_fi_minus_sum_mu_gso:
  assumes i: "i < m" 
  shows "gso i = fs ! i - sumlist (map (\<lambda> j. \<mu> i j \<cdot>\<^sub>v gso j) [0 ..< i])" (is "_ = _ - ?sum")
proof -
  have sum: "?sum \<in> carrier_vec n" 
    by (rule sumlist_carrier, insert gso_carrier i, auto)
  show ?thesis unfolding fs_by_gso_def[OF i]
    by (intro eq_vecI, insert gso_carrier[OF i] sum, auto)
qed

(* Theorem 16.5 (iv) *)  
lemma det: assumes m: "m = n" shows "det FF = det Fs" 
  unfolding matrix_equality
  apply (subst det_mult[OF M_dim(3)], (insert Fs_dim(3) m, auto)[1])
  apply (subst det_lower_triangular[OF _ M_dim(3)]) 
  by (subst M_index, (auto simp: \<mu>.simps)[3], unfold prod_list_diag_prod, auto simp: \<mu>.simps) 
end

locale gram_schmidt_fs_lin_indpt = gram_schmidt_fs_Rn +
  assumes lin_indpt: "lin_indpt (set fs)" and dist: "distinct fs"
begin

lemmas loc_assms = lin_indpt dist

lemma mn:
  shows "m \<le> n"
proof -
  have n: "n = dim" by (simp add: dim_is_n)
  have m: "m = card (set fs)"
    using distinct_card loc_assms by metis
  from m n have mn: "m \<le> n \<longleftrightarrow> card (set fs) \<le> dim" by simp
  show ?thesis unfolding mn
    by (rule li_le_dim, use loc_assms fs_carrier in auto)
qed

lemma
shows span_gso: "span (gso ` {0..<m}) = span (set fs)"
  and orthogonal_gso: "orthogonal (map gso [0..<m])" 
  and dist_gso: "distinct (map gso [0..<m])"
  using gram_schmidt_result[OF fs_carrier _ _ main_connect[symmetric]] loc_assms mn by auto

lemma gso_inj[intro]:
  assumes "i < m"
  shows "inj_on gso {0..<i}"
proof -
  { fix x y assume assms': "i < m" "x \<in> {0..<i}" "y \<in> {0..<i}" "gso x = gso y"
  have "distinct (map gso [0..<m])" "x < length (map gso [0..<m])" "y < length (map gso [0..<m])" 
    using dist_gso assms mn assms' by (auto intro!: dist_gso)
  from nth_eq_iff_index_eq[OF this] assms' have "x = y" by auto }
  then show ?thesis
    using assms by (intro inj_onI) auto
qed

lemma partial_span:
  assumes i: "i \<le> m" 
  shows "span (gso ` {0 ..< i}) = span (set (take i fs))" 
proof -
  let ?f = "\<lambda> i. fs ! i" 
  let ?us = "take i fs" 
  have len: "length ?us = i" using i by auto
  from fs_carrier i have us: "set ?us \<subseteq> carrier_vec n" 
    by (meson set_take_subset subset_trans)
  obtain vi where main: "snd (main ?us) = vi" by force
  from dist have dist: "distinct ?us" by auto
  from lin_indpt have indpt: "lin_indpt (set ?us)" 
    using supset_ld_is_ld[of "set ?us", of "set (?us @ drop i fs)"] 
    by (auto simp: set_take_subset)
  from partial_connect[OF _ i mn us main refl fs_carrier] assms
  have gso: "vi = gram_schmidt n ?us" and vi: "vi = map gso [0 ..< i]" by auto
  from cof_vec_space.gram_schmidt_result(1)[OF us dist indpt gso, unfolded vi]
  show ?thesis by auto
qed

lemma partial_span': 
  assumes i: "i \<le> m" 
  shows "span (gso ` {0 ..< i}) = span ((\<lambda> j. fs ! j) ` {0 ..< i})"
  unfolding partial_span[OF i]
  by (rule arg_cong[of _ _ span], subst nth_image, insert i loc_assms, auto)

(* Theorem 16.5 (iii) *)
lemma orthogonal:
  assumes "i < m" "j < m" "i \<noteq> j"
  shows "gso i \<bullet> gso j = 0"
  using assms mn orthogonal_gso[unfolded orthogonal_def] by auto

(* Theorem 16.5 (i) not in full general form *)  
lemma same_base:
  shows "span (set fs) = span (gso ` {0..<m})" 
  using span_gso loc_assms by simp

(* Theorem 16.5 (ii), second half *)
lemma sq_norm_gso_le_f:
  assumes i: "i < m"
  shows "sq_norm (gso i) \<le> sq_norm (fs ! i)"
proof -
  have id: "[0 ..< Suc i] = [0 ..< i] @ [i]" by simp
  let ?sum = "sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])" 
  have sum: "?sum \<in> carrier_vec n" and gsoi: "gso i \<in> carrier_vec n" using i
    by (auto intro!: sumlist_carrier gso_carrier)
  from fi_is_sum_of_mu_gso[OF i, unfolded id]
  have "sq_norm (fs ! i) = sq_norm (sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<i] @ [gso i]))" by (simp add: \<mu>.simps)
  also have "\<dots> = sq_norm (?sum + gso i)" 
    by (subst sumlist_append, insert gso_carrier i, auto)
  also have "\<dots> = (?sum + gso i) \<bullet> (?sum + gso i)" by (simp add: sq_norm_vec_as_cscalar_prod)
  also have "\<dots> = ?sum \<bullet> (?sum + gso i) + gso i \<bullet> (?sum + gso i)" 
    by (rule add_scalar_prod_distrib[OF sum gsoi], insert sum gsoi, auto)
  also have "\<dots> = (?sum \<bullet> ?sum + ?sum \<bullet> gso i) + (gso i \<bullet> ?sum + gso i \<bullet> gso i)" 
    by (subst (1 2) scalar_prod_add_distrib[of _ n], insert sum gsoi, auto)
  also have "?sum \<bullet> ?sum = sq_norm ?sum" by (simp add: sq_norm_vec_as_cscalar_prod)
  also have "gso i \<bullet> gso i = sq_norm (gso i)" by (simp add: sq_norm_vec_as_cscalar_prod)
  also have "gso i \<bullet> ?sum = ?sum \<bullet> gso i" using gsoi sum by (simp add: comm_scalar_prod)
  finally have "sq_norm (fs ! i) = sq_norm ?sum + 2 * (?sum \<bullet> gso i) + sq_norm (gso i)" by simp
  also have "\<dots> \<ge> 2 * (?sum \<bullet> gso i) + sq_norm (gso i)" using sq_norm_vec_ge_0[of ?sum] by simp
  also have "?sum \<bullet> gso i = (\<Sum>v\<leftarrow>map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<i]. v \<bullet> gso i)" 
    by (subst scalar_prod_left_sum_distrib[OF _ gsoi], insert i gso_carrier, auto)
  also have "\<dots> = 0" 
  proof (rule sum_list_neutral, goal_cases)
    case (1 x)
    then obtain j where j: "j < i" and x: "x = (\<mu> i j \<cdot>\<^sub>v gso j) \<bullet> gso i" by auto
    from j i have gsoj: "gso j \<in> carrier_vec n" by auto
    have "x = \<mu> i j * (gso j \<bullet> gso i)" using gsoi gsoj unfolding x by simp
    also have "gso j \<bullet> gso i = 0" 
      by (rule orthogonal, insert j i assms, auto)
    finally show "x = 0" by simp
  qed
  finally show ?thesis by simp
qed

(* Theorem 16.5 (ii), first half *)
lemma oc_projection_exist:
  assumes i: "i < m" 
  shows "fs ! i - gso i \<in> span (gso ` {0..<i})"
proof
  let ?A = "gso ` {0..<i}"
  show finA:"finite ?A" by auto
  have carA[intro!]:"?A \<subseteq> carrier_vec n" using gso_dim assms by auto
  let "?a v" = "\<Sum>n\<leftarrow>[0..<i]. if v = gso n then \<mu> i n else 0"
  have d:"(sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])) \<in> carrier_vec n"
    using gso.simps[of i] gso_dim[OF i] unfolding carrier_vec_def by auto
  note [intro] = f_carrier[OF i] gso_carrier[OF i] d
  have [intro!]:"(\<lambda>v. ?a v \<cdot>\<^sub>v v) \<in> gso ` {0..<i} \<rightarrow> carrier_vec n"
     using gso_carrier assms by auto
  {fix ia assume ia[intro]:"ia < n"
    have "(\<Sum>x\<in>gso ` {0..<i}. (?a x \<cdot>\<^sub>v x) $ ia) =
      - (\<Sum>x\<leftarrow>map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i]. x $ ia)"
    unfolding map_map comm_monoid_add_class.sum.reindex[OF gso_inj[OF assms]]
    unfolding atLeastLessThan_upt sum_set_upt_conv_sum_list_nat uminus_sum_list_map o_def
    proof(rule arg_cong[OF map_cong, OF refl],goal_cases)
      case (1 x) hence x:"x < m" "x < i" using assms by auto
      hence d:"insert x (set [0..<i]) = {0..<i}"
              "count (mset [0..<i]) x = 1" by auto
      hence "inj_on gso (insert x (set [0..<i]))" using gso_inj[OF assms] by auto
      from inj_on_filter_key_eq[OF this,folded replicate_count_mset_eq_filter_eq]
      have "[n\<leftarrow>[0..<i] . gso x = gso n] = [x]" using x assms d replicate.simps(2)[of 0] by auto
      hence "(\<Sum>n\<leftarrow>[0..<i]. if gso x = gso n then \<mu> i n else 0) = \<mu> i x"
        unfolding sum_list_map_filter'[symmetric] by auto
      with ia gso_dim x show ?case apply(subst index_smult_vec) by force+
    qed
    hence "(\<Oplus>\<^bsub>V\<^esub>v\<in>gso ` {0..<i}. ?a v \<cdot>\<^sub>v v) $ ia =
          (- local.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])) $ ia"
      using d assms
      apply (subst (0 0) finsum_index index_uminus_vec) apply force+
      apply (subst sumlist_vec_index) by force+
  }
  hence id: "(\<Oplus>\<^bsub>V\<^esub>v\<in>?A. ?a v \<cdot>\<^sub>v v) = - sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<i])"
    using d lincomb_dim[OF finA carA,unfolded lincomb_def] by(intro eq_vecI,auto)
  show "fs ! i - gso i = lincomb ?a ?A" unfolding lincomb_def gso.simps[of i] id
    by (rule eq_vecI, auto)
qed auto

lemma oc_projection_unique:
  assumes "i < m" 
          "v \<in> carrier_vec n"
          "\<And> x. x \<in> gso ` {0..<i} \<Longrightarrow> v \<bullet> x = 0"
          "fs ! i - v \<in> span (gso ` {0..<i})"
  shows "v = gso i"
proof -
  from assms have carr_span:"span (gso ` {0..<i}) \<subseteq> carrier_vec n" by(intro span_is_subset2) auto
  from assms have carr: "gso ` {0..<i} \<subseteq> carrier_vec n" by auto
  from assms have eq:"fs ! i - (fs ! i - v) = v" for v by auto
  from orthocompl_span[OF _ carr] assms
  have "y \<in> span (gso ` {0..<i}) \<Longrightarrow> v \<bullet> y = 0" for y by auto
  hence oc1:"fs ! i - (fs ! i - v) \<in> orthogonal_complement (span (gso ` {0..< i}))"
    unfolding eq orthogonal_complement_def using assms by auto
  have "x \<in> gso ` {0..<i} \<Longrightarrow> gso i \<bullet> x = 0" for x using assms orthogonal by auto
  hence "y \<in> span (gso ` {0..<i}) \<Longrightarrow> gso i \<bullet> y = 0" for y
    by (rule orthocompl_span) (use carr gso_carrier assms in auto)
  hence oc2:"fs ! i - (fs ! i - gso i) \<in> orthogonal_complement (span (gso ` {0..< i}))"
    unfolding eq orthogonal_complement_def using assms by auto
  note pe= oc_projection_exist[OF assms(1)]
  note prerec = carr_span f_carrier[OF assms(1)] assms(4) oc1 oc_projection_exist[OF assms(1)] oc2
  note prerec = carr_span f_carrier[OF assms(1)] assms(4) oc1 oc_projection_exist[OF assms(1)] oc2
  have gsoi: "gso i \<in> carrier_vec n" "fs ! i \<in> carrier_vec n"
    by (rule gso_carrier[OF \<open>i < m\<close>], rule f_carrier[OF \<open>i < m\<close>])
  note main = arg_cong[OF oc_projection_alt_def[OF carr_span f_carrier[OF assms(1)] assms(4) oc1 pe oc2], 
     of "\<lambda> v. - v $ j + fs ! i $ j" for j]
  show "v = gso i" 
  proof (intro eq_vecI)
    fix j
    show "j < dim_vec (gso i) \<Longrightarrow> v $ j = gso i $ j" 
      using assms gsoi main[of j] by (auto)
  qed (insert assms gsoi, auto)
qed

lemma gso_oc_projection:
  assumes "i < m"
  shows "gso i = oc_projection (gso ` {0..<i}) (fs ! i)"
  unfolding oc_projection_def is_oc_projection_def
proof (rule some_equality[symmetric,OF _ oc_projection_unique[OF assms]])
  have orthogonal:"\<And> xa. xa < i \<Longrightarrow> gso i \<bullet> gso xa = 0" by (rule orthogonal,insert assms, auto)
  show "gso i \<in> carrier_vec n \<and>
        fs ! i - gso i \<in> span (gso ` {0..<i}) \<and>
        (\<forall>x. x \<in> gso ` {0..<i} \<longrightarrow> gso i \<bullet> x = 0)"
    using gso_carrier oc_projection_exist assms orthogonal by auto
qed auto

lemma gso_oc_projection_span:
  assumes "i < m"
  shows "gso i = oc_projection (span (gso ` {0..<i})) (fs ! i)"
    and "is_oc_projection (gso i) (span (gso ` {0..<i})) (fs ! i)"
  unfolding oc_projection_def is_oc_projection_def
proof (rule some_equality[symmetric,OF _ oc_projection_unique[OF assms]])
  let ?P = "\<lambda>v. v \<in> carrier_vec n \<and> fs ! i - v \<in> span (span (gso ` {0..<i}))
    \<and> (\<forall>x. x \<in> span (gso ` {0..<i}) \<longrightarrow> v \<bullet> x = 0)"
  have carr:"gso ` {0..<i} \<subseteq> carrier_vec n" using assms by auto
  have *:  "\<And> xa. xa < i \<Longrightarrow> gso i \<bullet> gso xa = 0" by (rule orthogonal,insert assms, auto)
  have orthogonal:"\<And>x. x \<in> span (gso ` {0..<i}) \<Longrightarrow> gso i \<bullet> x = 0"
    apply(rule orthocompl_span) using assms * by auto
  show "?P (gso i)" "?P (gso i)" unfolding span_span[OF carr]
    using gso_carrier oc_projection_exist assms orthogonal by auto
  fix v assume p:"?P v"
  then show "v \<in> carrier_vec n" by auto
  from p show "fs ! i - v \<in> span (gso ` {0..<i})" unfolding span_span[OF carr] by auto
  fix xa assume "xa \<in> gso ` {0..<i}"
  hence "xa \<in> span (gso ` {0..<i})" using in_own_span[OF carr] by auto
  thus "v \<bullet> xa = 0" using p by auto
qed

lemma gso_is_oc_projection:
  assumes "i < m"
  shows "is_oc_projection (gso i) (set (take i fs)) (fs ! i)"
proof -
  have [simp]: "v \<in> carrier_vec n" if "v \<in> set (take i fs)" for v
    using that by (meson contra_subsetD fs_carrier in_set_takeD)
  have "span (gso ` {0..<i}) = span (set (take i fs))"
    by (rule partial_span) (auto simp add: assms less_or_eq_imp_le)
  moreover have "is_oc_projection (gso i) (span (gso ` {0..<i})) (fs ! i)"
    by (rule gso_oc_projection_span) (auto simp add: assms less_or_eq_imp_le)
  ultimately have "is_oc_projection (gso i) (span (set (take i fs))) (fs ! i)"
    by auto
  moreover have "set (take i fs) \<subseteq> span (set (take i fs))"
    by (auto intro!: span_mem)
  ultimately show ?thesis
    unfolding is_oc_projection_def by (subst (asm) span_span) (auto)
qed

lemma fi_scalar_prod_gso:
  assumes i: "i < m" and j: "j < m" 
  shows "fs ! i \<bullet> gso j = \<mu> i j * \<parallel>gso j\<parallel>\<^sup>2" 
proof -
  let ?mu = "\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j" 
  from i have list1: "[0..< m] = [0..< Suc i] @ [Suc i ..< m]" 
    by (intro nth_equalityI, auto simp: nth_append, rename_tac j, case_tac "j - i", auto)
  from j have list2: "[0..< m] = [0..< j] @ [j] @ [Suc j ..< m]" 
    by (intro nth_equalityI, auto simp: nth_append, rename_tac k, case_tac "k - j", auto)
  have "fs ! i \<bullet> gso j = sumlist (map ?mu [0..<Suc i]) \<bullet> gso j" 
    unfolding fi_is_sum_of_mu_gso[OF i] by simp
  also have "\<dots> = (\<Sum>v\<leftarrow>map ?mu [0..<Suc i]. v \<bullet> gso j) + 0" 
    by (subst scalar_prod_left_sum_distrib, insert gso_carrier assms, auto)
  also have "\<dots> = (\<Sum>v\<leftarrow>map ?mu [0..<Suc i]. v \<bullet> gso j) + (\<Sum>v\<leftarrow>map ?mu [Suc i..<m]. v \<bullet> gso j)" 
    by (subst (3) sum_list_neutral, insert assms gso_carrier, auto intro!: orthogonal simp: \<mu>.simps)
  also have "\<dots> = (\<Sum>v\<leftarrow>map ?mu [0..< m]. v \<bullet> gso j)" 
    unfolding list1 by simp
  also have "\<dots> = (\<Sum>v\<leftarrow>map ?mu [0..< j]. v \<bullet> gso j) + ?mu j \<bullet> gso j + (\<Sum>v\<leftarrow>map ?mu [Suc j..< m]. v \<bullet> gso j)" 
    unfolding list2 by simp
  also have "(\<Sum>v\<leftarrow>map ?mu [0..< j]. v \<bullet> gso j) = 0" 
    by (rule sum_list_neutral, insert assms gso_carrier, auto intro!: orthogonal)
  also have "(\<Sum>v\<leftarrow>map ?mu [Suc j..< m]. v \<bullet> gso j) = 0" 
    by (rule sum_list_neutral, insert assms gso_carrier, auto intro!: orthogonal)
  also have "?mu j \<bullet> gso j = \<mu> i j * sq_norm (gso j)" 
    using gso_carrier[OF j] by (simp add: sq_norm_vec_as_cscalar_prod)  
  finally show ?thesis by simp
qed

lemma gso_scalar_zero:
  assumes "k < m" "i < k"
  shows "(gso k) \<bullet> (fs ! i) = 0"
  by (subst comm_scalar_prod[OF gso_carrier]; (subst fi_scalar_prod_gso)?,
  insert assms, auto simp: \<mu>.simps)

lemma scalar_prod_lincomb_gso:
  assumes k: "k \<le> m"
  shows "sumlist (map (\<lambda> i. g i \<cdot>\<^sub>v gso i) [0 ..< k]) \<bullet> sumlist (map (\<lambda> i. h i \<cdot>\<^sub>v gso i) [0 ..< k])
    = sum_list (map (\<lambda> i. g i * h i * (gso i \<bullet> gso i)) [0 ..< k])" 
proof -
  have id1: "map (\<lambda>i. g i \<cdot>\<^sub>v map (gso) [0..<m] ! i) [0..<k] = map (\<lambda>i. g i \<cdot>\<^sub>v gso i) [0..<k]" for g using k
    by auto
  have id2: "(\<Sum>i\<leftarrow>[0..<k]. g i * h i * (map (gso) [0..<m] ! i \<bullet> map (gso) [0..<m] ! i)) 
    = (\<Sum>i\<leftarrow>[0..<k]. g i * h i * (gso i \<bullet> gso i))" using k
    by (intro arg_cong[OF map_cong], auto)
  define gs where "gs = map (gso) [0..<m]"
  have gs_gso: "gs ! i = gso i" if "i < k" for i
    using that assms unfolding gs_def by auto
  have "M.sumlist (map (\<lambda>i. g i \<cdot>\<^sub>v gs ! i) [0..<k]) \<bullet> M.sumlist (map (\<lambda>i. h i \<cdot>\<^sub>v gs ! i) [0..<k]) = 
        (\<Sum>i\<leftarrow>[0..<k]. g i * h i * (gs ! i \<bullet> gs ! i))"
    unfolding gs_def using  assms  orthogonal_gso 
    by (intro scalar_prod_lincomb_orthogonal) auto
  also have "map (\<lambda>i. g i \<cdot>\<^sub>v gs ! i) [0..<k] = map (\<lambda>i. g i \<cdot>\<^sub>v gso i) [0..<k]"
    using gs_gso by (intro map_cong) (auto)
  also have "map (\<lambda>i. h i \<cdot>\<^sub>v gs ! i) [0..<k] = map (\<lambda>i. h i \<cdot>\<^sub>v gso i) [0..<k]"
    using gs_gso by (intro map_cong) (auto)
  also have "map (\<lambda>i. g i * h i * (gs ! i \<bullet> gs ! i)) [0..<k] = map (\<lambda>i. g i * h i * (gso i \<bullet> gso i)) [0..<k]"
    using gs_gso by (intro map_cong) (auto)
  finally show ?thesis by simp
qed

lemma gso_times_self_is_norm:
  assumes "j < m"
  shows "fs ! j \<bullet> gso j = sq_norm (gso j)"
  by (subst fi_scalar_prod_gso, insert assms, auto simp: \<mu>.simps)

(* Lemma 16.7 *)
lemma gram_schmidt_short_vector: 
  assumes in_L: "h \<in> lattice_of fs - {0\<^sub>v n}" 
  shows "\<exists> i < m. \<parallel>h\<parallel>\<^sup>2 \<ge> \<parallel>gso i\<parallel>\<^sup>2"
proof -
  from in_L have non_0: "h \<noteq> 0\<^sub>v n" by auto
  from in_L[unfolded lattice_of_def] obtain lam where 
    h: "h =  sumlist (map (\<lambda> i. of_int (lam i) \<cdot>\<^sub>v fs ! i) [0 ..< length fs])" 
    by auto
  have in_L: "h = sumlist (map (\<lambda> i. of_int (lam i) \<cdot>\<^sub>v fs ! i) [0 ..< m])" unfolding length_map h
    by (rule arg_cong[of _ _ sumlist], rule map_cong, auto)
  let ?n = "[0 ..< m]" 
  let ?f = "(\<lambda> i. of_int (lam i) \<cdot>\<^sub>v fs ! i)" 
  let ?vs = "map ?f ?n" 
  let ?P = "\<lambda> k. k < m \<and> lam k \<noteq> 0" 
  define k where "k = (GREATEST kk. ?P kk)" 
  { 
    assume *: "\<forall> i < m. lam i = 0" 
    have vs: "?vs = map (\<lambda> i. 0\<^sub>v n) ?n"
      by (rule map_cong, insert f_dim *, auto)
    have "h = 0\<^sub>v n" unfolding in_L vs
      by (rule sumlist_neutral, auto)
    with non_0 have False by auto
  }  
  then obtain kk where "?P kk" by auto
  from GreatestI_nat[of ?P, OF this, of m] have Pk: "?P k" unfolding k_def by auto      
  hence kn: "k < m" by auto
  let ?gso = "(\<lambda>i j. \<mu> i j \<cdot>\<^sub>v gso j)" 
  have k: "k < i \<Longrightarrow> i < m \<Longrightarrow> lam i = 0" for i
    using Greatest_le_nat[of ?P i m, folded k_def] by auto
  define l where "l = lam k" 
  from Pk have l: "l \<noteq> 0" unfolding l_def by auto
  define idx where "idx = [0 ..< k]" 
  have idx: "\<And> i. i \<in> set idx \<Longrightarrow> i < k" "\<And> i. i \<in> set idx \<Longrightarrow> i < m"  unfolding idx_def using kn by auto
  from Pk have split: "[0 ..< m] = idx @ [k] @ [Suc k ..< m]" unfolding idx_def
    by (metis append_Cons append_self_conv2 less_Suc_eq_le less_imp_add_positive upt_add_eq_append 
        upt_rec zero_less_Suc)  
  define gg where "gg = sumlist 
    (map (\<lambda>i. of_int (lam i) \<cdot>\<^sub>v fs ! i) idx) + of_int l \<cdot>\<^sub>v sumlist (map (\<lambda>j. \<mu> k j \<cdot>\<^sub>v gso j) idx)" 
  have "h = sumlist ?vs" unfolding in_L ..
  also have "\<dots> = sumlist ((map ?f idx @ [?f k]) @ map ?f [Suc k ..< m])" unfolding split by auto
  also have "\<dots> = sumlist (map ?f idx @ [?f k]) + sumlist (map ?f [Suc k ..< m])" 
    by (rule sumlist_append, auto intro!: f_carrier, insert Pk idx, auto)
  also have "sumlist (map ?f [Suc k ..< m]) = 0\<^sub>v n" by (rule sumlist_neutral, auto simp: k)
  also have "sumlist (map ?f idx @ [?f k]) = sumlist (map ?f idx) + ?f k" 
    by (subst sumlist_append, auto intro!: f_carrier, insert Pk idx, auto)
  also have "fs ! k = sumlist (map (?gso k) [0..<Suc k])" using fi_is_sum_of_mu_gso[OF kn] by simp
  also have "\<dots> = sumlist (map (?gso k) idx @ [gso k])" by (simp add: \<mu>.simps[of k k] idx_def)
  also have "\<dots> = sumlist (map (?gso k) idx) + gso k" 
    by (subst sumlist_append, auto intro!: f_carrier, insert Pk idx, auto)
  also have "of_int (lam k) \<cdot>\<^sub>v \<dots> = of_int (lam k) \<cdot>\<^sub>v (sumlist (map (?gso k) idx)) 
    + of_int (lam k) \<cdot>\<^sub>v gso k" 
    unfolding idx_def
    by (rule smult_add_distrib_vec[OF sumlist_carrier], auto intro!: gso_carrier, insert kn, auto)
  finally have "h = sumlist (map ?f idx) +
       (of_int (lam k) \<cdot>\<^sub>v sumlist (map (?gso k) idx) + of_int (lam k) \<cdot>\<^sub>v gso k) + 0\<^sub>v n " by simp 
  also have "\<dots> = gg + of_int l \<cdot>\<^sub>v gso k" unfolding gg_def l_def
    by (rule eq_vecI, insert idx kn, auto simp: sumlist_vec_index,
      subst index_add_vec, auto simp: sumlist_dim kn, subst sumlist_dim, auto)
  finally have hgg: "h = gg + of_int l \<cdot>\<^sub>v gso k" .      
  let ?k = "[0 ..< k]" 
  define R where "R = {gg. \<exists> nu. gg = sumlist (map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) idx)}" 
  {
    fix nu
    have "dim_vec (sumlist (map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) idx)) = n" 
      by (rule sumlist_dim, insert kn, auto simp: idx_def)
  } note dim_nu[simp] = this
  define kk where "kk = ?k" 
  {
    fix v
    assume "v \<in> R"
    then obtain nu where v: "v = sumlist (map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) idx)" unfolding R_def by auto
    have "dim_vec v = n" unfolding gg_def v by simp
  } note dim_R = this
  {
    fix v1 v2
    assume "v1 \<in> R" "v2 \<in> R" 
    then obtain nu1 nu2 where v1: "v1 = sumlist (map (\<lambda> i. nu1 i \<cdot>\<^sub>v gso i) idx)" and
      v2: "v2 = sumlist (map (\<lambda> i. nu2 i \<cdot>\<^sub>v gso i) idx)"
      unfolding R_def by auto
    have "v1 + v2 \<in> R" unfolding R_def
      by (standard, rule exI[of _ "\<lambda> i. nu1 i + nu2 i"], unfold v1 v2, rule eq_vecI, 
        (subst sumlist_vec_index, insert idx, auto intro!: gso_carrier simp: o_def)+, 
        unfold sum_list_addf[symmetric], induct idx, auto simp: algebra_simps)
  } note add_R = this
  have "gg \<in> R" unfolding gg_def
  proof (rule add_R)
    show "of_int l \<cdot>\<^sub>v sumlist (map (\<lambda>j. \<mu> k j \<cdot>\<^sub>v gso j) idx) \<in> R" 
      unfolding R_def
      by (standard, rule exI[of _ "\<lambda>i. of_int l * \<mu> k i"], rule eq_vecI,
       (subst sumlist_vec_index, insert idx, auto intro!: gso_carrier simp: o_def)+, 
       induct idx, auto simp: algebra_simps)
    show "sumlist (map ?f idx) \<in> R" using idx
    proof (induct idx)
      case Nil
      show ?case by (simp add: R_def, intro exI[of _ "\<lambda> i. 0"], rule eq_vecI,
        (subst sumlist_vec_index, insert idx, auto intro!: gso_carrier simp: o_def)+, 
        induct idx, auto)
    next      
      case (Cons i idxs)
      have "sumlist (map ?f (i # idxs)) = sumlist ([?f i] @ map ?f idxs)" by simp
      also have "\<dots> = ?f i + sumlist (map ?f idxs)" 
        by (subst sumlist_append, insert Cons(3), auto intro!: f_carrier)
      finally have id: "sumlist (map ?f (i # idxs)) = ?f i + sumlist (map ?f idxs)" .
      show ?case unfolding id
      proof (rule add_R[OF _ Cons(1)[OF Cons(2-3)]])
        from Cons(2-3) have i: "i < m" "i < k" by auto
        hence idx_split: "idx = [0 ..< Suc i] @ [Suc i ..< k]" unfolding idx_def 
          by (metis Suc_lessI append_Nil2 less_imp_add_positive upt_add_eq_append upt_rec zero_le)
        {
          fix j
          assume j: "j < n" 
          define idxs where "idxs = [0 ..< Suc i]"
          let ?f = "\<lambda> x. ((if x < Suc i then of_int (lam i) * \<mu> i x else 0) \<cdot>\<^sub>v gso x) $ j" 
          have "(\<Sum>x\<leftarrow>idx. ?f x) = (\<Sum>x\<leftarrow>[0 ..< Suc i]. ?f x) + (\<Sum>x\<leftarrow> [Suc i ..< k]. ?f x)" 
            unfolding idx_split by auto
          also have "(\<Sum>x\<leftarrow> [Suc i ..< k]. ?f x) = 0" by (rule sum_list_neutral, insert j kn, auto)          
          also have "(\<Sum>x\<leftarrow>[0 ..< Suc i]. ?f x) = (\<Sum>x\<leftarrow>idxs. of_int (lam i) * (\<mu> i x \<cdot>\<^sub>v gso x) $ j)" 
            unfolding idxs_def by (rule arg_cong[of _ _ sum_list], rule map_cong[OF refl], 
                subst index_smult_vec, insert j i kn, auto)
          also have "\<dots> = of_int (lam i) * ((\<Sum>x\<leftarrow>[0..<Suc i]. (\<mu> i x \<cdot>\<^sub>v gso x) $ j))" 
            unfolding idxs_def[symmetric] by (induct idxs, auto simp: algebra_simps)
          finally have "(\<Sum>x\<leftarrow>idx. ?f x) = of_int (lam i) * ((\<Sum>x\<leftarrow>[0..<Suc i]. (\<mu> i x \<cdot>\<^sub>v gso x) $ j))" 
            by simp
        } note main = this
        show "?f i \<in> R" unfolding fi_is_sum_of_mu_gso[OF i(1)] R_def
          apply (standard, rule exI[of _ "\<lambda> j. if j < Suc i then of_int (lam i) * \<mu> i j else 0"], rule eq_vecI)
           apply (subst sumlist_vec_index, insert idx i, auto intro!: gso_carrier sumlist_dim simp: o_def)
          apply (subst index_smult_vec, subst sumlist_dim, auto) 
          apply (subst sumlist_vec_index, auto, insert idx i main, auto simp: o_def)
        done
      qed auto
    qed
  qed
  then obtain nu where gg: "gg = sumlist (map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) idx)" unfolding R_def by auto
  let ?ff = "sumlist (map (\<lambda>i. nu i \<cdot>\<^sub>v gso i) idx) + of_int l \<cdot>\<^sub>v gso k" 
  define hh where "hh = (\<lambda> i. (if i < k then nu i else of_int l))" 
  let ?hh = "sumlist (map (\<lambda> i. hh i \<cdot>\<^sub>v gso i) [0 ..< Suc k])" 
  have ffhh: "?hh = sumlist (map (\<lambda> i. hh i \<cdot>\<^sub>v gso i) [0 ..< k] @ [hh k \<cdot>\<^sub>v gso k])" 
    by simp
  also have "\<dots> = sumlist (map (\<lambda> i. hh i \<cdot>\<^sub>v gso i) [0 ..< k]) + sumlist [hh k \<cdot>\<^sub>v gso k]" 
    by (rule sumlist_append, insert kn, auto)
  also have "sumlist [hh k \<cdot>\<^sub>v gso k] = hh k \<cdot>\<^sub>v gso k" using kn by auto
  also have "\<dots> = of_int l \<cdot>\<^sub>v gso k" unfolding hh_def by auto
  also have "map (\<lambda> i. hh i \<cdot>\<^sub>v gso i) [0 ..< k] = map (\<lambda> i. nu i \<cdot>\<^sub>v gso i) [0 ..< k]" 
    by (rule map_cong, auto simp: hh_def)
  finally have ffhh: "?ff = ?hh" by (simp add: idx_def)
  from hgg[unfolded gg] 
  have h: "h = ?ff" by auto
  have "gso k \<bullet> gso k \<le> 1 * (gso k \<bullet> gso k)" by simp
  also have "\<dots> \<le> of_int (l * l) * (gso k \<bullet> gso k)" 
  proof (rule mult_right_mono)
    from l have "l * l \<ge> 1" by (meson eq_iff int_one_le_iff_zero_less mult_le_0_iff not_le)
    thus "1 \<le> (of_int (l * l) :: 'a)" by presburger     
    show "0 \<le> gso k \<bullet> gso k" by (rule scalar_prod_ge_0)
  qed
  also have "\<dots> = 0 + of_int (l * l) * (gso k \<bullet> gso k)" by simp
  also have "\<dots> \<le> sum_list (map (\<lambda> i. (nu i * nu i) * (gso i \<bullet> gso i)) idx) + of_int (l * l) * (gso k \<bullet> gso k)" 
    by (rule add_right_mono, rule sum_list_nonneg, auto, rule mult_nonneg_nonneg, auto simp: scalar_prod_ge_0)
  also have "map (\<lambda> i. (nu i * nu i) * (gso i \<bullet> gso i)) idx = map (\<lambda> i. hh i * hh i * (gso i \<bullet> gso i)) [0..<k]" 
    unfolding idx_def by (rule map_cong, auto simp: hh_def) 
  also have "of_int (l * l) = hh k * hh k" unfolding hh_def by auto
  also have "(\<Sum>i\<leftarrow>[0..<k]. hh i * hh i * (gso i \<bullet> gso i)) + hh k * hh k * (gso k \<bullet> gso k)
     = (\<Sum>i\<leftarrow>[0..<Suc k]. hh i * hh i * (gso i \<bullet> gso i))" by simp
  also have "\<dots> = ?hh \<bullet> ?hh" by (rule sym, rule scalar_prod_lincomb_gso, insert kn assms, auto)
  also have "\<dots> = ?ff \<bullet> ?ff" by (simp add: ffhh)
  also have "\<dots> = h \<bullet> h" unfolding h ..
  finally show ?thesis using kn unfolding sq_norm_vec_as_cscalar_prod by auto
qed

   
(* Theorem 16.9 
  (bound in textbook looks better as it uses 2^((n-1)/2), but this difference
  is caused by the fact that we here we look at the squared norms) *)
lemma weakly_reduced_imp_short_vector: 
  assumes "weakly_reduced \<alpha> m"
    and in_L: "h \<in> lattice_of fs - {0\<^sub>v n}" and \<alpha>_pos:"\<alpha> \<ge> 1"
  shows "fs \<noteq> [] \<and> sq_norm (fs ! 0) \<le> \<alpha>^(m-1) * sq_norm h"
proof -
  from gram_schmidt_short_vector assms obtain i where 
    i: "i < m" and le: "sq_norm (gso i) \<le> sq_norm h" by auto
  have small: "sq_norm (fs ! 0) \<le> \<alpha>^i * sq_norm (gso i)" using i
  proof (induct i)
    case 0
    show ?case unfolding fs0_gso0[OF 0] by auto
  next
    case (Suc i)
    hence "sq_norm (fs ! 0) \<le> \<alpha>^i * sq_norm (gso i)" by auto
    also have "\<dots> \<le> \<alpha>^i * (\<alpha> * (sq_norm (gso (Suc i))))" 
      using reduced_gso_E[OF assms(1) le_refl Suc(2)] \<alpha>_pos by auto
    finally show ?case unfolding class_semiring.nat_pow_Suc[of \<alpha> i] by auto
  qed
  also have "\<dots> \<le> \<alpha>^(m-1) * sq_norm h" 
    by (rule mult_mono[OF power_increasing le], insert i \<alpha>_pos, auto)
  finally show ?thesis using i by (cases fs, auto)
qed


lemma sq_norm_pos: 
  assumes j: "j < m" 
  shows "sq_norm (gso j) > 0"
proof -
  from j have jj: "j < m - 0" by simp
  from orthogonalD[OF orthogonal_gso, unfolded length_map length_upt, OF jj jj] assms
  have "sq_norm (gso j) \<noteq> 0" using j by (simp add: sq_norm_vec_as_cscalar_prod)    
  moreover have "sq_norm (gso j) \<ge> 0" by auto
  ultimately show "0 < sq_norm (gso j)" by auto
qed

lemma Gramian_determinant: 
  assumes k: "k \<le> m" 
  shows "Gramian_determinant fs k = (\<Prod> j<k. sq_norm (gso j))"
    "Gramian_determinant fs k > 0" 
proof -
  define Gk where "Gk = mat k n (\<lambda> (i,j). fs ! i $ j)" 
  have Gk: "Gk \<in> carrier_mat k n" unfolding Gk_def by auto
  define Mk where "Mk = mat k k (\<lambda> (i,j). \<mu> i j)" 
  have Mk_\<mu>: "i < k \<Longrightarrow> j < k \<Longrightarrow> Mk $$ (i,j) = \<mu> i j" for i j
    unfolding Mk_def using k by auto
  have Mk: "Mk \<in> carrier_mat k k" and [simp]: "dim_row Mk = k" "dim_col Mk = k" unfolding Mk_def by auto
  have "det Mk = prod_list (diag_mat Mk)" 
    by (rule det_lower_triangular[OF _ Mk], auto simp: Mk_\<mu> \<mu>.simps)
  also have "\<dots> = 1" 
    by (rule prod_list_neutral, auto simp: diag_mat_def Mk_\<mu> \<mu>.simps)
  finally have detMk: "det Mk = 1" .
  define Gsk where "Gsk = mat k n (\<lambda> (i,j). gso i $ j)" 
  have Gsk: "Gsk \<in> carrier_mat k n" unfolding Gsk_def by auto
  have Gsk': "Gsk\<^sup>T \<in> carrier_mat n k" using Gsk by auto
  let ?Rn = "carrier_vec n" 
  have id: "Gk = Mk * Gsk" 
  proof (rule eq_matI)
    from Gk Mk Gsk 
    have dim: "dim_row Gk = k" "dim_row (Mk * Gsk) = k" "dim_col Gk = n" "dim_col (Mk * Gsk) = n" by auto
    from dim show "dim_row Gk = dim_row (Mk * Gsk)" "dim_col Gk = dim_col (Mk * Gsk)" by auto
    fix i j
    assume "i < dim_row (Mk * Gsk)" "j < dim_col (Mk * Gsk)"     
    hence ij: "i < k" "j < n" and i: "i < m" using dim k by auto    
    have Gi: "fs ! i \<in> ?Rn" using i by simp
    have "Gk $$ (i, j) = fs ! i $ j" unfolding Gk_def using ij k Gi by auto
    also have "... = FF $$ (i,j)" using ij i by simp
    also have "FF = (M m) * Fs" by (rule matrix_equality)
    also have "\<dots> $$ (i,j) = row (M m) i \<bullet> col Fs j" 
      by (rule index_mult_mat(1), insert i ij, auto simp: mat_of_rows_list_def)
    also have "row (M m) i = vec m (\<lambda> j. if j < k then Mk $$ (i,j) else 0)" 
      (is "_ = vec m ?Mk") 
      unfolding Mk_def using ij i
      by (auto simp: mat_of_rows_list_def \<mu>.simps)
    also have "col Fs j = vec m (\<lambda> i'. if i' < k then Gsk $$ (i',j) else (Fs $$ (i',j)))" 
      (is "_ = vec m ?Gsk") 
      unfolding Gsk_def using ij i by (auto simp: mat_of_rows_def)
    also have "vec m ?Mk \<bullet> vec m ?Gsk = (\<Sum> i \<in> {0 ..< m}. ?Mk i * ?Gsk i)" 
      unfolding scalar_prod_def by auto
    also have "\<dots> = (\<Sum> i \<in> {0 ..< k} \<union> {k ..< m}. ?Mk i * ?Gsk i)"
      by (rule sum.cong, insert k, auto)
    also have "\<dots> = (\<Sum> i \<in> {0 ..< k}. ?Mk i * ?Gsk i) + (\<Sum> i \<in> {k ..< m}. ?Mk i * ?Gsk i)" 
      by (rule sum.union_disjoint, auto)
    also have "(\<Sum> i \<in> {k ..< m}. ?Mk i * ?Gsk i) = 0" 
      by (rule sum.neutral, auto)
    also have "(\<Sum> i \<in> {0 ..< k}. ?Mk i * ?Gsk i) = (\<Sum> i' \<in> {0 ..< k}. Mk $$ (i,i') * Gsk $$ (i',j))"
      by (rule sum.cong, auto)
    also have "\<dots> = row Mk i \<bullet> col Gsk j" unfolding scalar_prod_def using ij 
      by (auto simp: Gsk_def Mk_def)
    also have "\<dots> = (Mk * Gsk) $$ (i, j)" using ij Mk Gsk by simp
    finally show "Gk $$ (i, j) = (Mk * Gsk) $$ (i, j)" by simp
  qed
  have cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by auto
  have "Gramian_determinant fs k = det (Gk * Gk\<^sup>T)" 
    unfolding Gramian_determinant_def Gramian_matrix_def Let_def
    by (rule arg_cong[of _ _ det], rule cong, insert k, auto simp: Gk_def) 
  also have "Gk\<^sup>T = Gsk\<^sup>T * Mk\<^sup>T" (is "_ = ?TGsk * ?TMk") unfolding id 
    by (rule transpose_mult[OF Mk Gsk])
  also have "Gk = Mk * Gsk" by fact
  also have "\<dots> * (?TGsk * ?TMk) = Mk * (Gsk * (?TGsk * ?TMk))" 
    by (rule assoc_mult_mat[OF Mk Gsk, of _ k], insert Gsk Mk, auto)
  also have "det \<dots> = det Mk * det (Gsk * (?TGsk * ?TMk))" 
    by (rule det_mult[OF Mk], insert Gsk Mk, auto)
  also have "\<dots> = det (Gsk * (?TGsk * ?TMk))" using detMk by simp
  also have "Gsk * (?TGsk * ?TMk) = (Gsk * ?TGsk) * ?TMk" 
    by (rule assoc_mult_mat[symmetric, OF Gsk], insert Gsk Mk, auto)
  also have "det \<dots> = det (Gsk * ?TGsk) * det ?TMk" 
    by (rule det_mult, insert Gsk Mk, auto)
  also have "\<dots> = det (Gsk * ?TGsk)" using detMk det_transpose[OF Mk] by simp
  also have "Gsk * ?TGsk = mat k k (\<lambda> (i,j). if i = j then sq_norm (gso j) else 0)" (is "_ = ?M")
  proof (rule eq_matI)
    show "dim_row (Gsk * ?TGsk) = dim_row ?M" unfolding Gsk_def by auto
    show "dim_col (Gsk * ?TGsk) = dim_col ?M" unfolding Gsk_def by auto
    fix i j
    assume "i < dim_row ?M" "j < dim_col ?M" 
    hence ij: "i < k" "j < k" and ijn: "i < m" "j < m" using k by auto
    {
      fix i
      assume "i < k" 
      hence "i < m" using k by auto
      hence Gs: "gso i \<in> ?Rn" by auto
      have "row Gsk i = gso i" unfolding row_def Gsk_def
        by (rule eq_vecI, insert Gs \<open>i < k\<close>, auto)
    } note row = this
    have "(Gsk * ?TGsk) $$ (i,j) = row Gsk i \<bullet> row Gsk j" using ij Gsk by auto
    also have "\<dots> = gso i \<bullet> gso j" using row ij by simp
    also have "\<dots> = (if i = j then sq_norm (gso j) else 0)" 
    proof (cases "i = j")
      assume "i = j" 
      thus ?thesis by (simp add: sq_norm_vec_as_cscalar_prod) 
    next
      assume "i \<noteq> j" 
      from \<open>i \<noteq> j\<close> orthogonalD[OF orthogonal_gso] ijn assms
      show ?thesis by auto
    qed
    also have "\<dots> = ?M $$ (i,j)" using ij by simp
    finally show "(Gsk * ?TGsk) $$ (i,j) = ?M $$ (i,j)" .
  qed
  also have "det ?M = prod_list (diag_mat ?M)" 
    by (rule det_upper_triangular, auto)
  also have "diag_mat ?M = map (\<lambda> j. sq_norm (gso j)) [0 ..< k]" unfolding diag_mat_def by auto
  also have "prod_list \<dots> = (\<Prod> j < k. sq_norm (gso j))"
    by (subst prod.distinct_set_conv_list[symmetric], force, rule prod.cong, auto) 
  finally show "Gramian_determinant fs k = (\<Prod>j<k. \<parallel>gso j\<parallel>\<^sup>2)" .
  also have "\<dots> > 0" 
    by (rule prod_pos, intro ballI sq_norm_pos, insert k assms, auto)
  finally show "0 < Gramian_determinant fs k" by auto
qed

lemma Gramian_determinant_div:
  assumes "l < m"
  shows "Gramian_determinant fs (Suc l) / Gramian_determinant fs l = \<parallel>gso l\<parallel>\<^sup>2"
proof -
  note gram = Gramian_determinant(1)[symmetric]
  from assms have le: "Suc l \<le> m" "l \<le> m" by auto
  have "(\<Prod>j<Suc l. \<parallel>gso j\<parallel>\<^sup>2) = (\<Prod>j \<in> {0..<l} \<union> {l}. \<parallel>gso j\<parallel>\<^sup>2)"
    using assms by (intro prod.cong) (auto)
  also have "\<dots> = (\<Prod>j<l. \<parallel>gso j\<parallel>\<^sup>2) * \<parallel>gso l\<parallel>\<^sup>2"
    using assms by (subst prod_Un) (auto simp add: atLeast0LessThan)
  finally show ?thesis unfolding gram[OF le(1)] gram[OF le(2)]
    using Gramian_determinant(2)[OF le(2)] assms by auto 
qed

end

lemma (in gram_schmidt_fs_Rn) Gramian_determinant_Ints:
  assumes "k \<le> m" "\<And>i j. i < n \<Longrightarrow> j < m \<Longrightarrow> fs ! j $ i \<in> \<int>"
  shows "Gramian_determinant fs k \<in> \<int>"
proof -
  let ?oi = "of_int :: int \<Rightarrow> 'a" 
  from assms have "\<And> i. i < n \<Longrightarrow> \<forall>j. \<exists> c. j < m \<longrightarrow> fs ! j $ i = ?oi c" unfolding Ints_def by auto
  from choice[OF this] have "\<forall> i. \<exists> c. \<forall> j. i < n \<longrightarrow> j < m \<longrightarrow> fs ! j $ i = ?oi (c j)" by blast
  from choice[OF this] obtain c where c: "\<And> i j. i < n \<Longrightarrow> j < m \<Longrightarrow> fs ! j $ i = ?oi (c i j)" by blast
  define d where "d = map (\<lambda> j. vec n (\<lambda> i. c i j)) [0..<m]" 
  have fs: "fs = map (map_vec ?oi) d" 
    unfolding d_def by (rule nth_equalityI, auto intro!: eq_vecI c)
  have id: "mat k n (\<lambda>(i, y). map (map_vec ?oi) d ! i $ y) = map_mat of_int (mat k n (\<lambda>(i, y). d ! i $ y))" 
    by (rule eq_matI, insert \<open>k \<le> m\<close>, auto simp: d_def o_def)
  show ?thesis unfolding fs Gramian_determinant_def Gramian_matrix_def Let_def id
    map_mat_transpose
    by (subst of_int_hom.mat_hom_mult[symmetric], auto)
qed

locale gram_schmidt_fs_int = gram_schmidt_fs_lin_indpt +
  assumes fs_int: "\<And>i j. i < n \<Longrightarrow> j < m \<Longrightarrow> fs ! j $ i \<in> \<int>"
begin

lemma Gramian_determinant_ge1:
  assumes "k \<le> m"
  shows "1 \<le> Gramian_determinant fs k"
proof -
  have "0 < Gramian_determinant fs k"
    by (simp add: assms Gramian_determinant(2) less_or_eq_imp_le)
  moreover have "Gramian_determinant fs k \<in> \<int>"
    by (simp add: Gramian_determinant_Ints assms fs_int)
  ultimately show ?thesis
    using Ints_nonzero_abs_ge1 by fastforce
qed

lemma mu_bound_Gramian_determinant:
  assumes "l < k" "k < m"
  shows "(\<mu> k l)\<^sup>2 \<le> Gramian_determinant fs l * \<parallel>fs ! k\<parallel>\<^sup>2"
proof -
  have "(\<mu> k l)\<^sup>2  = (fs ! k \<bullet> gso l)\<^sup>2 / (\<parallel>gso l\<parallel>\<^sup>2)\<^sup>2"
    using assms by (simp add: power_divide \<mu>.simps)
  also have "\<dots> \<le> (\<parallel>fs ! k\<parallel>\<^sup>2 * \<parallel>gso l\<parallel>\<^sup>2) / (\<parallel>gso l\<parallel>\<^sup>2)\<^sup>2"
    using assms by (auto intro!: scalar_prod_Cauchy divide_right_mono)
  also have "\<dots> = \<parallel>fs ! k\<parallel>\<^sup>2 / \<parallel>gso l\<parallel>\<^sup>2"
    by (auto simp add: field_simps power2_eq_square)
  also have "\<dots> =  \<parallel>fs ! k\<parallel>\<^sup>2 / (Gramian_determinant fs (Suc l) / Gramian_determinant fs l)"
    using assms by (subst Gramian_determinant_div[symmetric]) auto
  also have "\<dots> =  Gramian_determinant fs l * \<parallel>fs ! k\<parallel>\<^sup>2 / Gramian_determinant fs (Suc l)"
    by (auto simp add: field_simps)
  also have "\<dots> \<le> Gramian_determinant fs l * \<parallel>fs ! k\<parallel>\<^sup>2 / 1"
    by (rule divide_left_mono, insert Gramian_determinant_ge1[of l] Gramian_determinant_ge1[of "Suc l"] assms,
    auto intro!: mult_nonneg_nonneg) 
  finally show ?thesis
    by simp
qed

end (* gram_schmidt_fs_int *)

context gram_schmidt
begin

lemma gso_cong:
  fixes f1 f2 :: "'a vec list"
  assumes "\<And> i. i \<le> x \<Longrightarrow> f1 ! i = f2 ! i"
  shows "gram_schmidt_fs.gso n f1 x = gram_schmidt_fs.gso n f2 x"
  using assms
proof(induct x rule:nat_less_induct[rule_format])
  case (1 x)
  interpret f1: gram_schmidt_fs n f1 .
  interpret f2: gram_schmidt_fs n f2 .
  have *: "map (\<lambda>j. - f1.\<mu> x j \<cdot>\<^sub>v f1.gso j) [0..<x] = map (\<lambda>j. - f2.\<mu> x j \<cdot>\<^sub>v f2.gso j) [0..<x]"
    using 1 by (intro map_cong) (auto simp add: f1.\<mu>.simps f2.\<mu>.simps)
  show ?case
    using 1 by (subst f1.gso.simps, subst f2.gso.simps, subst *) auto
qed

lemma \<mu>_cong:
  fixes f1 f2 :: "'a vec list"
  assumes "\<And> k. j < i \<Longrightarrow> k \<le> j \<Longrightarrow> f1 ! k = f2 ! k"
    and "j < i \<Longrightarrow> f1 ! i = f2 ! i" 
  shows "gram_schmidt_fs.\<mu> n f1 i j = gram_schmidt_fs.\<mu> n f2 i j"
proof -
  interpret f1: gram_schmidt_fs n f1 .
  interpret f2: gram_schmidt_fs n f2 .
  from gso_cong[of j f1 f2] assms have id: "j < i \<Longrightarrow> f1.gso j = f2.gso j" by auto
  show ?thesis unfolding f1.\<mu>.simps f2.\<mu>.simps using assms id by auto
qed

end

lemma prod_list_le_mono: fixes us :: "'a :: {linordered_nonzero_semiring,ordered_ring} list" 
  assumes "length us = length vs" 
  and "\<And> i. i < length vs \<Longrightarrow> 0 \<le> us ! i \<and> us ! i \<le> vs ! i" 
shows "0 \<le> prod_list us \<and> prod_list us \<le> prod_list vs" 
  using assms 
proof (induction us vs rule: list_induct2)
  case (Cons u us v vs)
  have "0 \<le> prod_list us \<and> prod_list us \<le> prod_list vs" 
    by (rule Cons.IH, insert Cons.prems[of "Suc i" for i], auto)
  moreover have "0 \<le> u \<and> u \<le> v" using Cons.prems[of 0] by auto
  ultimately show ?case by (auto intro: mult_mono)
qed simp

lemma lattice_of_of_int: assumes G: "set F \<subseteq> carrier_vec n" 
  and "f \<in> vec_module.lattice_of n F"     
shows "map_vec rat_of_int f \<in> vec_module.lattice_of n (map (map_vec of_int) F)" 
  (is "?f \<in> vec_module.lattice_of _ ?F")
proof -
  let ?sl = "abelian_monoid.sumlist (module_vec TYPE('a::semiring_1) n)" 
  note d = vec_module.lattice_of_def
  note dim = vec_module.sumlist_dim
  note sumlist_vec_index = vec_module.sumlist_vec_index
  from G have Gi: "\<And> i. i < length F \<Longrightarrow> F ! i \<in> carrier_vec n" by auto
  from Gi have Gid: "\<And> i. i < length F \<Longrightarrow> dim_vec (F ! i) = n" by auto
  from assms(2)[unfolded d]
  obtain c where 
    ffc: "f = ?sl (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v F ! i) [0..<length F])" (is "_ = ?g") by auto   
  have "?f = ?sl (map (\<lambda>i. of_int (c i) \<cdot>\<^sub>v ?F ! i) [0..<length ?F])" (is "_ = ?gg")
  proof -
    have d1[simp]: "dim_vec ?g = n" by (subst dim, auto simp: Gi)
    have d2[simp]: "dim_vec ?gg = n" unfolding length_map by (subst vec_module.sumlist_dim, auto simp: Gi G)
    show ?thesis
      unfolding ffc length_map
      apply (rule eq_vecI)
       apply (insert d1 d2, auto)[2]
      apply (subst (1 2) sumlist_vec_index, auto simp: o_def Gi G)
      apply (unfold of_int_hom.hom_sum_list)
      apply (intro arg_cong[of _ _ sum_list] map_cong)
        by (auto simp: G Gi, (subst index_smult_vec, simp add: Gid)+,
         subst index_map_vec, auto simp: Gid)
  qed
  thus "?f \<in> vec_module.lattice_of n ?F" unfolding d by auto
qed


(* Theorem 16.6, difficult part *)
lemma Hadamard's_inequality: 
  fixes A::"real mat"
  assumes A: "A \<in> carrier_mat n n" 
  shows  "abs (det A) \<le> sqrt (prod_list (map sq_norm (rows A)))" 
proof -
  let ?us = "map (row A) [0 ..< n]"
  interpret gso: gram_schmidt_fs n ?us .
  have len: "length ?us = n" by simp
  have us: "set ?us \<subseteq> carrier_vec n" using A by auto
  let ?vs = "map gso.gso [0..<n]" 
  show ?thesis
  proof (cases "carrier_vec n \<subseteq> gso.span (set ?us)")
    case True
    with us len have basis: "gso.basis_list ?us" unfolding gso.basis_list_def by auto
    note in_dep = gso.basis_list_imp_lin_indpt_list[OF basis]
    interpret gso: gram_schmidt_fs_lin_indpt n ?us
      by (standard) (use in_dep gso.lin_indpt_list_def in auto)
    have last: "0 \<le> prod_list (map sq_norm ?vs) \<and> prod_list (map sq_norm ?vs) \<le> prod_list (map sq_norm ?us)" 
    proof (rule prod_list_le_mono, force, unfold length_map length_upt)
      fix i
      assume "i < n - 0" 
      hence i: "i < n" by simp
      have vsi: "map sq_norm ?vs ! i = sq_norm (?vs ! i)" using i by simp
      have usi: "map sq_norm ?us ! i = sq_norm (row A i)" using i by simp
      have zero: "0 \<le> sq_norm (?vs ! i)" by auto
      have le: "sq_norm (?vs ! i) \<le> sq_norm (row A i)"
        using gso.sq_norm_gso_le_f i by simp
      show "0 \<le> map sq_norm ?vs ! i \<and> map sq_norm ?vs ! i \<le> map sq_norm ?us ! i" 
        unfolding vsi usi using zero le by auto
    qed
    have Fs: "gso.FF \<in> carrier_mat n n" by auto
    have A_Fs: "A = gso.FF" 
      by (rule eq_matI, subst gso.FF_index, insert A, auto)
    hence "abs (det A) = abs (det (gso.FF))" by simp
    (* the following three steps are based on a discussion with Bertram Felgenhauer *)
    also have "\<dots> = abs (sqrt (det (gso.FF) * det (gso.FF)))" by simp
    also have "det (gso.FF) * det (gso.FF) = det (gso.FF) * det (gso.FF)\<^sup>T" 
      unfolding det_transpose[OF Fs] ..
    also have "\<dots> = det (gso.FF * (gso.FF)\<^sup>T)" 
      by (subst det_mult[OF Fs], insert Fs, auto)
    also have "\<dots> = gso.Gramian_determinant ?us n" 
      unfolding gso.Gramian_matrix_def gso.Gramian_determinant_def Let_def A_Fs[symmetric]
      by (rule arg_cong[of _ _ det], rule arg_cong2[of _ _ _ _ "(*)"], insert A, auto)
    also have "\<dots> = (\<Prod>j \<in> set [0 ..< n]. \<parallel>?vs ! j\<parallel>\<^sup>2)"
      by (subst gso.Gramian_determinant) (auto intro!: prod.cong)
    also have "\<dots> = prod_list (map (\<lambda> i. sq_norm (?vs ! i)) [0 ..< n])"
      by (subst prod.distinct_set_conv_list, auto)
    also have "map (\<lambda> i. sq_norm (?vs ! i)) [0 ..< n] = map sq_norm ?vs" 
      by (intro nth_equalityI, auto)
    also have "abs (sqrt (prod_list \<dots>)) \<le> sqrt (prod_list (map sq_norm ?us))" 
      using last by simp
    also have "?us = rows A" unfolding rows_def using A by simp
    finally show ?thesis .
  next
    case False
    from mat_of_rows_rows[unfolded rows_def,of A] A gram_schmidt.non_span_det_zero[OF len False us]
    have zero: "det A = 0" by auto
    have ge: "prod_list (map sq_norm (rows A)) \<ge> 0" 
      by (rule prod_list_nonneg, auto simp: sq_norm_vec_ge_0)
    show ?thesis unfolding zero using ge by simp
  qed
qed


definition "gram_schmidt_wit = gram_schmidt.main" 

declare gram_schmidt.adjuster_wit.simps[code]
declare gram_schmidt.sub2_wit.simps[code]
declare gram_schmidt.main_def[code]
      
definition gram_schmidt_int :: "nat \<Rightarrow> int vec list \<Rightarrow> rat list list \<times> rat vec list" where
  "gram_schmidt_int n us = gram_schmidt_wit n (map (map_vec of_int) us)" 

lemma snd_gram_schmidt_int : "snd (gram_schmidt_int n us) = gram_schmidt n (map (map_vec of_int) us)"
  unfolding gram_schmidt_int_def gram_schmidt_wit_def gram_schmidt_fs.gso_connect by metis

text \<open>Faster implementation for rational vectors which also avoid recomputations
  of square-norms\<close>

fun adjuster_triv :: "nat \<Rightarrow> rat vec \<Rightarrow> (rat vec \<times> rat) list \<Rightarrow> rat vec"
  where "adjuster_triv n w [] = 0\<^sub>v n"
    |  "adjuster_triv n w ((u,nu)#us) = -(w \<bullet> u)/ nu \<cdot>\<^sub>v u + adjuster_triv n w us"

fun gram_schmidt_sub_triv
  where "gram_schmidt_sub_triv n us [] = us"
  | "gram_schmidt_sub_triv n us (w # ws) = (let u = adjuster_triv n w us + w in
     gram_schmidt_sub_triv n ((u, sq_norm_vec_rat u) # us) ws)"

definition gram_schmidt_triv :: "nat \<Rightarrow> rat vec list \<Rightarrow> (rat vec \<times> rat) list"
  where "gram_schmidt_triv n ws = rev (gram_schmidt_sub_triv n [] ws)"

lemma adjuster_triv: "adjuster_triv n w (map (\<lambda> x. (x,sq_norm x)) us) = adjuster n w us" 
  by (induct us, auto simp: sq_norm_vec_as_cscalar_prod) 

lemma gram_schmidt_sub_triv: "gram_schmidt_sub_triv n ((map (\<lambda> x. (x,sq_norm x)) us)) ws = 
  map (\<lambda> x. (x, sq_norm x)) (gram_schmidt_sub n us ws)" 
  by (rule sym, induct ws arbitrary: us, auto simp: adjuster_triv o_def Let_def)

lemma gram_schmidt_triv[simp]: "gram_schmidt_triv n ws = map (\<lambda> x. (x,sq_norm x)) (gram_schmidt n ws)" 
  unfolding gram_schmidt_def gram_schmidt_triv_def rev_map[symmetric] 
  by (auto simp: gram_schmidt_sub_triv[symmetric])

context gram_schmidt
begin

fun mus_adjuster :: "'a vec \<Rightarrow> ('a vec \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a vec \<Rightarrow> 'a list \<times> 'a vec"
  where
  "mus_adjuster f []           mus g' = (mus, g')" |
  "mus_adjuster f ((g, ng)#n_gs) mus g' = (let a = (f \<bullet> g) / ng in
                                             mus_adjuster f n_gs (a # mus) (-a \<cdot>\<^sub>v g + g'))"

fun norms_mus' where
  "norms_mus' []       n_gs mus = (map snd n_gs, mus)" |
  "norms_mus' (f # fs) n_gs mus =
    (let (mus_row, g') = mus_adjuster f n_gs [] (0\<^sub>v n);
                     g = g' + f in
      norms_mus' fs ((g, sq_norm_vec g) # n_gs) (mus_row#mus))"

lemma adjuster_wit_carrier_vec:
  assumes "f \<in> carrier_vec n" "set gs \<subseteq> carrier_vec n"
  shows "snd (adjuster_wit mus f gs) \<in> carrier_vec n"
  using assms
  by (induction mus f gs rule: adjuster_wit.induct) (auto simp add: Let_def case_prod_beta')

lemma adjuster_wit'':
  assumes "adjuster_wit mus_acc f gs = (mus, g')" "n_gs = map (\<lambda>x. (x, sq_norm_vec x)) gs"
 "f \<in> carrier_vec n" "acc \<in> carrier_vec n" "set gs \<subseteq> carrier_vec n"
  shows "mus_adjuster f n_gs mus_acc acc = (mus, acc + g')"
  using assms proof(induction f n_gs mus_acc acc arbitrary: g' gs mus rule: mus_adjuster.induct)
  case (1 mus' f acc g)
  then show ?case
    by auto
next
  case (2 f g n_g n_gs mus_acc acc g' gs mus)
  let ?gg = "snd (adjuster_wit (f \<bullet> g / n_g # mus_acc) f (tl gs))"
  from 2 have l: "gs = g # tl gs"
    by auto
  have gg: "?gg \<in> carrier_vec n"
    using 2 by (auto intro!: adjuster_wit_carrier_vec)
  then have [simp]: "g' = (- (f \<bullet> g / \<parallel>g\<parallel>\<^sup>2) \<cdot>\<^sub>v g + ?gg)"
    using 2 by (auto simp add: Let_def case_prod_beta')
  have "mus_adjuster f ((g, n_g) # n_gs) mus_acc acc =
        mus_adjuster f n_gs (f \<bullet> g / n_g # mus_acc) (- (f \<bullet> g / n_g) \<cdot>\<^sub>v g + acc)"
    by (auto simp add: Let_def)
  also have "\<dots> = (mus, - (f \<bullet> g / n_g) \<cdot>\<^sub>v g + acc + ?gg)"
  proof -
    have "adjuster_wit (f \<bullet> g / n_g # mus_acc) f (tl gs) = (mus, ?gg)"
      using 2 by (subst (asm) l) (auto simp add: Let_def case_prod_beta')
    then show ?thesis
      using 2 by (subst 2(1)[of _ "tl gs"]) (auto simp add: Let_def case_prod_beta')
  qed
  finally show ?case
    using 2 gg by auto
qed

lemma adjuster_wit':
  assumes "n_gs = map (\<lambda>x. (x, sq_norm_vec x)) gs" "f \<in> carrier_vec n" "set gs \<subseteq> carrier_vec n"
  shows "mus_adjuster f n_gs mus_acc (0\<^sub>v n) = adjuster_wit mus_acc f gs"
proof -
  let ?g = "snd (adjuster_wit mus_acc f gs)"
  let ?mus = "fst (adjuster_wit mus_acc f gs)"
  have "?g \<in> carrier_vec n"
    using assms by (auto intro!: adjuster_wit_carrier_vec)
  then show ?thesis
    using assms by (subst adjuster_wit''[of _ _ gs ?mus ?g]) (auto simp add: case_prod_beta')
qed

lemma sub2_wit_norms_mus':
  assumes "n_gs' = map (\<lambda>v. (v, sq_norm_vec v)) gs'"
   "sub2_wit gs' fs = (mus, gs)" "set fs \<subseteq> carrier_vec n" "set gs' \<subseteq> carrier_vec n"
 shows "norms_mus' fs n_gs' mus_acc = (map sq_norm_vec (rev gs @ gs'), rev mus @ mus_acc)"
  using assms proof (induction fs n_gs' mus_acc arbitrary: gs' mus gs rule: norms_mus'.induct)
  case (1 n_gs mus_acc)
  then show ?case by (auto simp add: rev_map)
next
  case (2  f fs n_gs mus_acc)
  note aw1 = conjunct1[OF conjunct2[OF gram_schmidt_fs.adjuster_wit]]
  let ?aw = "mus_adjuster f n_gs [] (0\<^sub>v n)"
  have aw: "?aw = adjuster_wit [] f gs'"
    apply(subst adjuster_wit') using 2 by auto
  have "sub2_wit ((snd ?aw + f) # gs') fs = sub2_wit ((snd (adjuster_wit [] f gs') + f) # gs') fs"
    apply(subst adjuster_wit') using 2 by auto
  also have "\<dots> = (tl mus, tl gs)"
    using 2 by (auto simp add: Let_def case_prod_beta')
  finally have sub_tl: "sub2_wit ((snd ?aw + f) # gs') fs = (tl mus, tl gs)"
    by simp
  have aw_c: "snd ?aw \<in> carrier_vec n"
    apply(subst adjuster_wit'[of _ gs'])
     using 2 adjuster_wit_carrier_vec by (auto)
  have gs: "gs = (snd ?aw + f) # tl gs"
    apply(subst aw) using 2 by (auto simp add: Let_def case_prod_beta')
  have mus: "mus = fst ?aw # tl mus"
    apply(subst aw) using 2 by (auto simp add: Let_def case_prod_beta')
  show ?case apply(simp add: Let_def case_prod_beta')
    apply(subst 2(1)[of _ _ _ _ "(snd ?aw + f)#gs'"  "tl mus" "tl gs"]) apply(simp) defer apply(simp)
         apply (simp add: "2.prems"(1))
    using sub_tl apply(simp)
    using 2 apply(simp)
    subgoal using 2 aw_c by (auto)
     defer
     apply(simp)
    apply(auto)
    using gs 
     apply(subst gs) apply(subst (2) gs)
     apply (metis list.simps(9) rev.simps(2) rev_map)
    using mus
    by (metis rev.simps(2))
qed

lemma sub2_wit_gram_schmidt_sub_triv'':
  assumes "sub2_wit [] fs = (mus, gs)" "set fs \<subseteq> carrier_vec n"
  shows "norms_mus' fs [] [] = (map sq_norm_vec (rev gs), rev mus)"
  using assms by (subst sub2_wit_norms_mus') (simp)+

definition norms_mus where
  "norms_mus fs = (let (n_gs, mus) = norms_mus' fs [] [] in (rev n_gs, rev mus))"

lemma sub2_wit_gram_schmidt_norm_mus:
  assumes "sub2_wit [] fs = (mus, gs)" "set fs \<subseteq> carrier_vec n"
  shows "norms_mus fs = (map sq_norm_vec gs, mus)"
  unfolding norms_mus_def using assms sub2_wit_gram_schmidt_sub_triv''
  by (auto simp add: Let_def case_prod_beta' rev_map)

lemma (in gram_schmidt_fs_Rn) norms_mus: assumes "set fs \<subseteq> carrier_vec n" "length fs \<le> n"
  shows "norms_mus fs = (map (\<lambda>j. \<parallel>gso j\<parallel>\<^sup>2) [0..<length fs], map (\<lambda>i. map (\<mu> i) [0..<i]) [0..<length fs])" 
proof -
  let ?s = "sub2_wit [] fs"
  have "gram_schmidt_sub2 n [] fs = snd ?s \<and> snd ?s = map (gso) [0..<length fs] \<and> fst ?s = map (\<lambda>i. map (\<mu> i) [0..<i]) [0..<length fs]"
    using assms by (intro sub2_wit) (auto simp add: map_nth)
  then have 1: "snd ?s = map (gso) [0..<length fs]" and 2: "fst ?s = map (\<lambda>i. map (\<mu> i) [0..<i]) [0..<length fs]" 
    by auto
  have s: "?s = (fst ?s, snd ?s)" by auto
  show ?thesis
    unfolding sub2_wit_gram_schmidt_norm_mus[OF s assms(1)]
    unfolding 1 2 o_def map_map by auto
qed

end

fun mus_adjuster_rat :: "rat vec \<Rightarrow> (rat vec \<times> rat) list \<Rightarrow> rat list \<Rightarrow> rat vec \<Rightarrow> rat list \<times> rat vec"
  where
  "mus_adjuster_rat f []           mus g' = (mus, g')" |
  "mus_adjuster_rat f ((g, ng)#n_gs) mus g' = (let a = (f \<bullet> g) / ng in
                                             mus_adjuster_rat f n_gs (a # mus) (-a \<cdot>\<^sub>v g + g'))"

fun norms_mus_rat' where
  "norms_mus_rat' n []       n_gs mus = (map snd n_gs, mus)" |
  "norms_mus_rat' n (f # fs) n_gs mus =
    (let (mus_row, g') = mus_adjuster_rat f n_gs [] (0\<^sub>v n);
                     g = g' + f in
      norms_mus_rat' n fs ((g, sq_norm_vec g) # n_gs) (mus_row#mus))"

definition norms_mus_rat where
  "norms_mus_rat n fs = (let (n_gs, mus) = norms_mus_rat' n fs [] [] in (rev n_gs, rev mus))"

lemma norms_mus_rat_norms_mus:
  "norms_mus_rat n fs = gram_schmidt.norms_mus n fs"
proof -
  have "mus_adjuster_rat f n_gs mus_acc g_acc = gram_schmidt.mus_adjuster f n_gs mus_acc g_acc"
    for f n_gs mus_acc g_acc
    by(induction f n_gs mus_acc g_acc rule: mus_adjuster_rat.induct)
      (auto simp add: gram_schmidt.mus_adjuster.simps)
  then have "norms_mus_rat' n fs n_gs mus = gram_schmidt.norms_mus' n fs n_gs mus" for n fs n_gs mus
    by(induction n fs n_gs mus rule: norms_mus_rat'.induct)
      (auto simp add: gram_schmidt.norms_mus'.simps case_prod_beta')
  then show ?thesis
    unfolding norms_mus_rat_def gram_schmidt.norms_mus_def by auto
qed

lemma of_int_dvd:
  "b dvd a" if "of_int a / (of_int b :: 'a :: field_char_0) \<in> \<int>" "b \<noteq> 0"
  using that by (cases rule: Ints_cases)
    (simp add: field_simps flip: of_int_mult)

lemma denom_dvd_ints:
  fixes i::int
  assumes "quotient_of r = (z, n)" "of_int i * r \<in> \<int>"
  shows "n dvd i"
proof -
  have "rat_of_int i * (rat_of_int z / rat_of_int n) \<in> \<int>"
    using assms quotient_of_div by blast
  then have "n dvd i * z"
    using quotient_of_denom_pos assms by (auto intro!: of_int_dvd)
  then show "n dvd i"
    using assms algebraic_semidom_class.coprime_commute 
      quotient_of_coprime coprime_dvd_mult_left_iff by blast
qed

lemma quotient_of_bounds: 
  assumes "quotient_of r = (n, d)" "rat_of_int i * r \<in> \<int>" "0 < i" "\<bar>r\<bar> \<le> b"
  shows "of_int \<bar>n\<bar> \<le> of_int i * b" "d \<le> i" 
proof -
  show ni: "d \<le> i"
    using assms denom_dvd_ints  by (intro zdvd_imp_le) blast+
  have "\<bar>r\<bar> = \<bar>rat_of_int n / rat_of_int d\<bar>"
    using assms quotient_of_div by blast
  also have "\<dots> = rat_of_int \<bar>n\<bar> / rat_of_int d"
    using assms using quotient_of_denom_pos by force
  finally have "of_int \<bar>n\<bar> = rat_of_int d * \<bar>r\<bar>"
    using assms by auto
  also have "\<dots> \<le> rat_of_int d * b"
    using assms quotient_of_denom_pos by auto
  also have "\<dots> \<le> rat_of_int i * b"
    using ni assms of_int_le_iff by (auto intro!: mult_right_mono)
  finally show "rat_of_int \<bar>n\<bar> \<le> rat_of_int i * b" 
    by simp
qed

context gram_schmidt_fs_Rn
begin

(* Lemma 16.17 *) 

lemma ex_\<kappa>:
  assumes "i < length fs" "l \<le> i"
  shows "\<exists>\<kappa>. sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0 ..< l]) =
             sumlist (map (\<lambda>j. \<kappa> j \<cdot>\<^sub>v fs ! j) [0 ..< l])" (is "\<exists>\<kappa>. ?Prop l i \<kappa>")
  using assms 
proof (induction l arbitrary: i)
  case (Suc l)
  then obtain \<kappa>\<^sub>i where \<kappa>\<^sub>i_def: "?Prop l i \<kappa>\<^sub>i"
    by force
  from Suc obtain \<kappa>\<^sub>l where \<kappa>\<^sub>l_def: "?Prop l l \<kappa>\<^sub>l"
    by force
  have [simp]: "dim_vec (M.sumlist (map (\<lambda>j. f j \<cdot>\<^sub>v fs ! j) [0..<y])) = n" if "y \<le> Suc l" for f y
    using Suc that by (auto intro!: dim_sumlist)
  define \<kappa> where "\<kappa> = (\<lambda>x. (if x < l then \<kappa>\<^sub>i x - \<kappa>\<^sub>l x * \<mu> i l else  - \<mu> i l))"
  let ?sum = "\<lambda>i. sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l])"
  have "M.sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<Suc l]) = 
        M.sumlist (map (\<lambda>j. \<kappa>\<^sub>i j \<cdot>\<^sub>v fs ! j) [0..<l]) + - \<mu> i l \<cdot>\<^sub>v gso l"
    using Suc by (subst \<kappa>\<^sub>i_def[symmetric], subst sumlist_snoc[symmetric]) (auto)
  also have "gso l = fs ! l + M.sumlist (map (\<lambda>j. \<kappa>\<^sub>l j \<cdot>\<^sub>v fs ! j) [0..<l])"
    by (subst gso.simps) (auto simp add: \<kappa>\<^sub>l_def)
  also have "M.sumlist (map (\<lambda>j. \<kappa>\<^sub>i j \<cdot>\<^sub>v fs ! j) [0..<l]) +
             - \<mu> i l \<cdot>\<^sub>v (fs ! l + M.sumlist (map (\<lambda>j. \<kappa>\<^sub>l j \<cdot>\<^sub>v fs ! j) [0..<l]))
             = M.sumlist (map (\<lambda>j. \<kappa> j \<cdot>\<^sub>v fs ! j) [0..<Suc l])" (is "?lhs = ?rhs")
  proof -
    have "?lhs $ k = ?rhs $ k" if "k < n" for k
    proof -
      have "(M.sumlist (map (\<lambda>j. \<kappa>\<^sub>i j \<cdot>\<^sub>v fs ! j) [0..<l]) + 
                - \<mu> i l \<cdot>\<^sub>v (fs ! l + M.sumlist (map (\<lambda>j. \<kappa>\<^sub>l j \<cdot>\<^sub>v fs ! j) [0..<l]))) $ k
          = (M.sumlist (map (\<lambda>j. \<kappa>\<^sub>i j \<cdot>\<^sub>v fs ! j) [0..<l]) $ k + 
                - \<mu> i l * (fs ! l $ k + M.sumlist (map (\<lambda>j. \<kappa>\<^sub>l j \<cdot>\<^sub>v fs ! j) [0..<l]) $ k))"
        using that by auto
      also have "\<dots> = (\<Sum>j = 0..<l. \<kappa>\<^sub>i j * fs ! j $ k) 
                 + (- \<mu> i l * (\<Sum>j = 0..<l. \<kappa>\<^sub>l j * fs ! j $ k)) - \<mu> i l * fs ! l $ k"
        using that Suc by (auto simp add: algebra_simps sumlist_nth)
      also have "- \<mu> i l * (\<Sum>j = 0..<l. \<kappa>\<^sub>l j * fs ! j $ k) 
               = (\<Sum>j = 0..<l. - \<mu> i l * (\<kappa>\<^sub>l j * fs ! j $ k))"
        using sum_distrib_left by blast
      also have "(\<Sum>j = 0..<l. \<kappa>\<^sub>i j * fs ! j $ k) + (\<Sum>j = 0..<l. - \<mu> i l * (\<kappa>\<^sub>l j * fs ! j $ k)) =
               (\<Sum>x = 0..<l. (\<kappa>\<^sub>i x - \<kappa>\<^sub>l x * \<mu> i l) * fs ! x $ k)"
        by (subst sum.distrib[symmetric]) (simp add: algebra_simps)
      also have "\<dots> = (\<Sum>x = 0..<l. \<kappa> x * fs ! x $ k)"
        unfolding \<kappa>_def by (rule sum.cong) (auto)
      also have "(\<Sum>x = 0..<l. \<kappa> x * fs ! x $ k) - \<mu> i l * fs ! l $ k =
                 (\<Sum>x = 0..<l. \<kappa> x * fs ! x $ k) + (\<Sum>x = l..<Suc l. \<kappa> x * fs ! x $ k)"
        unfolding \<kappa>_def by auto
      also have "\<dots> = (\<Sum>x = 0..<Suc l. \<kappa> x * fs ! x $ k)"
        by (subst sum.union_disjoint[symmetric]) auto
      also have "\<dots> = (\<Sum>x = 0..<Suc l. (\<kappa> x \<cdot>\<^sub>v fs ! x) $ k)"
        using that Suc by auto
      also have "\<dots> = M.sumlist (map (\<lambda>j. \<kappa> j \<cdot>\<^sub>v fs ! j) [0..<Suc l]) $ k"
        by (subst sumlist_nth, insert that Suc, auto simp: nth_append)
      finally show ?thesis by simp
    qed
    then show ?thesis
      using Suc by (auto simp add: dim_sumlist)
  qed
  finally show ?case by (intro exI[of _ \<kappa>]) simp
qed auto


definition \<kappa>_SOME_def:
  "\<kappa> = (SOME \<kappa>. \<forall>i l. i < length fs \<longrightarrow> l \<le> i \<longrightarrow>
        sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]) =
        sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]))"

lemma \<kappa>_def:
  assumes "i < length fs" "l \<le> i"
  shows "sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]) =
         sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])"
proof -
  let ?P = "\<lambda> i l \<kappa>. (i < length fs \<longrightarrow> l \<le> i \<longrightarrow>
                  sumlist (map (\<lambda>j. - \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]) =
                  sumlist (map (\<lambda>j. \<kappa> j \<cdot>\<^sub>v fs ! j) [0..<l]))" 
  from ex_\<kappa> have "\<And> i. \<forall> l. \<exists>\<kappa>. ?P i l \<kappa>" by blast
  from choice[OF this] have "\<forall>i. \<exists>\<kappa>. \<forall> l. ?P i l (\<kappa> l)" by blast
  from choice[OF this] have "\<exists>\<kappa>. \<forall>i l. ?P i l (\<kappa> i l)" by blast
  from someI_ex[OF this] show ?thesis
    unfolding \<kappa>_SOME_def using assms by blast
qed

lemma (in gram_schmidt_fs_lin_indpt) fs_i_sumlist_\<kappa>:
  assumes "i < m" "l \<le> i" "j < l"
  shows "(fs ! i + sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])) \<bullet> fs ! j = 0"
proof -
  have "fs ! i + sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])
        = fs ! i - M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<l])"
    using assms gso_carrier assms 
    by (subst \<kappa>_def[symmetric]) (auto simp add: dim_sumlist sumlist_nth sum_negf)
  also have "\<dots> = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
  proof -
    have "fs ! i = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<Suc i])"
      using assms by (intro fi_is_sum_of_mu_gso) auto
    also have "\<dots> = M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [0..<l]) +
                  M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
    proof -
      have *: "[0..<Suc i] = [0..<l] @ [l..<Suc i]"
        using assms by (metis diff_zero le_imp_less_Suc length_upt list_trisect upt_conv_Cons)
      show ?thesis
        by (subst *, subst map_append, subst sumlist_append) (use gso_carrier assms in auto)
    qed
    finally show ?thesis
      using assms gso_carrier assms by (auto simp add: algebra_simps dim_sumlist)
  qed
  finally have "fs ! i + M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) =
                M.sumlist (map (\<lambda>j. \<mu> i j \<cdot>\<^sub>v gso j) [l..<Suc i])"
    by simp
  moreover have "\<dots> \<bullet> (fs ! j) = 0"
    using assms gso_carrier assms unfolding lin_indpt_list_def
    by (subst scalar_prod_left_sum_distrib)
       (auto simp add: algebra_simps dim_sumlist gso_scalar_zero intro!: sum_list_zero)
  ultimately show ?thesis using assms by auto
qed


end (* gram_schmidt_fs_Rn *)

lemma Ints_sum:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>"
  shows "sum f A \<in> \<int>"
  using assms by (induction A rule: infinite_finite_induct) auto

lemma Ints_prod:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<in> \<int>"
  shows "prod f A \<in> \<int>"
using assms by (induction A rule: infinite_finite_induct) auto

lemma Ints_scalar_prod: 
  "v \<in> carrier_vec n \<Longrightarrow> w \<in> carrier_vec n
   \<Longrightarrow> (\<And> i. i < n \<Longrightarrow> v $ i \<in> \<int>) \<Longrightarrow> (\<And> i. i < n \<Longrightarrow> w $ i \<in> \<int>) \<Longrightarrow> v \<bullet> w \<in> \<int>" 
  unfolding scalar_prod_def by (intro Ints_sum Ints_mult, auto)

lemma Ints_det: assumes "\<And> i j. i < dim_row A \<Longrightarrow> j < dim_col A 
  \<Longrightarrow> A $$ (i,j) \<in> \<int>"
  shows "det A \<in> \<int>" 
proof (cases "dim_row A = dim_col A")
  case True
  show ?thesis unfolding Determinant.det_def using True assms
    by (auto intro!: Ints_sum Ints_mult Ints_prod simp: signof_def)
next
  case False
  show ?thesis unfolding Determinant.det_def using False by simp
qed


lemma (in gram_schmidt_fs_Rn) Gramian_matrix_alt_alt_def:
  assumes "k \<le> m"
  shows "Gramian_matrix fs k = mat k k (\<lambda>(i,j). fs ! i \<bullet> fs ! j)"
proof -
  have *: "vec n (($) (fs ! i)) = fs ! i" if "i < m" for i
    using that by auto
  then show ?thesis
    unfolding Gramian_matrix_def using assms
    by (intro eq_matI) (auto simp add: Let_def)
qed

lemma (in gram_schmidt_fs_int) fs_scalar_Ints:
  assumes "i < m" "j < m"
  shows "fs ! i \<bullet> fs ! j \<in> \<int>"
  by (rule Ints_scalar_prod[of _ n], insert fs_int assms, auto)

abbreviation (in gram_schmidt_fs_lin_indpt) d where "d \<equiv> Gramian_determinant fs" 


lemma (in gram_schmidt_fs_lin_indpt) fs_i_fs_j_sum_\<kappa> :
  assumes "i < m" "l \<le> i" "j < l"
  shows "- (fs ! i \<bullet> fs ! j) = (\<Sum>t = 0..<l. fs ! t \<bullet> fs ! j * \<kappa> i l t)"
proof -
  have [simp]: "M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) \<in> carrier_vec n"
    using assms by (auto intro!: sumlist_carrier simp add: dim_sumlist)
  have "0  = (fs ! i + M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l])) \<bullet> fs ! j"
    using fs_i_sumlist_\<kappa> assms by simp
  also have "\<dots> = fs ! i \<bullet> fs ! j + M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) \<bullet> fs ! j"
    using assms by (subst add_scalar_prod_distrib[of _ n]) (auto)
  also have "M.sumlist (map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]) \<bullet> fs ! j =
             (\<Sum>v\<leftarrow>map (\<lambda>j. \<kappa> i l j \<cdot>\<^sub>v fs ! j) [0..<l]. v \<bullet> fs ! j)"
    using assms by (intro scalar_prod_left_sum_distrib) (auto)
  also have "\<dots> = (\<Sum>t\<leftarrow>[0..<l]. (\<kappa> i l t \<cdot>\<^sub>v fs ! t) \<bullet> fs ! j)"
    by (rule arg_cong[where f=sum_list]) (auto)
  also have "\<dots> =  (\<Sum>t = 0..<l. (\<kappa> i l t \<cdot>\<^sub>v fs ! t) \<bullet> fs ! j) "
    by (subst interv_sum_list_conv_sum_set_nat) (auto)
  also have "\<dots> = (\<Sum>t = 0..<l. fs ! t \<bullet> fs ! j * \<kappa> i l t)"
    using assms by (intro sum.cong) auto
  finally show ?thesis by (simp add: field_simps)
qed

lemma (in gram_schmidt_fs_lin_indpt) Gramian_matrix_times_\<kappa> :
  assumes "i < m" "l \<le> i"
  shows "Gramian_matrix fs l *\<^sub>v (vec l (\<lambda>t. \<kappa> i l t)) = (vec l (\<lambda>j. - (fs ! i \<bullet> fs ! j)))"
proof -
  have "- (fs ! i \<bullet> fs ! j) = (\<Sum>t = 0..<l. fs ! t \<bullet> fs ! j * \<kappa> i l t)" if "j < l" for j
    using fs_i_fs_j_sum_\<kappa> assms that by simp
  then show ?thesis using assms
    by (subst Gramian_matrix_alt_alt_def) (auto simp add: scalar_prod_def algebra_simps)
qed

lemma (in gram_schmidt_fs_int) d_\<kappa>_Ints :
  assumes "i < m" "l \<le> i" "t < l"
  shows "d l * \<kappa> i l t \<in> \<int>"
proof -
  let ?A = "Gramian_matrix fs l"
  let ?B = "replace_col ?A (Gramian_matrix fs l *\<^sub>v vec l (\<kappa> i l)) t" 
  have deteq: "d l = det ?A"
    unfolding Gramian_determinant_def
    using Gramian_determinant_Ints
    by auto

  have **: "Gramian_matrix fs l \<in> carrier_mat l l" unfolding Gramian_matrix_def Let_def  using fs_carrier by auto
      
  then have " \<kappa> i l t * det ?A = det ?B"
    using assms fs_carrier cramer_lemma_mat[of ?A l " (vec l (\<lambda>t. \<kappa> i l t))" t]
    by auto

  also have " ... \<in> \<int> "
  proof -
    have *: "t<l \<Longrightarrow> (?A *\<^sub>v vec l (\<kappa> i l)) $ t \<in> \<int>" for t
      using assms
      apply(subst Gramian_matrix_times_\<kappa>, force, force)
      using fs_int fs_carrier
      by (auto intro!: fs_scalar_Ints Ints_minus)

    define B where "B = ?B"

    have Bint: "t1<l \<longrightarrow> s1 < l \<longrightarrow> B $$ (t1,s1) \<in> \<int>" for t1 s1
    proof (cases "s1 = t")
      case True
      from * ** this show ?thesis 
        unfolding replace_col_def B_def
        by auto
    next
      case False
      from * ** Gramian_matrix_def this fs_carrier assms show ?thesis
        unfolding replace_col_def B_def
        by (auto simp: Gramian_matrix_def Let_def scalar_prod_def intro!: Ints_sum Ints_mult fs_int)
    qed
    have B: "B \<in> carrier_mat l l"
      using ** replace_col_def unfolding B_def
      by (auto simp: replace_col_def)
    have "det B \<in> \<int>"
      using B Bint assms  det_col[of B l]
      by (auto intro!: Ints_sum Ints_mult Ints_prod simp: signof_def)
    thus ?thesis unfolding B_def.
  qed
  finally show ?thesis using deteq by (auto simp add: algebra_simps)
qed

lemma (in gram_schmidt_fs_int) d_gso_Ints:
  assumes "i < n" "k < m"
  shows "(d k \<cdot>\<^sub>v (gso k)) $ i \<in> \<int>"
proof -
  note d_\<kappa>_Ints[intro!]
  then have "(d k * \<kappa> k k j) * fs ! j $ i \<in> \<int>" if "j < k" for j
    using that fs_int assms by (auto intro: Ints_mult )
  moreover have "(d k * \<kappa> k k j) * fs ! j $ i = d k * \<kappa> k k j * fs ! j $ i" for j
    by (auto simp add: field_simps)
  ultimately have "d k * (\<Sum>j = 0..<k. \<kappa> k k j * fs ! j $ i) \<in> \<int>"
     by (subst sum_distrib_left) (auto simp add: field_simps intro!: Ints_sum)
  moreover have "(gso k) $ i = fs ! k $ i + sum (\<lambda>j. (\<kappa> k k j \<cdot>\<^sub>v fs ! j) $ i) {0..<k}"
  proof -
    have " i < dim_vec (M.sumlist (map (\<lambda>j. \<kappa> k k j \<cdot>\<^sub>v fs ! j) [0..<k]))"
      using assms by (subst sumlist_dim) auto
    then show ?thesis
      using assms by (subst gso.simps) (auto simp add: sumlist_nth sumlist_dim \<kappa>_def)
  qed
  ultimately show ?thesis
    using assms
    by (auto simp add: distrib_left Gramian_determinant_Ints fs_int intro!: Ints_mult Ints_add)
qed

lemma (in gram_schmidt_fs_int) d_mu_Ints:
  assumes "l \<le> k" "k < m"
  shows "d (Suc l) * \<mu> k l \<in> \<int>"
proof (cases "l < k")
  case True
  have ll: "d l * gso l $ i = (d l \<cdot>\<^sub>v gso l) $ i" if "i < n" for i
    using that assms by auto
  have "d (Suc l) * \<mu> k l =d (Suc l) * (fs ! k \<bullet> gso l) / \<parallel>gso l\<parallel>\<^sup>2 "
    using assms True unfolding \<mu>.simps by simp
  also have "\<dots> = fs ! k \<bullet> (d l \<cdot>\<^sub>v gso l)"
    using assms Gramian_determinant(2)[of "Suc l"]
    by (subst Gramian_determinant_div[symmetric]) (auto)
  also have "\<dots> \<in> \<int>"
  proof -
    have "d l * gso l $ i \<in> \<int>" if "i < n" for i
      using assms d_gso_Ints that ll by (simp)
    then show ?thesis
      using assms by (auto intro!: Ints_sum simp add: fs_int scalar_prod_def)
 qed
 finally show ?thesis
   by simp
next
  case False
  with assms have l: "l = k" by auto
  show ?thesis unfolding l \<mu>.simps using Gramian_determinant_Ints fs_int assms by simp
qed


lemma max_list_Max: "ls \<noteq> [] \<Longrightarrow> max_list ls = Max (set ls)"
  by (induction ls) (auto simp add: max_list_Cons)

subsection \<open>Explicit Bounds for Size of Numbers that Occur During GSO Algorithm \<close>

context gram_schmidt_fs_lin_indpt
begin

definition "N = Max (sq_norm ` set fs)"



lemma N_ge_0:
  assumes "0 < m"
  shows "0 \<le> N"
proof -
  have "x \<in> sq_norm ` set fs \<Longrightarrow> 0 \<le> x" for x
    by auto
  then show ?thesis
  using assms unfolding N_def by auto
qed

lemma N_fs:
  assumes "i < m"
  shows "\<parallel>fs ! i\<parallel>\<^sup>2 \<le> N"
    using assms unfolding N_def by (auto)

lemma N_gso:
  assumes "i < m"
  shows "\<parallel>gso i\<parallel>\<^sup>2 \<le> N"
  using assms N_fs sq_norm_gso_le_f by fastforce

lemma N_d:
  assumes "i \<le> m"
  shows "Gramian_determinant fs i \<le> N ^ i"
proof -
  have "(\<Prod>j<i. \<parallel>gso j\<parallel>\<^sup>2) \<le> (\<Prod>j<i. N)"
      using assms N_gso by (intro prod_mono) auto
    then show ?thesis
      using assms Gramian_determinant by auto
  qed


end

lemma ex_MAXIMUM: assumes "finite A" "A \<noteq> {}"
  shows "\<exists>a \<in> A. Max (f ` A) = f a"
proof -
  have "Max (f ` A) \<in> f ` A"
    using assms by (auto intro!: Max_in)
  then show ?thesis
    using assms imageE by blast
qed

context gram_schmidt_fs_int
begin

lemma fs_int': "k < n \<Longrightarrow> f \<in> set fs \<Longrightarrow> f $ k \<in> \<int>"
  by (metis fs_int in_set_conv_nth)

lemma
  assumes "i < m"
  shows fs_sq_norm_Ints: "\<parallel>fs ! i\<parallel>\<^sup>2 \<in> \<int>" and fs_sq_norm_ge_1: "1 \<le> \<parallel>fs ! i\<parallel>\<^sup>2"
proof -
  show fs_Ints: "\<parallel>fs ! i\<parallel>\<^sup>2 \<in> \<int>"
    using assms fs_int' carrier_vecD fs_carrier
    by (auto simp add: sq_norm_vec_as_cscalar_prod scalar_prod_def intro!: Ints_sum Ints_mult)
  have "fs ! i \<noteq> 0\<^sub>v n"
    using assms fs_carrier loc_assms nth_mem vs_zero_lin_dep by force
  then have *: "0 \<noteq> \<parallel>fs ! i\<parallel>\<^sup>2"
    using assms sq_norm_vec_eq_0 f_carrier by metis
  show "1 \<le> \<parallel>fs ! i\<parallel>\<^sup>2"
    by (rule Ints_cases[OF fs_Ints]) (use * sq_norm_vec_ge_0[of "fs ! i"] assms in auto)
qed

lemma
  assumes "set fs \<noteq> {}"
  shows N_Ints: "N \<in> \<int>" and N_1: "1 \<le> N"  
proof -
  have "\<exists>v\<^sub>m \<in> set fs. N = sq_norm v\<^sub>m"
    unfolding N_def using assms by (auto intro!: ex_MAXIMUM)
  then obtain v\<^sub>m::"'a vec" where v\<^sub>m_def: "v\<^sub>m \<in> set fs" "N = sq_norm v\<^sub>m"
    by blast
  then show N_Ints: "N \<in> \<int>"
    using fs_int' carrier_vecD fs_carrier
    by (auto simp add: sq_norm_vec_as_cscalar_prod scalar_prod_def intro!: Ints_sum Ints_mult)
  have *: "0 \<noteq> N"
    using N_gso sq_norm_pos assms by fastforce
  show "1 \<le> N"
    by (rule Ints_cases[OF N_Ints]) (use * N_ge_0 assms in force)+
qed

lemma N_mu:
  assumes "i < m" "j \<le> i"
  shows "(\<mu> i j)\<^sup>2 \<le> N ^ (Suc j)"
proof -
  { assume ji: "j < i"
    have "(\<mu> i j)\<^sup>2 \<le> Gramian_determinant fs j * \<parallel>fs ! i\<parallel>\<^sup>2"
      using assms ji by (intro mu_bound_Gramian_determinant) auto
    also have "\<dots> \<le> N ^ j * \<parallel>fs ! i\<parallel>\<^sup>2"
      using assms N_d N_ge_0 by (intro mult_mono) fastforce+
    also have "N ^ j * \<parallel>fs ! i\<parallel>\<^sup>2 \<le> N ^ j * N"
      using assms N_fs N_ge_0 by (intro mult_mono) fastforce+
    also have "\<dots> = N ^ (Suc j)"
      by auto
    finally have ?thesis
      by simp }
  moreover 
  { assume ji: "j = i"
    have "(\<mu> i j)\<^sup>2 = 1"
      using ji by (simp add: \<mu>.simps)
    also have "\<dots> \<le> N"
      using assms N_1 by fastforce
    also have "\<dots> \<le> N ^ (Suc j)"
      using assms N_1 by fastforce
    finally have ?thesis
      by simp }
  ultimately show ?thesis
    using assms by fastforce
qed

end


lemma vec_hom_Ints:
  assumes "i < n" "xs \<in> carrier_vec n"
  shows "of_int_hom.vec_hom xs $ i \<in> \<int>"
  using assms by auto

lemma division_to_div: "(of_int x  :: 'a :: floor_ceiling) = of_int y / of_int z \<Longrightarrow> x = y div z" 
  by (metis floor_divide_of_int_eq floor_of_int)

lemma exact_division: assumes "of_int x / (of_int y  :: 'a :: floor_ceiling) \<in> \<int>"
  shows "of_int (x div y) = of_int x / (of_int y :: 'a)" 
  using assms by (metis Ints_cases division_to_div)

lemma int_via_rat_eqI: "rat_of_int x = rat_of_int y \<Longrightarrow> x = y" by auto

locale fs_int =
  fixes
    n :: nat (* n-dimensional vectors, *) and
    fs_init :: "int vec list" (* initial basis *)
begin

sublocale vec_module "TYPE(int)" n .

abbreviation RAT where "RAT \<equiv> map (map_vec rat_of_int)" 
abbreviation (input) m where "m \<equiv> length fs_init"

sublocale gs: gram_schmidt_fs n "RAT fs_init" .

definition d :: "int vec list \<Rightarrow> nat \<Rightarrow> int" where "d fs k = gs.Gramian_determinant fs k"
definition D :: "int vec list \<Rightarrow> nat" where "D fs = nat (\<Prod> i < length fs. d fs i)" 

lemma of_int_Gramian_determinant:
  assumes "k \<le> length F" "\<And>i. i < length F \<Longrightarrow> dim_vec (F ! i) = n"
  shows "gs.Gramian_determinant (map of_int_hom.vec_hom F) k = of_int (gs.Gramian_determinant F k)"
  unfolding gs.Gramian_determinant_def of_int_hom.hom_det[symmetric]
proof (rule arg_cong[of _ _ det])
  let ?F = "map of_int_hom.vec_hom F"
  have cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by auto
  show "gs.Gramian_matrix ?F k = map_mat of_int (gs.Gramian_matrix F k)" 
    unfolding gs.Gramian_matrix_def Let_def
  proof (subst of_int_hom.mat_hom_mult[of _ k n _ k], (auto)[2], rule cong)
    show id: "mat k n (\<lambda> (i,j). ?F ! i $ j) = map_mat of_int (mat k n (\<lambda> (i, j). F ! i $ j))" (is "?L = map_mat _ ?R")
    proof (rule eq_matI, goal_cases)
      case (1 i j)
      hence ij: "i < k" "j < n" "i < length F" "dim_vec (F ! i) = n" using assms by auto
      show ?case using ij by simp 
    qed auto
    show "?L\<^sup>T = map_mat of_int ?R\<^sup>T" unfolding id by (rule eq_matI, auto)
  qed
qed

end

locale fs_int_indpt = fs_int n fs for n fs +
  assumes lin_indep: "gs.lin_indpt_list (RAT fs)"
begin

sublocale gs: gram_schmidt_fs_lin_indpt n "RAT fs"
  by (standard) (use lin_indep gs.lin_indpt_list_def in auto)

sublocale gs: gram_schmidt_fs_int n "RAT fs"
  by (standard) (use gs.f_carrier lin_indep gs.lin_indpt_list_def in \<open>auto intro!: vec_hom_Ints\<close>)

lemma f_carrier[dest]: "i < m \<Longrightarrow> fs ! i \<in> carrier_vec n"
  and fs_carrier [simp]: "set fs \<subseteq> carrier_vec n"
  using lin_indep gs.f_carrier gs.gso_carrier unfolding gs.lin_indpt_list_def by auto

lemma Gramian_determinant:
  assumes k: "k \<le> m" 
  shows "of_int (gs.Gramian_determinant fs k) = (\<Prod> j<k. sq_norm (gs.gso j))" (is ?g1)
    "gs.Gramian_determinant fs k > 0" (is ?g2)
proof -
  have hom: "gs.Gramian_determinant (RAT fs) k = of_int (gs.Gramian_determinant fs k)"
    using k by (intro of_int_Gramian_determinant) auto
  show ?g1
    unfolding hom[symmetric] using gs.Gramian_determinant assms by auto
  show ?g2
    using hom gs.Gramian_determinant assms by fastforce
qed

lemma fs_int_d_pos [intro]:
  assumes k: "k \<le> m" 
shows "d fs k > 0"
  unfolding d_def using Gramian_determinant[OF k] by auto

lemma fs_int_d_Suc:
  assumes k: "k < m" 
shows "of_int (d fs (Suc k)) = sq_norm (gs.gso k) * of_int (d fs k)" 
proof -
  from k have k: "k \<le> m" "Suc k \<le> m" by auto
  show ?thesis unfolding Gramian_determinant[OF k(1)] Gramian_determinant[OF k(2)] d_def
    by (subst prod.remove[of _ k], force+, rule arg_cong[of _ _ "\<lambda> x. _ * x"], rule prod.cong, auto)
qed

lemma fs_int_D_pos:
shows "D fs > 0"
proof -
  have "(\<Prod> j < m. d fs j) > 0"
    by (rule prod_pos, insert fs_int_d_pos, auto)
  thus ?thesis unfolding D_def by auto
qed

definition "d\<mu> i j = int_of_rat (of_int (d fs (Suc j)) * gs.\<mu> i j)" 

lemma fs_int_mu_d_Z:
  assumes j: "j \<le> ii" and ii: "ii < m" 
  shows "of_int (d fs (Suc j)) * gs.\<mu> ii j \<in> \<int>"
proof -
  have id: "of_int (d fs (Suc j)) = gs.Gramian_determinant (RAT fs) (Suc j)" 
    unfolding d_def
    by (rule of_int_Gramian_determinant[symmetric], insert j ii , auto)
  have "of_int_hom.vec_hom (fs ! j) $ i \<in> \<int>" if "i < n" "j < length fs" for i j
     using that by (intro vec_hom_Ints) auto
  then show ?thesis
    unfolding id using j ii unfolding gs.lin_indpt_list_def 
    by (intro gs.d_mu_Ints) (auto)
qed

lemma fs_int_mu_d_Z_m_m:
  assumes j: "j < m" and ii: "ii < m" 
  shows "of_int (d fs (Suc j)) * gs.\<mu> ii j \<in> \<int>"
proof (cases "j \<le> ii")
  case True
  thus ?thesis using fs_int_mu_d_Z[OF True ii] by auto
next
  case False thus ?thesis by (simp add: gs.\<mu>.simps)
qed


lemma sq_norm_fs_via_sum_mu_gso: assumes i: "i < m" 
  shows "of_int \<parallel>fs ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (gs.\<mu> i j)\<^sup>2 * \<parallel>gs.gso j\<parallel>\<^sup>2)" 
proof -
  let ?G = "map (gs.gso) [0 ..< m]" 
  let ?gso = "\<lambda> fs j. ?G ! j"
  have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 = \<parallel>RAT fs ! i\<parallel>\<^sup>2" unfolding sq_norm_of_int[symmetric] using insert i by auto
  also have "RAT fs ! i = gs.sumlist (map (\<lambda>j. gs.\<mu> i j \<cdot>\<^sub>v gs.gso j) [0..<Suc i])" 
    using gs.fi_is_sum_of_mu_gso i by auto
  also have id: "map (\<lambda>j. gs.\<mu> i j \<cdot>\<^sub>v gs.gso j) [0..<Suc i] = map (\<lambda>j. gs.\<mu> i j \<cdot>\<^sub>v ?gso fs j) [0..<Suc i]" 
    by (rule nth_equalityI, insert i, auto simp: nth_append)
  also have "sq_norm (gs.sumlist \<dots>) = sum_list (map sq_norm (map (\<lambda>j. gs.\<mu> i j \<cdot>\<^sub>v gs.gso j) [0..<Suc i]))" 
    unfolding map_map o_def sq_norm_smult_vec
    unfolding sq_norm_vec_as_cscalar_prod cscalar_prod_is_scalar_prod conjugate_id
  proof (subst gs.scalar_prod_lincomb_orthogonal)
    show "Suc i \<le> length ?G" using i by auto
    show "set ?G \<subseteq> carrier_vec n" using gs.gso_carrier by auto
    show "orthogonal ?G" using gs.orthogonal_gso by auto
  qed (rule arg_cong[of _ _ sum_list], intro nth_equalityI, insert i, auto simp: nth_append)
  also have "map sq_norm (map (\<lambda>j. gs.\<mu> i j \<cdot>\<^sub>v gs.gso j) [0..<Suc i]) = map (\<lambda>j. (gs.\<mu> i j)^2 * sq_norm (gs.gso j)) [0..<Suc i]" 
    unfolding map_map o_def sq_norm_smult_vec by (rule map_cong, auto simp: power2_eq_square)
  finally show ?thesis . 
qed

lemma d\<mu>: assumes "j < m" "ii < m" 
  shows "of_int (d\<mu> ii j) = of_int (d fs (Suc j)) * gs.\<mu> ii j" 
  unfolding d\<mu>_def using fs_int_mu_d_Z_m_m assms by auto

end

end
