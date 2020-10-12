section \<open>Matrices\<close>
theory IICF_Matrix
imports "../../Sepref"
begin
  subsection \<open>Relator and Interface\<close>
  definition [to_relAPP]: "mtx_rel A \<equiv> nat_rel \<times>\<^sub>r nat_rel \<rightarrow> A"

  lemma mtx_rel_id[simp]: "\<langle>Id\<rangle>mtx_rel = Id" unfolding mtx_rel_def by auto
  
  type_synonym 'a mtx = "nat\<times>nat \<Rightarrow> 'a"
  sepref_decl_intf 'a i_mtx is "nat\<times>nat \<Rightarrow> 'a"

  lemma [synth_rules]: "INTF_OF_REL A TYPE('a) \<Longrightarrow> INTF_OF_REL (\<langle>A\<rangle>mtx_rel) TYPE('a i_mtx)"
    by simp
  
  subsection \<open>Operations\<close>  

  definition op_mtx_new :: "'a mtx \<Rightarrow> 'a mtx" where [simp]: "op_mtx_new c \<equiv> c"

  sepref_decl_op (no_def) mtx_new: "op_mtx_new" :: "(nat_rel\<times>\<^sub>rnat_rel \<rightarrow> A) \<rightarrow> \<langle>A\<rangle>mtx_rel"
    apply (rule fref_ncI) unfolding op_mtx_new_def[abs_def] mtx_rel_def 
    by parametricity

  (* TODO: Ad-hoc rule *)
  lemma mtx_init_adhoc_frame_match_rule[sepref_frame_match_rules]:
    "hn_val (nat_rel\<times>\<^sub>rnat_rel \<rightarrow> A) x y \<Longrightarrow>\<^sub>t hn_val (nat_rel\<times>\<^sub>rnat_rel \<rightarrow> the_pure (pure A)) x y"
    by simp

  definition op_mtx_copy :: "'a mtx \<Rightarrow> 'a mtx" where [simp]: "op_mtx_copy c \<equiv> c"

  sepref_decl_op (no_def) mtx_copy: "op_mtx_copy" :: "\<langle>A\<rangle>mtx_rel \<rightarrow> \<langle>A\<rangle>mtx_rel" .

  sepref_decl_op mtx_get: "\<lambda>(c::'a mtx) ij. c ij" :: "\<langle>A\<rangle>mtx_rel \<rightarrow> (nat_rel\<times>\<^sub>rnat_rel) \<rightarrow> A"
    apply (rule fref_ncI) unfolding mtx_rel_def
    by parametricity
    
  sepref_decl_op mtx_set: "fun_upd::'a mtx \<Rightarrow> _" :: "\<langle>A\<rangle>mtx_rel \<rightarrow> (nat_rel\<times>\<^sub>rnat_rel) \<rightarrow> A \<rightarrow> \<langle>A\<rangle>mtx_rel"
    apply (rule fref_ncI) 
    unfolding mtx_rel_def
  proof goal_cases case 1  
    have [param]: "((=), (=)) \<in> nat_rel \<times>\<^sub>r nat_rel \<rightarrow> nat_rel \<times>\<^sub>r nat_rel \<rightarrow> bool_rel" by simp
    show ?case by parametricity
  qed

  definition mtx_nonzero :: "_ mtx \<Rightarrow> (nat\<times>nat) set" where "mtx_nonzero m \<equiv> {(i,j). m (i,j)\<noteq>0}"

  sepref_decl_op mtx_nonzero: "mtx_nonzero" :: "\<langle>A\<rangle>mtx_rel \<rightarrow> \<langle>nat_rel\<times>\<^sub>rnat_rel\<rangle>set_rel"
    where "IS_ID (A::(_\<times>(_::zero)) set)"
  proof goal_cases
    case 1
    assume "IS_ID A"
    hence U: "A=Id" by (simp only: IS_ID_def)
    have [param]: "((=),(=))\<in>A\<rightarrow>A\<rightarrow>bool_rel" using U by simp
    show ?case
      apply (rule fref_ncI)
      unfolding mtx_rel_def
      apply parametricity
      unfolding U by simp_all
  qed

  subsection \<open>Patterns\<close>
  lemma pat_amtx_get: "c$e\<equiv>op_mtx_get$'c$'e" by simp
  lemma pat_amtx_set: "fun_upd$c$e$v\<equiv>op_mtx_set$'c$'e$'v" by simp

  lemmas amtx_pats[pat_rules] = pat_amtx_get pat_amtx_set

  subsection \<open>Pointwise Operations\<close>
  subsubsection \<open>Auxiliary Definitions and Lemmas\<close>
  locale pointwise_op =
    fixes f :: "'p \<Rightarrow> 's \<Rightarrow> 's"
    fixes q :: "'s \<Rightarrow> 'p \<Rightarrow> 'a"
    assumes upd_indep1[simp, intro]: "p\<noteq>p' \<Longrightarrow> q (f p s) p' = q s p'"
    assumes upd_indep2[simp, intro]: "p\<noteq>p' \<Longrightarrow> q (f p (f p' s)) p = q (f p s) p"
  begin
    lemma pointwise_upd_fold: "distinct ps \<Longrightarrow> 
      q (fold f ps s) p = (if p\<in>set ps then q (f p s) p else q s p)"
      by (induction ps arbitrary: s) auto
  
  end
  
  lemma pointwise_fun_fold: 
    fixes f :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
    fixes s :: "'a \<Rightarrow> 'b"
    assumes indep1: "\<And>x x' s. x \<noteq> x' \<Longrightarrow> f x s x' = s x'"
    assumes indep2:  "\<And>x x' s. x \<noteq> x' \<Longrightarrow> f x (f x' s) x = f x s x"
    assumes [simp]: "distinct xs"
    shows "fold f xs s x = (if x \<in> set xs then f x s x else s x)"
  proof -
    interpret pointwise_op f "\<lambda>s. s"
      by unfold_locales fact+
  
    show ?thesis  
      using pointwise_upd_fold[of xs s x]
      by auto
  qed

  lemma list_prod_divmod_eq: "List.product [0..<M] [0..<N] = map (\<lambda>i. (i div N, i mod N)) [0..<N*M]"
  proof -
    have [simp]: "i < m*n \<Longrightarrow> (i::nat) div n < m" for i m n
      by (metis mult.commute div_eq_0_iff div_mult2_eq gr_implies_not_zero mult_not_zero)

    have [simp]: "i<N*M \<Longrightarrow> N>0 \<and> M>0" for i
      by (cases N; cases M; auto)

    show ?thesis  
      by (rule nth_equalityI) (auto simp add: product_nth algebra_simps)
  qed    


  lemma nfoldli_prod_divmod_conv: 
    "nfoldli (List.product [0..<N] [0..<M]) ctd (\<lambda>(i,j). f i j) = nfoldli [0..<N*M] ctd (\<lambda>i. f (i div M) (i mod M))"
    apply (intro ext)
    apply (subst list_prod_divmod_eq)
    apply (simp add: nfoldli_map)
    apply (fo_rule cong)+
    apply (auto simp: algebra_simps)
    done

  lemma nfoldli_prod_divmod_conv': 
    "nfoldli [0..<M] ctd (\<lambda>i. nfoldli [0..<N] ctd (f i)) = nfoldli [0..<N*M] ctd (\<lambda>i. f (i div N) (i mod N))"
    apply (intro ext)
    apply (subst nfoldli_nfoldli_prod_conv)
    by (simp add: nfoldli_prod_divmod_conv algebra_simps)

  lemma foldli_prod_divmod_conv': 
    "foldli [0..<M] ctd (\<lambda>i. foldli [0..<N] ctd (f i)) = foldli [0..<N*M] ctd (\<lambda>i. f (i div N) (i mod N))"
    (is "?lhs=?rhs")  
  proof -
    have "RETURN (?lhs s) = RETURN (?rhs s)" for s 
      apply (subst foldli_eq_nfoldli)+
      apply (subst nfoldli_prod_divmod_conv')
      ..
    thus ?thesis by auto
  qed  
    
  lemma fold_prod_divmod_conv': "fold (\<lambda>i. fold (f i) [0..<N]) [0..<M] = fold (\<lambda>i. f (i div N) (i mod N)) [0..<N*M]"
    using foldli_prod_divmod_conv'[of M "\<lambda>_. True" N f, THEN fun_cong]
    apply (intro ext)
    apply (simp add: foldli_foldl foldl_conv_fold)
    done
    


  lemma mtx_nonzero_cases[consumes 0, case_names nonzero zero]:
    obtains "(i,j)\<in>mtx_nonzero m" | "m (i,j) = 0"
    by (auto simp: mtx_nonzero_def)
  


  subsubsection \<open>Unary Pointwise\<close>
  definition mtx_pointwise_unop :: "(nat\<times>nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mtx \<Rightarrow> 'a mtx" where
    "mtx_pointwise_unop f m \<equiv> \<lambda>(i,j). f (i,j) (m(i,j))"
  
  context fixes f :: "nat\<times>nat \<Rightarrow> 'a \<Rightarrow> 'a" begin
    sepref_register "PR_CONST (mtx_pointwise_unop f)" :: "'a i_mtx \<Rightarrow> 'a i_mtx"
    lemma [def_pat_rules]: "mtx_pointwise_unop$f \<equiv> UNPROTECT (mtx_pointwise_unop f)" by simp
  end
  
  locale mtx_pointwise_unop_loc =
    fixes N :: nat and M :: nat
    fixes f :: "(nat\<times>nat) \<Rightarrow> 'a::{zero} \<Rightarrow> 'a"
    assumes pres_zero[simp]: "\<lbrakk> i\<ge>N \<or> j\<ge>M \<rbrakk> \<Longrightarrow> f (i,j) 0 = 0"
  begin  
    definition "opr_fold_impl \<equiv> fold (\<lambda>i. fold (\<lambda>j m. m( (i,j) := f (i,j) (m(i,j)) )) [0..<M]) [0..<N]"
    
    lemma opr_fold_impl_eq:
      assumes "mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
      shows "mtx_pointwise_unop f m = opr_fold_impl m"
      apply (rule ext)
      unfolding opr_fold_impl_def
      apply (simp add: fold_fold_prod_conv)
      apply (subst pointwise_fun_fold)
      apply (auto simp: mtx_pointwise_unop_def distinct_product) [3]
      apply clarsimp
      subgoal for a b
        apply (cases a b m rule: mtx_nonzero_cases)
        using assms
        apply (auto simp: mtx_pointwise_unop_def)
        done
      done  
  
    lemma opr_fold_impl_refine: "(opr_fold_impl, mtx_pointwise_unop f) \<in> [\<lambda>m. mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}]\<^sub>f Id \<rightarrow> Id"  
      apply (rule frefI)
      using opr_fold_impl_eq
      by auto
  
  end
  
  locale mtx_pointwise_unop_gen_impl = mtx_pointwise_unop_loc +
    fixes assn :: "'a mtx \<Rightarrow> 'i \<Rightarrow> assn"
    fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
    fixes get_impl :: "'i \<Rightarrow> nat\<times>nat \<Rightarrow> 'ai Heap"
    fixes set_impl :: "'i \<Rightarrow> nat\<times>nat \<Rightarrow> 'ai \<Rightarrow> 'i Heap"
    fixes fi :: "nat\<times>nat \<Rightarrow> 'ai \<Rightarrow> 'ai Heap"
    assumes assn_range: "rdomp assn m \<Longrightarrow> mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
    assumes get_impl_hnr: 
      "(uncurry get_impl,uncurry (RETURN oo op_mtx_get)) \<in> assn\<^sup>k *\<^sub>a (prod_assn (nbn_assn N) (nbn_assn M))\<^sup>k \<rightarrow>\<^sub>a A"
    assumes set_impl_hnr: 
      "(uncurry2 set_impl,uncurry2 (RETURN ooo op_mtx_set)) \<in> assn\<^sup>d *\<^sub>a (prod_assn (nbn_assn N) (nbn_assn M))\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a assn"
    assumes fi_hnr:
      "(uncurry fi,uncurry (RETURN oo f)) \<in> (prod_assn nat_assn nat_assn)\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a A"  
  begin
  
    lemma this_loc: "mtx_pointwise_unop_gen_impl N M f assn A get_impl set_impl fi"
      by unfold_locales
  
    context 
      notes [[sepref_register_adhoc f N M]]
      notes [intf_of_assn] = intf_of_assnI[where R=assn and 'a="'a i_mtx"]
      notes [sepref_import_param] = IdI[of N] IdI[of M]
      notes [sepref_fr_rules] = get_impl_hnr set_impl_hnr fi_hnr
    begin
      sepref_thm opr_fold_impl1 is "RETURN o opr_fold_impl" :: "assn\<^sup>d \<rightarrow>\<^sub>a assn"
        unfolding opr_fold_impl_def
        supply [[goals_limit = 1]]
        by sepref
    end    
  
    concrete_definition (in -) mtx_pointwise_unnop_fold_impl1 uses mtx_pointwise_unop_gen_impl.opr_fold_impl1.refine_raw
    prepare_code_thms (in -) mtx_pointwise_unnop_fold_impl1_def
  
    lemma op_hnr[sepref_fr_rules]: "(mtx_pointwise_unnop_fold_impl1 N M get_impl set_impl fi, RETURN \<circ> PR_CONST (mtx_pointwise_unop f)) \<in> assn\<^sup>d \<rightarrow>\<^sub>a assn"
      unfolding PR_CONST_def
      apply (rule hfref_weaken_pre'[OF _ mtx_pointwise_unnop_fold_impl1.refine[OF this_loc,FCOMP opr_fold_impl_refine]])
      by (simp add: assn_range)
  
  end

  subsubsection \<open>Binary Pointwise\<close>
  definition mtx_pointwise_binop :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mtx \<Rightarrow> 'a mtx \<Rightarrow> 'a mtx" where
    "mtx_pointwise_binop f m n \<equiv> \<lambda>(i,j). f (m(i,j)) (n(i,j))"
  context fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" begin
    sepref_register "PR_CONST (mtx_pointwise_binop f)" :: "'a i_mtx \<Rightarrow> 'a i_mtx \<Rightarrow> 'a i_mtx"
    lemma [def_pat_rules]: "mtx_pointwise_binop$f \<equiv> UNPROTECT (mtx_pointwise_binop f)" by simp
  end
  
  locale mtx_pointwise_binop_loc =
    fixes N :: nat and M :: nat
    fixes f :: "'a::{zero} \<Rightarrow> 'a \<Rightarrow> 'a"
    assumes pres_zero[simp]: "f 0 0 = 0"
  begin  
    definition "opr_fold_impl m n \<equiv> fold (\<lambda>i. fold (\<lambda>j m. m( (i,j) := f (m(i,j)) (n(i,j)) )) [0..<M]) [0..<N] m"
    
    lemma opr_fold_impl_eq:
      assumes "mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
      assumes "mtx_nonzero n \<subseteq> {0..<N}\<times>{0..<M}"
      shows "mtx_pointwise_binop f m n = opr_fold_impl m n"
      apply (rule ext)
      unfolding opr_fold_impl_def
      apply (simp add: fold_fold_prod_conv)
      apply (subst pointwise_fun_fold)
      apply (auto simp: mtx_pointwise_binop_def distinct_product) [3]
      apply clarsimp
      subgoal for a b
        apply (cases a b m rule: mtx_nonzero_cases; cases a b n rule: mtx_nonzero_cases)
        using assms
        apply (auto simp: mtx_pointwise_binop_def)
        done
      done  
  
    lemma opr_fold_impl_refine: "(uncurry opr_fold_impl, uncurry (mtx_pointwise_binop f)) \<in> [\<lambda>(m,n). mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M} \<and> mtx_nonzero n \<subseteq> {0..<N}\<times>{0..<M}]\<^sub>f Id\<times>\<^sub>rId \<rightarrow> Id"  
      apply (rule frefI)
      using opr_fold_impl_eq
      by auto
  
  end
  
  locale mtx_pointwise_binop_gen_impl = mtx_pointwise_binop_loc +
    fixes assn :: "'a mtx \<Rightarrow> 'i \<Rightarrow> assn"
    fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
    fixes get_impl :: "'i \<Rightarrow> nat\<times>nat \<Rightarrow> 'ai Heap"
    fixes set_impl :: "'i \<Rightarrow> nat\<times>nat \<Rightarrow> 'ai \<Rightarrow> 'i Heap"
    fixes fi :: "'ai \<Rightarrow> 'ai \<Rightarrow> 'ai Heap"
    assumes assn_range: "rdomp assn m \<Longrightarrow> mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
    assumes get_impl_hnr: 
      "(uncurry get_impl,uncurry (RETURN oo op_mtx_get)) \<in> assn\<^sup>k *\<^sub>a (prod_assn (nbn_assn N) (nbn_assn M))\<^sup>k \<rightarrow>\<^sub>a A"
    assumes set_impl_hnr: 
      "(uncurry2 set_impl,uncurry2 (RETURN ooo op_mtx_set)) \<in> assn\<^sup>d *\<^sub>a (prod_assn (nbn_assn N) (nbn_assn M))\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a assn"
    assumes fi_hnr:
      "(uncurry fi,uncurry (RETURN oo f)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a A"  
  begin
  
    lemma this_loc: "mtx_pointwise_binop_gen_impl N M f assn A get_impl set_impl fi"
      by unfold_locales
  
    context 
      notes [[sepref_register_adhoc f N M]]
      notes [intf_of_assn] = intf_of_assnI[where R=assn and 'a="'a i_mtx"]
      notes [sepref_import_param] = IdI[of N] IdI[of M]
      notes [sepref_fr_rules] = get_impl_hnr set_impl_hnr fi_hnr
    begin
      sepref_thm opr_fold_impl1 is "uncurry (RETURN oo opr_fold_impl)" :: "assn\<^sup>d*\<^sub>aassn\<^sup>k \<rightarrow>\<^sub>a assn"
        unfolding opr_fold_impl_def[abs_def]
        by sepref
        
    end    
  
    concrete_definition (in -) mtx_pointwise_binop_fold_impl1 
      uses mtx_pointwise_binop_gen_impl.opr_fold_impl1.refine_raw is "(uncurry ?f,_)\<in>_"
    prepare_code_thms (in -) mtx_pointwise_binop_fold_impl1_def
  
    lemma op_hnr[sepref_fr_rules]: "(uncurry (mtx_pointwise_binop_fold_impl1 N M get_impl set_impl fi), uncurry (RETURN oo PR_CONST (mtx_pointwise_binop f))) \<in> assn\<^sup>d *\<^sub>a assn\<^sup>k \<rightarrow>\<^sub>a assn"
      unfolding PR_CONST_def
      apply (rule hfref_weaken_pre'[OF _ mtx_pointwise_binop_fold_impl1.refine[OF this_loc,FCOMP opr_fold_impl_refine]])
      apply (auto dest: assn_range)
      done
  
  end



  subsubsection \<open>Compare Pointwise\<close>
  definition mtx_pointwise_cmpop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a mtx \<Rightarrow> 'a mtx \<Rightarrow> bool" where
    "mtx_pointwise_cmpop f g m n \<equiv> (\<forall>i j. f (m(i,j)) (n(i,j))) \<and> (\<exists>i j. g (m(i,j)) (n(i,j)))"
  context fixes f g :: "'a \<Rightarrow> 'a \<Rightarrow> bool" begin
    sepref_register "PR_CONST (mtx_pointwise_cmpop f g)" :: "'a i_mtx \<Rightarrow> 'a i_mtx \<Rightarrow> bool"
    lemma [def_pat_rules]: "mtx_pointwise_cmpop$f$g \<equiv> UNPROTECT (mtx_pointwise_cmpop f g)" by simp
  end

  (* TODO: Move *)  
  lemma mtx_nonzeroD:
    "\<lbrakk>\<not>i<N; mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}\<rbrakk> \<Longrightarrow> m(i,j) = 0"
    "\<lbrakk>\<not>j<M; mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}\<rbrakk> \<Longrightarrow> m(i,j) = 0"
    by (auto simp: mtx_nonzero_def)


  locale mtx_pointwise_cmpop_loc =
    fixes N :: nat and M :: nat
    fixes f g :: "'a::{zero} \<Rightarrow> 'a \<Rightarrow> bool"
    assumes pres_zero[simp]: "f 0 0 = True" "g 0 0 = False"
  begin  
    definition "opr_fold_impl m n \<equiv> do {
      s \<leftarrow> nfoldli (List.product [0..<N] [0..<M]) (\<lambda>s. s\<noteq>2) (\<lambda>(i,j) s. do {
        if f (m(i,j)) (n(i,j)) then
          if s=0 then
            if g (m(i,j)) (n(i,j)) then RETURN 1 else RETURN s
          else
            RETURN s

        else RETURN 2
      }) (0::nat);
      RETURN (s=1)
    }"

    lemma opr_fold_impl_eq:
      assumes "mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
      assumes "mtx_nonzero n \<subseteq> {0..<N}\<times>{0..<M}"
      shows "opr_fold_impl m n \<le> RETURN (mtx_pointwise_cmpop f g m n)"
    proof -
      have "(\<forall>i<N. \<forall>j<M. f (m (i, j)) (n (i, j))) \<Longrightarrow> f (m (i, j)) (n (i, j))" for i j
        apply (cases "i<N"; cases "j<M")
        using assms by (auto simp: mtx_nonzeroD)
      moreover have "g (m (i, j)) (n (i, j)) \<Longrightarrow> (\<exists>i<N. \<exists>j<M. g (m (i, j)) (n (i, j)))" for i j
        apply (cases "i<N"; cases "j<M")
        using assms by (auto simp: mtx_nonzeroD)
      ultimately have EQ: "mtx_pointwise_cmpop f g m n 
        \<longleftrightarrow> (\<forall>i<N. \<forall>j<M. f (m(i,j)) (n(i,j))) \<and> (\<exists>i<N. \<exists>j<M. g (m(i,j)) (n(i,j)))"
        unfolding mtx_pointwise_cmpop_def by meson
        
      have aux: "List.product [0..<N] [0..<M] = l1 @ (i, j) # l2 \<Longrightarrow> i<N \<and> j<M" for l1 i j l2
      proof -
        assume "List.product [0..<N] [0..<M] = l1 @ (i, j) # l2"
        hence "(i,j)\<in>set (List.product [0..<N] [0..<M])" by simp
        thus ?thesis by simp
      qed  

      show ?thesis  
        unfolding opr_fold_impl_def
        apply (refine_vcg
          nfoldli_rule[where I="\<lambda>l1 _ s. 
              if s=2 then \<exists>i<N. \<exists>j<M. \<not>f (m(i,j)) (n(i,j)) 
              else (
                (s=0 \<or> s=1) \<and>
                (\<forall>(i,j)\<in>set l1. f (m(i,j)) (n(i,j))) \<and>
                (s=1 \<longleftrightarrow> (\<exists>(i,j)\<in>set l1. g (m(i,j)) (n(i,j))))
              )"]
          )
        apply (vc_solve dest: aux solve: asm_rl simp: EQ) [6]
        apply (fastforce simp: EQ)
        done
    qed    
  
    lemma opr_fold_impl_refine: 
      "(uncurry opr_fold_impl, uncurry (RETURN oo mtx_pointwise_cmpop f g)) \<in> [\<lambda>(m,n). mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M} \<and> mtx_nonzero n \<subseteq> {0..<N}\<times>{0..<M}]\<^sub>f Id\<times>\<^sub>rId \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"  
      apply (rule frefI)
      using opr_fold_impl_eq
      by (auto intro: nres_relI)
  
  end
  
  locale mtx_pointwise_cmpop_gen_impl = mtx_pointwise_cmpop_loc +
    fixes assn :: "'a mtx \<Rightarrow> 'i \<Rightarrow> assn"
    fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
    fixes get_impl :: "'i \<Rightarrow> nat\<times>nat \<Rightarrow> 'ai Heap"
    fixes fi :: "'ai \<Rightarrow> 'ai \<Rightarrow> bool Heap"
    fixes gi :: "'ai \<Rightarrow> 'ai \<Rightarrow> bool Heap"
    assumes assn_range: "rdomp assn m \<Longrightarrow> mtx_nonzero m \<subseteq> {0..<N}\<times>{0..<M}"
    assumes get_impl_hnr: 
      "(uncurry get_impl,uncurry (RETURN oo op_mtx_get)) \<in> assn\<^sup>k *\<^sub>a (prod_assn (nbn_assn N) (nbn_assn M))\<^sup>k \<rightarrow>\<^sub>a A"
    assumes fi_hnr:
      "(uncurry fi,uncurry (RETURN oo f)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"  
    assumes gi_hnr:
      "(uncurry gi,uncurry (RETURN oo g)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"  
  begin
  
    lemma this_loc: "mtx_pointwise_cmpop_gen_impl N M f g assn A get_impl fi gi"
      by unfold_locales
  
    context 
      notes [[sepref_register_adhoc f g N M]]
      notes [intf_of_assn] = intf_of_assnI[where R=assn and 'a="'a i_mtx"]
      notes [sepref_import_param] = IdI[of N] IdI[of M]
      notes [sepref_fr_rules] = get_impl_hnr fi_hnr gi_hnr
    begin
      sepref_thm opr_fold_impl1 is "uncurry opr_fold_impl" :: "assn\<^sup>d*\<^sub>aassn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
        unfolding opr_fold_impl_def[abs_def] nfoldli_nfoldli_prod_conv[symmetric]
        by sepref
        
    end    
  
    concrete_definition (in -) mtx_pointwise_cmpop_fold_impl1 
      uses mtx_pointwise_cmpop_gen_impl.opr_fold_impl1.refine_raw is "(uncurry ?f,_)\<in>_"
    prepare_code_thms (in -) mtx_pointwise_cmpop_fold_impl1_def
  
    lemma op_hnr[sepref_fr_rules]: "(uncurry (mtx_pointwise_cmpop_fold_impl1 N M get_impl fi gi), uncurry (RETURN oo PR_CONST (mtx_pointwise_cmpop f g))) \<in> assn\<^sup>d *\<^sub>a assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      unfolding PR_CONST_def
      apply (rule hfref_weaken_pre'[OF _ mtx_pointwise_cmpop_fold_impl1.refine[OF this_loc,FCOMP opr_fold_impl_refine]])
      apply (auto dest: assn_range)
      done
  
  end

end

