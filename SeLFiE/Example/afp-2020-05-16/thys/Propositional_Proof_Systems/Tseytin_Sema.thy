theory Tseytin_Sema
imports Sema Tseytin
begin           

lemma biimp_simp[simp]: "\<A> \<Turnstile> F \<^bold>\<leftrightarrow> G \<longleftrightarrow> (\<A> \<Turnstile> F \<longleftrightarrow> \<A> \<Turnstile> G)"
  unfolding biimp_def by auto
    
locale freshstuff_sema = freshstuff
begin
  
definition "tseytin_update \<A> F \<equiv> (let U = map (apsnd (formula_semantics \<A>)) (tseytin_assmt F) in foldl pair_fun_upd \<A> U)"

lemma tseyting_update_keep_subformula_sema: "G \<in> set (subformulae F) \<Longrightarrow> tseytin_update \<A> F \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> G"
proof -
  assume "G \<in> set (subformulae F)"
  hence sub: "atoms G \<subseteq> atoms F" by(fact subformula_atoms)
  have natoms: "k \<in> atoms F \<Longrightarrow> k \<notin> fst ` set (tseytin_assmt F)" for k l 
    using tseytin_assmt_new_atoms by force
  have "k \<in> atoms F \<Longrightarrow> tseytin_update \<A> F k = \<A> k" for k
    unfolding tseytin_update_def Let_def 
    by(force intro!: fold_pair_upd_triv dest!: natoms)
  thus ?thesis using relevant_atoms_same_semantics sub by (metis subsetCE)
qed   

lemma "(k,G) \<in> set (tseytin_assmt F) \<Longrightarrow> tseytin_update \<A> F k \<longleftrightarrow> tseytin_update \<A> F \<Turnstile> G"
proof(induction F arbitrary: G)
  case (Atom x)
  then show ?case by(simp add: tseytin_update_def tseytin_assmt_def Let_def pair_fun_upd_def)
next
  case Bot
  then show ?case by(simp add: tseytin_update_def tseytin_assmt_def Let_def pair_fun_upd_def)
next
  case (Not F)
  then show ?case
    oops
      
lemma tseytin_updates: "(k,G) \<in> set (tseytin_assmt F) \<Longrightarrow> tseytin_update \<A> F k \<longleftrightarrow> tseytin_update \<A> F \<Turnstile> G"
  apply(subst tseytin_update_def)
  apply(simp add: tseytin_assmt_def Let_def foldl_pair_fun_upd_map_of map_of_map_apsnd distinct_zipunzip[OF nfresh_distinct[OF atoms_finite]])
  apply(subst tseyting_update_keep_subformula_sema)
   apply(erule in_set_zipE; simp; fail)
  ..

lemma tseytin_tran1: "G \<in> set (subformulae F) \<Longrightarrow> H \<in> set (tseytin_tran1 S G) \<Longrightarrow> \<forall>J \<in> set (subformulae F). tseytin_update \<A> F \<Turnstile> J \<longleftrightarrow> tseytin_update \<A> F \<Turnstile> (S J) \<Longrightarrow> tseytin_update \<A> F \<Turnstile> H"
proof(induction G arbitrary: H)
  case Bot thus ?case by auto
next
  case (Atom k) thus ?case by fastforce
next
  case (Not G)
  consider "H = S (\<^bold>\<not> G) \<^bold>\<leftrightarrow> \<^bold>\<not> (S G)" | " H \<in> set (tseytin_tran1 S G)" using Not.prems(2) by auto
  then show ?case proof cases
    case 1 then show ?thesis using Not.prems(3)
      by (metis Not.prems(1) biimp_simp formula_semantics.simps(3) set_subset_Cons subformulae.simps(3) subformulae_self subsetCE subsubformulae)
  next
    have D: "\<^bold>\<not>G \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F)"
      by(elim subsubformulae; simp)
    case 2 then show ?thesis using D Not.IH Not.prems(1,3) by blast
  qed
next
  case (And G1 G2)
  have el: "G1 \<in> set (subformulae F)" "G2 \<in> set (subformulae F)" using subsubformulae And.prems(1) by fastforce+
  with And.IH And.prems(3) have IH: "H \<in> set (tseytin_tran1 S G1) \<Longrightarrow> tseytin_update \<A> F \<Turnstile> H"
                                    "H \<in> set (tseytin_tran1 S G2) \<Longrightarrow> tseytin_update \<A> F \<Turnstile> H" for H
    by blast+
  show ?case using And.prems IH el by(simp; elim disjE; simp; insert And.prems(1) formula_semantics.simps(4), blast)
next
  case (Or G1 G2)
  have el: "G1 \<in> set (subformulae F)" "G2 \<in> set (subformulae F)" using subsubformulae Or.prems(1) by fastforce+
  with Or.IH Or.prems(3) have IH: "H \<in> set (tseytin_tran1 S G1) \<Longrightarrow> tseytin_update \<A> F \<Turnstile> H"
                                  "H \<in> set (tseytin_tran1 S G2) \<Longrightarrow> tseytin_update \<A> F \<Turnstile> H" for H
    by blast+
  show ?case using Or.prems(3,2) IH el by(simp; elim disjE; simp; metis Or.prems(1) formula_semantics.simps(5))
next
  case (Imp G1 G2)
  have el: "G1 \<in> set (subformulae F)" "G2 \<in> set (subformulae F)" using subsubformulae Imp.prems(1) by fastforce+
  with Imp.IH Imp.prems(3) have IH: "H \<in> set (tseytin_tran1 S G1) \<Longrightarrow> tseytin_update \<A> F \<Turnstile> H"
                                    "H \<in> set (tseytin_tran1 S G2) \<Longrightarrow> tseytin_update \<A> F \<Turnstile> H" for H
    by blast+
  show ?case using Imp.prems(3,2) IH el by(simp; elim disjE; simp; metis Imp.prems(1) formula_semantics.simps(6))
qed

lemma all_tran_formulas_validated: "\<forall>J \<in> set (subformulae F). tseytin_update \<A> F \<Turnstile> J \<longleftrightarrow> tseytin_update \<A> F \<Turnstile> (tseytin_toatom F J)"
  apply(simp add: tseytin_toatom_def)
  apply(intro ballI)
  apply(subst tseytin_updates)
   apply(erule tseytin_assmt_backlookup)
  ..

lemma tseytin_tran_equisat: "\<A> \<Turnstile> F \<longleftrightarrow> tseytin_update \<A> F \<Turnstile> (tseytin_tran F)"
  using all_tran_formulas_validated tseytin_tran1 all_tran_formulas_validated tseyting_update_keep_subformula_sema by(simp add: tseytin_tran_def Let_def) blast
(* unfortunately, that's not enough. *)
    
lemma tseytin_tran1_orig_connection: "G \<in> set (subformulae F) \<Longrightarrow> (\<forall>H\<in>set (tseytin_tran1 (tseytin_toatom F) G). \<A> \<Turnstile> H) \<Longrightarrow>
  \<A> \<Turnstile> G \<longleftrightarrow> \<A> \<Turnstile> tseytin_toatom F G"
  by(induction G; simp; drule subformulas_in_subformulas; simp)

lemma tseytin_untran: "\<A> \<Turnstile> (tseytin_tran F) \<Longrightarrow> \<A> \<Turnstile> F" 
proof -
  have 1: "\<lbrakk>\<A> \<Turnstile> tseytin_toatom F F; \<A> \<Turnstile> F\<rbrakk> \<Longrightarrow> tseytin_update \<A> F \<Turnstile> tseytin_toatom F F"
    using all_tran_formulas_validated tseyting_update_keep_subformula_sema by blast
  let ?C = "\<lambda>\<A>. (\<forall>H \<in> set (tseytin_tran1 (tseytin_toatom F) F). \<A> \<Turnstile> H)"
  have 2: "?C \<A> \<Longrightarrow> ?C (tseytin_update \<A> F)"
    using all_tran_formulas_validated tseytin_tran1 by blast
  assume "\<A> \<Turnstile> tseytin_tran F"
  hence "tseytin_update \<A> F \<Turnstile> tseytin_tran F" 
    unfolding tseytin_tran_def
    apply(simp add: Let_def)
    apply(intro conjI)
     apply(elim conjE)
     apply(drule tseytin_tran1_orig_connection[OF subformulae_self])
     apply(clarsimp simp add: tseytin_assmt_distinct foldl_pair_fun_upd_map_of 1 2)+
    done
  thus ?thesis using tseytin_tran_equisat by blast
qed
lemma tseytin_tran_equiunsatisfiable: "\<Turnstile> \<^bold>\<not>F \<longleftrightarrow> \<Turnstile> \<^bold>\<not> (tseytin_tran F)"  (is "?l \<longleftrightarrow> ?r")
proof(rule iffI; erule contrapos_pp)
  assume "\<not>?l"
  then obtain \<A> where "\<A> \<Turnstile> F" by auto
  hence "tseytin_update \<A> F \<Turnstile> (tseytin_tran F)" using tseytin_tran_equisat by simp
  thus "\<not>?r" by simp blast
next
  assume "\<not>?r"
  then obtain \<A> where "\<A> \<Turnstile> tseytin_tran F" by auto
  thus "~?l" using tseytin_untran by simp blast 
qed
  
end
  
interpretation freshsemanats: freshstuff_sema freshnat
  by (simp add: freshnats.freshstuff_axioms freshstuff_sema_def)
print_theorems
(* Just showing that it is possible. There isn't really anything new that could be executed here. *)
  
end
