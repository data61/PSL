subsection\<open>Compactness\<close>

theory Compactness
imports Sema
begin

lemma fin_sat_extend: "fin_sat S \<Longrightarrow> fin_sat (insert F S) \<or> fin_sat (insert (\<^bold>\<not>F) S)"
proof (rule ccontr)
  assume fs: "fin_sat S"
  assume nfs: "\<not> (fin_sat (insert F S) \<or> fin_sat (insert (\<^bold>\<not> F) S))"
  from nfs obtain s1 where s1: "s1 \<subseteq> insert F S"       "finite s1" "\<not>sat s1" unfolding fin_sat_def by blast
  from nfs obtain s2 where s2: "s2 \<subseteq> insert (Not F) S" "finite s2" "\<not>sat s2" unfolding fin_sat_def by blast
  let ?u = "(s1 - {F}) \<union> (s2 - {Not F})"
  have "?u \<subseteq> S" "finite ?u" using s1 s2 by auto
  hence "sat ?u" using fs unfolding fin_sat_def by blast
  then obtain A where A: "\<forall>F \<in> ?u. A \<Turnstile> F" unfolding sat_def by blast
  have "A \<Turnstile> F \<or> A \<Turnstile> \<^bold>\<not>F" by simp
  hence "sat s1 \<or> sat s2" using A unfolding sat_def by(fastforce intro!: exI[where x=A])
  thus False using s1(3) s2(3) by simp
qed

context
begin

lemma fin_sat_antimono: "fin_sat F \<Longrightarrow> G \<subseteq> F \<Longrightarrow> fin_sat G" unfolding fin_sat_def by simp
lemmas fin_sat_insert = fin_sat_antimono[OF _ subset_insertI]

primrec extender :: "nat \<Rightarrow> ('a :: countable) formula set \<Rightarrow> 'a formula set" where
"extender 0 S = S" |
"extender (Suc n) S = (
  let r = extender n S; 
  rt = insert (from_nat n) r;
  rf = insert (\<^bold>\<not>(from_nat n)) r
  in if fin_sat rf then rf else rt
)"

private lemma extender_fin_sat: "fin_sat S \<Longrightarrow> fin_sat (extender n S)"
proof(induction n arbitrary: S)
  case (Suc n)
  note mIH = Suc.IH[OF Suc.prems]
  show ?case proof(cases "fin_sat (insert (Not (from_nat n)) (extender n S))")
    case True thus ?thesis by simp
  next
    case False
    hence "fin_sat (insert ((from_nat n)) (extender n S))" using mIH fin_sat_extend by auto
    thus ?thesis by(simp add: Let_def)
  qed
qed simp

definition "extended S = \<Union>{extender n S|n. True}"

lemma extended_max: "F \<in> extended S \<or> Not F \<in> extended S"
proof -
  obtain n where [simp]: "F = from_nat n" by (metis from_nat_to_nat)
  have "F \<in> extender (Suc n) S \<or> Not F \<in> extender (Suc n) S" by(simp add: Let_def)
  thus ?thesis unfolding extended_def by blast
qed

private lemma extender_Sucset: "extender k S \<subseteq> extender (Suc k) S" by(force simp add: Let_def)
private lemma extender_deeper: "F \<in> extender k S \<Longrightarrow> k \<le> l \<Longrightarrow> F \<in> extender l S" using extender_Sucset le_Suc_eq
  by(induction l) (auto simp del: extender.simps)
private lemma extender_subset: "S \<subseteq> extender k S"
proof -
  from extender_deeper[OF _ le0] have "F \<in> extender 0 Sa \<Longrightarrow> F \<in> extender l Sa" for Sa l F .
  thus ?thesis by auto
qed

lemma extended_fin_sat: 
  assumes "fin_sat S"
  shows  "fin_sat (extended S)"
proof -
  have assm: "\<lbrakk>s \<subseteq> extender n S; finite s\<rbrakk> \<Longrightarrow> sat s" for s n
    using extender_fin_sat[OF assms] unfolding fin_sat_def by presburger
  hence "sat s" if su: "s \<subseteq> \<Union>{extender n S |n. True}" and fin: "finite s" for s proof -
    { fix x assume e: "x \<in> s"
      with su have "x \<in> \<Union>{extender n S |n. True}" by blast
      hence "\<exists>n. x \<in> extender n S" unfolding Union_eq by blast }
    hence "\<forall>x \<in> s. \<exists>n. x \<in> extender n S" by blast
    from finite_set_choice[OF fin this] obtain f where cf: "\<forall>x\<in>s. x \<in> extender (f x) S" ..
    have "\<exists>k. s \<subseteq> \<Union>{extender n S |n. n \<le> k}" proof(intro exI subsetI)
      fix x assume e: "x \<in> s"
      with cf have "x \<in> extender (f x) S" ..
      hence "x \<in> extender (Max (f ` s)) S" by(elim extender_deeper; simp add: e fin)
      thus "x \<in> \<Union>{extender n S |n. n \<le> Max (f ` s)}" by blast
    qed
    moreover have "\<Union>{extender n S |n. n \<le> k} = extender k S" for k proof(induction k) 
      case (Suc k)
      moreover have "\<Union>{extender n S |n. n \<le> Suc k} = \<Union>{extender n S |n. n \<le> k} \<union> extender (Suc k) S" 
        unfolding Union_eq le_Suc_eq
        using le_Suc_eq by(auto simp del: extender.simps)
      ultimately show ?case using extender_Sucset by(force simp del: extender.simps)
    qed simp
    ultimately show "sat s" using assm fin by auto
  qed
  thus ?thesis unfolding extended_def fin_sat_def by presburger
qed

lemma extended_superset: "S \<subseteq> extended S" unfolding extended_def using extender.simps(1) by blast

lemma extended_complem:
  assumes fs: "fin_sat S"
  shows "(F \<in> extended S) \<noteq> (Not F \<in> extended S)"
proof -
  note fs = fs[THEN extended_fin_sat]
  show ?thesis proof(cases "F \<in> extended S")
    case False with extended_max show ?thesis by blast
  next
    case True have "Not F \<notin> extended S" proof 
      assume False: "Not F \<in> extended S"
      with True have "{F, Not F} \<subseteq> extended S" by blast
      moreover have "finite {F, Not F}" by simp
      ultimately have "sat {F, Not F}" using fs unfolding fin_sat_def by blast
      thus False unfolding sat_def by simp
    qed
    with True show ?thesis by blast
  qed
qed

lemma not_fin_sat_extended_UNIV: fixes S :: "'a :: countable formula set" assumes "\<not>fin_sat S" shows "extended S = UNIV" 
text\<open>Note that this crucially depends on the fact that we check \emph{first} whether adding @{term "\<^bold>\<not>F"} makes the set not satisfiable, 
  and add @{term F} otherwise \emph{without any further checks}.
  The proof of compactness does (to the best of my knowledge) depend on neither of these two facts.\<close>
proof -
  from assms[unfolded fin_sat_def, simplified] obtain s :: "'a :: countable formula set"
    where "finite s" "\<not> sat s" by clarify
  from this(2)[unfolded sat_def, simplified] have "\<exists>x\<in>s. \<not> A \<Turnstile> x" for A ..
  have nfs: "\<not>fin_sat (insert x (extender n S))" for n x 
    apply(rule notI)
    apply(drule fin_sat_insert)
    apply(drule fin_sat_antimono)
     apply(rule extender_subset)
    apply(erule notE[rotated])
    apply(fact assms)
  done
  have "x \<in> \<Union>{extender n S |n. True}" for x proof cases
    assume "x \<in> S" thus ?thesis by (metis extended_def extended_superset insert_absorb insert_subset)
  next
    assume "x \<notin> S"
    have "x \<in> extender (Suc (to_nat x)) S" 
      unfolding extender.simps Let_def
      unfolding if_not_P[OF nfs] by simp
    thus ?thesis by blast
  qed
  thus ?thesis unfolding extended_def by auto
qed

lemma extended_tran: "S \<subseteq> T \<Longrightarrow> extended S \<subseteq> extended T"
text\<open>This lemma doesn't hold: think of making S empty and inserting a formula into T s.t. it can never be satisfied simultaneously with the first 
non-tautological formula in the extension S. Showing that this is possible is not worth the effort, since we can't influence the ordering of formulae.
But we showed it anyway.\<close>
oops
lemma extended_not_increasing: "\<exists>S T. fin_sat S \<and> fin_sat T \<and> \<not> (S \<subseteq> T \<longrightarrow> extended S \<subseteq> extended (T :: 'a :: countable formula set))"
proof -
  have ex_then_min: "\<exists>x :: nat. P x \<Longrightarrow> P (LEAST x. P x)" for P using LeastI2_wellorder by auto
  define P where "P x = (let F = (from_nat x :: 'a formula) in (\<exists>A. \<not> A \<Turnstile> F) \<and> (\<exists> A. A \<Turnstile> F))" for x
  define x where "x = (LEAST n. P n)"
  hence "\<exists>n. P n" unfolding P_def Let_def by(auto intro!: exI[where x="to_nat (Atom undefined :: 'a formula)"])
  from ex_then_min[OF this] have Px: "P x" unfolding x_def .
  have lessx: "n < x \<Longrightarrow> \<not> P n" for n unfolding x_def using not_less_Least by blast
  let ?S = "{} :: 'a formula set" let ?T = "{from_nat x :: 'a formula}"
  have s: "fin_sat ?S" "fin_sat ?T" using Px unfolding P_def fin_sat_def sat_def Let_def by fastforce+
  have reject: "Q A \<Longrightarrow> \<forall>A. \<not> Q A \<Longrightarrow> False" for A Q by simp
  have "y \<le> x \<Longrightarrow> F \<in> extender y ?S \<Longrightarrow> \<Turnstile> F" for F y
  proof(induction y arbitrary: F)
    case (Suc y)
    have *: "F \<in> extender y {} \<Longrightarrow> \<Turnstile> F" for F :: "'a formula" using Suc.IH Suc.prems(1) by auto
    let ?Y = "from_nat y :: 'a formula"
    have ex: "(\<forall>A. \<not> A \<Turnstile> ?Y) \<or> \<Turnstile> ?Y" unfolding formula_semantics.simps by (meson P_def Suc.prems(1) Suc_le_lessD lessx)
    have 1: "\<forall>A. \<not> A \<Turnstile> ?Y" if "fin_sat (Not ?Y \<triangleright> extender y ?S)"
    proof -
      note[[show_types]]
      from that have "\<exists>A. A \<Turnstile> Not ?Y" unfolding fin_sat_def sat_def  by(elim allE[where x="{Not ?Y}"]) simp
      hence "\<not>\<Turnstile> ?Y" by simp
      hence "\<forall>A. \<not> A \<Turnstile> ?Y" using ex by argo
      thus ?thesis by simp
    qed
    have 2: "\<not> fin_sat (Not ?Y \<triangleright> extender y ?S) \<Longrightarrow> \<Turnstile> ?Y"
    proof(erule contrapos_np)
      assume "\<not> \<Turnstile> ?Y"
      hence "\<forall>A. \<not> A \<Turnstile> ?Y" using ex by argo
      hence "\<Turnstile> \<^bold>\<not> ?Y" by simp
      thus "fin_sat (\<^bold>\<not> ?Y \<triangleright> extender y ?S)" unfolding fin_sat_def sat_def
        by(auto intro!: exI[where x="\<lambda>_ :: 'a. False"] dest!: rev_subsetD[rotated] *)
    qed
    show ?case using Suc.prems(2) by(simp add: Let_def split: if_splits; elim disjE; simp add: * 1 2)
  qed simp
  hence "fin_sat (\<^bold>\<not> (from_nat x) \<triangleright> extender x ?S)" using Px unfolding P_def Let_def
    by (clarsimp simp: fin_sat_def sat_def) (insert formula_semantics.simps(3), blast)
  hence "Not (from_nat x) \<in> extender (Suc x) ?S" by(simp)
  hence "Not (from_nat x) \<in> extended ?S" unfolding extended_def by blast
  moreover have "Not (from_nat x) \<notin> extended ?T" using extended_complem extended_superset s(2) by blast
  ultimately show ?thesis using s by blast
qed

private lemma not_in_extended_FE: "fin_sat S \<Longrightarrow> (\<not>sat (insert (Not F) G)) \<Longrightarrow> F \<notin> extended S \<Longrightarrow> G \<subseteq> extended S \<Longrightarrow> finite G \<Longrightarrow> False"
proof(goal_cases)
  case 1
  hence "Not F \<in> extended S" using extended_max by blast
  thus False using 1 extended_fin_sat fin_sat_def
    by (metis Diff_eq_empty_iff finite.insertI insert_Diff_if)
qed
  
lemma extended_id: "extended (extended S) = extended S" 
  using extended_complem extended_fin_sat extended_max extended_superset not_fin_sat_extended_UNIV 
  by(intro equalityI[rotated] extended_superset) blast
  
(* This would be nicer, though\<dots> 
inductive_set extended_set :: "form set \<Rightarrow> form set" for S where
"F \<in> S \<Longrightarrow> F \<in> extended_set S" |
"fin_sat (insert F (extended_set S)) \<or> F \<in> extended_set S \<Longrightarrow> F \<in> extended_set S"
but it can't work, as extended is not increasing (?) *)
  
lemma ext_model:
  assumes r: "fin_sat S"
  shows "(\<lambda>k. Atom k \<in> extended S) \<Turnstile> F \<longleftrightarrow> F \<in> extended S"
proof -
  note fs = r[THEN extended_fin_sat]
  have Elim: "F \<in> S \<and> G \<in> S \<Longrightarrow> {F,G} \<subseteq> S" "F \<in> S \<Longrightarrow> {F} \<subseteq> S" for F G S by simp+
  show ?thesis
  proof(induction F)
    case Atom thus ?case by(simp)
  next
    case Bot
    have False if "\<bottom> \<in> extended S" proof -
      have "finite {\<bottom>}" by simp
      moreover from that have "{\<bottom>} \<subseteq> extended S" by simp
      ultimately have "\<exists>A. A \<Turnstile> \<bottom>" using fs unfolding fin_sat_def sat_def
        by(elim allE[of _ "{\<bottom>}"]) simp
      thus False by simp
    qed
    thus ?case by auto
  next
    case (Not F)
    moreover have "A \<Turnstile> F \<noteq> A \<Turnstile> \<^bold>\<not>F" for A F by simp
    ultimately show ?case using extended_complem[OF r] by blast
  next
    case (And F G)
    have "(F \<in> extended S \<and> G \<in> extended S) = (F \<^bold>\<and> G \<in> extended S)" proof -
      have *: "\<not>sat {\<^bold>\<not> (F \<^bold>\<and> G), F, G}" "\<not>sat {\<^bold>\<not> F, (F \<^bold>\<and> G)}" "\<not>sat {\<^bold>\<not> G, (F \<^bold>\<and> G)}" unfolding sat_def by auto
      show ?thesis by(intro iffI; rule ccontr) (auto intro: *[THEN not_in_extended_FE[OF r]])
    qed
    thus ?case by(simp add: And) 
  next
    case (Or F G)
    have "(F \<in> extended S \<or> G \<in> extended S) = (F \<^bold>\<or> G \<in> extended S)" proof -
      have "\<not>sat {\<^bold>\<not>(F \<^bold>\<or> G), F}" "\<not>sat {\<^bold>\<not>(F \<^bold>\<or> G), G}" unfolding sat_def by auto
      from this[THEN not_in_extended_FE[OF r]] have 1: "\<lbrakk>F \<in> extended S \<or> G \<in> extended S; F \<^bold>\<or> G \<notin> extended S\<rbrakk> \<Longrightarrow> False" by auto
      have "\<not>sat {\<^bold>\<not>F, \<^bold>\<not>G, F \<^bold>\<or> G}" unfolding sat_def by auto
      hence 2: "\<lbrakk>F \<^bold>\<or> G \<in> extended S; F \<notin> extended S; G \<notin> extended S\<rbrakk> \<Longrightarrow> False" using extended_max not_in_extended_FE[OF r] by fastforce
      show ?thesis by(intro iffI; rule ccontr) (auto intro: 1 2)
    qed
    thus ?case by(simp add: Or)
  next
    case (Imp F G)
    have "(F \<in> extended S \<longrightarrow> G \<in> extended S) = (F \<^bold>\<rightarrow> G \<in> extended S)" proof -
      have "\<not>sat {\<^bold>\<not>G, F, F \<^bold>\<rightarrow> G}" unfolding sat_def by auto
      hence 1: "\<lbrakk>F \<^bold>\<rightarrow> G \<in> extended S; F \<in> extended S; G \<notin> extended S\<rbrakk> \<Longrightarrow> False" using extended_max not_in_extended_FE[OF r] by blast
      have "\<not>sat {\<^bold>\<not>F,\<^bold>\<not>(F \<^bold>\<rightarrow> G)}" unfolding sat_def by auto
      hence 2: "\<lbrakk>F \<^bold>\<rightarrow> G \<notin> extended S; F \<notin> extended S\<rbrakk> \<Longrightarrow> False" using extended_max not_in_extended_FE[OF r] by blast
      have "\<not>sat {\<^bold>\<not>(F \<^bold>\<rightarrow> G),G}" unfolding sat_def by auto
      hence 3: "\<lbrakk>F \<^bold>\<rightarrow> G \<notin> extended S; G \<in> extended S\<rbrakk> \<Longrightarrow> False" using extended_max not_in_extended_FE[OF r] by blast
      show ?thesis by(intro iffI; rule ccontr) (auto intro: 1 2 3)
    qed
    thus ?case by(simp add: Imp)
  qed
qed

theorem compactness:
  fixes S :: "'a :: countable formula set"
  shows "sat S \<longleftrightarrow> fin_sat S" (is "?l = ?r")
proof
  assume ?l thus ?r unfolding sat_def fin_sat_def by blast
next
  assume r: ?r
  note ext_model[OF r, THEN iffD2]
  hence "\<forall>F\<in>S. (\<lambda>k. Atom k \<in> extended S) \<Turnstile> F" using extended_superset by blast
  thus ?l unfolding sat_def by blast
qed

corollary compact_entailment:
  fixes F :: "'a :: countable formula"
  assumes fent: "\<Gamma> \<TTurnstile> F"
  shows "\<exists>\<Gamma>'. finite \<Gamma>' \<and> \<Gamma>' \<subseteq> \<Gamma> \<and> \<Gamma>' \<TTurnstile> F"
proof -
  have ND_sem:  "\<Gamma> \<TTurnstile> F \<longleftrightarrow> \<not>sat (insert (\<^bold>\<not>F) \<Gamma>)" 
    for \<Gamma> F unfolding sat_def entailment_def by auto
  obtain \<Gamma>' where 0: "finite \<Gamma>'" "\<Gamma>' \<TTurnstile> F" "\<Gamma>' \<subseteq> \<Gamma>" proof(goal_cases)
    from fent[unfolded ND_sem compactness] have "\<not> fin_sat (insert (\<^bold>\<not> F) \<Gamma>)" .
    from this[unfolded fin_sat_def] obtain s where s: "s \<subseteq> insert(\<^bold>\<not>F) \<Gamma>" "finite s" "\<not>sat s" by blast
    have 2: "finite (s - {\<^bold>\<not> F})" using s by simp
    have 3: "s - {\<^bold>\<not> F} \<TTurnstile> F" unfolding ND_sem using s(3) unfolding sat_def by blast
    have 4: "s - {\<^bold>\<not> F} \<subseteq> \<Gamma>" using s by blast
    case 1 from 2 3 4 show ?case by(intro 1[of "s - {Not F}"])
  qed
  thus ?thesis by blast
qed
  
corollary compact_to_formula:
  fixes F :: "'a :: countable formula"
  assumes fent: "\<Gamma> \<TTurnstile> F"
  obtains \<Gamma>' where "set \<Gamma>' \<subseteq> \<Gamma>" "\<Turnstile> (\<^bold>\<And>\<Gamma>') \<^bold>\<rightarrow> F"
proof goal_cases
  case 1
  note compact_entailment[OF assms]
  then guess \<Gamma>' ..
  moreover then obtain \<Gamma>'' where "\<Gamma>' = set \<Gamma>''" using finite_list by auto
  ultimately show thesis by(intro 1)  (blast, simp add: entailment_def)
qed

end
    
end
