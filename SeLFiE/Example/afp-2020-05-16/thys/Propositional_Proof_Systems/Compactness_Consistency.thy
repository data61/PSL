theory Compactness_Consistency
imports Consistency
begin
  
theorem "sat S \<longleftrightarrow> fin_sat (S :: 'a :: countable formula set)" (is "?l = ?r")
proof
  assume 0: ?r
  let ?C = "{W :: 'a formula set. fin_sat W}"
  have 1: "S \<in> ?C" using 0 unfolding mem_Collect_eq .
  have 2: "pcp ?C" proof -
    { fix S :: "'a formula set"
      assume "S \<in> ?C"
      hence a: "\<forall>s\<subseteq>S. finite s \<longrightarrow> (\<exists>\<A>. \<forall>F\<in>s. \<A> \<Turnstile> F)" by (simp add: fin_sat_def sat_def)
      have conj: "\<lbrakk>h F G \<in> S; s \<subseteq> f F \<triangleright> g G \<triangleright> S; finite s;
        \<And>A. A \<Turnstile> h F G \<Longrightarrow> A \<Turnstile> f F \<and> A \<Turnstile> g G\<rbrakk> \<Longrightarrow> \<exists>\<A>. \<forall>F\<in>s. \<A> \<Turnstile> F" 
        for F G s and f g :: "'a formula \<Rightarrow> 'a formula" and h :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula"
      proof goal_cases
        case 1
        have "h F G \<triangleright> s - {f F,g G}\<subseteq>S" "finite (h F G \<triangleright> s-{f F,g G})" using 1 by auto
        then obtain A where 2: "\<forall>H\<in>h F G \<triangleright> s-{f F,g G}. A \<Turnstile> H" using a by presburger
        hence "A \<Turnstile> f F" "A \<Turnstile> g G" using 1(4) by simp_all
        with 2 have "\<forall>H\<in>h F G \<triangleright> s. A \<Turnstile> H" by blast
        thus ?case by blast
      qed
      have disj: "\<lbrakk>h F G \<in> S; s1 \<subseteq> f F \<triangleright> S; s2 \<subseteq> g G \<triangleright> S; finite s1; \<forall>\<A>. \<exists>x\<in>s1. \<not> \<A> \<Turnstile> x; finite s2; \<forall>\<A>. \<exists>x\<in>s2. \<not> \<A> \<Turnstile> x;
        \<And>A. A \<Turnstile> h F G \<Longrightarrow> A \<Turnstile> f F \<or> A \<Turnstile> g G\<rbrakk> \<Longrightarrow> False"
        for F G s1 s2 and f g :: "'a formula \<Rightarrow> 'a formula" and h :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" 
      proof goal_cases
        case 1
        let ?U = "h F G \<triangleright> (s1 - {f F}) \<union> (s2 - {g G})"
        have "?U \<subseteq> S" "finite ?U" using 1 by auto
        with a obtain A where 2: "H \<in> ?U \<Longrightarrow> A \<Turnstile> H" for H by meson
        with 1(1) 1(8)  have "A \<Turnstile> f F \<or> A \<Turnstile> g G" by force
        hence "(\<forall>H \<in> s1. A \<Turnstile> H) \<or> (\<forall>H \<in> s1. A \<Turnstile> H)" using 1(7) 2
          by (metis DiffI Diff_empty Diff_iff UnCI insert_iff)
        thus ?case using 1 by fast
      qed
      have 1: "\<bottom> \<notin> S" using a by (meson empty_subsetI finite.emptyI finite.insertI formula_semantics.simps(2) insertI1 insert_subset)
      have 2: "Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False" for k using a[THEN spec[of _ "{Atom k, \<^bold>\<not>(Atom k)}"]] by auto
      have 3: "F \<^bold>\<and> G \<in> S \<longrightarrow> F \<triangleright> G \<triangleright> S \<in> Collect fin_sat" for F G unfolding fin_sat_def sat_def mem_Collect_eq using conj[] by fastforce
      have 4: "F \<^bold>\<or> G \<in> S \<longrightarrow> F \<triangleright> S \<in> Collect fin_sat \<or> G \<triangleright> S \<in> Collect fin_sat" for F G
        unfolding fin_sat_def sat_def mem_Collect_eq using disj[of Or F G _ "\<lambda>k. k" _ "\<lambda>k. k"] by (metis formula_semantics.simps(5))
      have 5: "F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not> F \<triangleright> S \<in> Collect fin_sat \<or> G \<triangleright> S \<in> Collect fin_sat" for F G
        unfolding fin_sat_def sat_def mem_Collect_eq using disj[of Imp F G _ Not _ "\<lambda>k. k"] by (metis formula_semantics.simps(3,6))
      have 6: "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<longrightarrow> F \<triangleright> S \<in> Collect fin_sat" for F unfolding fin_sat_def sat_def mem_Collect_eq using conj[of "\<lambda>F G. Not (Not F)" F F _ "\<lambda>k. k" "\<lambda>k. k"] by simp
      have 7: "\<^bold>\<not> (F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<triangleright> S \<in> Collect fin_sat \<or> \<^bold>\<not> G \<triangleright> S \<in> Collect fin_sat" for F G
        unfolding fin_sat_def sat_def mem_Collect_eq using disj[of "\<lambda>F G. Not (And F G)" F G _ Not _ Not] by (metis formula_semantics.simps(3,4))
      have 8: "\<forall>F G. \<^bold>\<not> (F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<triangleright> \<^bold>\<not> G \<triangleright> S \<in> Collect fin_sat" unfolding fin_sat_def sat_def mem_Collect_eq using conj[] by fastforce
      have 9: "\<forall>F G. \<^bold>\<not> (F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<triangleright> \<^bold>\<not> G \<triangleright> S \<in> Collect fin_sat" unfolding fin_sat_def sat_def mem_Collect_eq using conj[] by fastforce
      note 1 2 3 4 5 6 7 8 9
    }
    thus "pcp ?C" unfolding pcp_def by auto
  qed
  from pcp_sat 2 1 show ?l .
next
  assume ?l thus ?r unfolding sat_def fin_sat_def by blast
qed

end
