subsection\<open>Consistency\<close>

text\<open>We follow the proofs by Melvin Fitting~\cite{fitting1990first}.\<close>
theory Consistency
imports Sema
begin

definition "Hintikka S \<equiv> (
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<in> S \<and> G \<in> S)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<in> S \<or> G \<in> S)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<in> S)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S)
)"

lemma "Hintikka {Atom 0 \<^bold>\<and> ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), ((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), Atom 0, \<^bold>\<not>(\<^bold>\<not> (Atom 1)), Atom 1}"
  unfolding Hintikka_def by simp

theorem Hintikkas_lemma:
  assumes H: "Hintikka S"
  shows "sat S"
proof -
  from H[unfolded Hintikka_def]
  have H': "\<bottom> \<notin> S" 
    "Atom k \<in> S \<Longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<Longrightarrow> False"
    "F \<^bold>\<and> G \<in> S \<Longrightarrow> F \<in> S \<and> G \<in> S"
    "F \<^bold>\<or> G \<in> S \<Longrightarrow> F \<in> S \<or> G \<in> S"
    "F \<^bold>\<rightarrow> G \<in> S \<Longrightarrow> \<^bold>\<not>F \<in> S \<or> G \<in> S"
    "\<^bold>\<not> (\<^bold>\<not> F) \<in> S \<Longrightarrow> F \<in> S"
    "\<^bold>\<not> (F \<^bold>\<and> G) \<in> S \<Longrightarrow> \<^bold>\<not> F \<in> S \<or> \<^bold>\<not> G \<in> S"
    "\<^bold>\<not> (F \<^bold>\<or> G) \<in> S \<Longrightarrow> \<^bold>\<not> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    "\<^bold>\<not> (F \<^bold>\<rightarrow> G) \<in> S \<Longrightarrow> F \<in> S \<and> \<^bold>\<not> G \<in> S"
    for k F G by blast+
  let ?M = "\<lambda>k. Atom k \<in> S"
  have "(F \<in> S \<longrightarrow> (?M \<Turnstile> F)) \<and> (\<^bold>\<not> F \<in> S \<longrightarrow> (\<not>(?M \<Turnstile> F)))" for F
    by(induction F) (auto simp: H'(1) dest!: H'(2-))
  thus ?thesis unfolding sat_def by blast
qed

definition "pcp C \<equiv> (\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G. F \<^bold>\<and> G \<in> S \<longrightarrow> F \<triangleright> G \<triangleright> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<or> G \<in> S \<longrightarrow> F \<triangleright> S \<in> C \<or> G \<triangleright> S \<in> C)
\<and> (\<forall>F G. F \<^bold>\<rightarrow> G \<in> S \<longrightarrow> \<^bold>\<not>F \<triangleright> S \<in> C \<or> G \<triangleright> S \<in> C)
\<and> (\<forall>F. \<^bold>\<not> (\<^bold>\<not>F) \<in> S \<longrightarrow> F \<triangleright> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<and> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<triangleright> S \<in> C \<or> \<^bold>\<not> G \<triangleright> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<or> G) \<in> S \<longrightarrow> \<^bold>\<not> F \<triangleright> \<^bold>\<not> G \<triangleright> S \<in> C)
\<and> (\<forall>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G) \<in> S \<longrightarrow> F \<triangleright> \<^bold>\<not> G \<triangleright> S \<in> C)
)"

(* just some examples *)
lemma "pcp {}" "pcp {{}}" "pcp {{Atom 0}}" by (simp add: pcp_def)+
lemma "pcp {{(\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2},
   {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1))},
  {((\<^bold>\<not> (Atom 1)) \<^bold>\<rightarrow> Atom 2), \<^bold>\<not>(\<^bold>\<not> (Atom 1)),  Atom 1}}" by (auto simp add: pcp_def)

text\<open>Fitting uses uniform notation~\cite{smullyan1963unifying} for the definition of @{const pcp}. 
We try to mimic this, more to see whether it works than because it is ultimately necessary.\<close>
(* It does help a bit, occasionally. *)
    
inductive Con :: "'a formula => 'a formula => 'a formula => bool" where
"Con (And F G) F G" |
"Con (Not (Or F G)) (Not F) (Not G)" |
"Con (Not (Imp F G)) F (Not G)" |
"Con (Not (Not F)) F F"

inductive Dis :: "'a formula => 'a formula => 'a formula => bool" where
"Dis (Or F G) F G" |
"Dis (Imp F G) (Not F) G" |
"Dis (Not (And F G)) (Not F) (Not G)" |
"Dis (Not (Not F)) F F"

(* note that *)
lemma "Con (Not (Not F)) F F" "Dis (Not (Not F)) F F" by(intro Con.intros Dis.intros)+
(* i.e. \<^bold>\<not>\<^bold>\<not> is both Conjunctive and Disjunctive. I saw no reason to break this symmetry. *)

lemma con_dis_simps:
  "Con a1 a2 a3 = (a1 = a2 \<^bold>\<and> a3 \<or> (\<exists>F G. a1 = \<^bold>\<not> (F \<^bold>\<or> G) \<and> a2 = \<^bold>\<not> F \<and> a3 = \<^bold>\<not> G) \<or> (\<exists>G. a1 = \<^bold>\<not> (a2 \<^bold>\<rightarrow> G) \<and> a3 = \<^bold>\<not> G) \<or> a1 = \<^bold>\<not> (\<^bold>\<not> a2) \<and> a3 = a2)"
  "Dis a1 a2 a3 = (a1 = a2 \<^bold>\<or> a3 \<or> (\<exists>F G. a1 = F \<^bold>\<rightarrow> G \<and> a2 = \<^bold>\<not> F \<and> a3 = G) \<or> (\<exists>F G. a1 = \<^bold>\<not> (F \<^bold>\<and> G) \<and> a2 = \<^bold>\<not> F \<and> a3 = \<^bold>\<not> G) \<or> a1 = \<^bold>\<not> (\<^bold>\<not> a2) \<and> a3 = a2)"
  by(simp_all add: Con.simps Dis.simps)

lemma Hintikka_alt: "Hintikka S = (
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<and> H \<in> S)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<in> S \<or> H \<in> S)
)"  
  apply(simp add: Hintikka_def con_dis_simps)
  apply(rule iffI)
    (* simp only: \<emptyset> loops. :( *)
   subgoal by blast
  subgoal by safe metis+
done

lemma pcp_alt: "pcp C = (\<forall>S \<in> C.
  \<bottom> \<notin> S
\<and> (\<forall>k. Atom k \<in> S \<longrightarrow> \<^bold>\<not> (Atom k) \<in> S \<longrightarrow> False)
\<and> (\<forall>F G H. Con F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<triangleright> H \<triangleright> S \<in> C)
\<and> (\<forall>F G H. Dis F G H \<longrightarrow> F \<in> S \<longrightarrow> G \<triangleright> S \<in> C \<or> H \<triangleright> S \<in> C)
)"
  apply(simp add: pcp_def con_dis_simps)
  apply(rule iffI; unfold Ball_def; elim all_forward)
  by (auto simp add: insert_absorb split: formula.splits)
  
definition "subset_closed C \<equiv> (\<forall>S \<in> C. \<forall>s\<subseteq>S. s \<in> C)"
definition "finite_character C \<equiv> (\<forall>S. S \<in> C \<longleftrightarrow> (\<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C))"

lemma ex1: "pcp C \<Longrightarrow> \<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> subset_closed C'"
proof(intro exI[of _ "{s . \<exists>S \<in> C. s \<subseteq> S}"] conjI)
  let ?E = "{s. \<exists>S\<in>C. s \<subseteq> S}"
  show "C \<subseteq> ?E" by blast
  show "subset_closed ?E" unfolding subset_closed_def by blast
  assume C: \<open>pcp C\<close>
  show "pcp ?E" using C unfolding pcp_alt
    by (intro ballI conjI; simp; meson insertI1 rev_subsetD subset_insertI subset_insertI2)
qed

lemma sallI: "(\<And>s. s \<subseteq> S \<Longrightarrow> P s) \<Longrightarrow> \<forall>s \<subseteq> S. P s" by simp 

lemma ex2: 
  assumes fc: "finite_character C"
  shows "subset_closed C"
  unfolding subset_closed_def
proof (intro ballI sallI)
  fix s S
  assume e: \<open>S \<in> C\<close> and s: \<open>s \<subseteq> S\<close>
  hence *: "t \<subseteq> s \<Longrightarrow> t \<subseteq> S" for t by simp
  from fc have "t \<subseteq> S \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t unfolding finite_character_def using e by blast
  hence "t \<subseteq> s \<Longrightarrow> finite t \<Longrightarrow> t \<in> C" for t using * by simp
  with fc show \<open>s \<in> C\<close> unfolding finite_character_def by blast
qed

lemma
  assumes C: "pcp C"
  assumes S: "subset_closed C"
  shows ex3: "\<exists>C'. C \<subseteq> C' \<and> pcp C' \<and> finite_character C'"
proof(intro exI[of _ "C \<union> {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"] conjI)
  let ?E = " {S. \<forall>s \<subseteq> S. finite s \<longrightarrow> s \<in> C}"
  show "C \<subseteq> C \<union> ?E" by blast
  from S show "finite_character (C \<union> ?E)" unfolding finite_character_def subset_closed_def by blast
  note C'' = C[unfolded pcp_alt, THEN bspec]
    
  (* uniform notation. what did I learn? only slightly more elegant\<dots> *)
  have CON: "G \<triangleright> H \<triangleright> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" if si: "\<And>s. \<lbrakk>s\<subseteq>S; finite s\<rbrakk> \<Longrightarrow> s \<in> C" and
    un: "Con F G H" and el: " F \<in> S" for F G H S proof -
    have k: "\<forall>s \<subseteq> S. finite s \<longrightarrow> F \<in> s \<longrightarrow> G \<triangleright> H \<triangleright> s \<in> C"
      using si un C'' by simp
    have "G \<triangleright> H \<triangleright> S \<in> ?E"
      unfolding mem_Collect_eq Un_iff proof safe
      fix s
      assume "s \<subseteq> G \<triangleright> H \<triangleright> S" and f: "finite s"
      hence "F \<triangleright> (s - {G,H}) \<subseteq> S" using el by blast
      with k f have "G \<triangleright> H \<triangleright> F \<triangleright> (s - {G,H}) \<in> C" by simp
      hence "F \<triangleright> G \<triangleright> H \<triangleright> s \<in> C" using insert_absorb by fastforce
      thus "s \<in> C" using S unfolding subset_closed_def by fast  
    qed
    thus "G \<triangleright> H \<triangleright> S \<in> C \<union> ?E" by simp
  qed
  have DIS: "G \<triangleright> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C} \<or> H \<triangleright> S \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
    if si: "\<And>s. s\<subseteq>S \<Longrightarrow> finite s \<Longrightarrow> s \<in> C" and un: "Dis F G H" and el: "F \<in> S"
    for F G H S proof -
    have l: "\<exists>I\<in>{G, H}. I \<triangleright> s1 \<in> C \<and> I \<triangleright> s2 \<in> C" 
      if "s1 \<subseteq> S" "finite s1" "F \<in> s1" 
         "s2 \<subseteq> S" "finite s2" "F \<in> s2" for s1 s2
    proof -
      let ?s = "s1 \<union> s2"
      have "?s \<subseteq> S" "finite ?s" using that by simp_all 
      with si have "?s \<in> C" by simp
      moreover have "F \<in> ?s" using that by simp
      ultimately have "\<exists>I\<in>{G,H}. I \<triangleright> ?s \<in> C"
        using C'' un by simp
      thus "\<exists>I\<in>{G,H}. I \<triangleright> s1 \<in> C \<and> I \<triangleright> s2 \<in> C"
        by (meson S[unfolded subset_closed_def, THEN bspec] insert_mono sup.cobounded2 sup_ge1)
    qed
    have m: "\<lbrakk>s1 \<subseteq> S; finite s1; F \<in> s1; G \<triangleright> s1 \<notin> C; s2 \<subseteq> S; finite s2; F \<in> s2; H \<triangleright> s2 \<notin> C\<rbrakk> \<Longrightarrow> False" for s1 s2
      using l by blast
    have "False" if "s1 \<subseteq> S" "finite s1" "G \<triangleright> s1 \<notin> C" "s2 \<subseteq> S" "finite s2" "H \<triangleright> s2 \<notin> C" for s1 s2
    proof -
      have *: "F \<triangleright> s1 \<subseteq> S" "finite (F \<triangleright> s1)" "F \<in> F \<triangleright> s1" if  "s1 \<subseteq> S" "finite s1" for s1
        using that el by simp_all
      have  "G \<triangleright> F \<triangleright> s1 \<notin> C" "H \<triangleright> F \<triangleright> s2 \<notin> C" 
        by (meson S insert_mono subset_closed_def subset_insertI that(3,6))+
      from m[OF *[OF that(1-2)] this(1) *[OF that(4-5)] this(2)]
      show False .
    qed
    hence "G \<triangleright> S \<in> ?E \<or> H \<triangleright> S \<in> ?E"
      unfolding mem_Collect_eq Un_iff
      by (metis (no_types, lifting) finite_Diff insert_Diff si subset_insert_iff)
    thus "G \<triangleright> S \<in> C \<union> ?E \<or> H \<triangleright> S \<in> C \<union> ?E" by blast
  qed
    
  (* this proof does benefit from uniform notation a bit. Before it was introduced,
     the subclaims CON, DIS had to be stated as *)  
  have CON': "\<And>f2 g2 h2 F2 G2 S2. \<lbrakk>\<And>s. \<lbrakk>s \<in> C; h2 F2 G2 \<in> s\<rbrakk> \<Longrightarrow> f2 F2 \<triangleright> s \<in> C \<or> g2 G2 \<triangleright> s \<in> C; 
                                   \<forall>s\<subseteq>S2. finite s \<longrightarrow> s \<in> C; h2 F2 G2 \<in> S2; False\<rbrakk>
      \<Longrightarrow> f2 F2 \<triangleright> S2 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C} \<or> g2 G2 \<triangleright> S2 \<in> C \<union> {S. \<forall>s\<subseteq>S. finite s \<longrightarrow> s \<in> C}" 
    by fast
  (* (without the False, obviously). The proof of the subclaim does not change gravely, 
      but the f2 g2 h2 have to be instantiated manually upon use (with, e.g., id Not (\<lambda>F G. \<^bold>\<not>(F \<^bold>\<rightarrow> G))),
      and there were multiple working instantiations. Generally not as beautiful. *)

  show "pcp (C \<union> ?E)" unfolding pcp_alt
    apply(intro ballI conjI; elim UnE; (unfold mem_Collect_eq)?)
           subgoal using C'' by blast
          subgoal using C'' by blast
         subgoal using C'' by (simp;fail)
        subgoal by (meson C'' empty_subsetI finite.emptyI finite_insert insert_subset subset_insertI)
       subgoal using C'' by simp
      subgoal using CON by simp
     subgoal using C'' by blast
    subgoal using DIS by simp
  done
qed

primrec pcp_seq where
"pcp_seq C S 0 = S" |
"pcp_seq C S (Suc n) = (
  let Sn = pcp_seq C S n; Sn1 = from_nat n \<triangleright> Sn in
  if Sn1 \<in> C then Sn1 else Sn
)"

lemma pcp_seq_in: "pcp C \<Longrightarrow> S \<in> C \<Longrightarrow> pcp_seq C S n \<in> C"
proof(induction n)
  case (Suc n)
  hence "pcp_seq C S n \<in> C" by simp
  thus ?case by(simp add: Let_def)
qed simp
  
lemma pcp_seq_mono: "n \<le> m \<Longrightarrow> pcp_seq C S n \<subseteq> pcp_seq C S m"
proof(induction m)
  case (Suc m)
  thus ?case by(cases "n = Suc m"; simp add: Let_def; blast)
qed simp

lemma pcp_seq_UN: "\<Union>{pcp_seq C S n|n. n \<le> m} = pcp_seq C S m"
proof(induction m)
  case (Suc m)
  have "{f n |n. n \<le> Suc m} = f (Suc m) \<triangleright> {f n |n. n \<le> m}" for f using le_Suc_eq by auto
  hence "{pcp_seq C S n |n. n \<le> Suc m} = pcp_seq C S (Suc m) \<triangleright> {pcp_seq C S n |n. n \<le> m}" .
  hence "\<Union>{pcp_seq C S n |n. n \<le> Suc m} = \<Union>{pcp_seq C S n |n. n \<le> m} \<union> pcp_seq C S (Suc m)" by auto
  thus ?case using Suc pcp_seq_mono by blast
qed simp
  
lemma wont_get_added: "(F :: ('a :: countable) formula) \<notin> pcp_seq C S (Suc (to_nat F)) \<Longrightarrow> F \<notin> pcp_seq C S (Suc (to_nat F) + n)"
text\<open>We don't necessarily have @{term "n = to_nat (from_nat n)"}, so this doesn't hold.\<close>
oops

definition "pcp_lim C S \<equiv> \<Union>{pcp_seq C S n|n. True}"
  
lemma pcp_seq_sub: "pcp_seq C S n \<subseteq> pcp_lim C S"
  unfolding pcp_lim_def by(induction n; blast)
    
lemma pcp_lim_inserted_at_ex: "x \<in> pcp_lim C S \<Longrightarrow> \<exists>k. x \<in> pcp_seq C S k"
  unfolding pcp_lim_def by blast

lemma pcp_lim_in:
  assumes c: "pcp C"
  and el: "S \<in> C"
  and sc: "subset_closed C"
  and fc: "finite_character C"
  shows "pcp_lim C S \<in> C" (is "?cl \<in> C")
proof -
  from pcp_seq_in[OF c el, THEN allI] have "\<forall>n. pcp_seq C S n \<in> C" .
  hence "\<forall>m. \<Union>{pcp_seq C S n|n. n \<le> m} \<in> C" unfolding pcp_seq_UN .
  
  have "\<forall>s \<subseteq> ?cl. finite s \<longrightarrow> s \<in> C"
  proof safe
    fix s :: "'a formula set"
    have "pcp_seq C S (Suc (Max (to_nat ` s))) \<subseteq> pcp_lim C S" using pcp_seq_sub by blast
    assume \<open>finite s\<close> \<open>s \<subseteq> pcp_lim C S\<close>
    hence "\<exists>k. s \<subseteq> pcp_seq C S k" 
    proof(induction s rule: finite_induct) 
      case (insert x s)
      hence "\<exists>k. s \<subseteq> pcp_seq C S k" by fast
      then guess k1 ..
      moreover obtain k2 where "x \<in> pcp_seq C S k2"
        by (meson pcp_lim_inserted_at_ex insert.prems insert_subset)
      ultimately have "x \<triangleright> s \<subseteq> pcp_seq C S (max k1 k2)"
        by (meson pcp_seq_mono dual_order.trans insert_subset max.bounded_iff order_refl subsetCE)
      thus ?case by blast
    qed simp
    with pcp_seq_in[OF c el] sc
    show "s \<in> C" unfolding subset_closed_def by blast
  qed
  thus "?cl \<in> C" using fc unfolding finite_character_def by blast
qed
  
lemma cl_max:
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  assumes el: "K \<in> C"
  assumes su: "pcp_lim C S \<subseteq> K"
  shows "pcp_lim C S = K" (is ?e)
proof (rule ccontr)
  assume \<open>\<not>?e\<close>
  with su have "pcp_lim C S \<subset> K" by simp
  then obtain F where e: "F \<in> K" and ne: "F \<notin> pcp_lim C S" by blast
  from ne have "F \<notin> pcp_seq C S (Suc (to_nat F))" using pcp_seq_sub by fast
  hence 1: "F \<triangleright> pcp_seq C S (to_nat F) \<notin> C" by (simp add: Let_def split: if_splits)
  have "F \<triangleright> pcp_seq C S (to_nat F) \<subseteq> K" using pcp_seq_sub e su by blast
  hence "F \<triangleright> pcp_seq C S (to_nat F) \<in> C" using sc unfolding subset_closed_def using el by blast
  with 1 show False ..
qed

lemma cl_max':
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  shows "F \<triangleright> pcp_lim C S \<in> C \<Longrightarrow> F \<in> pcp_lim C S"
    "F \<triangleright> G \<triangleright> pcp_lim C S \<in> C \<Longrightarrow> F \<in> pcp_lim C S \<and> G \<in> pcp_lim C S"
using cl_max[OF assms] by blast+

lemma pcp_lim_Hintikka:
  assumes c: "pcp C"
  assumes sc: "subset_closed C"
  assumes fc: "finite_character C"
  assumes el: "S \<in> C"
  shows "Hintikka (pcp_lim C S)"
proof -
  let ?cl = "pcp_lim C S"
  have "?cl \<in> C" using pcp_lim_in[OF c el sc fc] .
  from c[unfolded pcp_alt, THEN bspec, OF this]
  have d: "\<bottom> \<notin> ?cl"
    "Atom k \<in> ?cl \<Longrightarrow> \<^bold>\<not> (Atom k) \<in> ?cl \<Longrightarrow> False"
    "Con F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> G \<triangleright> H \<triangleright> ?cl \<in> C"
    "Dis F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> G \<triangleright> ?cl \<in> C \<or> H \<triangleright> ?cl \<in> C"
  for k F G H by blast+
  have
    "Con F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> G \<in> ?cl \<and> H \<in> ?cl"
    "Dis F G H \<Longrightarrow> F \<in> ?cl \<Longrightarrow> G \<in> ?cl \<or> H \<in> ?cl"
    for F G H
    by(auto dest: d(3-) cl_max'[OF c sc])
  with d(1,2) show ?thesis unfolding Hintikka_alt by fast
qed
  
theorem pcp_sat: \<comment> \<open>model existence theorem\<close>
  fixes S :: "'a :: countable formula set"
  assumes c: "pcp C"
  assumes el: "S \<in> C"
  shows "sat S"
proof -
  note [[show_types]]
  from c obtain Ce where "C \<subseteq> Ce" "pcp Ce" "subset_closed Ce" "finite_character Ce" using ex1[where 'a='a] ex2[where 'a='a] ex3[where 'a='a]
    by (meson dual_order.trans ex2)
  have "S \<in> Ce" using \<open>C \<subseteq> Ce\<close> el ..
  with pcp_lim_Hintikka \<open>pcp Ce\<close> \<open>subset_closed Ce\<close> \<open>finite_character Ce\<close>
  have  "Hintikka (pcp_lim Ce S)" .
  with Hintikkas_lemma have "sat (pcp_lim Ce S)" .
  moreover have "S \<subseteq> pcp_lim Ce S" using pcp_seq.simps(1) pcp_seq_sub by fast
  ultimately show ?thesis unfolding sat_def by fast
qed
(* This and Hintikka's lemma are the only two where we need semantics. 
   Still, I don't think it's meaningful to separate those two into an extra theory. *)

end
