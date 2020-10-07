subsection\<open>Transforming SC proofs into proofs of CNFs\<close>
theory LSC
imports CNF_Formulas SC_Cut
begin

text\<open>Left handed SC with NNF transformation:\<close>
inductive LSC ("(_ \<Rightarrow>\<^sub>n)" [53]) where
\<comment> \<open>logic:\<close>
Ax: "\<^bold>\<not>(Atom k),Atom k,\<Gamma> \<Rightarrow>\<^sub>n" |
BotL: "\<bottom>,\<Gamma> \<Rightarrow>\<^sub>n" |
AndL: "F,G,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> F\<^bold>\<and>G,\<Gamma> \<Rightarrow>\<^sub>n" |               
OrL: "F,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> G,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> F\<^bold>\<or>G,\<Gamma> \<Rightarrow>\<^sub>n" |
\<comment> \<open>nnf rules:\<close>
NotOrNNF: "\<^bold>\<not>F,\<^bold>\<not>G,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<^bold>\<not>(F\<^bold>\<or>G),\<Gamma> \<Rightarrow>\<^sub>n" |
NotAndNNF: "\<^bold>\<not>F,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<^bold>\<not>G,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<^bold>\<not>(F\<^bold>\<and>G),\<Gamma> \<Rightarrow>\<^sub>n" |
ImpNNF: "\<^bold>\<not>F,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> G,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> F\<^bold>\<rightarrow>G,\<Gamma> \<Rightarrow>\<^sub>n" |
NotImpNNF: "F,\<^bold>\<not>G,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<^bold>\<not>(F\<^bold>\<rightarrow>G),\<Gamma> \<Rightarrow>\<^sub>n" |
NotNotNNF: "F,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<^bold>\<not>(\<^bold>\<not>F),\<Gamma> \<Rightarrow>\<^sub>n"
lemmas LSC.intros[intro!]
text\<open>You can prove that derivability in @{const SCp} is invariant to @{const nnf},
and then transform @{const SCp} to @{const LSC} while assuming NNF.
However, the transformation introduces the trouble of handling the right side of @{const SCp}.
The idea behind this is that handling the transformation is easier when not requiring NNF.\<close>

text\<open>One downside of the whole approach is that we often need everything to be in NNF. To shorten:\<close>
abbreviation "is_nnf_mset \<Gamma> \<equiv> \<forall>x \<in> set_mset \<Gamma>. is_nnf x"

lemma "\<Gamma> \<Rightarrow> {#} \<Longrightarrow> is_nnf_mset \<Gamma> \<Longrightarrow> \<Gamma> \<Rightarrow>\<^sub>n"
proof(induction \<Gamma> "{#}::'a formula multiset " rule: SCp.induct)
  case (BotL \<Gamma>)
  then obtain \<Gamma>' where "\<Gamma> = \<bottom>,\<Gamma>'" by(meson multi_member_split)
  thus ?case by auto
next
  case (Ax A \<Gamma>) hence False by simp thus ?case ..
  (* this case makes you think that there's something wrong with this proof *)
next
  case (AndL \<Gamma> F G) 
  hence IH: "\<Gamma>, F, G \<Rightarrow>\<^sub>n" by force
  thus ?case by auto
next
  case (NotL) thus ?case
  (* this demonstrates it *)
oops

lemma LSC_to_SC:
  shows "\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<Gamma> \<Rightarrow> {#}"
proof(induction rule: LSC.induct)
qed (auto dest!: NotL_inv intro!: SCp.intros(3-) intro: extended_Ax)

lemma SC_to_LSC:
  assumes "\<Gamma> \<Rightarrow> \<Delta>"
  shows "\<Gamma> + (image_mset Not \<Delta>) \<Rightarrow>\<^sub>n"
proof -
  have GO[simp]: 
    "NO_MATCH {# B #} F \<Longrightarrow> (F,S) + T = F, (S+T)" 
    "NO_MATCH {# B #} S \<Longrightarrow> S + (F,T) = F, (S+T)"
    "NO_MATCH (\<^bold>\<not>H) F \<Longrightarrow> F,\<^bold>\<not>G,S = \<^bold>\<not>G,F,S"
    for B S F G H T by simp_all
  from assms show ?thesis
  proof(induction rule: SCp.induct)
    case (BotL \<Gamma>)
    then obtain \<Gamma>' where "\<Gamma> = \<bottom>,\<Gamma>'" by(meson multi_member_split)
    thus ?case by auto
  next
    case (Ax k \<Gamma> \<Delta>)
    then obtain \<Gamma>' \<Delta>' where "\<Gamma> = Atom k, \<Gamma>'" "\<Delta> = Atom k, \<Delta>'" by(meson multi_member_split)
    thus ?case using LSC.Ax by simp
  qed auto
qed

corollary SC_LSC: "\<Gamma> \<Rightarrow> {#} \<longleftrightarrow> \<Gamma> \<Rightarrow>\<^sub>n" using SC_to_LSC LSC_to_SC by fastforce

text\<open>The nice thing: The NNF-Transformation is even easier to show on the one-sided variant.\<close>
(* part of that is because it is written down in a way that is easier to tackle for the solvers *)
lemma LSC_NNF: "\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> image_mset nnf \<Gamma> \<Rightarrow>\<^sub>n"
proof(induction rule: LSC.induct) 
  (* auto solved all, but I want to know what's going on. *)
  case (NotOrNNF F G \<Gamma>)
  from NotOrNNF.IH have "nnf (\<^bold>\<not> F), nnf (\<^bold>\<not> G), image_mset nnf \<Gamma> \<Rightarrow>\<^sub>n" by simp
  with LSC.AndL have "nnf (\<^bold>\<not> F) \<^bold>\<and> nnf (\<^bold>\<not> G), image_mset nnf \<Gamma> \<Rightarrow>\<^sub>n" .
  thus ?case by simp
next
  case (AndL F G \<Gamma>)
  from AndL.IH have "nnf F, nnf G, image_mset nnf \<Gamma> \<Rightarrow>\<^sub>n" by simp
  with LSC.AndL[where 'a='a] have "nnf F \<^bold>\<and> nnf G, image_mset nnf \<Gamma> \<Rightarrow>\<^sub>n" by simp
  thus ?case by simp
next  
qed (auto, metis add_mset_commute)

lemma LSC_NNF_back: "image_mset nnf \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<Gamma> \<Rightarrow>\<^sub>n"
proof(induction "image_mset nnf \<Gamma>" rule: LSC.induct) 
oops
(* should be possible, but I don't need it. *)

text\<open>If we got rid of the rules for NNF, we could call it Gentzen-Schütte-calculus. But it turned out that not doing that works quite fine.\<close>
 
text\<open>If you stare at left-handed Sequent calcului for too long, and they start staring back:
Try imagining that there is a @{term \<bottom>} on the right hand side.
Also, bear in mind that provability of @{term "\<Gamma> \<Rightarrow>\<^sub>n"} and satisfiability of @{term "\<Gamma>"} are opposites here.\<close>

lemma LHCut:
  assumes "F,\<Gamma> \<Rightarrow>\<^sub>n" "\<^bold>\<not>F, \<Gamma> \<Rightarrow>\<^sub>n"
  shows "\<Gamma> \<Rightarrow>\<^sub>n"
using assms
unfolding SC_LSC[symmetric]
using NotL_inv cut by blast

lemma 
 shows LSC_AndL_inv: "F\<^bold>\<and>G,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> F,G,\<Gamma> \<Rightarrow>\<^sub>n"
 and   LSC_OrL_inv: "F\<^bold>\<or>G,\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> F,\<Gamma> \<Rightarrow>\<^sub>n \<and> G,\<Gamma> \<Rightarrow>\<^sub>n"
 using SC_LSC AndL_inv OrL_inv by blast+
lemmas LSC_invs = LSC_AndL_inv LSC_OrL_inv
(* these are actually suitable as dest rules. But the proofs are usually slow, so I'd rather not. *)

(* direct proof is easy here and it saves us the hassle of the nnf-assumption *)
lemma LSC_weaken_set: "\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<Gamma> + \<Theta> \<Rightarrow>\<^sub>n"
  by(induction rule: LSC.induct) (auto simp: add.assoc)
lemma LSC_weaken: "\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> F,\<Gamma> \<Rightarrow>\<^sub>n"
  using LSC_weaken_set by (metis add_mset_add_single)

lemma LSC_Contract:
  assumes sfp: "F, F, \<Gamma> \<Rightarrow>\<^sub>n"
  shows "F, \<Gamma> \<Rightarrow>\<^sub>n"
  using SC_LSC contractL sfp by blast

lemma cnf:
  shows 
    "F \<^bold>\<or> (G \<^bold>\<and> H), \<Gamma> \<Rightarrow>\<^sub>n \<longleftrightarrow> (F \<^bold>\<or> G) \<^bold>\<and> (F \<^bold>\<or> H), \<Gamma> \<Rightarrow>\<^sub>n" (is "?l1 \<longleftrightarrow> ?r1")
    "(G \<^bold>\<and> H) \<^bold>\<or> F, \<Gamma> \<Rightarrow>\<^sub>n \<longleftrightarrow> (G \<^bold>\<or> F) \<^bold>\<and> (H \<^bold>\<or> F), \<Gamma> \<Rightarrow>\<^sub>n" (is "?l2 \<longleftrightarrow> ?r2")
proof -
  have GO(* get out *)[simp]:   
    "F,G,S \<Rightarrow>\<^sub>n \<Longrightarrow> G,F,S \<Rightarrow>\<^sub>n"
    for F G :: "'a formula" and S by (simp add: add_mset_commute)
  have ?r1 if ?l1 proof -
    from \<open>?l1\<close>[THEN LSC_invs(2)] have f: "F, \<Gamma> \<Rightarrow>\<^sub>n" "G \<^bold>\<and> H, \<Gamma> \<Rightarrow>\<^sub>n" by simp_all
    from this(2)[THEN LSC_invs(1)] have gh: "G, H, \<Gamma> \<Rightarrow>\<^sub>n" by simp
    show ?r1 using f gh by(auto dest!: LSC_invs simp: LSC_weaken)
  qed
  moreover have ?r2 if ?l2 proof -
    from \<open>?l2\<close> have f: "F, \<Gamma> \<Rightarrow>\<^sub>n" "G, H, \<Gamma> \<Rightarrow>\<^sub>n" by(auto dest!: LSC_invs)
    thus ?r2  by(auto dest!: LSC_invs simp: LSC_weaken)
  qed
  moreover have ?l1 if ?r1 proof -
    from \<open>?r1\<close>[THEN LSC_invs(1)] have *: "F \<^bold>\<or> G, F \<^bold>\<or> H, \<Gamma> \<Rightarrow>\<^sub>n" by simp
    hence "F, \<Gamma> \<Rightarrow>\<^sub>n" "G, H, \<Gamma> \<Rightarrow>\<^sub>n" by (auto elim!: LSC_Contract dest!: LSC_invs)
    thus ?l1 by(intro LSC.intros)
  qed
  moreover have ?l2 if ?r2 proof -
    from \<open>?r2\<close>[THEN LSC_invs(1)] have *: "G \<^bold>\<or> F, H \<^bold>\<or> F, \<Gamma> \<Rightarrow>\<^sub>n" by simp
    hence "F, \<Gamma> \<Rightarrow>\<^sub>n" "G, H, \<Gamma> \<Rightarrow>\<^sub>n" by(auto elim!: LSC_Contract dest!: LSC_invs)
    thus ?l2 by(intro LSC.intros)
  qed
  ultimately show "?l1 \<longleftrightarrow> ?r1" "?l2 \<longleftrightarrow> ?r2" by argo+
qed

text\<open>
  Interestingly, the DNF congruences are a lot easier to show, requiring neither weakening nor contraction.
  The reasons are to be sought in the asymmetries between the rules for @{const And} and @{const Or}.
\<close>
lemma dnf:
  shows 
    "F \<^bold>\<and> (G \<^bold>\<or> H), \<Gamma> \<Rightarrow>\<^sub>n \<longleftrightarrow> (F \<^bold>\<and> G) \<^bold>\<or> (F \<^bold>\<and> H), \<Gamma> \<Rightarrow>\<^sub>n" (is "?t1")
    "(G \<^bold>\<or> H) \<^bold>\<and> F, \<Gamma> \<Rightarrow>\<^sub>n \<longleftrightarrow> (G \<^bold>\<and> F) \<^bold>\<or> (H \<^bold>\<and> F), \<Gamma> \<Rightarrow>\<^sub>n" (is "?t2")
proof -
    have GO(* get out *)[simp]:
    "F,G,S \<Rightarrow>\<^sub>n \<Longrightarrow> G,F,S \<Rightarrow>\<^sub>n"
    for F G H I J S by(simp_all add: add_mset_commute)
    show ?t1 ?t2 by(auto dest!: LSC_invs)
qed

lemma LSC_sim_Resolution1:
  assumes R: "S \<^bold>\<or> T, \<Gamma> \<Rightarrow>\<^sub>n"
  shows "Atom k \<^bold>\<or> S, (\<^bold>\<not>(Atom k)) \<^bold>\<or> T, \<Gamma> \<Rightarrow>\<^sub>n"
proof -
  from R have r: "T, \<Gamma> \<Rightarrow>\<^sub>n" "S, \<Gamma> \<Rightarrow>\<^sub>n" by(auto dest: LSC_invs)
  show ?thesis proof(rule LHCut[where F="Atom k"])
    have 2: "T, Atom k, Atom k \<^bold>\<or> S, \<Gamma> \<Rightarrow>\<^sub>n" using LSC_weaken r(1) by auto
    hence " \<^bold>\<not> (Atom k) \<^bold>\<or> T, Atom k, Atom k \<^bold>\<or> S, \<Gamma> \<Rightarrow>\<^sub>n" by auto
    thus "Atom k, Atom k \<^bold>\<or> S, \<^bold>\<not> (Atom k) \<^bold>\<or> T, \<Gamma> \<Rightarrow>\<^sub>n" 
      by(auto dest!: LSC_invs) (metis add_mset_commute)
  next text\<open>analogously\<close>(*<*)
    have 2: "S, \<^bold>\<not>(Atom k), \<^bold>\<not>(Atom k) \<^bold>\<or> T, \<Gamma> \<Rightarrow>\<^sub>n" using LSC_weaken r(2) by auto
    hence "Atom k \<^bold>\<or> S, \<^bold>\<not> (Atom k), \<^bold>\<not> (Atom k) \<^bold>\<or> T, \<Gamma> \<Rightarrow>\<^sub>n" using LSC_weaken
      by(auto dest!: LSC_invs) blast
    from this (*>*)
    show "\<^bold>\<not> (Atom k), Atom k \<^bold>\<or> S, \<^bold>\<not> (Atom k) \<^bold>\<or> T, \<Gamma> \<Rightarrow>\<^sub>n" by simp
  qed
qed

lemma
  LSC_need_it_once_have_many:
  assumes el: "A \<in> set F"
  assumes once: "form_of_lit A \<^bold>\<or> disj_of_clause (removeAll A F),\<Gamma> \<Rightarrow>\<^sub>n"
  shows "disj_of_clause F,\<Gamma> \<Rightarrow>\<^sub>n"
using assms
proof(induction F)
  case Nil hence False by simp thus ?case ..
next (* there might be a smarter way to prove this by splitting F into two lists\<dots> but nah. *)
  case (Cons f F) 
  thus ?case proof(cases "A = f")
    case True
    with Cons.prems have ihm: "form_of_lit A \<^bold>\<or> disj_of_clause (removeAll A F), \<Gamma> \<Rightarrow>\<^sub>n" by simp
    with True have split: "form_of_lit f, \<Gamma> \<Rightarrow>\<^sub>n" "disj_of_clause (removeAll A F), \<Gamma> \<Rightarrow>\<^sub>n" 
      by (auto dest!: LSC_invs(2))
    from Cons.IH[OF _ ihm] have "A \<in> set F \<Longrightarrow> disj_of_clause F, \<Gamma> \<Rightarrow>\<^sub>n" .
    with split(2) have "disj_of_clause F, \<Gamma> \<Rightarrow>\<^sub>n" by(cases "A \<in> set F") simp_all
    with split(1) show ?thesis by auto
  next
    case False
    with Cons.prems(2) have prem: "form_of_lit A, \<Gamma> \<Rightarrow>\<^sub>n" "form_of_lit f, \<Gamma> \<Rightarrow>\<^sub>n" "disj_of_clause (removeAll A F), \<Gamma> \<Rightarrow>\<^sub>n" 
       by (auto dest!: LSC_invs(2))
    hence d: "form_of_lit A \<^bold>\<or> disj_of_clause (removeAll A F), \<Gamma> \<Rightarrow>\<^sub>n" by blast
    from False Cons.prems have el: "A \<in> set F"  by simp
    from Cons.IH[OF el d] have "disj_of_clause F, \<Gamma> \<Rightarrow>\<^sub>n" .
    with prem(2) show ?thesis by auto
 qed
qed

(* LSC_sim_Resolution1 is the naive summer child that requires everything to be in the right order. Here comes the real fun *)
lemma LSC_Sim_resolution_la:
  fixes k :: 'a
  assumes R: "disj_of_clause (removeAll (k\<^sup>+) F @ removeAll (k\<inverse>) G), \<Gamma> \<Rightarrow>\<^sub>n"
  assumes el: "k\<^sup>+ \<in> set F" "k\<inverse> \<in> set G"
  shows "disj_of_clause F, disj_of_clause G, \<Gamma> \<Rightarrow>\<^sub>n"
proof -
  have LSC_or_assoc: "(F \<^bold>\<or> G) \<^bold>\<or> H, \<Gamma> \<Rightarrow>\<^sub>n \<longleftrightarrow> F \<^bold>\<or> (G \<^bold>\<or> H), \<Gamma> \<Rightarrow>\<^sub>n" if "is_nnf F" "is_nnf G" "is_nnf H" for F G H
    using that by(auto dest!: LSC_invs(2))
  have dd: "disj_of_clause (F @ G), \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> disj_of_clause F \<^bold>\<or> disj_of_clause G, \<Gamma> \<Rightarrow>\<^sub>n" for F G
    by(induction F) (auto dest!: LSC_invs(2) simp add: LSC_or_assoc)
  from LSC_sim_Resolution1[OF dd[OF R]]
  have unord: "Atom k \<^bold>\<or> disj_of_clause (removeAll (k\<^sup>+) F), \<^bold>\<not> (Atom k) \<^bold>\<or> disj_of_clause (removeAll (k\<inverse>) G), \<Gamma> \<Rightarrow>\<^sub>n" .
  show ?thesis
    using LSC_need_it_once_have_many[OF el(1)] LSC_need_it_once_have_many[OF el(2)] unord
    by(simp add: add_mset_commute del: sc_insertion_ordering)
qed

lemma two_list_induct[case_names Nil Cons]: "P [] [] \<Longrightarrow> (\<And>a S T. P S T \<Longrightarrow> P (a # S) T &&& P S (a # T)) \<Longrightarrow> P S T"
  apply(induction S)
   apply(induction T)
    apply(simp_all)
done

lemma distrib1: "\<lbrakk>F, \<Gamma> \<Rightarrow>\<^sub>n; image_mset disj_of_clause (mset G) + \<Gamma> \<Rightarrow>\<^sub>n\<rbrakk>
    \<Longrightarrow> mset (map (\<lambda>d. F \<^bold>\<or> disj_of_clause d) G) + \<Gamma> \<Rightarrow>\<^sub>n"
(* surprisingly, the proof having a \<^bold>\<and> instead of the \<^bold>\<or> looks very similar. Yes, I mistook the two at some point\<dots> and downstream, where this is used, I only had to do a few text replacements. makes you really wonder whether what you're proving is meaningful. *)
proof(induction G arbitrary: \<Gamma>)
  have GO(* get out *)[simp]:
   "NO_MATCH ({#I\<^bold>\<or>J#}) H \<Longrightarrow> H+{#F\<^bold>\<or>G#}+S = F\<^bold>\<or>G,H+S"
   for F G H S I J by(simp_all add: add_mset_commute)
  case (Cons g G)
  from \<open>F, \<Gamma> \<Rightarrow>\<^sub>n\<close> have 1: "F, disj_of_clause g, \<Gamma> \<Rightarrow>\<^sub>n" by (metis LSC_weaken add_mset_commute)
  from \<open>image_mset disj_of_clause (mset (g # G)) + \<Gamma> \<Rightarrow>\<^sub>n\<close> 
  have 2: "image_mset disj_of_clause (mset G) + (disj_of_clause g, \<Gamma>) \<Rightarrow>\<^sub>n" by(simp add: add_mset_commute)
  from Cons.IH[OF 1 2] have IH: "disj_of_clause g, mset (map (\<lambda>d. F \<^bold>\<or> disj_of_clause d) G) + \<Gamma> \<Rightarrow>\<^sub>n" 
    by(simp add: add_mset_commute)
  from \<open>F, \<Gamma> \<Rightarrow>\<^sub>n\<close> have 3: "F, mset (map (\<lambda>d. F \<^bold>\<or> disj_of_clause d) G) + \<Gamma> \<Rightarrow>\<^sub>n"
    using LSC_weaken_set by (metis add.assoc add.commute add_mset_add_single)
  from IH 3 show ?case by auto
qed simp

lemma mset_concat_map_cons:
  "mset (concat (map (\<lambda>c. F c # G c) S)) = mset (map F S) + mset (concat (map G S))"
by(induction S; simp add: add_mset_commute)

lemma distrib: "
  image_mset disj_of_clause (mset F) + \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> 
  image_mset disj_of_clause (mset G) + \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow>
  mset [disj_of_clause c \<^bold>\<or> disj_of_clause d. c \<leftarrow> F, d \<leftarrow> G] + \<Gamma> \<Rightarrow>\<^sub>n"
proof(induction F G arbitrary: \<Gamma> rule: two_list_induct)
  case (Cons a F G)
  case 1
  from \<open>image_mset disj_of_clause (mset (a # F)) + \<Gamma> \<Rightarrow>\<^sub>n\<close>
  have a: "disj_of_clause a, image_mset disj_of_clause (mset F) + \<Gamma> \<Rightarrow>\<^sub>n" by(simp add: add_mset_commute)
  from \<open>image_mset disj_of_clause (mset G) + \<Gamma> \<Rightarrow>\<^sub>n\<close>
  have b: "image_mset disj_of_clause (mset G) + (image_mset disj_of_clause (mset F) + \<Gamma>) \<Rightarrow>\<^sub>n"
   and c: "image_mset disj_of_clause (mset G) + (mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) G) + \<Gamma>) \<Rightarrow>\<^sub>n"
    using LSC_weaken_set by (metis add.commute union_assoc)+
  from distrib1[OF a b]
  have "image_mset disj_of_clause (mset F) + (mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) G) + \<Gamma>) \<Rightarrow>\<^sub>n" 
    by (simp add: union_lcomm)
  from Cons[OF this c]
  have "mset (concat (map (\<lambda>c. map (\<lambda>d. disj_of_clause c \<^bold>\<or> disj_of_clause d) G) F)) +
  (mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) G) + \<Gamma>) \<Rightarrow>\<^sub>n" .
  thus ?case by(simp add: add.commute union_assoc)
next
  case (Cons a F G) case 2 text\<open>Just the whole thing again, with slightly more mset magic and swapping things around.\<close>
  from \<open>image_mset disj_of_clause (mset (a # G)) + \<Gamma> \<Rightarrow>\<^sub>n\<close>
  have a: "disj_of_clause a, image_mset disj_of_clause (mset G) + \<Gamma> \<Rightarrow>\<^sub>n" by(simp add: add_mset_commute)
  from \<open>image_mset disj_of_clause (mset F) + \<Gamma> \<Rightarrow>\<^sub>n\<close>
  have b: "image_mset disj_of_clause (mset F) + (image_mset disj_of_clause (mset G) + \<Gamma>) \<Rightarrow>\<^sub>n"
   and c: "image_mset disj_of_clause (mset F) + (mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) F) + \<Gamma>) \<Rightarrow>\<^sub>n"
    using LSC_weaken_set by (metis add.commute union_assoc)+
  have list_commute: "(mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) F) + \<Gamma>) \<Rightarrow>\<^sub>n =
  (mset (map (\<lambda>d. disj_of_clause d \<^bold>\<or> disj_of_clause a) F) + \<Gamma>) \<Rightarrow>\<^sub>n" for \<Gamma>
  proof(induction F arbitrary: \<Gamma>) (* meh, I should have only prooved one direction, would have been easier *)
    case (Cons f F) 
    have "mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) (f # F)) + \<Gamma> \<Rightarrow>\<^sub>n =
      disj_of_clause a \<^bold>\<or> disj_of_clause f, mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) F) + \<Gamma> \<Rightarrow>\<^sub>n" by(simp add: add_mset_commute)
    also have "\<dots> = disj_of_clause f \<^bold>\<or> disj_of_clause a, mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) F) + \<Gamma> \<Rightarrow>\<^sub>n"
      by(auto dest!: LSC_invs)
    also have "\<dots> = mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) F) + (disj_of_clause f \<^bold>\<or> disj_of_clause a, \<Gamma>) \<Rightarrow>\<^sub>n" by (simp add: add_mset_commute)
    also have "\<dots> = mset (map (\<lambda>d. disj_of_clause d \<^bold>\<or> disj_of_clause a) F) + (disj_of_clause f \<^bold>\<or> disj_of_clause a, \<Gamma>) \<Rightarrow>\<^sub>n" using Cons.IH
      by (metis disj_of_clause_is_nnf insert_iff is_nnf.simps(3) set_mset_add_mset_insert)
      (* this was the step that shows why I'm doing this *)
    finally show ?case by simp
  qed simp
  from distrib1[OF a b]
  have "image_mset disj_of_clause (mset G) + (mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) F) + \<Gamma>) \<Rightarrow>\<^sub>n"
    by(auto simp add: add.left_commute)
  from Cons[OF c this ]
  have "mset (concat (map (\<lambda>c. map (\<lambda>d. disj_of_clause c \<^bold>\<or> disj_of_clause d) G) F)) +
  (mset (map (\<lambda>d. disj_of_clause a \<^bold>\<or> disj_of_clause d) F) + \<Gamma>) \<Rightarrow>\<^sub>n" .
  thus ?case using list_commute by (simp add: mset_concat_map_cons add.assoc add.left_commute)
qed simp

lemma LSC_BigAndL: "mset F + \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<^bold>\<And>F, \<Gamma> \<Rightarrow>\<^sub>n"
  by(induction F arbitrary: \<Gamma>; simp add: LSC_weaken) (metis LSC.AndL add_mset_commute union_mset_add_mset_right)
lemma LSC_Top_unused: "\<lbrakk>\<Gamma> \<Rightarrow>\<^sub>n; is_nnf_mset \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> - {#\<^bold>\<not> \<bottom>#} \<Rightarrow>\<^sub>n"
proof(induction rule: LSC.induct)
  case Ax thus ?case by (metis LSC.Ax add.commute diff_union_swap formula.distinct(1,3) formula.inject(2))
next
 case BotL thus ?case by (metis LSC.BotL add.commute diff_union_swap formula.distinct(11))
next
  case (AndL F G \<Gamma>)
  hence "(F, G, \<Gamma>) - {#\<^bold>\<not> \<bottom>#} \<Rightarrow>\<^sub>n" by simp_all
  hence "F \<^bold>\<and> G, \<Gamma> - {#\<^bold>\<not> \<bottom>#} \<Rightarrow>\<^sub>n"
    by (metis AndL.hyps LSC.AndL diff_single_trivial diff_union_swap2)
  thus ?case by (metis add.commute diff_union_swap formula.distinct(19))
next
  case (OrL F \<Gamma> G)
  hence "(F, \<Gamma>) - {#\<^bold>\<not> \<bottom>#} \<Rightarrow>\<^sub>n" "(G, \<Gamma>) - {#\<^bold>\<not> \<bottom>#} \<Rightarrow>\<^sub>n" by simp_all
  hence "F \<^bold>\<or> G, \<Gamma> - {#\<^bold>\<not> \<bottom>#} \<Rightarrow>\<^sub>n" by (metis LSC.OrL OrL.hyps(1) OrL.hyps(2) diff_single_trivial diff_union_swap2)
  thus ?case by (metis diff_union_swap formula.distinct(21))
qed auto

lemma LSC_BigAndL_inv: "\<^bold>\<And>F, \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<forall>f \<in> set F. is_nnf f \<Longrightarrow> is_nnf_mset \<Gamma> \<Longrightarrow> mset F + \<Gamma> \<Rightarrow>\<^sub>n"
proof(induction F arbitrary: \<Gamma>)
  case Nil
  then show ?case using LSC_Top_unused by fastforce
next
  case (Cons a F)
  hence "\<^bold>\<And>F, a, \<Gamma> \<Rightarrow>\<^sub>n" by(auto dest: LSC_invs simp: add_mset_commute)
  with Cons have "mset F + (a, \<Gamma>) \<Rightarrow>\<^sub>n" by fastforce
  then show ?case by simp
qed

lemma LSC_reassociate_Ands: "{#disj_of_clause c \<^bold>\<or> disj_of_clause d. (c, d) \<in># C#} + \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow>
   is_nnf_mset \<Gamma> \<Longrightarrow>
  {#disj_of_clause (c @ d). (c, d) \<in># C#} + \<Gamma> \<Rightarrow>\<^sub>n"
proof(induction C arbitrary: \<Gamma>)
  case (add x C)
  obtain a b where [simp]: "x = (a, b)" by(cases x)
  from add.prems have a: "(disj_of_clause a \<^bold>\<or> disj_of_clause b), {#disj_of_clause c \<^bold>\<or> disj_of_clause d. (c, d) \<in># C#} + \<Gamma> \<Rightarrow>\<^sub>n" by(simp add: add_mset_commute)
  hence "(disj_of_clause (a@b)), {#disj_of_clause c \<^bold>\<or> disj_of_clause d. (c, d) \<in># C#} + \<Gamma> \<Rightarrow>\<^sub>n" proof -
    have pn: "is_nnf_mset ({#disj_of_clause c \<^bold>\<or> disj_of_clause d. (c, d) \<in># C#} + \<Gamma>)"
      using \<open>is_nnf_mset \<Gamma>\<close> by auto
    have "disj_of_clause a \<^bold>\<or> disj_of_clause b, \<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> is_nnf_mset \<Gamma> \<Longrightarrow> disj_of_clause (a @ b), \<Gamma> \<Rightarrow>\<^sub>n" for \<Gamma>
      by(induction a) (auto dest!: LSC_invs)
    from this[OF _ pn] a show ?thesis .
  qed
  hence "{#disj_of_clause c \<^bold>\<or> disj_of_clause d. (c, d) \<in># C#} + ((disj_of_clause (a@b)),\<Gamma>) \<Rightarrow>\<^sub>n" by(simp add: add_mset_commute)
  with add.IH have "{#disj_of_clause (c @ d). (c, d) \<in># C#} + (disj_of_clause (a @ b), \<Gamma>) \<Rightarrow>\<^sub>n"
    using \<open>is_nnf_mset \<Gamma>\<close> by fastforce
  thus ?case by(simp add: add_mset_commute)
qed simp

lemma LSC_cnf: "\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> is_nnf_mset \<Gamma> \<Longrightarrow> image_mset cnf_form_of \<Gamma> \<Rightarrow>\<^sub>n"
proof(induction "\<Gamma>" rule: LSC.induct)
  have [simp]: "NO_MATCH (And I J) F \<Longrightarrow> NO_MATCH (\<^bold>\<not>\<bottom>) F \<Longrightarrow> F,\<^bold>\<not>\<bottom>,\<Gamma> = \<^bold>\<not>\<bottom>,F,\<Gamma>" for F I J \<Gamma> by simp
  have [intro!]: "\<Gamma> \<Rightarrow>\<^sub>n \<Longrightarrow> \<^bold>\<not>\<bottom>, \<Gamma> \<Rightarrow>\<^sub>n" for \<Gamma> by (simp add: LSC_weaken)
  case Ax thus ?case by(auto simp: cnf_form_of_defs)
next
  case BotL show ?case by(auto simp: cnf_form_of_defs)
next
  have GO[simp]:
    "NO_MATCH ({#\<^bold>\<And>I#}) F \<Longrightarrow> F + (\<^bold>\<And>G, S) = \<^bold>\<And>G, (F + S)" 
    for F G H S I J a b by(simp_all add: add_mset_commute)
  case (AndL F G \<Gamma>) thus ?case
  by(auto dest!: LSC_BigAndL_inv intro!: LSC_BigAndL simp add: cnf_form_of_defs) (simp add: add_ac)
next
  case (OrL F \<Gamma> G)
  have 2: "image_mset disj_of_clause (mset (concat (map (\<lambda>f. map ((@) f) (cnf_lists G)) (cnf_lists F)))) + \<Gamma> \<Rightarrow>\<^sub>n"
    if pig: "is_nnf_mset \<Gamma>" and a:
      "mset (concat (map (\<lambda>c. map (\<lambda>d. disj_of_clause c \<^bold>\<or> disj_of_clause d) (cnf_lists G)) (cnf_lists F))) + \<Gamma> \<Rightarrow>\<^sub>n"
    (* just some nasty modification of the conjunction *) for \<Gamma>
  proof - 
    note cms[simp] = mset_map[symmetric] map_concat comp_def
    from a have "image_mset (\<lambda>(c,d). disj_of_clause c \<^bold>\<or> disj_of_clause d) (
      mset (concat (map (\<lambda>c. map (\<lambda>d. (c,d)) (cnf_lists G)) (cnf_lists F)))) + \<Gamma> \<Rightarrow>\<^sub>n" by simp
    hence "image_mset (\<lambda>(c,d). disj_of_clause (c@d)) (
      mset (concat (map (\<lambda>c. map (\<lambda>d. (c,d)) (cnf_lists G)) (cnf_lists F)))) + \<Gamma> \<Rightarrow>\<^sub>n" 
      using LSC_reassociate_Ands pig by blast
    thus ?thesis by simp
  qed
  have 1: "\<lbrakk>\<^bold>\<And> (map disj_of_clause (cnf_lists F)), \<Gamma> \<Rightarrow>\<^sub>n; \<^bold>\<And> (map disj_of_clause (cnf_lists G)), \<Gamma> \<Rightarrow>\<^sub>n\<rbrakk>
    \<Longrightarrow> is_nnf_mset \<Gamma>
    \<Longrightarrow> \<^bold>\<And> (map disj_of_clause (concat (map (\<lambda>f. map ((@) f) (cnf_lists G)) (cnf_lists F)))), \<Gamma> \<Rightarrow>\<^sub>n" 
    (* the actual disjunction is happening here *)
      for \<Gamma> using distrib[where 'a='a] 2 by(auto dest!: LSC_BigAndL_inv intro!: LSC_BigAndL)
  from OrL show ?case
    by(auto elim!: 1 simp add: cnf_form_of_def form_of_cnf_def)
qed auto

end
