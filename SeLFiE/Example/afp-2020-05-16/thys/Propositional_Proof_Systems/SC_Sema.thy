subsubsection\<open>Soundness, Completeness\<close>

theory SC_Sema
imports SC Sema
begin

definition sequent_semantics :: "'a valuation \<Rightarrow> 'a formula multiset \<Rightarrow> 'a formula multiset \<Rightarrow> bool" ("(_ \<Turnstile> (_ \<Rightarrow>/ _))" [53, 53,53] 53) where
"\<A> \<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<equiv> (\<forall>\<gamma> \<in># \<Gamma>. \<A> \<Turnstile> \<gamma>) \<longrightarrow> (\<exists>\<delta> \<in># \<Delta>. \<A> \<Turnstile> \<delta>)"
abbreviation sequent_valid :: "'a formula multiset \<Rightarrow> 'a formula multiset \<Rightarrow> bool" ("(\<Turnstile> (_ \<Rightarrow>/ _))" [53,53] 53) where
"\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<equiv> \<forall>A. A \<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
abbreviation sequent_nonvalid :: "'a valuation \<Rightarrow> 'a formula multiset \<Rightarrow> 'a formula multiset \<Rightarrow> bool" ("(_ \<not>\<Turnstile> (_ \<Rightarrow>/ _))" [53, 53,53] 53) where
"\<A> \<not>\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<equiv> \<not>\<A>\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"

lemma sequent_intuitonistic_semantics: "\<Turnstile> \<Gamma> \<Rightarrow> {#\<delta>#} \<longleftrightarrow> set_mset \<Gamma> \<TTurnstile> \<delta>"
  unfolding sequent_semantics_def entailment_def by simp

lemma SC_soundness: "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
  by(induction rule: SCp.induct) (auto simp add: sequent_semantics_def)

definition "sequent_cost \<Gamma> \<Delta> = Suc (sum_list (sorted_list_of_multiset (image_mset size (\<Gamma> + \<Delta>))))"

function(sequential)
  sc :: "'a formula list \<Rightarrow> 'a list \<Rightarrow> 'a formula list \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list) set" where
"sc (\<bottom> # \<Gamma>) A \<Delta> B = {}" |
"sc [] A [] B = (if set A \<inter> set B = {} then {(remdups A,remdups B)} else {})" |
"sc (Atom k # \<Gamma>) A  \<Delta> B = sc \<Gamma> (k#A) \<Delta> B" |
"sc (Not F # \<Gamma>) A \<Delta> B = sc \<Gamma> A (F#\<Delta>) B" |
"sc (And F G # \<Gamma>) A \<Delta> B = sc (F#G#\<Gamma>) A \<Delta> B" |
"sc (Or F G # \<Gamma>) A \<Delta> B = sc (F#\<Gamma>) A \<Delta> B \<union> sc (G#\<Gamma>) A \<Delta> B" |
"sc (Imp F G # \<Gamma>) A \<Delta> B = sc \<Gamma> A (F#\<Delta>) B \<union> sc (G#\<Gamma>) A \<Delta> B" |
"sc \<Gamma> A (\<bottom>#\<Delta>) B = sc \<Gamma> A \<Delta> B" |
"sc \<Gamma> A (Atom k # \<Delta>) B = sc \<Gamma> A \<Delta> (k#B)" |
"sc \<Gamma> A (Not F # \<Delta>) B = sc (F#\<Gamma>) A \<Delta> B" |
"sc \<Gamma> A (And F G # \<Delta>) B = sc \<Gamma> A (F#\<Delta>) B \<union> sc \<Gamma> A (G#\<Delta>) B" |
"sc \<Gamma> A (Or F G # \<Delta>) B = sc \<Gamma> A (F#G#\<Delta>) B" |
"sc \<Gamma> A (Imp F G # \<Delta>) B = sc (F#\<Gamma>) A (G#\<Delta>) B"
  by pat_completeness auto
(* Paremeters 2 and 4:
   atoms are stored in lists, not sets, simply because lists are automatically finite;
   finiteness is required when we relate back to sequents, which are finite. *)

definition "list_sequent_cost \<Gamma> \<Delta> = 2*sum_list (map size (\<Gamma>@\<Delta>)) + length (\<Gamma>@\<Delta>)"
termination sc by (relation "measure (\<lambda>(\<Gamma>,A,\<Delta>,B). list_sequent_cost \<Gamma> \<Delta>)") (simp_all add: list_sequent_cost_def)

lemma "sc [] [] [((Atom 0 \<^bold>\<rightarrow> Atom 1) \<^bold>\<rightarrow> Atom 0) \<^bold>\<rightarrow> Atom 1] [] = {([0], [1 :: nat])}"
  (* An atom may appear twice in one of the lists, but that is of no concern. 
     Using sets for the atoms stands in the way of automation. *)
by code_simp

lemma sc_sim:
  fixes \<Gamma> \<Delta> :: "'a formula list" and G D :: "'a list"
  assumes "sc \<Gamma> A \<Delta> B = {}"
  shows "image_mset Atom (mset A) + mset \<Gamma> \<Rightarrow> image_mset Atom (mset B) + mset \<Delta>"
proof -
  have *[simp]: "image_mset Atom (mset A) \<Rightarrow> image_mset Atom (mset B)" (is ?k) if "k \<in> set A" "k \<in> set B" for A B :: "'a list" and k
  proof -
    from that obtain a where "a \<in> set A" "a \<in> set B" by blast
    thus ?k by(force simp: in_image_mset intro: SCp.Ax[where k=a])
  qed
  from assms show ?thesis
    by(induction rule: sc.induct[where 'a='a]) (auto
        simp add: list_sequent_cost_def add.assoc Bot_delR_simp
        split: if_splits option.splits 
        intro: SCp.intros(3-))
qed

lemma scc_ce_distinct:
  "(C,E) \<in> sc \<Gamma> G \<Delta> D \<Longrightarrow> set C \<inter> set E = {}"
by(induction \<Gamma> G \<Delta> D arbitrary: C E rule: sc.induct)
  (fastforce split: if_splits)+

text\<open>Completeness set aside, this is an interesting fact on the side: Sequent Calculus can provide counterexamples.\<close>
theorem SC_counterexample:
  "(C,D) \<in> sc \<Gamma> A \<Delta> B \<Longrightarrow>
  (\<lambda>a. a \<in> set C) \<not>\<Turnstile> image_mset Atom (mset A) + mset \<Gamma> \<Rightarrow> image_mset Atom (mset B) + mset \<Delta>"
by(induction rule: sc.induct[where 'a='a]; 
   simp add: sequent_semantics_def split: if_splits; 
   (* used to be only for one, now it's four\<dots> *) blast)

corollary SC_counterexample':
  assumes "(C,D) \<in> sc \<Gamma> [] \<Delta> []"
  shows "(\<lambda>k. k \<in> set C) \<not>\<Turnstile> mset \<Gamma> \<Rightarrow> mset \<Delta>"
using SC_counterexample[OF assms] by simp

theorem SC_sound_complete: "\<Gamma> \<Rightarrow> \<Delta> \<longleftrightarrow> \<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
proof
  assume "\<Gamma> \<Rightarrow> \<Delta>" thus "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>" using SC_soundness by blast
next
  obtain \<Gamma>' \<Delta>' where [simp]: "\<Gamma> = mset  \<Gamma>'" "\<Delta> = mset \<Delta>'" by (metis ex_mset)
  assume "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
  hence "sc \<Gamma>' [] \<Delta>' [] = {}"
  proof(rule contrapos_pp)
    assume "sc \<Gamma>' [] \<Delta>' [] \<noteq> {}"
    then obtain C E where "(C,E) \<in> sc \<Gamma>' [] \<Delta>' []" by fast
    thus "\<not> \<Turnstile> \<Gamma> \<Rightarrow> \<Delta>" using SC_counterexample' by fastforce
  qed
  from sc_sim[OF this] show "\<Gamma> \<Rightarrow> \<Delta>" by auto
qed
  
theorem "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof -
  assume s: "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
  obtain \<Gamma>' \<Delta>' where p: "\<Gamma> = mset \<Gamma>'" "\<Delta> = mset \<Delta>'" by (metis ex_mset)
  have "mset \<Gamma>' \<Rightarrow> mset \<Delta>'"
  proof cases \<comment> \<open>just to show that we didn't need to show the lemma above by contraposition. It's just quicker to do so.\<close>
    assume "sc \<Gamma>' [] \<Delta>' [] = {}"
    from sc_sim[OF this] show "mset \<Gamma>' \<Rightarrow> mset \<Delta>'" by auto
  next
    assume "sc \<Gamma>' [] \<Delta>' [] \<noteq> {}"
    with SC_counterexample have "\<not> \<Turnstile> mset \<Gamma>' \<Rightarrow> mset \<Delta>'" by fastforce
    moreover note s[unfolded p]
    ultimately have False ..
    thus "mset \<Gamma>' \<Rightarrow> mset \<Delta>'" ..
  qed
  thus ?thesis unfolding p .
qed

(*
Just as a side-note: some textbooks advertise completeness as a consequence of cut elimination.
This only makes sense if you have a cut-rule in the rules of SC to begin with.
But even if we did, this proof of completeness would not change a bit.
So\<dots> huh.
*)
  
end
