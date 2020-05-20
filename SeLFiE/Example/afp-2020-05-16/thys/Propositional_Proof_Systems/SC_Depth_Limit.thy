theory SC_Depth_Limit
imports SC_Sema SC_Depth
begin
  
lemma SC_completeness: "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> sequent_cost \<Gamma> \<Delta>"
proof(induction "sequent_cost \<Gamma> \<Delta>" arbitrary: \<Gamma> \<Delta>)
  case 0 hence False by(simp add: sequent_cost_def) thus ?case by clarify
next
  case (Suc n)
  from Suc(3) show ?case
    using SCc.cases[OF Suc.hyps(1)]
oops
text\<open>Making this proof of completeness go through should be possible,
  but finding the right way to split the cases could get verbose.
The variant with the search procedure is a lot more elegant.\<close>
  

lemma sc_sim_depth:
  assumes "sc \<Gamma> A \<Delta> B = {}"
  shows "image_mset Atom (mset A) + mset \<Gamma> \<Rightarrow> image_mset Atom (mset B) + mset \<Delta> \<down> sum_list (map size (\<Gamma>@\<Delta>)) + (if set A \<inter> set B = {} then 0 else 1)"
proof -
  have [simp]: "image_mset Atom (mset A) \<Rightarrow> image_mset Atom (mset B) \<down> Suc 0" (is ?k) if "set A \<inter> set B \<noteq> {}" for A B 
  proof -
    from that obtain a where "a \<in> set A" "a \<in> set B" by blast
    thus ?k by(force simp: in_image_mset intro: SCc.Ax[where k=a])
  qed
  note SCc.intros(3-)[intro]
  have [elim!]: "\<Gamma> \<Rightarrow> \<Delta> \<down> n \<Longrightarrow> n \<le> m \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta> \<down> m" for \<Gamma> \<Delta> n m using dec_induct by(fastforce elim!: deeper_suc) (* sledgehammer is flippin' using induction. *)
  from assms show ?thesis
    by(induction \<Gamma> A \<Delta> B rule: sc.induct)
      (auto
      simp add: list_sequent_cost_def add.assoc deeper_suc weakenR'
      split: if_splits option.splits)
qed

corollary sc_depth_complete:
  assumes s: "\<Turnstile> \<Gamma> \<Rightarrow> \<Delta>"
  shows "\<Gamma> \<Rightarrow> \<Delta> \<down> sum_mset (image_mset size (\<Gamma>+\<Delta>))"
proof -
  obtain \<Gamma>' \<Delta>' where p: "\<Gamma> = mset \<Gamma>'" "\<Delta> = mset \<Delta>'" by (metis ex_mset)
  with s have sl: "\<Turnstile> mset \<Gamma>' \<Rightarrow> mset \<Delta>'" by simp
  let ?d = "sum_mset (image_mset size (\<Gamma>+\<Delta>))"
  have d: "?d = sum_list (map size (\<Gamma>'@\<Delta>'))"
    unfolding p by (metis mset_append mset_map sum_mset_sum_list)
  have "mset \<Gamma>' \<Rightarrow> mset \<Delta>' \<down> ?d"
  proof cases
    assume "sc \<Gamma>' [] \<Delta>' [] = {}"
    from sc_sim_depth[OF this] show "mset \<Gamma>' \<Rightarrow> mset \<Delta>' \<down> ?d" unfolding d by auto
  next
    assume "sc \<Gamma>' [] \<Delta>' [] \<noteq> {}"
    with SC_counterexample have "\<not> \<Turnstile> mset \<Gamma>' \<Rightarrow> mset \<Delta>'" by fastforce
    moreover note s[unfolded p]
    ultimately have False ..
    thus "mset \<Gamma>' \<Rightarrow> mset \<Delta>' \<down> ?d" ..
  qed
  thus ?thesis unfolding p .
qed

end
