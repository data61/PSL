section \<open>Horwitz-Reps-Binkley Slice\<close>

theory HRBSlice imports SDG begin

context SDG begin

subsection \<open>Set describing phase 1 of the two-phase slicer\<close>

inductive_set sum_SDG_slice1 :: "'node SDG_node \<Rightarrow> 'node SDG_node set"
  for n::"'node SDG_node"
  where refl_slice1:"valid_SDG_node n \<Longrightarrow> n \<in> sum_SDG_slice1 n"
  | cdep_slice1:
  "\<lbrakk>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"
  | ddep_slice1: 
  "\<lbrakk>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"
  | call_slice1:
  "\<lbrakk>n'' s-p\<rightarrow>\<^bsub>call\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"
  | param_in_slice1: 
  "\<lbrakk>n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"
  | sum_slice1:
  "\<lbrakk>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'; n' \<in> sum_SDG_slice1 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice1 n"


lemma slice1_cdep_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s\<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)

lemma slice1_ddep_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s-V\<rightarrow>\<^sub>d\<^sub>d n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)

lemma slice1_sum_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)

lemma slice1_call_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s-p\<rightarrow>\<^bsub>call\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)

lemma slice1_param_in_slice1:
  "\<lbrakk>nx \<in> sum_SDG_slice1 n; n s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice1 n'"
by(induct rule:sum_SDG_slice1.induct,
   auto intro:sum_SDG_slice1.intros sum_SDG_edge_valid_SDG_node)


lemma is_SDG_path_slice1:
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n'; n' \<in> sum_SDG_slice1 n''\<rbrakk> \<Longrightarrow> n \<in> sum_SDG_slice1 n''"
proof(induct rule:intra_sum_SDG_path.induct)
  case isSp_Nil thus ?case by simp
next
  case (isSp_Append_cdep n ns nx n')
  note IH = \<open>nx \<in> sum_SDG_slice1 n'' \<Longrightarrow> n \<in> sum_SDG_slice1 n''\<close>
  from \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> \<open>n' \<in> sum_SDG_slice1 n''\<close>
  have "nx \<in> sum_SDG_slice1 n''" by(rule cdep_slice1)
  from IH[OF this] show ?case .
next
  case (isSp_Append_ddep n ns nx V n')
  note IH = \<open>nx \<in> sum_SDG_slice1 n'' \<Longrightarrow> n \<in> sum_SDG_slice1 n''\<close>
  from \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>n' \<in> sum_SDG_slice1 n''\<close>
  have "nx \<in> sum_SDG_slice1 n''" by(rule ddep_slice1)
  from IH[OF this] show ?case .
next
  case (isSp_Append_sum n ns nx p n')
  note IH = \<open>nx \<in> sum_SDG_slice1 n'' \<Longrightarrow> n \<in> sum_SDG_slice1 n''\<close>
  from \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> \<open>n' \<in> sum_SDG_slice1 n''\<close>
  have "nx \<in> sum_SDG_slice1 n''" by(rule sum_slice1)
  from IH[OF this] show ?case .
qed


subsection \<open>Set describing phase 2 of the two-phase slicer\<close>

inductive_set sum_SDG_slice2 :: "'node SDG_node \<Rightarrow> 'node SDG_node set"
  for n::"'node SDG_node"
  where refl_slice2:"valid_SDG_node n \<Longrightarrow> n \<in> sum_SDG_slice2 n"
  | cdep_slice2:
  "\<lbrakk>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"
  | ddep_slice2: 
  "\<lbrakk>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"
  | return_slice2:
  "\<lbrakk>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"
  | param_out_slice2: 
  "\<lbrakk>n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"
  | sum_slice2:
  "\<lbrakk>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'; n' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n"


lemma slice2_cdep_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s\<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)

lemma slice2_ddep_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s-V\<rightarrow>\<^sub>d\<^sub>d n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)

lemma slice2_sum_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)

lemma slice2_ret_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s-p\<rightarrow>\<^bsub>ret\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)

lemma slice2_param_out_slice2:
  "\<lbrakk>nx \<in> sum_SDG_slice2 n; n s-p:V\<rightarrow>\<^bsub>out\<^esub> n'\<rbrakk> \<Longrightarrow> nx \<in> sum_SDG_slice2 n'"
by(induct rule:sum_SDG_slice2.induct,
   auto intro:sum_SDG_slice2.intros sum_SDG_edge_valid_SDG_node)


lemma is_SDG_path_slice2:
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n'; n' \<in> sum_SDG_slice2 n''\<rbrakk> \<Longrightarrow> n \<in> sum_SDG_slice2 n''"
proof(induct rule:intra_sum_SDG_path.induct)
  case isSp_Nil thus ?case by simp
next
  case (isSp_Append_cdep n ns nx n')
  note IH = \<open>nx \<in> sum_SDG_slice2 n'' \<Longrightarrow> n \<in> sum_SDG_slice2 n''\<close>
  from \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> \<open>n' \<in> sum_SDG_slice2 n''\<close>
  have "nx \<in> sum_SDG_slice2 n''" by(rule cdep_slice2)
  from IH[OF this] show ?case .
next
  case (isSp_Append_ddep n ns nx V n')
  note IH = \<open>nx \<in> sum_SDG_slice2 n'' \<Longrightarrow> n \<in> sum_SDG_slice2 n''\<close>
  from \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>n' \<in> sum_SDG_slice2 n''\<close>
  have "nx \<in> sum_SDG_slice2 n''" by(rule ddep_slice2)
  from IH[OF this] show ?case .
next
  case (isSp_Append_sum n ns nx p n')
  note IH = \<open>nx \<in> sum_SDG_slice2 n'' \<Longrightarrow> n \<in> sum_SDG_slice2 n''\<close>
  from \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> \<open>n' \<in> sum_SDG_slice2 n''\<close>
  have "nx \<in> sum_SDG_slice2 n''" by(rule sum_slice2)
  from IH[OF this] show ?case .
qed



lemma slice2_is_SDG_path_slice2: 
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n'; n'' \<in> sum_SDG_slice2 n\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n'"
proof(induct rule:intra_sum_SDG_path.induct)
  case isSp_Nil thus ?case by simp
next
  case (isSp_Append_cdep n ns nx n')
  from \<open>n'' \<in> sum_SDG_slice2 n \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx\<close> \<open>n'' \<in> sum_SDG_slice2 n\<close>
  have "n'' \<in> sum_SDG_slice2 nx" .
  with \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> show ?case by -(rule slice2_cdep_slice2)
next
  case (isSp_Append_ddep n ns nx V n')
  from \<open>n'' \<in> sum_SDG_slice2 n \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx\<close> \<open>n'' \<in> sum_SDG_slice2 n\<close>
  have "n'' \<in> sum_SDG_slice2 nx" .
  with \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> show ?case by -(rule slice2_ddep_slice2)
next
  case (isSp_Append_sum n ns nx p n')
  from \<open>n'' \<in> sum_SDG_slice2 n \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx\<close> \<open>n'' \<in> sum_SDG_slice2 n\<close>
  have "n'' \<in> sum_SDG_slice2 nx" .
  with \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> show ?case by -(rule slice2_sum_slice2)
qed


subsection \<open>The backward slice using the Horwitz-Reps-Binkley slicer\<close>

text \<open>Note: our slicing criterion is a set of nodes, not a unique node.\<close>

inductive_set combine_SDG_slices :: "'node SDG_node set \<Rightarrow> 'node SDG_node set"
  for S::"'node SDG_node set"
  where combSlice_refl:"n \<in> S \<Longrightarrow> n \<in> combine_SDG_slices S" 
  | combSlice_Return_parent_node:
  "\<lbrakk>n' \<in> S; n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n'); n \<in> sum_SDG_slice2 n'\<rbrakk> 
  \<Longrightarrow> n \<in> combine_SDG_slices S"


definition HRB_slice :: "'node SDG_node set \<Rightarrow> 'node SDG_node set"
  where "HRB_slice S \<equiv> {n'. \<exists>n \<in> S. n' \<in> combine_SDG_slices (sum_SDG_slice1 n)}"


lemma HRB_slice_cases[consumes 1,case_names phase1 phase2]:
  "\<lbrakk>x \<in> HRB_slice S; \<And>n nx. \<lbrakk>n \<in> sum_SDG_slice1 nx; nx \<in> S\<rbrakk> \<Longrightarrow> P n;
   \<And>nx n' n'' p n. \<lbrakk>n' \<in> sum_SDG_slice1 nx; n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n'); 
                    n \<in> sum_SDG_slice2 n'; nx \<in> S\<rbrakk> \<Longrightarrow> P n\<rbrakk>
  \<Longrightarrow> P x"
  by(fastforce elim:combine_SDG_slices.cases simp:HRB_slice_def)



lemma HRB_slice_refl:
  assumes "valid_node m" and "CFG_node m \<in> S" shows "CFG_node m \<in> HRB_slice S"
proof -
  from \<open>valid_node m\<close> have "CFG_node m \<in> sum_SDG_slice1 (CFG_node m)"
    by(fastforce intro:refl_slice1)
  with \<open>CFG_node m \<in> S\<close> show ?thesis
    by(simp add:HRB_slice_def)(blast intro:combSlice_refl)
qed


lemma HRB_slice_valid_node: "n \<in> HRB_slice S \<Longrightarrow> valid_SDG_node n"
proof(induct rule:HRB_slice_cases)
  case (phase1 n nx) thus ?case
    by(induct rule:sum_SDG_slice1.induct,auto intro:sum_SDG_edge_valid_SDG_node)
next
  case (phase2 nx n' n'' p n)
  from \<open>n \<in> sum_SDG_slice2 n'\<close>
  show ?case
    by(induct rule:sum_SDG_slice2.induct,auto intro:sum_SDG_edge_valid_SDG_node)
qed


lemma valid_SDG_node_in_slice_parent_node_in_slice:
  assumes "n \<in> HRB_slice S" shows "CFG_node (parent_node n) \<in> HRB_slice S"
proof -
  from \<open>n \<in> HRB_slice S\<close> have "valid_SDG_node n" by(rule HRB_slice_valid_node)
  hence "n = CFG_node (parent_node n) \<or> CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by(rule valid_SDG_node_cases)
  thus ?thesis
  proof
    assume "n = CFG_node (parent_node n)"
    with \<open>n \<in> HRB_slice S\<close> show ?thesis by simp
  next
    assume "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    hence "CFG_node (parent_node n) s\<longrightarrow>\<^bsub>cd\<^esub> n" by(rule SDG_edge_sum_SDG_edge)
    with \<open>n \<in> HRB_slice S\<close> show ?thesis
      by(fastforce elim:combine_SDG_slices.cases 
                 intro:combine_SDG_slices.intros cdep_slice1 cdep_slice2 
                  simp:HRB_slice_def)
  qed
qed


lemma HRB_slice_is_SDG_path_HRB_slice: 
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n'; n'' \<in> HRB_slice {n}; n' \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S"
proof(induct arbitrary:S rule:intra_sum_SDG_path.induct)
  case (isSp_Nil n) thus ?case by(fastforce simp:HRB_slice_def)
next
  case (isSp_Append_cdep n ns nx n')
  note IH = \<open>\<And>S. \<lbrakk>n'' \<in> HRB_slice {n}; nx \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from IH[OF \<open>n'' \<in> HRB_slice {n}\<close>] have "n'' \<in> HRB_slice {nx}" by simp
  thus ?case
  proof(induct rule:HRB_slice_cases)
    case (phase1 n nx') 
    from \<open>nx' \<in> {nx}\<close> have "nx' = nx" by simp
    with \<open>n \<in> sum_SDG_slice1 nx'\<close> \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "n \<in> sum_SDG_slice1 n'"
      by(fastforce intro:slice1_cdep_slice1)
    with \<open>n' \<in> S\<close> show ?case
      by(fastforce intro:combine_SDG_slices.combSlice_refl simp:HRB_slice_def)
  next
    case (phase2 nx'' nx' n'' p n)
    from \<open>nx'' \<in> {nx}\<close> have "nx'' = nx" by simp
    with \<open>nx' \<in> sum_SDG_slice1 nx''\<close> \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "nx' \<in> sum_SDG_slice1 n'"
      by(fastforce intro:slice1_cdep_slice1)
    with \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node nx')\<close> \<open>n \<in> sum_SDG_slice2 nx'\<close> \<open>n' \<in> S\<close>
    show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                            simp:HRB_slice_def)
  qed
next
  case (isSp_Append_ddep n ns nx V n')
  note IH = \<open>\<And>S. \<lbrakk>n'' \<in> HRB_slice {n}; nx \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from IH[OF \<open>n'' \<in> HRB_slice {n}\<close>] have "n'' \<in> HRB_slice {nx}" by simp
  thus ?case
  proof(induct rule:HRB_slice_cases)
    case (phase1 n nx') 
    from \<open>nx' \<in> {nx}\<close> have "nx' = nx" by simp
    with \<open>n \<in> sum_SDG_slice1 nx'\<close> \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "n \<in> sum_SDG_slice1 n'"
      by(fastforce intro:slice1_ddep_slice1)
    with \<open>n' \<in> S\<close> show ?case
      by(fastforce intro:combine_SDG_slices.combSlice_refl simp:HRB_slice_def)
  next
    case (phase2 nx'' nx' n'' p n)
    from \<open>nx'' \<in> {nx}\<close> have "nx'' = nx" by simp
    with \<open>nx' \<in> sum_SDG_slice1 nx''\<close> \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "nx' \<in> sum_SDG_slice1 n'"
      by(fastforce intro:slice1_ddep_slice1)
    with \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node nx')\<close> \<open>n \<in> sum_SDG_slice2 nx'\<close> \<open>n' \<in> S\<close>
    show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                            simp:HRB_slice_def)
  qed
next
  case (isSp_Append_sum n ns nx p n')
  note IH = \<open>\<And>S. \<lbrakk>n'' \<in> HRB_slice {n}; nx \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from IH[OF \<open>n'' \<in> HRB_slice {n}\<close>] have "n'' \<in> HRB_slice {nx}" by simp
  thus ?case
  proof(induct rule:HRB_slice_cases)
    case (phase1 n nx') 
    from \<open>nx' \<in> {nx}\<close> have "nx' = nx" by simp
    with \<open>n \<in> sum_SDG_slice1 nx'\<close> \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> have "n \<in> sum_SDG_slice1 n'"
      by(fastforce intro:slice1_sum_slice1)
    with \<open>n' \<in> S\<close> show ?case
      by(fastforce intro:combine_SDG_slices.combSlice_refl simp:HRB_slice_def)
  next
    case (phase2 nx'' nx' n'' p' n)
    from \<open>nx'' \<in> {nx}\<close> have "nx'' = nx" by simp
    with \<open>nx' \<in> sum_SDG_slice1 nx''\<close> \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> have "nx' \<in> sum_SDG_slice1 n'"
      by(fastforce intro:slice1_sum_slice1)
    with \<open>n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node nx')\<close> \<open>n \<in> sum_SDG_slice2 nx'\<close> \<open>n' \<in> S\<close>
    show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                            simp:HRB_slice_def)
  qed
qed


lemma call_return_nodes_in_slice:
  assumes "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  and "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'" and "a \<in> get_return_edges a'"
  and "CFG_node (targetnode a) \<in> HRB_slice S"
  shows "CFG_node (sourcenode a) \<in> HRB_slice S"
  and "CFG_node (sourcenode a') \<in> HRB_slice S" 
  and "CFG_node (targetnode a') \<in> HRB_slice S"
proof -
  from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close> \<open>a \<in> get_return_edges a'\<close>
  have "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
    by(fastforce intro:sum_SDG_call_summary_edge)
  with \<open>CFG_node (targetnode a) \<in> HRB_slice S\<close>
  show "CFG_node (sourcenode a') \<in> HRB_slice S"
    by(fastforce elim!:combine_SDG_slices.cases 
                intro:combine_SDG_slices.intros sum_slice1 sum_slice2 
                 simp:HRB_slice_def)
  from \<open>CFG_node (targetnode a) \<in> HRB_slice S\<close>
  obtain n\<^sub>c where "CFG_node (targetnode a) \<in> combine_SDG_slices (sum_SDG_slice1 n\<^sub>c)"
    and "n\<^sub>c \<in> S"
    by(simp add:HRB_slice_def) blast
  thus "CFG_node (sourcenode a) \<in> HRB_slice S"
  proof(induct "CFG_node (targetnode a)" rule:combine_SDG_slices.induct)
    case combSlice_refl
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
    have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)"
      by(fastforce intro:sum_SDG_return_edge)
    with \<open>valid_edge a\<close> 
    have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 (CFG_node (targetnode a))"
      by(fastforce intro:sum_SDG_slice2.intros)
    with \<open>CFG_node (targetnode a) \<in> sum_SDG_slice1 n\<^sub>c\<close> \<open>n\<^sub>c \<in> S\<close>
      \<open>CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)\<close>
    show ?case by(fastforce intro:combSlice_Return_parent_node simp:HRB_slice_def)
  next
    case (combSlice_Return_parent_node n' n'' p')
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
    have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)"
      by(fastforce intro:sum_SDG_return_edge)
    with \<open>CFG_node (targetnode a) \<in> sum_SDG_slice2 n'\<close>
    have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 n'"
      by(fastforce intro:sum_SDG_slice2.intros)
    with \<open>n' \<in> sum_SDG_slice1 n\<^sub>c\<close> \<open>n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close> \<open>n\<^sub>c \<in> S\<close>
    show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                            simp:HRB_slice_def)
  qed
  from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close> \<open>a \<in> get_return_edges a'\<close>
  have "CFG_node (targetnode a') s\<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a)"
    by(fastforce intro:sum_SDG_proc_entry_exit_cdep)
  with \<open>CFG_node (sourcenode a) \<in> HRB_slice S\<close> \<open>n\<^sub>c \<in> S\<close>
  show "CFG_node (targetnode a') \<in> HRB_slice S"
    by(fastforce elim!:combine_SDG_slices.cases 
                intro:combine_SDG_slices.intros cdep_slice1 cdep_slice2 
                 simp:HRB_slice_def)
qed



subsection \<open>Proof of Precision\<close>


lemma in_intra_SDG_path_in_slice2:
  "\<lbrakk>n i-ns\<rightarrow>\<^sub>d* n'; n'' \<in> set ns\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n'"
proof(induct rule:intra_SDG_path.induct)
  case iSp_Nil thus ?case by simp
next
  case (iSp_Append_cdep n ns nx n')
  note IH = \<open>n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx\<close>
  from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by auto
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> sum_SDG_slice2 nx" by simp
    with \<open>nx \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> show ?thesis
      by(fastforce intro:slice2_cdep_slice2 SDG_edge_sum_SDG_edge)
  next
    assume "n'' = nx"
    from \<open>nx \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
    hence "n' \<in> sum_SDG_slice2 n'" by(rule refl_slice2)
    with \<open>nx \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "nx \<in> sum_SDG_slice2 n'"
      by(fastforce intro:cdep_slice2 SDG_edge_sum_SDG_edge)
    with \<open>n'' = nx\<close> show ?thesis by simp
  qed
next
  case (iSp_Append_ddep n ns nx V n')
  note IH = \<open>n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx\<close>
  from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by auto
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> sum_SDG_slice2 nx" by simp
    with \<open>nx -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> show ?thesis
      by(fastforce intro:slice2_ddep_slice2 SDG_edge_sum_SDG_edge)
  next
    assume "n'' = nx"
    from \<open>nx -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
    hence "n' \<in> sum_SDG_slice2 n'" by(rule refl_slice2)
    with \<open>nx -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "nx \<in> sum_SDG_slice2 n'"
      by(fastforce intro:ddep_slice2 SDG_edge_sum_SDG_edge)
    with \<open>n'' = nx\<close> show ?thesis by simp
  qed
qed


lemma in_intra_SDG_path_in_HRB_slice:
  "\<lbrakk>n i-ns\<rightarrow>\<^sub>d* n'; n'' \<in> set ns; n' \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S"
proof(induct arbitrary:S rule:intra_SDG_path.induct)
  case iSp_Nil thus ?case by simp
next
  case (iSp_Append_cdep n ns nx n')
  note IH = \<open>\<And>S. \<lbrakk>n'' \<in> set ns; nx \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by auto
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF \<open>n'' \<in> set ns\<close>] have "n'' \<in> HRB_slice {nx}" by simp
    from this \<open>nx \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> \<open>n' \<in> S\<close> show ?case
      by(fastforce elim:HRB_slice_cases slice1_cdep_slice1
        intro:bexI[where x="n'"] combine_SDG_slices.intros SDG_edge_sum_SDG_edge 
        simp:HRB_slice_def)
  next
    assume "n'' = nx"
    from \<open>nx \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
    hence "n' \<in> sum_SDG_slice1 n'" by(rule refl_slice1)
    with \<open>nx \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "nx \<in> sum_SDG_slice1 n'" 
      by(fastforce intro:cdep_slice1 SDG_edge_sum_SDG_edge)
    with \<open>n'' = nx\<close> \<open>n' \<in> S\<close> show ?case
      by(fastforce intro:combSlice_refl simp:HRB_slice_def)
  qed
next
  case (iSp_Append_ddep n ns nx V n')
  note IH = \<open>\<And>S. \<lbrakk>n'' \<in> set ns; nx \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by auto
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF \<open>n'' \<in> set ns\<close>] have "n'' \<in> HRB_slice {nx}" by simp
    from this \<open>nx -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>n' \<in> S\<close> show ?case
      by(fastforce elim:HRB_slice_cases slice1_ddep_slice1
        intro:bexI[where x="n'"] combine_SDG_slices.intros SDG_edge_sum_SDG_edge 
        simp:HRB_slice_def)
  next
    assume "n'' = nx"
    from \<open>nx -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
    hence "n' \<in> sum_SDG_slice1 n'" by(rule refl_slice1)
    with \<open>nx -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "nx \<in> sum_SDG_slice1 n'" 
      by(fastforce intro:ddep_slice1 SDG_edge_sum_SDG_edge)
    with \<open>n'' = nx\<close> \<open>n' \<in> S\<close> show ?case 
      by(fastforce intro:combSlice_refl simp:HRB_slice_def)
  qed
qed


lemma in_matched_in_slice2:
  "\<lbrakk>matched n ns n'; n'' \<in> set ns\<rbrakk> \<Longrightarrow> n'' \<in> sum_SDG_slice2 n'"
proof(induct rule:matched.induct)
  case matched_Nil thus ?case by simp
next
  case (matched_Append_intra_SDG_path n ns nx ns' n')
  note IH = \<open>n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 nx\<close>
  from \<open>n'' \<in> set (ns@ns')\<close> have "n'' \<in> set ns \<or> n'' \<in> set ns'" by simp
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> sum_SDG_slice2 nx" .
    with \<open>nx i-ns'\<rightarrow>\<^sub>d* n'\<close> show ?thesis
      by(fastforce intro:slice2_is_SDG_path_slice2 
                        intra_SDG_path_is_SDG_path)
  next
    assume "n'' \<in> set ns'"
    with \<open>nx i-ns'\<rightarrow>\<^sub>d* n'\<close> show ?case by(rule in_intra_SDG_path_in_slice2)
  qed
next
  case (matched_bracket_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 ns' n\<^sub>3 n\<^sub>4 V a a')
  note IH1 = \<open>n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 n\<^sub>1\<close>
  note IH2 = \<open>n'' \<in> set ns' \<Longrightarrow> n'' \<in> sum_SDG_slice2 n\<^sub>3\<close>
  from \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2\<close> \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> 
    \<open>a' \<in> get_return_edges a\<close> \<open>valid_edge a\<close>
    \<open>sourcenode a = parent_node n\<^sub>1\<close> \<open>targetnode a = parent_node n\<^sub>2\<close>
    \<open>sourcenode a' = parent_node n\<^sub>3\<close> \<open>targetnode a' = parent_node n\<^sub>4\<close>
  have "matched n\<^sub>1 ([]@n\<^sub>1#ns'@[n\<^sub>3]) n\<^sub>4"
    by(fastforce intro:matched.matched_bracket_call matched_Nil 
                 elim:SDG_edge_valid_SDG_node)
  then obtain nsx where "n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4" by(erule matched_is_SDG_path)
  from \<open>n'' \<in> set (ns@n\<^sub>1#ns'@[n\<^sub>3])\<close> 
  have "((n'' \<in> set ns \<or> n'' = n\<^sub>1) \<or> n'' \<in> set ns') \<or> n'' = n\<^sub>3" by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH1[OF this] have "n'' \<in> sum_SDG_slice2 n\<^sub>1" .
    with \<open>n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4\<close> show ?thesis 
      by -(rule slice2_is_SDG_path_slice2)
  next
    assume "n'' = n\<^sub>1"
    from \<open>n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4\<close> have "n\<^sub>1 \<in> sum_SDG_slice2 n\<^sub>4" 
      by(fastforce intro:is_SDG_path_slice2 refl_slice2 is_SDG_path_valid_SDG_node)
    with \<open>n'' = n\<^sub>1\<close> show ?thesis by(fastforce intro:combSlice_refl simp:HRB_slice_def)
  next
    assume "n'' \<in> set ns'"
    from IH2[OF this] have "n'' \<in> sum_SDG_slice2 n\<^sub>3" .
    with \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> show ?thesis 
      by(fastforce intro:slice2_ret_slice2 slice2_param_out_slice2 
                        SDG_edge_sum_SDG_edge)
  next
    assume "n'' = n\<^sub>3"
    from \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "n\<^sub>3 s-p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 s-p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4" 
      by(fastforce intro:SDG_edge_sum_SDG_edge)
    hence "n\<^sub>3 \<in> sum_SDG_slice2 n\<^sub>4"
      by(fastforce intro:return_slice2 param_out_slice2 refl_slice2 
                        sum_SDG_edge_valid_SDG_node)
    with \<open>n'' = n\<^sub>3\<close> show ?thesis by simp
  qed
next
  case (matched_bracket_param n\<^sub>0 ns n\<^sub>1 p V n\<^sub>2 ns' n\<^sub>3 V' n\<^sub>4 a a')
  note IH1 = \<open>n'' \<in> set ns \<Longrightarrow> n'' \<in> sum_SDG_slice2 n\<^sub>1\<close>
  note IH2 = \<open>n'' \<in> set ns' \<Longrightarrow> n'' \<in> sum_SDG_slice2 n\<^sub>3\<close>
  from \<open>n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close> \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> 
    \<open>a' \<in> get_return_edges a\<close> \<open>valid_edge a\<close>
    \<open>sourcenode a = parent_node n\<^sub>1\<close> \<open>targetnode a = parent_node n\<^sub>2\<close>
    \<open>sourcenode a' = parent_node n\<^sub>3\<close> \<open>targetnode a' = parent_node n\<^sub>4\<close>
  have "matched n\<^sub>1 ([]@n\<^sub>1#ns'@[n\<^sub>3]) n\<^sub>4"
    by(fastforce intro:matched.matched_bracket_param matched_Nil 
                 elim:SDG_edge_valid_SDG_node)
  then obtain nsx where "n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4" by(erule matched_is_SDG_path)
  from \<open>n'' \<in> set (ns@n\<^sub>1#ns'@[n\<^sub>3])\<close> 
  have "((n'' \<in> set ns \<or> n'' = n\<^sub>1) \<or> n'' \<in> set ns') \<or> n'' = n\<^sub>3" by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH1[OF this] have "n'' \<in> sum_SDG_slice2 n\<^sub>1" .
    with \<open>n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4\<close> show ?thesis 
      by -(rule slice2_is_SDG_path_slice2)
  next
    assume "n'' = n\<^sub>1"
    from \<open>n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4\<close> have "n\<^sub>1 \<in> sum_SDG_slice2 n\<^sub>4" 
      by(fastforce intro:is_SDG_path_slice2 refl_slice2 is_SDG_path_valid_SDG_node)
    with \<open>n'' = n\<^sub>1\<close> show ?thesis by(fastforce intro:combSlice_refl simp:HRB_slice_def)
  next
    assume "n'' \<in> set ns'"
    from IH2[OF this] have "n'' \<in> sum_SDG_slice2 n\<^sub>3" .
    with \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> show ?thesis 
      by(fastforce intro:slice2_param_out_slice2 SDG_edge_sum_SDG_edge)
  next
    assume "n'' = n\<^sub>3"
    from \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "n\<^sub>3 s-p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4" by(rule SDG_edge_sum_SDG_edge)
    hence "n\<^sub>3 \<in> sum_SDG_slice2 n\<^sub>4"
      by(fastforce intro:param_out_slice2 refl_slice2 sum_SDG_edge_valid_SDG_node)
    with \<open>n'' = n\<^sub>3\<close> show ?thesis by simp
  qed
qed


lemma in_matched_in_HRB_slice:
  "\<lbrakk>matched n ns n'; n'' \<in> set ns; n' \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S"
proof(induct arbitrary:S rule:matched.induct)
   case matched_Nil thus ?case by simp
next
  case (matched_Append_intra_SDG_path n ns nx ns' n')
  note IH = \<open>\<And>S. \<lbrakk>n'' \<in> set ns; nx \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from \<open>n'' \<in> set (ns@ns')\<close> have "n'' \<in> set ns \<or> n'' \<in> set ns'" by simp
  thus ?case
  proof
    assume "n'' \<in> set ns"
    from IH[OF \<open>n'' \<in> set ns\<close>] have "n'' \<in> HRB_slice {nx}" by simp
    with \<open>nx i-ns'\<rightarrow>\<^sub>d* n'\<close> \<open>n' \<in> S\<close> show ?thesis
      by(fastforce intro:HRB_slice_is_SDG_path_HRB_slice 
                        intra_SDG_path_is_SDG_path)
  next
    assume "n'' \<in> set ns'"
    with \<open>nx i-ns'\<rightarrow>\<^sub>d* n'\<close> \<open>n' \<in> S\<close> show ?case 
      by(fastforce intro:in_intra_SDG_path_in_HRB_slice simp:HRB_slice_def)
  qed
next
  case (matched_bracket_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 ns' n\<^sub>3 n\<^sub>4 V a a')
  note IH1 = \<open>\<And>S. \<lbrakk>n'' \<in> set ns; n\<^sub>1 \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  note IH2 = \<open>\<And>S. \<lbrakk>n'' \<in> set ns'; n\<^sub>3 \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2\<close> \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> 
    \<open>a' \<in> get_return_edges a\<close> \<open>valid_edge a\<close>
    \<open>sourcenode a = parent_node n\<^sub>1\<close> \<open>targetnode a = parent_node n\<^sub>2\<close>
    \<open>sourcenode a' = parent_node n\<^sub>3\<close> \<open>targetnode a' = parent_node n\<^sub>4\<close>
  have "matched n\<^sub>1 ([]@n\<^sub>1#ns'@[n\<^sub>3]) n\<^sub>4"
    by(fastforce intro:matched.matched_bracket_call matched_Nil 
                 elim:SDG_edge_valid_SDG_node)
  then obtain nsx where "n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4" by(erule matched_is_SDG_path)
  from \<open>n'' \<in> set (ns@n\<^sub>1#ns'@[n\<^sub>3])\<close> 
  have "((n'' \<in> set ns \<or> n'' = n\<^sub>1) \<or> n'' \<in> set ns') \<or> n'' = n\<^sub>3" by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH1[OF this] have "n'' \<in> HRB_slice {n\<^sub>1}" by simp
    with \<open>n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4\<close> \<open>n\<^sub>4 \<in> S\<close> show ?thesis 
      by -(rule HRB_slice_is_SDG_path_HRB_slice)
  next
    assume "n'' = n\<^sub>1"
    from \<open>n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4\<close> have "n\<^sub>1 \<in> sum_SDG_slice1 n\<^sub>4" 
      by(fastforce intro:is_SDG_path_slice1 refl_slice1 is_SDG_path_valid_SDG_node)
    with \<open>n'' = n\<^sub>1\<close> \<open>n\<^sub>4 \<in> S\<close> show ?thesis
      by(fastforce intro:combSlice_refl simp:HRB_slice_def)
  next
    assume "n'' \<in> set ns'"
    with \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> have "n'' \<in> sum_SDG_slice2 n\<^sub>3"
      by(rule in_matched_in_slice2)
    with \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "n'' \<in> sum_SDG_slice2 n\<^sub>4"
      by(fastforce intro:slice2_ret_slice2 slice2_param_out_slice2 
                        SDG_edge_sum_SDG_edge)
    from \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "valid_SDG_node n\<^sub>4"
      by(fastforce intro:SDG_edge_valid_SDG_node)
    hence "n\<^sub>4 \<in> sum_SDG_slice1 n\<^sub>4" by(rule refl_slice1)
    from \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close>
    have "CFG_node (parent_node n\<^sub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^sub>4)"
      by(fastforce elim:SDG_edge.cases intro:SDG_return_edge)
    with \<open>n'' \<in> sum_SDG_slice2 n\<^sub>4\<close> \<open>n\<^sub>4 \<in> sum_SDG_slice1 n\<^sub>4\<close> \<open>n\<^sub>4 \<in> S\<close>
    show ?case by(fastforce intro:combSlice_Return_parent_node SDG_edge_sum_SDG_edge 
                            simp:HRB_slice_def)
  next
    assume "n'' = n\<^sub>3"
    from \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close>
    have "CFG_node (parent_node n\<^sub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^sub>4)"
      by(fastforce elim:SDG_edge.cases intro:SDG_return_edge)
    from \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "valid_SDG_node n\<^sub>4"
      by(fastforce intro:SDG_edge_valid_SDG_node)
    hence "n\<^sub>4 \<in> sum_SDG_slice1 n\<^sub>4" by(rule refl_slice1)
    from \<open>valid_SDG_node n\<^sub>4\<close> have "n\<^sub>4 \<in> sum_SDG_slice2 n\<^sub>4" by(rule refl_slice2)
    with \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "n\<^sub>3 \<in> sum_SDG_slice2 n\<^sub>4" 
      by(fastforce intro:return_slice2 param_out_slice2 SDG_edge_sum_SDG_edge)
    with \<open>n\<^sub>4 \<in> sum_SDG_slice1 n\<^sub>4\<close> 
      \<open>CFG_node (parent_node n\<^sub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^sub>4)\<close> \<open>n'' = n\<^sub>3\<close> \<open>n\<^sub>4 \<in> S\<close>
    show ?case by(fastforce intro:combSlice_Return_parent_node SDG_edge_sum_SDG_edge
                            simp:HRB_slice_def)
  qed
next
  case (matched_bracket_param n\<^sub>0 ns n\<^sub>1 p V n\<^sub>2 ns' n\<^sub>3 V' n\<^sub>4 a a')
  note IH1 = \<open>\<And>S. \<lbrakk>n'' \<in> set ns; n\<^sub>1 \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  note IH2 = \<open>\<And>S. \<lbrakk>n'' \<in> set ns'; n\<^sub>3 \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from \<open>n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close> \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> 
    \<open>a' \<in> get_return_edges a\<close> \<open>valid_edge a\<close>
    \<open>sourcenode a = parent_node n\<^sub>1\<close> \<open>targetnode a = parent_node n\<^sub>2\<close>
    \<open>sourcenode a' = parent_node n\<^sub>3\<close> \<open>targetnode a' = parent_node n\<^sub>4\<close>
  have "matched n\<^sub>1 ([]@n\<^sub>1#ns'@[n\<^sub>3]) n\<^sub>4"
    by(fastforce intro:matched.matched_bracket_param matched_Nil 
                 elim:SDG_edge_valid_SDG_node)
  then obtain nsx where "n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4" by(erule matched_is_SDG_path)
  from \<open>n'' \<in> set (ns@n\<^sub>1#ns'@[n\<^sub>3])\<close> 
  have "((n'' \<in> set ns \<or> n'' = n\<^sub>1) \<or> n'' \<in> set ns') \<or> n'' = n\<^sub>3" by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH1[OF this] have "n'' \<in> HRB_slice {n\<^sub>1}" by simp
    with \<open>n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4\<close> \<open>n\<^sub>4 \<in> S\<close> show ?thesis 
      by -(rule HRB_slice_is_SDG_path_HRB_slice)
  next
    assume "n'' = n\<^sub>1"
    from \<open>n\<^sub>1 is-nsx\<rightarrow>\<^sub>d* n\<^sub>4\<close> have "n\<^sub>1 \<in> sum_SDG_slice1 n\<^sub>4"
      by(fastforce intro:is_SDG_path_slice1 refl_slice1 is_SDG_path_valid_SDG_node)
    with \<open>n'' = n\<^sub>1\<close> \<open>n\<^sub>4 \<in> S\<close> show ?thesis
      by(fastforce intro:combSlice_refl simp:HRB_slice_def)
  next
    assume "n'' \<in> set ns'"
    with \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> have "n'' \<in> sum_SDG_slice2 n\<^sub>3"
      by(rule in_matched_in_slice2)
    with \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "n'' \<in> sum_SDG_slice2 n\<^sub>4"
      by(fastforce intro:slice2_param_out_slice2 SDG_edge_sum_SDG_edge)
    from \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "valid_SDG_node n\<^sub>4" by(rule SDG_edge_valid_SDG_node)
    hence "n\<^sub>4 \<in> sum_SDG_slice1 n\<^sub>4" by(rule refl_slice1)
    from \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> 
    have "CFG_node (parent_node n\<^sub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^sub>4)"
      by(fastforce elim:SDG_edge.cases intro:SDG_return_edge)
    with \<open>n'' \<in> sum_SDG_slice2 n\<^sub>4\<close> \<open>n\<^sub>4 \<in> sum_SDG_slice1 n\<^sub>4\<close> \<open>n\<^sub>4 \<in> S\<close>
    show ?case by(fastforce intro:combSlice_Return_parent_node SDG_edge_sum_SDG_edge 
                            simp:HRB_slice_def)
  next
    assume "n'' = n\<^sub>3"
    from \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "n\<^sub>3 s-p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4" by(rule SDG_edge_sum_SDG_edge)
    from \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "valid_SDG_node n\<^sub>4" by(rule SDG_edge_valid_SDG_node)
    hence "n\<^sub>4 \<in> sum_SDG_slice1 n\<^sub>4" by(rule refl_slice1)
    from \<open>valid_SDG_node n\<^sub>4\<close> have "n\<^sub>4 \<in> sum_SDG_slice2 n\<^sub>4" by(rule refl_slice2)
    with \<open>n\<^sub>3 s-p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> have "n\<^sub>3 \<in> sum_SDG_slice2 n\<^sub>4" by(rule param_out_slice2)
    from \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> 
    have "CFG_node (parent_node n\<^sub>3) -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n\<^sub>4)"
      by(fastforce elim:SDG_edge.cases intro:SDG_return_edge)
    with \<open>n\<^sub>3 \<in> sum_SDG_slice2 n\<^sub>4\<close> \<open>n\<^sub>4 \<in> sum_SDG_slice1 n\<^sub>4\<close> \<open>n'' = n\<^sub>3\<close> \<open>n\<^sub>4 \<in> S\<close>
    show ?case by(fastforce intro:combSlice_Return_parent_node SDG_edge_sum_SDG_edge
                            simp:HRB_slice_def)
  qed
qed


theorem in_realizable_in_HRB_slice:
  "\<lbrakk>realizable n ns n'; n'' \<in> set ns; n' \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S"
proof(induct arbitrary:S rule:realizable.induct)
  case (realizable_matched n ns n') thus ?case by(rule in_matched_in_HRB_slice)
next
  case (realizable_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 V ns' n\<^sub>3)
  note IH = \<open>\<And>S. \<lbrakk>n'' \<in> set ns; n\<^sub>1 \<in> S\<rbrakk> \<Longrightarrow> n'' \<in> HRB_slice S\<close>
  from \<open>n'' \<in> set (ns@n\<^sub>1#ns')\<close> have "(n'' \<in> set ns \<or> n'' = n\<^sub>1) \<or> n'' \<in> set ns'"
    by auto
  thus ?case apply -
  proof(erule disjE)+
    assume "n'' \<in> set ns"
    from IH[OF this] have "n'' \<in> HRB_slice {n\<^sub>1}" by simp
    hence "n'' \<in> HRB_slice {n\<^sub>2}"
    proof(induct rule:HRB_slice_cases)
      case (phase1 n nx)
      from \<open>nx \<in> {n\<^sub>1}\<close> have "nx = n\<^sub>1" by simp
      with \<open>n \<in> sum_SDG_slice1 nx\<close> \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close>
      have "n \<in> sum_SDG_slice1 n\<^sub>2" 
        by(fastforce intro:slice1_call_slice1 slice1_param_in_slice1 
                          SDG_edge_sum_SDG_edge)
      thus ?case
        by(fastforce intro:combine_SDG_slices.combSlice_refl simp:HRB_slice_def)
    next
      case (phase2 nx n' n'' p' n)
      from \<open>nx \<in> {n\<^sub>1}\<close> have "nx = n\<^sub>1" by simp
      with \<open>n' \<in> sum_SDG_slice1 nx\<close> \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close>
      have "n' \<in> sum_SDG_slice1 n\<^sub>2" 
        by(fastforce intro:slice1_call_slice1 slice1_param_in_slice1 
                          SDG_edge_sum_SDG_edge)
      with \<open>n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close> \<open>n \<in> sum_SDG_slice2 n'\<close> show ?case
        by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                     simp:HRB_slice_def)
    qed
    from \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> obtain nsx where "n\<^sub>2 is-nsx\<rightarrow>\<^sub>d* n\<^sub>3"
      by(erule matched_is_SDG_path)
    with \<open>n'' \<in> HRB_slice {n\<^sub>2}\<close> \<open>n\<^sub>3 \<in> S\<close> show ?thesis
      by(fastforce intro:HRB_slice_is_SDG_path_HRB_slice)
  next
    assume "n'' = n\<^sub>1"
    from \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> obtain nsx where "n\<^sub>2 is-nsx\<rightarrow>\<^sub>d* n\<^sub>3"
      by(erule matched_is_SDG_path)
    hence "n\<^sub>2 \<in> sum_SDG_slice1 n\<^sub>2" 
      by(fastforce intro:refl_slice1 is_SDG_path_valid_SDG_node)
    with \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close>
    have "n\<^sub>1 \<in> sum_SDG_slice1 n\<^sub>2"
      by(fastforce intro:call_slice1 param_in_slice1 SDG_edge_sum_SDG_edge)
    hence "n\<^sub>1 \<in> HRB_slice {n\<^sub>2}" by(fastforce intro:combSlice_refl simp:HRB_slice_def)
    with \<open>n\<^sub>2 is-nsx\<rightarrow>\<^sub>d* n\<^sub>3\<close> \<open>n'' = n\<^sub>1\<close> \<open>n\<^sub>3 \<in> S\<close> show ?thesis
      by(fastforce intro:HRB_slice_is_SDG_path_HRB_slice)
  next
    assume "n'' \<in> set ns'"
    from \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> this \<open>n\<^sub>3 \<in> S\<close> show ?thesis
      by(rule in_matched_in_HRB_slice)
  qed
qed


lemma slice1_ics_SDG_path:
  assumes "n \<in> sum_SDG_slice1 n'" and "n \<noteq> n'"
  obtains ns where "CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n'" and "n \<in> set ns"
proof(atomize_elim)
  from \<open>n \<in> sum_SDG_slice1 n'\<close> 
  have "n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns)"
  proof(induct rule:sum_SDG_slice1.induct)
    case refl_slice1 thus ?case by simp
  next
    case (cdep_slice1 n'' n)
    from \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n\<close> have "valid_SDG_node n''" by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^sub>d* n''" by(rule icsSp_Nil)
    from \<open>valid_SDG_node n''\<close> have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n'' = (_Exit_)")
      case True
      with \<open>valid_SDG_node n''\<close> have "n'' = CFG_node (_Exit_)"
        by(rule valid_SDG_node_parent_Exit)
      with \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n\<close> have False by(fastforce intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case False
      from \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n\<close> have "valid_SDG_node n''"
        by(rule sum_SDG_edge_valid_SDG_node)
      from this False obtain ns 
        where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n''"
        by(erule Entry_cc_SDG_path_to_inner_node)
      with \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n\<close> have "CFG_node (_Entry_) cc-ns@[n'']\<rightarrow>\<^sub>d* n"
        by(fastforce intro:ccSp_Append_cdep sum_SDG_edge_SDG_edge)
      hence "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n"
        by(rule cc_SDG_path_ics_SDG_path)
      from \<open>n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns)\<close>
      show ?thesis
      proof
        assume "n = n'"
        with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close> show ?thesis by fastforce
      next
        assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns"
        then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^sub>d* n'" and "n \<in> set nsx"
          by blast
        then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^sub>d* n'"
          by -(erule ics_SDG_path_split)
        with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close>
        show ?thesis by(fastforce intro:ics_SDG_path_Append)
      qed
    qed
  next
    case (ddep_slice1 n'' V n)
    from \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n\<close> have "valid_SDG_node n''" by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^sub>d* n''" by(rule icsSp_Nil)
    from \<open>valid_SDG_node n''\<close> have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n'' = (_Exit_)")
      case True
      with \<open>valid_SDG_node n''\<close> have "n'' = CFG_node (_Exit_)"
        by(rule valid_SDG_node_parent_Exit)
      with \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n\<close> have False by(fastforce intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case False
      from \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n\<close> have "valid_SDG_node n''"
        by(rule sum_SDG_edge_valid_SDG_node)
      from this False obtain ns 
        where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n''"
        by(erule Entry_cc_SDG_path_to_inner_node)
     hence "CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n''"
        by(rule cc_SDG_path_ics_SDG_path)
      show ?thesis
      proof(cases "n'' = n")
        case True
        from \<open>n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns)\<close>
        show ?thesis
        proof
          assume "n = n'"
          with \<open>n'' = n\<close> show ?thesis by simp
        next
          assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns"
          with \<open>n'' = n\<close> show ?thesis by fastforce
        qed
      next
        case False
        with \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n\<close> \<open>CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n''\<close>
        have "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n"
          by -(rule icsSp_Append_ddep)
        from \<open>n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns)\<close>
        show ?thesis
        proof
          assume "n = n'"
          with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close> show ?thesis by fastforce
        next
          assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns"
          then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^sub>d* n'" and "n \<in> set nsx"
            by blast
          then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^sub>d* n'"
            by -(erule ics_SDG_path_split)
          with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close>
          show ?thesis by(fastforce intro:ics_SDG_path_Append)
        qed
      qed
    qed
  next
    case (call_slice1 n'' p n)
    from \<open>n'' s-p\<rightarrow>\<^bsub>call\<^esub> n\<close> have "valid_SDG_node n''" 
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^sub>d* n''" by(rule icsSp_Nil)
    from \<open>valid_SDG_node n''\<close> have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n'' = (_Exit_)")
      case True
      with \<open>valid_SDG_node n''\<close> have "n'' = CFG_node (_Exit_)"
        by(rule valid_SDG_node_parent_Exit)
      with \<open>n'' s-p\<rightarrow>\<^bsub>call\<^esub> n\<close> have False by(fastforce intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case False
      from \<open>n'' s-p\<rightarrow>\<^bsub>call\<^esub> n\<close> have "valid_SDG_node n''"
        by(rule sum_SDG_edge_valid_SDG_node)
      from this False obtain ns 
        where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n''"
        by(erule Entry_cc_SDG_path_to_inner_node)
      with \<open>n'' s-p\<rightarrow>\<^bsub>call\<^esub> n\<close> have "CFG_node (_Entry_) cc-ns@[n'']\<rightarrow>\<^sub>d* n"
        by(fastforce intro:ccSp_Append_call sum_SDG_edge_SDG_edge)
      hence "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n"
        by(rule cc_SDG_path_ics_SDG_path)
      from \<open>n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns)\<close>
      show ?thesis
      proof
        assume "n = n'"
        with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close> show ?thesis by fastforce
      next
        assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns"
        then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^sub>d* n'" and "n \<in> set nsx"
          by blast
        then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^sub>d* n'"
          by -(erule ics_SDG_path_split)
        with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close>
        show ?thesis by(fastforce intro:ics_SDG_path_Append)
      qed
    qed
  next
    case (param_in_slice1 n'' p V n)
    from \<open>n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n\<close> have "valid_SDG_node n''" 
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^sub>d* n''" by(rule icsSp_Nil)
    from \<open>valid_SDG_node n''\<close> have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n'' = (_Exit_)")
      case True
      with \<open>valid_SDG_node n''\<close> have "n'' = CFG_node (_Exit_)"
        by(rule valid_SDG_node_parent_Exit)
      with \<open>n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n\<close> have False by(fastforce intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case False
      from \<open>n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n\<close> have "valid_SDG_node n''"
        by(rule sum_SDG_edge_valid_SDG_node)
      from this False obtain ns 
        where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n''"
        by(erule Entry_cc_SDG_path_to_inner_node)
      hence "CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n''"
        by(rule cc_SDG_path_ics_SDG_path)
      with \<open>n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n\<close> have "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n"
        by -(rule icsSp_Append_param_in)
      from \<open>n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns)\<close>
      show ?thesis
      proof
        assume "n = n'"
        with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close> show ?thesis by fastforce
      next
        assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns"
        then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^sub>d* n'" and "n \<in> set nsx"
          by blast
        then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^sub>d* n'"
          by -(erule ics_SDG_path_split)
        with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close>
        show ?thesis by(fastforce intro:ics_SDG_path_Append)
      qed
    qed
  next
    case (sum_slice1 n'' p n)
    from \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n\<close> have "valid_SDG_node n''" 
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' ics-[]\<rightarrow>\<^sub>d* n''" by(rule icsSp_Nil)
    from \<open>valid_SDG_node n''\<close> have "valid_node (parent_node n'')"
      by(rule valid_SDG_CFG_node)
    thus ?case
    proof(cases "parent_node n'' = (_Exit_)")
      case True
      with \<open>valid_SDG_node n''\<close> have "n'' = CFG_node (_Exit_)"
        by(rule valid_SDG_node_parent_Exit)
      with \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n\<close> have False by(fastforce intro:Exit_no_sum_SDG_edge_source)
      thus ?thesis by simp
    next
      case False
      from \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n\<close> have "valid_SDG_node n''"
        by(rule sum_SDG_edge_valid_SDG_node)
      from this False obtain ns 
        where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n''"
        by(erule Entry_cc_SDG_path_to_inner_node)
      hence "CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n''"
        by(rule cc_SDG_path_ics_SDG_path)
      with \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n\<close> have "CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n"
        by -(rule icsSp_Append_sum)
      from \<open>n = n' \<or> (\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns)\<close>
      show ?thesis
      proof
        assume "n = n'"
        with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close> show ?thesis by fastforce
      next
        assume "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns"
        then obtain nsx where "CFG_node (_Entry_) ics-nsx\<rightarrow>\<^sub>d* n'" and "n \<in> set nsx"
          by blast
        then obtain ns' ns'' where "nsx = ns'@ns''" and "n ics-ns''\<rightarrow>\<^sub>d* n'"
          by -(erule ics_SDG_path_split)
        with \<open>CFG_node (_Entry_) ics-ns@[n'']\<rightarrow>\<^sub>d* n\<close>
        show ?thesis by(fastforce intro:ics_SDG_path_Append)
      qed
    qed
  qed
  with \<open>n \<noteq> n'\<close> show "\<exists>ns. CFG_node (_Entry_) ics-ns\<rightarrow>\<^sub>d* n' \<and> n \<in> set ns" by simp
qed


lemma slice2_irs_SDG_path:
  assumes "n \<in> sum_SDG_slice2 n'" and "valid_SDG_node n'"
  obtains ns where "n irs-ns\<rightarrow>\<^sub>d* n'"
using assms
by(induct rule:sum_SDG_slice2.induct,auto intro:intra_return_sum_SDG_path.intros)


theorem HRB_slice_realizable:
  assumes "n \<in> HRB_slice S" and "\<forall>n' \<in> S. valid_SDG_node n'" and "n \<notin> S"
  obtains n' ns where "n' \<in> S" and "realizable (CFG_node (_Entry_)) ns n'" 
  and "n \<in> set ns"
proof(atomize_elim)
  from \<open>n \<in> HRB_slice S\<close> \<open>n \<notin> S\<close>
  show "\<exists>n' ns. n' \<in> S \<and> realizable (CFG_node (_Entry_)) ns n' \<and> n \<in> set ns"
  proof(induct rule:HRB_slice_cases)
    case (phase1 n nx)
    with \<open>n \<notin> S\<close> show ?case
      by(fastforce elim:slice1_ics_SDG_path ics_SDG_path_realizable)
  next
    case (phase2 n' nx n'' p n)
    from \<open>\<forall>n' \<in> S. valid_SDG_node n'\<close> \<open>n' \<in> S\<close> have "valid_SDG_node n'" by simp
    with \<open>nx \<in> sum_SDG_slice1 n'\<close> have "valid_SDG_node nx"
      by(auto elim:slice1_ics_SDG_path ics_SDG_path_split 
              intro:ics_SDG_path_valid_SDG_node)
    with \<open>n \<in> sum_SDG_slice2 nx\<close>
    obtain nsx where "n irs-nsx\<rightarrow>\<^sub>d* nx" by(erule slice2_irs_SDG_path)
    show ?case
    proof(cases "n = nx")
      case True
      show ?thesis
      proof(cases "nx = n'")
        case True
        with \<open>n = nx\<close> \<open>n \<notin> S\<close> \<open>n' \<in> S\<close> have False by simp
        thus ?thesis by simp
      next
        case False
        with \<open>nx \<in> sum_SDG_slice1 n'\<close> obtain ns 
          where "realizable (CFG_node (_Entry_)) ns n'" and "nx \<in> set ns"
          by(fastforce elim:slice1_ics_SDG_path ics_SDG_path_realizable)
        with \<open>n = nx\<close> \<open>n' \<in> S\<close> show ?thesis by blast
      qed
    next
      case False
      with \<open>n irs-nsx\<rightarrow>\<^sub>d* nx\<close> obtain ns
        where "realizable (CFG_node (_Entry_)) ns nx" and "n \<in> set ns"
        by(erule irs_SDG_path_realizable)
      show ?thesis
      proof(cases "nx = n'")
        case True
        with \<open>realizable (CFG_node (_Entry_)) ns nx\<close> \<open>n \<in> set ns\<close> \<open>n' \<in> S\<close>
        show ?thesis by blast
      next
        case False
        with \<open>nx \<in> sum_SDG_slice1 n'\<close> obtain nsx'
          where "CFG_node (_Entry_) ics-nsx'\<rightarrow>\<^sub>d* n'" and "nx \<in> set nsx'"
          by(erule slice1_ics_SDG_path)
        then obtain ns' where "nx ics-ns'\<rightarrow>\<^sub>d* n'" by -(erule ics_SDG_path_split)
        with \<open>realizable (CFG_node (_Entry_)) ns nx\<close>
        obtain ns'' where "realizable (CFG_node (_Entry_)) (ns@ns'') n'"
          by(erule realizable_Append_ics_SDG_path)
        with \<open>n \<in> set ns\<close> \<open>n' \<in> S\<close> show ?thesis by fastforce
      qed
    qed
  qed
qed


theorem HRB_slice_precise:
  "\<lbrakk>\<forall>n' \<in> S. valid_SDG_node n'; n \<notin> S\<rbrakk> \<Longrightarrow>
    n \<in> HRB_slice S = 
    (\<exists>n' ns. n' \<in> S \<and> realizable (CFG_node (_Entry_)) ns n' \<and> n \<in> set ns)"
  by(fastforce elim:HRB_slice_realizable intro:in_realizable_in_HRB_slice)

end

end
