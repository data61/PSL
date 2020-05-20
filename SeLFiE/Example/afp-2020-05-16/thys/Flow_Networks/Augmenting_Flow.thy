section \<open>Augmenting Flows\<close>
theory Augmenting_Flow
imports Residual_Graph
begin

text \<open>
  In this theory, we define the concept of an augmenting flow,
  augmentation with a flow, and show that augmentation of a flow 
  with an augmenting flow yields a valid flow again.
  \<close>

text \<open>We assume that there is a network with a flow @{term f} on it\<close>
context NFlow
begin

subsection \<open>Augmentation of a Flow\<close>
text \<open>The flow can be augmented by another flow, by adding the flows 
  of edges parallel to edges in the network, and subtracting the edges 
  reverse to edges in the network.\<close>
(* TODO: Define in network locale, with \<up> syntax. *)
definition augment :: "'capacity flow \<Rightarrow> 'capacity flow"
where "augment f' \<equiv> \<lambda>(u, v).
  if (u, v) \<in> E then
    f (u, v) + f' (u, v) - f' (v, u)
  else
    0"

text \<open>We define a syntax similar to Cormen et el.:\<close>    
abbreviation (input) augment_syntax (infix "\<up>" 55) 
  where "\<And>f f'. f\<up>f' \<equiv> NFlow.augment c f f'"
text \<open>such that we can write @{term [source] "f\<up>f'"} for the flow @{term f} 
  augmented by @{term f'}.\<close>


subsection \<open>Augmentation yields Valid Flow\<close>
text \<open>We show that, if we augment the flow with a valid flow of
  the residual graph, the augmented flow is a valid flow again, i.e. 
  it satisfies the capacity and conservation constraints:\<close>
context 
  \<comment> \<open>Let the \emph{residual flow} @{term f'} be a flow in the residual graph\<close>
  fixes f' :: "'capacity flow"
  assumes f'_flow: "Flow cf s t f'"
begin  

interpretation f': Flow cf s t f' by (rule f'_flow)

subsubsection \<open>Capacity Constraint\<close>
text \<open>First, we have to show that the new flow satisfies the capacity constraint:\<close>
(* FIXME: Indentation unfortunate, but required to extract snippet for latex presentation *)    
text_raw \<open>\DefineSnippet{augment_flow_presv_cap}{\<close>  
lemma augment_flow_presv_cap: 
  shows "0 \<le> (f\<up>f')(u,v) \<and> (f\<up>f')(u,v) \<le> c(u,v)"
proof (cases "(u,v)\<in>E"; rule conjI) 
  assume [simp]: "(u,v)\<in>E"
  hence "f(u,v) = cf(v,u)" 
    using no_parallel_edge by (auto simp: residualGraph_def)
  also have "cf(v,u) \<ge> f'(v,u)" using f'.capacity_const by auto
  finally(*<*)(xtrans)(*>*) have "f'(v,u) \<le> f(u,v)" .

(*<*){
    note [trans] = xtrans
  (*>*)text_raw \<open>\isanewline\<close>

  text_raw \<open>\ \ \<close>have "(f\<up>f')(u,v) = f(u,v) + f'(u,v) - f'(v,u)"
    by (auto simp: augment_def)
  also have "\<dots> \<ge> f(u,v) + f'(u,v) - f(u,v)"
  (*<*)(is "_ \<ge> \<dots>")(*>*)  using \<open>f'(v,u) \<le> f(u,v)\<close> by auto
  also have "\<dots> = f'(u,v)" by auto
  also have "\<dots> \<ge> 0" using f'.capacity_const by auto
  finally show "(f\<up>f')(u,v) \<ge> 0" .
  (*<*)}(*>*)
    
  have "(f\<up>f')(u,v) = f(u,v) + f'(u,v) - f'(v,u)" 
    by (auto simp: augment_def)
  also have "\<dots> \<le> f(u,v) + f'(u,v)" using f'.capacity_const by auto
  also have "\<dots> \<le> f(u,v) + cf(u,v)" using f'.capacity_const by auto
  also have "\<dots> = f(u,v) + c(u,v) - f(u,v)" 
    by (auto simp: residualGraph_def)
  also have "\<dots> = c(u,v)" by auto
  finally show "(f\<up>f')(u, v) \<le> c(u, v)" .
qed (auto simp: augment_def cap_positive)
text_raw \<open>}%EndSnippet\<close>

  
subsubsection \<open>Conservation Constraint\<close>
text \<open>In order to show the conservation constraint, we need some 
  auxiliary lemmas first.\<close>

text \<open>As there are no parallel edges in the network, and all edges 
  in the residual graph are either parallel or reverse to a network edge,
  we can split summations of the residual flow over outgoing/incoming edges in the 
  residual graph to summations over outgoing/incoming edges in the network.

  Note that the term @{term \<open>E``{u}\<close>} characterizes the successor nodes of @{term \<open>u\<close>},
  and @{term \<open>E\<inverse>``{u}\<close>} characterizes the predecessor nodes of @{term \<open>u\<close>}.
\<close>
(* TODO: Introduce pred/succ functions on Graph *)
private lemma split_rflow_outgoing: 
  "(\<Sum>v\<in>cf.E``{u}. f' (u,v)) = (\<Sum>v\<in>E``{u}. f'(u,v)) + (\<Sum>v\<in>E\<inverse>``{u}. f'(u,v))"
  (is "?LHS = ?RHS")
proof -
  from no_parallel_edge have DJ: "E``{u} \<inter> E\<inverse>``{u} = {}" by auto

  have "?LHS = (\<Sum>v\<in>E``{u} \<union> E\<inverse>``{u}. f' (u,v))"
    apply (rule sum.mono_neutral_left)
    using cfE_ss_invE
    by (auto intro: finite_Image)
  also have "\<dots> = ?RHS"
    apply (subst sum.union_disjoint[OF _ _ DJ])
    by (auto intro: finite_Image)
  finally show "?LHS = ?RHS" .
qed  

private lemma split_rflow_incoming: 
  "(\<Sum>v\<in>cf.E\<inverse>``{u}. f' (v,u)) = (\<Sum>v\<in>E``{u}. f'(v,u)) + (\<Sum>v\<in>E\<inverse>``{u}. f'(v,u))"
  (is "?LHS = ?RHS")
proof -
  from no_parallel_edge have DJ: "E``{u} \<inter> E\<inverse>``{u} = {}" by auto

  have "?LHS = (\<Sum>v\<in>E``{u} \<union> E\<inverse>``{u}. f' (v,u))"
    apply (rule sum.mono_neutral_left)
    using cfE_ss_invE
    by (auto intro: finite_Image)
  also have "\<dots> = ?RHS"
    apply (subst sum.union_disjoint[OF _ _ DJ])
    by (auto intro: finite_Image)
  finally show "?LHS = ?RHS" .
qed  

text \<open>For proving the conservation constraint, let's fix a node @{term u}, which
  is neither the source nor the sink: \<close>
context 
  fixes u :: node
  assumes U_ASM: "u\<in>V - {s,t}"
begin  

text \<open>We first show an auxiliary lemma to compare the 
  effective residual flow on incoming network edges to
  the effective residual flow on outgoing network edges.
  
  Intuitively, this lemma shows that the effective residual flow added to the 
  network edges satisfies the conservation constraint.
\<close>
private lemma flow_summation_aux:
  shows "(\<Sum>v\<in>E``{u}. f' (u,v))  - (\<Sum>v\<in>E``{u}. f' (v,u))
       = (\<Sum>v\<in>E\<inverse>``{u}. f' (v,u)) - (\<Sum>v\<in>E\<inverse>``{u}. f' (u,v))"
   (is "?LHS = ?RHS" is "?A - ?B = ?RHS")
proof -
  text \<open>The proof is by splitting the flows, and careful 
    cancellation of the summands.\<close>
  have "?A = (\<Sum>v\<in>cf.E``{u}. f' (u, v)) - (\<Sum>v\<in>E\<inverse>``{u}. f' (u, v))"
    by (simp add: split_rflow_outgoing)
  also have "(\<Sum>v\<in>cf.E``{u}. f' (u, v)) = (\<Sum>v\<in>cf.E\<inverse>``{u}. f' (v, u))"  
    using U_ASM
    by (simp add: f'.conservation_const_pointwise)
  finally have "?A = (\<Sum>v\<in>cf.E\<inverse>``{u}. f' (v, u)) - (\<Sum>v\<in>E\<inverse>``{u}. f' (u, v))" 
    by simp
  moreover
  have "?B = (\<Sum>v\<in>cf.E\<inverse>``{u}. f' (v, u)) - (\<Sum>v\<in>E\<inverse>``{u}. f' (v, u))"
    by (simp add: split_rflow_incoming)
  ultimately show "?A - ?B = ?RHS" by simp
qed    

text \<open>Finally, we are ready to prove that the augmented flow satisfies the 
  conservation constraint:\<close>
lemma augment_flow_presv_con: 
  shows "(\<Sum>e \<in> outgoing u. augment f' e) = (\<Sum>e \<in> incoming u. augment f' e)"
    (is "?LHS = ?RHS")
proof -
  text \<open>We define shortcuts for the successor and predecessor nodes of @{term u} 
    in the network:\<close>
  let ?Vo = "E``{u}" let ?Vi = "E\<inverse>``{u}"

  text \<open>Using the auxiliary lemma for the effective residual flow,
    the proof is straightforward:\<close>
  have "?LHS = (\<Sum>v\<in>?Vo. augment f' (u,v))"
    by (auto simp: sum_outgoing_pointwise)
  also have "\<dots> 
    = (\<Sum>v\<in>?Vo. f (u,v) + f'(u,v) - f'(v,u))"  
    by (auto simp: augment_def)
  also have "\<dots> 
    = (\<Sum>v\<in>?Vo. f (u,v)) + (\<Sum>v\<in>?Vo. f' (u,v)) - (\<Sum>v\<in>?Vo. f' (v,u))"
    by (auto simp: sum_subtractf sum.distrib)
  also have "\<dots> 
    = (\<Sum>v\<in>?Vi. f (v,u)) + (\<Sum>v\<in>?Vi. f' (v,u)) - (\<Sum>v\<in>?Vi. f' (u,v))" 
    by (auto simp: conservation_const_pointwise[OF U_ASM] flow_summation_aux)
  also have "\<dots> 
    = (\<Sum>v\<in>?Vi. f (v,u) + f' (v,u) - f' (u,v))" 
    by (auto simp: sum_subtractf sum.distrib)
  also have "\<dots> 
    = (\<Sum>v\<in>?Vi. augment f' (v,u))"  
    by (auto simp: augment_def)
  also have "\<dots> 
    = ?RHS"
    by (auto simp: sum_incoming_pointwise)
  finally show "?LHS = ?RHS" .
qed  
text \<open>Note that we tried to follow the proof presented by Cormen et al.~\cite{CLRS09} 
  as closely as possible. Unfortunately, this proof generalizes the summation to all 
  nodes immediately, rendering the first equation invalid.
  Trying to fix this error, we encountered that the step that uses the conservation 
  constraints on the augmenting flow is more subtle as indicated in the original proof.
  Thus, we moved this argument to an auxiliary lemma. \<close>


end \<comment> \<open>@{term u} is node\<close>

text \<open>As main result, we get that the augmented flow is again a valid flow.\<close>
corollary augment_flow_presv: "Flow c s t (f\<up>f')"
  using augment_flow_presv_cap augment_flow_presv_con 
  by (rule_tac intro_Flow) auto

subsection \<open>Value of the Augmented Flow\<close>
text \<open>Next, we show that the value of the augmented flow is the sum of the values
  of the original flow and the augmenting flow.\<close>
  
lemma augment_flow_value: "Flow.val c s (f\<up>f') = val + Flow.val cf s f'"
proof -
  interpret f'': Flow c s t "f\<up>f'" using augment_flow_presv . 

  txt \<open>For this proof, we set up Isabelle's rewriting engine for rewriting of sums.
    In particular, we add lemmas to convert sums over incoming or outgoing 
    edges to sums over all vertices. This allows us to write the summations
    from Cormen et al.~a bit more concise, leaving some of the tedious 
    calculation work to the computer.\<close>
  note sum_simp_setup[simp] = 
    sum_outgoing_alt[OF capacity_const] s_node
    sum_incoming_alt[OF capacity_const]
    cf.sum_outgoing_alt[OF f'.capacity_const]
    cf.sum_incoming_alt[OF f'.capacity_const]
    sum_outgoing_alt[OF f''.capacity_const]
    sum_incoming_alt[OF f''.capacity_const]
    sum_subtractf sum.distrib
  
  txt \<open>Note that, if neither an edge nor its reverse is in the graph,
    there is also no edge in the residual graph, and thus the flow value
    is zero.\<close>  
  have aux1: "f'(u,v) = 0" if "(u,v)\<notin>E" "(v,u)\<notin>E" for u v
  proof -
    from that cfE_ss_invE have "(u,v)\<notin>cf.E" by auto
    thus "f'(u,v) = 0" by auto
  qed  

  txt \<open>Now, the proposition follows by straightforward rewriting of 
    the summations:\<close>
  have "f''.val = (\<Sum>u\<in>V. augment f' (s, u) - augment f' (u, s))" 
    unfolding f''.val_def by simp
  also have "\<dots> = (\<Sum>u\<in>V. f (s, u) - f (u, s) + (f' (s, u) - f' (u, s)))"
    \<comment> \<open>Note that this is the crucial step of the proof, which Cormen et al. leave as an exercise.\<close>
    by (rule sum.cong) (auto simp: augment_def no_parallel_edge aux1)
  also have "\<dots> = val + Flow.val cf s f'"  
    unfolding val_def f'.val_def by simp
  finally show "f''.val = val + f'.val" .  
qed    

txt \<open>Note, there is also an automatic proof. When creating the above 
    explicit proof, this automatic one has been used to extract meaningful
    subgoals, abusing Isabelle as a term rewriter.\<close>
lemma "Flow.val c s (f\<up>f') = val + Flow.val cf s f'"
proof -
  interpret f'': Flow c s t "f\<up>f'" using augment_flow_presv . 

  have aux1: "f'(u,v) = 0" if A: "(u,v)\<notin>E" "(v,u)\<notin>E" for u v
  proof -
    from A cfE_ss_invE have "(u,v)\<notin>cf.E" by auto
    thus "f'(u,v) = 0" by auto
  qed  

  show ?thesis
    unfolding val_def f'.val_def f''.val_def
    apply (simp del:
      add: 
      sum_outgoing_alt[OF capacity_const] s_node
      sum_incoming_alt[OF capacity_const]
      sum_outgoing_alt[OF f''.capacity_const]
      sum_incoming_alt[OF f''.capacity_const]
      cf.sum_outgoing_alt[OF f'.capacity_const]
      cf.sum_incoming_alt[OF f'.capacity_const]
      sum_subtractf[symmetric] sum.distrib[symmetric]
      )
    apply (rule sum.cong)
    apply (auto simp: augment_def no_parallel_edge aux1)
    done
qed


end \<comment> \<open>Augmenting flow\<close>
end \<comment> \<open>Network flow\<close>

end \<comment> \<open>Theory\<close>
