theory TopoS_Interface
imports Main "Lib/FiniteGraph" TopoS_Vertices "Lib/TopoS_Util"
begin



section \<open>Security Invariants\<close>
  text\<open>
    A good documentation of this formalization is available in \cite{diekmann2014forte}. 
\<close>

  text\<open>
    We define security invariants over a graph.
    The graph corresponds to the network's access control structure.
\<close>

  (*TODO: make datatype!*)
  \<comment> \<open>@{typ "'v"} is the type of the nodes in the graph (hosts in the network). 
     @{typ "'a"} is the type of the host attributes.\<close>
  record ('v::vertex, 'a) TopoS_Params =
    node_properties :: "'v::vertex \<Rightarrow> 'a option"

text\<open>
A Security Invariant is defined as locale.

We successively define more and more locales with more and more assumptions.
This clearly depicts which assumptions are necessary to use certain features of a Security Invariant.
In addition, it makes instance proofs of Security Invariants easier, since the lemmas obtained by an (easy, few assumptions) instance proof 
can be used for the complicated (more assumptions) instance proofs.

A security Invariant consists of one function: \<open>sinvar\<close>.
Essentially, it is a predicate over the policy (depicted as graph \<open>G\<close> and a host attribute mapping (\<open>nP\<close>)).
\<close>

text \<open>A Security Invariant where the offending flows (flows that invalidate the policy) can be defined and calculated.
No assumptions are necessary for this step.
\<close>  
  locale SecurityInvariant_withOffendingFlows = 
    fixes sinvar::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool" \<comment> \<open>policy @{text "\<Rightarrow>"} host attribute mapping @{text "\<Rightarrow>"} bool\<close>
   begin
    \<comment> \<open>Offending Flows definitions:\<close>
    definition is_offending_flows::"('v \<times> 'v) set \<Rightarrow> 'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool" where
      "is_offending_flows f G nP \<equiv> \<not> sinvar G nP \<and> sinvar (delete_edges G f) nP"
    
    \<comment> \<open>Above definition is not minimal:\<close>
    definition is_offending_flows_min_set::"('v \<times> 'v) set \<Rightarrow> 'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> bool" where
      "is_offending_flows_min_set f G nP \<equiv> is_offending_flows f G nP \<and> 
        (\<forall> (e1, e2) \<in> f. \<not> sinvar (add_edge e1 e2 (delete_edges G f)) nP)"

    \<comment> \<open>The set of all offending flows.\<close>
    definition set_offending_flows::"'v graph \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<times> 'v) set set" where
      "set_offending_flows G  nP = {F. F \<subseteq> (edges G) \<and> is_offending_flows_min_set F G nP}"
  

    text \<open>Some of the @{const set_offending_flows} definition\<close>
    lemma offending_not_empty: "\<lbrakk> F \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow> F \<noteq> {}"
     by(auto simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def)
    lemma empty_offending_contra:
       "\<lbrakk> F \<in> set_offending_flows G nP; F = {}\<rbrakk> \<Longrightarrow> False"
     by(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def)
    lemma offending_notevalD: "F \<in> set_offending_flows G nP \<Longrightarrow> \<not> sinvar G nP"
     by(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def)
    lemma sinvar_no_offending: "sinvar G nP \<Longrightarrow> set_offending_flows G nP = {}"
      by(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def)
    theorem removing_offending_flows_makes_invariant_hold:
      "\<forall>F \<in> set_offending_flows G nP. sinvar (delete_edges G F) nP"
      proof(cases "sinvar G nP")
       case True
        hence no_offending: "set_offending_flows G nP = {}" using sinvar_no_offending by simp
        thus "\<forall>F\<in>set_offending_flows G nP. sinvar (delete_edges G F) nP" using empty_iff by simp
       next
       case False thus "\<forall>F\<in>set_offending_flows G nP. sinvar (delete_edges G F) nP"
        by(simp add: set_offending_flows_def is_offending_flows_def is_offending_flows_min_set_def graph_ops)
      qed
  corollary valid_without_offending_flows:
  "\<lbrakk> F \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow> sinvar (delete_edges G F) nP"
    by(simp add: removing_offending_flows_makes_invariant_hold)

  lemma set_offending_flows_simp: 
    "\<lbrakk> wf_graph G \<rbrakk> \<Longrightarrow>
      set_offending_flows G nP = {F. F \<subseteq> edges G \<and>
        (\<not> sinvar G nP \<and> sinvar \<lparr>nodes = nodes G, edges = edges G - F\<rparr> nP) \<and>
        (\<forall>(e1, e2)\<in>F. \<not> sinvar \<lparr>nodes = nodes G, edges = {(e1, e2)} \<union> (edges G - F)\<rparr> nP)}"
    apply(simp only: set_offending_flows_def is_offending_flows_min_set_def 
      is_offending_flows_def delete_edges_simp2 add_edge_def graph.select_convs)
    apply(subgoal_tac "\<And>F e1 e2. F \<subseteq> edges G \<Longrightarrow> (e1, e2) \<in> F \<Longrightarrow> nodes G \<union> {e1, e2} = nodes G")
     apply fastforce
    apply(simp add: wf_graph_def)
    by (metis fst_conv imageI in_mono insert_absorb snd_conv)

   end



print_locale! SecurityInvariant_withOffendingFlows


text\<open>
The locale \<open>SecurityInvariant_withOffendingFlows\<close> has no assumptions about the security invariant \<open>sinvar\<close>.
Undesirable things may happen:
The offending flows can be empty, even for a violated invariant.

We provide an example, the security invariant @{term "(\<lambda>_ _. False)"}.
As host attributes, we simply use the identity function @{const id}.
\<close>
lemma "SecurityInvariant_withOffendingFlows.set_offending_flows (\<lambda>_ _. False) \<lparr> nodes = {''v1''}, edges={} \<rparr> id = {}"
by %invisible (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def 
  SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def SecurityInvariant_withOffendingFlows.is_offending_flows_def)
lemma "SecurityInvariant_withOffendingFlows.set_offending_flows (\<lambda>_ _. False) 
  \<lparr> nodes = {''v1'', ''v2''}, edges = {(''v1'', ''v2'')} \<rparr> id = {}"
by %invisible (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def 
  SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def SecurityInvariant_withOffendingFlows.is_offending_flows_def)

text \<open>In general, there exists a @{term sinvar} such that the invariant does not hold and no offending flows exits.\<close>
  lemma "\<exists>sinvar. \<not> sinvar G nP \<and> SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP = {}"
  apply(simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
    SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def SecurityInvariant_withOffendingFlows.is_offending_flows_def)
  apply(rule_tac x="(\<lambda>_ _. False)" in exI)
  apply(simp)
  done


text\<open>Thus, we introduce usefulness properties that prohibits such useless invariants.\<close>
text\<open>We summarize them in an invariant.
It requires the following: 
\begin{enumerate}
  \item The offending flows are always defined.
  \item The invariant is monotonic, i.e. prohibiting more is more secure.
  \item And, the (non-minimal) offending flows are monotonic, i.e. prohibiting more solves more security issues.
\end{enumerate}

Later, we will show that is suffices to show that the invariant is monotonic. The other two properties can be derived.
\<close>

  locale SecurityInvariant_preliminaries = SecurityInvariant_withOffendingFlows sinvar
    for sinvar
    +
    assumes 
      defined_offending:
      "\<lbrakk> wf_graph G; \<not> sinvar G nP \<rbrakk> \<Longrightarrow> set_offending_flows G nP \<noteq> {}"
    and
      mono_sinvar:
      "\<lbrakk> wf_graph \<lparr> nodes = N, edges = E \<rparr>; E' \<subseteq> E; sinvar \<lparr> nodes = N, edges = E \<rparr> nP \<rbrakk> \<Longrightarrow> 
        sinvar \<lparr> nodes = N, edges = E' \<rparr> nP"
    and mono_offending:
      "\<lbrakk> wf_graph G; is_offending_flows ff G nP \<rbrakk> \<Longrightarrow> is_offending_flows (ff \<union> f') G nP"
  begin

  text \<open>
    \begin{small}
    To instantiate a @{const SecurityInvariant_preliminaries}, here are some hints: 
    Have a look at the \<open>TopoS_withOffendingFlows.thy\<close> file.
    There is a definition of @{prop sinvar_mono}. It impplies @{prop mono_sinvar} and @{prop mono_offending}
    \<open>apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_sinvar_mono[OF sinvar_mono])
    apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])\<close>
  
    In addition, \<open>SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono]\<close> gives a nice proof rule for
    @{prop defined_offending}
  
    Basically, \<open>sinvar_mono.\<close> implies almost all assumptions here and is equal to @{prop mono_sinvar}.
    \end{small}
\<close>
  end


subsection\<open>Security Invariants with secure auto-completion of host attribute mappings\<close>

text\<open>
We will now add a new artifact to the Security Invariant.
It is a secure default host attribute, we will use the symbol \<open>\<bottom>\<close>.

The newly introduced Boolean \<open>receiver_violation\<close> tells whether a security violation happens at the sender's or the receiver's side.

The details can be looked up in \cite{diekmann2014forte}. 
\<close>

  \<comment> \<open>Some notes about the notation:
          @{term "fst ` F"} means to apply the function @{const "fst"} to the set @{term "F"} element-wise.
          Example: If @{term "F"} is a set of directed edges, 
          @{term "F \<subseteq> edges G"}, then @{term "fst ` F"}
          is the set of senders and @{term "snd ` f"} the set of receivers.\<close>

  locale SecurityInvariant = SecurityInvariant_preliminaries sinvar
    for sinvar::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
    +
    fixes default_node_properties :: "'a" ("\<bottom>") 
    and receiver_violation :: "bool"
    assumes 
      \<comment> \<open>default value can never fix a security violation.\<close>
      \<comment> \<open>Idea: Assume there is a violation, then there is some offending flow. 
        @{text receiver_violation} defines whether the violation happens at the sender's or the receiver's side. 
        We call the place of the violation the \emph{offending host}. 
        We replace the host attribute of the offending host with the default attribute. 
        Giving an offending host, a \emph{secure} default attribute does not change whether the invariant holds.
        I.e.\ this reconfiguration does not remove information, thus preserves all security critical information.
        Thought experiment preliminaries: Can a default configuration ever solve an existing security violation? NO!
        Thought experiment 1: admin forgot to configure host, hence it is handled by default configuration value ...
        Thought experiment 2: new node (attacker) is added to the network. What is its default configuration value ...\<close>
      default_secure:
      "\<lbrakk> wf_graph G; \<not> sinvar G nP; F \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow>
        (\<not> receiver_violation \<longrightarrow> i \<in> fst ` F \<longrightarrow> \<not> sinvar G (nP(i := \<bottom>))) \<and>
        (receiver_violation \<longrightarrow> i \<in> snd ` F \<longrightarrow> \<not> sinvar G (nP(i := \<bottom>)))"
      and
      default_unique:
      "otherbot \<noteq> \<bottom> \<Longrightarrow> 
        \<exists> (G::('v::vertex) graph) nP i F. wf_graph G \<and> \<not> sinvar G nP \<and> F \<in> set_offending_flows G nP \<and> 
         sinvar (delete_edges G F) nP \<and>
         (\<not> receiver_violation \<longrightarrow> i \<in> fst ` F \<and> sinvar G (nP(i := otherbot))) \<and>
         (receiver_violation \<longrightarrow> i \<in> snd ` F \<and> sinvar G (nP(i := otherbot))) "
   begin
    \<comment> \<open>Removes option type, replaces with default host attribute\<close>
    fun node_props :: "('v, 'a) TopoS_Params \<Rightarrow> ('v \<Rightarrow> 'a)" where
    "node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> \<bottom>))"

    definition node_props_formaldef :: "('v, 'a) TopoS_Params \<Rightarrow> ('v \<Rightarrow> 'a)" where
    "node_props_formaldef P \<equiv>
    (\<lambda> i. (if i \<in> dom (node_properties P) then the (node_properties P i) else \<bottom>))"

    lemma node_props_eq_node_props_formaldef: "node_props_formaldef = node_props"
     by(simp add: fun_eq_iff node_props_formaldef_def option.case_eq_if domIff)

    text\<open>
      Checking whether a security invariant holds.
      \begin{enumerate}
        \item check that the policy @{term G} is syntactically valid
        \item check the security invariant @{term sinvar}
      \end{enumerate}
\<close>
    definition eval::"'v graph \<Rightarrow> ('v, 'a) TopoS_Params \<Rightarrow> bool" where
    "eval G P \<equiv> wf_graph G \<and> sinvar G (node_props P)"


    lemma unique_common_math_notation:
    assumes "\<forall>G nP i F. wf_graph (G::('v::vertex) graph) \<and> \<not> sinvar G nP \<and> F \<in> set_offending_flows G nP \<and> 
         sinvar (delete_edges G F) nP \<and> 
         (\<not> receiver_violation \<longrightarrow> i \<in> fst ` F \<longrightarrow> \<not> sinvar G (nP(i := otherbot))) \<and>
         (receiver_violation \<longrightarrow> i \<in> snd ` F \<longrightarrow> \<not> sinvar G (nP(i := otherbot)))"
    shows "otherbot = \<bottom>"
    apply(rule ccontr)
    apply(drule default_unique)
    using assms by blast
   end

print_locale! SecurityInvariant



subsection\<open>Information Flow Security and Access Control\<close>
text\<open>

@{term receiver_violation} defines the offending host. Thus, it defines when the violation happens. 

We found that this coincides with the invariant's security strategy. 

\begin{description}
\item[ACS] If the violation happens at the sender, we have an access control strategy (\emph{ACS}). 
I.e.\ the sender does not have the appropriate rights to initiate the connection.

\item[IFS] If the violation happens at the receiver, we have an information flow security strategy (\emph{IFS})
I.e.\ the receiver lacks the appropriate security level to retrieve the (confidential) information. 
The violations happens only when the receiver reads the data.
\end{description}

We refine our @{term SecurityInvariant} locale.
\<close>

subsection \<open>Information Flow Security Strategy (IFS)\<close>
  locale SecurityInvariant_IFS = SecurityInvariant_preliminaries sinvar
      for sinvar::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
      +
      fixes default_node_properties :: "'a" ("\<bottom>") 
      assumes  default_secure_IFS:
        "\<lbrakk> wf_graph G; f \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow>
          \<forall>i \<in> snd` f. \<not> sinvar G (nP(i := \<bottom>))"
      and
      \<comment> \<open>If some otherbot fulfills @{text default_secure}, it must be @{term "\<bottom>"} 
             Hence, @{term "\<bottom>"} is uniquely defined\<close>
      default_unique_IFS:
      "(\<forall>G f nP i. wf_graph G \<and> f \<in> set_offending_flows G nP \<and> i \<in> snd` f 
                \<longrightarrow> \<not> sinvar G (nP(i := otherbot))) \<Longrightarrow> otherbot = \<bottom>"
      begin
        lemma default_unique_EX_notation: "otherbot \<noteq> \<bottom> \<Longrightarrow> 
          \<exists> G nP i f. wf_graph G \<and> \<not> sinvar G nP \<and> f \<in> set_offending_flows G nP \<and> 
           sinvar (delete_edges G f) nP \<and>
           (i \<in> snd` f \<and> sinvar G (nP(i := otherbot)))"
          apply(erule contrapos_pp)
          apply(simp)
          using default_unique_IFS SecurityInvariant_withOffendingFlows.valid_without_offending_flows offending_notevalD
          by metis
      end
  
  sublocale SecurityInvariant_IFS \<subseteq> SecurityInvariant where receiver_violation=True
  apply(unfold_locales)
   apply(simp add: default_secure_IFS)
  apply(simp only: HOL.simp_thms)
  apply(drule default_unique_EX_notation)
  apply(assumption)
  done

  (*other direction*)
  locale SecurityInvariant_IFS_otherDirectrion = SecurityInvariant where receiver_violation=True
  sublocale SecurityInvariant_IFS_otherDirectrion \<subseteq> SecurityInvariant_IFS
  apply(unfold_locales)
   apply (metis default_secure offending_notevalD)
  apply(erule contrapos_pp)
  apply(simp)
  apply(drule default_unique)
  apply(simp)
  apply(blast)
  done
  

lemma default_uniqueness_by_counterexample_IFS:
  assumes "(\<forall>G F nP i. wf_graph G \<and> F \<in> SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP \<and> i \<in> snd` F 
                \<longrightarrow> \<not> sinvar G (nP(i := otherbot)))"
  and "otherbot \<noteq> default_value \<Longrightarrow>
    \<exists>G nP i F. wf_graph G \<and> \<not> sinvar G nP \<and> F \<in> (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP) \<and>
       sinvar (delete_edges G F) nP \<and>
        i \<in> snd ` F \<and> sinvar G (nP(i := otherbot)) "
   shows "otherbot = default_value"
   using assms by blast


subsection \<open>Access Control Strategy (ACS)\<close>
  locale SecurityInvariant_ACS = SecurityInvariant_preliminaries sinvar
      for sinvar::"('v::vertex) graph \<Rightarrow> ('v::vertex \<Rightarrow> 'a) \<Rightarrow> bool"
      +
      fixes default_node_properties :: "'a" ("\<bottom>") 
      assumes  default_secure_ACS:
        "\<lbrakk> wf_graph G; f \<in> set_offending_flows G nP \<rbrakk> \<Longrightarrow>
          \<forall>i \<in> fst` f. \<not> sinvar G (nP(i := \<bottom>))"
      and
      default_unique_ACS:
      "(\<forall>G f nP i. wf_graph G \<and> f \<in> set_offending_flows G nP \<and> i \<in> fst` f 
                \<longrightarrow> \<not> sinvar G (nP(i := otherbot))) \<Longrightarrow> otherbot = \<bottom>"
      begin
        lemma default_unique_EX_notation: "otherbot \<noteq> \<bottom> \<Longrightarrow> 
          \<exists> G nP i f. wf_graph G \<and> \<not> sinvar G nP \<and> f \<in> set_offending_flows G nP \<and> 
           sinvar (delete_edges G f) nP \<and>
           (i \<in> fst` f \<and> sinvar G (nP(i := otherbot)))"
          apply(erule contrapos_pp)
          apply(simp)
          using default_unique_ACS SecurityInvariant_withOffendingFlows.valid_without_offending_flows offending_notevalD
          by metis
      end
  
  sublocale SecurityInvariant_ACS \<subseteq> SecurityInvariant where receiver_violation=False
  apply(unfold_locales)
   apply(simp add: default_secure_ACS)
  apply(simp only: HOL.simp_thms)
  apply(drule default_unique_EX_notation)
  apply(assumption)
  done


  (*other direction*)
  locale SecurityInvariant_ACS_otherDirectrion = SecurityInvariant where receiver_violation=False
  sublocale SecurityInvariant_ACS_otherDirectrion \<subseteq> SecurityInvariant_ACS
  apply(unfold_locales)
   apply (metis default_secure offending_notevalD)
  apply(erule contrapos_pp)
  apply(simp)
  apply(drule default_unique)
  apply(simp)
  apply(blast)
  done


lemma default_uniqueness_by_counterexample_ACS:
  assumes "(\<forall>G F nP i. wf_graph G \<and> F \<in> SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP \<and> i \<in> fst ` F 
                \<longrightarrow> \<not> sinvar G (nP(i := otherbot)))"
  and "otherbot \<noteq> default_value \<Longrightarrow>
    \<exists>G nP i F. wf_graph G \<and> \<not> sinvar G nP \<and> F \<in> (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP) \<and>
       sinvar (delete_edges G F) nP \<and>
        i \<in> fst ` F \<and> sinvar G (nP(i := otherbot))"
  shows "otherbot = default_value"
  using assms by blast


text\<open>The sublocale relationships tell that the simplified @{const SecurityInvariant_ACS} and @{const SecurityInvariant_IFS} 
  assumptions suffice to do tho generic SecurityInvariant assumptions.\<close>

end
