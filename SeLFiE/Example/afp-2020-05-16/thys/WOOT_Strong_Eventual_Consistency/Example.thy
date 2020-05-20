section \<open>Example\label{sec:example}\<close>

theory Example
  imports SEC
begin

text \<open>In this section we formalize the example from Figure \ref{fig:session} for a possible run of 
the WOOT framework with three peers, each performing an edit operation. We verify that it fulfills
the conditions of the locale @{locale dist_execution} and apply the theorems.\<close>

datatype example_peers
  = PeerA
  | PeerB
  | PeerC
derive linorder example_peers

fun example_events :: "example_peers \<Rightarrow> (example_peers, char) event list" where
  "example_events PeerA = [
      Send (Insert (InsertMessage \<turnstile> (PeerA, 0) \<stileturn> CHR ''B'')),
      Receive (PeerA, 0) (Insert (InsertMessage \<turnstile> (PeerA, 0) \<stileturn> CHR ''B'')),
      Receive (PeerB, 0) (Insert (InsertMessage \<turnstile> (PeerB, 0) \<stileturn> CHR ''A'')),
      Receive (PeerC, 1) (Insert (InsertMessage \<lbrakk>(PeerA, 0)\<rbrakk>  (PeerC, 1) \<stileturn> CHR ''R''))
  ]" |
  "example_events PeerB = [
      Send (Insert (InsertMessage \<turnstile> (PeerB, 0) \<stileturn> CHR ''A'')),
      Receive (PeerB, 0) (Insert (InsertMessage \<turnstile> (PeerB, 0) \<stileturn> CHR ''A'')),
      Receive (PeerA, 0) (Insert (InsertMessage \<turnstile> (PeerA, 0) \<stileturn> CHR ''B'')),
      Receive (PeerC, 1) (Insert (InsertMessage \<lbrakk>(PeerA, 0)\<rbrakk>  (PeerC, 1) \<stileturn> CHR ''R''))
  ]" |
  "example_events PeerC = [
      Receive (PeerA, 0) (Insert (InsertMessage \<turnstile> (PeerA, 0) \<stileturn> CHR ''B'')),
      Send (Insert (InsertMessage \<lbrakk>(PeerA, 0)\<rbrakk>  (PeerC, 1) \<stileturn> CHR ''R'')),
      Receive (PeerC, 1) (Insert (InsertMessage \<lbrakk>(PeerA, 0)\<rbrakk>  (PeerC, 1) \<stileturn> CHR ''R'')),
      Receive (PeerB, 0) (Insert (InsertMessage \<turnstile> (PeerB, 0) \<stileturn> CHR ''A''))
  ]"

text \<open>The function @{term example_events} returns the sequence of events that each 
peer evaluates. We instantiate the preliminary context by showing that the set of 
peers is finite.\<close>

interpretation example: dist_execution_preliminary "example_events"
proof
  have a:"UNIV = {PeerA, PeerB, PeerC}" 
    using example_events.cases by auto
  show "finite (UNIV :: example_peers set)" by (simp add:a)
qed

text \<open>
  To prove that the @{term happened_before} relation is acyclic, we provide an  order on the state
  that is consistent with it, i.e.:
  \begin{itemize}
  \item  The assigned indicies for
  successive states of the same peer are increasing.
  \item The assigned index of a state receiving a message is 
    larger than the assigned index of the messages source state.
  \end{itemize}
\<close>

fun witness_acyclic_events :: "example_peers event_id \<Rightarrow> nat"
  where 
    "witness_acyclic_events (PeerA, 0) = 0" |
    "witness_acyclic_events (PeerB, 0) = 1" |
    "witness_acyclic_events (PeerA, (Suc 0)) = 2" |
    "witness_acyclic_events (PeerB, (Suc 0)) = 3" |
    "witness_acyclic_events (PeerC, 0) = 4" |
    "witness_acyclic_events (PeerC, (Suc 0)) = 5" |
    "witness_acyclic_events (PeerC, (Suc (Suc 0))) = 6" |
    "witness_acyclic_events (PeerC, (Suc (Suc (Suc 0)))) = 7" |
    "witness_acyclic_events (PeerA, (Suc (Suc 0))) = 8" |
    "witness_acyclic_events (PeerA, (Suc (Suc (Suc 0)))) = 9" |
    "witness_acyclic_events (PeerB, (Suc (Suc 0))) = 8" |
    "witness_acyclic_events (PeerB, (Suc (Suc (Suc 0)))) = 9" |
    "witness_acyclic_events (PeerA, (Suc (Suc (Suc (Suc n))))) = undefined" |
    "witness_acyclic_events (PeerB, (Suc (Suc (Suc (Suc n))))) = undefined" |
    "witness_acyclic_events (PeerC, (Suc (Suc (Suc (Suc n))))) = undefined"

text \<open>
  To prove that the created messages make sense, we provide the edit operation
  that results with it. The first function is the inserted letter and the second
  function is the position the letter was inserted.
\<close>

fun witness_create_letter :: "example_peers event_id \<Rightarrow> char"
  where 
    "witness_create_letter (PeerA, 0) = CHR ''B''" |
    "witness_create_letter (PeerB, 0) = CHR ''A''" |
    "witness_create_letter (PeerC, Suc 0) = CHR ''R''"

fun witness_create_position :: "example_peers event_id \<Rightarrow> nat"
  where 
    "witness_create_position (PeerA, 0) = 0" |
    "witness_create_position (PeerB, 0) = 0" |
    "witness_create_position (PeerC, Suc 0) = 1"

text \<open>
  To prove that dependencies of a message are received before a message, we
  provide the event id as well as the message, when the peer received a 
  messages dependency.\<close>

fun witness_deps_received_at :: "example_peers event_id \<Rightarrow> example_peers event_id \<Rightarrow> nat"
  where
    "witness_deps_received_at (PeerA, Suc (Suc (Suc 0))) (PeerA, 0) = 1" |
    "witness_deps_received_at (PeerB, Suc (Suc (Suc 0))) (PeerA, 0) = 2" |
    "witness_deps_received_at (PeerC, Suc (Suc 0)) (PeerA, 0) = 0"

fun witness_deps_received_is :: "example_peers event_id \<Rightarrow> example_peers event_id \<Rightarrow> (example_peers event_id, char) insert_message"
  where
    "witness_deps_received_is (PeerA, Suc (Suc (Suc 0))) (PeerA, 0) = (InsertMessage \<turnstile> (PeerA, 0) \<stileturn> CHR ''B'')" |
    "witness_deps_received_is (PeerB, Suc (Suc (Suc 0))) (PeerA, 0) = (InsertMessage \<turnstile> (PeerA, 0) \<stileturn> CHR ''B'')" |
    "witness_deps_received_is (PeerC, Suc (Suc 0)) (PeerA, 0) = (InsertMessage \<turnstile> (PeerA, 0) \<stileturn> CHR ''B'')"

lemma well_order_consistent:
  fixes i j 
  assumes "example.happened_immediately_before i j"
  shows "witness_acyclic_events i < witness_acyclic_events j"
  using assms
  apply (rule_tac [!] witness_acyclic_events.cases [where x="i"])
  apply (rule_tac [!] witness_acyclic_events.cases [where x="j"])
  by simp+

text \<open>Finally we show that the @{term example_events} meet the assumptions
  for the distributed execution context.\<close>

interpretation example: dist_execution "example_events"
proof
  fix i s m
  show 
    "dist_execution_preliminary.event_at example_events i (Receive s m) \<Longrightarrow>
     dist_execution_preliminary.event_at example_events s (Send m)"
    apply (rule_tac [!] witness_acyclic_events.cases [where x="i"])
    by simp+
next
  fix i j s :: "example_peers event_id"
  fix m
  show "example.event_at i (Receive s m) \<Longrightarrow>
       example.event_at j (Receive s m) \<Longrightarrow> fst i = fst j \<Longrightarrow> i = j"
  apply (rule_tac [!] witness_acyclic_events.cases [where x="i"])
  apply (rule_tac [!] witness_acyclic_events.cases [where x="j"])
    by simp+
next
  have "wf (inv_image {(x,y). x < y} witness_acyclic_events)"
    by (simp add: wf_less)
  moreover have "{(x, y). example.happened_immediately_before x y} \<le>
    inv_image {(x,y). x < y} witness_acyclic_events" 
    using well_order_consistent by auto
  ultimately have "wfP example.happened_immediately_before" 
    using well_order_consistent wfP_def wf_subset by blast
  thus "acyclicP example.happened_immediately_before"
    using wfP_acyclicP by blast
next
  fix m s i j i'
  have "example.event_at (i, j) (Receive s m) \<Longrightarrow>
       i' \<in> deps m \<Longrightarrow>
      example.event_at (i, witness_deps_received_at (i, j) i') (Receive (I (witness_deps_received_is (i, j) i')) (Insert (witness_deps_received_is (i, j) i'))) \<and> witness_deps_received_at (i, j) i' < j \<and> I (witness_deps_received_is (i, j) i') = i'"
    apply (rule_tac [!] witness_acyclic_events.cases [where x="(i,j)"])
    by simp+
  thus "example.event_at (i, j) (Receive s m) \<Longrightarrow>
       i' \<in> deps m \<Longrightarrow>
       \<exists>s' j' m'.
          example.event_at (i, j') (Receive s' (Insert m')) \<and> j' < j \<and> I m' = i'"
    by blast
next
  fix m i
  have "example.event_at i (Send m) \<Longrightarrow>
        Inr m = example.state i \<bind> (\<lambda>s. create_insert s (witness_create_position i) (witness_create_letter i) i)"
    apply (rule_tac [!] witness_acyclic_events.cases [where x="i"])
    by (simp add:ext_ids_def)+
  thus "example.event_at i (Send m) \<Longrightarrow>
           (\<exists>n \<sigma>. return m = example.state i \<bind> (\<lambda>s. create_insert s n \<sigma> i)) \<or>
           (\<exists>n. return m = example.state i \<bind> (\<lambda>s. create_delete s n))"
    by blast
qed

text \<open>As expected all peers reach the same final state.\<close>

lemma
  "example.state (PeerA, 4) = Inr [
    InsertMessage \<turnstile> (PeerA, 0) \<stileturn> (Some CHR ''B''),
    InsertMessage \<turnstile> (PeerB, 0) \<stileturn> (Some CHR ''A''),
    InsertMessage \<lbrakk>(PeerA, 0)\<rbrakk>  (PeerC, 1) \<stileturn> (Some CHR ''R'')]"
  "example.state (PeerA, 4) = example.state (PeerB, 4)"
  "example.state (PeerB, 4) = example.state (PeerC, 4)"
  by (simp del:substr_simp add:ext_ids_def substr.simps less_example_peers_def)+

text \<open>We can also derive the equivalence of states using the strong
  convergence theorem. For example the set of received messages in
  the third state of peer A and B is equivalent, even though they were
  not received in the same order:\<close>

lemma
  "example.state (PeerA, 3) = example.state (PeerB, 3)"
proof -
  have "example.is_valid_state_id (PeerA, 3)" by auto
  moreover have "example.is_valid_state_id (PeerB, 3)" by auto
  moreover have
    "set (example.received_messages (PeerA, 3)) = 
     set (example.received_messages (PeerB, 3))"
    by auto
  ultimately show ?thesis
    by (rule example.strong_convergence)
qed

text \<open>Similarly we can conclude that reached states are successful.\<close>
lemma
  "isOK (example.state (PeerC, 4))"
proof -
  have "example.is_valid_state_id (PeerC, 4)" by auto
  thus ?thesis by (rule example.no_failure)
qed

end