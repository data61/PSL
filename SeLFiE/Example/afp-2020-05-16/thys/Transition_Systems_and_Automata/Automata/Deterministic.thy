section \<open>Deterministic Automata\<close>

theory Deterministic
imports
  "../Transition_Systems/Transition_System"
  "../Transition_Systems/Transition_System_Extra"
  "../Transition_Systems/Transition_System_Construction"
  "../Basic/Degeneralization"
begin

  locale automaton =
    fixes automaton :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    fixes alphabet initial transition condition
    assumes automaton[simp]: "automaton (alphabet A) (initial A) (transition A) (condition A) = A"
    assumes alphabet[simp]: "alphabet (automaton a i t c) = a"
    assumes initial[simp]: "initial (automaton a i t c) = i"
    assumes transition[simp]: "transition (automaton a i t c) = t"
    assumes condition[simp]: "condition (automaton a i t c) = c"
  begin

    (* TODO: is there a way to use defines without renaming the constants? *)
    sublocale transition_system_initial
      "transition A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A"
      for A
      defines path' = path and run' = run and reachable' = reachable and nodes' = nodes
      by this

    lemma path_alt_def: "path A w p \<longleftrightarrow> w \<in> lists (alphabet A)"
    proof
      show "w \<in> lists (alphabet A)" if "path A w p" using that by (induct arbitrary: p) (auto)
      show "path A w p" if "w \<in> lists (alphabet A)" using that by (induct arbitrary: p) (auto)
    qed
    lemma run_alt_def: "run A w p \<longleftrightarrow> w \<in> streams (alphabet A)"
    proof
      show "w \<in> streams (alphabet A)" if "run A w p"
        using that by (coinduction arbitrary: w p) (force elim: run.cases)
      show "run A w p" if "w \<in> streams (alphabet A)"
        using that by (coinduction arbitrary: w p) (force elim: streams.cases)
    qed

  end

  locale automaton_path =
    automaton automaton alphabet initial transition condition
    for automaton :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    and alphabet initial transition condition
    +
    fixes test :: "'condition \<Rightarrow> 'label list \<Rightarrow> 'state list \<Rightarrow> 'state \<Rightarrow> bool"
  begin

    definition language :: "'automaton \<Rightarrow> 'label list set" where
      "language A \<equiv> {w. path A w (initial A) \<and> test (condition A) w (states A w (initial A)) (initial A)}"

    lemma language[intro]:
      assumes "path A w (initial A)" "test (condition A) w (states A w (initial A)) (initial A)"
      shows "w \<in> language A"
      using assms unfolding language_def by auto
    lemma language_elim[elim]:
      assumes "w \<in> language A"
      obtains "path A w (initial A)" "test (condition A) w (states A w (initial A)) (initial A)"
      using assms unfolding language_def by auto

    lemma language_alphabet: "language A \<subseteq> lists (alphabet A)" using path_alt_def by auto

  end

  locale automaton_run =
    automaton automaton alphabet initial transition condition
    for automaton :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    and alphabet initial transition condition
    +
    fixes test :: "'condition \<Rightarrow> 'label stream \<Rightarrow> 'state stream \<Rightarrow> 'state \<Rightarrow> bool"
  begin

    definition language :: "'automaton \<Rightarrow> 'label stream set" where
      "language A \<equiv> {w. run A w (initial A) \<and> test (condition A) w (trace A w (initial A)) (initial A)}"

    lemma language[intro]:
      assumes "run A w (initial A)" "test (condition A) w (trace A w (initial A)) (initial A)"
      shows "w \<in> language A"
      using assms unfolding language_def by auto
    lemma language_elim[elim]:
      assumes "w \<in> language A"
      obtains "run A w (initial A)" "test (condition A) w (trace A w (initial A)) (initial A)"
      using assms unfolding language_def by auto

    lemma language_alphabet: "language A \<subseteq> streams (alphabet A)" using run_alt_def by auto

  end

  locale automaton_degeneralization =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> 'item pred gen \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state degen \<Rightarrow> ('label \<Rightarrow> 'state degen \<Rightarrow> 'state degen) \<Rightarrow> 'item_degen pred \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    +
    fixes item :: "'state \<times> 'label \<times> 'state \<Rightarrow> 'item"
    fixes translate :: "'item_degen \<Rightarrow> 'item degen"
  begin

    definition degeneralize :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2" where
      "degeneralize A \<equiv> automaton\<^sub>2
        (alphabet\<^sub>1 A)
        (initial\<^sub>1 A, 0)
        (\<lambda> a (p, k). (transition\<^sub>1 A a p, count (condition\<^sub>1 A) (item (p, a, transition\<^sub>1 A a p)) k))
        (degen (condition\<^sub>1 A) \<circ> translate)"

    lemma degeneralize_simps[simp]:
      "alphabet\<^sub>2 (degeneralize A) = alphabet\<^sub>1 A"
      "initial\<^sub>2 (degeneralize A) = (initial\<^sub>1 A, 0)"
      "transition\<^sub>2 (degeneralize A) a (p, k) =
        (transition\<^sub>1 A a p, count (condition\<^sub>1 A) (item (p, a, transition\<^sub>1 A a p)) k)"
      "condition\<^sub>2 (degeneralize A) = degen (condition\<^sub>1 A) \<circ> translate"
      unfolding degeneralize_def by auto

    lemma degeneralize_target[simp]: "b.target (degeneralize A) w (p, k) =
      (a.target A w p, fold (count (condition\<^sub>1 A) \<circ> item) (p # a.states A w p || w || a.states A w p) k)"
      by (induct w arbitrary: p k) (auto)
    lemma degeneralize_states[simp]: "b.states (degeneralize A) w (p, k) =
      a.states A w p || scan (count (condition\<^sub>1 A) \<circ> item) (p # a.states A w p || w || a.states A w p) k"
      by (induct w arbitrary: p k) (auto)
    lemma degeneralize_trace[simp]: "b.trace (degeneralize A) w (p, k) =
      a.trace A w p ||| sscan (count (condition\<^sub>1 A) \<circ> item) (p ## a.trace A w p ||| w ||| a.trace A w p) k"
      by (coinduction arbitrary: w p k) (auto, metis sscan.code)

    lemma degeneralize_path[iff]: "b.path (degeneralize A) w (p, k) \<longleftrightarrow> a.path A w p"
      unfolding a.path_alt_def b.path_alt_def by simp
    lemma degeneralize_run[iff]: "b.run (degeneralize A) w (p, k) \<longleftrightarrow> a.run A w p"
      unfolding a.run_alt_def b.run_alt_def by simp

    lemma degeneralize_reachable_fst[simp]: "fst ` b.reachable (degeneralize A) (p, k) = a.reachable A p"
      unfolding a.reachable_alt_def b.reachable_alt_def image_def by simp
    lemma degeneralize_reachable_snd_empty[simp]:
      assumes "condition\<^sub>1 A = []"
      shows "snd ` b.reachable (degeneralize A) (p, k) = {k}"
    proof -
      have "snd ql = k" if "ql \<in> b.reachable (degeneralize A) (p, k)" for ql
        using that assms by induct auto
      then show ?thesis by auto
    qed
    lemma degeneralize_reachable_empty[simp]:
      assumes "condition\<^sub>1 A = []"
      shows "b.reachable (degeneralize A) (p, k) = a.reachable A p \<times> {k}"
      using degeneralize_reachable_fst degeneralize_reachable_snd_empty assms
      by (metis prod_singleton(2))
    lemma degeneralize_reachable_snd:
      "snd ` b.reachable (degeneralize A) (p, k) \<subseteq> insert k {0 ..< length (condition\<^sub>1 A)}"
      by (cases "condition\<^sub>1 A = []") (auto)
    lemma degeneralize_reachable:
      "b.reachable (degeneralize A) (p, k) \<subseteq> a.reachable A p \<times> insert k {0 ..< length (condition\<^sub>1 A)}"
      by (cases "condition\<^sub>1 A = []") (auto 0 3)

    lemma degeneralize_nodes_fst[simp]: "fst ` b.nodes (degeneralize A) = a.nodes A"
      unfolding a.nodes_alt_def b.nodes_alt_def by simp
    lemma degeneralize_nodes_snd_empty:
      assumes "condition\<^sub>1 A = []"
      shows "snd ` b.nodes (degeneralize A) = {0}"
      using assms unfolding b.nodes_alt_def by auto
    lemma degeneralize_nodes_empty:
      assumes "condition\<^sub>1 A = []"
      shows "b.nodes (degeneralize A) = a.nodes A \<times> {0}"
      using assms unfolding b.nodes_alt_def by auto
    lemma degeneralize_nodes_snd:
      "snd ` b.nodes (degeneralize A) \<subseteq> insert 0 {0 ..< length (condition\<^sub>1 A)}"
      using degeneralize_reachable_snd unfolding b.nodes_alt_def by auto
    lemma degeneralize_nodes:
      "b.nodes (degeneralize A) \<subseteq> a.nodes A \<times> insert 0 {0 ..< length (condition\<^sub>1 A)}"
      using degeneralize_reachable unfolding a.nodes_alt_def b.nodes_alt_def by simp
  
    lemma degeneralize_nodes_finite[iff]: "finite (b.nodes (degeneralize A)) \<longleftrightarrow> finite (a.nodes A)"
    proof
      show "finite (a.nodes A)" if "finite (b.nodes (degeneralize A))"
        using that by (auto simp flip: degeneralize_nodes_fst)
      show "finite (b.nodes (degeneralize A))" if "finite (a.nodes A)"
        using finite_subset degeneralize_nodes that by blast
    qed
    lemma degeneralize_nodes_card: "card (b.nodes (degeneralize A)) \<le>
      max 1 (length (condition\<^sub>1 A)) * card (a.nodes A)"
    proof (cases "finite (a.nodes A)")
      case True
      have "card (b.nodes (degeneralize A)) \<le> card (a.nodes A \<times> insert 0 {0 ..< length (condition\<^sub>1 A)})"
        using degeneralize_nodes True by (blast intro: card_mono)
      also have "\<dots> = card (insert 0 {0 ..< length (condition\<^sub>1 A)}) * card (a.nodes A)"
        unfolding card_cartesian_product by simp
      also have "card (insert 0 {0 ..< length (condition\<^sub>1 A)}) = max 1 (length (condition\<^sub>1 A))"
        by (simp add: card_insert_if Suc_leI max_absorb2)
      finally show ?thesis by this
    next
      case False
      then have "card (a.nodes A) = 0" "card (b.nodes (degeneralize A)) = 0" by auto
      then show ?thesis by simp
    qed

  end

  locale automaton_degeneralization_run =
    automaton_degeneralization
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      item translate +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and item translate
    +
    assumes test[iff]: "test\<^sub>2 (degen cs \<circ> translate) w
      (r ||| sscan (count cs \<circ> item) (p ## r ||| w ||| r) k) (p, k) \<longleftrightarrow> test\<^sub>1 cs w r p"
  begin

    lemma degeneralize_language[simp]: "b.language (degeneralize A) = a.language A" by force

  end

  locale automaton_product =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    c: automaton automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>1 \<Rightarrow> 'state\<^sub>1) \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>2 \<Rightarrow> 'state\<^sub>2) \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    and automaton\<^sub>3 :: "'label set \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2 \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2 \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2) \<Rightarrow> 'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    +
    fixes condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
  begin

    definition product :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2 \<Rightarrow> 'automaton\<^sub>3" where
      "product A B \<equiv> automaton\<^sub>3
        (alphabet\<^sub>1 A \<inter> alphabet\<^sub>2 B)
        (initial\<^sub>1 A, initial\<^sub>2 B)
        (\<lambda> a (p, q). (transition\<^sub>1 A a p, transition\<^sub>2 B a q))
        (condition (condition\<^sub>1 A) (condition\<^sub>2 B))"

    lemma product_simps[simp]:
      "alphabet\<^sub>3 (product A B) = alphabet\<^sub>1 A \<inter> alphabet\<^sub>2 B"
      "initial\<^sub>3 (product A B) = (initial\<^sub>1 A, initial\<^sub>2 B)"
      "transition\<^sub>3 (product A B) a (p, q) = (transition\<^sub>1 A a p, transition\<^sub>2 B a q)"
      "condition\<^sub>3 (product A B) = condition (condition\<^sub>1 A) (condition\<^sub>2 B)"
      unfolding product_def by auto

    lemma product_target[simp]: "c.target (product A B) w (p, q) = (a.target A w p, b.target B w q)"
      by (induct w arbitrary: p q) (auto)
    lemma product_states[simp]: "c.states (product A B) w (p, q) = a.states A w p || b.states B w q"
      by (induct w arbitrary: p q) (auto)
    lemma product_trace[simp]: "c.trace (product A B) w (p, q) = a.trace A w p ||| b.trace B w q"
      by (coinduction arbitrary: w p q) (auto)

    lemma product_path[iff]: "c.path (product A B) w (p, q) \<longleftrightarrow> a.path A w p \<and> b.path B w q"
      unfolding a.path_alt_def b.path_alt_def c.path_alt_def by simp
    lemma product_run[iff]: "c.run (product A B) w (p, q) \<longleftrightarrow> a.run A w p \<and> b.run B w q"
      unfolding a.run_alt_def b.run_alt_def c.run_alt_def by simp

    lemma product_reachable[simp]: "c.reachable (product A B) (p, q) \<subseteq> a.reachable A p \<times> b.reachable B q"
      unfolding c.reachable_alt_def by auto
    lemma product_nodes[simp]: "c.nodes (product A B) \<subseteq> a.nodes A \<times> b.nodes B"
      unfolding a.nodes_alt_def b.nodes_alt_def c.nodes_alt_def by auto
    lemma product_reachable_fst[simp]:
      assumes "alphabet\<^sub>1 A \<subseteq> alphabet\<^sub>2 B"
      shows "fst ` c.reachable (product A B) (p, q) = a.reachable A p"
      using assms
      unfolding a.reachable_alt_def a.path_alt_def
      unfolding b.reachable_alt_def b.path_alt_def
      unfolding c.reachable_alt_def c.path_alt_def
      by auto force
    lemma product_reachable_snd[simp]:
      assumes "alphabet\<^sub>1 A \<supseteq> alphabet\<^sub>2 B"
      shows "snd ` c.reachable (product A B) (p, q) = b.reachable B q"
      using assms
      unfolding a.reachable_alt_def a.path_alt_def
      unfolding b.reachable_alt_def b.path_alt_def
      unfolding c.reachable_alt_def c.path_alt_def
      by auto force
    lemma product_nodes_fst[simp]:
      assumes "alphabet\<^sub>1 A \<subseteq> alphabet\<^sub>2 B"
      shows "fst ` c.nodes (product A B) = a.nodes A"
      using assms product_reachable_fst
      unfolding a.nodes_alt_def b.nodes_alt_def c.nodes_alt_def
      by fastforce
    lemma product_nodes_snd[simp]:
      assumes "alphabet\<^sub>1 A \<supseteq> alphabet\<^sub>2 B"
      shows "snd ` c.nodes (product A B) = b.nodes B"
      using assms product_reachable_snd
      unfolding a.nodes_alt_def b.nodes_alt_def c.nodes_alt_def
      by fastforce

    lemma product_nodes_finite[intro]:
      assumes "finite (a.nodes A)" "finite (b.nodes B)"
      shows "finite (c.nodes (product A B))"
    proof (rule finite_subset)
      show "c.nodes (product A B) \<subseteq> a.nodes A \<times> b.nodes B" using product_nodes by this
      show "finite (a.nodes A \<times> b.nodes B)" using assms by simp
    qed
    lemma product_nodes_finite_strong[iff]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "finite (c.nodes (product A B)) \<longleftrightarrow> finite (a.nodes A) \<and> finite (b.nodes B)"
    proof safe
      show "finite (a.nodes A)" if "finite (c.nodes (product A B))"
        using product_nodes_fst assms that by (metis finite_imageI equalityD1)
      show "finite (b.nodes B)" if "finite (c.nodes (product A B))"
        using product_nodes_snd assms that by (metis finite_imageI equalityD2)
      show "finite (c.nodes (product A B))" if "finite (a.nodes A)" "finite (b.nodes B)"
        using that by rule
    qed
    lemma product_nodes_card[intro]:
      assumes "finite (a.nodes A)" "finite (b.nodes B)"
      shows "card (c.nodes (product A B)) \<le> card (a.nodes A) * card (b.nodes B)"
    proof -
      have "card (c.nodes (product A B)) \<le> card (a.nodes A \<times> b.nodes B)"
      proof (rule card_mono)
        show "finite (a.nodes A \<times> b.nodes B)" using assms by simp
        show "c.nodes (product A B) \<subseteq> a.nodes A \<times> b.nodes B" using product_nodes by this
      qed
      also have "\<dots> = card (a.nodes A) * card (b.nodes B)" using card_cartesian_product by this
      finally show ?thesis by this
    qed
    lemma product_nodes_card_strong[intro]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "card (c.nodes (product A B)) \<le> card (a.nodes A) * card (b.nodes B)"
    proof (cases "finite (a.nodes A) \<and> finite (b.nodes B)")
      case True
      show ?thesis using True by auto
    next
      case False
      have 1: "card (c.nodes (product A B)) = 0" using False assms by simp
      have 2: "card (a.nodes A) * card (b.nodes B) = 0" using False by auto
      show ?thesis using 1 2 by simp
    qed

  end

  locale automaton_intersection_path =
    automaton_product
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
      condition +
    a: automaton_path automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_path automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_path automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    and condition
    +
    assumes test[iff]: "length r = length s \<Longrightarrow>
      test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (r || s) (p, q) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w r p \<and> test\<^sub>2 c\<^sub>2 w s q"
  begin

    lemma product_language[simp]: "c.language (product A B) = a.language A \<inter> b.language B" by force

  end

  locale automaton_union_path =
    automaton_product
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
      condition +
    a: automaton_path automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_path automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_path automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    and condition
    +
    assumes test[iff]: "length r = length s \<Longrightarrow>
      test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (r || s) (p, q) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w r p \<or> test\<^sub>2 c\<^sub>2 w s q"
  begin

    lemma product_language[simp]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.language (product A B) = a.language A \<union> b.language B"
      using assms by (force simp: a.path_alt_def b.path_alt_def)

  end

  locale automaton_intersection_run =
    automaton_product
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
      condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_run automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    and condition
    +
    assumes test[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (r ||| s) (p, q) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w r p \<and> test\<^sub>2 c\<^sub>2 w s q"
  begin

    lemma product_language[simp]: "c.language (product A B) = a.language A \<inter> b.language B" by force

  end

  locale automaton_union_run =
    automaton_product
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
      condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2 +
    c: automaton_run automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3 test\<^sub>3
    and condition
    +
    assumes test[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (r ||| s) (p, q) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w r p \<or> test\<^sub>2 c\<^sub>2 w s q"
  begin

    lemma product_language[simp]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.language (product A B) = a.language A \<union> b.language B"
      using assms by (force simp: a.run_alt_def b.run_alt_def)

  end

  (* TODO: complete this in analogy to the pair case *)
  locale automaton_product_list =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state list \<Rightarrow> ('label \<Rightarrow> 'state list \<Rightarrow> 'state list) \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    +
    fixes condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
  begin

    definition product :: "'automaton\<^sub>1 list \<Rightarrow> 'automaton\<^sub>2" where
      "product AA \<equiv> automaton\<^sub>2
        (\<Inter> (alphabet\<^sub>1 ` set AA))
        (map initial\<^sub>1 AA)
        (\<lambda> a ps. map2 (\<lambda> A p. transition\<^sub>1 A a p) AA ps)
        (condition (map condition\<^sub>1 AA))"

    lemma product_simps[simp]:
      "alphabet\<^sub>2 (product AA) = \<Inter> (alphabet\<^sub>1 ` set AA)"
      "initial\<^sub>2 (product AA) = map initial\<^sub>1 AA"
      "transition\<^sub>2 (product AA) a ps = map2 (\<lambda> A p. transition\<^sub>1 A a p) AA ps"
      "condition\<^sub>2 (product AA) = condition (map condition\<^sub>1 AA)"
      unfolding product_def by auto

    (* TODO: get rid of indices, express this using stranspose and listset *)
    lemma product_trace_smap:
      assumes "length ps = length AA" "k < length AA"
      shows "smap (\<lambda> ps. ps ! k) (b.trace (product AA) w ps) = a.trace (AA ! k) w (ps ! k)"
      using assms by (coinduction arbitrary: w ps) (force)

    lemma product_nodes: "b.nodes (product AA) \<subseteq> listset (map a.nodes AA)"
    proof
      show "ps \<in> listset (map a.nodes AA)" if "ps \<in> b.nodes (product AA)" for ps
        using that by (induct) (auto simp: listset_member list_all2_conv_all_nth)
    qed

    lemma product_nodes_finite[intro]:
      assumes "list_all (finite \<circ> a.nodes) AA"
      shows "finite (b.nodes (product AA))"
      using list.pred_map product_nodes assms by (blast dest: finite_subset)
    lemma product_nodes_card:
      assumes "list_all (finite \<circ> a.nodes) AA"
      shows "card (b.nodes (product AA)) \<le> prod_list (map (card \<circ> a.nodes) AA)"
    proof -
      have "card (b.nodes (product AA)) \<le> card (listset (map a.nodes AA))"
        using list.pred_map product_nodes assms by (blast intro: card_mono)
      also have "\<dots> = prod_list (map (card \<circ> a.nodes) AA)" by simp
      finally show ?thesis by this
    qed

  end

  locale automaton_intersection_list_run =
    automaton_product_list
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and condition
    +
    assumes test[iff]: "test\<^sub>2 (condition cs) w rs ps \<longleftrightarrow>
      (\<forall> k < length cs. test\<^sub>1 (cs ! k) w (smap (\<lambda> ps. ps ! k) rs) (ps ! k))"
  begin

    lemma product_language[simp]: "b.language (product AA) = \<Inter> (a.language ` set AA)"
      unfolding a.language_def b.language_def
      unfolding a.run_alt_def b.run_alt_def streams_iff_sset
      by (fastforce simp: set_conv_nth product_trace_smap)

  end

  locale automaton_union_list_run =
    automaton_product_list
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and condition
    +
    assumes test[iff]: "test\<^sub>2 (condition cs) w rs ps \<longleftrightarrow>
      (\<exists> k < length cs. test\<^sub>1 (cs ! k) w (smap (\<lambda> ps. ps ! k) rs) (ps ! k))"
  begin

    lemma product_language[simp]:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      shows "b.language (product AA) = \<Union> (a.language ` set AA)"
      using assms
      unfolding a.language_def b.language_def
      unfolding a.run_alt_def b.run_alt_def streams_iff_sset
      by (fastforce simp: set_conv_nth product_trace_smap)

  end

  locale automaton_complement =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    +
    fixes condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2"
  begin

    definition complement :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2" where
      "complement A \<equiv> automaton\<^sub>2 (alphabet\<^sub>1 A) (initial\<^sub>1 A) (transition\<^sub>1 A) (condition (condition\<^sub>1 A))"

    lemma combine_simps[simp]:
      "alphabet\<^sub>2 (complement A) = alphabet\<^sub>1 A"
      "initial\<^sub>2 (complement A) = initial\<^sub>1 A"
      "transition\<^sub>2 (complement A) = transition\<^sub>1 A"
      "condition\<^sub>2 (complement A) = condition (condition\<^sub>1 A)"
      unfolding complement_def by auto

  end

  locale automaton_complement_path =
    automaton_complement
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      condition +
    a: automaton_path automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_path automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and condition
    +
    assumes test[iff]: "test\<^sub>2 (condition c) w r p \<longleftrightarrow> \<not> test\<^sub>1 c w r p"
  begin

    lemma complement_language[simp]: "b.language (complement A) = lists (alphabet\<^sub>1 A) - a.language A"
      unfolding a.language_def b.language_def a.path_alt_def b.path_alt_def by auto

  end

  locale automaton_complement_run =
    automaton_complement
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and condition
    +
    assumes test[iff]: "test\<^sub>2 (condition c) w r p \<longleftrightarrow> \<not> test\<^sub>1 c w r p"
  begin

    lemma complement_language[simp]: "b.language (complement A) = streams (alphabet\<^sub>1 A) - a.language A"
      unfolding a.language_def b.language_def a.run_alt_def b.run_alt_def by auto

  end

end