section \<open>Nondeterministic Automata\<close>

theory Nondeterministic
imports
  "../Transition_Systems/Transition_System"
  "../Transition_Systems/Transition_System_Extra"
  "../Transition_Systems/Transition_System_Construction"
  "../Basic/Degeneralization"
begin

  locale automaton =
    fixes automaton :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state set) \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    fixes alphabet initial transition condition
    assumes automaton[simp]: "automaton (alphabet A) (initial A) (transition A) (condition A) = A"
    assumes alphabet[simp]: "alphabet (automaton a i t c) = a"
    assumes initial[simp]: "initial (automaton a i t c) = i"
    assumes transition[simp]: "transition (automaton a i t c) = t"
    assumes condition[simp]: "condition (automaton a i t c) = c"
  begin

    sublocale transition_system_initial
      "\<lambda> a p. snd a" "\<lambda> a p. fst a \<in> alphabet A \<and> snd a \<in> transition A (fst a) p" "\<lambda> p. p \<in> initial A"
      for A
      defines path' = path and run' = run and reachable' = reachable and nodes' = nodes
      by this

    lemma states_alt_def: "states r p = map snd r" by (induct r arbitrary: p) (auto)
    lemma trace_alt_def: "trace r p = smap snd r" by (coinduction arbitrary: r p) (auto)

    lemma successors_alt_def: "successors A p = (\<Union> a \<in> alphabet A. transition A a p)" by auto

    lemma reachable_transition[intro]:
      assumes "a \<in> alphabet A" "q \<in> reachable A p" "r \<in> transition A a q"
      shows "r \<in> reachable A p"
      using reachable.execute assms by force
    lemma nodes_transition[intro]:
      assumes "a \<in> alphabet A" "p \<in> nodes A" "q \<in> transition A a p"
      shows "q \<in> nodes A"
      using nodes.execute assms by force

    lemma path_alphabet:
      assumes "length r = length w" "path A (w || r) p"
      shows "w \<in> lists (alphabet A)"
      using assms by (induct arbitrary: p rule: list_induct2) (auto)
    lemma run_alphabet:
      assumes "run A (w ||| r) p"
      shows "w \<in> streams (alphabet A)"
      using assms by (coinduction arbitrary: w r p) (metis run.cases stream.map szip_smap szip_smap_fst)

    definition restrict :: "'automaton \<Rightarrow> 'automaton" where
      "restrict A \<equiv> automaton
        (alphabet A)
        (initial A)
        (\<lambda> a p. if a \<in> alphabet A then transition A a p else {})
        (condition A)"

    lemma restrict_simps[simp]:
      "alphabet (restrict A) = alphabet A"
      "initial (restrict A) = initial A"
      "transition (restrict A) a p = (if a \<in> alphabet A then transition A a p else {})"
      "condition (restrict A) = condition A"
      unfolding restrict_def by auto

    lemma restrict_path[simp]: "path (restrict A) = path A"
    proof (intro ext iffI)
      show "path A wr p" if "path (restrict A) wr p" for wr p using that by induct auto
      show "path (restrict A) wr p" if "path A wr p" for wr p using that by induct auto
    qed
    lemma restrict_run[simp]: "run (restrict A) = run A"
    proof (intro ext iffI)
      show "run A wr p" if "run (restrict A) wr p" for wr p using that by coinduct auto
      show "run (restrict A) wr p" if "run A wr p" for wr p using that by coinduct auto
    qed

  end

  locale automaton_path =
    automaton automaton alphabet initial transition condition
    for automaton :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state set) \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    and alphabet initial transition condition
    +
    fixes test :: "'condition \<Rightarrow> 'label list \<Rightarrow> 'state list \<Rightarrow> 'state \<Rightarrow> bool"
  begin

    definition language :: "'automaton \<Rightarrow> 'label list set" where
      "language A \<equiv> {w |w r p. length r = length w \<and> p \<in> initial A \<and> path A (w || r) p \<and> test (condition A) w r p}"

    lemma language[intro]:
      assumes "length r = length w" "p \<in> initial A" "path A (w || r) p" "test (condition A) w r p"
      shows "w \<in> language A"
      using assms unfolding language_def by auto
    lemma language_elim[elim]:
      assumes "w \<in> language A"
      obtains r p
      where "length r = length w" "p \<in> initial A" "path A (w || r) p" "test (condition A) w r p"
      using assms unfolding language_def by auto

    lemma language_alphabet: "language A \<subseteq> lists (alphabet A)" by (auto dest: path_alphabet)

    lemma restrict_language[simp]: "language (restrict A) = language A" by force

  end

  locale automaton_run =
    automaton automaton alphabet initial transition condition
    for automaton :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state set) \<Rightarrow> 'condition \<Rightarrow> 'automaton"
    and alphabet initial transition condition
    +
    fixes test :: "'condition \<Rightarrow> 'label stream \<Rightarrow> 'state stream \<Rightarrow> 'state \<Rightarrow> bool"
  begin

    definition language :: "'automaton \<Rightarrow> 'label stream set" where
      "language A \<equiv> {w |w r p. p \<in> initial A \<and> run A (w ||| r) p \<and> test (condition A) w r p}"

    lemma language[intro]:
      assumes "p \<in> initial A" "run A (w ||| r) p" "test (condition A) w r p"
      shows "w \<in> language A"
      using assms unfolding language_def by auto
    lemma language_elim[elim]:
      assumes "w \<in> language A"
      obtains r p
      where "p \<in> initial A" "run A (w ||| r) p" "test (condition A) w r p"
      using assms unfolding language_def by auto

    lemma language_alphabet: "language A \<subseteq> streams (alphabet A)" by (auto dest: run_alphabet)

    lemma restrict_language[simp]: "language (restrict A) = language A" by force

  end

  locale automaton_degeneralization =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state set) \<Rightarrow> 'item pred gen \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state degen set \<Rightarrow> ('label \<Rightarrow> 'state degen \<Rightarrow> 'state degen set) \<Rightarrow> 'item_degen pred \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    +
    fixes item :: "'state \<times> 'label \<times> 'state \<Rightarrow> 'item"
    fixes translate :: "'item_degen \<Rightarrow> 'item degen"
  begin

    definition degeneralize :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2" where
      "degeneralize A \<equiv> automaton\<^sub>2
        (alphabet\<^sub>1 A)
        (initial\<^sub>1 A \<times> {0})
        (\<lambda> a (p, k). {(q, count (condition\<^sub>1 A) (item (p, a, q)) k) |q. q \<in> transition\<^sub>1 A a p})
        (degen (condition\<^sub>1 A) \<circ> translate)"

    lemma degeneralize_simps[simp]:
      "alphabet\<^sub>2 (degeneralize A) = alphabet\<^sub>1 A"
      "initial\<^sub>2 (degeneralize A) = initial\<^sub>1 A \<times> {0}"
      "transition\<^sub>2 (degeneralize A) a (p, k) =
        {(q, count (condition\<^sub>1 A) (item (p, a, q)) k) |q. q \<in> transition\<^sub>1 A a p}"
      "condition\<^sub>2 (degeneralize A) = degen (condition\<^sub>1 A) \<circ> translate"
      unfolding degeneralize_def by auto

    lemma run_degeneralize:
      assumes "a.run A (w ||| r) p"
      shows "b.run (degeneralize A) (w ||| r ||| sscan (count (condition\<^sub>1 A) \<circ> item) (p ## r ||| w ||| r) k) (p, k)"
      using assms by (coinduction arbitrary: w r p k) (force elim: a.run.cases)
    lemma degeneralize_run:
      assumes "b.run (degeneralize A) (w ||| rs) pk"
      obtains r s p k
      where "rs = r ||| s" "pk = (p, k)" "a.run A (w ||| r) p" "s = sscan (count (condition\<^sub>1 A) \<circ> item) (p ## r ||| w ||| r) k"
    proof -
      obtain r s p k where 1: "rs = r ||| s" "pk = (p, k)" using szip_smap surjective_pairing by metis
      show ?thesis
      proof
        show "rs = r ||| s" "pk = (p, k)" using 1 by this
        show "a.run A (w ||| r) p"
          using assms unfolding 1 by (coinduction arbitrary: w r s p k) (force elim: b.run.cases)
        show "s = sscan (count (condition\<^sub>1 A) \<circ> item) (p ## r ||| w ||| r) k"
          using assms unfolding 1 by (coinduction arbitrary: w r s p k) (erule b.run.cases, force)
      qed
    qed

    lemma degeneralize_nodes:
      "b.nodes (degeneralize A) \<subseteq> a.nodes A \<times> insert 0 {0 ..< length (condition\<^sub>1 A)}"
    proof
      fix pk
      assume "pk \<in> b.nodes (degeneralize A)"
      then show "pk \<in> a.nodes A \<times> insert 0 {0 ..< length (condition\<^sub>1 A)}"
        by (induct) (force, cases "condition\<^sub>1 A = []", auto)
    qed
    lemma nodes_degeneralize: "a.nodes A \<subseteq> fst ` b.nodes (degeneralize A)"
    proof
      fix p
      assume "p \<in> a.nodes A"
      then show "p \<in> fst ` b.nodes (degeneralize A)"
      proof induct
        case (initial p)
        have "(p, 0) \<in> b.nodes (degeneralize A)" using initial by auto
        then show ?case using image_iff fst_conv by force
      next
        case (execute p aq)
        obtain k where "(p, k) \<in> b.nodes (degeneralize A)" using execute(2) by auto
        then have "(snd aq, count (condition\<^sub>1 A) (item (p, aq)) k) \<in> b.nodes (degeneralize A)"
          using execute(3) by auto
        then show ?case using image_iff snd_conv by force
      qed
    qed

    lemma degeneralize_nodes_finite[iff]: "finite (b.nodes (degeneralize A)) \<longleftrightarrow> finite (a.nodes A)"
    proof
      show "finite (a.nodes A)" if "finite (b.nodes (degeneralize A))"
        using finite_subset nodes_degeneralize that by blast
      show "finite (b.nodes (degeneralize A))" if "finite (a.nodes A)"
        using finite_subset degeneralize_nodes that by blast
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

    lemma degeneralize_language[simp]: "b.language (degeneralize A) = a.language A"
      unfolding a.language_def b.language_def by (auto dest: run_degeneralize elim!: degeneralize_run)

  end

  locale automaton_product =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    c: automaton automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 set \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>1 \<Rightarrow> 'state\<^sub>1 set) \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 set \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>2 \<Rightarrow> 'state\<^sub>2 set) \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    and automaton\<^sub>3 :: "'label set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>1 \<times> 'state\<^sub>2 \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set) \<Rightarrow> 'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    +
    fixes condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
  begin

    definition product :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2 \<Rightarrow> 'automaton\<^sub>3" where
      "product A B \<equiv> automaton\<^sub>3
        (alphabet\<^sub>1 A \<inter> alphabet\<^sub>2 B)
        (initial\<^sub>1 A \<times> initial\<^sub>2 B)
        (\<lambda> a (p, q). transition\<^sub>1 A a p \<times> transition\<^sub>2 B a q)
        (condition (condition\<^sub>1 A) (condition\<^sub>2 B))"

    lemma product_simps[simp]:
      "alphabet\<^sub>3 (product A B) = alphabet\<^sub>1 A \<inter> alphabet\<^sub>2 B"
      "initial\<^sub>3 (product A B) = initial\<^sub>1 A \<times> initial\<^sub>2 B"
      "transition\<^sub>3 (product A B) a (p, q) = transition\<^sub>1 A a p \<times> transition\<^sub>2 B a q"
      "condition\<^sub>3 (product A B) = condition (condition\<^sub>1 A) (condition\<^sub>2 B)"
      unfolding product_def by auto

    lemma product_target[simp]:
      assumes "length w = length r" "length r = length s"
      shows "c.target (w || r || s) (p, q) = (a.target (w || r) p, b.target (w || s) q)"
      using assms by (induct arbitrary: p q rule: list_induct3) (auto)

    lemma product_path[iff]:
      assumes "length w = length r" "length r = length s"
      shows "c.path (product A B) (w || r || s) (p, q) \<longleftrightarrow>
        a.path A (w || r) p \<and> b.path B (w || s) q"
      using assms by (induct arbitrary: p q rule: list_induct3) (auto)
    lemma product_run[iff]: "c.run (product A B) (w ||| r ||| s) (p, q) \<longleftrightarrow>
      a.run A (w ||| r) p \<and> b.run B (w ||| s) q"
    proof safe
      show "a.run A (w ||| r) p" if "c.run (product A B) (w ||| r ||| s) (p, q)"
        using that by (coinduction arbitrary: w r s p q) (force elim: c.run.cases)
      show "b.run B (w ||| s) q" if "c.run (product A B) (w ||| r ||| s) (p, q)"
        using that by (coinduction arbitrary: w r s p q) (force elim: c.run.cases)
      show "c.run (product A B) (w ||| r ||| s) (p, q)" if "a.run A (w ||| r) p" "b.run B (w ||| s) q"
        using that by (coinduction arbitrary: w r s p q) (auto elim: a.run.cases b.run.cases)
    qed

    lemma product_nodes: "c.nodes (product A B) \<subseteq> a.nodes A \<times> b.nodes B"
    proof
      fix pq
      assume "pq \<in> c.nodes (product A B)"
      then show "pq \<in> a.nodes A \<times> b.nodes B" by induct auto
    qed

    lemma product_nodes_finite[intro]:
      assumes "finite (a.nodes A)" "finite (b.nodes B)"
      shows "finite (c.nodes (product A B))"
      using finite_subset product_nodes assms by blast

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
    assumes test[iff]: "length r = length w \<Longrightarrow> length s = length w \<Longrightarrow>
      test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (r || s) (p, q) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w r p \<and> test\<^sub>2 c\<^sub>2 w s q"
  begin

    lemma product_language[simp]: "c.language (product A B) = a.language A \<inter> b.language B"
      unfolding a.language_def b.language_def c.language_def by (force iff: split_zip)

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

    lemma product_language[simp]: "c.language (product A B) = a.language A \<inter> b.language B"
      unfolding a.language_def b.language_def c.language_def by (fastforce iff: split_szip)

  end

  locale automaton_sum =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 +
    c: automaton automaton\<^sub>3 alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state\<^sub>1 set \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>1 \<Rightarrow> 'state\<^sub>1 set) \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state\<^sub>2 set \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>2 \<Rightarrow> 'state\<^sub>2 set) \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    and automaton\<^sub>3 :: "'label set \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) set \<Rightarrow> ('label \<Rightarrow> 'state\<^sub>1 + 'state\<^sub>2 \<Rightarrow> ('state\<^sub>1 + 'state\<^sub>2) set) \<Rightarrow> 'condition\<^sub>3 \<Rightarrow> 'automaton\<^sub>3"
    and alphabet\<^sub>3 initial\<^sub>3 transition\<^sub>3 condition\<^sub>3
    +
    fixes condition :: "'condition\<^sub>1 \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'condition\<^sub>3"
  begin

    definition sum :: "'automaton\<^sub>1 \<Rightarrow> 'automaton\<^sub>2 \<Rightarrow> 'automaton\<^sub>3" where
      "sum A B \<equiv> automaton\<^sub>3
        (alphabet\<^sub>1 A \<union> alphabet\<^sub>2 B)
        (initial\<^sub>1 A <+> initial\<^sub>2 B)
        (\<lambda> a. \<lambda> Inl p \<Rightarrow> Inl ` transition\<^sub>1 A a p | Inr q \<Rightarrow> Inr ` transition\<^sub>2 B a q)
        (condition (condition\<^sub>1 A) (condition\<^sub>2 B))"

    lemma sum_simps[simp]:
      "alphabet\<^sub>3 (sum A B) = alphabet\<^sub>1 A \<union> alphabet\<^sub>2 B"
      "initial\<^sub>3 (sum A B) = initial\<^sub>1 A <+> initial\<^sub>2 B"
      "transition\<^sub>3 (sum A B) a (Inl p) = Inl ` transition\<^sub>1 A a p"
      "transition\<^sub>3 (sum A B) a (Inr q) = Inr ` transition\<^sub>2 B a q"
      "condition\<^sub>3 (sum A B) = condition (condition\<^sub>1 A) (condition\<^sub>2 B)"
      unfolding sum_def by auto

    lemma path_sum_a:
      assumes "length r = length w" "a.path A (w || r) p"
      shows "c.path (sum A B) (w || map Inl r) (Inl p)"
      using assms by (induct arbitrary: p rule: list_induct2) (auto)
    lemma path_sum_b:
      assumes "length s = length w" "b.path B (w || s) q"
      shows "c.path (sum A B) (w || map Inr s) (Inr q)"
      using assms by (induct arbitrary: q rule: list_induct2) (auto)
    lemma sum_path:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      assumes "length rs = length w" "c.path (sum A B) (w || rs) pq"
      obtains
        (a) r p where "rs = map Inl r" "pq = Inl p" "a.path A (w || r) p" |
        (b) s q where "rs = map Inr s" "pq = Inr q" "b.path B (w || s) q"
    proof (cases pq)
      case (Inl p)
      have 1: "rs = map Inl (map projl rs)"
        using assms(2, 3) unfolding Inl by (induct arbitrary: p rule: list_induct2) (auto)
      have 2: "a.path A (w || map projl rs) p"
        using assms(2, 1, 3) unfolding Inl by (induct arbitrary: p rule: list_induct2) (auto)
      show ?thesis using a 1 Inl 2 by this
    next
      case (Inr q)
      have 1: "rs = map Inr (map projr rs)"
        using assms(2, 3) unfolding Inr by (induct arbitrary: q rule: list_induct2) (auto)
      have 2: "b.path B (w || map projr rs) q"
        using assms(2, 1, 3) unfolding Inr by (induct arbitrary: q rule: list_induct2) (auto)
      show ?thesis using b 1 Inr 2 by this
    qed

    lemma run_sum_a:
      assumes "a.run A (w ||| r) p"
      shows "c.run (sum A B) (w ||| smap Inl r) (Inl p)"
      using assms by (coinduction arbitrary: w r p) (force elim: a.run.cases)
    lemma run_sum_b:
      assumes "b.run B (w ||| s) q"
      shows "c.run (sum A B) (w ||| smap Inr s) (Inr q)"
      using assms by (coinduction arbitrary: w s q) (force elim: b.run.cases)
    lemma sum_run:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      assumes "c.run (sum A B) (w ||| rs) pq"
      obtains
        (a) r p where "rs = smap Inl r" "pq = Inl p" "a.run A (w ||| r) p" |
        (b) s q where "rs = smap Inr s" "pq = Inr q" "b.run B (w ||| s) q"
    proof (cases pq)
      case (Inl p)
      have 1: "rs = smap Inl (smap projl rs)"
        using assms(2) unfolding Inl by (coinduction arbitrary: w rs p) (force elim: c.run.cases)
      have 2: "a.run A (w ||| smap projl rs) p"
        using assms unfolding Inl by (coinduction arbitrary: w rs p) (force elim: c.run.cases)
      show ?thesis using a 1 Inl 2 by this
    next
      case (Inr q)
      have 1: "rs = smap Inr (smap projr rs)"
        using assms(2) unfolding Inr by (coinduction arbitrary: w rs q) (force elim: c.run.cases)
      have 2: "b.run B (w ||| smap projr rs) q"
        using assms unfolding Inr by (coinduction arbitrary: w rs q) (force elim: c.run.cases)
      show ?thesis using b 1 Inr 2 by this
    qed

    lemma sum_nodes:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.nodes (sum A B) \<subseteq> a.nodes A <+> b.nodes B"
    proof
      fix pq
      assume "pq \<in> c.nodes (sum A B)"
      then show "pq \<in> a.nodes A <+> b.nodes B" using assms by (induct) (auto 0 3)
    qed

    lemma sum_nodes_finite[intro]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      assumes "finite (a.nodes A)" "finite (b.nodes B)"
      shows "finite (c.nodes (sum A B))"
      using finite_subset sum_nodes assms by (auto intro: finite_Plus)

  end

  locale automaton_union_path =
    automaton_sum
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
    assumes test\<^sub>1[iff]: "length r = length w \<Longrightarrow> test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (map Inl r) (Inl p) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w r p"
    assumes test\<^sub>2[iff]: "length s = length w \<Longrightarrow> test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (map Inr s) (Inr q) \<longleftrightarrow> test\<^sub>2 c\<^sub>2 w s q"
  begin

    lemma sum_language[simp]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.language (sum A B) = a.language A \<union> b.language B"
      using assms unfolding a.language_def b.language_def c.language_def
      by (force intro: path_sum_a path_sum_b elim!: sum_path)

  end

  locale automaton_union_run =
    automaton_sum
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
    assumes test\<^sub>1[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (smap Inl r) (Inl p) \<longleftrightarrow> test\<^sub>1 c\<^sub>1 w r p"
    assumes test\<^sub>2[iff]: "test\<^sub>3 (condition c\<^sub>1 c\<^sub>2) w (smap Inr s) (Inr q) \<longleftrightarrow> test\<^sub>2 c\<^sub>2 w s q"
  begin

    lemma sum_language[simp]:
      assumes "alphabet\<^sub>1 A = alphabet\<^sub>2 B"
      shows "c.language (sum A B) = a.language A \<union> b.language B"
      using assms unfolding a.language_def b.language_def c.language_def
      by (auto intro: run_sum_a run_sum_b elim!: sum_run)

  end

  locale automaton_product_list =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state set) \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> 'state list set \<Rightarrow> ('label \<Rightarrow> 'state list \<Rightarrow> 'state list set) \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    +
    fixes condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
  begin

    definition product :: "'automaton\<^sub>1 list \<Rightarrow> 'automaton\<^sub>2" where
      "product AA \<equiv> automaton\<^sub>2
        (\<Inter> (alphabet\<^sub>1 ` set AA))
        (listset (map initial\<^sub>1 AA))
        (\<lambda> a ps. listset (map2 (\<lambda> A p. transition\<^sub>1 A a p) AA ps))
        (condition (map condition\<^sub>1 AA))"

    lemma product_simps[simp]:
      "alphabet\<^sub>2 (product AA) = \<Inter> (alphabet\<^sub>1 ` set AA)"
      "initial\<^sub>2 (product AA) = listset (map initial\<^sub>1 AA)"
      "transition\<^sub>2 (product AA) a ps = listset (map2 (\<lambda> A p. transition\<^sub>1 A a p) AA ps)"
      "condition\<^sub>2 (product AA) = condition (map condition\<^sub>1 AA)"
      unfolding product_def by auto

    lemma product_run_length:
      assumes "length ps = length AA"
      assumes "b.run (product AA) (w ||| r) ps"
      assumes "qs \<in> sset r"
      shows "length qs = length AA"
    proof -
      have "pred_stream (\<lambda> qs. length qs = length AA) r"
        using assms(1, 2) by (coinduction arbitrary: w r ps)
          (force elim: b.run.cases simp: listset_member list_all2_conv_all_nth)
      then show ?thesis using assms(3) unfolding stream.pred_set by auto
    qed
    lemma product_run_stranspose:
      assumes "length ps = length AA"
      assumes "b.run (product AA) (w ||| r) ps"
      obtains rs where "r = stranspose rs" "length rs = length AA"
    proof
      define rs where "rs \<equiv> map (\<lambda> k. smap (\<lambda> ps. ps ! k) r) [0 ..< length AA]"
      have "length qs = length AA" if "qs \<in> sset r" for qs using product_run_length assms that by this
      then show "r = stranspose rs"
        unfolding rs_def by (coinduction arbitrary: r) (auto intro: nth_equalityI simp: comp_def)
      show "length rs = length AA" unfolding rs_def by auto
    qed

    lemma run_product:
      assumes "length rs = length AA" "length ps = length AA"
      assumes "\<And> k. k < length AA \<Longrightarrow> a.run (AA ! k) (w ||| rs ! k) (ps ! k)"
      shows "b.run (product AA) (w ||| stranspose rs) ps"
    using assms
    proof (coinduction arbitrary: w rs ps)
      case (run ap r)
      then show ?case
      proof (intro conjI exI)
        show "fst ap \<in> alphabet\<^sub>2 (product AA)"
          using run by (force elim: a.run.cases simp: set_conv_nth)
        show "snd ap \<in> transition\<^sub>2 (product AA) (fst ap) ps"
          using run by (force elim: a.run.cases simp: listset_member list_all2_conv_all_nth)
        show "\<forall> k < length AA. a.run' (AA ! k) (stl w ||| map stl rs ! k) (map shd rs ! k)"
          using run by (force elim: a.run.cases)
      qed auto
    qed
    lemma product_run:
      assumes "length rs = length AA" "length ps = length AA"
      assumes "b.run (product AA) (w ||| stranspose rs) ps"
      shows "k < length AA \<Longrightarrow> a.run (AA ! k) (w ||| rs ! k) (ps ! k)"
    using assms
    proof (coinduction arbitrary: w rs ps)
      case (run ap wr)
      then show ?case
      proof (intro exI conjI)
        show "fst ap \<in> alphabet\<^sub>1 (AA ! k)"
          using run by (force elim: b.run.cases)
        show "snd ap \<in> transition\<^sub>1 (AA ! k) (fst ap) (ps ! k)"
          using run by (force elim: b.run.cases simp: listset_member list_all2_conv_all_nth)
        show "b.run' (product AA) (stl w ||| stranspose (map stl rs)) (shd (stranspose rs))"
          using run by (force elim: b.run.cases)
      qed auto
    qed

    lemma product_nodes: "b.nodes (product AA) \<subseteq> listset (map a.nodes AA)"
    proof
      show "ps \<in> listset (map a.nodes AA)" if "ps \<in> b.nodes (product AA)" for ps
        using that by (induct) (auto 0 3 simp: listset_member list_all2_conv_all_nth)
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
    assumes test[iff]: "length rs = length cs \<Longrightarrow> length ps = length cs \<Longrightarrow>
      test\<^sub>2 (condition cs) w (stranspose rs) ps \<longleftrightarrow> list_all (\<lambda> (c, r, p). test\<^sub>1 c w r p) (cs || rs || ps)"
  begin

    lemma product_language[simp]: "b.language (product AA) = \<Inter> (a.language ` set AA)"
    proof safe
      fix A w
      assume 1: "w \<in> b.language (product AA)" "A \<in> set AA"
      obtain r ps where 2:
        "ps \<in> initial\<^sub>2 (product AA)"
        "b.run (product AA) (w ||| r) ps"
        "test\<^sub>2 (condition\<^sub>2 (product AA)) w r ps"
        using 1(1) by auto
      have 3: "length ps = length AA" using 2(1) by (simp add: listset_member list_all2_conv_all_nth)
      obtain rs where 4: "r = stranspose rs" "length rs = length AA"
        using product_run_stranspose 3 2(2) by this
      obtain k where 5: "k < length AA" "A = AA ! k" using 1(2) unfolding set_conv_nth by auto
      show "w \<in> a.language A"
      proof
        show "ps ! k \<in> initial\<^sub>1 A" using 2(1) 5 by (auto simp: listset_member list_all2_conv_all_nth)
        show "a.run A (w ||| rs ! k) (ps ! k)" using 2(2) 3 4 5 by (auto intro: product_run)
        show "test\<^sub>1 (condition\<^sub>1 A) w (rs ! k) (ps ! k)" using 2(3) 3 4 5 by (simp add: list_all_length)
      qed
    next
      fix w
      assume 1: "w \<in> \<Inter> (a.language ` set AA)"
      have 2: "\<forall> A \<in> set AA. \<exists> r p. p \<in> initial\<^sub>1 A \<and> a.run A (w ||| r) p \<and> test\<^sub>1 (condition\<^sub>1 A) w r p"
        using 1 by blast
      obtain rs ps where 3:
        "length rs = length AA" "length ps = length AA"
        "\<And> k. k < length AA \<Longrightarrow> ps ! k \<in> initial\<^sub>1 (AA ! k)"
        "\<And> k. k < length AA \<Longrightarrow> a.run (AA ! k) (w ||| rs ! k) (ps ! k)"
        "\<And> k. k < length AA \<Longrightarrow> test\<^sub>1 (condition\<^sub>1 (AA ! k)) w (rs ! k) (ps ! k)"
        using 2
        unfolding Ball_set list_choice_zip list_choice_pair
        unfolding list.pred_set set_conv_nth
        by force
      show "w \<in> b.language (product AA)"
      proof
        show "ps \<in> initial\<^sub>2 (product AA)" using 3 by (auto simp: listset_member list_all2_conv_all_nth)
        show "b.run (product AA) (w ||| stranspose rs) ps" using 3 by (auto intro: run_product)
        show "test\<^sub>2 (condition\<^sub>2 (product AA)) w (stranspose rs) ps" using 3 by (auto simp: list_all_length)
      qed
    qed

  end

  locale automaton_sum_list =
    a: automaton automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 +
    b: automaton automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    for automaton\<^sub>1 :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('label \<Rightarrow> 'state \<Rightarrow> 'state set) \<Rightarrow> 'condition\<^sub>1 \<Rightarrow> 'automaton\<^sub>1"
    and alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
    and automaton\<^sub>2 :: "'label set \<Rightarrow> (nat \<times> 'state) set \<Rightarrow> ('label \<Rightarrow> nat \<times> 'state \<Rightarrow> (nat \<times> 'state) set) \<Rightarrow> 'condition\<^sub>2 \<Rightarrow> 'automaton\<^sub>2"
    and alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
    +
    fixes condition :: "'condition\<^sub>1 list \<Rightarrow> 'condition\<^sub>2"
  begin

    definition sum :: "'automaton\<^sub>1 list \<Rightarrow> 'automaton\<^sub>2" where
      "sum AA \<equiv> automaton\<^sub>2
        (\<Union> (alphabet\<^sub>1 ` set AA))
        (\<Union> k < length AA. {k} \<times> initial\<^sub>1 (AA ! k))
        (\<lambda> a (k, p). {k} \<times> transition\<^sub>1 (AA ! k) a p)
        (condition (map condition\<^sub>1 AA))"

    lemma sum_simps[simp]:
      "alphabet\<^sub>2 (sum AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      "initial\<^sub>2 (sum AA) = (\<Union> k < length AA. {k} \<times> initial\<^sub>1 (AA ! k))"
      "transition\<^sub>2 (sum AA) a (k, p) = {k} \<times> transition\<^sub>1 (AA ! k) a p"
      "condition\<^sub>2 (sum AA) = condition (map condition\<^sub>1 AA)"
      unfolding sum_def by auto

    lemma run_sum:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      assumes "A \<in> set AA"
      assumes "a.run A (w ||| s) p"
      obtains k where "k < length AA" "A = AA ! k" "b.run (sum AA) (w ||| sconst k ||| s) (k, p)"
    proof -
      obtain k where 1: "k < length AA" "A = AA ! k" using assms(2) unfolding set_conv_nth by auto
      show ?thesis
      proof
        show "k < length AA" "A = AA ! k" using 1 by this
        show "b.run (sum AA) (w ||| sconst k ||| s) (k, p)"
          using assms 1(2) by (coinduction arbitrary: w s p) (force elim: a.run.cases)
      qed
    qed
    lemma sum_run:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      assumes "k < length AA"
      assumes "b.run (sum AA) (w ||| r) (k, p)"
      obtains s where "r = sconst k ||| s" "a.run (AA ! k) (w ||| s) p"
    proof
      show "r = sconst k ||| smap snd r"
        using assms by (coinduction arbitrary: w r p) (force elim: b.run.cases)
      show "a.run (AA ! k) (w ||| smap snd r) p"
        using assms by (coinduction arbitrary: w r p) (force elim: b.run.cases)
    qed

    lemma sum_nodes:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      shows "b.nodes (sum AA) \<subseteq> (\<Union> k < length AA. {k} \<times> a.nodes (AA ! k))"
    proof
      show "kp \<in> (\<Union> k < length AA. {k} \<times> a.nodes (AA ! k))" if "kp \<in> b.nodes (sum AA)" for kp
        using that assms by (induct) (auto 0 4)
    qed

    lemma sum_nodes_finite[intro]:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      assumes "list_all (finite \<circ> a.nodes) AA"
      shows "finite (b.nodes (sum AA))"
    proof (rule finite_subset)
      show "b.nodes (sum AA) \<subseteq> (\<Union> k < length AA. {k} \<times> a.nodes (AA ! k))"
        using sum_nodes assms(1) by this
      show "finite (\<Union> k < length AA. {k} \<times> a.nodes' (AA ! k))"
        using assms(2) unfolding list_all_length by auto
    qed

  end

  locale automaton_union_list_run =
    automaton_sum_list
      automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1
      automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2
      condition +
    a: automaton_run automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1 +
    b: automaton_run automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    for automaton\<^sub>1 alphabet\<^sub>1 initial\<^sub>1 transition\<^sub>1 condition\<^sub>1 test\<^sub>1
    and automaton\<^sub>2 alphabet\<^sub>2 initial\<^sub>2 transition\<^sub>2 condition\<^sub>2 test\<^sub>2
    and condition
    +
    assumes test[iff]: "k < length cs \<Longrightarrow> test\<^sub>2 (condition cs) w (sconst k ||| r) (k, p) \<longleftrightarrow> test\<^sub>1 (cs ! k) w r p"
  begin

    lemma sum_language[simp]:
      assumes "\<Inter> (alphabet\<^sub>1 ` set AA) = \<Union> (alphabet\<^sub>1 ` set AA)"
      shows "b.language (sum AA) = \<Union> (a.language ` set AA)"
    proof
      show "b.language (sum AA) \<subseteq> \<Union> (a.language ` set AA)"
        using assms unfolding a.language_def b.language_def by (force elim: sum_run)
      show "\<Union> (a.language ` set AA) \<subseteq> b.language (sum AA)"
        using assms unfolding a.language_def b.language_def by (force elim!: run_sum)
    qed

  end

end