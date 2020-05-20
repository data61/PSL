(*  Title:       Tree Automata
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section "Tree Automata"
theory Ta
imports Main Automatic_Refinement.Misc Tree
begin
text_raw \<open>\label{sec:ta}\<close>


text \<open>
  This theory defines tree automata, tree regular languages and 
  specifies basic algorithms.

  Nondeterministic and deterministic (bottom-up) tree automata are defined.

  For non-deterministic tree automata, basic algorithms for membership, union,
  intersection, forward and backward reduction, and emptiness check are 
  specified.
  Moreover, a (brute-force) determinization algorithm is specified.
  
  For deterministic tree automata, we specify algorithms for complement 
  and completion. 

  Finally, the class of regular languages over a given ranked alphabet is defined
  and its standard closure properties are proved.

  The specification of the algorithms in this theory is very high-level, and the
  specifications are not executable. A bit more specific algorithms are defined 
  in Section~\ref{sec:absalgo}, and a refinement to executable definitions is 
  done in Section~\ref{sec:taimpl}.
\<close>

subsection "Basic Definitions"

subsubsection "Tree Automata"

text \<open>
  A tree automata consists of a (finite) set of initial states
  and a (finite) set of rules. 

  A rule has the form \<open>q \<rightarrow> l q1\<dots>qn\<close>, 
  with the meaning that one can derive 
  \<open>l(q1\<dots>qn)\<close> from the state \<open>q\<close>.
\<close>

(* Workaround for bug in Haskell-code generator: Type variables have to be 
  lower-case *)
(* datatype ('Q,'L) ta_rule = RULE 'Q 'L "'Q list" ("_ \<rightarrow> _ _") *)
datatype ('q,'l) ta_rule = RULE 'q 'l "'q list" ("_ \<rightarrow> _ _")

record ('Q,'L) tree_automaton_rec =
  ta_initial :: "'Q set"
  ta_rules :: "('Q,'L) ta_rule set"

  \<comment> \<open>Rule deconstruction\<close>
fun lhs where "lhs (q \<rightarrow> l qs) = q"
fun rhsq where "rhsq (q \<rightarrow> l qs) = qs"
fun rhsl where "rhsl (q \<rightarrow> l qs) = l"
  \<comment> \<open>States in a rule\<close>
fun rule_states where "rule_states (q \<rightarrow> l qs) = insert q (set qs)"
  \<comment> \<open>States in a set of rules\<close>
definition "\<delta>_states \<delta> == \<Union>(rule_states ` \<delta>)"
  \<comment> \<open>States in a tree automaton\<close>
definition "ta_rstates TA = ta_initial TA \<union> \<delta>_states (ta_rules TA)"
  \<comment> \<open>Symbols occurring in rules\<close>
definition "\<delta>_symbols \<delta> == rhsl`\<delta>"

  \<comment> \<open>Nondeterministic, finite tree automaton (NFTA)\<close>
locale tree_automaton = 
  fixes TA :: "('Q,'L) tree_automaton_rec"
  assumes finite_rules[simp, intro!]: "finite (ta_rules TA)"
  assumes finite_initial[simp, intro!]: "finite (ta_initial TA)"
begin
  abbreviation "Qi == ta_initial TA"
  abbreviation "\<delta> == ta_rules TA"
  abbreviation "Q == ta_rstates TA"
end

subsubsection "Acceptance"
text \<open>
  The predicate \<open>accs \<delta> t q\<close> is true, iff the tree \<open>t\<close> is accepted
  in state \<open>q\<close> w.r.t. the rules in \<open>\<delta>\<close>.
  
  A tree is accepted in state $q$, if it can be produced from $q$ using the 
  rules.
\<close>
inductive accs :: "('Q,'L) ta_rule set \<Rightarrow> 'L tree \<Rightarrow> 'Q \<Rightarrow> bool"
where
  "\<lbrakk>
     (q \<rightarrow> f qs) \<in> \<delta>; length ts = length qs; 
     !!i. i<length qs \<Longrightarrow> accs \<delta> (ts ! i) (qs ! i) 
   \<rbrakk> \<Longrightarrow> accs \<delta> (NODE f ts) q"


\<comment> \<open>Characterization of @{const accs} using @{const list_all_zip}\<close>
inductive accs_laz :: "('Q,'L) ta_rule set \<Rightarrow> 'L tree \<Rightarrow> 'Q \<Rightarrow> bool"
where
  "\<lbrakk>
     (q \<rightarrow> f qs) \<in> \<delta>; 
     list_all_zip (accs_laz \<delta>) ts qs
   \<rbrakk> \<Longrightarrow> accs_laz \<delta> (NODE f ts) q"

lemma accs_laz: "accs = accs_laz"
  apply (intro ext)
  apply (rule iffI)
  apply (erule accs.induct)
  apply (auto intro: accs_laz.intros[simplified list_all_zip_alt]) 
  apply (erule accs_laz.induct)
  apply (auto intro: accs.intros simp add: list_all_zip_alt)
  done


subsubsection "Language"
text \<open>
  The language of a tree automaton is the set of all trees that are accepted
  in an initial state.
\<close>
definition "ta_lang TA == { t . \<exists>q\<in>ta_initial TA. accs (ta_rules TA) t q }"

subsection "Basic Properties"

lemma rule_states_simp: 
  "rule_states x = (case x of (q \<rightarrow> l qs) \<Rightarrow> insert q (set qs))"
  by (case_tac x) auto

lemma rule_states_lhs[simp]: "lhs r \<in> rule_states r" 
  by (auto split: ta_rule.split simp add: rule_states_simp)

lemma rule_states_rhsq: "set (rhsq r) \<subseteq> rule_states r"
  by (auto split: ta_rule.split simp add: rule_states_simp)

lemma rule_states_finite[simp, intro!]: "finite (rule_states r)"
  by (simp add: rule_states_simp split: ta_rule.split)

lemma \<delta>_statesI: 
  assumes A: "(q \<rightarrow> l qs)\<in>\<delta>"
  shows "q\<in>\<delta>_states \<delta>"
        "set qs \<subseteq> \<delta>_states \<delta>"
  using A
  apply (unfold \<delta>_states_def)
  by (auto split: ta_rule.split simp add: rule_states_simp)

lemma \<delta>_statesI': "\<lbrakk>(q \<rightarrow> l qs)\<in>\<delta>; qi\<in>set qs\<rbrakk> \<Longrightarrow> qi\<in>\<delta>_states \<delta>"
  using \<delta>_statesI(2) by fast

lemma \<delta>_states_accsI: "accs \<delta> n q \<Longrightarrow> q\<in>\<delta>_states \<delta>"
  by (auto elim: accs.cases intro: \<delta>_statesI)

lemma \<delta>_states_union[simp]: "\<delta>_states (\<delta>\<union>\<delta>') = \<delta>_states \<delta> \<union> \<delta>_states \<delta>'"
  by (auto simp add: \<delta>_states_def)

lemma \<delta>_states_insert[simp]: 
  "\<delta>_states (insert r \<delta>) = (rule_states r \<union> \<delta>_states \<delta>)"
  by (unfold \<delta>_states_def) auto

lemma \<delta>_states_mono: "\<lbrakk>\<delta> \<subseteq> \<delta>'\<rbrakk> \<Longrightarrow> \<delta>_states \<delta> \<subseteq> \<delta>_states \<delta>'"
  by (unfold \<delta>_states_def) auto

lemma \<delta>_states_finite[simp, intro]: "finite \<delta> \<Longrightarrow> finite (\<delta>_states \<delta>)"
  by (unfold \<delta>_states_def) auto

lemma \<delta>_statesE: "\<lbrakk>q\<in>\<delta>_states \<Delta>;
    !!f qs. \<lbrakk> (q \<rightarrow> f qs)\<in>\<Delta> \<rbrakk> \<Longrightarrow> P;
    !!ql f qs. \<lbrakk> (ql \<rightarrow> f qs)\<in>\<Delta>; q\<in>set qs \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  apply (unfold \<delta>_states_def)
  apply (auto)
  apply (auto simp add: rule_states_simp split: ta_rule.split_asm)
  done

lemma \<delta>_symbolsI: "(q \<rightarrow> f qs)\<in>\<delta> \<Longrightarrow> f\<in>\<delta>_symbols \<delta>" 
  by (force simp add: \<delta>_symbols_def)

lemma \<delta>_symbolsE: 
  assumes A: "f\<in>\<delta>_symbols \<delta>"
  obtains q qs where "(q \<rightarrow> f qs) \<in> \<delta>"
  using A
  apply (simp add: \<delta>_symbols_def)
  apply (erule imageE)
  apply (case_tac x)
  apply simp
  done

lemma \<delta>_symbols_simps[simp]:
  "\<delta>_symbols {} = {}"
  "\<delta>_symbols (insert r \<delta>) = insert (rhsl r) (\<delta>_symbols \<delta>)"
  "\<delta>_symbols (\<delta>\<union>\<delta>') = \<delta>_symbols \<delta> \<union> \<delta>_symbols \<delta>'"
  by (auto simp add: \<delta>_symbols_def)

lemma \<delta>_symbols_finite[simp, intro!]:
  "finite \<delta> \<Longrightarrow> finite (\<delta>_symbols \<delta>)"
  by (auto simp add: \<delta>_symbols_def)

lemma accs_mono: "\<lbrakk>accs \<delta> n q; \<delta>\<subseteq>\<delta>'\<rbrakk> \<Longrightarrow> accs \<delta>' n q"
proof (induct rule: accs.induct[case_names step])
  case (step q l qs \<delta> n)
  hence R': "(q \<rightarrow> l qs) \<in> \<delta>'" by auto
  from accs.intros[OF R' step.hyps(2)] 
       step.hyps(4)[OF _ step.prems] 
  show ?case .
qed

context tree_automaton
begin
  lemma initial_subset: "ta_initial TA \<subseteq> ta_rstates TA" 
    by (unfold ta_rstates_def) auto
  lemma states_subset: "\<delta>_states (ta_rules TA) \<subseteq> ta_rstates TA" 
    by (unfold ta_rstates_def) auto
  
  lemma finite_states[simp, intro!]: "finite (ta_rstates TA)"
    by (auto simp add: ta_rstates_def \<delta>_states_def 
             intro: finite_rules finite_UN_I)

  lemma finite_symbols[simp, intro!]: "finite (\<delta>_symbols (ta_rules TA))"
    by simp

  lemmas is_subset = rev_subsetD[OF _ initial_subset] 
                     rev_subsetD[OF _ states_subset]
end

subsection "Other Classes of Tree Automata"

subsubsection "Automata over Ranked Alphabets"
  \<comment> \<open>All trees over ranked alphabet\<close>
inductive_set ranked_trees :: "('L \<rightharpoonup> nat) \<Rightarrow> 'L tree set"
  for A where
  "\<lbrakk> \<forall>t\<in>set ts. t\<in>ranked_trees A; A f = Some (length ts) \<rbrakk> 
    \<Longrightarrow> NODE f ts \<in> ranked_trees A"

locale finite_alphabet =
  fixes A :: "('L \<rightharpoonup> nat)"
  assumes A_finite[simp, intro!]: "finite (dom A)"
begin
  abbreviation "F == dom A"
end

context finite_alphabet
begin

  definition "legal_rules Q == { (q \<rightarrow> f qs) | q f qs.
    q \<in> Q
    \<and> qs \<in> lists Q
    \<and> A f = Some (length qs)}"

  lemma legal_rulesI: 
    "\<lbrakk> 
      r\<in>\<delta>; 
      rule_states r \<subseteq> Q; 
      A (rhsl r) = Some (length (rhsq r)) 
    \<rbrakk> \<Longrightarrow> r\<in>legal_rules Q"
    apply (unfold legal_rules_def)
    apply (cases r)
    apply (auto)
    done

  lemma legal_rules_finite[simp, intro!]:
    fixes Q::"'Q set"
    assumes [simp, intro!]: "finite Q"
    shows "finite (legal_rules Q)"
  proof -
    define possible_rules_f
      where "possible_rules_f = (\<lambda>(Q::'Q set) f. 
      (\<lambda>(q,qs). (q \<rightarrow> f qs)) ` (Q \<times> (lists Q \<inter> {qs. A f = Some (length qs)})))"
    
    have "legal_rules Q = \<Union>(possible_rules_f Q`F)"
      by (auto simp add: legal_rules_def possible_rules_f_def)
    moreover have "!!f. finite (possible_rules_f Q f)" 
      apply (unfold possible_rules_f_def)
      apply (rule finite_imageI)
      apply (rule finite_SigmaI)
      apply simp
      apply (case_tac "A f")
      apply simp
      apply (simp add: lists_of_len_fin)
      done
    ultimately show ?thesis by auto
  qed
end

  \<comment> \<open>Finite tree automata with ranked alphabet\<close>
locale ranked_tree_automaton = 
  tree_automaton TA +
  finite_alphabet A
  for TA :: "('Q,'L) tree_automaton_rec" 
  and A :: "'L \<rightharpoonup> nat" +
  assumes ranked: "(q \<rightarrow> f qs)\<in>\<delta> \<Longrightarrow> A f = Some (length qs)"
begin

  lemma rules_legal: "r\<in>\<delta> \<Longrightarrow> r\<in>legal_rules Q"
    apply (rule legal_rulesI)
    apply assumption
    apply (auto simp add: ta_rstates_def \<delta>_states_def) [1]
    apply (case_tac r)
    apply (auto intro: ranked)
    done

    \<comment> \<open>Only well-ranked trees are accepted\<close>
  lemma accs_is_ranked: "accs \<delta> t q \<Longrightarrow> t\<in>ranked_trees A"
    apply (induct \<delta>\<equiv>\<delta> t q rule: accs.induct)
    apply (rule ranked_trees.intros)
    apply (auto simp add: set_conv_nth ranked)
    done

    \<comment> \<open>The language consists of well-ranked trees\<close>
  theorem lang_is_ranked: "ta_lang TA \<subseteq> ranked_trees A"
    using accs_is_ranked by (auto simp add: ta_lang_def)

end

subsubsection "Deterministic Tree Automata"

  \<comment> \<open>Deterministic, (bottom-up) finite tree automaton (DFTA)\<close>
locale det_tree_automaton = ranked_tree_automaton TA A
  for TA :: "('Q,'L) tree_automaton_rec" and A +
  assumes deterministic: "\<lbrakk> (q \<rightarrow> f qs)\<in>\<delta>; (q' \<rightarrow> f qs)\<in>\<delta> \<rbrakk> \<Longrightarrow> q=q'"
begin
  theorem accs_unique: "\<lbrakk> accs \<delta> t q; accs \<delta> t q' \<rbrakk> \<Longrightarrow> q=q'"
    unfolding accs_laz
  proof (induct \<delta>\<equiv>\<delta> t q arbitrary: q' rule: accs_laz.induct[case_names step])
    case (step q f qs ts q')
    hence I: 
      "(q \<rightarrow> f qs) \<in> \<delta>"
      "list_all_zip (accs_laz \<delta>) ts qs"
      "list_all_zip (\<lambda>t q. (\<forall>q'. accs_laz \<delta> t q' \<longrightarrow> q=q')) ts qs"
      "accs_laz \<delta> (NODE f ts) q'"
      by auto
    from I(4) obtain qs' where A':
      "(q' \<rightarrow> f qs') \<in> \<delta>"
      "list_all_zip (accs_laz \<delta>) ts qs'"
      by (auto elim!: accs_laz.cases)

    from I(2,3) A'(2) have "list_all_zip (=) qs qs'"
      by (auto simp add: list_all_zip_alt)
    hence "qs=qs'" by (auto simp add: laz_eq)
    with deterministic[OF I(1), of q'] A'(1) show "q=q'" by simp
  qed
    
end

subsubsection "Complete Tree Automata"

locale complete_tree_automaton = det_tree_automaton TA A 
  for TA :: "('Q,'L) tree_automaton_rec" and A
  +
  assumes complete: 
  "\<lbrakk> qs\<in>lists Q; A f = Some (length qs) \<rbrakk> \<Longrightarrow> \<exists>q. (q \<rightarrow> f qs)\<in>\<delta>"
begin

    \<comment> \<open>In a complete DFTA, all trees can be labeled by some state\<close>
  theorem label_all: "t\<in>ranked_trees A \<Longrightarrow> \<exists>q\<in>Q. accs \<delta> t q"
  proof (induct rule: ranked_trees.induct[case_names constr])
    case (constr ts f)
    obtain qs where QS:
      "qs\<in>lists Q"
      "list_all_zip (accs \<delta>) ts qs" 
      and [simp]: "length qs = length ts"
    proof -
      from constr(1) have "\<forall>i<length ts. \<exists>q. q\<in>Q \<and> accs \<delta> (ts!i) q" 
        by (auto)
      thus ?thesis
        apply (erule_tac obtain_list_from_elements)
        apply (rule_tac that)
        apply (auto simp add: list_all_zip_alt set_conv_nth)
        done
    qed
    moreover from complete[OF QS(1), simplified, OF constr(2)] obtain q 
      where "(q \<rightarrow> f qs) \<in>\<delta>" ..
    ultimately show ?case 
      by (auto simp add: accs_laz ta_rstates_def 
               intro: accs_laz.intros \<delta>_statesI)
  qed

end


subsection "Algorithms"
text \<open>
  In this section, basic algorithms on tree-automata are specified.
  The specification is a high-level, non-executable specification, intended
  to be refined to more low-level specifications, as done in 
  Sections~\ref{sec:absalgo} and \ref{sec:taimpl}.
\<close>

subsubsection "Empty Automaton"
definition "ta_empty == \<lparr> ta_initial = {}, ta_rules = {}\<rparr>"

theorem ta_empty_lang[simp]: "ta_lang ta_empty = {}"
  by (auto simp add: ta_empty_def ta_lang_def)

theorem ta_empty_ta[simp, intro!]: "tree_automaton ta_empty"
  apply (unfold_locales)
  apply (unfold ta_empty_def)
  apply auto
  done

theorem (in finite_alphabet) ta_empty_rta[simp, intro!]: 
  "ranked_tree_automaton ta_empty A"
  apply (unfold_locales)
  apply (unfold ta_empty_def)
  apply auto
  done

theorem (in finite_alphabet) ta_empty_dta[simp, intro!]: 
  "det_tree_automaton ta_empty A"
  apply (unfold_locales)
  apply (unfold ta_empty_def)
  apply (auto)
  done

subsubsection "Remapping of States"

fun remap_rule where "remap_rule f (q \<rightarrow> l qs) = ((f q) \<rightarrow> l (map f qs))"
definition 
  "ta_remap f TA == \<lparr> ta_initial = f ` ta_initial TA, 
                      ta_rules = remap_rule f ` ta_rules TA 
                    \<rparr>"

lemma \<delta>_states_remap[simp]: "\<delta>_states (remap_rule f ` \<delta>) = f` \<delta>_states \<delta>"
  apply (auto simp add: \<delta>_states_def)
  apply (case_tac a)
  apply force
  apply (case_tac xb)
  apply force
  done

lemma remap_accs1: "accs \<delta> n q \<Longrightarrow> accs (remap_rule f ` \<delta>) n (f q)"
proof (induct rule: accs.induct[case_names step])
  case (step q l qs \<delta> ts)
  from step.hyps(1) have 1: "((f q) \<rightarrow> l (map f qs)) \<in> remap_rule f ` \<delta>" 
    by (drule_tac f="remap_rule f" in imageI) simp
  show ?case proof (rule accs.intros[OF 1])
    fix i assume "i<length (map f qs)"
    with step.hyps(4) show "accs (remap_rule f ` \<delta>) (ts ! i) (map f qs ! i)" 
      by auto
  qed (auto simp add: step.hyps(2))
qed

lemma remap_lang1: "t\<in>ta_lang TA \<Longrightarrow> t\<in>ta_lang (ta_remap f TA)"
  by (unfold ta_lang_def ta_remap_def) (auto dest: remap_accs1)

lemma remap_accs2: "\<lbrakk> 
    accs \<delta>' n q'; 
    \<delta>'=(remap_rule f ` \<delta>); 
    q'=f q; 
    inj_on f Q; 
    q\<in>Q; 
    \<delta>_states \<delta> \<subseteq> Q 
  \<rbrakk> \<Longrightarrow> accs \<delta> n q"
proof (induct arbitrary: \<delta> q rule: accs.induct[case_names step])
  case (step q' l qs \<delta>' ts \<delta> q)
  note [simp] = step.prems(1,2)
  from step.hyps(1)[simplified] step.prems(3,4,5) have 
    R: "(q \<rightarrow> l (map (inv_on f Q) qs))\<in>\<delta>"
    apply (erule_tac imageE)
    apply (case_tac x)
    apply (auto simp del:map_map)
    apply (subst inj_on_map_inv_f)
    apply (auto dest: \<delta>_statesI) [2]
    apply (subgoal_tac "q\<in>\<delta>_states \<delta>")
    apply (unfold inj_on_def) [1]
    apply (metis \<delta>_statesI(1) contra_subsetD)
    apply (fastforce intro: \<delta>_statesI(1) dest: inj_onD)
    done
  show ?case proof (rule accs.intros[OF R])
    fix i 
    assume "i < length (map (inv_on f Q) qs)"
    hence L: "i<length qs" by simp

    from step.hyps(1)[simplified] step.prems(5) have 
      IR: "!!i. i<length qs \<Longrightarrow> qs!i \<in> f ` Q"
      apply auto
      apply (case_tac x)
      apply (auto)
      apply (rename_tac list)
      apply (subgoal_tac "list!i \<in> \<delta>_states \<delta>")
      apply blast
      apply (auto dest!: \<delta>_statesI(2))
      done

    show "accs \<delta> (ts ! i) (map (inv_on f Q) qs ! i)"
      apply (rule step.hyps(4)[OF L, simplified])
      apply (simp_all add: f_inv_on_f[OF IR[OF L]] 
                      inv_on_f_range[OF IR[OF L]] 
                      L step.prems(3,5))
      done
  qed (auto simp add: step.hyps(2))
qed

lemma (in tree_automaton) remap_lang2: 
  assumes I: "inj_on f (ta_rstates TA)" 
  shows "t\<in>ta_lang (ta_remap f TA) \<Longrightarrow> t\<in>ta_lang TA"
  apply (unfold ta_lang_def ta_remap_def) 
  apply auto
  apply (rule_tac x=x in bexI)
  apply (drule remap_accs2[OF _ _ _ I])
  apply (auto dest: is_subset)
  done

theorem (in tree_automaton) remap_lang: 
  "inj_on f (ta_rstates TA) \<Longrightarrow> ta_lang (ta_remap f TA) = ta_lang TA"
  by (auto intro: remap_lang1 remap_lang2)

lemma (in tree_automaton) remap_ta[intro!, simp]: 
  "tree_automaton (ta_remap f TA)"
  using initial_subset states_subset finite_states finite_rules
  by (unfold_locales) (auto simp add: ta_remap_def ta_rstates_def)

lemma (in ranked_tree_automaton) remap_rta[intro!, simp]:
  "ranked_tree_automaton (ta_remap f TA) A"
proof -
  interpret ta: tree_automaton "(ta_remap f TA)" by simp
  show ?thesis
    apply (unfold_locales)
    apply (auto simp add: ta_remap_def)
    apply (case_tac x)
    apply (auto simp add: ta_remap_def intro: ranked)
    done
qed

lemma (in det_tree_automaton) remap_dta[intro, simp]:
  assumes INJ: "inj_on f Q"
  shows "det_tree_automaton (ta_remap f TA) A"
proof -
  interpret ta: ranked_tree_automaton "(ta_remap f TA)" A by simp
  show ?thesis 
  proof
    fix q q' l qs
    assume A: 
      "(q \<rightarrow> l qs) \<in>ta_rules (ta_remap f TA)"
      "(q' \<rightarrow> l qs) \<in>ta_rules (ta_remap f TA)"
    then obtain qo qo' qso qso' where RO:
      "(qo \<rightarrow> l qso) \<in> \<delta>"
      "(qo' \<rightarrow> l qso') \<in> \<delta>"
      and [simp]:
      "q=f qo"
      "q'=f qo'"
      "qs = map f qso"
      "map f qso = map f qso'"
      apply (auto simp add: ta_remap_def)
      apply (case_tac x, case_tac xa)
      apply auto
      done
    from RO have OQ: "qo\<in>Q" "qo'\<in>Q" "set qso \<subseteq> Q" "set qso' \<subseteq> Q"
      by (unfold ta_rstates_def)
         (auto dest: \<delta>_statesI)
    
    from OQ(3,4) have INJQSO: "inj_on f (set qso \<union> set qso')"
      by (auto intro: subset_inj_on[OF INJ])

    from inj_on_map_eq_map[OF INJQSO] have "qso=qso'" by simp
    with deterministic[OF RO(1)] RO(2) have "qo=qo'" by simp
    thus "q=q'" by simp
  qed
qed

  
lemma (in complete_tree_automaton) remap_cta[intro, simp]:
  assumes INJ: "inj_on f Q"
  shows "complete_tree_automaton (ta_remap f TA) A"
proof -
  interpret ta: det_tree_automaton "(ta_remap f TA)" A by (simp add: INJ)
  show ?thesis
  proof
    fix qs l
    assume A:
      "qs \<in> lists (ta_rstates (ta_remap f TA))" 
      "A l = Some (length qs)"
    from A(1) have "qs\<in>lists (f`Q)"
      by (auto simp add: ta_rstates_def ta_remap_def)
    then obtain qso where QSO:
      "qso\<in>lists Q"
      "qs = map f qso"
      by (blast elim!: lists_image_witness)
    hence [simp]: "length qso = length qs" by simp

    from complete[OF QSO(1)] A(2) obtain qo where "(qo \<rightarrow> l qso) \<in> \<delta>"
      by auto
    
    with QSO(2) have "((f qo) \<rightarrow> l qs)\<in>ta_rules (ta_remap f TA)" 
      by (force simp add: ta_remap_def)
    thus "\<exists>q. q \<rightarrow> l qs \<in> ta_rules (ta_remap f TA)" ..
  qed
qed

subsubsection "Union"

definition "ta_union TA TA' == 
  \<lparr> ta_initial = ta_initial TA \<union> ta_initial TA', 
    ta_rules = ta_rules TA \<union> ta_rules TA' 
  \<rparr>"

\<comment> \<open>Given two disjoint sets of states, where no rule contains states from
  both sets, then any accepted tree is also accepted when only using one of the 
  subsets of states and rules. 
  This lemma and its corollaries capture the basic idea of 
  the union-algorithm.\<close>
lemma accs_exclusive_aux: 
  "\<lbrakk> accs \<delta>n n q; \<delta>n=\<delta>\<union>\<delta>'; \<delta>_states \<delta> \<inter> \<delta>_states \<delta>' = {}; q\<in>\<delta>_states \<delta> \<rbrakk> 
   \<Longrightarrow> accs \<delta> n q"
proof (induct arbitrary: \<delta> \<delta>' rule: accs.induct[case_names step])
  case (step q l qs \<delta>n ts \<delta> \<delta>')
  note [simp] = step.prems(1)
  note [simp] = step.hyps(2)[symmetric] step.hyps(3)
  from step.prems have "q\<notin>\<delta>_states \<delta>'" by blast
  with step.hyps(1) have "set qs \<subseteq> \<delta>_states \<delta>" and R: "(q \<rightarrow> l qs)\<in>\<delta>" 
    by (auto dest: \<delta>_statesI)
  hence "!!i. i<length qs \<Longrightarrow> accs \<delta> (ts ! i) (qs ! i)" 
    by (force intro: step.hyps(4)[OF _ step.prems(1,2)])
  with accs.intros[OF R step.hyps(2)] show ?case .
qed

corollary accs_exclusive1: 
  "\<lbrakk> accs (\<delta>\<union>\<delta>') n q; \<delta>_states \<delta> \<inter> \<delta>_states \<delta>' = {}; q\<in>\<delta>_states \<delta> \<rbrakk> 
   \<Longrightarrow> accs \<delta> n q"
using accs_exclusive_aux[of _ n q \<delta> \<delta>'] by blast

corollary accs_exclusive2: 
  "\<lbrakk> accs (\<delta>\<union>\<delta>') n q; \<delta>_states \<delta> \<inter> \<delta>_states \<delta>' = {}; q\<in>\<delta>_states \<delta>' \<rbrakk> 
   \<Longrightarrow> accs \<delta>' n q"
using accs_exclusive_aux[of _ n q \<delta>' \<delta>] by blast

lemma ta_union_correct_aux1: 
  fixes TA TA'
  assumes TA: "tree_automaton TA"
  assumes TA': "tree_automaton TA'"
  assumes DJ: "ta_rstates TA \<inter> ta_rstates TA' = {}" 
  shows "ta_lang (ta_union TA TA') = ta_lang TA \<union> ta_lang TA'"
proof (safe)
  interpret ta: tree_automaton TA using TA .
  interpret ta': tree_automaton TA' using TA' .

  from DJ ta.states_subset ta'.states_subset have 
    DJ': "\<delta>_states (ta_rules TA) \<inter> \<delta>_states (ta_rules TA') = {}" 
    by blast

  fix n
  assume A: "n \<in> ta_lang (ta_union TA TA')" "n \<notin> ta_lang TA'"
  from A(1) obtain q where 
    B: "q\<in>ta_initial TA \<union> ta_initial TA'" 
       "accs (ta_rules TA \<union> ta_rules TA') n q"
    by (auto simp add: ta_lang_def ta_union_def)
  from \<delta>_states_accsI[OF B(2), simplified] show "n\<in>ta_lang TA" proof
    assume C: "q\<in>\<delta>_states (ta_rules TA)"
    with accs_exclusive1[OF B(2) DJ'] have "accs (ta_rules TA) n q" .
    moreover from DJ C ta'.initial_subset ta.states_subset B(1) have 
      "q\<in>ta_initial TA" 
      by auto
    ultimately show ?thesis by (unfold ta_lang_def) auto
  next
    assume C: "q\<in>\<delta>_states (ta_rules TA')"
    with accs_exclusive2[OF B(2) DJ'] have "accs (ta_rules TA') n q" .
    moreover from DJ C ta.initial_subset B(1) ta'.states_subset have 
      "q\<in>ta_initial TA'" 
      by auto
    ultimately have False using A(2) by (unfold ta_lang_def) auto
    thus ?thesis ..
  qed
qed (unfold ta_lang_def ta_union_def, auto intro: accs_mono)

lemma ta_union_correct_aux2: 
  fixes TA TA'
  assumes TA: "tree_automaton TA"
  assumes TA': "tree_automaton TA'"
  shows "tree_automaton (ta_union TA TA')"
proof -
  interpret ta: tree_automaton TA using TA .
  interpret ta': tree_automaton TA' using TA' .

  show ?thesis
    apply (unfold_locales)
    apply (unfold ta_union_def)
    apply auto
    done
qed

  \<comment> \<open>If the sets of states are disjoint, the language of the union-automaton
    is the union of the languages of the original automata.\<close>
theorem ta_union_correct:
  fixes TA TA'
  assumes TA: "tree_automaton TA"
  assumes TA': "tree_automaton TA'"
  assumes DJ: "ta_rstates TA \<inter> ta_rstates TA' = {}" 
  shows "ta_lang (ta_union TA TA') = ta_lang TA \<union> ta_lang TA'"
        "tree_automaton (ta_union TA TA')"
  using ta_union_correct_aux1[OF TA TA' DJ]
        ta_union_correct_aux2[OF TA TA']
  by auto

lemma ta_union_rta: 
  fixes TA TA'
  assumes TA: "ranked_tree_automaton TA A"
  assumes TA': "ranked_tree_automaton TA' A"
  shows "ranked_tree_automaton (ta_union TA TA') A"
proof -
  interpret ta: ranked_tree_automaton TA A using TA .
  interpret ta': ranked_tree_automaton TA' A using TA' .

  show ?thesis
    apply (unfold_locales)
    apply (unfold ta_union_def)
    apply (auto intro: ta.ranked ta'.ranked)
    done
qed

text "The union-algorithm may wrap the states of the first and second automaton 
      in order to make them disjoint"
datatype ('q1,'q2) ustate_wrapper = USW1 'q1 | USW2 'q2 

lemma usw_disjoint[simp]: 
  "USW1 ` X \<inter> USW2 ` Y = {}"
  "remap_rule USW1 ` X \<inter> remap_rule USW2 ` Y = {}"
  apply auto
  apply (case_tac xa, case_tac xb)
  apply auto
  done
  
lemma states_usw_disjoint[simp]: 
  "ta_rstates (ta_remap USW1 X) \<inter> ta_rstates (ta_remap USW2 Y) = {}"
  by (auto simp add: ta_remap_def ta_rstates_def)

lemma usw_inj_on[simp, intro!]:
  "inj_on USW1 X" 
  "inj_on USW2 X" 
  by (auto intro: inj_onI)

definition "ta_union_wrap TA TA' = 
  ta_union (ta_remap USW1 TA) (ta_remap USW2 TA')"

lemma ta_union_wrap_correct:
  fixes TA :: "('Q1,'L) tree_automaton_rec"
  fixes TA' :: "('Q2,'L) tree_automaton_rec"
  assumes TA: "tree_automaton TA"
  assumes TA': "tree_automaton TA'"
  shows "ta_lang (ta_union_wrap TA TA') = ta_lang TA \<union> ta_lang TA'" (is ?T1)
        "tree_automaton (ta_union_wrap TA TA')" (is ?T2)
proof -
  interpret a1: tree_automaton TA by fact
  interpret a2: tree_automaton TA' by fact

  show ?T1 ?T2
    by (unfold ta_union_wrap_def)
       (simp_all add: ta_union_correct a1.remap_lang a2.remap_lang)
qed

lemma ta_union_wrap_rta:
  fixes TA TA'
  assumes TA: "ranked_tree_automaton TA A"
  assumes TA': "ranked_tree_automaton TA' A"
  shows "ranked_tree_automaton (ta_union_wrap TA TA') A"
proof -
  interpret ta: ranked_tree_automaton TA A using TA .
  interpret ta': ranked_tree_automaton TA' A using TA' .

  show ?thesis
    by (unfold ta_union_wrap_def)
       (simp add: ta_union_rta)

qed


subsubsection "Reduction"

definition "reduce_rules \<delta> P == \<delta> \<inter> { r. rule_states r \<subseteq> P }"

lemma reduce_rulesI: "\<lbrakk>r\<in>\<delta>; rule_states r \<subseteq> P\<rbrakk> \<Longrightarrow> r\<in>reduce_rules \<delta> P"
  by (unfold reduce_rules_def) auto

lemma reduce_rulesD: 
  "\<lbrakk> r\<in>reduce_rules \<delta> P \<rbrakk> \<Longrightarrow> r\<in>\<delta>"
  "\<lbrakk> r\<in>reduce_rules \<delta> P; q\<in>rule_states r\<rbrakk> \<Longrightarrow> q\<in>P"
  by (unfold reduce_rules_def) auto

lemma reduce_rules_subset: "reduce_rules \<delta> P \<subseteq> \<delta>"
  by (unfold reduce_rules_def) auto

lemma reduce_rules_mono: "P \<subseteq> P' \<Longrightarrow> reduce_rules \<delta> P \<subseteq> reduce_rules \<delta> P'"
  by (unfold reduce_rules_def) auto

lemma \<delta>_states_reduce_subset: 
  shows "\<delta>_states (reduce_rules \<delta> Q) \<subseteq> \<delta>_states \<delta> \<inter> Q"
  by (unfold \<delta>_states_def reduce_rules_def)
    auto

lemmas \<delta>_states_reduce_subsetI = rev_subsetD[OF _ \<delta>_states_reduce_subset]

definition ta_reduce 
  :: "('Q,'L) tree_automaton_rec \<Rightarrow> ('Q set) \<Rightarrow> ('Q,'L) tree_automaton_rec"
  where "ta_reduce TA P ==
    \<lparr> ta_initial = ta_initial TA \<inter> P,
      ta_rules = reduce_rules (ta_rules TA) P \<rparr>"

\<comment> \<open>Reducing a tree automaton preserves the tree automata invariants\<close>
theorem ta_reduce_inv: assumes A: "tree_automaton TA" 
  shows "tree_automaton (ta_reduce TA P)"
proof -
  interpret tree_automaton TA using A .
  show ?thesis proof
    show "finite (ta_rules (ta_reduce TA P))" 
         "finite (ta_initial (ta_reduce TA P))"
      using finite_states finite_rules finite_subset[OF reduce_rules_subset]
      by (unfold ta_reduce_def) (auto simp add: Let_def)
  qed
qed
 
lemma reduce_\<delta>_states_rules[simp]: 
  "(ta_rules (ta_reduce TA (\<delta>_states (ta_rules TA)))) = ta_rules TA"
  by (auto simp add: ta_reduce_def \<delta>_states_def reduce_rules_def)

\<comment> \<open>Reducing a tree automaton to the states that occur in its rules does 
      not change its language\<close>
lemma ta_reduce_\<delta>_states: 
  "ta_lang (ta_reduce TA (\<delta>_states (ta_rules TA))) = ta_lang TA"
  apply (auto simp add: ta_lang_def)
  apply (frule \<delta>_states_accsI)
  apply (auto simp add: ta_reduce_def \<delta>_states_def reduce_rules_def) [1]
  apply (frule \<delta>_states_accsI)
  apply (auto simp add: ta_reduce_def \<delta>_states_def reduce_rules_def) [1]
done

text_raw \<open>\paragraph{Forward Reduction}\<close>
text \<open>
  We characterize the set of forward accessible states by the reflexive,
  transitive closure of a forward-successor (\<open>f_succ \<subseteq> Q\<times>Q\<close>) relation 
  applied to the initial states.
  
  The forward-successors of a state $q$ are those states $q'$ such that there is
  a rule $q \leftarrow f(\ldots q' \ldots)$.
\<close>

  \<comment> \<open>Forward successors\<close>
inductive_set f_succ for \<delta> where
  "\<lbrakk>(q \<rightarrow> l qs)\<in>\<delta>; q'\<in>set qs\<rbrakk> \<Longrightarrow> (q,q') \<in> f_succ \<delta>"

  \<comment> \<open>Alternative characterization of forward successors\<close>
lemma f_succ_alt: "f_succ \<delta> = {(q,q'). \<exists>l qs. (q \<rightarrow> l qs)\<in>\<delta> \<and> q'\<in>set qs}"
  by (auto intro: f_succ.intros elim!: f_succ.cases)

  \<comment> \<open>Forward accessible states\<close>
definition "f_accessible \<delta> Q0 == ((f_succ \<delta>)\<^sup>*) `` Q0"

  \<comment> \<open>Alternative characterization of forward accessible states.
      The initial states are forward accessible, and if there is a rule
      whose lhs-state is forward-accessible, all rhs-states of that rule
      are forward-accessible, too.\<close>
inductive_set f_accessible_alt :: "('Q,'L) ta_rule set \<Rightarrow> 'Q set \<Rightarrow> 'Q set"
for \<delta> Q0
where
  fa_refl: "q0\<in>Q0 \<Longrightarrow> q0 \<in> f_accessible_alt \<delta> Q0" |
  fa_step: "\<lbrakk> q\<in>f_accessible_alt \<delta> Q0; (q \<rightarrow> l qs)\<in>\<delta>; q'\<in>set qs \<rbrakk> 
            \<Longrightarrow> q' \<in> f_accessible_alt \<delta> Q0"

lemma f_accessible_alt: "f_accessible \<delta> Q0 = f_accessible_alt \<delta> Q0"
  apply (unfold f_accessible_def f_succ_alt)
  apply auto
proof goal_cases
  case 1 thus ?case
    apply (induct rule: rtrancl_induct)
    apply (auto intro: f_accessible_alt.intros)
    done
next
  case 2 thus ?case
    apply (induct rule: f_accessible_alt.induct)
    apply (auto simp add: Image_def intro: rtrancl.intros)
    done
qed

lemmas f_accessibleI = f_accessible_alt.intros[folded f_accessible_alt]
lemmas f_accessibleE = f_accessible_alt.cases[folded f_accessible_alt]

lemma f_succ_finite[simp, intro]: "finite \<delta> \<Longrightarrow> finite (f_succ \<delta>)"
  apply (unfold f_succ_alt)
  apply (rule_tac B="\<delta>_states \<delta> \<times> \<delta>_states \<delta>" in finite_subset)
  apply (auto dest: \<delta>_statesI simp add: \<delta>_states_finite)
  done

lemma f_accessible_mono: "Q\<subseteq>Q' \<Longrightarrow> x\<in>f_accessible \<delta> Q \<Longrightarrow> x\<in>f_accessible \<delta> Q'"
  by (auto simp add: f_accessible_def)
  
lemma f_accessible_prepend: 
  "\<lbrakk> (q \<rightarrow> l qs) \<in> \<delta>; q'\<in>set qs; x\<in>f_accessible \<delta> {q'} \<rbrakk> 
    \<Longrightarrow> x\<in>f_accessible \<delta> {q}"
  by (auto dest: f_succ.intros simp add: f_accessible_def)

lemma f_accessible_subset: "q\<in>f_accessible \<delta> Q \<Longrightarrow> q\<in>Q \<union> \<delta>_states \<delta>"
  apply (unfold f_accessible_alt)
  apply (induct rule: f_accessible_alt.induct)
  apply (force simp add: \<delta>_states_def split: ta_rule.split_asm)+
  done

lemma (in tree_automaton) f_accessible_in_states: 
  "q\<in>f_accessible (ta_rules TA) (ta_initial TA) \<Longrightarrow> q\<in>ta_rstates TA"
  using initial_subset states_subset
  by (drule_tac f_accessible_subset) (auto)

lemma f_accessible_refl_inter_simp[simp]: "Q \<inter> f_accessible r Q = Q"
  by (unfold f_accessible_alt) (auto intro: fa_refl)

  \<comment> \<open>A tree remains accepted by a state @{text q} if the rules are reduced to 
        the states that are forward-accessible from @{text q}\<close>
lemma accs_reduce_f_acc: 
  "accs \<delta> t q \<Longrightarrow> accs (reduce_rules \<delta> (f_accessible \<delta> {q})) t q"
proof (induct rule: accs.induct[case_names step])
  case (step q l qs \<delta> n) 
  show ?case proof (rule accs.intros[of q l qs])
    show "(q \<rightarrow> l qs) \<in> reduce_rules \<delta> (f_accessible \<delta> {q})"
      using step(1)
      by (fastforce 
        intro!: reduce_rulesI 
        intro: f_succ.intros 
        simp add: f_accessible_def)
  next
    fix i 
    assume A: "i<length qs"

    have B: "f_accessible \<delta> {q} \<supseteq> f_accessible \<delta> {qs!i}" using step.hyps(1)
      by (force 
        simp add: A f_accessible_def 
        intro: converse_rtrancl_into_rtrancl f_succ.intros[where q'="qs!i"])
    show "accs (reduce_rules \<delta> (f_accessible \<delta> {q})) (n ! i) (qs ! i)"
      using accs_mono[OF step.hyps(4)[OF A] reduce_rules_mono[OF B]] .
  qed (simp_all add: step.hyps(2,3))
qed

  \<comment> \<open>Short-hand notation for forward-reducing a tree-automaton\<close>
abbreviation "ta_fwd_reduce TA == 
  (ta_reduce TA (f_accessible (ta_rules TA) (ta_initial TA)))"

\<comment> \<open>Forward-reducing a tree automaton does not change its language\<close>
theorem ta_reduce_f_acc[simp]: "ta_lang (ta_fwd_reduce TA) = ta_lang TA"
  apply (rule sym)
  apply (unfold ta_reduce_def ta_lang_def)
  apply (auto simp add: Let_def)
  apply (rule_tac x=q in bexI)
  apply (drule accs_reduce_f_acc)
  apply (rule_tac 
    P1="(f_accessible (ta_rules TA) {q})" 
    in accs_mono[OF _ reduce_rules_mono])
  apply (auto simp add: f_accessible_def)
  apply (rule_tac x=q in bexI)
  apply (blast intro: accs_mono[OF _ reduce_rules_subset])
  .

text_raw \<open>\paragraph{Backward Reduction}\<close>

text \<open>
  A state is backward accessible, iff at least one tree is accepted in it.

  Inductively, backward accessible states can be characterized as follows:
  A state is backward accessible, if it occurs on the left hand side of a 
  rule, and all states on this rule's right hand side are backward accessible.
\<close>
inductive_set b_accessible :: "('Q,'L) ta_rule set \<Rightarrow> 'Q set" 
  for \<delta>
  where
  "\<lbrakk> (q \<rightarrow> l qs)\<in>\<delta>; !!x. x\<in>set qs \<Longrightarrow> x\<in>b_accessible \<delta> \<rbrakk> \<Longrightarrow> q\<in>b_accessible \<delta>"

lemma b_accessibleI: 
  "\<lbrakk>(q \<rightarrow> l qs)\<in>\<delta>; set qs \<subseteq> b_accessible \<delta>\<rbrakk> \<Longrightarrow> q\<in>b_accessible \<delta>"
  by (auto intro: b_accessible.intros)

\<comment> \<open>States that accept a tree are backward accessible\<close>
lemma accs_is_b_accessible: "accs \<delta> t q \<Longrightarrow> q\<in>b_accessible \<delta>"
  apply (induct rule: accs.induct)
  apply (rule b_accessible.intros)
  apply assumption
  apply (fastforce simp add: in_set_conv_nth)
  done

lemma b_acc_subset_\<delta>_statesI: "x\<in>b_accessible \<delta> \<Longrightarrow> x\<in>\<delta>_states \<delta>"
  apply (erule b_accessible.cases)
  apply (auto intro: \<delta>_statesI)
  done

lemma b_acc_subset_\<delta>_states: "b_accessible \<delta> \<subseteq> \<delta>_states \<delta>"
  by (auto simp add: b_acc_subset_\<delta>_statesI)

lemma b_acc_finite[simp, intro!]: "finite \<delta> \<Longrightarrow> finite (b_accessible \<delta>)"
  apply (rule finite_subset[OF b_acc_subset_\<delta>_states])
  apply auto
  done

  \<comment> \<open>Backward accessible states accept at least one tree\<close>
lemma b_accessible_is_accs: 
  "\<lbrakk> q\<in>b_accessible (ta_rules TA); 
     !!t. accs (ta_rules TA) t q \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
proof (induct arbitrary: P rule: b_accessible.induct[case_names IH])
  case (IH q l qs) 

  obtain ts where 
    A: "\<forall>i<length qs. accs (ta_rules TA) (ts!i) (qs!i)" 
       "length ts = length qs"
  proof -
    from IH(3) have "\<forall>x\<in>set qs. \<exists>t. accs (ta_rules TA) t x" by auto
    hence "\<exists>ts. (\<forall>i<length qs. accs (ta_rules TA) (ts!i) (qs!i)) 
                \<and> length ts = length qs"
    proof (induct qs)
      case Nil thus ?case by simp
    next
      case (Cons q qs) then obtain ts where 
        IHAPP: "\<forall>i<length qs. accs (ta_rules TA) (ts ! i) (qs ! i)" and 
        L: "length ts = length qs" 
        by auto
      moreover from Cons obtain t where "accs (ta_rules TA) t q" by auto
      ultimately have 
        "\<forall>i<length (q#qs). accs (ta_rules TA) ((t#ts) ! i) ((q#qs) ! i)"
        apply auto
        apply (case_tac i)
        apply auto
        done
      thus ?case using L by auto
    qed
    thus thesis by (blast intro: that)
  qed

  from A show ?case 
    apply (rule_tac IH(4)[OF accs.intros[OF IH(1)]])
    apply auto
    done
qed

  \<comment> \<open>All trees remain accepted when reducing the rules to 
      backward-accessible states\<close>
lemma accs_reduce_b_acc: 
  "accs \<delta> t q \<Longrightarrow> accs (reduce_rules \<delta> (b_accessible \<delta>)) t q"
  apply (induct rule: accs.induct)
  apply (rule accs.intros)
  apply (rule reduce_rulesI)
  apply assumption
  apply (auto)
  apply (rule_tac t="NODE f ts" in accs_is_b_accessible)
  apply (rule_tac accs.intros)
  apply auto
  apply (simp only: in_set_conv_nth)
  apply (erule_tac exE)
  apply (rule_tac t="ts ! i" in accs_is_b_accessible)
  apply auto
  done

  \<comment> \<open>Shorthand notation for backward-reduction of a tree automaton\<close>
abbreviation "ta_bwd_reduce TA == (ta_reduce TA (b_accessible (ta_rules TA)))"

\<comment> \<open>Backwards-reducing a tree automaton does not change its language\<close>
theorem ta_reduce_b_acc[simp]: "ta_lang (ta_bwd_reduce TA) = ta_lang TA"
  apply (rule sym)
  apply (unfold ta_reduce_def ta_lang_def)
  apply (auto simp add: Let_def)
  apply (rule_tac x=q in bexI)
  apply (blast intro: accs_reduce_b_acc)
  apply (blast dest: accs_is_b_accessible)
  apply (rule_tac x=q in bexI)
  apply (blast intro: accs_mono[OF _ reduce_rules_subset])
  .

  \<comment> \<open>Emptiness check by backward reduction. The language of a tree automaton 
    is empty, if and only if no initial state is backwards-accessible.\<close>
theorem empty_if_no_b_accessible: 
  "ta_lang TA = {} \<longleftrightarrow> ta_initial TA \<inter> b_accessible (ta_rules TA) = {}"
  by (auto 
    simp add: ta_lang_def 
    intro: accs_is_b_accessible b_accessible_is_accs)

subsubsection "Product Automaton"
text \<open>
  The product automaton of two tree automata accepts the intersection 
  of the languages of the two automata.
\<close>

  \<comment> \<open>Product rule\<close>
fun r_prod where
  "r_prod (q1 \<rightarrow> l1 qs1) (q2 \<rightarrow> l2 qs2) = ((q1,q2) \<rightarrow> l1 (zip qs1 qs2))"

  \<comment> \<open>Product rules\<close>
definition "\<delta>_prod \<delta>1 \<delta>2 == {
  r_prod (q1 \<rightarrow> l qs1) (q2 \<rightarrow> l qs2) | q1 q2 l qs1 qs2.
    length qs1 = length qs2 \<and> 
    (q1 \<rightarrow> l qs1)\<in>\<delta>1 \<and> 
    (q2 \<rightarrow> l qs2)\<in>\<delta>2
}"

lemma \<delta>_prodI: "\<lbrakk> 
    length qs1 = length qs2;
    (q1 \<rightarrow> l qs1)\<in>\<delta>1;
    (q2 \<rightarrow> l qs2)\<in>\<delta>2 \<rbrakk> \<Longrightarrow> ((q1,q2) \<rightarrow> l (zip qs1 qs2)) \<in> \<delta>_prod \<delta>1 \<delta>2"
  by (auto simp add: \<delta>_prod_def)

lemma \<delta>_prodE: 
  "\<lbrakk> 
    r\<in>\<delta>_prod \<delta>1 \<delta>2; 
    !!q1 q2 l qs1 qs2. \<lbrakk> length qs1 = length qs2;
                         (q1 \<rightarrow> l qs1)\<in>\<delta>1;
                         (q2 \<rightarrow> l qs2)\<in>\<delta>2;
                         r = ((q1,q2) \<rightarrow> l (zip qs1 qs2)) 
                       \<rbrakk> \<Longrightarrow> P 
   \<rbrakk> \<Longrightarrow> P"
  by (auto simp add: \<delta>_prod_def)

  \<comment> \<open>With the product rules, only trees can be constructed that can also be 
      constructed with the two original sets of rules\<close>
lemma \<delta>_prod_sound: 
  assumes A: "accs (\<delta>_prod \<delta>1 \<delta>2) t (q1,q2)" 
  shows "accs \<delta>1 t q1" "accs \<delta>2 t q2"
proof -
  {
    fix \<delta> q
    assume "accs \<delta> t q" "\<delta> = (\<delta>_prod \<delta>1 \<delta>2)" "q=(q1,q2)"
    hence "accs \<delta>1 t q1 \<and> accs \<delta>2 t q2"
      by (induct arbitrary: \<delta>1 \<delta>2 q1 q2 rule: accs.induct)
         (auto intro: accs.intros simp add: \<delta>_prod_def)
  } with A show "accs \<delta>1 t q1" "accs \<delta>2 t q2" by auto
qed

  \<comment> \<open>Any tree that can be constructed with both original sets of rules can also
      be constructed with the product rules\<close>
lemma \<delta>_prod_precise: 
  "\<lbrakk> accs \<delta>1 t q1; accs \<delta>2 t q2 \<rbrakk> \<Longrightarrow> accs (\<delta>_prod \<delta>1 \<delta>2) t (q1,q2)"
proof (induct arbitrary: \<delta>2 q2 rule: accs.induct[case_names step])
  case (step q1 l qs1 \<delta>1 ts \<delta>2 q2)
  note [simp] = step.hyps(2,3)
  from step.hyps(2) obtain qs2 where 
    I2: "(q2 \<rightarrow> l qs2)\<in>\<delta>2" 
        "!!i. i<length qs2 \<Longrightarrow> accs \<delta>2 (ts ! i) (qs2 ! i)" and 
    [simp]: "length qs2 = length ts"
    by (rule_tac accs.cases[OF step.prems]) fastforce
  show ?case 
  proof (rule accs.intros)
    from step.hyps(1) I2(1) show 
      "((q1,q2) \<rightarrow> l (zip qs1 qs2))\<in>\<delta>_prod \<delta>1 \<delta>2" and 
      [simp]: "length ts = length (zip qs1 qs2)"
      by (unfold \<delta>_prod_def) force+
  next
    fix i
    assume L: "i<length (zip qs1 qs2)"
    with step.hyps(4)[OF _ I2(2), of i] have 
      "accs (\<delta>_prod \<delta>1 \<delta>2) (ts ! i) (qs1 ! i, qs2 ! i)" 
      by simp
    also have "(qs1 ! i, qs2 ! i) = zip qs1 qs2 ! i" using L by auto
    finally show "accs (\<delta>_prod \<delta>1 \<delta>2) (ts ! i) (zip qs1 qs2 ! i)" .
  qed
qed

lemma \<delta>_prod_empty[simp]: 
  "\<delta>_prod {} \<delta> = {}"
  "\<delta>_prod \<delta> {} = {}"
  by (unfold \<delta>_prod_def) auto

lemma \<delta>_prod_2sng[simp]: 
  "\<lbrakk> rhsl r1 \<noteq> rhsl r2 \<rbrakk> \<Longrightarrow> \<delta>_prod {r1} {r2} = {}"
  "\<lbrakk> length (rhsq r1) \<noteq> length (rhsq r2) \<rbrakk> \<Longrightarrow> \<delta>_prod {r1} {r2} = {}"
  "\<lbrakk> rhsl r1 = rhsl r2; length (rhsq r1) = length (rhsq r2) \<rbrakk> 
    \<Longrightarrow> \<delta>_prod {r1} {r2} = {r_prod r1 r2}"
  apply (unfold \<delta>_prod_def)
  apply (cases r1, cases r2, auto)+
  done

lemma \<delta>_prod_Un[simp]: 
  "\<delta>_prod (\<delta>1\<union>\<delta>1') \<delta>2 = \<delta>_prod \<delta>1 \<delta>2 \<union> \<delta>_prod \<delta>1' \<delta>2"
  "\<delta>_prod \<delta>1 (\<delta>2\<union>\<delta>2') = \<delta>_prod \<delta>1 \<delta>2 \<union> \<delta>_prod \<delta>1 \<delta>2'"
  by (auto elim: \<delta>_prodE intro: \<delta>_prodI)

text \<open>The next two definitions are solely for technical reasons.
  They are required to allow simplification of expressions of the form
  @{term "\<delta>_prod (insert r \<delta>1) \<delta>2"} or @{term "\<delta>_prod \<delta>1 (insert r \<delta>2)"}, 
  without making the simplifier loop.
\<close>
definition "\<delta>_prod_sng1 r \<delta>2 == 
  case r of (q1 \<rightarrow> l qs1) \<Rightarrow> 
    { r_prod r (q2 \<rightarrow> l qs2) | 
         q2 qs2. length qs1 = length qs2 \<and> (q2 \<rightarrow> l qs2)\<in>\<delta>2 
    }"
definition "\<delta>_prod_sng2 \<delta>1 r == 
  case r of (q2 \<rightarrow> l qs2) \<Rightarrow> 
    { r_prod (q1 \<rightarrow> l qs1) r | 
         q1 qs1. length qs1 = length qs2 \<and> (q1 \<rightarrow> l qs1)\<in>\<delta>1 
    }"

lemma \<delta>_prod_sng_alt:
  "\<delta>_prod_sng1 r \<delta>2 = \<delta>_prod {r} \<delta>2"
  "\<delta>_prod_sng2 \<delta>1 r = \<delta>_prod \<delta>1 {r}"
  apply (unfold \<delta>_prod_def \<delta>_prod_sng1_def \<delta>_prod_sng2_def)
  apply (auto split: ta_rule.split)
  done
  
lemmas \<delta>_prod_insert = 
  \<delta>_prod_Un(1)[where ?\<delta>1.0="{x}", simplified, folded \<delta>_prod_sng_alt]
  \<delta>_prod_Un(2)[where ?\<delta>2.0="{x}", simplified, folded \<delta>_prod_sng_alt]
  for x

  \<comment> \<open>Product automaton\<close>
definition "ta_prod TA1 TA2 == 
  \<lparr> ta_initial = ta_initial TA1 \<times> ta_initial TA2, 
    ta_rules = \<delta>_prod (ta_rules TA1) (ta_rules TA2) 
  \<rparr>"
   
lemma ta_prod_correct_aux1: 
  "ta_lang (ta_prod TA1 TA2) = ta_lang TA1 \<inter> ta_lang TA2"
  by (unfold ta_lang_def ta_prod_def) (auto dest: \<delta>_prod_sound \<delta>_prod_precise)

lemma \<delta>_states_cart: 
  "q \<in> \<delta>_states (\<delta>_prod \<delta>1 \<delta>2) \<Longrightarrow> q \<in> \<delta>_states \<delta>1 \<times> \<delta>_states \<delta>2"
  by (unfold \<delta>_states_def \<delta>_prod_def) 
     (force split: ta_rule.split simp add: set_zip)

lemma \<delta>_prod_finite [simp, intro]: 
  "finite \<delta>1 \<Longrightarrow> finite \<delta>2 \<Longrightarrow> finite (\<delta>_prod \<delta>1 \<delta>2)"
proof -
  have 
    "\<delta>_prod \<delta>1 \<delta>2 
    \<subseteq> (\<lambda>(r1,r2). case r1 of (q1 \<rightarrow> l1 qs1) \<Rightarrow> 
                  case r2 of (q2 \<rightarrow> l2 qs2) \<Rightarrow> 
                    ((q1,q2) \<rightarrow> l1 (zip qs1 qs2))) 
       ` (\<delta>1 \<times> \<delta>2)"
    by (unfold \<delta>_prod_def) force
  moreover assume "finite \<delta>1" "finite \<delta>2"
  ultimately show ?thesis 
    by (metis finite_imageI finite_cartesian_product finite_subset)
qed

lemma ta_prod_correct_aux2: 
  assumes TA: "tree_automaton TA1" "tree_automaton TA2" 
  shows "tree_automaton (ta_prod TA1 TA2)"
proof -
  interpret ta1: tree_automaton TA1 using TA by blast
  interpret ta2: tree_automaton TA2 using TA by blast
  show ?thesis 
    apply unfold_locales
    apply (unfold ta_prod_def)
    apply (auto 
      intro: ta1.is_subset ta2.is_subset \<delta>_prod_finite 
      dest: \<delta>_states_cart 
      simp add: ta1.finite_states ta2.finite_states 
                ta1.finite_rules ta2.finite_rules)
    done
qed

  \<comment> \<open>The language of the product automaton is the intersection of the languages
      of the two original automata\<close>
theorem ta_prod_correct:
  assumes TA: "tree_automaton TA1" "tree_automaton TA2" 
  shows 
    "ta_lang (ta_prod TA1 TA2) = ta_lang TA1 \<inter> ta_lang TA2"
    "tree_automaton (ta_prod TA1 TA2)"
  using ta_prod_correct_aux1 
        ta_prod_correct_aux2[OF TA] 
  by auto


lemma ta_prod_rta: 
  assumes TA: "ranked_tree_automaton TA1 A" "ranked_tree_automaton TA2 A" 
  shows "ranked_tree_automaton (ta_prod TA1 TA2) A"
proof -
  interpret ta1: ranked_tree_automaton TA1 A using TA by blast
  interpret ta2: ranked_tree_automaton TA2 A using TA by blast

  interpret tap: tree_automaton "(ta_prod TA1 TA2)"
    apply (rule ta_prod_correct_aux2)
    by unfold_locales

  show ?thesis 
    apply unfold_locales
    apply (unfold ta_prod_def \<delta>_prod_def)
    apply (auto intro: ta1.ranked ta2.ranked)
    done
qed

subsubsection "Determinization"
text \<open>
  We only formalize the brute-force subset construction without reduction. 

  The basic idea of this construction is to construct an automaton where the
  states are sets of original states, and the lhs of a rule consists of all
  states that a term with given rhs and function symbol may be labeled by.
\<close>

context ranked_tree_automaton
begin
  \<comment> \<open>Left-hand side of subset rule for given symbol and rhs\<close>
  definition "\<delta>ss_lhs f ss == 
    { q | q qs. (q \<rightarrow> f qs)\<in>\<delta> \<and> list_all_zip (\<in>) qs ss }"

  \<comment> \<open>Subset construction\<close>
  inductive_set \<delta>ss :: "('Q set,'L) ta_rule set" where
    "\<lbrakk> A f = Some (length ss); 
       ss \<in> lists {s. s \<subseteq> ta_rstates TA}; 
       s = \<delta>ss_lhs f ss
     \<rbrakk> \<Longrightarrow> (s \<rightarrow> f ss) \<in> \<delta>ss"

  lemma \<delta>ssI: 
    assumes A: "A f = Some (length ss)"
               "ss \<in> lists {s. s \<subseteq> ta_rstates TA}"
    shows 
      "( (\<delta>ss_lhs f ss) \<rightarrow> f ss) \<in> \<delta>ss"
    using \<delta>ss.intros[where s="(\<delta>ss_lhs f ss)"] A
    by auto

  lemma \<delta>ss_subset[simp, intro!]: "\<delta>ss_lhs f ss \<subseteq> Q"
    by (unfold ta_rstates_def \<delta>ss_lhs_def) (auto intro: \<delta>_statesI)

  lemma \<delta>ss_finite[simp, intro!]: "finite \<delta>ss"
  proof -
    have "\<delta>ss \<subseteq> \<Union>((\<lambda>f. (\<lambda>(s,ss). (s \<rightarrow> f ss))
                     `({s. s\<subseteq>Q} 
                       \<times> (lists {s. s\<subseteq>Q} \<inter> {l. length l = the (A f)}))
                  ) ` F)" 
      (is "_\<subseteq>\<Union>((\<lambda>f. ?tr f ` ?prod f)`F)")
    proof (intro equalityI subsetI)
      fix r
      assume "r\<in>\<delta>ss"
      then obtain f s ss where 
        U: "r=(s \<rightarrow> f ss)" 
           "A f = Some (length ss)" 
           "ss\<in>lists {s. s\<subseteq>Q}" 
           "s=\<delta>ss_lhs f ss"
        by (force elim!: \<delta>ss.cases)
      from U(4) have "s\<subseteq>Q" by simp 
      moreover from U(2) have "length ss = the (A f)" by simp
      ultimately have "(s,ss)\<in>?prod f" using U(3) by auto
      hence "(s \<rightarrow> f ss)\<in>?tr f ` ?prod f" by auto
      moreover from U(2) have "f\<in>F" by auto
      ultimately show "r\<in>\<Union>((\<lambda>f. ?tr f ` ?prod f)`F)" using U(1) by auto
    qed
    moreover have "finite \<dots>"
      by (auto intro!: finite_imageI finite_SigmaI lists_of_len_fin)
    ultimately show ?thesis by (blast intro: finite_subset)
  qed

  lemma \<delta>ss_det: "\<lbrakk> (q \<rightarrow> f qs) \<in> \<delta>ss; (q' \<rightarrow> f qs) \<in>\<delta>ss \<rbrakk> \<Longrightarrow> q=q'"
    by (auto elim!: \<delta>ss.cases)

  lemma \<delta>ss_accs_sound: 
    assumes A: "accs \<delta> t q"  
    obtains s where
    "s\<subseteq>Q"
    "q\<in>s"
    "accs \<delta>ss t s"
  proof -
    have "\<exists>s\<subseteq>Q. q\<in>s \<and> accs_laz \<delta>ss t s" using A[unfolded accs_laz]
    proof (induct \<delta>\<equiv>\<delta> t q rule: accs_laz.induct[case_names step])
      case (step q f qs ts)
      hence I:
        "(q \<rightarrow> f qs)\<in>\<delta>"
        "list_all_zip (accs_laz \<delta>) ts qs"
        "list_all_zip (\<lambda>t q. \<exists>s. s\<subseteq>Q \<and> q\<in>s \<and> accs_laz \<delta>ss t s) ts qs"
        by simp_all
      from I(3) obtain ss where SS: 
        "ss \<in> lists {s. s\<subseteq>Q}"
        "list_all_zip (\<in>) qs ss"
        "list_all_zip (accs_laz \<delta>ss) ts ss"
        by (erule_tac laz_swap_ex) auto
      from I(2) SS(2) have 
        LEN[simp]: "length qs = length ts" "length ss = length ts"
        by (auto simp add: list_all_zip_alt)
      from ranked[OF I(1)] have AF: "A f = Some (length ts)" by simp

      from \<delta>ssI[of f ss, OF _ SS(1)] AF have 
        RULE_S: "((\<delta>ss_lhs f ss) \<rightarrow> f ss) \<in> \<delta>ss"
        by simp
      
      from accs_laz.intros[OF RULE_S SS(3)] have 
        G1: "accs_laz \<delta>ss (NODE f ts) (\<delta>ss_lhs f ss)" .
      from I(1) SS(2) have "q\<in>(\<delta>ss_lhs f ss)" by (auto simp add: \<delta>ss_lhs_def)
      thus ?case using G1 by auto
    qed
    thus ?thesis 
      apply (elim exE conjE)
      apply (rule_tac that)
      apply assumption
      apply (auto simp add: accs_laz)
      done
  qed


  lemma \<delta>ss_accs_precise:
    assumes A: "accs \<delta>ss t s" "q\<in>s"  
    shows "accs \<delta> t q"
    using A
    unfolding accs_laz
  proof (induct \<delta>\<equiv>\<delta>ss t s 
                arbitrary: q 
                rule: accs_laz.induct[case_names step])
    case (step s f ss ts)
    hence I:
      "(s \<rightarrow> f ss) \<in> \<delta>ss"
      "list_all_zip (accs_laz \<delta>ss) ts ss"
      "list_all_zip (\<lambda>t s. \<forall>q\<in>s. accs_laz \<delta> t q) ts ss"
      "q\<in>s"
      by (auto simp add: Ball_def)
      
    from I(2) have [simp]: "length ss = length ts" 
      by (simp add: list_all_zip_alt)

    from I(1) have SS: 
      "A f = Some (length ts)"
      "ss \<in> lists {s. s\<subseteq>Q}"
      "s=\<delta>ss_lhs f ss"
      by (force elim!: \<delta>ss.cases)+
      
    from I(4) SS(3) obtain qs where
      RULE: "(q \<rightarrow> f qs) \<in> \<delta>" and
      QSISS: "list_all_zip (\<in>) qs ss"
      by (auto simp add: \<delta>ss_lhs_def)
    from I(3) QSISS have CA: "list_all_zip (accs_laz \<delta>) ts qs"
      by (auto simp add: list_all_zip_alt)
    from accs_laz.intros[OF RULE CA] show ?case .
  qed
    

  \<comment> \<open>Determinization\<close>
  definition "detTA == \<lparr> ta_initial = { s. s\<subseteq>Q \<and> s\<inter>Qi \<noteq> {} }, 
                         ta_rules = \<delta>ss \<rparr>"
      
  theorem detTA_is_ta[simp, intro]:
    "det_tree_automaton detTA A"
    apply (unfold_locales)
    apply (auto simp add: detTA_def elim: \<delta>ss.cases)
    done
    

  theorem detTA_lang[simp]:
    "ta_lang (detTA) = ta_lang TA"
    apply (unfold ta_lang_def detTA_def)
    apply safe
    apply simp_all
  proof -
    fix t s
    assume A: 
      "s\<subseteq>Q \<and> s\<inter>Qi \<noteq> {}"
      "accs \<delta>ss t s"
    from A(1) obtain qi where QI: "qi\<in>s" "qi\<in>Qi" by auto

    from \<delta>ss_accs_precise[OF A(2) QI(1)] have "accs \<delta> t qi" .
    with QI(2) show "\<exists>qi\<in>Qi. accs \<delta> t qi" by blast
  next
    fix t qi
    assume A: 
      "qi\<in>Qi" 
      "accs \<delta> t qi"
    from \<delta>ss_accs_sound[OF A(2)] obtain s where SS: 
      "s\<subseteq>Q" 
      "qi\<in>s" 
      "accs \<delta>ss t s" .
    with A(1) show "\<exists>s\<subseteq>Q. s \<inter> Qi \<noteq> {} \<and> accs \<delta>ss t s" by blast
  qed
    
  lemmas detTA_correct = detTA_is_ta detTA_lang
end

subsubsection "Completion"
text \<open>
  To each deterministic tree automaton, rules and states can be added to make
  it complete, without changing its language.
\<close>

context det_tree_automaton
begin
  \<comment> \<open>States of the complete automaton\<close>
  definition "Qcomplete == insert None (Some`Q)"

  lemma Qcomplete_finite[simp, intro!]: "finite Qcomplete"
    by (auto simp add: Qcomplete_def)

  \<comment> \<open>Rules of the complete automaton\<close>
  definition \<delta>complete :: "('Q option, 'L) ta_rule set" where
    "\<delta>complete == (remap_rule Some ` \<delta>) 
                  \<union> { (None \<rightarrow> f qs) | f qs. 
                         A f = Some (length qs) 
                         \<and> qs\<in>lists Qcomplete 
                         \<and> \<not>(\<exists>qo qso. (qo \<rightarrow> f qso)\<in>\<delta> \<and> qs=map Some qso ) }"


  lemma \<delta>_states_complete: "q\<in>\<delta>_states \<delta>complete \<Longrightarrow> q\<in>Qcomplete"
    apply (erule \<delta>_statesE)
    apply (unfold \<delta>complete_def Qcomplete_def)
    apply auto
    apply (case_tac x)
    apply (auto simp add: ta_rstates_def intro: \<delta>_statesI) [1]
    apply (case_tac x)
    apply (auto simp add: ta_rstates_def dest: \<delta>_statesI)
    done
    

  definition 
    "completeTA == \<lparr> ta_initial = Some`Qi, ta_rules = \<delta>complete \<rparr>"

  lemma \<delta>complete_finite[simp, intro]: "finite \<delta>complete"
  proof -
    have "\<delta>complete \<subseteq> legal_rules Qcomplete"
      apply (rule)
      apply (rule legal_rulesI)
      apply assumption
      apply (case_tac x)
      apply (unfold \<delta>complete_def Qcomplete_def ta_rstates_def) [1]
      apply auto
      apply (case_tac xa)
      apply (auto dest: \<delta>_statesI)
      apply (case_tac xa)
      apply (auto dest: \<delta>_statesI)
      apply (unfold \<delta>complete_def Qcomplete_def ta_rstates_def) [1]
      apply (auto)
      apply (case_tac xa)
      apply (auto intro: ranked)
      done
    thus ?thesis by (auto intro: finite_subset)
  qed

  theorem completeTA_is_ta: "complete_tree_automaton completeTA A"
  proof (standard, goal_cases)
    case 1 thus ?case by (simp add: completeTA_def)
  next
    case 2 thus ?case by (simp add: completeTA_def)
  next
    case 3 thus ?case
      apply (auto simp add: completeTA_def \<delta>complete_def)
      apply (case_tac x)
      apply (auto intro: ranked)
      done
  next
    case 4 thus ?case
      apply (auto simp add: completeTA_def \<delta>complete_def)
      apply (case_tac x, case_tac xa)
      apply (auto intro: deterministic) [1]
      apply (case_tac x)
      apply auto [1]
      apply (case_tac x)
      apply auto [1]
      done
  next
    case prems: (5 qs f)
    {
      fix qo qso
      assume R: "(qo \<rightarrow> f qso)\<in>\<delta>" and [simp]: "qs=map Some qso"
      hence "((Some qo) \<rightarrow> f qs) \<in> remap_rule Some ` \<delta>" by force
      hence ?case by (simp add: completeTA_def \<delta>complete_def) blast
    } moreover {
      assume A: "\<not>(\<exists>qo qso. (qo \<rightarrow> f qso)\<in>\<delta> \<and> qs=map Some qso)"

      have "(Some ` Qi \<union> \<delta>_states \<delta>complete) \<subseteq> Qcomplete"
        apply (auto intro: \<delta>_states_complete)
        apply (simp add: Qcomplete_def ta_rstates_def)
        done

      with prems have B: "qs\<in>lists Qcomplete"
        by (auto simp add: completeTA_def ta_rstates_def)

      from A B prems(2) have ?case
        apply (rule_tac x=None in exI)
        apply (simp add: completeTA_def \<delta>complete_def)
        done
    } ultimately show ?case by blast
  qed

  theorem completeTA_lang: "ta_lang completeTA = ta_lang TA"
  proof (intro equalityI subsetI)
    \<comment> \<open>This direction is done by a monotonicity argument\<close>
    fix t
    assume "t\<in>ta_lang TA"
    then obtain qi where "qi\<in>Qi" "accs \<delta> t qi" by (auto simp add: ta_lang_def)
    hence 
      QI: "Some qi \<in> Some`Qi" and
      ACCS: "accs (remap_rule Some`\<delta>) t (Some qi)"
      by (auto intro: remap_accs1)
    have "(remap_rule Some`\<delta>) \<subseteq> \<delta>complete" by (unfold \<delta>complete_def) auto
    with ACCS have "accs \<delta>complete t (Some qi)" by (blast dest: accs_mono)
    thus "t\<in>ta_lang completeTA" using QI 
      by (auto simp add: ta_lang_def completeTA_def)
  next
    fix t
    assume A: "t\<in>ta_lang completeTA"
    then obtain qi where 
      QI: "qi\<in>Qi" and
      ACCS: "accs \<delta>complete t (Some qi)" 
      by (auto simp add: ta_lang_def completeTA_def)
    moreover
    {
      fix qi
      have "\<lbrakk> accs \<delta>complete t (Some qi) \<rbrakk> \<Longrightarrow> accs \<delta> t qi"
        unfolding accs_laz
      proof (induct \<delta>\<equiv>\<delta>complete t q\<equiv>"Some qi"
                    arbitrary: qi
                    rule: accs_laz.induct[case_names step])
        case (step f qs ts qi)
        hence I:
          "((Some qi) \<rightarrow> f qs) \<in> \<delta>complete"
          "list_all_zip (accs_laz \<delta>complete) ts qs"
          "list_all_zip (\<lambda>t q. (\<forall>qo. q=Some qo \<longrightarrow> accs_laz \<delta> t qo)) ts qs"
          by auto
        from I(1) have "((Some qi) \<rightarrow> f qs) \<in> remap_rule Some`\<delta>"
          by (unfold \<delta>complete_def) auto
        then obtain qso where 
          RULE: "(qi \<rightarrow> f qso)\<in>\<delta>" and
          QSF: "qs=map Some qso"
          apply (auto)
          apply (case_tac x)
          apply auto
          done
        from I(3) QSF have ACCS: "list_all_zip (accs_laz \<delta>) ts qso"
          by (auto simp add: list_all_zip_alt)
        from accs_laz.intros[OF RULE ACCS] show ?case .
      qed
    }
    ultimately have "accs \<delta> t qi" by blast
    thus "t\<in>ta_lang TA" using QI by (auto simp add: ta_lang_def)
  qed
        
  lemmas completeTA_correct = completeTA_is_ta completeTA_lang
end

subsubsection "Complement"
text \<open>
  A deterministic, complete tree automaton can be transformed into an automaton
  accepting the complement language by complementing its initial states.
\<close>

context complete_tree_automaton
begin

    \<comment> \<open>Complement automaton, i.e. that accepts exactly the 
        trees not accepted by this automaton\<close>
  definition "complementTA == \<lparr>
    ta_initial = Q - Qi,
    ta_rules = \<delta> \<rparr>"

    
  lemma cta_rules[simp]: "ta_rules complementTA = \<delta>" 
    by (auto simp add: complementTA_def)

  theorem complementTA_correct:
    "ta_lang complementTA = ranked_trees A - ta_lang TA" (is ?T1)
    "complete_tree_automaton complementTA A" (is ?T2)
  proof -
    show ?T1
      apply (unfold ta_lang_def complementTA_def)
      apply (force intro: accs_is_ranked dest: accs_unique label_all)
      done

    have QSS: "!!q. q\<in>ta_rstates complementTA \<Longrightarrow> q\<in>Q"
      by (auto simp add: complementTA_def ta_rstates_def)

    show ?T2
      apply (unfold_locales)
      apply (unfold complementTA_def)[4]
      apply (auto simp add: deterministic ranked 
                  intro: complete QSS)
      done
  qed

end


subsection "Regular Tree Languages"
subsubsection "Definitions"

  \<comment> \<open>Regular languages over alphabet @{text A}\<close>
definition regular_languages :: "('L \<rightharpoonup> nat) \<Rightarrow> 'L tree set set" 
  where "regular_languages A == 
    { ta_lang TA | (TA::(nat,'L) tree_automaton_rec). 
                          ranked_tree_automaton TA A }"


lemma rtlE:
  fixes L :: "'L tree set"
  assumes A: "L\<in>regular_languages A"
  obtains TA::"(nat,'L) tree_automaton_rec" where 
    "L=ta_lang TA"
    "ranked_tree_automaton TA A"
  using A that
  by (unfold regular_languages_def) blast

context ranked_tree_automaton
begin

  lemma (in ranked_tree_automaton) rtlI[simp]:
    shows "ta_lang TA \<in> regular_languages A"
  proof -
    \<comment> \<open>Obtain injective mapping from the finite set of states to the 
        natural numbers\<close>
    from finite_imp_inj_to_nat_seg[OF finite_states] obtain f :: "'Q \<Rightarrow> nat" 
      where INJMAP: "inj_on f (ta_rstates TA)" by blast
    \<comment> \<open>Remap automaton. The language remains the same.\<close>
    from remap_lang[OF INJMAP] have LE: "ta_lang (ta_remap f TA) = ta_lang TA" .
    moreover have "ranked_tree_automaton (ta_remap f TA) A" ..
    ultimately show ?thesis by (auto simp add: regular_languages_def)
  qed

  text \<open>
    It is sometimes more handy to obtain a complete, deterministic tree automaton
    accepting a given regular language.
\<close>
  theorem obtain_complete:
    obtains TAC::"('Q set option,'L) tree_automaton_rec" where
    "ta_lang TAC = ta_lang TA"
    "complete_tree_automaton TAC A"
  proof -
    from detTA_correct have 
      DT: "det_tree_automaton detTA A" and
      [simp]: "ta_lang detTA = ta_lang TA"
      by simp_all
    
    interpret dt: det_tree_automaton detTA A using DT .
    
    from dt.completeTA_correct have G: 
      "ta_lang (det_tree_automaton.completeTA detTA A) = ta_lang TA"
      "complete_tree_automaton (det_tree_automaton.completeTA detTA A) A"
      by simp_all
    thus ?thesis by (blast intro: that)
  qed

end


lemma rtlE_complete:
  fixes L :: "'L tree set"
  assumes A: "L\<in>regular_languages A"
  obtains TA::"(nat,'L) tree_automaton_rec" where 
    "L=ta_lang TA"
    "complete_tree_automaton TA A"
proof -
  from rtlE[OF A] obtain TA :: "(nat,'L) tree_automaton_rec" where
    [simp, symmetric]: "L = ta_lang TA" and
        RT: "ranked_tree_automaton TA A" .

  interpret ta: ranked_tree_automaton TA A using RT .

  obtain TAC :: "(nat set option,'L) tree_automaton_rec" 
    where [simp]: "ta_lang TAC = L" and CT: "complete_tree_automaton TAC A"
    by (rule_tac ta.obtain_complete) auto
  
  interpret tac: complete_tree_automaton TAC A using CT .

  \<comment> \<open>Obtain injective mapping from the finite set of states to the 
      natural numbers\<close>
  from finite_imp_inj_to_nat_seg[OF tac.finite_states] 
  obtain f :: "nat set option \<Rightarrow> nat" where
    INJMAP: "inj_on f (ta_rstates TAC)" by blast
  \<comment> \<open>Remap automaton. The language remains the same.\<close>
  from tac.remap_lang[OF INJMAP] have LE: "ta_lang (ta_remap f TAC) = L" 
    by simp
  have "complete_tree_automaton (ta_remap f TAC) A" 
    using tac.remap_cta[OF INJMAP] .
  thus ?thesis by (rule_tac that[OF LE[symmetric]])
qed

subsubsection "Closure Properties"
text \<open>
  In this section, we derive the standard closure properties of regular languages,
  i.e. that regular languages are closed under union, intersection, complement, 
  and difference, as well as that the empty and the universal language are
  regular.
  
  Note that we do not formalize homomorphisms or tree transducers here.
\<close>
  
theorem (in finite_alphabet) rtl_empty[simp, intro!]: "{} \<in> regular_languages A"
  by (rule ranked_tree_automaton.rtlI[OF ta_empty_rta, simplified])


theorem rtl_union_closed: 
  "\<lbrakk> L1\<in>regular_languages A; L2\<in>regular_languages A \<rbrakk> 
    \<Longrightarrow> L1\<union>L2 \<in> regular_languages A"
proof (elim rtlE)
  fix TA1 TA2
  assume TA[simp]: "ranked_tree_automaton TA1 A" "ranked_tree_automaton TA2 A"
    and [simp]: "L1=ta_lang TA1" "L2=ta_lang TA2"


  interpret ta1: ranked_tree_automaton TA1 A by simp
  interpret ta2: ranked_tree_automaton TA2 A by simp

  have "ta_lang (ta_union_wrap TA1 TA2) = ta_lang TA1 \<union> ta_lang TA2" 
    apply (rule ta_union_wrap_correct)
    by unfold_locales
  with ranked_tree_automaton.rtlI[OF ta_union_wrap_rta[OF TA]] show ?thesis
    by (simp)

qed
   
theorem rtl_inter_closed: 
  "\<lbrakk>L1\<in>regular_languages A; L2\<in>regular_languages A\<rbrakk> \<Longrightarrow> 
    L1\<inter>L2 \<in> regular_languages A" 
proof (elim rtlE, goal_cases)
  case (1 TA1 TA2)
  with ta_prod_correct[of TA1 TA2] ta_prod_rta[of TA1 A TA2] have 
     L: "ta_lang (ta_prod TA1 TA2) = L1\<inter>L2"  and
     A: "ranked_tree_automaton (ta_prod TA1 TA2) A"
    by (simp_all add: ranked_tree_automaton.axioms)
  show ?thesis using ranked_tree_automaton.rtlI[OF A]
    by (simp add: L)
qed

theorem rtl_complement_closed:
  "L\<in>regular_languages A \<Longrightarrow> ranked_trees A - L \<in> regular_languages A"
proof (elim rtlE_complete, goal_cases)
  case prems: (1 TA)
  then interpret ta: complete_tree_automaton TA A by simp
  
  from ta.complementTA_correct have
    [simp]: "ta_lang (ta.complementTA) = ranked_trees A - ta_lang TA" and
    CTA: "complete_tree_automaton ta.complementTA A" by auto
  interpret cta: complete_tree_automaton ta.complementTA A using CTA .
  
  from cta.rtlI prems(1) show ?case by simp
qed

theorem (in finite_alphabet) rtl_univ: 
  "ranked_trees A \<in> regular_languages A"
  using rtl_complement_closed[OF rtl_empty] 
  by simp

theorem rtl_diff_closed:
  fixes L1 :: "'L tree set"
  assumes A[simp]: "L1 \<in> regular_languages A" "L2\<in>regular_languages A" 
  shows "L1-L2 \<in> regular_languages A"
proof -
  from rtlE[OF A(1)] obtain TA1::"(nat,'L) tree_automaton_rec" where
    L1: "L1=ta_lang TA1" and
    RT1: "ranked_tree_automaton TA1 A"
    .
  from rtlE[OF A(2)] obtain TA2::"(nat,'L) tree_automaton_rec" where
    L2: "L2=ta_lang TA2" and
    RT2: "ranked_tree_automaton TA2 A"
    .

  interpret ta1: ranked_tree_automaton TA1 A using RT1 .
  interpret ta2: ranked_tree_automaton TA2 A using RT2 .

  from ta1.lang_is_ranked have ALT: "L1-L2 = L1 \<inter> (ranked_trees A - L2)"
    by (auto simp add: L1 L2)

  show ?thesis
    unfolding ALT
    by (simp add: rtl_complement_closed rtl_inter_closed)
qed


lemmas rtl_closed = finite_alphabet.rtl_empty finite_alphabet.rtl_univ 
  rtl_complement_closed
  rtl_inter_closed rtl_union_closed rtl_diff_closed


end
