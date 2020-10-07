chapter \<open>Finite Automata using the Hereditarily Finite Sets\<close>

theory Finite_Automata_HF imports
  HereditarilyFinite.Ordinal
  "Regular-Sets.Regular_Exp"
begin

text\<open>Finite Automata, both deterministic and non-deterministic, for regular languages.
  The Myhill-Nerode Theorem. Closure under intersection, concatenation, etc.
  Regular expressions define regular languages. Closure under reversal;
  the powerset construction mapping NFAs to DFAs. Left and right languages; minimal DFAs.
  Brzozowski's minimization algorithm. Uniqueness up to isomorphism of minimal DFAs.\<close>

section\<open>Deterministic Finite Automata\<close>

text\<open>Right invariance is the key property for equivalence relations on states of DFAs.\<close>
definition right_invariant :: "('a list \<times> 'a list) set \<Rightarrow> bool" where
  "right_invariant r \<equiv> (\<forall>u v w. (u,v) \<in> r \<longrightarrow> (u@w, v@w) \<in> r)"

subsection\<open>Basic Definitions\<close>

text\<open>First, the record for DFAs\<close>
record 'a dfa = states :: "hf set"
                init   :: "hf"
                final  :: "hf set"
                nxt    :: "hf \<Rightarrow> 'a \<Rightarrow> hf"

locale dfa =
  fixes M :: "'a dfa"
  assumes init [simp]: "init M \<in> states M"
      and final:       "final M \<subseteq> states M"
      and nxt:         "\<And>q x. q \<in> states M \<Longrightarrow> nxt M q x \<in> states M"
      and finite:      "finite (states M)"
begin

lemma finite_final [simp]: "finite (final M)"
  using final finite_subset finite by blast

text\<open>Transition function for a given starting state and word.\<close>
primrec nextl :: "[hf, 'a list] \<Rightarrow> hf" where
    "nextl q []     = q"
  | "nextl q (x#xs) = nextl (nxt M q x) xs"

definition language :: "'a list set"  where
  "language \<equiv> {xs. nextl (init M) xs \<in> final M}"

text\<open>The left language WRT a state q is the set of words that lead to q.\<close>
definition left_lang :: "hf \<Rightarrow> 'a list set"  where
  "left_lang q \<equiv> {u. nextl (init M) u = q}"

text\<open>Part of Prop 1 of
  Jean-Marc Champarnaud, A. Khorsi and T. Paranthoën,
  Split and join for minimizing: Brzozowski's algorithm,
  Prague Stringology Conference 2002\<close>
lemma left_lang_disjoint:
  "q1 \<noteq> q2 \<Longrightarrow> left_lang q1 \<inter> left_lang q2 = {}"
  unfolding left_lang_def by auto

text\<open>The right language WRT a state q is the set of words that go from q to F.\<close>
definition right_lang :: "hf \<Rightarrow> 'a list set"  where
  "right_lang q \<equiv> {u. nextl q u \<in> final M}"

lemma language_eq_right_lang: "language = right_lang (init M)"
  using language_def right_lang_def by auto

lemma nextl_app: "nextl q (xs@ys) = nextl (nextl q xs) ys"
  by (induct xs arbitrary: q) auto

lemma nextl_snoc [simp]: "nextl q (xs@[x]) = nxt M (nextl q xs) x"
  by (simp add: nextl_app)

lemma nextl_state: "q \<in> states M \<Longrightarrow> nextl q xs \<in> states M"
  by (induct xs arbitrary: q) (auto simp: nxt)

lemma nextl_init_state [simp]: "nextl (init M) xs \<in> states M"
  by (simp add: nextl_state)

subsection\<open>An Equivalence Relation on States\<close>

text\<open>Two words are equivalent if they take the machine to the same state.
  See e.g. Kozen, Automata and Computability, Springer, 1997, page 90.\<close>


text\<open>This relation asks, do @{term u} and @{term v} lead to the same state?\<close>
definition eq_nextl :: "('a list \<times> 'a list) set" where
  "eq_nextl \<equiv> {(u,v). nextl (init M) u = nextl (init M) v}"

lemma equiv_eq_nextl: "equiv UNIV eq_nextl"
  by (simp add: equivI refl_on_def sym_def trans_def eq_nextl_def)

lemma right_invariant_eq_nextl: "right_invariant eq_nextl"
  by (auto simp: right_invariant_def eq_nextl_def nextl_app)

lemma range_nextl: "range (nextl (init M)) \<subseteq> states M"
using hmem_def nextl_init_state by auto

lemma eq_nextl_class_in_left_lang_im: "eq_nextl `` {u} \<in> left_lang ` states M"
  apply (rule rev_image_eqI [of "nextl (init M) u"])
  apply (auto simp: eq_nextl_def left_lang_def)
  done

lemma language_eq_nextl: "language = eq_nextl `` (\<Union>q \<in> final M. left_lang q)"
  by (auto simp: language_def eq_nextl_def left_lang_def hmem_def)

lemma finite_index_eq_nextl: "finite (UNIV // eq_nextl)"
  apply (rule finite_surj [where f = left_lang, OF finite])
  apply (auto simp: quotient_def eq_nextl_class_in_left_lang_im)
  done

lemma index_eq_nextl_le_states: "card (UNIV // eq_nextl) \<le> card (states M)"
  apply (rule surj_card_le [where f = left_lang, OF finite])
  apply (auto simp: quotient_def eq_nextl_class_in_left_lang_im)
  done

subsection \<open>Minimisation via Accessibility\<close>

definition accessible :: "hf set"  where
  "accessible \<equiv> {q. left_lang q \<noteq> {}}"

lemma accessible_imp_states: "q \<in> accessible \<Longrightarrow> q \<in> states M"
  by (auto simp: accessible_def left_lang_def)

lemma nxt_accessible: "q \<in> accessible \<Longrightarrow> nxt M q a \<in> accessible"
  by (auto simp: image_iff accessible_def left_lang_def) (metis nextl.simps nextl_app)

lemma inj_on_left_lang: "inj_on left_lang accessible"
  by (auto simp: inj_on_def left_lang_def accessible_def)

definition path_to :: "hf \<Rightarrow> 'a list"  where
  "path_to q \<equiv> SOME u. u \<in> left_lang q"

lemma path_to_left_lang: "q \<in> accessible \<Longrightarrow> path_to q \<in> left_lang q"
  unfolding path_to_def left_lang_def accessible_def
  by (auto intro: someI)

lemma nextl_path_to: "q \<in> accessible \<Longrightarrow> nextl (dfa.init M) (path_to q) = q"
  using path_to_left_lang  unfolding left_lang_def
  by auto

definition Accessible_dfa :: "'a dfa" where
  "Accessible_dfa = \<lparr>dfa.states = accessible,
                     init  = init M,
                     final = final M \<inter> accessible,
                     nxt   = nxt M\<rparr>"

lemma states_Accessible_dfa [simp]: "states Accessible_dfa = accessible"
  by (simp add: Accessible_dfa_def)

lemma init_Accessible_dfa [simp]: "init Accessible_dfa = init M"
  by (simp add: Accessible_dfa_def)

lemma final_Accessible_dfa [simp]: "final Accessible_dfa = final M \<inter> accessible"
  by (simp add: Accessible_dfa_def)

lemma nxt_Accessible_dfa [simp]: "nxt Accessible_dfa = nxt M"
  by (simp add: Accessible_dfa_def)

interpretation Accessible: dfa Accessible_dfa
proof unfold_locales
  show "init Accessible_dfa \<in> states Accessible_dfa"
    by (auto simp: accessible_def left_lang_def) (metis nextl.simps(1))
next
  show "final Accessible_dfa \<subseteq> states Accessible_dfa"
    by (auto simp: accessible_imp_states)
next
  fix q a
  show "q \<in> states Accessible_dfa \<Longrightarrow> nxt Accessible_dfa q a \<in> states Accessible_dfa"
    by (auto simp: nxt nxt_accessible)
next
  show "finite (states Accessible_dfa)"
    by (auto intro: accessible_imp_states finite_subset finite)
qed

lemma dfa_Accessible: "dfa Accessible_dfa"
  by unfold_locales

lemma nextl_Accessible_dfa [simp]:
     "q \<in> accessible \<Longrightarrow> Accessible.nextl q u = nextl q u"
  by (induct u rule: List.rev_induct, auto)

lemma init_Accessible: "init M \<in> accessible"
  using dfa.init dfa_Accessible by force

declare nextl_Accessible_dfa [OF init_Accessible, simp]

lemma Accessible_left_lang_eq [simp]: "Accessible.left_lang q = left_lang q"
  by (auto simp: Accessible.left_lang_def left_lang_def)

lemma Accessible_right_lang_eq [simp]:
  "q \<in> accessible \<Longrightarrow> Accessible.right_lang q = right_lang q"
  by (auto simp: Accessible.right_lang_def right_lang_def accessible_def left_lang_def nextl_app [symmetric])

lemma Accessible_language [simp]: "Accessible.language = language"
  by (simp add: Accessible.language_eq_right_lang language_eq_right_lang
                Accessible_right_lang_eq [OF init_Accessible])

lemma Accessible_accessible [simp]: "Accessible.accessible = accessible"
  using Accessible.accessible_def accessible_def by auto


lemma left_lang_half:
  assumes sb: "\<Union>(left_lang ` qs1) \<subseteq> \<Union>(left_lang ` qs2)"
      and ne: "\<And>x. x \<in> qs1 \<Longrightarrow> left_lang x \<noteq> {}"
    shows "qs1 \<subseteq> qs2"
proof
  fix x
  assume x: "x \<in> qs1"
  with ne obtain y where y: "y \<in> left_lang x"
    by blast
  then have "y \<in> \<Union>(left_lang ` qs2)"
    using x sb [THEN subsetD]
    by blast
  then show "x \<in> qs2"
    by (metis UN_E disjoint_iff_not_equal left_lang_disjoint y)
qed

lemma left_lang_UN:
     "\<lbrakk>\<Union>(left_lang ` qs1) = \<Union>(left_lang ` qs2); qs1 \<union> qs2 \<subseteq> accessible\<rbrakk>
      \<Longrightarrow> qs1 = qs2"
  apply (rule equalityI [OF _ dfa.left_lang_half [OF dfa_Accessible]])
  apply (rule dfa.left_lang_half [OF dfa_Accessible], auto simp: accessible_def)
  done

definition minimal where
  "minimal \<equiv> accessible = states M \<and> inj_on right_lang (dfa.states M)"



subsection\<open>An Equivalence Relation on States\<close>

text\<open>Collapsing map on states. Two states are equivalent if they yield identical outcomes\<close>
definition eq_right_lang :: "(hf \<times> hf) set" where
  "eq_right_lang \<equiv> {(u,v). u \<in> states M \<and> v \<in> states M \<and> right_lang u = right_lang v}"

lemma equiv_eq_right_lang: "equiv (states M) eq_right_lang"
  by (auto simp: equiv_def refl_on_def sym_def trans_def eq_right_lang_def)

lemma eq_right_lang_finite_index: "finite (states M // eq_right_lang)"
  by (metis finite_imageI finite proj_image)

definition Collapse_dfa :: "'a dfa" where
  "Collapse_dfa = \<lparr>dfa.states = HF ` (states M // eq_right_lang),
                   init       = HF (eq_right_lang `` {init M}),
                   final      = {HF (eq_right_lang `` {q}) | q. q \<in> final M},
                   nxt        = \<lambda>Q x. HF (\<Union>q \<in> hfset Q. eq_right_lang `` {nxt M q x})\<rparr>"

lemma nxt_Collapse_resp: "(\<lambda>q. eq_right_lang `` {nxt M q x}) respects eq_right_lang"
  by (auto simp: nextl.simps [symmetric] congruent_def eq_right_lang_def nxt right_lang_def
           simp del: nextl.simps)

lemma finite_Collapse_state: "Q \<in> states M // eq_right_lang \<Longrightarrow> finite Q"
  by (meson equiv_eq_right_lang finite_subset in_quotient_imp_subset finite)

interpretation Collapse: dfa Collapse_dfa
proof unfold_locales
  show "dfa.init Collapse_dfa \<in> dfa.states Collapse_dfa"
    by (simp add: Collapse_dfa_def quotientI)
next
  show "dfa.final Collapse_dfa \<subseteq> dfa.states Collapse_dfa"
    using final
    by (auto simp: Collapse_dfa_def quotientI)
next
  fix q a
  show "q \<in> dfa.states Collapse_dfa \<Longrightarrow> dfa.nxt Collapse_dfa q a \<in> dfa.states Collapse_dfa"
    by (auto simp: Collapse_dfa_def nxt quotientI finite_Collapse_state
                   UN_equiv_class_type [OF equiv_eq_right_lang nxt_Collapse_resp])
next
  show "finite (dfa.states Collapse_dfa)"
    by (simp add: Collapse_dfa_def eq_right_lang_finite_index)
qed

corollary dfa_Collapse: "dfa Collapse_dfa"
  by unfold_locales

lemma nextl_Collapse_dfa:
     "Q = HF (eq_right_lang `` {q}) \<Longrightarrow> Q \<in> dfa.states Collapse_dfa \<Longrightarrow>
      q \<in> states M \<Longrightarrow>
             Collapse.nextl Q u = HF (eq_right_lang `` {nextl q u})"
  apply (induct u rule: List.rev_induct, auto)
  apply (simp add: Collapse_dfa_def)
  apply (subst inj_on_eq_iff [OF inj_on_HF])
  apply (rule UN_equiv_class_type [OF equiv_eq_right_lang nxt_Collapse_resp])
  apply (auto simp: nxt quotientI finite_Collapse_state nextl_state)
  apply (force simp add: nextl.simps [symmetric]  eq_right_lang_def nxt right_lang_def
               simp del: nextl.simps)
  apply (metis equiv_class_self equiv_eq_right_lang nextl_state)
  done

lemma ext_language_Collapse_dfa:
     "u \<in> Collapse.language \<longleftrightarrow> u \<in> language"
  apply (simp add: Collapse.language_def language_def)
  apply (subst nextl_Collapse_dfa)
  apply (auto simp: Collapse_dfa_def)
  using final [THEN subsetD] init
  apply (auto simp: quotientI  inj_on_eq_iff [OF inj_on_HF] finite_Collapse_state
                    UN_equiv_class_type [OF equiv_eq_right_lang nxt_Collapse_resp])
  apply (drule eq_equiv_class [OF _ equiv_eq_right_lang])
  apply (auto simp: eq_right_lang_def right_lang_def)
  apply (metis mem_Collect_eq nextl.simps(1))
  done

theorem language_Collapse_dfa:
     "Collapse.language = language"
  by (simp add: ext_language_Collapse_dfa subset_antisym subset_iff)

lemma card_Collapse_dfa: "card (states M // eq_right_lang) \<le> card (states M)"
  by (metis card_image_le finite proj_image)

end


subsection \<open>Isomorphisms Between DFAs\<close>

locale dfa_isomorphism = M: dfa M + N: dfa N for M :: "'a dfa" and N :: "'a dfa" +
  fixes h :: "hf \<Rightarrow> hf"
  assumes h: "bij_betw h (states M) (states N)"
      and init  [simp]: "h (init M) = init N"
      and final [simp]: "h ` final M = final N"
      and nxt   [simp]: "\<And>q x. q \<in> states M \<Longrightarrow> h (nxt M q x) = nxt N (h q) x"

begin

lemma nextl [simp]: "q \<in> states M \<Longrightarrow> h (M.nextl q u) = N.nextl (h q) u"
  by (induct u rule: List.rev_induct) (auto simp: M.nextl_state)

theorem language: "M.language = N.language"
proof (rule set_eqI)
  fix u
  have "M.nextl (init M) u \<in> final M \<longleftrightarrow> h (M.nextl (init M) u) \<in> h ` final M"
    by (subst inj_on_image_mem_iff [OF bij_betw_imp_inj_on [OF h] _ M.final]) (auto)
  also have "... \<longleftrightarrow> N.nextl (init N) u \<in> final N"
    by simp
  finally show "u \<in> M.language \<longleftrightarrow> u \<in> dfa.language N"
    by (simp add: M.language_def N.language_def)
qed

lemma nxt_inv_into: "q \<in> states N \<Longrightarrow> nxt N q x = h (nxt M (inv_into (states M) h q) x)"
  apply (subst nxt)
  apply (metis bij_betw_def h inv_into_into)
  apply (metis bij_betw_inv_into_right h)
  done

lemma sym: "dfa_isomorphism N M (inv_into (states M) h)"
  apply unfold_locales
  apply (metis bij_betw_inv_into h)
  apply (metis M.init bij_betw_imp_inj_on h inv_into_f_eq init)
  apply (metis M.final bij_betw_def bij_betw_inv_into_subset h final)
  apply (simp add: nxt_inv_into)
  apply (metis M.nxt bij_betw_def h inv_into_f_eq inv_into_into)
  done

lemma trans: "dfa_isomorphism N N' h' \<Longrightarrow> dfa_isomorphism M N' (h' o h)"
  apply (auto simp: dfa_isomorphism_def dfa_isomorphism_axioms_def)
      apply unfold_locales
     apply (metis bij_betw_comp_iff h)
    apply (metis imageI final)
   apply (simp only: final [symmetric] image_comp) apply simp
  apply (metis bij_betw_def h image_iff)
  done

end

section\<open>The Myhill-Nerode theorem: three characterisations of a regular language\<close>

definition regular :: "'a list set \<Rightarrow> bool" where
  "regular L \<equiv> \<exists>M. dfa M \<and> dfa.language M = L"

definition MyhillNerode :: "'a list set \<Rightarrow> ('a list * 'a list) set \<Rightarrow> bool" where
  "MyhillNerode L R \<equiv> equiv UNIV R \<and> right_invariant R \<and> finite (UNIV//R) \<and> (\<exists>A. L = R``A)"

text\<open>This relation can be seen as an abstraction of the idea, do @{term u} and @{term v}
  lead to the same state?  Compare with @{term eq_nextl}, which does precisely that.\<close>
definition eq_app_right :: "'a list set \<Rightarrow> ('a list * 'a list) set" where
  "eq_app_right L \<equiv> {(u,v). \<forall>w. u@w \<in> L \<longleftrightarrow> v@w \<in> L}"

lemma equiv_eq_app_right: "equiv UNIV (eq_app_right L)"
  by (simp add: equivI refl_on_def sym_def trans_def eq_app_right_def)

lemma right_invariant_eq_app_right: "right_invariant (eq_app_right L)"
  by (simp add: right_invariant_def eq_app_right_def)

lemma eq_app_right_eq: "eq_app_right L `` L = L"
  unfolding eq_app_right_def
  by auto (metis append_Nil2)

lemma MN_eq_app_right:
     "finite (UNIV // eq_app_right L) \<Longrightarrow> MyhillNerode L (eq_app_right L)"
  unfolding MyhillNerode_def
  using eq_app_right_eq
  by (auto simp: equiv_eq_app_right right_invariant_eq_app_right)

lemma MN_refines: "\<lbrakk>MyhillNerode L R; (x,y) \<in> R\<rbrakk> \<Longrightarrow> x \<in> L \<longleftrightarrow> y \<in> L"
  unfolding equiv_def trans_def sym_def MyhillNerode_def
  by blast

lemma MN_refines_eq_app_right: "MyhillNerode L R \<Longrightarrow> R \<subseteq> eq_app_right L"
  unfolding eq_app_right_def MyhillNerode_def right_invariant_def equiv_def trans_def sym_def
  by blast

text\<open>Step 1 in the circle of implications: every regular language @{term L} is recognised
  by some Myhill-Nerode relation, @{term R}\<close>
context dfa
begin
  lemma MN_eq_nextl: "MyhillNerode language eq_nextl"
    unfolding MyhillNerode_def
    using language_eq_nextl
    by (blast intro: equiv_eq_nextl right_invariant_eq_nextl finite_index_eq_nextl)

  corollary eq_nextl_refines_eq_app_right: "eq_nextl \<subseteq> eq_app_right language"
    by (simp add: MN_eq_nextl MN_refines_eq_app_right)

  lemma index_le_index_eq_nextl:
       "card (UNIV // eq_app_right language) \<le> card (UNIV // eq_nextl)"
    by (metis finite_refines_card_le finite_index_eq_nextl equiv_eq_nextl equiv_eq_app_right
              eq_nextl_refines_eq_app_right)

  text\<open>A specific lower bound on the number of states in a DFA\<close>
  lemma index_eq_app_right_lower:
       "card (UNIV // eq_app_right language) \<le> card (states M)"
    using index_eq_nextl_le_states index_le_index_eq_nextl order_trans by blast
end

lemma L1_2: "regular L \<Longrightarrow> \<exists>R. MyhillNerode L R"
  by (metis dfa.MN_eq_nextl regular_def)

text\<open>Step 2: every Myhill-Nerode relation @{term R} for the language @{term L}
  can be mapped to the canonical M-N relation.\<close>
lemma L2_3:
  assumes "MyhillNerode L R"
  obtains "finite (UNIV // eq_app_right L)"
          "card (UNIV // eq_app_right L) \<le> card (UNIV // R)"
by (meson assms MN_refines_eq_app_right MyhillNerode_def equiv_eq_app_right finite_refines_finite finite_refines_card_le)

text \<open>Working towards step 3.  Also, every Myhill-Nerode relation @{term R} for @{term L}
  can be mapped to a machine. The locale below constructs such a DFA.\<close>

locale MyhillNerode_dfa =
  fixes L :: "'a list set" and R :: "('a list * 'a list) set"
    and A :: "'a list set" and n :: nat and h :: "'a list set \<Rightarrow> hf"
  assumes eqR: "equiv UNIV R"
      and riR: "right_invariant R"
      and L:   "L = R``A"
      and h:   "bij_betw h (UNIV//R) (hfset (ord_of n))"
begin

  lemma injh: "inj_on h (UNIV//R)"
    using h bij_betw_imp_inj_on by blast

  definition hinv ("h\<^sup>-\<^sup>1") where "h\<^sup>-\<^sup>1 \<equiv> inv_into (UNIV//R) h"

  lemma finix: "finite (UNIV//R)"
    using h bij_betw_finite finite_hfset by blast

  definition DFA :: "'a dfa" where
    "DFA = \<lparr>states = h ` (UNIV//R),
            init  = h (R `` {[]}),
            final = {h (R `` {u}) | u. u \<in> A},
            nxt   = \<lambda>q x. h (\<Union>u \<in> h\<^sup>-\<^sup>1 q. R `` {u@[x]})\<rparr>"

  lemma resp: "\<And>x. (\<lambda>u. R `` {u @ [x]}) respects R"
    using riR
    by (auto simp: congruent_def right_invariant_def intro!: equiv_class_eq [OF eqR])

  lemma dfa: "dfa DFA"
    apply (auto simp: dfa_def DFA_def quotientI finix)
    apply (subst inj_on_image_mem_iff [OF injh])
    apply (rule UN_equiv_class_type [OF eqR resp])
    apply (auto simp: injh DFA_def hinv_def quotientI)
    done

  interpretation MN: dfa DFA
    by (simp add: dfa)

  lemma MyhillNerode: "MyhillNerode L R"
    using L
    by (auto simp: MyhillNerode_def eqR riR finix)

  lemma R_iff: "(\<exists>x\<in>L. (u, x) \<in> R) = (u \<in> L)"
    using MN_refines MyhillNerode eqR eq_equiv_class_iff
    by fastforce

  lemma nextl: "MN.nextl (init DFA) u = h (R `` {u})"
    apply (induct u rule: List.rev_induct, auto)
    apply (simp_all add: DFA_def hinv_def injh quotientI UN_equiv_class [OF eqR resp])
    done

  lemma language: "MN.language = L"
  proof -
   { fix u
    have "u \<in> MN.language \<longleftrightarrow> u \<in> L"
      using L eqR
      apply (simp add: MN.language_def nextl)
      apply (simp add: DFA_def inj_on_eq_iff [OF injh] eq_equiv_class_iff [OF eqR] quotientI)
      apply (auto simp: equiv_def sym_def)
      done
   } then show ?thesis
       by blast
  qed

  lemma card_states: "card (states DFA) = card (UNIV // R)"
    using h
    by (simp add: DFA_def bij_betw_def) (metis card_image)

end


theorem MN_imp_dfa:
  assumes "MyhillNerode L R"
  obtains M where "dfa M" "dfa.language M = L" "card (states M) = card (UNIV//R)"
proof -
  from assms obtain A
    where eqR: "equiv UNIV R"
      and riR: "right_invariant R"
      and finix: "finite (UNIV//R)"
      and L: "L = R``A"
    by (auto simp: MyhillNerode_def)
  let ?n = "card (UNIV//R)"
  from ex_bij_betw_finite_nat [OF finix]
  obtain h where h: "bij_betw h (UNIV//R) (hfset (ord_of ?n))"
    using bij_betw_ord_ofI by blast
  interpret MN: MyhillNerode_dfa L R A "?n" h
    by (simp add: MyhillNerode_dfa_def eqR riR L h)
  show ?thesis
    by (auto simp: MN.language intro: that MN.dfa MN.language MN.card_states)
  qed

corollary MN_imp_regular:
  assumes "MyhillNerode L R"  shows "regular L"
  using MN_imp_dfa [OF assms] unfolding regular_def
  by auto

corollary eq_app_right_finite_index_imp_dfa:
  assumes "finite (UNIV // eq_app_right L)"
  obtains M where
    "dfa M" "dfa.language M = L" "card (states M) = card (UNIV // eq_app_right L)"
  using MN_eq_app_right MN_imp_dfa assms by blast

text\<open>Step 3\<close>
corollary L3_1: "finite (UNIV // eq_app_right L) \<Longrightarrow> regular L"
  using eq_app_right_finite_index_imp_dfa regular_def by blast


section\<open>Non-Deterministic Finite Automata\<close>

text\<open>These NFAs may include epsilon-transitions and multiple start states.\<close>

subsection\<open>Basic Definitions\<close>

record 'a nfa = states :: "hf set"
                init   :: "hf set"
                final  :: "hf set"
                nxt    :: "hf \<Rightarrow> 'a \<Rightarrow> hf set"
                eps    :: "(hf * hf) set"

locale nfa =
  fixes M :: "'a nfa"
  assumes init: "init M \<subseteq> states M"
      and final: "final M \<subseteq> states M"
      and nxt:   "\<And>q x. q \<in> states M \<Longrightarrow> nxt M q x \<subseteq> states M"
      and finite: "finite (states M)"
begin

lemma subset_states_finite [intro,simp]: "Q \<subseteq> states M \<Longrightarrow> finite Q"
  by (simp add: finite_subset finite)

definition epsclo :: "hf set \<Rightarrow> hf set" where
  "epsclo Q \<equiv> states M \<inter> (\<Union>q\<in>Q. {q'. (q,q') \<in> (eps M)\<^sup>*})"

lemma epsclo_eq_Image: "epsclo Q = states M \<inter> (eps M)\<^sup>* `` Q"
  by (auto simp: epsclo_def)

lemma epsclo_empty [simp]: "epsclo {} = {}"
  by (auto simp: epsclo_def)

lemma epsclo_idem [simp]: "epsclo (epsclo Q) = epsclo Q"
  by (auto simp: epsclo_def)

lemma epsclo_increasing: "Q \<inter> states M \<subseteq> epsclo Q"
  by (auto simp: epsclo_def)

lemma epsclo_Un [simp]: "epsclo (Q1 \<union> Q2) = epsclo Q1 \<union> epsclo Q2"
  by (auto simp: epsclo_def)

lemma epsclo_UN [simp]: "epsclo (\<Union>x\<in>A. B x) = (\<Union>x\<in>A. epsclo (B x))"
  by (auto simp: epsclo_def)

lemma epsclo_subset [simp]: "epsclo Q \<subseteq> states M"
  by (auto simp: epsclo_def)

lemma epsclo_trivial [simp]: "eps M \<subseteq> Q \<times> Q \<Longrightarrow> epsclo Q = states M \<inter> Q"
  by (auto simp: epsclo_def elim: rtranclE)

lemma epsclo_mono: "Q' \<subseteq> Q \<Longrightarrow> epsclo Q' \<subseteq> epsclo Q"
  by (auto simp: epsclo_def)

lemma finite_epsclo [simp]: "finite (epsclo Q)"
  using epsclo_subset finite_subset finite by blast

lemma finite_final: "finite (final M)"
  using final finite_subset finite by blast

lemma finite_nxt: "q \<in> states M \<Longrightarrow> finite (nxt M q x)"
  by (metis finite_subset finite nxt)

text\<open>Transition function for a given starting state and word.\<close>
primrec nextl :: "[hf set, 'a list] \<Rightarrow> hf set" where
    "nextl Q []     = epsclo Q"
  | "nextl Q (x#xs) = nextl (\<Union>q \<in> epsclo Q. nxt M q x) xs"

definition language :: "'a list set"  where
  "language \<equiv> {xs. nextl (init M) xs \<inter> final M \<noteq> {}}"

text\<open>The right language WRT a state q is the set of words that go from q to F.\<close>
definition right_lang :: "hf \<Rightarrow> 'a list set"  where
  "right_lang q \<equiv> {u. nextl {q} u \<inter> final M \<noteq> {}}"

lemma nextl_epsclo [simp]: "nextl (epsclo Q) xs = nextl Q xs"
  by (induct xs) auto

lemma epsclo_nextl [simp]: "epsclo (nextl Q xs) = nextl Q xs"
  by (induct xs arbitrary: Q) auto

lemma nextl_app: "nextl Q (xs@ys) = nextl (nextl Q xs) ys"
  by (induct xs arbitrary: Q) auto

lemma nextl_snoc [simp]: "nextl Q (xs@[x]) = (\<Union>q \<in> nextl Q xs. epsclo (nxt M q x))"
  by (simp add: nextl_app)

lemma nextl_state: "nextl Q xs \<subseteq> states M"
  by (induct xs arbitrary: Q) auto

lemma nextl_mono: "Q' \<subseteq> Q \<Longrightarrow> nextl Q' u \<subseteq> nextl Q u"
  by (induct u rule: rev_induct) (auto simp: epsclo_mono)

lemma nextl_eps: "q \<in> nextl Q u \<Longrightarrow> (q,q') \<in> eps M \<Longrightarrow> q' \<in> states M \<Longrightarrow> q' \<in> nextl Q u"
  using rtrancl_into_rtrancl epsclo_nextl epsclo_eq_Image by fastforce

lemma finite_nextl: "finite (nextl Q u)"
  by (induct u rule: List.rev_induct) auto

lemma nextl_empty [simp]: "nextl {} xs = {}"
  by (induct xs) auto

lemma nextl_Un: "nextl (Q1 \<union> Q2) xs = nextl Q1 xs \<union> nextl Q2 xs"
  by (induct xs arbitrary: Q1 Q2) auto

lemma nextl_UN: "nextl (\<Union>i\<in>I. f i) xs = (\<Union>i\<in>I. nextl (f i) xs)"
  by (induct xs arbitrary: f) auto

subsection\<open>The Powerset Construction\<close>

definition Power_dfa :: "'a dfa" where
  "Power_dfa = \<lparr>dfa.states = {HF (epsclo q) | q. q \<in> Pow (states M)},
                     init  = HF (epsclo (init M)),
                     final = {HF (epsclo Q) | Q. Q \<subseteq> states M \<and> Q \<inter> final M \<noteq> {}},
                     nxt   = \<lambda>Q x. HF(\<Union>q \<in> epsclo (hfset Q). epsclo (nxt M q x))\<rparr>"

lemma states_Power_dfa [simp]: "dfa.states Power_dfa = HF ` epsclo ` Pow (states M)"
  by (auto simp add: Power_dfa_def)

lemma init_Power_dfa [simp]: "dfa.init Power_dfa = HF (epsclo (nfa.init M))"
  by (simp add: Power_dfa_def)

lemma final_Power_dfa [simp]: "dfa.final Power_dfa = {HF (epsclo Q) | Q. Q \<subseteq> states M \<and> Q \<inter> final M \<noteq> {}}"
  by (simp add: Power_dfa_def)

lemma nxt_Power_dfa [simp]: "dfa.nxt Power_dfa = (\<lambda>Q x. HF(\<Union>q \<in> epsclo (hfset Q). epsclo (nxt M q x)))"
  by (simp add: Power_dfa_def)

interpretation Power: dfa Power_dfa
proof unfold_locales
  show "dfa.init Power_dfa \<in> dfa.states Power_dfa"
    by (force simp add: init)
next
  show "dfa.final Power_dfa \<subseteq> dfa.states Power_dfa"
    by auto
next
  fix q a
  show "q \<in> dfa.states Power_dfa \<Longrightarrow> dfa.nxt Power_dfa q a \<in> dfa.states Power_dfa"
    apply (auto simp: nxt)
    apply (subst inj_on_image_mem_iff [OF inj_on_HF])
    apply (auto simp: rev_finite_subset [OF finite] nxt)
    apply (metis Pow_iff epsclo_UN epsclo_idem epsclo_subset image_eqI)
    done
next
  show "finite (dfa.states Power_dfa)"
    by (force simp: finite)
qed

corollary dfa_Power: "dfa Power_dfa"
  by unfold_locales

lemma nextl_Power_dfa:
     "qs \<in> dfa.states Power_dfa
     \<Longrightarrow> dfa.nextl Power_dfa qs u = HF (\<Union>q \<in> hfset qs. nextl {q} u)"
  apply (induct u rule: List.rev_induct)
  apply (auto simp: finite_nextl inj_on_HF [THEN inj_on_eq_iff])
  apply (metis Int_empty_left Int_insert_left_if1 epsclo_increasing epsclo_subset subsetD singletonI)
  apply (metis contra_subsetD empty_subsetI epsclo_idem epsclo_mono insert_subset)
  done

text\<open>Part of Prop 4 of Jean-Marc Champarnaud, A. Khorsi and T. Paranthoën (2002)\<close>
lemma Power_right_lang:
     "qs \<in> dfa.states Power_dfa \<Longrightarrow> Power.right_lang qs = (\<Union>q \<in> hfset qs. right_lang q)"
using epsclo_increasing
apply (auto simp: Power.right_lang_def right_lang_def nextl_Power_dfa
                  inj_on_HF [THEN inj_on_eq_iff] finite_nextl, blast)
apply (rename_tac Q u q1 q2)
apply (drule_tac x="(\<Union>x\<in>epsclo Q. nextl {x} u)" in spec)
apply auto
using nextl_state apply blast
done


text\<open>The Power DFA accepts the same language as the NFA.\<close>
theorem Power_language [simp]: "Power.language = language"
proof -
  { fix u
    have "(Power.nextl (dfa.init Power_dfa) u) = HF (nextl (init M) u)"
    proof (induct u rule: List.rev_induct)
      case Nil show ?case
        using Power.nextl.simps
        by (auto simp: hinsert_def)
    next
      case (snoc x u) then show ?case
        by (simp add: init finite_nextl nextl_state [THEN subsetD])
    qed
    then have "u \<in> Power.language \<longleftrightarrow> u \<in> language"
      apply (auto simp add: Power.language_def language_def disjoint_iff_not_equal)
      apply (metis Int_iff finite_nextl hfset_HF nextl.simps(1) epsclo_increasing subsetCE)
      apply (metis epsclo_nextl nextl_state)
      done
  }
  then show ?thesis
    by blast
qed

text\<open>Every language accepted by a NFA is also accepted by a DFA.\<close>
corollary imp_regular: "regular language"
  using Power_language dfa_Power regular_def by blast

end

text\<open>As above, outside the locale\<close>
corollary nfa_imp_regular:
  assumes "nfa M" "nfa.language M = L"
    shows "regular L"
using assms nfa.imp_regular by blast


section\<open>Closure Properties for Regular Languages\<close>

subsection\<open>The Empty Language\<close>

theorem regular_empty:  "regular {}"
proof -
  interpret D: dfa "\<lparr>dfa.states = {0}, init = 0, final = {}, nxt = \<lambda>q x. q\<rparr>"
    by (auto simp: dfa_def)
  have "D.language = {}"
    by (simp add: D.language_def)
  then show ?thesis
    unfolding regular_def dfa_def
    by force
qed

subsection\<open>The Empty Word\<close>

theorem regular_nullstr:  "regular {[]}"
proof -
  interpret N: nfa "\<lparr>states = {0}, init = {0}, final = {0}, nxt = \<lambda>q x. {}, eps = {} \<rparr>"
    by (auto simp: nfa_def)
  have "\<And>u. 0 \<in> N.nextl {0} u \<Longrightarrow> u = []"
    by (rule list.exhaust, auto)
  then have "N.language = {[]}"
    by (auto simp: N.language_def)
  then show ?thesis
    by (metis N.imp_regular)
qed

subsection\<open>Single Symbol Languages\<close>

theorem regular_singstr: "regular {[a]}"
proof -
  let ?N = "\<lparr>states = {0,1}, init = {0}, final = {1},
             nxt = \<lambda>q x. if q=0 \<and> x=a then {1} else {},
             eps = {}\<rparr>"
  interpret N: nfa ?N
    by (auto simp: nfa_def)
  have [intro]: "\<And>u. 1 \<in> N.nextl {1} u \<Longrightarrow> u = []"
      by (rule list.exhaust) auto
  { fix u
    have "\<lbrakk>1 \<in> nfa.nextl ?N {0} u\<rbrakk> \<Longrightarrow> u = [a]"
      by (cases u) (auto split: if_split_asm)
  }
  then have "N.language = {[a]}"
    by (auto simp: N.language_def split: if_split_asm)
  then show ?thesis
    by (metis N.imp_regular)
qed

subsection\<open>The Complement of a Language\<close>

theorem regular_Compl:
  assumes S: "regular S" shows "regular (-S)"
proof -
  obtain MS  where M: "dfa MS" and lang: "dfa.language MS = S"
    using S by (auto simp: regular_def)
  interpret ST: dfa "\<lparr>dfa.states= dfa.states MS,
                     init= dfa.init MS, final= dfa.states MS - dfa.final MS,
                     nxt= \<lambda>q x. dfa.nxt MS q x\<rparr>"
    using M
    by (force simp add: dfa_def)
  { fix u
    have "ST.nextl (dfa.init MS) u = dfa.nextl MS (dfa.init MS) u"
      by (induct u rule: List.rev_induct) (auto simp: dfa.nextl_snoc dfa.nextl.simps M)
    then have "u \<in> ST.language \<longleftrightarrow> u \<notin> dfa.language MS"
      by (auto simp: M dfa.nextl_init_state ST.language_def dfa.language_def)
  }
  then have eq_L: "ST.language = -S"
    using lang  by blast
  show ?thesis
    unfolding regular_def
    by (intro exI conjI, unfold_locales) (rule eq_L)
qed

subsection\<open>The Intersection and Union of Two Languages\<close>

text\<open>By the familiar product construction\<close>

theorem regular_Int:
  assumes S: "regular S" and T: "regular T" shows "regular (S \<inter> T)"
proof -
  obtain MS MT where M: "dfa MS" "dfa MT" and lang: "dfa.language MS = S" "dfa.language MT = T"
    using S T by (auto simp: regular_def)
  interpret ST: dfa "\<lparr>dfa.states = {\<langle>q1,q2\<rangle> | q1 q2. q1 \<in> dfa.states MS \<and> q2 \<in> dfa.states MT},
                     init       = \<langle>dfa.init MS, dfa.init MT\<rangle>,
                     final      = {\<langle>q1,q2\<rangle> | q1 q2. q1 \<in> dfa.final MS \<and> q2 \<in> dfa.final MT},
                     nxt        = \<lambda>\<langle>qs,qt\<rangle> x. \<langle>dfa.nxt MS qs x, dfa.nxt MT qt x\<rangle>\<rparr>"
    using M
    by (auto simp: dfa_def finite_image_set2)
  { fix u
    have "ST.nextl \<langle>dfa.init MS, dfa.init MT\<rangle> u =
         \<langle>dfa.nextl MS (dfa.init MS) u, dfa.nextl MT (dfa.init MT) u\<rangle>"
    proof (induct u rule: List.rev_induct)
      case Nil show ?case
        by (auto simp: dfa.nextl.simps M)
    next
      case (snoc x u) then show ?case
        by (simp add: dfa.nextl_snoc M)
    qed
    then have "u \<in> ST.language \<longleftrightarrow> u \<in> dfa.language MS \<and> u \<in> dfa.language MT"
      by (auto simp: M ST.language_def dfa.language_def dfa.finite_final)
  }
  then have eq_L: "ST.language = S \<inter> T"
    using lang
    by blast
  show ?thesis
    unfolding regular_def
    by (intro exI conjI, unfold_locales) (rule eq_L)
qed

corollary regular_Un:
  assumes S: "regular S" and T: "regular T" shows "regular (S \<union> T)"
  by (metis S T compl_sup double_compl regular_Compl  regular_Int [of "-S" "-T"])


subsection\<open>The Concatenation of Two Languages\<close>

lemma Inlr_rtrancl [simp]: "((\<lambda>q. (Inl q, Inr a)) ` A)\<^sup>* = ((\<lambda>q. (Inl q, Inr a)) ` A)\<^sup>="
  by (auto elim: rtranclE)

theorem regular_conc:
  assumes S: "regular S" and T: "regular T" shows "regular (S @@ T)"
proof -
  obtain MS MT where M: "dfa MS" "dfa MT" and lang: "dfa.language MS = S" "dfa.language MT = T"
    using S T by (auto simp: regular_def)
  note [simp] = dfa.init dfa.nxt dfa.nextl.simps dfa.nextl_snoc
  let ?ST = "\<lparr>nfa.states = Inl ` (dfa.states MS) \<union> Inr ` (dfa.states MT),
                  init  = {Inl (dfa.init MS)},
                  final = Inr ` (dfa.final MT),
                  nxt   = \<lambda>q x. sum_case (\<lambda>qs. {Inl (dfa.nxt MS qs x)})
                                             (\<lambda>qt. {Inr (dfa.nxt MT qt x)}) q,
                  eps   = (\<lambda>q. (Inl q, Inr (dfa.init MT))) ` dfa.final MS\<rparr>"
  interpret ST: nfa ?ST
    using M dfa.final
    by (force simp add: nfa_def dfa.finite)
  have Inl_in_eps_iff: "\<And>q Q. Inl q \<in> nfa.epsclo ?ST Q \<longleftrightarrow> Inl q \<in> Q \<and> q \<in> dfa.states MS"
    by (auto simp: M dfa.finite ST.epsclo_def)
  have Inr_in_eps_iff: "\<And>q Q. Inr q \<in> nfa.epsclo ?ST Q \<longleftrightarrow>
           (Inr q \<in> Q \<and> q \<in> dfa.states MT \<or> (q = dfa.init MT \<and> (\<exists>qf \<in> dfa.final MS. Inl qf \<in> Q)))"
    by (auto simp: M dfa.finite ST.epsclo_def)
  { fix u
    have "\<And>q. Inl q \<in> ST.nextl {Inl (dfa.init MS)} u \<longleftrightarrow> q = (dfa.nextl MS (dfa.init MS) u)"
    proof (induct u rule: List.rev_induct)
      case Nil show ?case
        by (auto simp: M Inl_in_eps_iff)
    next
      case (snoc x u) then show ?case
        apply (auto simp add: M dfa.nextl_init_state Inl_in_eps_iff is_hsum_def split: sum_case_split)
        apply (frule ST.nextl_state [THEN subsetD], auto)
        done
    qed
  } note Inl_ST_iff = this
  { fix u
    have "\<And>q. Inr q \<in> ST.nextl {Inl (dfa.init MS)} u  \<longleftrightarrow>
               (\<exists>uS uT. uS \<in> dfa.language MS \<and> u = uS@uT \<and> q = dfa.nextl MT (dfa.init MT) uT)"
    proof (induct u rule: List.rev_induct)
      case Nil show ?case
        by (auto simp: M dfa.language_def Inr_in_eps_iff)
    next
      case (snoc x u)
      then show ?case using M
        apply (auto simp: Inr_in_eps_iff)
        apply (frule ST.nextl_state [THEN subsetD], force)
        apply (frule ST.nextl_state [THEN subsetD])
        apply (auto simp: dfa.language_def Inl_ST_iff)
        apply (metis (lifting) append_Nil2 dfa.nextl.simps(1) dfa.nextl_snoc)
        apply (rename_tac uS uT)
        apply (rule_tac xs=uT in rev_exhaust, simp)
        apply (rule bexI [where x="Inl (dfa.nextl MS (dfa.init MS) u)"])
        apply (auto simp: Inl_ST_iff)
        apply (rule bexI)
        apply (auto simp: dfa.nextl_init_state)
        done
    qed
    then have "u \<in> ST.language \<longleftrightarrow>
               (\<exists>uS uT. uS \<in> dfa.language MS \<and> uT \<in> dfa.language MT \<and> u = uS@uT)"
      by (force simp: M ST.language_def dfa.language_def)
  }
  then have eq_L: "ST.language = S @@ T"
    using lang unfolding conc_def
    by blast
  then show ?thesis
    by (metis ST.imp_regular)
qed

lemma regular_word: "regular {u}"
proof (induction u)
  case Nil show ?case
    by (simp add: regular_nullstr)
next
  case (Cons x l)
  have "{x#l} = {[x]} @@ {l}"
    by (simp add: conc_def)
  then show ?case
    by (simp add: Cons.IH regular_conc regular_singstr)
qed

text\<open>All finite sets are regular.\<close>
theorem regular_finite: "finite L \<Longrightarrow> regular L"
  apply (induct L rule: finite.induct)
  apply (simp add: regular_empty)
  using regular_Un regular_word by fastforce

subsection\<open>The Kleene Star of a Language\<close>

theorem regular_star:
  assumes S: "regular S" shows "regular (star S)"
proof -
  obtain MS where M: "dfa MS" and lang: "dfa.language MS = S"
    using S by (auto simp: regular_def)
  note [simp] = dfa.init [OF M] dfa.nextl.simps [OF M] dfa.nextl_snoc [OF M]
  obtain q0 where q0: "q0 \<notin> dfa.states MS" using dfa.finite [OF M]
    by (metis hdomain_not_mem hfset_HF hmem_def)
  have [simp]: "q0 \<noteq> dfa.init MS"
    using M dfa.init q0 by blast
  have [simp]: "\<And>q x. q \<in> dfa.states MS \<Longrightarrow> q0 \<noteq> dfa.nxt MS q x"
    using M dfa.nxt q0 by fastforce
  have [simp]: "\<And>q u. q \<in> dfa.states MS \<Longrightarrow> q0 \<noteq> dfa.nextl MS q u"
    using M dfa.nextl_state q0 by blast
  let ?ST = "\<lparr>nfa.states = insert q0 (dfa.states MS),
                   init  = {q0},
                   final = {q0},
                   nxt   = \<lambda>q x. if q \<in> dfa.states MS then {dfa.nxt MS q x} else {},
                   eps   = insert (q0, dfa.init MS) (((\<lambda>q. (q, q0)) ` (dfa.final MS)))\<rparr>"
  interpret ST: nfa ?ST
    using M dfa.final
    by (auto simp: q0 nfa_def dfa.init dfa.finite dfa.nxt)
  have "\<And>x y. (x, y) \<in> (insert (q0, dfa.init MS) ((\<lambda>q. (q, q0)) ` dfa.final MS))\<^sup>* \<longleftrightarrow>
                 (x=y) \<or> (x = q0 \<and> y = dfa.init MS) \<or>
                 (x \<in> dfa.final MS \<and> y \<in> {q0, dfa.init MS})"
    apply (rule iffI)
    apply (erule rtrancl_induct)
    apply (auto intro: rtrancl.rtrancl_into_rtrancl)
    done
  then have eps_iff:
    "\<And>q Q. q \<in> ST.epsclo Q \<longleftrightarrow>
                 q \<in> Q \<inter> insert q0 (dfa.states MS) \<or>
                 (q = q0 \<and> dfa.final MS \<inter> Q \<noteq> {}) \<or>
                 (q = dfa.init MS \<and> insert q0 (dfa.final MS) \<inter> Q \<noteq> {})"
    by (auto simp: q0 ST.epsclo_def)
  { fix u
    have "dfa.nextl MS (dfa.init MS) u \<in> ST.nextl {q0} u"
    proof (induct u rule: List.rev_induct)
      case Nil show ?case
        by (auto simp: M eps_iff)
    next
      case (snoc x u) then show ?case
        using M q0
        apply (simp add: eps_iff)
        apply (rule bexI [where x="dfa.nextl MS (dfa.init MS) u"])
        apply (auto simp: dfa.nextl_init_state dfa.nxt)
        done
    qed
    } note dfa_in_ST = this
  { fix ustar
    assume "ustar \<in> star (dfa.language MS)"
    then have "q0 \<in> ST.nextl {q0} ustar"
    proof (induct rule: star_induct)
      case Nil show ?case
        by (auto simp: eps_iff)
    next
      case (append u v)
      then have "dfa.nextl MS (dfa.init MS) u \<in> dfa.final MS"
        by (simp add: M dfa.language_def)
      then have "q0 \<in> ST.nextl {q0} u"
        by (auto intro: ST.nextl_eps dfa_in_ST)
      then show ?case
        using append ST.nextl_mono
        by (clarsimp simp add: ST.nextl_app) blast
    qed
  } note star_dfa_in_ST = this
  { fix u q
    assume "q \<in> ST.nextl {q0} u"
    then have  "q = q0 \<and> u=[] \<or>
                (\<exists>u1 u2. u = u1@u2 \<and> u1 \<in> star (dfa.language MS) \<and>
                  (q \<in> ST.epsclo {dfa.nextl MS (dfa.init MS) u2}))"
    proof (induction u arbitrary: q rule: List.rev_induct)
      case Nil then show ?case
        by (auto simp: M  dfa.init eps_iff)
    next
      case (snoc x u) show ?case using snoc.prems q0 M
        apply (auto split: if_split_asm simp: dfa.language_def eps_iff
                    dest!: snoc.IH)
        apply (metis dfa.nextl_snoc)
        apply (rename_tac u1 u2)
        apply (rule_tac x="u1@u2" in exI, auto)
        apply (rule_tac x = u1 in exI, auto)
        apply (rule_tac x="u1@u2" in exI, auto)
        apply (rule_tac x="u1@u2@[x]" in exI, auto)
        apply (rule_tac x="u1@u2@[x]" in exI, auto)
        done
    qed
  } note in_ST_imp = this
  have "\<And>u. q0 \<in> ST.nextl {q0} u \<Longrightarrow> u \<in> star (dfa.language MS)"
    by (auto simp: M dfa.init dfa.language_def eps_iff dest: in_ST_imp)
  then have eq_L: "ST.language = star S"
    using lang
    by (auto simp: ST.language_def star_dfa_in_ST)
  then show ?thesis
    by (metis ST.imp_regular)
qed

subsection\<open>The Reversal of a Regular Language\<close>

definition Reverse_nfa :: "'a dfa \<Rightarrow> 'a nfa" where
  "Reverse_nfa MS = \<lparr>nfa.states = dfa.states MS,
                         init  = dfa.final MS,
                         final = {dfa.init MS},
                         nxt   = \<lambda>q x. {q' \<in> dfa.states MS. q = dfa.nxt MS q' x},
                         eps   = {}\<rparr>"

lemma states_Reverse_nfa [simp]: "states (Reverse_nfa MS) = dfa.states MS"
  by (simp add: Reverse_nfa_def)

lemma init_Reverse_nfa [simp]: "init (Reverse_nfa MS) = dfa.final MS"
  by (simp add: Reverse_nfa_def)

lemma final_Reverse_nfa [simp]: "final (Reverse_nfa MS) = {dfa.init MS}"
  by (simp add: Reverse_nfa_def)

lemma nxt_Reverse_nfa [simp]:
  "nxt (Reverse_nfa MS) q x = {q' \<in> dfa.states MS. q = dfa.nxt MS q' x}"
  by (simp add: Reverse_nfa_def)

lemma eps_Reverse_nfa [simp]: "eps (Reverse_nfa MS) = {}"
  by (simp add: Reverse_nfa_def)

context dfa
begin

  lemma nfa_Reverse_nfa: "nfa (Reverse_nfa M)"
    by unfold_locales (auto simp: final finite)

  lemma nextl_Reverse_nfa:
    "nfa.nextl (Reverse_nfa M) Q u = {q' \<in> dfa.states M. dfa.nextl M q' (rev u) \<in> Q}"
  proof -
    interpret NR: nfa "Reverse_nfa M"
      by (rule nfa_Reverse_nfa)
    show ?thesis
      by (induct u rule: rev_induct) (auto simp: nxt)
  qed

  text\<open>Part of Prop 3 of Jean-Marc Champarnaud, A. Khorsi and T. Paranthoën (2002)\<close>
  lemma right_lang_Reverse: "nfa.right_lang (Reverse_nfa M) q = rev ` (dfa.left_lang M q)"
  proof -
    interpret NR: nfa "Reverse_nfa M"
      by (rule nfa_Reverse_nfa)
    show ?thesis
      by (force simp add: left_lang_def NR.right_lang_def nfa_Reverse_nfa nextl_Reverse_nfa)
  qed

  lemma right_lang_Reverse_disjoint:
    "q1 \<noteq> q2 \<Longrightarrow> nfa.right_lang (Reverse_nfa M) q1 \<inter> nfa.right_lang (Reverse_nfa M) q2 = {}"
    by (auto simp: left_lang_def right_lang_Reverse)

  lemma epsclo_Reverse_nfa [simp]: "nfa.epsclo (Reverse_nfa M) Q = Q \<inter> dfa.states M"
    by (auto simp: nfa.epsclo_def nfa_Reverse_nfa)

  theorem language_Reverse_nfa [simp]:
     "nfa.language (Reverse_nfa M) = (rev ` dfa.language M)"
  proof -
    interpret NR: nfa "Reverse_nfa M"
      by (rule nfa_Reverse_nfa)
    have "NR.language = {u. rev u \<in> dfa.language M}"
    proof (rule set_eqI, simp)
      fix u
      have "\<And>Q q'. q' \<in> dfa.states M \<Longrightarrow>
                   q' \<in> NR.nextl Q u \<longleftrightarrow> dfa.nextl M q' (rev u) \<in> Q"
        by (induct u rule: List.rev_induct) (auto simp: nxt)
      then show "u \<in> nfa.language (Reverse_nfa M) \<longleftrightarrow> rev u \<in> language"
        by (simp add: NR.language_def language_def)
    qed
    then show ?thesis
      by (force simp add: language_def)
  qed

end

corollary regular_Reverse:
  assumes S: "regular S" shows "regular (rev ` S)"
proof -
  obtain MS where MS: "dfa MS" "dfa.language MS = S"
    using S by (auto simp: regular_def)
  then interpret dfa "MS"
    by simp
  show ?thesis
    using nfa_Reverse_nfa nfa_imp_regular language_Reverse_nfa MS
    by blast
qed


text\<open>All regular expressions yield regular languages.\<close>
theorem regular_lang: "regular (lang r)"
  by (induct r)
     (auto simp: regular_empty regular_nullstr regular_singstr regular_Un regular_conc regular_star)


section\<open>Brzozowski's Minimization Algorithm\<close>

context dfa
  begin

subsection\<open>More about the relation @{term eq_app_right}\<close>

  lemma left_eq_app_right:
       "\<lbrakk>u \<in> left_lang q; v \<in> left_lang q\<rbrakk> \<Longrightarrow> (u,v) \<in> eq_app_right language"
    by (simp add: eq_app_right_def left_lang_def language_def nextl_app)

  lemma eq_app_right_class_eq:
    "UNIV // eq_app_right language = (\<lambda>q. eq_app_right language `` {path_to q}) ` accessible"
  proof -
    { fix u
      have "eq_app_right language `` {u} \<in> (\<lambda>q. eq_app_right language `` {path_to q}) ` accessible"
        apply (rule image_eqI)
        apply (rule equiv_class_eq [OF equiv_eq_app_right])
        apply (rule left_eq_app_right [OF _ path_to_left_lang])
        apply (auto simp: left_lang_def accessible_def)
        done
    }
    then show ?thesis
      by (auto simp: quotient_def)
  qed

  lemma inj_right_lang_imp_eq_app_right_index:
    assumes "inj_on right_lang (dfa.states M)"
      shows "bij_betw (\<lambda>q. eq_app_right language `` {path_to q})
                      accessible  (UNIV // eq_app_right language)"
    using assms
    apply (auto simp: bij_betw_def inj_on_def eq_app_right_class_eq)
    apply (drule eq_equiv_class [OF _ equiv_eq_app_right])
    apply (auto simp: nextl_path_to eq_app_right_def language_def right_lang_def
                 nextl_app accessible_imp_states)
    done

  definition min_states where
    "min_states \<equiv> card (UNIV // eq_app_right language)"

  lemma minimal_imp_index_eq_app_right:
    "minimal \<Longrightarrow> card (dfa.states M) = min_states"
    unfolding min_states_def minimal_def
    by (metis bij_betw_def card_image inj_right_lang_imp_eq_app_right_index)

  text\<open>A minimal machine has a minimal number of states, compared with any other machine
        for the same language.\<close>
  theorem minimal_imp_card_states_le:
       "\<lbrakk>minimal; dfa M'; dfa.language M' = language\<rbrakk>
        \<Longrightarrow> card (dfa.states M) \<le> card (dfa.states M')"
    using minimal_imp_index_eq_app_right dfa.index_eq_app_right_lower min_states_def
    by fastforce

  definition index_f :: "'a list set \<Rightarrow> hf" where
    "index_f \<equiv> SOME h. bij_betw h (UNIV // eq_app_right language) (hfset (ord_of min_states))"

  lemma index_f: "bij_betw index_f (UNIV // eq_app_right language) (hfset (ord_of min_states))"
  proof -
    have "\<exists>h. bij_betw h (UNIV // eq_app_right language) (hfset (ord_of min_states))"
      unfolding min_states_def
      by (metis L2_3 MN_eq_nextl ex_bij_betw_finite_nat bij_betw_ord_ofI)
   then show ?thesis
      unfolding index_f_def  by (metis someI_ex)
   qed

  interpretation Canon:
      MyhillNerode_dfa language "eq_app_right language"
                       language
                       min_states index_f
    by (simp add: MyhillNerode_dfa_def equiv_eq_app_right right_invariant_eq_app_right
                  index_f eq_app_right_eq)

  interpretation MN: dfa Canon.DFA
    by (fact Canon.dfa)

  definition iso :: "hf \<Rightarrow> hf" where
    "iso \<equiv> index_f o (\<lambda>q. eq_app_right language `` {path_to q})"

  theorem minimal_imp_isomorphic_to_canonical:
    assumes minimal
      shows "dfa_isomorphism M Canon.DFA iso"
    proof (unfold_locales, simp_all add: Canon.DFA_def)
      have "bij_betw iso accessible (hfset (ord_of min_states))"
        using assms bij_betw_trans index_f inj_right_lang_imp_eq_app_right_index
        unfolding iso_def minimal_def
        by blast
      then show "bij_betw iso (dfa.states M) (index_f ` (UNIV // eq_app_right language))"
        by (metis assms bij_betw_def index_f minimal_def)
    next
      have "eq_app_right language `` {path_to (dfa.init M)} = eq_app_right language `` {[]}"
      proof (rule equiv_class_eq [OF equiv_eq_app_right])
        show "(path_to (dfa.init M), []) \<in> eq_app_right language"
        using nextl_path_to assms
        by (auto simp: minimal_def eq_app_right_def language_def nextl_app)
      qed
      then show "iso (dfa.init M) = index_f (eq_app_right language `` {[]})"
        by (simp add: iso_def)
    next
      have "(\<lambda>u. eq_app_right language `` {path_to u}) ` dfa.final M =
            (\<lambda>l. eq_app_right language `` {l}) ` language"
        using assms final nextl_path_to nextl_app
        apply (auto simp: dfa_isomorphism_def language_def minimal_def)
        apply (auto simp: eq_app_right_def
                    intro: rev_image_eqI equiv_class_eq [OF equiv_eq_app_right])
        done
      from this [THEN image_eq_imp_comp [where h = index_f]]
      show "iso ` dfa.final M = {index_f (eq_app_right language `` {u}) |u. u \<in> language}"
        by (simp add: iso_def o_def Setcompr_eq_image)
    next
      have nxt: "\<And>q x. q \<in> dfa.states M \<Longrightarrow>
                       eq_app_right language `` {path_to (dfa.nxt M q x)} =
                       eq_app_right language `` {path_to q @ [x]}"
        apply (rule equiv_class_eq [OF equiv_eq_app_right])
        using assms nextl_path_to nxt nextl_app
        apply (auto simp: minimal_def nextl_path_to eq_app_right_def language_def)
        done
      show "\<And>q x. q \<in> dfa.states M \<Longrightarrow>
           iso (dfa.nxt M q x) =
           index_f
            (\<Union>u\<in>MyhillNerode_dfa.hinv (eq_app_right language) index_f (iso q).
                eq_app_right language `` {u @ [x]})"
        by (simp add: iso_def Canon.injh Canon.hinv_def quotientI Canon.resp nxt
                      UN_equiv_class [OF equiv_eq_app_right])
  qed

  lemma states_PR [simp]:
       "dfa.states (nfa.Power_dfa (Reverse_nfa M)) = HF ` Pow (dfa.states M)"
    by (rule set_eqI)
       (auto simp: nfa.states_Power_dfa nfa_Reverse_nfa image_iff Bex_def)

  lemma inj_on_right_lang_PR:
    assumes "dfa.states M = accessible"
      shows "inj_on (dfa.right_lang (nfa.Power_dfa (Reverse_nfa M)))
                    (dfa.states (nfa.Power_dfa (Reverse_nfa M)))"
  proof (rule inj_onI)
    fix q1 q2
    assume *: "q1 \<in> dfa.states (nfa.Power_dfa (Reverse_nfa M))"
              "q2 \<in> dfa.states (nfa.Power_dfa (Reverse_nfa M))"
              "dfa.right_lang (nfa.Power_dfa (Reverse_nfa M)) q1 =
               dfa.right_lang (nfa.Power_dfa (Reverse_nfa M)) q2"
    then have "hfset q1 \<subseteq> accessible \<and> hfset q2 \<subseteq> accessible"
      using assms rev_finite_subset [OF finite]
      by force
    with * show "q1 = q2"
      apply (simp add: nfa_Reverse_nfa nfa.Power_right_lang right_lang_Reverse
                       image_UN [symmetric] inj_image_eq_iff)
      apply (metis HF_hfset le_sup_iff left_lang_UN)
      done
  qed

  abbreviation APR :: "'x dfa \<Rightarrow> 'x dfa" where
    "APR X \<equiv> dfa.Accessible_dfa (nfa.Power_dfa (Reverse_nfa X))"

  theorem minimal_APR:
    assumes "dfa.states M = accessible"
      shows "dfa.minimal (APR M)"
    proof -
      have PR: "dfa (APR M)"
               "dfa (nfa.Power_dfa (Reverse_nfa M))"
        by (auto simp: dfa.dfa_Accessible nfa.dfa_Power nfa_Reverse_nfa)
      then show ?thesis
        apply (simp add: dfa.minimal_def dfa.states_Accessible_dfa dfa.Accessible_accessible)
        apply (simp add: inj_on_def dfa.Accessible_right_lang_eq)
        apply (meson assms dfa.accessible_imp_states inj_onD inj_on_right_lang_PR)
        done
    qed

  definition Brzozowski :: "'a dfa" where
    "Brzozowski \<equiv> APR (APR M)"

  lemma dfa_Brzozowski: "dfa Brzozowski"
    by (simp add: Brzozowski_def dfa.dfa_Accessible dfa.nfa_Reverse_nfa
                  nfa.dfa_Power nfa_Reverse_nfa)

  theorem language_Brzozowski: "dfa.language Brzozowski = language"
    by (simp add: Brzozowski_def dfa.Accessible_language nfa.Power_language
          dfa.dfa_Accessible dfa.nfa_Reverse_nfa nfa.dfa_Power nfa_Reverse_nfa
          dfa.language_Reverse_nfa image_image)

  theorem minimal_Brzozowski: "dfa.minimal Brzozowski"
  unfolding Brzozowski_def
  proof (rule dfa.minimal_APR)
    show "dfa (APR M)"
      by (simp add: dfa.dfa_Accessible nfa.dfa_Power nfa_Reverse_nfa)
  next
    show "dfa.states (APR M) = dfa.accessible (APR M)"
      by (simp add: dfa.Accessible_accessible dfa.states_Accessible_dfa nfa.dfa_Power nfa_Reverse_nfa)
  qed

  end

lemma index_f_cong:
     "\<lbrakk>dfa.language M = dfa.language N; dfa M; dfa N\<rbrakk> \<Longrightarrow> dfa.index_f M = dfa.index_f N"
  by (simp add: dfa.index_f_def dfa.min_states_def)

theorem minimal_imp_isomorphic:
     "\<lbrakk>dfa.language M = dfa.language N; dfa.minimal M; dfa.minimal N; dfa M; dfa N\<rbrakk>
      \<Longrightarrow> \<exists>h. dfa_isomorphism M N h"
  by (metis dfa_isomorphism.sym dfa_isomorphism.trans
            dfa.minimal_imp_isomorphic_to_canonical index_f_cong)

end

