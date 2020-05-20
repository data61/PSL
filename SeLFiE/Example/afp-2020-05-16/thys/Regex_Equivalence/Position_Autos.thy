(*  Author: Tobias Nipkow, Dmitriy Traytel *)

section \<open>Framework Instantiations using Marked Regular Expressions\<close>

(*<*)
theory Position_Autos
imports
  Automaton
begin
(*>*)

subsection \<open>Marked Regular Expressions\<close>

type_synonym 'a mrexp = "(bool * 'a) rexp"

abbreviation "strip \<equiv> map_rexp snd"

primrec mrexps :: "'a rexp \<Rightarrow> ('a mrexp) set" where
  "mrexps Zero = {Zero}"
| "mrexps One = {One}"
| "mrexps (Atom a) = {Atom (True, a), Atom (False, a)}"
| "mrexps (Plus r s) = case_prod Plus ` (mrexps r \<times> mrexps s)"
| "mrexps (Times r s) = case_prod Times ` (mrexps r \<times> mrexps s)"
| "mrexps (Star r) = Star ` mrexps r"

lemma finite_mrexps[simp]: "finite (mrexps r)"
by (induction r) auto

lemma strip_mrexps: "strip ` mrexps r = {r}"
by (induction r) (auto simp: set_eq_subset subset_iff image_iff)

fun Lm :: "'a mrexp \<Rightarrow> 'a lang" where
"Lm Zero = {}" |
"Lm One = {}" |
"Lm (Atom(m,a)) = (if m then {[a]} else {})" |
"Lm (Plus r s) = Lm r \<union> Lm s" |
"Lm (Times r s) = Lm r @@ lang(strip s) \<union> Lm s" |
"Lm (Star r) = Lm r @@ star(lang(strip r))"

fun final :: "'a mrexp \<Rightarrow> bool" where
"final Zero = False" |
"final One = False" |
"final (Atom(m,a)) = m" |
"final (Plus r s) = (final r \<or> final s)" |
"final (Times r s) = (final s \<or> nullable s \<and> final r)" |
"final (Star r) = final r"

abbreviation read :: "'a \<Rightarrow> 'a mrexp \<Rightarrow> 'a mrexp" where
"read a \<equiv> map_rexp (\<lambda>(m,x). (m \<and> a=x, x))"

lemma read_mrexps[simp]: "r \<in> mrexps s \<Longrightarrow> read a r \<in> mrexps s"
by (induction s arbitrary: a r) (auto simp: image_iff)

fun follow :: "bool \<Rightarrow> 'a mrexp \<Rightarrow> 'a mrexp" where
"follow m Zero = Zero" |
"follow m One = One" |
"follow m (Atom(_,a)) = Atom(m,a)" |
"follow m (Plus r s) = Plus (follow m r) (follow m s)" |
"follow m (Times r s) =
  Times (follow m r) (follow (final r \<or> m \<and> nullable r) s)" |
"follow m (Star r) = Star(follow (final r \<or> m) r)"

lemma follow_mrexps[simp]: "r \<in> mrexps s \<Longrightarrow> follow b r \<in> mrexps s"
by (induction s arbitrary: b r) (auto simp: image_iff)

lemma strip_read[simp]: "strip (read a r) = strip r"
by (simp add: map_map_rexp split_def)

lemma Nil_notin_Lm[simp]: "[] \<notin> Lm r"
by (induction r) (auto split: if_splits)

lemma Nil_in_lang_strip[simp]: "[] \<in> lang(r) \<longleftrightarrow> [] \<in> lang(strip r)"
by (induction r) auto

lemma strip_follow[simp]: "strip(follow m r) = strip r"
by (induction r arbitrary: m) (auto split: if_splits)

lemma conc_lemma: "[] \<notin> A \<Longrightarrow> {w : A @@ B. w \<noteq> [] \<and> P(hd w)} = {w : A. w \<noteq> [] \<and> P(hd w)} @@ B"
  unfolding conc_def by auto (metis hd_append2)+

lemma Lm_read: "Lm (read a r) = {w : Lm r. w \<noteq> [] \<and> hd w = a}"
proof (induction r)
  case (Times r1 r2) thus ?case
    using conc_lemma[OF Nil_notin_Lm, where P = "\<lambda>x. x=a" and r1 = r1] by auto
next
  case Star thus ?case using conc_lemma[OF Nil_notin_Lm, where P = "\<lambda>x. x=a"] by simp
qed (auto split: if_splits)

lemma tl_conc[simp]: "[] \<notin> A \<Longrightarrow>tl ` (A @@ B) = tl ` A @@ B"
by (fastforce simp: image_def Bex_def tl_append split: list.split)

lemma Nil_in_tl_Lm_if_final[simp]: "final r \<Longrightarrow> [] : tl ` Lm r"
by (induction r) (auto simp: nullable_iff image_Un)

lemma Nil_notin_tl_if_not_final: "\<not> final r \<Longrightarrow> [] \<notin> tl ` Lm r"
by (induction r) (auto simp: nullable_iff Nil_tl singleton_in_conc intro!: image_eqI[rotated])

lemma Lm_follow: "Lm (follow m r) = tl ` Lm r \<union> (if m then lang(strip r) else {}) - {[]}"
proof (induction r arbitrary: m)
  case (Atom mb) thus ?case by (cases mb) auto
next
  case (Times r s) thus ?case
    by (simp add: Un_Diff image_Un conc_Un_distrib nullable_iff
          conc_Diff_if_Nil1 Nil_notin_tl_if_not_final Un_ac)
next
  case (Star r) thus ?case
    by (simp add: Un_Diff conc_Un_distrib
          conc_Diff_if_Nil1 Nil_notin_tl_if_not_final star_Diff_Nil_fold)
qed auto

subsection \<open>Mark Before Atom\<close>

text\<open>Position automaton where mark is placed before atoms.\<close>

abbreviation "empty_mrexp \<equiv> map_rexp (\<lambda>a. (False,a))"

lemma empty_mrexp_mrexps[simp]: "empty_mrexp r \<in> mrexps r"
by (induction r) auto

lemma nullable_empty_mrexp[simp]: "nullable (empty_mrexp r) = nullable r"
  by (induct r) auto

definition "init_b r = (follow True (empty_mrexp r), nullable r)"

lemma init_b_mrexps[simp]: "init_b r \<in> mrexps r \<times> UNIV"
  unfolding init_b_def by auto

fun delta_b where
"delta_b a (r,b) = (let r' = read a r in (follow False r', final r'))"

lemma delta_b_mrexps[simp]: "rb \<in> mrexps r \<times> UNIV \<Longrightarrow> delta_b a rb \<in> mrexps r \<times> UNIV"
by (auto simp: Let_def)

lemma fold_delta_b_init_b_mrexps[simp]: "fold delta_b w (init_b s) \<in> mrexps s \<times> UNIV"
by (induction w arbitrary: s rule: rev_induct) auto

fun L_b where
"L_b (r,b) = Lm r \<union> (if b then {[]} else {})"

abbreviation "final_b \<equiv> snd"

lemma Lm_empty: "Lm (empty_mrexp r) = {}"
by (induction r) auto

lemma final_read_Lm: "final(read a r) \<longleftrightarrow> [a] \<in> Lm r"
by (induction r) (auto simp: nullable_iff concI_if_Nil2 singleton_in_conc split: if_splits)

global_interpretation before: rexp_DFA init_b delta_b final_b L_b
  defines before_closure = before.closure
    and check_eqv_b = before.check_eqv
    and reachable_b = before.reachable
    and automaton_b = before.automaton
    and match_b = before.match
proof (standard, goal_cases)
  case (1 r) show "L_b (init_b r) = lang r"
    by(auto simp add: init_b_def Lm_follow Lm_empty map_map_rexp nullable_iff)
next
  case (2 a rb) show "L_b (delta_b a rb) = Deriv a (L_b rb)"
    by (cases rb) (auto simp add: Deriv_def final_read_Lm image_def Lm_read Lm_follow)
next
  case (3 rb) show  "final_b rb \<longleftrightarrow> [] \<in> L_b rb" by (cases rb) simp
next
  case (4 s)
  have "{fold delta_b w (init_b s) |w. True} \<subseteq> mrexps s \<times> UNIV"
    by (intro subsetI, elim CollectE exE) (simp only: fold_delta_b_init_b_mrexps)
  then show "finite {fold delta_b w (init_b s) |w. True}" by (rule finite_subset) simp
qed

subsection \<open>Mark After Atom\<close>

text\<open>Position automaton where mark is placed after atoms. This is the
Glushkov and McNaughton/Yamada construction.\<close>

definition "init_a r = (True, empty_mrexp r)"

lemma init_a_mrexps[simp]: "init_a r \<in> UNIV \<times> mrexps r"
  unfolding init_a_def by auto

fun delta_a where
"delta_a a (b,r) = (False, read a (follow b r))"

lemma delta_a_mrexps[simp]: "br \<in> UNIV \<times> mrexps r \<Longrightarrow> delta_a a br \<in> UNIV \<times> mrexps r"
by auto

lemma fold_delta_a_init_a_mrexps[simp]: "fold delta_a w (init_a s) \<in> UNIV \<times> mrexps s"
by (induction w arbitrary: s rule: rev_induct) auto

fun final_a where
"final_a (b,r) \<longleftrightarrow> final r \<or> b \<and> nullable r"

fun L_a where
"L_a (b,r) = Lm (follow b r) \<union> (if final_a(b,r)  then {[]} else {})"

lemma nonfinal_empty_mrexp: "\<not> final (empty_mrexp r)"
by (induction r) auto

lemma Cons_eq_tl_iff[simp]: "x # xs = tl ys \<longleftrightarrow> (\<exists>y. ys = y # x # xs)"
by (cases ys) auto

lemma tl_eq_Cons_iff[simp]: "tl ys = x # xs \<longleftrightarrow> (\<exists>y. ys = y # x # xs)"
by (cases ys) auto

global_interpretation after: rexp_DFA init_a delta_a final_a L_a
  defines after_closure = after.closure
    and check_eqv_a = after.check_eqv
    and reachable_a = after.reachable
    and automaton_a = after.automaton
    and match_a = after.match
proof (standard, goal_cases)
  case (1 r) show "L_a (init_a r) = lang r"
    by (auto simp: init_a_def nonfinal_empty_mrexp Lm_follow Lm_empty map_map_rexp nullable_iff)
next
  case (2 a br) show "L_a (delta_a a br) = Deriv a (L_a br)"
    by (cases br) (simp add: Deriv_def final_read_Lm Lm_read Lm_follow,
      fastforce simp: image_def neq_Nil_conv)
next
  case (3 br) show  "final_a br \<longleftrightarrow> [] \<in> L_a br" by (cases br) simp
next
  case (4 s)
  have "{fold delta_a w (init_a s) |w. True} \<subseteq> UNIV \<times> mrexps s"
    by (intro subsetI, elim CollectE exE) (simp only: fold_delta_a_init_a_mrexps)
  then show "finite {fold delta_a w (init_a s) |w. True}" by (rule finite_subset) simp
qed

text \<open>
The ``before'' atomaton is a quotient of the ``after'' automaton.

The proof below follows an informal proof given by Helmut Seidl in personal communication. 
\<close>

fun hom_ab where
  "hom_ab (b, r) = (follow b r, final_a (b, r))"

lemma hom_delta: "hom_ab (delta_a x br) = delta_b x (hom_ab br)"
by(cases br) (auto simp add: Let_def)

lemma hom_deltas: "hom_ab (fold delta_a w br) = fold delta_b w (hom_ab br)"
  by (induct w arbitrary: br) (auto simp add: hom_delta)

lemma hom_init: "hom_ab (init_a r) = init_b r"
  unfolding init_a_def init_b_def hom_ab.simps by (simp add: nonfinal_empty_mrexp)
  
lemma reachable_ab: "reachable_b as r = hom_ab ` reachable_a as r"
  unfolding after.reachable before.reachable by (force simp: hom_init hom_deltas)

theorem card_reachable_ab: "card (reachable_b as r) \<le> card (reachable_a as r)"
  unfolding reachable_ab using after.finite_reachable by (rule card_image_le)

text\<open>The implementation by Fischer et al.:\<close>

(* better: shift b m r and move m b r *)
fun shift :: "bool \<Rightarrow> 'a mrexp \<Rightarrow> 'a \<Rightarrow> 'a mrexp" where
"shift _ One _ = One" |
"shift _ Zero _ = Zero" |
"shift m (Atom (_,x)) c = Atom (m \<and> (x=c),x)" |
"shift m (Plus r s) c = Plus (shift m r c) (shift m s c)" |
"shift m (Times r s) c =
  Times (shift m r c) (shift (final r \<or> m \<and> nullable r) s c)" |
"shift m (Star r) c = Star (shift (final r \<or> m) r c)"

lemma shift_read_follow: "shift m r x = read x (follow m r)"
by (induction m r x rule: shift.induct) auto

text\<open>In the spirit of Asperti, and similarly quadratic because of need
to call final1 in move.\<close>

fun final1 :: "'a mrexp \<Rightarrow> 'a \<Rightarrow> bool" where
"final1 Zero _ = False" |
"final1 One _ = False" |
"final1 (Atom(m,a)) x = (m \<and> a=x)" |
"final1 (Plus r s) x = (final1 r x \<or> final1 s x)" |
"final1 (Times r s) x = (final1 s x \<or> nullable s \<and> final1 r x)" |
"final1 (Star r) x = final1 r x"

fun move :: "'a \<Rightarrow> 'a mrexp \<Rightarrow> bool \<Rightarrow> 'a mrexp" where
"move _ One _ = One" |
"move _ Zero _ = Zero" |
"move c (Atom (_,a)) m = Atom (m, a)" |
"move c (Plus r s) m = Plus (move c r m) (move c s m)" |
"move c (Times r s) m =
  Times (move c r m) (move c s (final1 r c \<or> m \<and> nullable r))" |
"move c (Star r) m = Star (move c r (final1 r c \<or> m))"

lemma nullable_read[simp]: "nullable (read c r) = nullable r"
by (induction r) auto

lemma final_read_final1: "final (read c r) = final1 r c"
by (induction r) auto

lemma move_follow_read: "move c r m = follow m (read c r)"
by (induction c r m rule: move.induct) (auto simp: final_read_final1)

(*<*)
end
(*>*)

