(*  Author: Tobias Nipkow, Dmitriy Traytel *)

section \<open>Linear Time Optimization for ``Mark Before Atom'' (for a Fixed Alphabet)\<close>

(*<*)
theory Before2
imports
  Position_Autos
begin
(*>*)

declare Let_def[simp]

datatype 'a mrexp3 =
  Zero3 |
  One3 |
  Atom3 bool 'a |
  Plus3 "'a mrexp3" "'a mrexp3" (fin1: "'a set") (nul: bool) |
  Times3 "'a mrexp3" "'a mrexp3" (fin1: "'a set") (nul: bool) |
  Star3 "'a mrexp3" (fin1: "'a set")
where
  "fin1 Zero3 = {}"
| "nul Zero3 = False"
| "fin1 One3 = {}"
| "nul One3 = True"
| "fin1 (Atom3 m a) = (if m then {a} else {})"
| "nul (Atom3 _ _) = False"
| "nul (Star3 _ _) = True"

primrec final3 where
  "final3 Zero3 = False"
| "final3 One3 = False"
| "final3 (Atom3 m a) = m"
| "final3 (Plus3 r s _ _) = (final3 r \<or> final3 s)"
| "final3 (Times3 r s _ _) = (final3 s \<or> nul s \<and> final3 r)"
| "final3 (Star3 r _) = final3 r"

primrec mrexps3 :: "'a rexp \<Rightarrow> ('a mrexp3) set" where
  "mrexps3 Zero = {Zero3}"
| "mrexps3 One = {One3} "
| "mrexps3 (Atom a) = {Atom3 True a, Atom3 False a}"
| "mrexps3 (Plus r s) = (\<lambda>(r, s, f1, n). Plus3 r s f1 n) ` (mrexps3 r \<times> mrexps3 s \<times> Pow (atoms (Plus r s)) \<times> UNIV)"
| "mrexps3 (Times r s) = (\<lambda>(r, s, f1, n). Times3 r s f1 n) ` (mrexps3 r \<times> mrexps3 s \<times> Pow (atoms (Times r s))  \<times> UNIV)"
| "mrexps3 (Star r) = (\<lambda>(r, f1). Star3 r f1) ` (mrexps3 r \<times> Pow (atoms (Star r)))"

lemma finite_atoms[simp]: "finite (atoms r)"
  by (induct r) auto

lemma finite_mrexps3[simp]: "finite (mrexps3 r)"
  by (induct r) auto

definition[simp]: "plus3 r s == Plus3 r s (fin1 r \<union> fin1 s) (nul r \<or> nul s)"
definition[simp]: "times3 r s ==
  let ns = nul s in Times3 r s (fin1 s \<union> (if ns then fin1 r else {})) (nul r \<and> ns)"
definition[simp]: "star3 r == Star3 r (fin1 r)"

primrec follow3 :: "bool \<Rightarrow> 'a mrexp3 \<Rightarrow> 'a mrexp3" where
"follow3 m Zero3 = Zero3" |
"follow3 m One3 = One3" |
"follow3 m (Atom3 _ a) = Atom3 m a" |
"follow3 m (Plus3 r s _ _) = plus3 (follow3 m r) (follow3 m s)" |
"follow3 m (Times3 r s _ _) =
  times3 (follow3 m r) (follow3 (final3 r \<or> m \<and> nul r) s)" |
"follow3 m (Star3 r _) = star3(follow3 (final3 r \<or> m) r)"

primrec empty_mrexp3 :: "'a rexp \<Rightarrow> 'a mrexp3" where
"empty_mrexp3 Zero = Zero3" |
"empty_mrexp3 One = One3" |
"empty_mrexp3 (Atom x) = Atom3 False x" |
"empty_mrexp3 (Plus r s) = plus3 (empty_mrexp3 r) (empty_mrexp3 s)" |
"empty_mrexp3 (Times r s) = times3 (empty_mrexp3 r) (empty_mrexp3 s)" |
"empty_mrexp3 (Star r) = star3 (empty_mrexp3 r)"

primrec move3 :: "'a \<Rightarrow> 'a mrexp3 \<Rightarrow> bool \<Rightarrow> 'a mrexp3" where
"move3 _ One3 _ = One3" |
"move3 _ Zero3 _ = Zero3" |
"move3 c (Atom3 _ a) m = Atom3 m a" |
"move3 c (Plus3 r s _ _) m = plus3 (move3 c r m) (move3 c s m)" |
"move3 c (Times3 r s _ _) m =
  times3 (move3 c r m) (move3 c s (c \<in> fin1 r \<or> m \<and> nul r))" |
"move3 c (Star3 r _) m = star3 (move3 c r (c \<in> fin1 r \<or> m))"

primrec strip3 where
"strip3 Zero3 = Zero" |
"strip3 One3 = One" |
"strip3 (Atom3 m x) = Atom (m, x)" |
"strip3 (Plus3 r s _ _) = Plus (strip3 r) (strip3 s)" |
"strip3 (Times3 r s _ _) = Times (strip3 r) (strip3 s)" |
"strip3 (Star3 r _) = Star (strip3 r)"

lemma strip_mrexps3: "(strip o strip3) ` mrexps3 r = {r}"
by (induction r) (auto simp: set_eq_subset subset_iff image_iff)

primrec ok3 :: "'a mrexp3 \<Rightarrow> bool" where
"ok3 Zero3 = True" |
"ok3 One3 = True" |
"ok3 (Atom3 _ _) = True" |
"ok3 (Plus3 r s f1 n) = (ok3 r \<and> ok3 s \<and>
   (let rs = Plus (strip3 r) (strip3 s) in f1 = Collect (final1 rs) \<and> n = nullable rs))" |
"ok3 (Times3 r s f1 n) = (ok3 r \<and> ok3 s \<and>
   (let rs = Times (strip3 r) (strip3 s) in f1 = Collect (final1 rs) \<and> n = nullable rs))" |
"ok3 (Star3 r f1) = (ok3 r \<and> f1 = Collect (final1 (strip3 r)))"

lemma ok3_fin1_final1[simp]: "ok3 r \<Longrightarrow> fin1 r = Collect (final1 (strip3 r))"
  by (induct r) (auto simp add: set_eq_iff)

lemma ok3_nul_nullable[simp]: "ok3 r \<Longrightarrow> nul r = nullable (strip3 r)"
  by (induct r) auto

lemma ok3_final3_final[simp]: "ok3 r \<Longrightarrow> final3 r = final (strip3 r)"
  by (induct r) auto

lemma follow3_follow[simp]: "ok3 r \<Longrightarrow> strip3 (follow3 m r) = follow m (strip3 r)"
  by (induct r arbitrary: m) auto

lemma nul_follow3[simp]: "ok3 r \<Longrightarrow> nul (follow3 m r) = nul r"
  by (induct r arbitrary: m) auto

lemma ok3_follow3[simp]: "ok3 r \<Longrightarrow> ok3 (follow3 m r)"
  by (induct r arbitrary: m) auto

lemma fin1_atoms: "\<lbrakk>x \<in> fin1 mr; mr \<in> mrexps3 r\<rbrakk> \<Longrightarrow> x \<in> atoms r"
  by (induct r) auto

lemma follow3_mrexps3[simp]: "r \<in> mrexps3 s \<Longrightarrow> follow3 m r \<in> mrexps3 s"
  by (induct s arbitrary: m r) (fastforce simp add: image_iff dest: fin1_atoms)+

lemma empty_mrexp3_mrexps[simp]: "empty_mrexp3 r \<in> mrexps3 r"
  by (induct r) (auto simp: image_iff dest: fin1_atoms)

lemma strip3_empty_mrexp3[simp]: "strip3 (empty_mrexp3 r) = empty_mrexp r"
  by (induct r) auto

lemma strip3_move3: "ok3 r \<Longrightarrow> strip3(move3 m r c) = move m (strip3 r) c"
apply(induction r arbitrary: c)
apply (auto simp: disj_commute)
done

lemma nul_empty_mrexp3[simp]: "nul (empty_mrexp3 r) = nullable r"
apply(induction r)
apply auto
done

lemma ok3_empty_mrexp3: "ok3 (empty_mrexp3 r)"
apply(induction r)
apply auto
done

lemma ok3_move3: "ok3 r \<Longrightarrow> ok3(move3 m r c)"
apply(induction r arbitrary: c)
apply auto
done

lemma nonfin1_empty_mrexp3[simp]: "c \<notin> fin1 (empty_mrexp3 r)"
  by (induct r) auto

lemma move3_mrexps3[simp]: "r \<in> mrexps3 s \<Longrightarrow> move3 x r a \<in> mrexps3 s"
  by (induct s arbitrary: r x a) (fastforce simp: image_iff dest: fin1_atoms)+

typedef 'a ok_mrexp3 = "{(r :: 'a mrexp3, b :: bool). ok3 r}"
  unfolding mem_Collect_eq split_beta by (metis fst_eqD ok3_empty_mrexp3)

setup_lifting type_definition_ok_mrexp3

abbreviation "init_m r \<equiv> let mr = follow3 True (empty_mrexp3 r) in (mr, nul mr)"

lift_definition init_okm :: "'a rexp \<Rightarrow> 'a ok_mrexp3" is init_m
  by (simp add: ok3_empty_mrexp3)
lift_definition delta_okm :: "'a \<Rightarrow> 'a ok_mrexp3 \<Rightarrow> 'a ok_mrexp3" is
  "\<lambda>a (r, m). (move3 a r False, a \<in> fin1 r)"
  unfolding mem_Collect_eq split_beta fst_conv by (intro ok3_move3) simp
lift_definition nullable_okm :: "'a ok_mrexp3 \<Rightarrow> bool" is "snd" .
lift_definition lang_okm :: "'a ok_mrexp3 \<Rightarrow> 'a lang" is "\<lambda>(r, m). L_b (strip3 r, m)" .


instantiation ok_mrexp3 :: (equal) "equal"
begin

fun eq_mrexp3 where
  "eq_mrexp3 Zero3 Zero3 = True"
| "eq_mrexp3 One3 One3 = True"
| "eq_mrexp3 (Atom3 m x) (Atom3 m' y) = (m = m' \<and> x = y)"
| "eq_mrexp3 (Plus3 r1 s1 _ _) (Plus3 r3 s3 _ _) = (eq_mrexp3 r1 r3 \<and> eq_mrexp3 s1 s3)"
| "eq_mrexp3 (Times3 r1 s1 _ _) (Times3 r3 s3 _ _) = (eq_mrexp3 r1 r3 \<and> eq_mrexp3 s1 s3)"
| "eq_mrexp3 (Star3 r1 _) (Star3 r3 _) = (eq_mrexp3 r1 r3)"
| "eq_mrexp3 r s = False"

lemma eq_mrexp3_imp_eq: "\<lbrakk>eq_mrexp3 r s; ok3 r; ok3 s\<rbrakk> \<Longrightarrow> (r = s)"
  by (induct rule: eq_mrexp3.induct) auto

lemma eq_mrexp3_refl[simplified, simp]: "r = s \<Longrightarrow> eq_mrexp3 r s"
  by (induct rule: eq_mrexp3.induct) auto

lemma eq_mrexp3_eq: "\<lbrakk>ok3 r; ok3 s\<rbrakk> \<Longrightarrow> eq_mrexp3 r s = (r = s)"
  by (metis eq_mrexp3_imp_eq eq_mrexp3_refl)

lift_definition equal_ok_mrexp3 :: "'a ok_mrexp3 \<Rightarrow> 'a ok_mrexp3 \<Rightarrow> bool"
   is "\<lambda>(r1, b1) (r3, b3). b1 = b3 \<and> eq_mrexp3 r1 r3" .

instance by intro_classes (transfer, auto simp: eq_mrexp3_eq)

end

global_interpretation before2: rexp_DFA init_okm delta_okm nullable_okm lang_okm
  defines before2_closure = before2.closure
    and check_eqv_b2 = before2.check_eqv
    and reachable_b2 = before2.reachable
    and automaton_b2 = before2.automaton
    and match_b2 = before2.match
proof (standard, goal_cases)
  case (1 r) show "lang_okm (init_okm r) = lang r"
    by transfer (auto simp: split_beta init_a_def nonfinal_empty_mrexp Lm_follow Lm_empty
      map_map_rexp nullable_iff ok3_empty_mrexp3)
next
  case (2 a br) show "lang_okm (delta_okm a br) = Deriv a (lang_okm br)"
    apply transfer
    unfolding split_beta fst_conv snd_conv mem_Collect_eq before.L_delta[symmetric] delta_b.simps
      move_follow_read[symmetric] final_read_final1 Let_def
    by (subst strip3_move3) simp_all
next
  case (3 br) show  "nullable_okm br = ([] \<in> lang_okm br)"
    by transfer (simp add: split_beta)
next
  case (4 s)
  have "{fold (\<lambda>a (r, m). (move3 a r False, a \<in> fin1 r)) w (init_m s) |w. True} \<subseteq>
    mrexps3 s \<times> UNIV"
  proof (intro subsetI, elim CollectE exE conjE, hypsubst)
    fix w show "fold (\<lambda>a (r, m). (move3 a r False, a \<in> fin1 r)) w (init_m s) \<in>
      mrexps3 s \<times> UNIV"
    by (induct w rule: rev_induct) (auto simp: split: prod.splits intro!: move3_mrexps3)
  qed
  then show "finite {fold delta_okm w (init_okm s) |w. True}"
    by transfer (erule finite_subset[OF subset_trans[rotated]], auto)
qed

(*<*)
end
(*>*)
