(* Author: Tobias Nipkow, Dmitriy Traytel *)

section \<open>Linear Time Optimization for ``Mark After Atom''\<close>

(*<*)
theory After2
imports
  Position_Autos
begin
(*>*)

datatype 'a mrexp2 =
  Zero2 |
  One2 |
  Atom2 (fin: bool) 'a |
  Plus2 "'a mrexp2" "'a mrexp2" (fin: bool) (nul: bool) |
  Times2 "'a mrexp2" "'a mrexp2" (fin: bool) (nul: bool) |
  Star2 "'a mrexp2" (fin: bool)
where
  "fin Zero2 = False"
| "nul Zero2 = False"
| "fin One2 = False"
| "nul One2 = True"
| "nul (Atom2 _ _) = False"
| "nul (Star2 _ _) = True"

primrec mrexps2 :: "'a rexp \<Rightarrow> ('a mrexp2) set" where
  "mrexps2 Zero = {Zero2}"
| "mrexps2 One = {One2} "
| "mrexps2 (Atom a) = {Atom2 True a, Atom2 False a}"
| "mrexps2 (Plus r s) = (\<lambda>(r, s, f, n). Plus2 r s f n) ` (mrexps2 r \<times> mrexps2 s \<times> UNIV)"
| "mrexps2 (Times r s) = (\<lambda>(r, s, f, n). Times2 r s f n) ` (mrexps2 r \<times> mrexps2 s  \<times> UNIV)"
| "mrexps2 (Star r) = (\<lambda>(r, f). Star2 r f) ` (mrexps2 r \<times> UNIV)"

lemma finite_mrexps3[simp]: "finite (mrexps2 r)"
by (induction r) auto

definition[simp]: "plus2 r s == Plus2 r s (fin r \<or> fin s) (nul r \<or> nul s)"
definition[simp]: "times2 r s == Times2 r s (fin r \<and> nul s \<or> fin s) (nul r \<and> nul s)"
definition[simp]: "star2 r == Star2 r (fin r)"

primrec empty_mrexp2 :: "'a rexp \<Rightarrow> 'a mrexp2" where
"empty_mrexp2 Zero = Zero2" |
"empty_mrexp2 One = One2" |
"empty_mrexp2 (Atom x) = Atom2 False x" |
"empty_mrexp2 (Plus r s) = plus2 (empty_mrexp2 r) (empty_mrexp2 s)" |
"empty_mrexp2 (Times r s) = times2 (empty_mrexp2 r) (empty_mrexp2 s)" |
"empty_mrexp2 (Star r) = star2 (empty_mrexp2 r)"

primrec shift2 :: "bool \<Rightarrow> 'a mrexp2 \<Rightarrow> 'a \<Rightarrow> 'a mrexp2" where
"shift2 _ One2 _ = One2" |
"shift2 _ Zero2 _ = Zero2" |
"shift2 m (Atom2 _ x) c = Atom2 (m \<and> (x=c)) x" |
"shift2 m (Plus2 r s _ _) c = plus2 (shift2 m r c) (shift2 m s c)" |
"shift2 m (Times2 r s _ _) c = times2 (shift2 m r c) (shift2 (m \<and> nul r \<or> fin r) s c)" |
"shift2 m (Star2 r _) c =  star2 (shift2 (m \<or> fin r) r c)"

primrec strip2 where
"strip2 Zero2 = Zero" |
"strip2 One2 = One" |
"strip2 (Atom2 m x) = Atom (m, x)" |
"strip2 (Plus2 r s _ _) = Plus (strip2 r) (strip2 s)" |
"strip2 (Times2 r s _ _) = Times (strip2 r) (strip2 s)" |
"strip2 (Star2 r _) = Star (strip2 r)"

lemma strip_mrexps2: "(strip o strip2) ` mrexps2 r = {r}"
by (induction r) (auto simp: set_eq_subset subset_iff image_iff)

primrec ok2 :: "'a mrexp2 \<Rightarrow> bool" where
"ok2 Zero2 = True" |
"ok2 One2 = True" |
"ok2 (Atom2 _ _) = True" |
"ok2 (Plus2 r s f n) = (ok2 r \<and> ok2 s \<and>
   (let rs = Plus (strip2 r) (strip2 s) in f = final rs \<and> n = nullable rs))" |
"ok2 (Times2 r s f n) = (ok2 r \<and> ok2 s \<and>
   (let rs = Times (strip2 r) (strip2 s) in f = final rs \<and> n = nullable rs))" |
"ok2 (Star2 r f) = (ok2 r \<and> f = final (strip2 r))"

lemma ok2_fin_final[simp]: "ok2 r \<Longrightarrow> fin r = final (strip2 r)"
  by (induct r) auto

lemma ok2_nul_nullable[simp]: "ok2 r \<Longrightarrow> nul r = nullable (strip2 r)"
  by (induct r) auto

lemma strip2_shift2: "ok2 r \<Longrightarrow> strip2(shift2 m r c) = shift m (strip2 r) c"
apply(induction r arbitrary: m)
apply (auto simp: disj_commute)
done

lemma ok2_empty_mrexp2: "ok2 (empty_mrexp2 r)"
apply(induction r)
apply auto
done

lemma ok2_shift2: "ok2 r \<Longrightarrow> ok2(shift2 m r c)"
apply(induction r arbitrary: m)
apply auto
done

lemma strip2_empty_mrexp2[simp]: "strip2 (empty_mrexp2 r) = empty_mrexp r"
  by (induct r) auto

lemma nul_empty_mrexp2[simp]: "nul (empty_mrexp2 r) = nullable r"
  by (induct r) auto

lemma nonfin_empty_mrexp2[simp]: "\<not> fin (empty_mrexp2 r)"
  by (induct r) auto

lemma empty_mrexp2_mrexps2[simp]: "empty_mrexp2 s \<in> mrexps2 s"
  by (induct s) (auto simp: image_iff)

lemma shift2_mrexps2[simp]: "r \<in> mrexps2 s \<Longrightarrow> shift2 x r a \<in> mrexps2 s"
  by (induct s arbitrary: r x) (auto simp: image_iff)

typedef 'a ok_mrexp2 = "{(b :: bool, r :: 'a mrexp2). ok2 r}"
  unfolding mem_Collect_eq split_beta by (metis snd_eqD ok2_empty_mrexp2)

setup_lifting type_definition_ok_mrexp2

lift_definition init_okm :: "'a rexp \<Rightarrow> 'a ok_mrexp2" is "\<lambda>r. (True, empty_mrexp2 r)"
  by (simp add: ok2_empty_mrexp2 del: ok2.simps)
lift_definition delta_okm :: "'a \<Rightarrow> 'a ok_mrexp2 \<Rightarrow> 'a ok_mrexp2" is
  "\<lambda>a (m, r). (False, shift2 m r a)"
  unfolding mem_Collect_eq split_beta snd_conv by (intro ok2_shift2) simp
lift_definition nullable_okm :: "'a ok_mrexp2 \<Rightarrow> bool" is "\<lambda>(m, r). fin r \<or> m \<and> nul r" .
lift_definition lang_okm :: "'a ok_mrexp2 \<Rightarrow> 'a lang" is "\<lambda>(m, r). L_a (m, strip2 r)" .


instantiation ok_mrexp2 :: (equal) "equal"
begin

fun eq_mrexp2 where
  "eq_mrexp2 Zero2 Zero2 = True"
| "eq_mrexp2 One2 One2 = True"
| "eq_mrexp2 (Atom2 m x) (Atom2 m' y) = (m = m' \<and> x = y)"
| "eq_mrexp2 (Plus2 r1 s1 _ _) (Plus2 r2 s2 _ _) = (eq_mrexp2 r1 r2 \<and> eq_mrexp2 s1 s2)"
| "eq_mrexp2 (Times2 r1 s1 _ _) (Times2 r2 s2 _ _) = (eq_mrexp2 r1 r2 \<and> eq_mrexp2 s1 s2)"
| "eq_mrexp2 (Star2 r1 _) (Star2 r2 _) = (eq_mrexp2 r1 r2)"
| "eq_mrexp2 r s = False"

lemma eq_mrexp2_imp_eq: "\<lbrakk>eq_mrexp2 r s; ok2 r; ok2 s\<rbrakk> \<Longrightarrow> (r = s)"
  by (induct rule: eq_mrexp2.induct) auto

lemma eq_mrexp2_refl[simplified, simp]: "r = s \<Longrightarrow> eq_mrexp2 r s"
  by (induct rule: eq_mrexp2.induct) auto

lemma eq_mrexp2_eq: "\<lbrakk>ok2 r; ok2 s\<rbrakk> \<Longrightarrow> eq_mrexp2 r s = (r = s)"
  by (metis eq_mrexp2_imp_eq eq_mrexp2_refl)

lift_definition equal_ok_mrexp2 :: "'a ok_mrexp2 \<Rightarrow> 'a ok_mrexp2 \<Rightarrow> bool"
   is "\<lambda>(b1,r1) (b2, r2). b1 = b2 \<and> eq_mrexp2 r1 r2" .

instance by intro_classes (transfer, auto simp: eq_mrexp2_eq)

end

global_interpretation after2: rexp_DFA init_okm delta_okm nullable_okm lang_okm
  defines after2_closure = after2.closure
    and check_eqv_a2 = after2.check_eqv
    and reachable_a2 = after2.reachable
    and automaton_a2 = after2.automaton
    and match_a2 = after2.match
proof (standard, goal_cases)
  case (1 r) show "lang_okm (init_okm r) = lang r"
    by transfer (auto simp: split_beta init_a_def nonfinal_empty_mrexp Lm_follow Lm_empty
      map_map_rexp nullable_iff)
next
  case (2 a br) show "lang_okm (delta_okm a br) = Deriv a (lang_okm br)"
    apply transfer
    unfolding split_beta fst_conv snd_conv mem_Collect_eq after.L_delta[symmetric] delta_a.simps
      shift_read_follow[symmetric]
    by (subst strip2_shift2) simp_all
next
  case (3 br) show  "nullable_okm br = ([] \<in> lang_okm br)"
    by transfer (simp add: split_beta)
next
  case (4 s)
  have "{fold (\<lambda>a (m, r). (False, shift2 m r a)) w (True, empty_mrexp2 s) |w. True} \<subseteq>
    UNIV \<times> mrexps2 s"
  proof (intro subsetI, elim CollectE exE conjE, hypsubst)
    fix w show "fold (\<lambda>a (m, r). (False, shift2 m r a)) w (True, empty_mrexp2 s) \<in>
      UNIV \<times> mrexps2 s"
    by (induct w rule: rev_induct) (auto simp: split: prod.splits intro!: shift2_mrexps2)
  qed
  then show "finite {fold delta_okm w (init_okm s) |w. True}"
    by transfer (erule finite_subset[OF subset_trans[rotated]], auto)
qed

(*<*)
end
(*>*)
