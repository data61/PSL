section \<open>Word Problem for Context-Free Grammars\<close>
(*<*)
theory Context_Free_Grammar
imports Coinductive_Language "HOL-Library.FSet"
begin
(*>*)


section \<open>Context Free Languages\<close>

text \<open>
A context-free grammar consists of a list of productions for every nonterminal
and an initial nonterminal. The productions are required to be in weak Greibach
normal form, i.e. each right hand side of a production must either be empty or
start with a terminal.
\<close>

abbreviation "wgreibach \<alpha> \<equiv> (case \<alpha> of (Inr N # _) \<Rightarrow> False | _ \<Rightarrow> True)"

record ('t, 'n) cfg =
  init :: "'n :: finite"
  prod :: "'n \<Rightarrow> ('t + 'n) list fset"

context
  fixes G :: "('t, 'n :: finite) cfg"
begin

inductive in_cfl where
  "in_cfl [] []"
| "in_cfl \<alpha> w \<Longrightarrow> in_cfl (Inl a # \<alpha>) (a # w)"
| "fBex (prod G N) (\<lambda>\<beta>. in_cfl (\<beta> @ \<alpha>) w) \<Longrightarrow> in_cfl (Inr N # \<alpha>) w"

abbreviation lang_trad where
  "lang_trad \<equiv> {w. in_cfl [Inr (init G)] w}"

fun \<oo>\<^sub>P where
  "\<oo>\<^sub>P [] = True"
| "\<oo>\<^sub>P (Inl _ # _) = False"
| "\<oo>\<^sub>P (Inr N # \<alpha>) = ([] |\<in>| prod G N \<and> \<oo>\<^sub>P \<alpha>)"

fun \<dd>\<^sub>P where
  "\<dd>\<^sub>P [] a = {||}"
| "\<dd>\<^sub>P (Inl b # \<alpha>) a = (if a = b then {|\<alpha>|} else {||})"
| "\<dd>\<^sub>P (Inr N # \<alpha>) a =
    (\<lambda>\<beta>. tl \<beta> @ \<alpha>) |`| ffilter (\<lambda>\<beta>. \<beta> \<noteq> [] \<and> hd \<beta> = Inl a) (prod G N) |\<union>|
    (if [] |\<in>| prod G N then \<dd>\<^sub>P \<alpha> a else {||})"

primcorec subst :: "('t + 'n) list fset \<Rightarrow> 't language" where
  "subst P = Lang (fBex P \<oo>\<^sub>P) (\<lambda>a. subst (ffUnion ((\<lambda>r. \<dd>\<^sub>P r a) |`| P)))"

inductive in_cfls where
  "fBex P \<oo>\<^sub>P \<Longrightarrow> in_cfls P []"
| "in_cfls (ffUnion ((\<lambda>\<alpha>. \<dd>\<^sub>P \<alpha> a) |`| P)) w \<Longrightarrow> in_cfls P (a # w)"

inductive_cases [elim!]: "in_cfls P []"
inductive_cases [elim!]: "in_cfls P (a # w)"

declare inj_eq[OF bij_is_inj[OF to_language_bij], simp]

lemma subst_in_cfls: "subst P = to_language {w. in_cfls P w}"
  by (coinduction arbitrary: P) (auto intro: in_cfls.intros)

lemma \<oo>\<^sub>P_in_cfl: "\<oo>\<^sub>P \<alpha> \<Longrightarrow> in_cfl \<alpha> []"
  by (induct \<alpha> rule: \<oo>\<^sub>P.induct) (auto intro!: in_cfl.intros elim: fBexI[rotated])

lemma \<dd>\<^sub>P_in_cfl: "\<beta> |\<in>| \<dd>\<^sub>P \<alpha> a \<Longrightarrow> in_cfl \<beta> w \<Longrightarrow> in_cfl \<alpha> (a # w)"
proof (induct \<alpha> a arbitrary: \<beta> w rule: \<dd>\<^sub>P.induct)
  case (3 N \<alpha> a)
  then show ?case
    by (auto simp: rev_fBexI neq_Nil_conv split: if_splits
      intro!: in_cfl.intros  elim!: rev_fBexI[of "_ # _"])
qed (auto split: if_splits intro: in_cfl.intros)

lemma in_cfls_in_cfl: "in_cfls P w \<Longrightarrow> fBex P (\<lambda>\<alpha>. in_cfl \<alpha> w)"
  by (induct P w rule: in_cfls.induct)
    (auto simp: \<oo>\<^sub>P_in_cfl \<dd>\<^sub>P_in_cfl ffUnion.rep_eq fmember.rep_eq fBex.rep_eq fBall.rep_eq
      intro: in_cfl.intros elim: rev_bexI)

lemma in_cfls_mono: "in_cfls P w \<Longrightarrow> P |\<subseteq>| Q \<Longrightarrow> in_cfls Q w"
proof (induct P w arbitrary: Q rule: in_cfls.induct)
  case (2 a P w)
  from 2(3) 2(2)[of "ffUnion ((\<lambda>\<alpha>. local.\<dd>\<^sub>P \<alpha> a) |`| Q)"] show ?case
    by (auto intro!: ffunion_mono in_cfls.intros)
qed (auto intro!: in_cfls.intros)

end

locale cfg_wgreibach =
  fixes G :: "('t, 'n :: finite) cfg"
  assumes weakGreibach: "\<And>N \<alpha>. \<alpha> |\<in>| prod G N \<Longrightarrow> wgreibach \<alpha>"
begin

lemma in_cfl_in_cfls: "in_cfl G \<alpha> w \<Longrightarrow> in_cfls G {|\<alpha>|} w"
proof (induct \<alpha> w rule: in_cfl.induct)
  case (3 N \<alpha> w)
  then obtain \<beta> where
    \<beta>: "\<beta> |\<in>| prod G N" and
    in_cfl: "in_cfl G (\<beta> @ \<alpha>) w" and
    in_cfls: "in_cfls G {|\<beta> @ \<alpha>|} w" by blast
  then show ?case
  proof (cases \<beta>)
    case [simp]: Nil
    from \<beta> in_cfls show ?thesis
       by (cases w) (auto intro!: in_cfls.intros elim: in_cfls_mono)
  next
    case [simp]: (Cons x \<gamma>)
    from weakGreibach[OF \<beta>] obtain a where [simp]: "x = Inl a" by (cases x) auto
    with \<beta> in_cfls show ?thesis
      apply -
      apply (rule  in_cfl.cases[OF in_cfl]; auto)
      apply (force intro: in_cfls.intros(2) elim!: in_cfls_mono)
      done
  qed
qed (auto intro!: in_cfls.intros)

abbreviation lang where
  "lang \<equiv> subst G {|[Inr (init G)]|}"

lemma lang_lang_trad: "lang = to_language (lang_trad G)"
proof -
  have "in_cfls G {|[Inr (init G)]|} w \<longleftrightarrow> in_cfl G [Inr (init G)] w" for w
    by (auto dest: in_cfls_in_cfl in_cfl_in_cfls)
  then show ?thesis
    by (auto simp: subst_in_cfls)
qed

end

text \<open>
The function @{term in_language} decides the word problem for a given language.
Since we can construct the language of a CFG using @{const cfg_wgreibach.lang} we obtain an
executable (but not very efficient) decision procedure for CFGs for free.
\<close>

abbreviation "\<aa> \<equiv> Inl True"
abbreviation "\<bb> \<equiv> Inl False"
abbreviation "S \<equiv> Inr ()"

interpretation palindromes: cfg_wgreibach "\<lparr>init = (), prod = \<lambda>_. {|[], [\<aa>], [\<bb>], [\<aa>, S, \<aa>], [\<bb>, S, \<bb>]|}\<rparr>"
  by unfold_locales auto

lemma "in_language palindromes.lang []" by normalization
lemma "in_language palindromes.lang [True]" by normalization
lemma "in_language palindromes.lang [False]" by normalization
lemma "in_language palindromes.lang [True, True]" by normalization
lemma "in_language palindromes.lang [True, False, True]" by normalization
lemma "\<not> in_language palindromes.lang [True, False]" by normalization
lemma "\<not> in_language palindromes.lang [True, False, True, False]" by normalization
lemma "in_language palindromes.lang [True, False, True, True, False, True]" by normalization
lemma "\<not> in_language palindromes.lang [True, False, True, False, False, True]" by normalization

interpretation Dyck: cfg_wgreibach "\<lparr>init = (), prod = \<lambda>_. {|[], [\<aa>, S, \<bb>, S]|}\<rparr>"
  by unfold_locales auto
lemma "in_language Dyck.lang []" by normalization
lemma "\<not> in_language Dyck.lang [True]" by normalization
lemma "\<not> in_language Dyck.lang [False]" by normalization
lemma "in_language Dyck.lang [True, False, True, False]" by normalization
lemma "in_language Dyck.lang [True, True, False, False]" by normalization
lemma "in_language Dyck.lang [True, False, True, False]" by normalization
lemma "in_language Dyck.lang [True, False, True, False, True, True, False, False]" by normalization
lemma "\<not> in_language Dyck.lang [True, False, True, True, False]" by normalization
lemma "\<not> in_language Dyck.lang [True, True, False, False, False, True]" by normalization

interpretation abSSa: cfg_wgreibach "\<lparr>init = (), prod = \<lambda>_. {|[], [\<aa>, \<bb>, S, S, \<aa>]|}\<rparr>"
  by unfold_locales auto
lemma "in_language abSSa.lang []" by normalization
lemma "\<not> in_language abSSa.lang [True]" by normalization
lemma "\<not> in_language abSSa.lang [False]" by normalization
lemma "in_language abSSa.lang [True, False, True]" by normalization
lemma "in_language abSSa.lang [True, False, True, False, True, True, False, True, True]" by normalization
lemma "in_language abSSa.lang [True, False, True, False, True, True]" by normalization
lemma "\<not> in_language abSSa.lang [True, False, True, True, False]" by normalization
lemma "\<not> in_language abSSa.lang [True, True, False, False, False, True]" by normalization

(*<*)
end
(*>*)