(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "The Monty Hall Problem"

theory Monty imports "../pGCL" begin

text \<open>
We now tackle a more substantial example, allowing us to demonstrate
the tools for compositional reasoning and the use of invariants in
non-recursive programs.  Our example is the well-known Monty Hall puzzle
in statistical inference \citep{Selvin_75}.

The setting is a game show:  There is a prize hidden behind one
of three doors, and the contestant is invited to choose one.  Once
the guess is made, the host than opens one of the remaining two 
doors, revealing a goat and showing that the prize is elsewhere.  The
contestent is then given the choice of switching their guess to the
other unopened door, or sticking to their first guess.

The puzzle is whether the contestant is better off switching or
staying put; or indeed whether it makes a difference at all.  Most people's
intuition suggests that it make no difference, whereas in fact,
switching raises the chance of success from 1/3 to 2/3.
\<close>

subsection \<open>The State Space\<close>

text \<open>The game state consists of the prize location, the guess,
and the clue (the door the host opens).  These are not constrained a
priori to the range @{term "{1::real,2,3}"}, but are simply natural numbers:
We instead show that this is in fact an invariant.
\<close>

record game =
  prize  :: nat
 "guess" :: nat
  clue   :: nat

text \<open>The victory condition: The player wins if they have guessed the
  correct door, when the game ends.\<close>
definition player_wins :: "game \<Rightarrow> bool"
where "player_wins g \<equiv> guess g = prize g"

subsubsection \<open>Invariants\<close>

text \<open>We prove explicitly that only valid doors are ever chosen.\<close>

definition inv_prize :: "game \<Rightarrow> bool"
where "inv_prize g \<equiv> prize g \<in> {1,2,3}"

definition inv_clue :: "game \<Rightarrow> bool"
where "inv_clue g \<equiv> clue g \<in> {1,2,3}"

definition inv_guess :: "game \<Rightarrow> bool"
where "inv_guess g \<equiv> guess g \<in> {1,2,3}"

subsection \<open>The Game\<close>

text \<open>Hide the prize behind door @{term D}.\<close>
definition hide_behind :: "nat \<Rightarrow> game prog"
where "hide_behind D \<equiv> Apply (prize_update (\<lambda>x. D))"

text \<open>Choose door @{term D}.\<close>
definition guess_behind :: "nat \<Rightarrow> game prog"
where "guess_behind D \<equiv> Apply (guess_update (\<lambda>x. D))"

text \<open>Open door @{term D} and reveal what's behind.\<close>
definition open_door :: "nat \<Rightarrow> game prog"
where "open_door D \<equiv> Apply (clue_update (\<lambda>x. D))"

text \<open>Hide the prize behind door 1, 2 or 3, demonically i.e.~according
  to any probability distribution (or none).\<close>
definition hide_prize :: "game prog"
where "hide_prize \<equiv> hide_behind 1 \<Sqinter> hide_behind 2 \<Sqinter> hide_behind 3"

text \<open>Guess uniformly at random.\<close>
definition make_guess :: "game prog"
where "make_guess \<equiv> guess_behind 1 \<^bsub>(\<lambda>s. 1/3)\<^esub>\<oplus>
                    guess_behind 2 \<^bsub>(\<lambda>s. 1/2)\<^esub>\<oplus> guess_behind 3"

text \<open>Open one of the two doors that \emph{doesn't} hide the prize.\<close>
definition reveal :: "game prog"
where "reveal \<equiv> \<Sqinter>d\<in>(\<lambda>s. {1,2,3} - {prize s, guess s}). open_door d"

text \<open>Switch your guess to the other unopened door.\<close>
definition switch_guess :: "game prog"
where "switch_guess \<equiv> \<Sqinter>d\<in>(\<lambda>s. {1,2,3} - {clue s, guess s}). guess_behind d"

text \<open>The complete game, either with or without switching guesses.\<close>
definition monty :: "bool \<Rightarrow> game prog"
where
  "monty switch \<equiv> hide_prize ;;
                  make_guess ;;
                  reveal ;;
                  (if switch then switch_guess else Skip)"

subsection \<open>A Brute Force Solution\<close>

text \<open>For sufficiently simple programs, we can calculate the exact weakest
  pre-expectation by unfolding.\<close>

lemma eval_win[simp]:
  "p = g \<Longrightarrow> \<guillemotleft>player_wins\<guillemotright> (s\<lparr> prize := p, guess := g, clue := c \<rparr>) = 1"
  by(simp add:embed_bool_def player_wins_def)

lemma eval_loss[simp]:
  "p \<noteq> g \<Longrightarrow> \<guillemotleft>player_wins\<guillemotright> (s\<lparr> prize := p, guess := g, clue := c \<rparr>) = 0"
  by(simp add:embed_bool_def player_wins_def)

text \<open>If they stick to their guns, the player wins with $p=1/3$.\<close>
lemma wp_monty_noswitch:
  "(\<lambda>s. 1/3) = wp (monty False) \<guillemotleft>player_wins\<guillemotright>"
  unfolding monty_def hide_prize_def make_guess_def reveal_def
            hide_behind_def guess_behind_def open_door_def
            switch_guess_def
  by(simp add:wp_eval insert_Diff_if o_def)

lemma swap_upd:
  "s\<lparr> prize := p, clue := c, guess := g \<rparr> =
   s\<lparr> prize := p, guess := g, clue := c \<rparr>"
  by(simp)

text \<open>If they switch, they win with $p=2/3$.  Brute force here
  takes longer, but is still feasible.  On larger programs,
  this will rapidly become impossible, as the size of the terms
  (generally) grows exponentially with the length of the program.\<close>

lemma wp_monty_switch_bruteforce:
  "(\<lambda>s. 2/3) = wp (monty True) \<guillemotleft>player_wins\<guillemotright>"
  unfolding monty_def hide_prize_def make_guess_def reveal_def
            hide_behind_def guess_behind_def open_door_def
            switch_guess_def
  \<comment> \<open>Note that this is getting slow\<close>
  by (simp add: wp_eval insert_Diff_if swap_upd o_def cong del: INF_cong_simp)

subsection \<open>A Modular Approach\<close>

text \<open>We can solve the problem more efficiently, at the cost of
  a little more user effort, by breaking up the problem and annotating
  each step of the game separately.  While this is not strictly necessary
  for this program, it will scale to larger examples, as the work in
  annotation only increases linearly with the length of the program.\<close>

subsubsection \<open>Healthiness\<close>

text \<open>We first establish healthiness for each step. This follows
  straightforwardly by applying the supplied rulesets.\<close>

lemma wd_hide_prize:
  "well_def hide_prize"
  unfolding hide_prize_def hide_behind_def
  by(simp add:wd_intros)

lemma wd_make_guess:
  "well_def make_guess"
  unfolding make_guess_def guess_behind_def
  by(simp add:wd_intros)

lemma wd_reveal:
  "well_def reveal"
proof -
  txt \<open>Here, we do need a subsidiary lemma: that there is always
    a `fresh' door available.  The rest of the healthiness proof follows
    as usual.\<close>
  have "\<And>s. {1, 2, 3} - {prize s, guess s} \<noteq> {}"
    by(auto simp:insert_Diff_if)
  thus ?thesis
    unfolding reveal_def open_door_def
    by(intro wd_intros, auto)
qed

lemma wd_switch_guess:
  "well_def switch_guess"
proof -
  have "\<And>s. {1, 2, 3} - {clue s, guess s} \<noteq> {}"
    by(auto simp:insert_Diff_if)
  thus ?thesis
    unfolding switch_guess_def guess_behind_def
    by(intro wd_intros, auto)
qed

lemmas monty_healthy =
  wd_switch_guess wd_reveal wd_make_guess wd_hide_prize

subsubsection \<open>Annotations\<close>

text \<open>We now annotate each step individually, and then combine them to
  produce an annotation for the entire program.\<close>

text \<open>@{term hide_prize} chooses a valid door.\<close>
lemma wp_hide_prize:
  "(\<lambda>s. 1) \<tturnstile> wp hide_prize \<guillemotleft>inv_prize\<guillemotright>"
  unfolding hide_prize_def hide_behind_def wp_eval o_def
  by(simp add:embed_bool_def inv_prize_def)

text \<open>Given the prize invariant, @{term make_guess} chooses a valid
  door, and guesses incorrectly with probability at least 2/3.\<close>
lemma wp_make_guess:
  "(\<lambda>s. 2/3 * \<guillemotleft>\<lambda>g. inv_prize g\<guillemotright> s) \<tturnstile>
   wp make_guess \<guillemotleft>\<lambda>g. guess g \<noteq> prize g \<and> inv_prize g \<and> inv_guess g\<guillemotright>"
  unfolding make_guess_def guess_behind_def wp_eval o_def
  by(auto simp:embed_bool_def inv_prize_def inv_guess_def)

lemma last_one:
  assumes "a \<noteq> b" and "a \<in> {1::nat,2,3}" and "b \<in> {1,2,3}"
  shows "\<exists>!c. {1,2,3} - {b,a} = {c}"
  apply(simp add:insert_Diff_if)
  using assms by(auto intro:assms)

text \<open>Given the composed invariants, and an incorrect guess, @{term reveal}
  will give a clue that is neither the prize, nor the guess.\<close>
lemma wp_reveal:
  "\<guillemotleft>\<lambda>g. guess g \<noteq> prize g \<and> inv_prize g \<and> inv_guess g\<guillemotright> \<tturnstile>
   wp reveal \<guillemotleft>\<lambda>g. guess g \<noteq> prize g \<and>
                  clue g \<noteq> prize g \<and>
                  clue g \<noteq> guess g \<and>
                  inv_prize g \<and> inv_guess g \<and> inv_clue g\<guillemotright>"
  (is "?X \<tturnstile> wp reveal ?Y")
proof(rule use_premise, rule well_def_wp_healthy[OF wd_reveal], clarify)
  fix s
  assume "guess s \<noteq> prize s"
     and "inv_prize s"
     and "inv_guess s"
  moreover then obtain c
    where singleton: "{Suc 0,2,3} -  {prize s, guess s} = {c}"
      and "c \<noteq> prize s"
      and "c \<noteq> guess s"
      and "c \<in> {Suc 0,2,3}"
    unfolding inv_prize_def inv_guess_def
    by(force dest:last_one elim!:ex1E)
  ultimately show "1 \<le> wp reveal ?Y s"
    by(simp add:reveal_def open_door_def wp_eval singleton o_def
                embed_bool_def inv_prize_def inv_guess_def inv_clue_def)
qed

text \<open>Showing that the three doors are all district is a largeish
  first-order problem, for which sledgehammer gives us a reasonable
  script.\<close>
lemma distinct_game:
  "\<lbrakk> guess g \<noteq> prize g; clue g \<noteq> prize g; clue g \<noteq> guess g;
     inv_prize g; inv_guess g; inv_clue g \<rbrakk> \<Longrightarrow> 
   {1, 2, 3} = {guess g, prize g, clue g}"
  unfolding inv_prize_def inv_guess_def inv_clue_def
  apply(rule set_eqI)
  apply(rule iffI)
   apply(clarify)
   apply(metis (full_types) empty_iff insert_iff)
  apply(metis insert_iff)
  done

text \<open>Given the invariants, switching from the wrong guess gives
  the right one.\<close>
lemma wp_switch_guess:
  "\<guillemotleft>\<lambda>g. guess g \<noteq> prize g \<and> clue g \<noteq> prize g \<and> clue g \<noteq> guess g \<and>
        inv_prize g \<and> inv_guess g \<and> inv_clue g\<guillemotright> \<tturnstile>
   wp switch_guess \<guillemotleft>player_wins\<guillemotright>"
proof(rule use_premise, safe)
  from wd_switch_guess show "healthy (wp switch_guess)" by(auto)

  fix s
  assume "guess s \<noteq> prize s" and "clue s \<noteq> prize s"
     and "clue s \<noteq> guess s" and "inv_prize s"
     and "inv_guess s" and "inv_clue s"
  note state = this
  hence "1 \<le> Inf ((\<lambda>a. \<guillemotleft> player_wins \<guillemotright> (s\<lparr>guess := a\<rparr>)) `
    ({guess s, prize s, clue s} - {clue s, guess s}))"
    by(auto simp:insert_Diff_if player_wins_def)
  also from state
  have "... = Inf ((\<lambda>a. \<guillemotleft> player_wins \<guillemotright> (s\<lparr>guess := a\<rparr>)) `
                  ({1, 2, 3} - {clue s, guess s}))"
    by(simp add:distinct_game[symmetric])
  also have "... = wp switch_guess \<guillemotleft>player_wins\<guillemotright> s"
    by(simp add:switch_guess_def guess_behind_def wp_eval o_def)
  finally show "1 \<le> wp switch_guess \<guillemotleft> player_wins \<guillemotright> s" .
qed

text \<open>Given componentwise specifications, we can glue them together
with calculational reasoning to get our result.\<close>
lemma wp_monty_switch_modular:
  "(\<lambda>s. 2/3) \<tturnstile> wp (monty True) \<guillemotleft>player_wins\<guillemotright>"
proof(rule wp_validD)  \<comment> \<open>Work in probabilistic Hoare triples\<close>
  note wp_validI[OF wp_scale, OF wp_hide_prize, simplified]
    \<comment> \<open>Here we apply scaling to match our pre-expectation\<close>
  also note wp_validI[OF wp_make_guess]
  also note wp_validI[OF wp_reveal]
  also note wp_validI[OF wp_switch_guess]
  finally show "\<lbrace>\<lambda>s. 2/3\<rbrace> monty True \<lbrace>\<guillemotleft>player_wins\<guillemotright>\<rbrace>p"
    unfolding monty_def
    by(simp add:wd_intros sound_intros monty_healthy)
qed

subsubsection \<open>Using the VCG\<close>

lemmas scaled_hide = wp_scale[OF wp_hide_prize, simplified]
declare scaled_hide[pwp] wp_make_guess[pwp] wp_reveal[pwp] wp_switch_guess[pwp]
declare wd_hide_prize[wd] wd_make_guess[wd] wd_reveal[wd] wd_switch_guess[wd]

text \<open>Alternatively, the VCG will get this using the same annotations.\<close>
lemma wp_monty_switch_vcg:
  "(\<lambda>s. 2/3) \<tturnstile> wp (monty True) \<guillemotleft>player_wins\<guillemotright>"
  unfolding monty_def
  by(simp, pvcg)

end
