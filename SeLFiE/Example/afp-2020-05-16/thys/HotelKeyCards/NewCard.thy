(*  Title:      State based hotel key card system with "new card"

    Author:     Tobias Nipkow, TU Muenchen

Like State.thy but with additional features: cards can be lost and new
ones can be issued. Cannot build on State.thy because record state
needs to be extended with a new field. This would require explaining
Isabelle's record inheritance. An interesting project, but not now.
*)

(*<*)
theory NewCard
imports Main
begin

abbreviation
 "SomeFloor" ("(\<lfloor>_\<rfloor>)") where "\<lfloor>x\<rfloor> \<equiv> Some x"

declare if_split_asm[split]

typedecl guest
typedecl key
type_synonym card = "key * key"
typedecl room

record state =
 (* reception: *)
 owns :: "room \<Rightarrow> guest option"
 prevk :: "room \<Rightarrow> key"
 currk :: "room \<Rightarrow> key"
 issued :: "key set"
 (* guests: *)
 cards :: "guest \<Rightarrow> card set"
 (* rooms: *)
 roomk :: "room \<Rightarrow> key"
 isin :: "room \<Rightarrow> guest set"
 (* ghost variable: *)
 safe :: "room \<Rightarrow> bool"

inductive_set reach :: "state set"
where
init: (* prevk = arbitrary prevents the invariant prevk : issued *)
"\<forall>r r'. (initk r = initk r') = (r = r') \<Longrightarrow>
\<lparr> owns = (\<lambda>r. None), prevk = initk, currk = initk, issued = range initk,
  cards = (\<lambda>g. {}), roomk = initk, isin = (\<lambda>r. {}),
  safe = (\<lambda>r. True) \<rparr> \<in> reach"

| enter_room:
"\<lbrakk> s \<in> reach; (k,k') \<in> cards s g; roomk s r \<in> {k,k'} \<rbrakk> \<Longrightarrow>
s\<lparr> isin := (isin s)(r := isin s r \<union> {g}),
   roomk := (roomk s)(r := k'),
   safe := (safe s)(r := owns s r = \<lfloor>g\<rfloor> \<and> isin s r = {} \<and> k' = currk s r
                              \<or> safe s r)
  \<rparr> \<in> reach"

| exit_room:
"\<lbrakk> s \<in> reach;  g \<in> isin s r \<rbrakk> \<Longrightarrow>
s\<lparr> isin := (isin s)(r := isin s r - {g}) \<rparr> \<in> reach"

| check_in:
"\<lbrakk> s : reach; k \<notin> issued s \<rbrakk> \<Longrightarrow>
 s\<lparr>currk := (currk s)(r := k), prevk := (prevk s)(r := currk s r),
   issued := issued s \<union> {k},
   cards := (cards s)(g := cards s g \<union> {(currk s r, k)}),
   owns :=  (owns s)(r := Some g),
   safe := (safe s)(r := False) \<rparr> : reach"

| loose_card:
"s : reach \<Longrightarrow> c : cards s g \<Longrightarrow>
 s\<lparr>cards := (cards s)(g := cards s g - {c})\<rparr> : reach"

| new_card:
"s : reach \<Longrightarrow> owns s r = Some g \<Longrightarrow>
 s\<lparr>cards := (cards s)(g := cards s g \<union> {(prevk s r, currk s r)})\<rparr> : reach"


lemma currk_issued[simp]: "s : reach \<Longrightarrow> currk s r : issued s"
by (induct set: reach) auto

lemma prevk_issued[simp]: "s : reach \<Longrightarrow> prevk s r : issued s"
by (induct set: reach) auto

lemma key2_issued[simp]: "s : reach \<Longrightarrow> (k,k') : cards s g \<Longrightarrow> k' : issued s"
by (induct set: reach) auto

lemma key1_issued[simp]: "s : reach \<Longrightarrow> (k,k') : cards s g \<Longrightarrow> k : issued s"
by (induct set: reach) auto

lemma roomk_issued[simp]: "s : reach \<Longrightarrow> roomk s k : issued s"
by (induct set: reach) auto

lemma currk_inj[simp]:
 "s : reach \<Longrightarrow> \<forall>r r'. (currk s r = currk s r') = (r = r')"
by (induct set: reach) auto

lemma currk_not_prevk[simp]:
 "s : reach \<Longrightarrow> owns s r' = Some g \<Longrightarrow> currk s r \<noteq> prevk s r'"
by (induct set: reach) auto

lemma key1_not_currk[simp]:
 "s : reach \<Longrightarrow> (currk s r,k') \<notin> cards s g"
by (induct set: reach) auto

lemma key2_not_currk:
 "s : reach \<Longrightarrow> owns s r = Some g \<Longrightarrow> g \<noteq> g' \<Longrightarrow> (k, currk s r) \<notin> cards s g'"
by (induct set: reach) auto

lemma guest_key2_disj2[simp]:
"\<lbrakk> s : reach; (k\<^sub>1,k) \<in> cards s g\<^sub>1; (k\<^sub>2,k) \<in> cards s g\<^sub>2 \<rbrakk> \<Longrightarrow> g\<^sub>1=g\<^sub>2"
by (induct set: reach) (auto simp:key2_not_currk)

lemma safe_roomk_currk[simp]:
 "s : reach \<Longrightarrow> safe s r \<Longrightarrow> roomk s r = currk s r"
by (induct set: reach) auto

lemma only_owner_enter_normal[simp]:
 "\<lbrakk> s : reach; safe s r; (k',roomk s r) \<in> cards s g \<rbrakk> \<Longrightarrow> owns s r = Some g"
by (induct set: reach) auto

theorem "s : reach \<Longrightarrow> safe s r \<Longrightarrow> g : isin s r \<Longrightarrow> owns s r = Some g"
by (induct set: reach) auto

lemmas new_invs = prevk_issued currk_not_prevk key2_not_currk
(*>*)

subsection\<open>An extension\<close>

text\<open>
To test the flexibility of our model we extended it with the
possibility for obtaining a new card, e.g.\ when one has lost one's
card. Now reception needs to remember not just the current but also
the previous key for each room, i.e.\ a new field \<open>prevk :: room
\<Rightarrow> key\<close> is added to @{typ state}. It is initialized with the same value
as @{const currk}: though strictly speaking it could be arbitrary,
this permits the convenient invariant @{prop"prevk s r \<in> issued s"}.
Upon check-in we set \<open>prevk\<close> to \mbox{@{term"(prevk s)(r := currk s r)"}}.
Event \<open>new_card\<close> is simple enough:
@{thm[display] new_card}

The verification is not seriously affected. Some additional
invariants are required
@{thm[display] new_invs}
but the proofs are still of the same trivial induct-auto format.

Adding a further event for loosing a card has no impact at all on the proofs.
\<close>

(*<*)
end
(*>*)
