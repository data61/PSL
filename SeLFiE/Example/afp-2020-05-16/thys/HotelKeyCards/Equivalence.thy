(*<*)
theory Equivalence
imports State Trace
begin

lemma [simp]: "safe [] = (%r. False)"
by(simp add:Trace.safe_def fun_eq_iff)

lemma [simp]: "safe (Exit g r # t) r' = safe t r'"
apply(simp add:Trace.safe_def)
apply(rule iffI)
 apply clarsimp
 apply(case_tac s\<^sub>3) apply simp
 apply clarsimp
 apply(rule_tac x = s\<^sub>1 in exI)
 apply(rule_tac x = s\<^sub>2 in exI)
 apply simp
apply clarsimp
apply(rule_tac x = s\<^sub>1 in exI)
apply(rule_tac x = s\<^sub>2 in exI)
apply simp
done

lemma [simp]: "\<not> safe (Check_in g r c # t) r"
apply(clarsimp simp add:Trace.safe_def)
apply(case_tac s\<^sub>3) apply simp
apply(cases c)
apply auto
done

lemma [simp]: "r \<noteq> r' \<Longrightarrow> safe (Check_in g r' c # t) r = safe t r"
apply(simp add:Trace.safe_def)
apply(rule iffI)
 apply clarsimp
 apply(case_tac s\<^sub>3) apply simp
 apply clarsimp
 apply(rule_tac x = s\<^sub>1 in exI)
 apply(rule_tac x = s\<^sub>2 in exI)
 apply simp
apply clarsimp
apply(rule_tac x = s\<^sub>1 in exI)
apply(rule_tac x = s\<^sub>2 in exI)
apply simp
done



lemma [simp]: "r \<noteq> r' \<Longrightarrow> safe (Enter g r' c # t) r = safe t r"
apply(simp add:Trace.safe_def)
apply(rule iffI)
 apply clarsimp
 apply(case_tac s\<^sub>3) apply simp
 apply clarsimp
 apply(rule_tac x = s\<^sub>1 in exI)
 apply(rule_tac x = s\<^sub>2 in exI)
 apply simp
apply clarsimp
apply(rule_tac x = s\<^sub>1 in exI)
apply(rule_tac x = s\<^sub>2 in exI)
apply simp
done

lemma reach_cong: "r : reach \<Longrightarrow> r = r' \<Longrightarrow> r' : reach"
by simp

lemma cards_app: "cards (s @ s') g = cards s g \<union> cards s' g"
by (induct s) (auto split:event.split)


lemma ownsD: "owns s r = Some g \<Longrightarrow>
 \<exists>s\<^sub>1 s\<^sub>2 c. s = s\<^sub>2 @ [Check_in g r c] @ s\<^sub>1 \<and> no_Check_in s\<^sub>2 r"
apply(induct s)
 apply simp
apply (auto split:event.splits)
apply(rule_tac x = s in exI)
apply(rule_tac x = "[]" in exI)
apply simp
apply(rule_tac x = s\<^sub>1 in exI)
apply simp
apply(rule_tac x = s\<^sub>1 in exI)
apply simp
apply(rule_tac x = s\<^sub>1 in exI)
apply simp
done

lemma [simp]: "safe t r \<Longrightarrow> safe (Enter g r c # t) r"
apply(clarsimp simp:Trace.safe_def)
apply(rule_tac x = s\<^sub>1 in exI)
apply(rule_tac x = s\<^sub>2 in exI)
apply simp
done

lemma same_key2D:
"hotel (s\<^sub>2 @ Check_in g r (k\<^sub>2,k) # s\<^sub>1) \<Longrightarrow>
 (k\<^sub>1,k) : cards(s\<^sub>2 @ Check_in g r (k\<^sub>2,k) # s\<^sub>1) g' \<Longrightarrow> g=g' \<and> k\<^sub>1=k\<^sub>2"
apply(induct s\<^sub>2)
apply clarsimp
using [[simp_depth_limit = 5]]
apply (auto simp:issued_app split:event.splits)
done


lemma safe_Enter[simp]: "hotel (Enter g r (k,k') # t) \<Longrightarrow>
 safe (Enter g r (k,k') # t) r =
 (owns t r = \<lfloor>g\<rfloor> \<and> isin t r = {} \<and> k' = currk t r \<or> safe t r)"
 apply rule
 apply(frule_tac g=g in Trace.safe, assumption) apply simp
 apply(clarsimp simp add:Trace.safe_def)
 apply(case_tac s\<^sub>3)
  apply clarsimp
 apply simp
 apply blast
  apply(erule disjE)
   prefer 2 apply fastforce
  apply (erule conjE)+
  apply(drule ownsD)
  apply(clarsimp simp add:Trace.safe_def)
  apply(frule (1) same_key2D)
  apply(rule_tac x = s\<^sub>1 in exI)
  apply(rule_tac x = s\<^sub>2 in exI)
  apply(rule_tac x = "[]" in exI)
  apply clarsimp
done

lemma hotel_reach: "inj initk \<Longrightarrow> hotel t \<Longrightarrow> \<lparr> state.owns = owns t,
 state.currk = currk t,
 state.issued = issued t,
 state.cards = cards t,
 state.roomk = roomk t,
 state.isin = isin t,
 state.safe = (%r. safe t r \<or> owns t r =  None)\<rparr> : reach"
apply(induct t)
 apply simp
 apply(insert State.init[where initk=initk])[1]
 apply simp
 apply(erule reach_cong)
 apply (simp add: fun_eq_iff)

apply (clarsimp split:event.splits)
prefer 3
apply(drule exit_room)
apply simp
apply(erule reach_cong)
apply (simp add: fun_eq_iff)

apply(rename_tac guest room key)
apply(drule_tac g = guest and r = room in check_in)
apply simp
apply(erule reach_cong)
apply (simp add: fun_eq_iff)

apply(rename_tac guest room key1 key2)
apply(drule_tac g = guest and r = room in enter_room) apply simp apply simp
apply(erule reach_cong)
apply (fastforce simp add: fun_eq_iff)
done

lemma reach_hotel: "s : reach \<Longrightarrow>
 \<exists>t ik. initk = ik \<longrightarrow> hotel t \<and>
 state.cards s = cards t \<and>
 state.isin s =  isin t \<and>
 state.roomk s = roomk t \<and> state.owns s = owns t \<and>
 state.currk s = currk t \<and>
 state.issued s = issued t \<and>
 state.safe s = (\<lambda>r. safe t r \<or> owns t r = None)"
apply(erule reach.induct)
 apply(rule_tac x = "[]" in exI)
 apply fastforce
apply clarsimp
apply(rule_tac x = "Check_in g r (currk t r,k) # t" in exI)
apply (simp add: fun_eq_iff [where 'a=room] fun_eq_iff [where 'a=guest])
apply (clarsimp simp add: fun_eq_iff [where 'a=room] fun_eq_iff [where 'a=guest and 'b="(key \<times> key) set"])
apply(erule disjE)
apply clarsimp
apply(rule_tac x = "Enter g r (roomk t r,k') # t" in exI)
apply clarsimp
apply clarsimp
apply(rule_tac x = "Enter g r (k, roomk t r) # t" in exI)
apply clarsimp
apply clarsimp
apply(rule_tac x = "Exit g r # t" in exI)
apply (clarsimp simp add: fun_eq_iff [where 'a=room] fun_eq_iff [where 'a=guest and 'b="(key \<times> key) set"])
done
(*>*)

section\<open>Equivalence\<close>

text\<open>Although the state based and the trace based model look similar
enough, the
nagging feeling remains that they could be subtly different. Hence I
wanted to show the equivalence formally. This was very fortunate,
because it revealed some unintended discrepancies (no longer
present). Although I had proved both systems safe, it turned out that
the state based version of safety was more restrictive than the trace
based one. In the state based version of \<open>safe\<close> the room had to
be empty the first time the owner enters with the latest card, whereas
in the trace based version any time the owner enters with the latest
card can make a room safe.  Such errors in an automaton checking a
trace property are very common and show the superiority of the trace
based formalism.

When comparing the two models we have to take two slight differences
into account:
\begin{itemize}

\item The initial setting of the room keys @{const Trace.initk} in the
trace based model is an arbitrary but fixed value.  In the state based
model any injective initial value is fine.

\item As a consequence (see the end of
Section~\ref{sec:FormalSafetyTrace}) @{const state.safe} is initially
true whereas @{const Trace.safe} is initially false.

\end{itemize}
Since many names occur in both models they are disambiguated by the
prefixes \<open>state\<close> and \<open>Trace\<close>.

In the one direction I have shown that any hotel trace starting
with an injective @{const initk} gives rise to a reachable state
when the components of that state are computed by the trace functions:
@{thm[display]hotel_reach}

Conversely, for any reachable state there is a hotel trace leading to it:
@{thm[display]reach_hotel}
The precondition @{prop"initk = ik"} just says that we can find some
interpretation for @{const initk} that works, namely the one that was
chosen as the initial setting for the keys in @{term s}.

\sloppy
The proofs are almost automatic, except for the \<open>safe\<close>
component. In essence, we have to show that the procedural @{const
state.safe} implements the declarative @{const Trace.safe}. The proof
was complicated by the fact that initially it was not true and I had
to debug @{const Trace.safe} by proof.
Unfortunately Isabelle's current counterexample
finders~\cite{BerghoferN-SEFM04,Weber05bounded}
did not seem to work here due to search space reasons.
Once the bugs were ironed out, the following key lemma,
together with some smaller lemmas,
automated the correspondence proof for \<open>safe\<close>:
@{thm[display]safe_Enter}
In addition we used many lemmas from the trace model, including
Theorem~\ref{safe}.
\fussy

\<close>

(*<*)
end
(*>*)
