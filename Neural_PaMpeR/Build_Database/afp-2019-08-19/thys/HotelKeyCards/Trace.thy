(*<*)
theory Trace
imports Basis
begin

declare Let_def[simp] if_split_asm[split]
(*>*)

section\<open>A trace based model\<close>

text\<open>The only clumsy aspect of the state based model is \<open>safe\<close>: we use a state component to record if the sequence of events
that lead to a state satisfies some property. That is, we simulate a
condition on traces via the state. Unsurprisingly, it is not trivial
to convince oneself that \<open>safe\<close> really has the informal meaning
set out at the beginning of subsection~\ref{sec:formalizing-safety}.
Hence we now describe an alternative, purely trace based model,
similar to Paulson's inductive protocol model~\cite{Paulson-JCS98}.
The events are:
\<close>

datatype event =
  Check_in guest room card | Enter guest room card | Exit guest room

text\<open>Instead of a state, we have a trace, i.e.\ list of events, and
extract the state from the trace:\<close>

consts
  initk :: "room \<Rightarrow> key"
   
primrec owns :: "event list \<Rightarrow> room \<Rightarrow> guest option" where
"owns [] r = None" |
"owns (e#s) r = (case e of
 Check_in g r' c \<Rightarrow> if r' = r then Some g else owns s r |
 Enter g r' c \<Rightarrow> owns s r |
 Exit g r' \<Rightarrow> owns s r)"

primrec currk :: "event list \<Rightarrow> room \<Rightarrow> key" where
"currk [] r = initk r" |
"currk (e#s) r = (let k = currk s r in
    case e of Check_in g r' c \<Rightarrow> if r' = r then snd c else k
            | Enter g r' c \<Rightarrow> k
            | Exit g r \<Rightarrow> k)"

primrec issued :: "event list \<Rightarrow> key set" where
"issued [] = range initk" |
"issued (e#s) = issued s \<union>
  (case e of Check_in g r c \<Rightarrow> {snd c} | Enter g r c \<Rightarrow> {} | Exit g r \<Rightarrow> {})"

primrec cards :: "event list \<Rightarrow> guest \<Rightarrow> card set" where
"cards [] g = {}" |
"cards (e#s) g = (let C = cards s g in
                    case e of Check_in g' r c \<Rightarrow> if g' = g then insert c C
                                                else C
                            | Enter g r c \<Rightarrow> C
                            | Exit g r \<Rightarrow> C)"

primrec roomk :: "event list \<Rightarrow> room \<Rightarrow> key" where
"roomk [] r = initk r" |
"roomk (e#s) r = (let k = roomk s r in
    case e of Check_in g r' c \<Rightarrow> k
            | Enter g r' (x,y) \<Rightarrow> if r' = r \<^cancel>\<open>\<and> x = k\<close> then y else k
            | Exit g r \<Rightarrow> k)"

primrec isin :: "event list \<Rightarrow> room \<Rightarrow> guest set" where
"isin [] r = {}" |
"isin (e#s) r = (let G = isin s r in
                 case e of Check_in g r c \<Rightarrow> G
                 | Enter g r' c \<Rightarrow> if r' = r then {g} \<union> G else G
                 | Exit g r' \<Rightarrow> if r'=r then G - {g} else G)"

primrec hotel :: "event list \<Rightarrow> bool" where
"hotel []  = True" |
"hotel (e # s) = (hotel s & (case e of
  Check_in g r (k,k') \<Rightarrow> k = currk s r \<and> k' \<notin> issued s |
  Enter g r (k,k') \<Rightarrow> (k,k') : cards s g & (roomk s r : {k, k'}) |
  Exit g r \<Rightarrow> g : isin s r))"

text\<open>Except for @{const initk}, which is completely unspecified,
all these functions are defined by primitive recursion over traces:
@{thm[display]owns.simps}
@{thm[display]currk.simps}
@{thm[display]issued.simps}
@{thm[display]cards.simps}
@{thm[display]roomk.simps}
@{thm[display]isin.simps}

However, not every trace is possible. Function @{const hotel} tells us
which traces correspond to real hotels:
@{thm[display]hotel.simps}
Alternatively we could have followed Paulson~\cite{Paulson-JCS98}
in defining @{const hotel} as an inductive set of traces.
The difference is only slight.

\subsection{Formalizing safety}
\label{sec:FormalSafetyTrace}

The principal advantage of the trace model is the intuitive
specification of safety. Using the auxiliary predicate \<open>no_Check_in\<close>
\<close>

(*<*)abbreviation no_Check_in :: "event list \<Rightarrow> room \<Rightarrow> bool" where(*>*)
"no_Check_in s r \<equiv> \<not>(\<exists>g c. Check_in g r c \<in> set s)"

text\<open>\medskip\noindent we define a trace to be \<open>safe\<^sub>0\<close> for a
room if the card obtained at the last @{const Check_in} was later
actually used to @{const Enter} the room:\<close>

(*<*)definition safe\<^sub>0 :: "event list \<Rightarrow> room \<Rightarrow> bool" where(*>*)
"safe\<^sub>0 s r = (\<exists>s\<^sub>1 s\<^sub>2 s\<^sub>3 g c.
 s = s\<^sub>3 @ [Enter g r c] @ s\<^sub>2 @ [Check_in g r c] @ s\<^sub>1 \<and> no_Check_in (s\<^sub>3 @ s\<^sub>2) r)"

text\<open>\medskip\noindent A trace is \<open>safe\<close> if additionally the room was
empty when it was entered:\<close>

(*<*)definition safe :: "event list \<Rightarrow> room \<Rightarrow> bool" where(*>*)
"safe s r = (\<exists>s\<^sub>1 s\<^sub>2 s\<^sub>3 g c.
 s = s\<^sub>3 @ [Enter g r c] @ s\<^sub>2 @ [Check_in g r c] @ s\<^sub>1 \<and>
 no_Check_in (s\<^sub>3 @ s\<^sub>2) r \<and> isin (s\<^sub>2 @ [Check_in g r c] @ s\<^sub>1) r = {})"

text\<open>\medskip\noindent The two notions of safety are distinguished because,
except for the main theorem, @{const safe\<^sub>0} suffices.

The alert reader may already have wondered why, in contrast to the
state based model, we do not require @{const initk} to be
injective. If @{const initk} is not injective, e.g.\ @{prop"initk
r\<^sub>1 = initk r\<^sub>2"} and @{prop"r\<^sub>1 \<noteq> r\<^sub>2"},
then @{term"[Enter g r\<^sub>2 (initk r\<^sub>1,k), Check_in g
r\<^sub>1 (initk r\<^sub>1,k)]"} is a legal trace and guest \<open>g\<close> ends up in a room he is not the owner of.  However, this is not a
safe trace for room \<open>r\<^sub>2\<close> according to our
definition. This reflects that hotel rooms are not safe until
the first time their owner has entered them. We no longer protect the
hotel from its guests.\<close>

(* state thm w/o "isin"
hotel s ==> s = Enter g # s' \<Longrightarrow> owns s' r = Some g \<or> s' = s1 @ Checkin g @ s2 \<and> 
no checkin, no enter in s1

*)

(*<*)
lemma safe_safe: "safe s r \<Longrightarrow> safe\<^sub>0 s r"
by (simp add: safe\<^sub>0_def safe_def) blast

lemma initk_issued[simp]: "hotel s \<Longrightarrow> initk r \<in> issued s"
by (induct s) (auto split:event.split)

lemma currk_issued[simp]: "hotel s \<Longrightarrow> currk s r \<in> issued s"
by (induct s) (auto split:event.split)

lemma key1_issued[simp]: "hotel s \<Longrightarrow> (k,k') : cards s g \<Longrightarrow> k \<in> issued s"
by (induct s) (auto split:event.split)

lemma key2_issued[simp]: "hotel s \<Longrightarrow> (k,k') : cards s g \<Longrightarrow> k' \<in> issued s"
by (induct s) (auto split:event.split)

lemma roomk_issued[simp]: "hotel s \<Longrightarrow> roomk s r \<in> issued s"
by (induct s) (auto split:event.split)

lemma issued_app: "issued (s @ s') = issued s \<union> issued s'"
apply (induct s) apply (auto split:event.split)
apply (induct s') apply (auto split:event.split)
done

lemma owns_app[simp]: "no_Check_in s\<^sub>2 r \<Longrightarrow> owns (s\<^sub>2 @ s\<^sub>1) r = owns s\<^sub>1 r"
by (induct s\<^sub>2) (auto split:event.split)

lemma currk_app[simp]: "no_Check_in s\<^sub>2 r \<Longrightarrow> currk (s\<^sub>2 @ s\<^sub>1) r = currk s\<^sub>1 r"
by (induct s\<^sub>2) (auto split:event.split)

lemma currk_Check_in:
 "\<lbrakk> hotel (s\<^sub>2 @ Check_in g r (k, k')# s\<^sub>1);
    k' = currk (s\<^sub>2 @ Check_in g r (k, k') # s\<^sub>1) r' \<rbrakk> \<Longrightarrow> r' = r"
by (induct s\<^sub>2) (auto simp: issued_app split:event.splits)

lemma no_checkin_no_newkey:
"\<lbrakk> hotel(s\<^sub>2 @ [Check_in g r (k,k')] @ s\<^sub>1); no_Check_in s\<^sub>2 r \<rbrakk>
 \<Longrightarrow> (k',k'') \<notin> cards (s\<^sub>2 @ Check_in g r (k,k') # s\<^sub>1) g'"
apply(induct s\<^sub>2)
 apply fastforce
apply(fastforce split:event.splits dest: currk_Check_in)
done

lemma guest_key2_disj2[simp]: 
"\<lbrakk> hotel s; (k\<^sub>1,k) \<in> cards s g\<^sub>1; (k\<^sub>2,k) \<in> cards s g\<^sub>2 \<rbrakk> \<Longrightarrow> g\<^sub>1=g\<^sub>2"
apply (induct s)
apply(auto split:event.splits)
done

lemma safe_roomk_currk[simp]:
 "hotel s \<Longrightarrow> safe\<^sub>0 s r \<Longrightarrow> roomk s r = currk s r"
apply(clarsimp simp:safe\<^sub>0_def)
apply(hypsubst_thin)
apply(erule rev_mp)+
apply(induct_tac s\<^sub>3)
apply(auto split:event.split)
apply(rename_tac guest ba)
apply(subgoal_tac "(b, ba)
        \<notin> cards ((list @ Enter g r (a, b) # s\<^sub>2) @ Check_in g r (a, b) # s\<^sub>1)
           guest")
apply simp
apply(rule no_checkin_no_newkey) apply simp_all
done

lemma only_owner_enter_normal:
 "\<lbrakk> hotel s; safe\<^sub>0 s r; (k,roomk s r) \<in> cards s g \<rbrakk> \<Longrightarrow> owns s r = Some g"
apply(clarsimp simp:safe\<^sub>0_def)
apply(hypsubst_thin)
apply(erule rev_mp)+
apply(induct_tac s\<^sub>3)
 apply (fastforce)
apply (auto simp add:issued_app split:event.split)
done

(* A short proof *)
lemma "\<lbrakk> hotel s; safe s r; g \<in> isin s r \<rbrakk> \<Longrightarrow> owns s r = Some g"
apply(clarsimp simp add:safe_def)
apply(hypsubst_thin)
apply(rename_tac g' k k')
apply(erule rev_mp)+
apply(induct_tac s\<^sub>3)
 apply simp
apply (auto split:event.split)
 apply(subgoal_tac
 "safe\<^sub>0 (list @ Enter g' r (k,k') # s\<^sub>2 @ Check_in g' r (k, k') # s\<^sub>1) r")
  prefer 2
  apply(simp add:safe\<^sub>0_def)apply blast
 apply(simp)
 apply(cut_tac s\<^sub>2 = "list @ Enter g' r (k, k') # s\<^sub>2" in no_checkin_no_newkey)
   apply simp
  apply simp
 apply simp
 apply fast
apply(subgoal_tac
 "safe\<^sub>0 (list @ Enter g' r (k,k') # s\<^sub>2 @ Check_in g' r (k, k') # s\<^sub>1) r")
 apply(drule (1) only_owner_enter_normal)
  apply blast
 apply simp
apply(simp add:safe\<^sub>0_def)
apply blast
done

lemma in_set_conv_decomp_firstD:
assumes "P x"
shows "x \<in> set xs \<Longrightarrow>
  \<exists>ys x zs. xs = ys @ x # zs \<and> P x \<and> (\<forall>y \<in> set ys. \<not> P y)"
  (is "_ \<Longrightarrow> \<exists>ys x zs. ?P xs ys x zs")
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  show ?case
  proof cases
    assume "x = a \<or> P a" hence "?P (a#xs) [] a xs" using \<open>P x\<close> by auto
    thus ?case by blast
  next
    assume "\<not>(x = a \<or> P a)"
    with assms Cons show ?case by clarsimp (fastforce intro!: Cons_eq_appendI)
  qed
qed

lemma ownsD: "owns s r = Some g \<Longrightarrow>
 \<exists>s\<^sub>1 s\<^sub>2 g c. s = s\<^sub>2 @ [Check_in g r c] @ s\<^sub>1 \<and> no_Check_in s\<^sub>2 r"
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

lemma no_Check_in_owns[simp]: "no_Check_in s r \<Longrightarrow> owns s r = None"
by (induct s) (auto split:event.split)

theorem Enter_safe:
 "\<lbrakk> hotel(Enter g r c # s); safe\<^sub>0 s r \<rbrakk> \<Longrightarrow> owns s r = Some g"
apply(subgoal_tac "\<exists>s\<^sub>1 s\<^sub>2 g c. s = s\<^sub>2 @ [Check_in g r c] @ s\<^sub>1 \<and> no_Check_in s\<^sub>2 r")
 prefer 2
 apply(simp add:safe\<^sub>0_def)
 apply(elim exE conjE)
 apply(rule_tac x = s\<^sub>1 in exI)
 apply (simp)
apply(elim exE conjE)
apply(cases c)
apply(clarsimp)
apply(erule disjE)
apply (simp add:no_checkin_no_newkey)
apply simp
apply(frule only_owner_enter_normal)
apply assumption
apply simp
apply simp
done

lemma safe_future: "safe\<^sub>0 s r \<Longrightarrow> no_Check_in s' r \<Longrightarrow> safe\<^sub>0 (s' @ s) r"
apply(clarsimp simp:safe\<^sub>0_def)
apply(rule_tac x = s\<^sub>1 in exI)
apply(rule_tac x = s\<^sub>2 in exI)
apply simp
done

corollary Enter_safe_future:
 "\<lbrakk> hotel(Enter g r c # s' @ s); safe\<^sub>0 s r; no_Check_in s' r \<rbrakk>
 \<Longrightarrow> owns s r = Some g"
apply(drule (1) safe_future)
apply(drule (1) Enter_safe)
apply simp
done
(*>*)

text_raw\<open>
  \begin{figure}
  \begin{center}\begin{minipage}{\textwidth}  
  \isastyle\isamarkuptrue
\<close>
theorem safe: assumes "hotel s" and "safe s r" and "g \<in> isin s r"
                    shows "owns s r = \<lfloor>g\<rfloor>"
proof -
  { fix s\<^sub>1 s\<^sub>2 s\<^sub>3 g' k k'
    let ?b = "[Enter g' r (k,k')] @ s\<^sub>2 @ [Check_in g' r (k,k')] @ s\<^sub>1"
    let ?s = "s\<^sub>3 @ ?b"
    assume 0: "isin (s\<^sub>2 @ [Check_in g' r (k,k')] @ s\<^sub>1) r = {}"
    have "\<lbrakk> hotel ?s; no_Check_in (s\<^sub>3 @ s\<^sub>2) r; g \<in> isin ?s r \<rbrakk> \<Longrightarrow> g' = g"
    proof(induct s\<^sub>3)
      case Nil thus ?case using 0 by simp
    next
      case (Cons e s\<^sub>3)
      let ?s = "s\<^sub>3 @ ?b" and ?t = "(e \<cdot> s\<^sub>3) @ ?b"
      show ?case
      proof(cases e)
        case [simp]: (Enter g'' r' c)
        show "g' = g"
        proof cases
          assume [simp]: "r' = r"
          show "g' = g"
          proof cases
            assume [simp]: "g'' = g"
            have 1: "hotel ?s" and 2: "c \<in> cards ?s g" using \<open>hotel ?t\<close> by auto
            have 3: "safe ?s r" using \<open>no_Check_in ((e \<cdot> s\<^sub>3) @ s\<^sub>2) r\<close> 0
              by(simp add:safe_def) blast
            obtain k\<^sub>1 k\<^sub>2 where [simp]: "c = (k\<^sub>1,k\<^sub>2)" by force
            have "roomk ?s r = k'"
              using safe_roomk_currk[OF 1 safe_safe[OF 3]]
                \<open>no_Check_in ((e \<cdot> s\<^sub>3) @ s\<^sub>2) r\<close> by auto
            hence "k\<^sub>1 \<noteq> roomk ?s r"
              using no_checkin_no_newkey[where s\<^sub>2 = "s\<^sub>3 @ [Enter g' r (k,k')] @ s\<^sub>2"]
                1 2 \<open>no_Check_in ((e \<cdot> s\<^sub>3) @ s\<^sub>2) r\<close> by auto
            hence "k\<^sub>2 = roomk ?s r" using \<open>hotel ?t\<close> by auto
            with only_owner_enter_normal[OF 1 safe_safe[OF 3]] 2
            have "owns ?t r =  \<lfloor>g\<rfloor>" by auto
            moreover have "owns ?t r = \<lfloor>g'\<rfloor>"
              using \<open>hotel ?t\<close> \<open>no_Check_in ((e \<cdot> s\<^sub>3) @ s\<^sub>2) r\<close> by simp
            ultimately show "g' = g" by simp
          next
            assume "g'' \<noteq> g" thus "g' = g" using Cons by auto
          qed
        next
          assume "r' \<noteq> r" thus "g' = g" using Cons by auto
        qed
      qed (insert Cons, auto)
    qed
  } with assms show "owns s r = \<lfloor>g\<rfloor>" by(auto simp:safe_def)
qed
text_raw\<open>
  \end{minipage}
  \end{center}
  \caption{Isar proof of Theorem~\ref{safe}}\label{fig:proof}
  \end{figure}
\<close>
text\<open>
\subsection{Verifying safety}

Lemma~\ref{state-lemmas} largely carries over after replacing
\mbox{@{prop"s : reach"}} by @{prop"hotel s"} and @{const safe} by
@{const safe\<^sub>0}. Only properties \ref{currk_inj} and
\ref{key1_not_currk} no longer hold because we no longer assume that
@{const roomk} is initially injective.
They are replaced by two somewhat similar properties:
\begin{lemma}\label{trace-lemmas}\mbox{}
\begin{enumerate}
\item @{thm[display,margin=80]currk_Check_in}
\item \label{no_checkin_no_newkey}
  @{thm[display,margin=100] no_checkin_no_newkey}
\end{enumerate}
\end{lemma}
Both are proved by induction on \<open>s\<^sub>2\<close>.
In addition we need some easy structural properties:
\begin{lemma}\label{app-lemmas}
\begin{enumerate}
\item @{thm issued_app}
\item @{thm owns_app}
\item \label{currk_app} @{thm currk_app}
\end{enumerate}
\end{lemma}

The main theorem again correspond closely to its state based
counterpart:
\begin{theorem}\label{safe}
@{thm[mode=IfThen] safe}
\end{theorem}
Let us examine the proof of this theorem to show how it differs from
the state based version. For the core of the proof let
@{prop"s = s\<^sub>3 @ [Enter g' r (k,k')] @ s\<^sub>2 @ [Check_in g' r (k,k')] @ s\<^sub>1"}
and assume
@{prop"isin (s\<^sub>2 @ [Check_in g' r (k,k')] @ s\<^sub>1) r = {}"} (0). By induction on
\<open>s\<^sub>3\<close> we prove
@{prop[display]"\<lbrakk>hotel s; no_Check_in (s\<^sub>3 @ s\<^sub>2) r; g \<in> isin s r \<rbrakk> \<Longrightarrow> g' = g"}
The actual theorem follows by definition of @{const safe}.
The base case of the induction follows from (0). For the induction step let
@{prop"t = (e#s\<^sub>3) @ [Enter g' r (k,k')] @ s\<^sub>2 @ [Check_in g' r (k,k')] @ s\<^sub>1"}.
We assume @{prop"hotel t"}, @{prop"no_Check_in ((e#s\<^sub>3) @ s\<^sub>2) r"},
and @{prop"g \<in> isin s r"}, and show @{prop"g' = g"}.
The proof is by case distinction on the event \<open>e\<close>.
The cases @{const Check_in} and @{const Exit} follow directly from the
induction hypothesis because the set of occupants of \<open>r\<close>
can only decrease. Now we focus on the case @{prop"e = Enter g'' r' c"}.
If @{prop"r' \<noteq> r"} the set of occupants of \<open>r\<close> remains unchanged
and the claim follow directly from the induction hypothesis.
If @{prop"g'' \<noteq> g"} then \<open>g\<close> must already have been in \<open>r\<close>
before the \<open>Enter\<close> event and the claim again follows directly
from the induction hypothesis. Now assume @{prop"r' = r"}
and @{prop"g'' = g"}.
From @{prop"hotel t"} we obtain @{prop"hotel s"} (1) and
@{prop"c \<in> cards s g"} (2), and
from @{prop"no_Check_in (s\<^sub>3 @ s\<^sub>2) r"} and (0)
we obtain @{prop"safe s r"} (3). Let @{prop"c = (k\<^sub>1,k\<^sub>2)"}.
From Lemma~\ref{state-lemmas}.\ref{safe_roomk_currk} and
Lemma~\ref{app-lemmas}.\ref{currk_app} we obtain
\<open>roomk s r = currk s r = k'\<close>.
Hence @{prop"k\<^sub>1 \<noteq> roomk s r"} by
Lemma~\ref{trace-lemmas}.\ref{no_checkin_no_newkey}
using (1), (2) and @{prop"no_Check_in (s\<^sub>3 @ s\<^sub>2) r"}.
Hence @{prop"k\<^sub>2 = roomk s r"} by @{prop"hotel t"}.
With Lemma~\ref{state-lemmas}.\ref{safe_only_owner_enter_normal}
and (1--3) we obtain
@{prop"owns t r =  \<lfloor>g\<rfloor>"}. At the same time we have @{prop"owns t r = \<lfloor>g'\<rfloor>"}
because @{prop"hotel t"} and @{prop"no_Check_in ((e # s\<^sub>3) @ s\<^sub>2) r"}: nobody
has checked in to room \<open>r\<close> after \<open>g'\<close>. Thus the claim
@{prop"g' = g"} follows.

The details of this proof differ from those of Theorem~\ref{safe-state}
but the structure is very similar.

\subsection{Eliminating \isa{isin}}

In the state based approach we needed @{const isin} to express our
safety guarantees. In the presence of traces, we can do away with it
and talk about @{const Enter} events instead. We show that if somebody
enters a safe room, he is the owner:
\begin{theorem}\label{Enter_safe}
@{thm[mode=IfThen] Enter_safe}
\end{theorem}
From @{prop"safe\<^sub>0 s r"} it follows that \<open>s\<close> must be of the form
@{term"s\<^sub>2 @ [Check_in g\<^sub>0 r c'] @ s\<^sub>1"} such that @{prop"no_Check_in s\<^sub>2 r"}.
Let @{prop"c = (x,y)"} and @{prop"c' = (k,k')"}.
By Lemma~\ref{state-lemmas}.\ref{safe_roomk_currk} we have
\<open>roomk s r = currk s r = k'\<close>.
From @{prop"hotel(Enter g r c # s)"} it follows that
@{prop"(x,y) \<in> cards s g"} and @{prop"k' \<in> {x,y}"}.
By Lemma~\ref{trace-lemmas}.\ref{no_checkin_no_newkey}
@{prop"x = k'"} would contradict @{prop"(x,y) \<in> cards s g"}.
Hence @{prop"y = k'"}.
With Lemma~\ref{state-lemmas}.\ref{safe_only_owner_enter_normal}
we obtain @{prop"owns s r = \<lfloor>g\<rfloor>"}.

Having dispensed with @{const isin} we could also eliminate @{const
Exit} to arrive at a model closer to the ones in~\cite{Jackson06}.

Finally one may quibble that all the safety theorems proved so far
assume safety of the room at that point in time when somebody enters
it.  That is, the owner of the room must be sure that once a room is
safe, it stays safe, in order to profit from those safety theorems.
Of course, this is the case as long as nobody else checks in to that room:
\begin{lemma}
@{thm[mode=IfThen]safe_future}
\end{lemma}
It follows easily that Theorem~\ref{Enter_safe} also extends until check-in:
\begin{corollary}
@{thm[mode=IfThen]Enter_safe_future}
\end{corollary}

\subsection{Completeness of @{const safe}}

Having proved correctness of @{const safe}, i.e.\ that safe behaviour
protects against intruders, one may wonder if @{const safe} is
complete, i.e.\ if it covers all safe behaviour, or if it is too
restrictive. It turns out that @{const safe} is incomplete for two
different reasons.  The trivial one is that in case @{const initk} is
injective, every room is protected against intruders right from the
start. That is, @{term"[Check_in g r c]"} will only allow @{term g} to
enter \<open>r\<close> until somebody else checks in to \<open>r\<close>. The
second, more subtle incompleteness is that even if there are previous
owners of a room, it may be safe to enter a room with an old card
\<open>c\<close>: one merely needs to make sure that no other guest checked
in after the check-in where one obtained \<open>c\<close>. However,
formalizing this is not only messy, it is also somewhat pointless:
this liberalization is not something a guest can take advantage of
because there is no (direct) way he can find out which of his cards
meets this criterion. But without this knowledge, the only safe thing
to do is to make sure he has used his latest card. This incompleteness
applies to the state based model as well.
\<close>

(*<*)
end
(*>*)
