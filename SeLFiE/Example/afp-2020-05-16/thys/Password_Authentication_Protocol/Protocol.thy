(*  Title:       Verification of a Diffie-Hellman Password-based Authentication Protocol by Extending the Inductive Method
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjosystems dot com
*)

section "Protocol modeling and verification"

theory Protocol
imports Propaedeutics
begin


subsection "Protocol modeling"

text \<open>
The protocol under consideration can be formalized by means of the following inductive definition.

\null
\<close>

inductive_set protocol :: "(event list \<times> state \<times> msg set \<times> msg set) set" where

Nil:  "([], start_S, start_A, start_U) \<in> protocol" |

R1:   "\<lbrakk>(evsR1, S, A, U) \<in> protocol; Pri_AgrK s \<notin> U; s \<noteq> 0;
         NonceS (S (Card n, n, run)) = None\<rbrakk>
  \<Longrightarrow> (Says n run 1 (Card n) (User m) (Crypt (symK n) (Pri_AgrK s)) # evsR1,
       S ((Card n, n, run) := S (Card n, n, run) \<lparr>NonceS := Some s\<rparr>),
       if n \<in> bad then insert (Pri_AgrK s) A else A,
       insert (Pri_AgrK s) U) \<in> protocol" |

FR1:  "\<lbrakk>(evsFR1, S, A, U) \<in> protocol; User m \<noteq> Spy; s \<noteq> 0;
         Crypt (symK m) (Pri_AgrK s) \<in> synth (analz (A \<union> spies evsFR1))\<rbrakk>
  \<Longrightarrow> (Says n run 1 Spy (User m) (Crypt (symK m) (Pri_AgrK s)) # evsFR1,
       S, A, U) \<in> protocol" |

C2:   "\<lbrakk>(evsC2, S, A, U) \<in> protocol; Pri_AgrK a \<notin> U;
         NonceS (S (User m, n, run)) = None;
         Says n run 1 X (User m) (Crypt (symK n') (Pri_AgrK s)) \<in> set evsC2;
         s' = (if symK n' = symK m then s else 0)\<rbrakk>
  \<Longrightarrow> (Says n run 2 (User m) (Card n) (pubAK a) # evsC2,
       S ((User m, n, run) := S (User m, n, run)
         \<lparr>NonceS := Some s', IntMapK := Some a\<rparr>),
       if User m = Spy then insert (Pri_AgrK a) A else A,
       insert (Pri_AgrK a) U) \<in> protocol" |

FC2:  "\<lbrakk>(evsFC2, S, A, U) \<in> protocol;
         Pri_AgrK a \<in> analz (A \<union> spies evsFC2)\<rbrakk>
  \<Longrightarrow> (Says n run 2 Spy (Card n) (pubAK a) # evsFC2,
       S, A, U) \<in> protocol" |

R2:   "\<lbrakk>(evsR2, S, A, U) \<in> protocol; Pri_AgrK b \<notin> U;
         NonceS (S (Card n, n, run)) \<noteq> None;
         IntMapK (S (Card n, n, run)) = None;
         Says n run 2 X (Card n) (pubAK a) \<in> set evsR2\<rbrakk>
  \<Longrightarrow> (Says n run 2 (Card n) X (pubAK b) # evsR2,
       S ((Card n, n, run) := S (Card n, n, run)
         \<lparr>IntMapK := Some b, ExtMapK := Some a\<rparr>),
       A, insert (Pri_AgrK b) U) \<in> protocol" |

FR2:  "\<lbrakk>(evsFR2, S, A, U) \<in> protocol; User m \<noteq> Spy;
         Pri_AgrK b \<in> analz (A \<union> spies evsFR2)\<rbrakk>
  \<Longrightarrow> (Says n run 2 Spy (User m) (pubAK b) # evsFR2,
       S, A, U) \<in> protocol" |

C3:   "\<lbrakk>(evsC3, S, A, U) \<in> protocol; Pri_AgrK c \<notin> U;
         NonceS (S (User m, n, run)) = Some s;
         IntMapK (S (User m, n, run)) = Some a;
         ExtMapK (S (User m, n, run)) = None;
         Says n run 2 X (User m) (pubAK b) \<in> set evsC3;
         c * (s + a * b) \<noteq> 0\<rbrakk>
  \<Longrightarrow> (Says n run 3 (User m) (Card n) (pubAK (c * (s + a * b))) # evsC3,
       S ((User m, n, run) := S (User m, n, run)
         \<lparr>ExtMapK := Some b, IntAgrK := Some c\<rparr>),
       if User m = Spy then insert (Pri_AgrK c) A else A,
       insert (Pri_AgrK c) U) \<in> protocol" |

FC3:  "\<lbrakk>(evsFC3, S, A, U) \<in> protocol;
         NonceS (S (Card n, n, run)) = Some s;
         IntMapK (S (Card n, n, run)) = Some b;
         ExtMapK (S (Card n, n, run)) = Some a;
         {Pri_AgrK s, Pri_AgrK a, Pri_AgrK c} \<subseteq> analz (A \<union> spies evsFC3)\<rbrakk>
  \<Longrightarrow> (Says n run 3 Spy (Card n) (pubAK (c * (s + a * b))) # evsFC3,
       S, A, U) \<in> protocol" |

R3:   "\<lbrakk>(evsR3, S, A, U) \<in> protocol; Pri_AgrK d \<notin> U;
         NonceS (S (Card n, n, run)) = Some s;
         IntMapK (S (Card n, n, run)) = Some b;
         ExtMapK (S (Card n, n, run)) = Some a;
         IntAgrK (S (Card n, n, run)) = None;
         Says n run 3 X (Card n) (pubAK (c * (s' + a * b))) \<in> set evsR3;
         Key (sesK (c * d * (s' + a * b))) \<notin> U;
         Key (sesK (c * d * (s + a * b))) \<notin> U;
         d * (s + a * b) \<noteq> 0\<rbrakk>
  \<Longrightarrow> (Says n run 3 (Card n) X (pubAK (d * (s + a * b))) # evsR3,
       S ((Card n, n, run) := S (Card n, n, run)
         \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s' + a * b))\<rparr>),
       if s' = s \<and> Pri_AgrK c \<in> analz (A \<union> spies evsR3)
         then insert (Key (sesK (c * d * (s + a * b)))) A else A,
       {Pri_AgrK d,
         Key (sesK (c * d * (s' + a * b))), Key (sesK (c * d * (s + a * b))),
         \<lbrace>Key (sesK (c * d * (s + a * b))), Agent X, Number n, Number run\<rbrace>} \<union> U) \<in> protocol" |

FR3:  "\<lbrakk>(evsFR3, S, A, U) \<in> protocol; User m \<noteq> Spy;
         NonceS (S (User m, n, run)) = Some s;
         IntMapK (S (User m, n, run)) = Some a;
         ExtMapK (S (User m, n, run)) = Some b;
         IntAgrK (S (User m, n, run)) = Some c;
         {Pri_AgrK s, Pri_AgrK b, Pri_AgrK d} \<subseteq> analz (A \<union> spies evsFR3);
         Key (sesK (c * d * (s + a * b))) \<notin> U\<rbrakk>
  \<Longrightarrow> (Says n run 3 Spy (User m) (pubAK (d * (s + a * b))) # evsFR3, S,
       insert (Key (sesK (c * d * (s + a * b)))) A,
       {Key (sesK (c * d * (s + a * b))),
         \<lbrace>Key (sesK (c * d * (s + a * b))), Agent (User m), Number n, Number run\<rbrace>} \<union> U) \<in> protocol" |

C4:   "\<lbrakk>(evsC4, S, A, U) \<in> protocol;
         IntAgrK (S (User m, n, run)) = Some c;
         ExtAgrK (S (User m, n, run)) = None;
         Says n run 3 X (User m) (pubAK f) \<in> set evsC4;
         \<lbrace>Key (sesK (c * f)), Agent (User m), Number n, Number run\<rbrace> \<in> U\<rbrakk>
  \<Longrightarrow> (Says n run 4 (User m) (Card n) (Crypt (sesK (c * f)) (pubAK f)) # evsC4,
       S ((User m, n, run) := S (User m, n, run) \<lparr>ExtAgrK := Some f\<rparr>),
       A, U) \<in> protocol" |

FC4:  "\<lbrakk>(evsFC4, S, A, U) \<in> protocol;
         NonceS (S (Card n, n, run)) = Some s;
         IntMapK (S (Card n, n, run)) = Some b;
         ExtMapK (S (Card n, n, run)) = Some a;
         IntAgrK (S (Card n, n, run)) = Some d;
         ExtAgrK (S (Card n, n, run)) = Some e;
         Crypt (sesK (d * e)) (pubAK (d * (s + a * b)))
           \<in> synth (analz (A \<union> spies evsFC4))\<rbrakk>
  \<Longrightarrow> (Says n run 4 Spy (Card n)
         (Crypt (sesK (d * e)) (pubAK (d * (s + a * b)))) # evsFC4,
       S, A, U) \<in> protocol" |

R4:   "\<lbrakk>(evsR4, S, A, U) \<in> protocol;
         NonceS (S (Card n, n, run)) = Some s;
         IntMapK (S (Card n, n, run)) = Some b;
         ExtMapK (S (Card n, n, run)) = Some a;
         IntAgrK (S (Card n, n, run)) = Some d;
         ExtAgrK (S (Card n, n, run)) = Some e;
         Says n run 4 X (Card n) (Crypt (sesK (d * e))
           (pubAK (d * (s + a * b)))) \<in> set evsR4\<rbrakk>
  \<Longrightarrow> (Says n run 4 (Card n) X (Crypt (sesK (d * e))
         \<lbrace>pubAK e, Auth_Data (priAK n) b, pubAK (priAK n),
          Crypt (priSK CA) (Hash (pubAK (priAK n)))\<rbrace>) # evsR4,
       S, A, U) \<in> protocol" |

FR4:  "\<lbrakk>(evsFR4, S, A, U) \<in> protocol; User m \<noteq> Spy;
         NonceS (S (User m, n, run)) = Some s;
         IntMapK (S (User m, n, run)) = Some a;
         ExtMapK (S (User m, n, run)) = Some b;
         IntAgrK (S (User m, n, run)) = Some c;
         ExtAgrK (S (User m, n, run)) = Some f;
         Crypt (sesK (c * f))
           \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
            Crypt (priSK CA) (Hash (pubAK g))\<rbrace> \<in> synth (analz (A \<union> spies evsFR4))\<rbrakk>
  \<Longrightarrow> (Says n run 4 Spy (User m) (Crypt (sesK (c * f))
         \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
          Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) # evsFR4,
       S, A, U) \<in> protocol" |

C5:   "\<lbrakk>(evsC5, S, A, U) \<in> protocol;
         NonceS (S (User m, n, run)) = Some s;
         IntMapK (S (User m, n, run)) = Some a;
         ExtMapK (S (User m, n, run)) = Some b;
         IntAgrK (S (User m, n, run)) = Some c;
         ExtAgrK (S (User m, n, run)) = Some f;
         Says n run 4 X (User m) (Crypt (sesK (c * f))
           \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
            Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evsC5\<rbrakk>
  \<Longrightarrow> (Says n run 5 (User m) (Card n) (Crypt (sesK (c * f)) (Passwd m)) # evsC5,
       S, A, U) \<in> protocol" |

FC5:  "\<lbrakk>(evsFC5, S, A, U) \<in> protocol;
         IntAgrK (S (Card n, n, run)) = Some d;
         ExtAgrK (S (Card n, n, run)) = Some e;
         Crypt (sesK (d * e)) (Passwd n) \<in> synth (analz (A \<union> spies evsFC5))\<rbrakk>
  \<Longrightarrow> (Says n run 5 Spy (Card n) (Crypt (sesK (d * e)) (Passwd n)) # evsFC5,
       S, A, U) \<in> protocol" |

R5:   "\<lbrakk>(evsR5, S, A, U) \<in> protocol;
         IntAgrK (S (Card n, n, run)) = Some d;
         ExtAgrK (S (Card n, n, run)) = Some e;
         Says n run 5 X (Card n) (Crypt (sesK (d * e)) (Passwd n)) \<in> set evsR5\<rbrakk>
  \<Longrightarrow> (Says n run 5 (Card n) X (Crypt (sesK (d * e)) (Number 0)) # evsR5,
       S, A, U) \<in> protocol" |

FR5:  "\<lbrakk>(evsFR5, S, A, U) \<in> protocol; User m \<noteq> Spy;
         IntAgrK (S (User m, n, run)) = Some c;
         ExtAgrK (S (User m, n, run)) = Some f;
         Crypt (sesK (c * f)) (Number 0) \<in> synth (analz (A \<union> spies evsFR5))\<rbrakk>
  \<Longrightarrow> (Says n run 5 Spy (User m) (Crypt (sesK (c * f)) (Number 0)) # evsFR5,
       S, A, U) \<in> protocol"

text \<open>
\null

Here below are some comments about the most significant points of this definition.

\begin{itemize}

\item
Rules @{thm [source] R1} and @{thm [source] FR1} constrain the values of nonce $s$ to be different
from 0. In this way, the state of affairs where an incorrect PACE authentication key has been used
to encrypt nonce $s$, so that a wrong value results from the decryption, can be modeled in rule
@{thm [source] C2} by identifying such value with 0.

\item
The spy can disclose session keys as soon as they are established, namely in correspondence with
rules @{thm [source] R3} and @{thm [source] FR3}.
\\In the former rule, condition @{term "s' = s"} identifies Diffie-Hellman private key \<open>c\<close> as
the terminal's ephemeral private key for key agreement, and then $[c \times d \times (s + a \times
b)]G$ as the terminal's value of the shared secret, which the spy can compute by multiplying the
card's ephemeral public key $[d \times (s + a \times b)]G$ by \<open>c\<close> provided she knows
\<open>c\<close>.
\\In the latter rule, the spy is required to know private keys \<open>s\<close>, \<open>b\<close>, and \<open>d\<close>
to be able to compute and send public key $[d \times (s + a \times b)]G$. This is the only way to
share with @{term "User m"} the same shared secret's value $[c \times d \times (s + a \times b)]G$,
which the spy can compute by multiplying the user's ephemeral public key $[c \times (s + a \times
b)]G$ by \<open>d\<close>.

\item
Rules @{thm [source] R3} and @{thm [source] FR3} record the user, the communication channel, and the
protocol run associated to the session key having been established by adding this information to the
set of the messages already used. In this way, rule @{thm [source] C4} can specify that the session
key computed by @{term "User m"} is fresh by assuming that a corresponding record be included in set
\<open>U\<close>. In fact, a simple check that the session key be not included in \<open>U\<close> would vacuously
fail, as session keys are added to the set of the messages already used in rules @{thm [source] R3}
and @{thm [source] FR3}.

\end{itemize}
\<close>


subsection "Secrecy theorems"

text \<open>
This section contains a series of lemmas culminating in the secrecy theorems \<open>pr_key_secrecy\<close>
and \<open>pr_passwd_secrecy\<close>. Structured Isar proofs are used, possibly preceded by
\emph{apply}-style scripts in case a substantial amount of backward reasoning steps is required at
the beginning.

\null
\<close>

lemma pr_state:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    (NonceS (S (X, n, run)) = None \<longrightarrow> IntMapK (S (X, n, run)) = None) \<and>
    (IntMapK (S (X, n, run)) = None \<longrightarrow> ExtMapK (S (X, n, run)) = None) \<and>
    (ExtMapK (S (X, n, run)) = None \<longrightarrow> IntAgrK (S (X, n, run)) = None) \<and>
    (IntAgrK (S (X, n, run)) = None \<longrightarrow> ExtAgrK (S (X, n, run)) = None)"
proof (erule protocol.induct, simp_all)
qed (rule_tac [!] impI, simp_all)

lemma pr_state_1:
 "\<lbrakk>(evs, S, A, U) \<in> protocol; NonceS (S (X, n, run)) = None\<rbrakk> \<Longrightarrow>
    IntMapK (S (X, n, run)) = None"
by (simp add: pr_state)

lemma pr_state_2:
 "\<lbrakk>(evs, S, A, U) \<in> protocol; IntMapK (S (X, n, run)) = None\<rbrakk> \<Longrightarrow>
    ExtMapK (S (X, n, run)) = None"
by (simp add: pr_state)

lemma pr_state_3:
 "\<lbrakk>(evs, S, A, U) \<in> protocol; ExtMapK (S (X, n, run)) = None\<rbrakk> \<Longrightarrow>
    IntAgrK (S (X, n, run)) = None"
by (simp add: pr_state)

lemma pr_state_4:
 "\<lbrakk>(evs, S, A, U) \<in> protocol; IntAgrK (S (X, n, run)) = None\<rbrakk> \<Longrightarrow>
    ExtAgrK (S (X, n, run)) = None"
by (simp add: pr_state)

lemma pr_analz_used:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> A \<subseteq> U"
by (erule protocol.induct, auto)

lemma pr_key_parts_intro [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Key K \<in> parts (A \<union> spies evs) \<longrightarrow>
  Key K \<in> A"
proof (erule protocol.induct, subst parts_simp, simp, blast, simp)
qed (simp_all add: parts_simp_insert parts_auth_data parts_crypt parts_mpair)

lemma pr_key_analz:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> (Key K \<in> analz (A \<union> spies evs)) = (Key K \<in> A)"
proof (rule iffI, drule subsetD [OF analz_parts_subset], erule pr_key_parts_intro,
 assumption)
qed (rule subsetD [OF analz_subset], simp)

lemma pr_symk_used:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> Key (symK n) \<in> U"
by (erule protocol.induct, simp_all)

lemma pr_symk_analz:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> (Key (symK n) \<in> analz (A \<union> spies evs)) = (n \<in> bad)"
proof (simp add: pr_key_analz, erule protocol.induct, simp_all, rule_tac [2] impI,
 rule_tac [!] iffI, simp_all, erule disjE, erule_tac [2-4] disjE, simp_all)
  assume "Key (symK n) \<in> Key ` symK ` bad"
  hence "\<exists>m \<in> bad. symK n = symK m"
   by (simp add: image_iff)
  then obtain m where "m \<in> bad" and "symK n = symK m" ..
  thus "n \<in> bad"
   by (rule symK_bad)
next
  assume "Key (symK n) \<in> Key ` range pubSK"
  thus "n \<in> bad"
   by (auto, drule_tac sym, erule_tac notE [OF pubSK_symK])
next
  assume "Key (symK n) \<in> pubAK ` range priAK"
  thus "n \<in> bad"
   by blast
next
  fix evsR3 S A U s a b c d
  assume "(evsR3, S, A, U) \<in> protocol"
  hence "Key (symK n) \<in> U"
   by (rule pr_symk_used)
  moreover assume "symK n = sesK (c * d * (s + a * b))"
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show "n \<in> bad"
   by contradiction
next
  fix evsFR3 S A U s a b c d
  assume "(evsFR3, S, A, U) \<in> protocol"
  hence "Key (symK n) \<in> U"
   by (rule pr_symk_used)
  moreover assume "symK n = sesK (c * d * (s + a * b))"
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show "n \<in> bad"
   by contradiction
qed

lemma pr_sesk_card [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    IntAgrK (S (Card n, n, run)) = Some d \<longrightarrow>
    ExtAgrK (S (Card n, n, run)) = Some e \<longrightarrow>
  Key (sesK (d * e)) \<in> U"
proof (erule protocol.induct, simp_all, (rule impI)+, simp)
qed (subst (2) mult.commute, subst mult.assoc, simp)

lemma pr_sesk_user_1 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    IntAgrK (S (User m, n, run)) = Some c \<longrightarrow>
    ExtAgrK (S (User m, n, run)) = Some f \<longrightarrow>
  \<lbrace>Key (sesK (c * f)), Agent (User m), Number n, Number run\<rbrace> \<in> U"
proof (erule protocol.induct, simp_all, (rule_tac [!] impI)+, simp_all)
  fix evsC3 S A U m n run
  assume A: "(evsC3, S, A, U) \<in> protocol" and
   "ExtMapK (S (User m, n, run)) = None"
  hence "IntAgrK (S (User m, n, run)) = None"
   by (rule pr_state_3)
  with A have "ExtAgrK (S (User m, n, run)) = None"
   by (rule pr_state_4)
  moreover assume "ExtAgrK (S (User m, n, run)) = Some f"
  ultimately show "\<lbrace>Key (sesK (c * f)), Agent (User m), Number n, Number run\<rbrace> \<in> U"
   by simp
qed

lemma pr_sesk_user_2 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    \<lbrace>Key (sesK K), Agent (User m), Number n, Number run\<rbrace> \<in> U \<longrightarrow>
  Key (sesK K) \<in> U"
by (erule protocol.induct, blast, simp_all)

lemma pr_auth_key_used:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> Pri_AgrK (priAK n) \<in> U"
by (erule protocol.induct, simp_all)

lemma pr_int_mapk_used [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
  Pri_AgrK b \<in> U"
by (erule protocol.induct, simp_all)

lemma pr_valid_key_analz:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> Key (pubSK X) \<in> analz (A \<union> spies evs)"
by (simp add: pr_key_analz, erule protocol.induct, simp_all)

lemma pr_pri_agrk_parts [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Pri_AgrK x \<notin> U \<longrightarrow>
  Pri_AgrK x \<notin> parts (A \<union> spies evs)"
proof (induction arbitrary: x rule: protocol.induct,
 simp_all add: parts_simp_insert parts_auth_data parts_crypt parts_mpair,
 subst parts_simp, blast, blast, rule_tac [!] impI)
  fix evsFR1 A U m s x
  assume
   "\<And>x. Pri_AgrK x \<notin> U \<longrightarrow> Pri_AgrK x \<notin> parts (A \<union> spies evsFR1)" and
   "Pri_AgrK x \<notin> U"
  hence A: "Pri_AgrK x \<notin> parts (A \<union> spies evsFR1)" ..
  assume B: "Crypt (symK m) (Pri_AgrK s) \<in> synth (analz (A \<union> spies evsFR1))"
  show "x \<noteq> s"
  proof
    assume "x = s"
    hence "Crypt (symK m) (Pri_AgrK x) \<in> synth (analz (A \<union> spies evsFR1))"
     using B by simp
    hence "Crypt (symK m) (Pri_AgrK x) \<in> analz (A \<union> spies evsFR1) \<or>
      Pri_AgrK x \<in> synth (analz (A \<union> spies evsFR1)) \<and>
      Key (symK m) \<in> analz (A \<union> spies evsFR1)"
      (is "?P \<or> ?Q")
     by (rule synth_crypt)
    moreover {
      assume ?P
      hence "Crypt (symK m) (Pri_AgrK x) \<in> parts (A \<union> spies evsFR1)"
       by (rule subsetD [OF analz_parts_subset])
      hence "Pri_AgrK x \<in> parts (A \<union> spies evsFR1)"
       by (rule parts.Body)
      hence False
       using A by contradiction
    }
    moreover {
      assume ?Q
      hence "Pri_AgrK x \<in> synth (analz (A \<union> spies evsFR1))" ..
      hence "Pri_AgrK x \<in> analz (A \<union> spies evsFR1)"
       by (rule synth_simp_intro, simp)
      hence "Pri_AgrK x \<in> parts (A \<union> spies evsFR1)"
       by (rule subsetD [OF analz_parts_subset])
      hence False
       using A by contradiction
    }
    ultimately show False ..
  qed
next
  fix evsR4 S A U b n run x
  assume
    A: "(evsR4, S, A, U) \<in> protocol" and
    B: "IntMapK (S (Card n, n, run)) = Some b" and
    C: "Pri_AgrK x \<notin> U"
  show "x \<noteq> priAK n \<and> x \<noteq> b"
  proof (rule conjI, rule_tac [!] notI)
    assume "x = priAK n"
    moreover have "Pri_AgrK (priAK n) \<in> U"
     using A by (rule pr_auth_key_used)
    ultimately have "Pri_AgrK x \<in> U"
     by simp
    thus False
     using C by contradiction
  next
    assume "x = b"
    moreover have "Pri_AgrK b \<in> U"
     using A and B by (rule pr_int_mapk_used)
    ultimately have "Pri_AgrK x \<in> U"
     by simp
    thus False
     using C by contradiction
  qed
next
  fix evsFR4 S A U s a b c f g x
  assume
    A: "\<And>x. Pri_AgrK x \<notin> U \<longrightarrow> Pri_AgrK x \<notin> parts (A \<union> spies evsFR4)" and
    B: "(evsFR4, S, A, U) \<in> protocol" and
    C: "Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace> \<in> synth (analz (A \<union> spies evsFR4))"
      (is "Crypt _ ?M \<in> synth (analz ?A)") and
    D: "Pri_AgrK x \<notin> U"
  show "x \<noteq> g \<and> x \<noteq> b"
  proof -
    have E: "Pri_AgrK b \<in> U \<and> Pri_AgrK g \<in> U"
    proof -
      have "Crypt (sesK (c * f)) ?M \<in> analz ?A \<or>
        ?M \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
       using C by (rule synth_crypt)
      moreover {
        assume "Crypt (sesK (c * f)) ?M \<in> analz ?A"
        hence "Crypt (sesK (c * f)) ?M \<in> parts ?A"
         by (rule subsetD [OF analz_parts_subset])
        hence "?M \<in> parts ?A"
         by (rule parts.Body)
        hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
          \<in> parts ?A"
         by (rule parts.Snd)
        hence F: "Auth_Data g b \<in> parts ?A"
         by (rule parts.Fst)
        hence "Pri_AgrK b \<in> parts ?A"
         by (rule parts.Auth_Snd)
        moreover have "Pri_AgrK g \<in> parts ?A"
         using F by (rule parts.Auth_Fst)
        ultimately have "Pri_AgrK b \<in> parts ?A \<and> Pri_AgrK g \<in> parts ?A" ..
      }
      moreover {
        assume "?M \<in> synth (analz ?A) \<and>
          Key (sesK (c * f)) \<in> analz ?A"
        hence "?M \<in> synth (analz ?A)" ..
        hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
          \<in> synth (analz ?A)"
         by (rule synth_analz_snd)
        hence "Auth_Data g b \<in> synth (analz ?A)"
         by (rule synth_analz_fst)
        hence "Auth_Data g b \<in> analz ?A \<or>
          Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b \<in> analz ?A"
         by (rule synth_auth_data)
        moreover {
          assume "Auth_Data g b \<in> analz ?A"
          hence F: "Auth_Data g b \<in> parts ?A"
           by (rule subsetD [OF analz_parts_subset])
          hence "Pri_AgrK b \<in> parts ?A"
           by (rule parts.Auth_Snd)
          moreover have "Pri_AgrK g \<in> parts ?A"
           using F by (rule parts.Auth_Fst)
          ultimately have "Pri_AgrK b \<in> parts ?A \<and> Pri_AgrK g \<in> parts ?A" ..
        }
        moreover {
          assume F: "Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b \<in> analz ?A"
          hence "Pri_AgrK b \<in> analz ?A" ..
          hence "Pri_AgrK b \<in> parts ?A"
           by (rule subsetD [OF analz_parts_subset])
          moreover have "Pri_AgrK g \<in> analz ?A"
           using F ..
          hence "Pri_AgrK g \<in> parts ?A"
           by (rule subsetD [OF analz_parts_subset])
          ultimately have "Pri_AgrK b \<in> parts ?A \<and> Pri_AgrK g \<in> parts ?A" ..
        }
        ultimately have "Pri_AgrK b \<in> parts ?A \<and> Pri_AgrK g \<in> parts ?A" ..
      }
      ultimately have F: "Pri_AgrK b \<in> parts ?A \<and> Pri_AgrK g \<in> parts ?A" ..
      hence "Pri_AgrK b \<in> parts ?A" ..
      hence "Pri_AgrK b \<in> U"
       by (rule contrapos_pp, insert A, simp)
      moreover have "Pri_AgrK g \<in> parts ?A"
       using F ..
      hence "Pri_AgrK g \<in> U"
       by (rule contrapos_pp, insert A, simp)
      ultimately show ?thesis ..
    qed
    show ?thesis
    proof (rule conjI, rule_tac [!] notI)
      assume "x = g"
      hence "Pri_AgrK x \<in> U"
       using E by simp
      thus False
       using D by contradiction
    next
      assume "x = b"
      hence "Pri_AgrK x \<in> U"
       using E by simp
      thus False
       using D by contradiction
    qed
  qed
qed

lemma pr_pri_agrk_items:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Pri_AgrK x \<notin> U \<Longrightarrow>
  items (insert (Pri_AgrK x) (A \<union> spies evs)) =
    insert (Pri_AgrK x) (items (A \<union> spies evs))"
by (rule items_pri_agrk_out, rule pr_pri_agrk_parts)

lemma pr_auth_data_items:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
  Pri_AgrK (priAK n) \<notin> items (A \<union> spies evs) \<and>
  (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
    Pri_AgrK b \<notin> items (A \<union> spies evs))"
proof (induction arbitrary: n run b rule: protocol.induct,
 simp_all add: items_simp_insert_2 items_crypt items_mpair pr_pri_agrk_items,
 subst items_simp, blast+)
  fix evsR1 S A U n' run' s n run b
  assume
    A: "(evsR1, S, A, U) \<in> protocol" and
    B: "Pri_AgrK s \<notin> U"
  show
   "(n = n' \<and> run = run' \<longrightarrow>
      priAK n' \<noteq> s \<and> (IntMapK (S (Card n', n', run')) = Some b \<longrightarrow> b \<noteq> s)) \<and>
    ((n = n' \<longrightarrow> run \<noteq> run') \<longrightarrow>
      priAK n \<noteq> s \<and> (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow> b \<noteq> s))"
  proof (rule conjI, rule_tac [!] impI, rule_tac [!] conjI, rule_tac [2] impI,
   rule_tac [4] impI, rule_tac [!] notI)
    have "Pri_AgrK (priAK n) \<in> U"
     using A by (rule pr_auth_key_used)
    moreover assume "priAK n = s"
    ultimately have "Pri_AgrK s \<in> U"
     by simp
    thus False
     using B by contradiction
  next
    assume "IntMapK (S (Card n, n, run)) = Some b"
    with A have "Pri_AgrK b \<in> U"
     by (rule pr_int_mapk_used)
    moreover assume "b = s"
    ultimately have "Pri_AgrK s \<in> U"
     by simp
    thus False
     using B by contradiction
  next
    have "Pri_AgrK (priAK n') \<in> U"
     using A by (rule pr_auth_key_used)
    moreover assume "priAK n' = s"
    ultimately have "Pri_AgrK s \<in> U"
     by simp
    thus False
     using B by contradiction
  next
    assume "IntMapK (S (Card n', n', run')) = Some b"
    with A have "Pri_AgrK b \<in> U"
     by (rule pr_int_mapk_used)
    moreover assume "b = s"
    ultimately have "Pri_AgrK s \<in> U"
     by simp
    thus False
     using B by contradiction
  qed
next
  fix evsFR1 A m s n run b and S :: state
  assume A: "\<And>n run b. Pri_AgrK (priAK n) \<notin> items (A \<union> spies evsFR1) \<and>
    (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
      Pri_AgrK b \<notin> items (A \<union> spies evsFR1))"
  assume "Crypt (symK m) (Pri_AgrK s) \<in> synth (analz (A \<union> spies evsFR1))"
  hence "Crypt (symK m) (Pri_AgrK s) \<in> analz (A \<union> spies evsFR1) \<or>
    Pri_AgrK s \<in> synth (analz (A \<union> spies evsFR1)) \<and>
    Key (symK m) \<in> analz (A \<union> spies evsFR1)"
    (is "?P \<or> ?Q")
   by (rule synth_crypt)
  moreover {
    assume ?P
    hence "Crypt (symK m) (Pri_AgrK s) \<in> items (A \<union> spies evsFR1)"
     by (rule subsetD [OF analz_items_subset])
    hence "Pri_AgrK s \<in> items (A \<union> spies evsFR1)"
     by (rule items.Body)
  }
  moreover {
    assume ?Q
    hence "Pri_AgrK s \<in> synth (analz (A \<union> spies evsFR1))" ..
    hence "Pri_AgrK s \<in> analz (A \<union> spies evsFR1)"
     by (rule synth_simp_intro, simp)
    hence "Pri_AgrK s \<in> items (A \<union> spies evsFR1)"
     by (rule subsetD [OF analz_items_subset])
  }
  ultimately have B: "Pri_AgrK s \<in> items (A \<union> spies evsFR1)" ..
  show "Pri_AgrK (priAK n) \<notin> items (insert (Pri_AgrK s) (A \<union> spies evsFR1)) \<and>
    (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
      Pri_AgrK b \<notin> items (insert (Pri_AgrK s) (A \<union> spies evsFR1)))"
   by (simp add: items_simp_insert_1 [OF B] A)
next
  fix evsC2 S A U a n run b and m :: nat
  assume
    A: "(evsC2, S, A, U) \<in> protocol" and
    B: "Pri_AgrK a \<notin> U"
  show "m = 0 \<longrightarrow> priAK n \<noteq> a \<and> (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow> b \<noteq> a)"
  proof (rule impI, rule conjI, rule_tac [2] impI, rule_tac [!] notI)
    have "Pri_AgrK (priAK n) \<in> U"
     using A by (rule pr_auth_key_used)
    moreover assume "priAK n = a"
    ultimately have "Pri_AgrK a \<in> U"
     by simp
    thus False
     using B by contradiction
  next
    assume "IntMapK (S (Card n, n, run)) = Some b"
    with A have "Pri_AgrK b \<in> U"
     by (rule pr_int_mapk_used)
    moreover assume "b = a"
    ultimately have "Pri_AgrK a \<in> U"
     by simp
    thus False
     using B by contradiction
  qed
next
  fix evsR2 S A U b' n' run' b and n :: nat and run :: nat
  assume
    A: "(evsR2, S, A, U) \<in> protocol" and
    B: "Pri_AgrK b' \<notin> U"
  show "n = n' \<and> run = run' \<longrightarrow> b' = b \<longrightarrow> Pri_AgrK b \<notin> items (A \<union> spies evsR2)"
  proof ((rule impI)+, drule sym, simp)
  qed (rule contra_subsetD [OF items_parts_subset], rule pr_pri_agrk_parts [OF A B])
next
  fix evsC3 S A U c n run b and m :: nat
  assume
    A: "(evsC3, S, A, U) \<in> protocol" and
    B: "Pri_AgrK c \<notin> U"
  show "m = 0 \<longrightarrow> priAK n \<noteq> c \<and> (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow> b \<noteq> c)"
  proof (rule impI, rule conjI, rule_tac [2] impI, rule_tac [!] notI)
    have "Pri_AgrK (priAK n) \<in> U"
     using A by (rule pr_auth_key_used)
    moreover assume "priAK n = c"
    ultimately have "Pri_AgrK c \<in> U"
     by simp
    thus False
     using B by contradiction
  next
    assume "IntMapK (S (Card n, n, run)) = Some b"
    with A have "Pri_AgrK b \<in> U"
     by (rule pr_int_mapk_used)
    moreover assume "b = c"
    ultimately have "Pri_AgrK c \<in> U"
     by simp
    thus False
     using B by contradiction
  qed
next
  fix evsR3 A n' run' s b' c n run b and S :: state and s' :: pri_agrk
  assume
    A: "\<And>n run b. Pri_AgrK (priAK n) \<notin> items (A \<union> spies evsR3) \<and>
      (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
        Pri_AgrK b \<notin> items (A \<union> spies evsR3))" and
    B: "IntMapK (S (Card n', n', run')) = Some b'"
  show
   "(s' = s \<and> Pri_AgrK c \<in> analz (A \<union> spies evsR3) \<longrightarrow>
       n = n' \<and> run = run' \<longrightarrow> b' = b \<longrightarrow>
     Pri_AgrK b \<notin> items (A \<union> spies evsR3)) \<and>
    ((s' = s \<longrightarrow> Pri_AgrK c \<notin> analz (A \<union> spies evsR3)) \<longrightarrow>
       n = n' \<and> run = run' \<longrightarrow> b' = b \<longrightarrow>
     Pri_AgrK b \<notin> items (A \<union> spies evsR3))"
  proof (rule conjI, (rule_tac [!] impI)+)
    have "Pri_AgrK (priAK n') \<notin> items (A \<union> spies evsR3) \<and>
      (IntMapK (S (Card n', n', run')) = Some b' \<longrightarrow>
        Pri_AgrK b' \<notin> items (A \<union> spies evsR3))"
     using A .
    hence "Pri_AgrK b' \<notin> items (A \<union> spies evsR3)"
     using B by simp
    moreover assume "b' = b"
    ultimately show "Pri_AgrK b \<notin> items (A \<union> spies evsR3)"
     by simp
  next
    have "Pri_AgrK (priAK n') \<notin> items (A \<union> spies evsR3) \<and>
      (IntMapK (S (Card n', n', run')) = Some b' \<longrightarrow>
        Pri_AgrK b' \<notin> items (A \<union> spies evsR3))"
     using A .
    hence "Pri_AgrK b' \<notin> items (A \<union> spies evsR3)"
     using B by simp
    moreover assume "b' = b"
    ultimately show "Pri_AgrK b \<notin> items (A \<union> spies evsR3)"
     by simp
  qed
next
  fix evsR4 A n' run' b' n run b and S :: state
  let ?M = "\<lbrace>pubAK (priAK n'), Crypt (priSK CA) (Hash (pubAK (priAK n')))\<rbrace>"
  assume
    A: "\<And>n run b. Pri_AgrK (priAK n) \<notin> items (A \<union> spies evsR4) \<and>
      (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
        Pri_AgrK b \<notin> items (A \<union> spies evsR4))" and
    B: "IntMapK (S (Card n', n', run')) = Some b'"
  show
   "Pri_AgrK (priAK n) \<notin> items (insert (Auth_Data (priAK n') b')
      (insert ?M (A \<union> spies evsR4))) \<and>
    (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
      Pri_AgrK b \<notin> items (insert (Auth_Data (priAK n') b')
        (insert ?M (A \<union> spies evsR4))))"
  proof (subst (1 2) insert_commute, simp add: items_mpair,
   subst (1 3) insert_commute, simp add: items_simp_insert_2,
   subst (1 2) insert_commute, simp add: items_crypt items_simp_insert_2)
    have C: "Pri_AgrK (priAK n') \<notin> items (A \<union> spies evsR4) \<and>
      (IntMapK (S (Card n', n', run')) = Some b' \<longrightarrow>
        Pri_AgrK b' \<notin> items (A \<union> spies evsR4))"
     using A .
    hence "Pri_AgrK (priAK n') \<notin> items (A \<union> spies evsR4)" ..
    moreover have "Pri_AgrK b' \<notin> items (A \<union> spies evsR4)"
     using B and C by simp
    ultimately show
     "Pri_AgrK (priAK n) \<notin> items (insert (Auth_Data (priAK n') b')
        (A \<union> spies evsR4)) \<and>
      (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
        Pri_AgrK b \<notin> items (insert (Auth_Data (priAK n') b')
          (A \<union> spies evsR4)))"
     by (simp add: items_auth_data_out A)
  qed
next
  fix evsFR4 A s a b' c f g n run b and S :: state
  let ?M = "\<lbrace>pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>"
  assume
    A: "\<And>n run b. Pri_AgrK (priAK n) \<notin> items (A \<union> spies evsFR4) \<and>
      (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
        Pri_AgrK b \<notin> items (A \<union> spies evsFR4))" and
    B: "Crypt (sesK (c * f)) \<lbrace>pubAK (c * (s + a * b')), Auth_Data g b', ?M\<rbrace>
      \<in> synth (analz (A \<union> spies evsFR4))"
    (is "Crypt _ ?M' \<in> synth (analz ?A)")
  have C: "Pri_AgrK b' \<in> items ?A \<or> Pri_AgrK g \<in> items ?A \<longrightarrow>
    Pri_AgrK b' \<in> items ?A \<and> Pri_AgrK g \<in> items ?A"
    (is "?P \<longrightarrow> ?Q")
  proof
    assume ?P
    have "Crypt (sesK (c * f)) ?M' \<in> analz ?A \<or>
      ?M' \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
     using B by (rule synth_crypt)
    moreover {
      assume "Crypt (sesK (c * f)) ?M' \<in> analz ?A"
      hence "Crypt (sesK (c * f)) ?M' \<in> items ?A"
       by (rule subsetD [OF analz_items_subset])
      hence "?M' \<in> items ?A"
       by (rule items.Body)
      hence "\<lbrace>Auth_Data g b', pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> items ?A"
       by (rule items.Snd)
      hence D: "Auth_Data g b' \<in> items ?A"
       by (rule items.Fst)
      have ?Q
      proof (rule disjE [OF \<open>?P\<close>])
        assume "Pri_AgrK b' \<in> items ?A"
        moreover from this have "Pri_AgrK g \<in> items ?A"
         by (rule items.Auth_Fst [OF D])
        ultimately show ?Q ..
      next
        assume "Pri_AgrK g \<in> items ?A"
        moreover from this have "Pri_AgrK b' \<in> items ?A"
         by (rule items.Auth_Snd [OF D])
        ultimately show ?Q
         by simp
      qed
    }
    moreover {
      assume "?M' \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
      hence "?M' \<in> synth (analz ?A)" ..
      hence "\<lbrace>Auth_Data g b', pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> synth (analz ?A)"
       by (rule synth_analz_snd)
      hence "Auth_Data g b' \<in> synth (analz ?A)"
       by (rule synth_analz_fst)
      hence "Auth_Data g b' \<in> analz ?A \<or>
        Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b' \<in> analz ?A"
       by (rule synth_auth_data)
      moreover {
        assume "Auth_Data g b' \<in> analz ?A"
        hence D: "Auth_Data g b' \<in> items ?A"
         by (rule subsetD [OF analz_items_subset])
        have ?Q
        proof (rule disjE [OF \<open>?P\<close>])
          assume "Pri_AgrK b' \<in> items ?A"
          moreover from this have "Pri_AgrK g \<in> items ?A"
           by (rule items.Auth_Fst [OF D])
          ultimately show ?Q ..
        next
          assume "Pri_AgrK g \<in> items ?A"
          moreover from this have "Pri_AgrK b' \<in> items ?A"
           by (rule items.Auth_Snd [OF D])
          ultimately show ?Q
           by simp
        qed
      }
      moreover {
        assume D: "Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b' \<in> analz ?A"
        hence "Pri_AgrK b' \<in> analz ?A" ..
        hence "Pri_AgrK b' \<in> items ?A"
         by (rule subsetD [OF analz_items_subset])
        moreover have "Pri_AgrK g \<in> analz ?A"     
         using D ..
        hence "Pri_AgrK g \<in> items ?A"
         by (rule subsetD [OF analz_items_subset])
        ultimately have ?Q ..
      }
      ultimately have ?Q ..
    }
    ultimately show ?Q ..
  qed
  show
   "Pri_AgrK (priAK n) \<notin> items (insert (Auth_Data g b')
      (insert ?M (A \<union> spies evsFR4))) \<and>
    (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
      Pri_AgrK b \<notin> items (insert (Auth_Data g b')
        (insert ?M (A \<union> spies evsFR4))))"
  proof (subst (1 2) insert_commute, simp add: items_mpair,
   subst (1 3) insert_commute, simp add: items_simp_insert_2,
   subst (1 2) insert_commute, simp add: items_crypt items_simp_insert_2, cases ?P)
    case True
    with C have ?Q ..
    thus
     "Pri_AgrK (priAK n) \<notin> items (insert (Auth_Data g b')
        (A \<union> spies evsFR4)) \<and>
      (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
        Pri_AgrK b \<notin> items (insert (Auth_Data g b')
          (A \<union> spies evsFR4)))"
     by (simp add: items_auth_data_in items_simp_insert_1 A)
  next
    case False
    thus
     "Pri_AgrK (priAK n) \<notin> items (insert (Auth_Data g b')
        (A \<union> spies evsFR4)) \<and>
      (IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
        Pri_AgrK b \<notin> items (insert (Auth_Data g b')
          (A \<union> spies evsFR4)))"
     by (simp add: items_auth_data_out A)
  qed
qed

lemma pr_auth_key_analz:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> Pri_AgrK (priAK n) \<notin> analz (A \<union> spies evs)"
proof (rule contra_subsetD [OF analz_items_subset], drule pr_auth_data_items)
qed (erule conjE)

lemma pr_int_mapk_analz:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    IntMapK (S (Card n, n, run)) = Some b \<Longrightarrow>
  Pri_AgrK b \<notin> analz (A \<union> spies evs)"
proof (rule contra_subsetD [OF analz_items_subset], drule pr_auth_data_items)
qed (erule conjE, rule mp)

lemma pr_key_set_unused [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
  analz (H \<union> A \<union> spies evs) = H \<union> analz (A \<union> spies evs)"
proof (induction arbitrary: H rule: protocol.induct, simp_all add: analz_simp_insert_2,
 rule impI, (subst analz_simp, blast)+, simp)
  fix evsR1 S A U n s H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsR1) = H \<union> analz (A \<union> spies evsR1)" and
    B: "(evsR1, S, A, U) \<in> protocol" and
    C: "Pri_AgrK s \<notin> U"
  let
    ?B = "H \<union> A \<union> spies evsR1" and
    ?C = "A \<union> spies evsR1"
  show
   "(n \<in> bad \<longrightarrow>
       H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK s) U \<longrightarrow>
     analz (insert (Crypt (symK n) (Pri_AgrK s)) (insert (Pri_AgrK s) ?B)) =
     H \<union> analz (insert (Crypt (symK n) (Pri_AgrK s)) (insert (Pri_AgrK s) ?C))) \<and>
    (n \<notin> bad \<longrightarrow>
       H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK s) U \<longrightarrow>
     analz (insert (Crypt (symK n) (Pri_AgrK s)) ?B) =
     H \<union> analz (insert (Crypt (symK n) (Pri_AgrK s)) ?C))"
    (is "(_ \<longrightarrow> _ \<longrightarrow> ?T) \<and> (_ \<longrightarrow> _ \<longrightarrow> ?T')")
  proof (rule conjI, (rule_tac [!] impI)+)
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK s) U"
    hence "insert (Pri_AgrK s) H \<subseteq> range Key \<union> range Pri_AgrK - U"
     using C by blast
    with A have "analz (insert (Pri_AgrK s) H \<union> A \<union> spies evsR1) =
      insert (Pri_AgrK s) H \<union> analz (A \<union> spies evsR1)" ..
    hence "analz (insert (Pri_AgrK s) ?B) = H \<union> insert (Pri_AgrK s) (analz ?C)"
     by simp
    moreover have "{Pri_AgrK s} \<subseteq> range Key \<union> range Pri_AgrK - U"
     using C by simp
    with A have "analz ({Pri_AgrK s} \<union> A \<union> spies evsR1) =
      {Pri_AgrK s} \<union> analz (A \<union> spies evsR1)" ..
    hence "insert (Pri_AgrK s) (analz ?C) = analz (insert (Pri_AgrK s) ?C)"
     by simp
    ultimately have D: "analz (insert (Pri_AgrK s) ?B) =
      H \<union> analz (insert (Pri_AgrK s) ?C)"
     by simp
    assume "n \<in> bad"
    hence E: "Key (invK (symK n)) \<in> analz ?C"
     using B by (simp add: pr_symk_analz invK_symK)
    have "Key (invK (symK n)) \<in> analz (insert (Pri_AgrK s) ?B)"
     by (rule subsetD [OF _ E], rule analz_mono, blast)
    hence "analz (insert (Crypt (symK n) (Pri_AgrK s)) (insert (Pri_AgrK s) ?B)) =
      insert (Crypt (symK n) (Pri_AgrK s)) (analz (insert (Pri_AgrK s) ?B))"
     by (simp add: analz_crypt_in)
    moreover have "Key (invK (symK n)) \<in> analz (insert (Pri_AgrK s) ?C)"
     by (rule subsetD [OF _ E], rule analz_mono, blast)
    hence "analz (insert (Crypt (symK n) (Pri_AgrK s)) (insert (Pri_AgrK s) ?C)) =
      insert (Crypt (symK n) (Pri_AgrK s)) (analz (insert (Pri_AgrK s) ?C))"
     by (simp add: analz_crypt_in)
    ultimately show ?T
     using D by simp
  next
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK s) U"
    hence D: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
     by blast
    with A have E: "analz ?B = H \<union> analz ?C" ..
    moreover assume "n \<notin> bad"
    hence F: "Key (invK (symK n)) \<notin> analz ?C"
     using B by (simp add: pr_symk_analz invK_symK)
    ultimately have "Key (invK (symK n)) \<notin> analz ?B"
    proof (simp add: invK_symK, insert pr_symk_used [OF B, of n])
    qed (rule notI, drule subsetD [OF D], simp)
    hence "analz (insert (Crypt (symK n) (Pri_AgrK s)) ?B) =
      insert (Crypt (symK n) (Pri_AgrK s)) (analz ?B)"
     by (simp add: analz_crypt_out)
    moreover have "H \<union> analz (insert (Crypt (symK n) (Pri_AgrK s)) ?C) =
      insert (Crypt (symK n) (Pri_AgrK s)) (H \<union> analz ?C)"
     using F by (simp add: analz_crypt_out)
    ultimately show ?T'
     using E by simp
  qed
next
  fix evsFR1 S A U m s H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsFR1) = H \<union> analz (A \<union> spies evsFR1)" and
    B: "(evsFR1, S, A, U) \<in> protocol" and
    C: "Crypt (symK m) (Pri_AgrK s) \<in> synth (analz (A \<union> spies evsFR1))"
  let
    ?B = "H \<union> A \<union> spies evsFR1" and
    ?C = "A \<union> spies evsFR1"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (symK m) (Pri_AgrK s)) ?B) =
    H \<union> analz (insert (Crypt (symK m) (Pri_AgrK s)) ?C)"
    (is "_ \<longrightarrow> ?T")
  proof (rule impI, cases "Key (invK (symK m)) \<in> analz ?C")
    case True
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have "analz ?B = H \<union> analz ?C" ..
    moreover have "Pri_AgrK s \<in> analz ?C"
    proof (insert synth_crypt [OF C], erule disjE, erule_tac [2] conjE)
      assume "Crypt (symK m) (Pri_AgrK s) \<in> analz ?C"
      thus ?thesis
       using True by (rule analz.Decrypt)
    next
      assume "Pri_AgrK s \<in> synth (analz ?C)"
      thus ?thesis
       by (rule synth_simp_intro, simp)
    qed
    moreover from this have "Pri_AgrK s \<in> analz ?B"
     by (rule rev_subsetD, rule_tac analz_mono, blast)
    ultimately have D: "analz (insert (Pri_AgrK s) ?B) =
      H \<union> analz (insert (Pri_AgrK s) ?C)"
     by (simp add: analz_simp_insert_1)
    have "Key (invK (symK m)) \<in> analz ?B"
     by (rule subsetD [OF _ True], rule analz_mono, blast)
    hence "analz (insert (Crypt (symK m) (Pri_AgrK s)) ?B) =
      insert (Crypt (symK m) (Pri_AgrK s)) (analz (insert (Pri_AgrK s) ?B))"
     by (simp add: analz_crypt_in)
    moreover have "analz (insert (Crypt (symK m) (Pri_AgrK s)) ?C) =
      insert (Crypt (symK m) (Pri_AgrK s)) (analz (insert (Pri_AgrK s) ?C))"
     using True by (simp add: analz_crypt_in)
    ultimately show ?T
     using D by simp
  next
    case False
    moreover assume D: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have E: "analz ?B = H \<union> analz ?C" ..
    ultimately have "Key (invK (symK m)) \<notin> analz ?B"
    proof (simp add: invK_symK, insert pr_symk_used [OF B, of m])
    qed (rule notI, drule subsetD [OF D], simp)
    hence "analz (insert (Crypt (symK m) (Pri_AgrK s)) ?B) =
      insert (Crypt (symK m) (Pri_AgrK s)) (analz ?B)"
     by (simp add: analz_crypt_out)
    moreover have "H \<union> analz (insert (Crypt (symK m) (Pri_AgrK s)) ?C) =
      insert (Crypt (symK m) (Pri_AgrK s)) (H \<union> analz ?C)"
     using False by (simp add: analz_crypt_out)
    ultimately show ?T
     using E by simp
  qed
next
  fix evsC2 S A U a H and m :: nat
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsC2) = H \<union> analz (A \<union> spies evsC2)" and
    B: "Pri_AgrK a \<notin> U"
  let
    ?B = "H \<union> A \<union> spies evsC2" and
    ?C = "A \<union> spies evsC2"
  show
   "(m = 0 \<longrightarrow>
       H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK a) U \<longrightarrow>
     insert (pubAK a) (analz (insert (Pri_AgrK a) ?B)) =
     insert (pubAK a) (H \<union> analz (insert (Pri_AgrK a) ?C))) \<and>
    (0 < m \<longrightarrow>
       H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK a) U \<longrightarrow>
     insert (pubAK a) (analz ?B) =
     insert (pubAK a) (H \<union> analz ?C))"
    (is "(_ \<longrightarrow> _ \<longrightarrow> ?T) \<and> (_ \<longrightarrow> _ \<longrightarrow> ?T')")
  proof (rule conjI, (rule_tac [!] impI)+)
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK a) U"
    hence "insert (Pri_AgrK a) H \<subseteq> range Key \<union> range Pri_AgrK - U"
     using B by blast
    with A have "analz (insert (Pri_AgrK a) H \<union> A \<union> spies evsC2) =
      insert (Pri_AgrK a) H \<union> analz (A \<union> spies evsC2)" ..
    hence "analz (insert (Pri_AgrK a) ?B) = H \<union> insert (Pri_AgrK a) (analz ?C)"
     by simp
    moreover have "{Pri_AgrK a} \<subseteq> range Key \<union> range Pri_AgrK - U"
     using B by simp
    with A have "analz ({Pri_AgrK a} \<union> A \<union> spies evsC2) =
      {Pri_AgrK a} \<union> analz (A \<union> spies evsC2)" ..
    hence "insert (Pri_AgrK a) (analz ?C) = analz (insert (Pri_AgrK a) ?C)"
     by simp
    ultimately have "analz (insert (Pri_AgrK a) ?B) =
      H \<union> analz (insert (Pri_AgrK a) ?C)"
     by simp
    thus ?T
     by simp
  next
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK a) U"
    hence "H \<subseteq> range Key \<union> range Pri_AgrK - U"
     by blast
    with A have "analz ?B = H \<union> analz ?C" ..
    thus ?T'
     by simp
  qed
next
  fix evsR2 S A U b H
  assume A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (H \<union> A \<union> spies evsR2) = H \<union> analz (A \<union> spies evsR2)"
  let
    ?B = "H \<union> A \<union> spies evsR2" and
    ?C = "A \<union> spies evsR2"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK b) U \<longrightarrow>
    insert (pubAK b) (analz ?B) = insert (pubAK b) (H \<union> analz ?C)"
    (is "_ \<longrightarrow> ?T")
  proof
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK b) U"
    hence "H \<subseteq> range Key \<union> range Pri_AgrK - U"
     by blast
    with A have "analz ?B = H \<union> analz ?C" ..
    thus ?T
     by simp
  qed
next
  fix evsC3 S A U s a b c H and m :: nat
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsC3) = H \<union> analz (A \<union> spies evsC3)" and
    B: "Pri_AgrK c \<notin> U"
  let
    ?B = "H \<union> A \<union> spies evsC3" and
    ?C = "A \<union> spies evsC3"
  show
   "(m = 0 \<longrightarrow>
       H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK c) U \<longrightarrow>
     insert (pubAK (c * (s + a * b))) (analz (insert (Pri_AgrK c) ?B)) =
     insert (pubAK (c * (s + a * b))) (H \<union> analz (insert (Pri_AgrK c) ?C))) \<and>
    (0 < m \<longrightarrow>
       H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK c) U \<longrightarrow>
     insert (pubAK (c * (s + a * b))) (analz ?B) =
     insert (pubAK (c * (s + a * b))) (H \<union> analz ?C))"
    (is "(_ \<longrightarrow> _ \<longrightarrow> ?T) \<and> (_ \<longrightarrow> _ \<longrightarrow> ?T')")
  proof (rule conjI, (rule_tac [!] impI)+)
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK c) U"
    hence "insert (Pri_AgrK c) H \<subseteq> range Key \<union> range Pri_AgrK - U"
     using B by blast
    with A have "analz (insert (Pri_AgrK c) H \<union> A \<union> spies evsC3) =
      insert (Pri_AgrK c) H \<union> analz (A \<union> spies evsC3)" ..
    hence "analz (insert (Pri_AgrK c) ?B) = H \<union> insert (Pri_AgrK c) (analz ?C)"
     by simp
    moreover have "{Pri_AgrK c} \<subseteq> range Key \<union> range Pri_AgrK - U"
     using B by simp
    with A have "analz ({Pri_AgrK c} \<union> A \<union> spies evsC3) =
      {Pri_AgrK c} \<union> analz (A \<union> spies evsC3)" ..
    hence "insert (Pri_AgrK c) (analz ?C) = analz (insert (Pri_AgrK c) ?C)"
     by simp
    ultimately have "analz (insert (Pri_AgrK c) ?B) =
      H \<union> analz (insert (Pri_AgrK c) ?C)"
     by simp
    thus ?T
     by simp
  next
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK c) U"
    hence "H \<subseteq> range Key \<union> range Pri_AgrK - U"
     by blast
    with A have "analz ?B = H \<union> analz ?C" ..
    thus ?T'
     by simp
  qed
next
  fix evsR3 S A U n run s s' a b c d X H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsR3) = H \<union> analz (A \<union> spies evsR3)" and
    B: "Key (sesK (c * d * (s + a * b))) \<notin> U"
      (is "Key ?K \<notin> _")
  let
    ?B = "H \<union> A \<union> spies evsR3" and
    ?C = "A \<union> spies evsR3" and
    ?K' = "sesK (c * d * (s' + a * b))"
  show
   "(s' = s \<and> Pri_AgrK c \<in> analz (A \<union> spies evsR3) \<longrightarrow>
       H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK d)
         (insert (Key ?K) (insert \<lbrace>Key ?K, Agent X, Number n, Number run\<rbrace> U)) \<longrightarrow>
     insert (pubAK (d * (s + a * b))) (analz (insert (Key ?K) ?B)) =
     insert (pubAK (d * (s + a * b))) (H \<union> analz (insert (Key ?K) ?C))) \<and>
    ((s' = s \<longrightarrow> Pri_AgrK c \<notin> analz (A \<union> spies evsR3)) \<longrightarrow>
       H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK d) (insert (Key ?K')
         (insert (Key ?K) (insert \<lbrace>Key ?K, Agent X, Number n, Number run\<rbrace> U))) \<longrightarrow>
     insert (pubAK (d * (s + a * b))) (analz ?B) =
     insert (pubAK (d * (s + a * b))) (H \<union> analz ?C))"
    (is "(_ \<longrightarrow> _ \<longrightarrow> ?T) \<and> (_ \<longrightarrow> _ \<longrightarrow> ?T')")
  proof (rule conjI, (rule_tac [!] impI)+)
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK d)
      (insert (Key ?K) (insert \<lbrace>Key ?K, Agent X, Number n, Number run\<rbrace> U))"
    hence "insert (Key ?K) H \<subseteq> range Key \<union> range Pri_AgrK - U"
     using B by blast
    with A have "analz (insert (Key ?K) H \<union> A \<union> spies evsR3) =
      insert (Key ?K) H \<union> analz (A \<union> spies evsR3)" ..
    hence "analz (insert (Key ?K) ?B) = H \<union> insert (Key ?K) (analz ?C)"
     by simp
    moreover have "{Key ?K} \<subseteq> range Key \<union> range Pri_AgrK - U"
     using B by simp
    with A have "analz ({Key ?K} \<union> A \<union> spies evsR3) =
      {Key ?K} \<union> analz (A \<union> spies evsR3)" ..
    hence "insert (Key ?K) (analz ?C) = analz (insert (Key ?K) ?C)"
     by simp
    ultimately have "analz (insert (Key ?K) ?B) = H \<union> analz (insert (Key ?K) ?C)"
     by simp
    thus ?T
     by simp
  next
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Pri_AgrK d) (insert (Key ?K')
      (insert (Key ?K) (insert \<lbrace>Key ?K, Agent X, Number n, Number run\<rbrace> U)))"
    hence "H \<subseteq> range Key \<union> range Pri_AgrK - U"
     by blast
    with A have "analz ?B = H \<union> analz ?C" ..
    thus ?T'
     by simp
  qed
next
  fix evsFR3 S A U m n run s a b c d H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsFR3) = H \<union> analz (A \<union> spies evsFR3)" and
    B: "Key (sesK (c * d * (s + a * b))) \<notin> U"
      (is "Key ?K \<notin> _")
  let
    ?B = "H \<union> A \<union> spies evsFR3" and
    ?C = "A \<union> spies evsFR3"
  show
   "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Key ?K)
      (insert \<lbrace>Key ?K, Agent (User m), Number n, Number run\<rbrace> U) \<longrightarrow>
    insert (pubAK (d * (s + a * b))) (analz (insert (Key ?K) ?B)) =
    insert (pubAK (d * (s + a * b))) (H \<union> analz (insert (Key ?K) ?C))"
    (is "_ \<longrightarrow> ?T")
  proof
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - insert (Key ?K)
      (insert \<lbrace>Key ?K, Agent (User m), Number n, Number run\<rbrace> U)"
    hence "insert (Key ?K) H \<subseteq> range Key \<union> range Pri_AgrK - U"
     using B by blast
    with A have "analz (insert (Key ?K) H \<union> A \<union> spies evsFR3) =
      insert (Key ?K) H \<union> analz (A \<union> spies evsFR3)" ..
    hence "analz (insert (Key ?K) ?B) = H \<union> insert (Key ?K) (analz ?C)"
     by simp
    moreover have "{Key ?K} \<subseteq> range Key \<union> range Pri_AgrK - U"
     using B by simp
    with A have "analz ({Key ?K} \<union> A \<union> spies evsFR3) =
      {Key ?K} \<union> analz (A \<union> spies evsFR3)" ..
    hence "insert (Key ?K) (analz ?C) = analz (insert (Key ?K) ?C)"
     by simp
    ultimately have "analz (insert (Key ?K) ?B) = H \<union> analz (insert (Key ?K) ?C)"
     by simp
    thus ?T
     by simp
  qed
next
  fix evsC4 S A U m n run c f H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsC4) = H \<union> analz (A \<union> spies evsC4)" and
    B: "(evsC4, S, A, U) \<in> protocol" and
    C: "\<lbrace>Key (sesK (c * f)), Agent (User m), Number n, Number run\<rbrace> \<in> U"
  let
    ?B = "H \<union> A \<union> spies evsC4" and
    ?C = "A \<union> spies evsC4"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (sesK (c * f)) (pubAK f)) ?B) =
    H \<union> analz (insert (Crypt (sesK (c * f)) (pubAK f)) ?C)"
    (is "_ \<longrightarrow> ?T")
  proof (rule impI, cases "Key (invK (sesK (c * f))) \<in> analz ?C")
    case True
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have D: "analz ?B = H \<union> analz ?C" ..
    have "Key (invK (sesK (c * f))) \<in> analz ?B"
     by (rule subsetD [OF _ True], rule analz_mono, blast)
    hence "analz (insert (Crypt (sesK (c * f)) (pubAK f)) ?B) =
      insert (Crypt (sesK (c * f)) (pubAK f)) (insert (pubAK f) (analz ?B))"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    moreover have "H \<union> analz (insert (Crypt (sesK (c * f)) (pubAK f)) ?C) =
      insert (Crypt (sesK (c * f)) (pubAK f)) (insert (pubAK f) (H \<union> analz ?C))"
     using True by (simp add: analz_crypt_in analz_simp_insert_2)
    ultimately show ?T
     using D by simp
  next
    case False
    moreover assume D: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have E: "analz ?B = H \<union> analz ?C" ..
    ultimately have "Key (invK (sesK (c * f))) \<notin> analz ?B"
    proof (simp add: invK_sesK, insert pr_sesk_user_2 [OF B C])
    qed (rule notI, drule subsetD [OF D], simp)
    hence "analz (insert (Crypt (sesK (c * f)) (pubAK f)) ?B) =
      insert (Crypt (sesK (c * f)) (pubAK f)) (analz ?B)"
     by (simp add: analz_crypt_out)
    moreover have "H \<union> analz (insert (Crypt (sesK (c * f)) (pubAK f)) ?C) =
      insert (Crypt (sesK (c * f)) (pubAK f)) (H \<union> analz ?C)"
     using False by (simp add: analz_crypt_out)
    ultimately show ?T
     using E by simp
  qed
next
  fix evsFC4 S A U n run s a b d e H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsFC4) = H \<union> analz (A \<union> spies evsFC4)" and
    B: "(evsFC4, S, A, U) \<in> protocol" and
    C: "IntAgrK (S (Card n, n, run)) = Some d" and
    D: "ExtAgrK (S (Card n, n, run)) = Some e"
  let
    ?B = "H \<union> A \<union> spies evsFC4" and
    ?C = "A \<union> spies evsFC4" and
    ?f = "d * (s + a * b)"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (sesK (d * e)) (pubAK ?f)) ?B) =
    H \<union> analz (insert (Crypt (sesK (d * e)) (pubAK ?f)) ?C)"
    (is "_ \<longrightarrow> ?T")
  proof (rule impI, cases "Key (invK (sesK (d * e))) \<in> analz ?C")
    case True
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have E: "analz ?B = H \<union> analz ?C" ..
    have "Key (invK (sesK (d * e))) \<in> analz ?B"
     by (rule subsetD [OF _ True], rule analz_mono, blast)
    hence "analz (insert (Crypt (sesK (d * e)) (pubAK ?f)) ?B) =
      insert (Crypt (sesK (d * e)) (pubAK ?f)) (insert (pubAK ?f) (analz ?B))"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    moreover have "H \<union> analz (insert (Crypt (sesK (d * e)) (pubAK ?f)) ?C) =
      insert (Crypt (sesK (d * e)) (pubAK ?f)) (insert (pubAK ?f) (H \<union> analz ?C))"
     using True by (simp add: analz_crypt_in analz_simp_insert_2)
    ultimately show ?T
     using E by simp
  next
    case False
    moreover assume E: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have F: "analz ?B = H \<union> analz ?C" ..
    ultimately have "Key (invK (sesK (d * e))) \<notin> analz ?B"
    proof (simp add: invK_sesK, insert pr_sesk_card [OF B C D])
    qed (rule notI, drule subsetD [OF E], simp)
    hence "analz (insert (Crypt (sesK (d * e)) (pubAK ?f)) ?B) =
      insert (Crypt (sesK (d * e)) (pubAK ?f)) (analz ?B)"
     by (simp add: analz_crypt_out)
    moreover have "H \<union> analz (insert (Crypt (sesK (d * e)) (pubAK ?f)) ?C) =
      insert (Crypt (sesK (d * e)) (pubAK ?f)) (H \<union> analz ?C)"
     using False by (simp add: analz_crypt_out)
    ultimately show ?T
     using F by simp
  qed
next
  fix evsR4 S A U n run b d e H
  let
    ?B = "H \<union> A \<union> spies evsR4" and
    ?C = "A \<union> spies evsR4" and
    ?H = "Hash (pubAK (priAK n))" and
    ?M = "\<lbrace>pubAK (priAK n), Crypt (priSK CA) (Hash (pubAK (priAK n)))\<rbrace>" and
    ?M' = "\<lbrace>pubAK e, Auth_Data (priAK n) b, pubAK (priAK n),
      Crypt (priSK CA) (Hash (pubAK (priAK n)))\<rbrace>"
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsR4) = H \<union> analz (A \<union> spies evsR4)" and
    B: "(evsR4, S, A, U) \<in> protocol" and
    C: "IntMapK (S (Card n, n, run)) = Some b" and
    D: "IntAgrK (S (Card n, n, run)) = Some d" and
    E: "ExtAgrK (S (Card n, n, run)) = Some e"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (sesK (d * e)) ?M') ?B) =
    H \<union> analz (insert (Crypt (sesK (d * e)) ?M') ?C)"
    (is "_ \<longrightarrow> ?T")
  proof
    assume F: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have G: "analz ?B = H \<union> analz ?C" ..
    have H: "Key (pubSK CA) \<in> analz ?C"
     using B by (rule pr_valid_key_analz)
    hence I: "analz (insert (Crypt (priSK CA) ?H) ?C) =
      {Crypt (priSK CA) ?H, ?H} \<union> analz ?C"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    have "Key (pubSK CA) \<in> analz ?B"
     by (rule subsetD [OF _ H], rule analz_mono, blast)
    hence J: "analz (insert (Crypt (priSK CA) ?H) ?B) =
      {Crypt (priSK CA) ?H, ?H} \<union> analz ?B"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    have K: "Pri_AgrK (priAK n) \<notin> analz ?C"
     using B by (rule pr_auth_key_analz)
    hence L: "Pri_AgrK (priAK n) \<notin> analz (insert (Crypt (priSK CA) ?H) ?C)"
     using I by simp
    have M: "Pri_AgrK b \<notin> analz ?C"
     using B and C by (rule pr_int_mapk_analz)
    hence N: "Pri_AgrK b \<notin> analz (insert (Crypt (priSK CA) ?H) ?C)"
     using I by simp
    have "Pri_AgrK (priAK n) \<in> U"
     using B by (rule pr_auth_key_used)
    hence "Pri_AgrK (priAK n) \<notin> H"
     using F by blast
    hence O: "Pri_AgrK (priAK n) \<notin> analz (insert (Crypt (priSK CA) ?H) ?B)"
     using G and J and K by simp
    have "Pri_AgrK b \<in> U"
     using B and C by (rule pr_int_mapk_used)
    hence "Pri_AgrK b \<notin> H"
     using F by blast
    hence P: "Pri_AgrK b \<notin> analz (insert (Crypt (priSK CA) ?H) ?B)"
     using G and J and M by simp
    show ?T
    proof (cases "Key (invK (sesK (d * e))) \<in> analz ?C")
      case True
      have Q: "Key (invK (sesK (d * e))) \<in> analz ?B"
       by (rule subsetD [OF _ True], rule analz_mono, blast)
      show ?T
      proof (simp add: analz_crypt_in analz_mpair analz_simp_insert_2 True Q,
       rule equalityI, (rule_tac [!] insert_mono)+)
        show "analz (insert (Auth_Data (priAK n) b) (insert ?M ?B)) \<subseteq>
          H \<union> analz (insert (Auth_Data (priAK n) b) (insert ?M ?C))"
        proof (subst (1 2) insert_commute, simp add: analz_mpair analz_simp_insert_2
         del: Un_insert_right, subst (1 3) insert_commute,
         subst analz_auth_data_out [OF O P], subst analz_auth_data_out [OF L N])
        qed (auto simp add: G I J)
      next
        show "H \<union> analz (insert (Auth_Data (priAK n) b) (insert ?M ?C)) \<subseteq>
          analz (insert (Auth_Data (priAK n) b) (insert ?M ?B))"
        proof (subst (1 2) insert_commute, simp add: analz_mpair analz_simp_insert_2
         del: Un_insert_right Un_subset_iff semilattice_sup_class.sup.bounded_iff,
         subst (1 3) insert_commute, subst analz_auth_data_out [OF L N],
         subst analz_auth_data_out [OF O P])
        qed (auto simp add: G I J)
      qed
    next
      case False
      hence "Key (invK (sesK (d * e))) \<notin> analz ?B"
      proof (simp add: invK_sesK G, insert pr_sesk_card [OF B D E])
      qed (rule notI, drule subsetD [OF F], simp)
      hence "analz (insert (Crypt (sesK (d * e)) ?M') ?B) =
        insert (Crypt (sesK (d * e)) ?M') (analz ?B)"
       by (simp add: analz_crypt_out)
      moreover have "H \<union> analz (insert (Crypt (sesK (d * e)) ?M') ?C) =
        insert (Crypt (sesK (d * e)) ?M') (H \<union> analz ?C)"
       using False by (simp add: analz_crypt_out)
      ultimately show ?T
       using G by simp
    qed
  qed
next
  fix evsFR4 S A U m n run s a b c f g H
  let
    ?B = "H \<union> A \<union> spies evsFR4" and
    ?C = "A \<union> spies evsFR4" and
    ?H = "Hash (pubAK g)" and
    ?M = "\<lbrace>pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>" and
    ?M' = "\<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
      Crypt (priSK CA) (Hash (pubAK g))\<rbrace>"
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsFR4) = H \<union> analz (A \<union> spies evsFR4)" and
    B: "(evsFR4, S, A, U) \<in> protocol" and
    C: "IntAgrK (S (User m, n, run)) = Some c" and
    D: "ExtAgrK (S (User m, n, run)) = Some f" and
    E: "Crypt (sesK (c * f)) ?M' \<in> synth (analz ?C)"
  have F:
   "Key (invK (sesK (c * f))) \<in> analz ?C \<longrightarrow>
      Pri_AgrK b \<in> analz ?C \<or> Pri_AgrK g \<in> analz ?C \<longrightarrow>
    Pri_AgrK b \<in> analz ?C \<and> Pri_AgrK g \<in> analz ?C"
    (is "?P \<longrightarrow> ?Q \<longrightarrow> ?R")
  proof (rule impI)+
    assume ?P and ?Q
    have "Crypt (sesK (c * f)) ?M' \<in> analz ?C \<or>
      ?M' \<in> synth (analz ?C) \<and> Key (sesK (c * f)) \<in> analz ?C"
     using E by (rule synth_crypt)
    moreover {
      assume "Crypt (sesK (c * f)) ?M' \<in> analz ?C"
      hence "?M' \<in> analz ?C"
       using \<open>?P\<close> by (rule analz.Decrypt)
      hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> analz ?C"
       by (rule analz.Snd)
      hence G: "Auth_Data g b \<in> analz ?C"
       by (rule analz.Fst)
      have ?R
      proof (rule disjE [OF \<open>?Q\<close>])
        assume "Pri_AgrK b \<in> analz ?C"
        moreover from this have "Pri_AgrK g \<in> analz ?C"
         by (rule analz.Auth_Fst [OF G])
        ultimately show ?R ..
      next
        assume "Pri_AgrK g \<in> analz ?C"
        moreover from this have "Pri_AgrK b \<in> analz ?C"
         by (rule analz.Auth_Snd [OF G])
        ultimately show ?R
         by simp
      qed
    }
    moreover {
      assume "?M' \<in> synth (analz ?C) \<and> Key (sesK (c * f)) \<in> analz ?C"
      hence "?M' \<in> synth (analz ?C)" ..
      hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> synth (analz ?C)"
       by (rule synth_analz_snd)
      hence "Auth_Data g b \<in> synth (analz ?C)"
       by (rule synth_analz_fst)
      hence "Auth_Data g b \<in> analz ?C \<or>
        Pri_AgrK g \<in> analz ?C \<and> Pri_AgrK b \<in> analz ?C"
       by (rule synth_auth_data)
      moreover {
        assume G: "Auth_Data g b \<in> analz ?C"
        have ?R
        proof (rule disjE [OF \<open>?Q\<close>])
          assume "Pri_AgrK b \<in> analz ?C"
          moreover from this have "Pri_AgrK g \<in> analz ?C"
           by (rule analz.Auth_Fst [OF G])
          ultimately show ?R ..
        next
          assume "Pri_AgrK g \<in> analz ?C"
          moreover from this have "Pri_AgrK b \<in> analz ?C"
           by (rule analz.Auth_Snd [OF G])
          ultimately show ?R
           by simp
        qed
      }
      moreover {
        assume "Pri_AgrK g \<in> analz ?C \<and> Pri_AgrK b \<in> analz ?C"
        hence ?R
         by simp
      }
      ultimately have ?R ..
    }
    ultimately show ?R ..
  qed
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (sesK (c * f)) ?M') ?B) =
    H \<union> analz (insert (Crypt (sesK (c * f)) ?M') ?C)"
    (is "_ \<longrightarrow> ?T")
  proof
    assume G: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have H: "analz ?B = H \<union> analz ?C" ..
    have I: "Key (pubSK CA) \<in> analz ?C"
     using B by (rule pr_valid_key_analz)
    hence J: "analz (insert (Crypt (priSK CA) ?H) ?C) =
      {Crypt (priSK CA) ?H, ?H} \<union> analz ?C"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    have "Key (pubSK CA) \<in> analz ?B"
     by (rule subsetD [OF _ I], rule analz_mono, blast)
    hence K: "analz (insert (Crypt (priSK CA) ?H) ?B) =
      {Crypt (priSK CA) ?H, ?H} \<union> analz ?B"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    show ?T
    proof (cases "Key (invK (sesK (c * f))) \<in> analz ?C",
     cases "Pri_AgrK g \<in> analz ?C \<or> Pri_AgrK b \<in> analz ?C", simp_all)
      assume L: "Key (invK (sesK (c * f))) \<in> analz ?C"
      have M: "Key (invK (sesK (c * f))) \<in> analz ?B"
       by (rule subsetD [OF _ L], rule analz_mono, blast)
      assume N: "Pri_AgrK g \<in> analz ?C \<or> Pri_AgrK b \<in> analz ?C"
      hence O: "Pri_AgrK g \<in> analz (insert (Crypt (priSK CA) ?H) ?C) \<or>
        Pri_AgrK b \<in> analz (insert (Crypt (priSK CA) ?H) ?C)"
       using J by simp
      have "Pri_AgrK g \<in> analz ?B \<or> Pri_AgrK b \<in> analz ?B"
       using H and N by blast
      hence P: "Pri_AgrK g \<in> analz (insert (Crypt (priSK CA) ?H) ?B) \<or>
        Pri_AgrK b \<in> analz (insert (Crypt (priSK CA) ?H) ?B)"
       using K by simp
      have Q: "Pri_AgrK b \<in> analz ?C \<and> Pri_AgrK g \<in> analz ?C"
       using F and L and N by blast
      hence "Pri_AgrK g \<in> analz (insert (Crypt (priSK CA) ?H) ?C)"
       using J by simp
      hence R: "Pri_AgrK g \<in> analz (insert (Pri_AgrK b)
        (insert (Crypt (priSK CA) ?H) ?C))"
       by (rule rev_subsetD, rule_tac analz_mono, blast)
      have S: "Pri_AgrK b \<in> analz (insert (Crypt (priSK CA) ?H) ?C)"
       using J and Q by simp
      have T: "Pri_AgrK b \<in> analz ?B \<and> Pri_AgrK g \<in> analz ?B"
       using H and Q by simp
      hence "Pri_AgrK g \<in> analz (insert (Crypt (priSK CA) ?H) ?B)"
       using K by simp
      hence U: "Pri_AgrK g \<in> analz (insert (Pri_AgrK b)
        (insert (Crypt (priSK CA) ?H) ?B))"
       by (rule rev_subsetD, rule_tac analz_mono, blast)
      have V: "Pri_AgrK b \<in> analz (insert (Crypt (priSK CA) ?H) ?B)"
       using K and T by simp
      show ?T
      proof (simp add: analz_crypt_in analz_mpair analz_simp_insert_2 L M,
       rule equalityI, (rule_tac [!] insert_mono)+)
        show "analz (insert (Auth_Data g b) (insert ?M ?B)) \<subseteq>
          H \<union> analz (insert (Auth_Data g b) (insert ?M ?C))"
        proof (subst (1 2) insert_commute, simp add: analz_mpair analz_simp_insert_2
         del: Un_insert_right, subst (1 3) insert_commute,
         subst analz_auth_data_in [OF P], subst analz_auth_data_in [OF O],
         simp del: Un_insert_right)
          show
           "analz (insert (Pri_AgrK g) (insert (Pri_AgrK b)
              (insert (Crypt (priSK CA) ?H) ?B))) \<subseteq>
            H \<union> insert ?M (insert (pubAK g) (insert (Auth_Data g b)
              (analz (insert (Pri_AgrK g) (insert (Pri_AgrK b)
                (insert (Crypt (priSK CA) ?H) ?C))))))"
          proof (subst analz_simp_insert_1 [OF U], subst analz_simp_insert_1 [OF V],
           subst analz_simp_insert_1 [OF R], subst analz_simp_insert_1 [OF S])
          qed (auto simp add: H J K)
        qed
      next
        show "H \<union> analz (insert (Auth_Data g b) (insert ?M ?C)) \<subseteq>
          analz (insert (Auth_Data g b) (insert ?M ?B))"
        proof (subst (1 2) insert_commute, simp add: analz_mpair analz_simp_insert_2
         del: Un_insert_right Un_subset_iff semilattice_sup_class.sup.bounded_iff,
         subst (2 4) insert_commute, subst analz_auth_data_in [OF O],
         subst analz_auth_data_in [OF P], simp only: Un_insert_left Un_empty_left)
          show
           "H \<union> insert ?M (insert (pubAK g) (insert (Auth_Data g b)
              (analz (insert (Pri_AgrK g) (insert (Pri_AgrK b)
                (insert (Crypt (priSK CA) ?H) ?C)))))) \<subseteq>
            insert ?M (insert (pubAK g) (insert (Auth_Data g b)
              (analz (insert (Pri_AgrK g) (insert (Pri_AgrK b)
                (insert (Crypt (priSK CA) ?H) ?B))))))"
          proof (subst analz_simp_insert_1 [OF R], subst analz_simp_insert_1 [OF S],
           subst analz_simp_insert_1 [OF U], subst analz_simp_insert_1 [OF V])
          qed (auto simp add: H J K)
        qed
      qed
    next
      assume L: "Key (invK (sesK (c * f))) \<in> analz ?C"
      have M: "Key (invK (sesK (c * f))) \<in> analz ?B"
       by (rule subsetD [OF _ L], rule analz_mono, blast)
      assume N: "Pri_AgrK g \<notin> analz ?C \<and> Pri_AgrK b \<notin> analz ?C"
      hence O: "Pri_AgrK g \<notin> analz (insert (Crypt (priSK CA) ?H) ?C)"
       using J by simp
      have P: "Pri_AgrK b \<notin> analz (insert (Crypt (priSK CA) ?H) ?C)"
       using J and N by simp
      have Q: "Pri_AgrK g \<in> U \<and> Pri_AgrK b \<in> U"
      proof -
        have "Crypt (sesK (c * f)) ?M' \<in> analz ?C \<or>
          ?M' \<in> synth (analz ?C) \<and> Key (sesK (c * f)) \<in> analz ?C"
         using E by (rule synth_crypt)
        moreover {
          assume "Crypt (sesK (c * f)) ?M' \<in> analz ?C"
          hence "Crypt (sesK (c * f)) ?M' \<in> parts ?C"
           by (rule subsetD [OF analz_parts_subset])
          hence "?M' \<in> parts ?C"
           by (rule parts.Body)
          hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
            \<in> parts ?C"
           by (rule parts.Snd)
          hence R: "Auth_Data g b \<in> parts ?C"
           by (rule parts.Fst)
          hence "Pri_AgrK g \<in> parts ?C"
           by (rule parts.Auth_Fst)
          hence "Pri_AgrK g \<in> U"
           by (rule contrapos_pp, rule_tac pr_pri_agrk_parts [OF B])
          moreover have "Pri_AgrK b \<in> parts ?C"
           using R by (rule parts.Auth_Snd)
          hence "Pri_AgrK b \<in> U"
           by (rule contrapos_pp, rule_tac pr_pri_agrk_parts [OF B])
          ultimately have ?thesis ..
        }
        moreover {
          assume "?M' \<in> synth (analz ?C) \<and>
            Key (sesK (c * f)) \<in> analz ?C"
          hence "?M' \<in> synth (analz ?C)" ..
          hence "\<lbrace>Auth_Data g b, pubAK g,
            Crypt (priSK CA) (Hash (pubAK g))\<rbrace> \<in> synth (analz ?C)"
           by (rule synth_analz_snd)
          hence "Auth_Data g b \<in> synth (analz ?C)"
           by (rule synth_analz_fst)
          hence "Auth_Data g b \<in> analz ?C \<or>
            Pri_AgrK g \<in> analz ?C \<and> Pri_AgrK b \<in> analz ?C"
           by (rule synth_auth_data)
          moreover {
            assume "Auth_Data g b \<in> analz ?C"
            hence R: "Auth_Data g b \<in> parts ?C"
             by (rule subsetD [OF analz_parts_subset])
            hence "Pri_AgrK g \<in> parts ?C"
             by (rule parts.Auth_Fst)
            hence "Pri_AgrK g \<in> U"
             by (rule contrapos_pp, rule_tac pr_pri_agrk_parts [OF B])
            moreover have "Pri_AgrK b \<in> parts ?C"
             using R by (rule parts.Auth_Snd)
            hence "Pri_AgrK b \<in> U"
             by (rule contrapos_pp, rule_tac pr_pri_agrk_parts [OF B])
            ultimately have ?thesis ..
          }
          moreover {
            assume R: "Pri_AgrK g \<in> analz ?C \<and> Pri_AgrK b \<in> analz ?C"
            hence "Pri_AgrK g \<in> analz ?C" ..
            hence "Pri_AgrK g \<in> parts ?C"
             by (rule subsetD [OF analz_parts_subset])
            hence "Pri_AgrK g \<in> U"
             by (rule contrapos_pp, rule_tac pr_pri_agrk_parts [OF B])
            moreover have "Pri_AgrK b \<in> analz ?C"
             using R ..
            hence "Pri_AgrK b \<in> parts ?C"
             by (rule subsetD [OF analz_parts_subset])
            hence "Pri_AgrK b \<in> U"
             by (rule contrapos_pp, rule_tac pr_pri_agrk_parts [OF B])
            ultimately have ?thesis ..
          }
          ultimately have ?thesis ..
        }
        ultimately show ?thesis ..
      qed
      have R: "Pri_AgrK g \<notin> analz ?B \<and> Pri_AgrK b \<notin> analz ?B"
      proof (simp add: H N, rule conjI, rule_tac [!] notI, drule_tac [!] subsetD [OF G])
      qed (simp_all add: Q)
      hence S: "Pri_AgrK g \<notin> analz (insert (Crypt (priSK CA) ?H) ?B)"
       using K by simp
      have T: "Pri_AgrK b \<notin> analz (insert (Crypt (priSK CA) ?H) ?B)"
       using K and R by simp
      show ?T
      proof (simp add: analz_crypt_in analz_mpair analz_simp_insert_2 L M,
       rule equalityI, (rule_tac [!] insert_mono)+)
        show "analz (insert (Auth_Data g b) (insert ?M ?B)) \<subseteq>
          H \<union> analz (insert (Auth_Data g b) (insert ?M ?C))"
        proof (subst (1 2) insert_commute, simp add: analz_mpair analz_simp_insert_2
         del: Un_insert_right, subst (1 3) insert_commute,
         subst analz_auth_data_out [OF S T], subst analz_auth_data_out [OF O P])
        qed (auto simp add: H J K)
      next
        show "H \<union> analz (insert (Auth_Data g b) (insert ?M ?C)) \<subseteq>
          analz (insert (Auth_Data g b) (insert ?M ?B))"
        proof (subst (1 2) insert_commute, simp add: analz_mpair analz_simp_insert_2
         del: Un_insert_right Un_subset_iff semilattice_sup_class.sup.bounded_iff,
         subst (2 4) insert_commute, subst analz_auth_data_out [OF O P],
         subst analz_auth_data_out [OF S T])
        qed (simp add: H J K)
      qed
    next
      assume L: "Key (invK (sesK (c * f))) \<notin> analz ?C"
      hence "Key (invK (sesK (c * f))) \<notin> analz ?B"
      proof (simp add: invK_sesK, insert pr_sesk_user_1 [OF B C D,
       THEN pr_sesk_user_2 [OF B]])
      qed (rule notI, simp add: H, drule subsetD [OF G], simp)
      hence "analz (insert (Crypt (sesK (c * f)) ?M') ?B) =
        insert (Crypt (sesK (c * f)) ?M') (analz ?B)"
       by (simp add: analz_crypt_out)
      moreover have "H \<union> analz (insert (Crypt (sesK (c * f)) ?M') ?C) =
        insert (Crypt (sesK (c * f)) ?M') (H \<union> analz ?C)"
       using L by (simp add: analz_crypt_out)
      ultimately show ?T
       using H by simp
    qed
  qed
next
  fix evsC5 S A U m n run c f H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsC5) = H \<union> analz (A \<union> spies evsC5)" and
    B: "(evsC5, S, A, U) \<in> protocol" and
    C: "IntAgrK (S (User m, n, run)) = Some c" and
    D: "ExtAgrK (S (User m, n, run)) = Some f"
  let
    ?B = "H \<union> A \<union> spies evsC5" and
    ?C = "A \<union> spies evsC5"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (sesK (c * f)) (Passwd m)) ?B) =
    H \<union> analz (insert (Crypt (sesK (c * f)) (Passwd m)) ?C)"
    (is "_ \<longrightarrow> ?T")
  proof (rule impI, cases "Key (invK (sesK (c * f))) \<in> analz ?C")
    case True
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have E: "analz ?B = H \<union> analz ?C" ..
    have "Key (invK (sesK (c * f))) \<in> analz ?B"
     by (rule subsetD [OF _ True], rule analz_mono, blast)
    hence "analz (insert (Crypt (sesK (c * f)) (Passwd m)) ?B) =
      insert (Crypt (sesK (c * f)) (Passwd m)) (insert (Passwd m) (analz ?B))"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    moreover have "H \<union> analz (insert (Crypt (sesK (c * f)) (Passwd m)) ?C) =
      insert (Crypt (sesK (c * f)) (Passwd m)) (insert (Passwd m) (H \<union> analz ?C))"
     using True by (simp add: analz_crypt_in analz_simp_insert_2)
    ultimately show ?T
     using E by simp
  next
    case False
    moreover assume E: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have F: "analz ?B = H \<union> analz ?C" ..
    ultimately have "Key (invK (sesK (c * f))) \<notin> analz ?B"
    proof (simp add: invK_sesK, insert pr_sesk_user_1 [OF B C D,
     THEN pr_sesk_user_2 [OF B]])
    qed (rule notI, drule subsetD [OF E], simp)
    hence "analz (insert (Crypt (sesK (c * f)) (Passwd m)) ?B) =
      insert (Crypt (sesK (c * f)) (Passwd m)) (analz ?B)"
     by (simp add: analz_crypt_out)
    moreover have "H \<union> analz (insert (Crypt (sesK (c * f)) (Passwd m)) ?C) =
      insert (Crypt (sesK (c * f)) (Passwd m)) (H \<union> analz ?C)"
     using False by (simp add: analz_crypt_out)
    ultimately show ?T
     using F by simp
  qed
next
  fix evsFC5 S A U n run d e H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsFC5) = H \<union> analz (A \<union> spies evsFC5)" and
    B: "(evsFC5, S, A, U) \<in> protocol" and
    C: "IntAgrK (S (Card n, n, run)) = Some d" and
    D: "ExtAgrK (S (Card n, n, run)) = Some e"
  let
    ?B = "H \<union> A \<union> spies evsFC5" and
    ?C = "A \<union> spies evsFC5"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (sesK (d * e)) (Passwd n)) ?B) =
    H \<union> analz (insert (Crypt (sesK (d * e)) (Passwd n)) ?C)"
    (is "_ \<longrightarrow> ?T")
  proof (rule impI, cases "Key (invK (sesK (d * e))) \<in> analz ?C")
    case True
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have E: "analz ?B = H \<union> analz ?C" ..
    have "Key (invK (sesK (d * e))) \<in> analz ?B"
     by (rule subsetD [OF _ True], rule analz_mono, blast)
    hence "analz (insert (Crypt (sesK (d * e)) (Passwd n)) ?B) =
      insert (Crypt (sesK (d * e)) (Passwd n)) (insert (Passwd n) (analz ?B))"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    moreover have "H \<union> analz (insert (Crypt (sesK (d * e)) (Passwd n)) ?C) =
      insert (Crypt (sesK (d * e)) (Passwd n)) (insert (Passwd n) (H \<union> analz ?C))"
     using True by (simp add: analz_crypt_in analz_simp_insert_2)
    ultimately show ?T
     using E by simp
  next
    case False
    moreover assume E: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have F: "analz ?B = H \<union> analz ?C" ..
    ultimately have "Key (invK (sesK (d * e))) \<notin> analz ?B"
    proof (simp add: invK_sesK, insert pr_sesk_card [OF B C D])
    qed (rule notI, drule subsetD [OF E], simp)
    hence "analz (insert (Crypt (sesK (d * e)) (Passwd n)) ?B) =
      insert (Crypt (sesK (d * e)) (Passwd n)) (analz ?B)"
     by (simp add: analz_crypt_out)
    moreover have "H \<union> analz (insert (Crypt (sesK (d * e)) (Passwd n)) ?C) =
      insert (Crypt (sesK (d * e)) (Passwd n)) (H \<union> analz ?C)"
     using False by (simp add: analz_crypt_out)
    ultimately show ?T
     using F by simp
  qed
next
  fix evsR5 S A U n run d e H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsR5) = H \<union> analz (A \<union> spies evsR5)" and
    B: "(evsR5, S, A, U) \<in> protocol" and
    C: "IntAgrK (S (Card n, n, run)) = Some d" and
    D: "ExtAgrK (S (Card n, n, run)) = Some e"
  let
    ?B = "H \<union> A \<union> spies evsR5" and
    ?C = "A \<union> spies evsR5"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (sesK (d * e)) (Number 0)) (H \<union> A \<union> spies evsR5)) =
    H \<union> analz (insert (Crypt (sesK (d * e)) (Number 0)) (A \<union> spies evsR5))"
    (is "_ \<longrightarrow> ?T")
  proof (rule impI, cases "Key (invK (sesK (d * e))) \<in> analz ?C")
    case True
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have E: "analz ?B = H \<union> analz ?C" ..
    have "Key (invK (sesK (d * e))) \<in> analz ?B"
     by (rule subsetD [OF _ True], rule analz_mono, blast)
    hence "analz (insert (Crypt (sesK (d * e)) (Number 0)) ?B) =
      insert (Crypt (sesK (d * e)) (Number 0)) (insert (Number 0) (analz ?B))"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    moreover have "H \<union> analz (insert (Crypt (sesK (d * e)) (Number 0)) ?C) =
      insert (Crypt (sesK (d * e)) (Number 0)) (insert (Number 0) (H \<union> analz ?C))"
     using True by (simp add: analz_crypt_in analz_simp_insert_2)
    ultimately show ?T
     using E by simp
  next
    case False
    moreover assume E: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have F: "analz ?B = H \<union> analz ?C" ..
    ultimately have "Key (invK (sesK (d * e))) \<notin> analz ?B"
    proof (simp add: invK_sesK, insert pr_sesk_card [OF B C D])
    qed (rule notI, drule subsetD [OF E], simp)
    hence "analz (insert (Crypt (sesK (d * e)) (Number 0)) ?B) =
      insert (Crypt (sesK (d * e)) (Number 0)) (analz ?B)"
     by (simp add: analz_crypt_out)
    moreover have "H \<union> analz (insert (Crypt (sesK (d * e)) (Number 0)) ?C) =
      insert (Crypt (sesK (d * e)) (Number 0)) (H \<union> analz ?C)"
     using False by (simp add: analz_crypt_out)
    ultimately show ?T
     using F by simp
  qed
next
  fix evsFR5 S A U m n run c f H
  assume
    A: "\<And>H. H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
      analz (H \<union> A \<union> spies evsFR5) = H \<union> analz (A \<union> spies evsFR5)" and
    B: "(evsFR5, S, A, U) \<in> protocol" and
    C: "IntAgrK (S (User m, n, run)) = Some c" and
    D: "ExtAgrK (S (User m, n, run)) = Some f"
  let
    ?B = "H \<union> A \<union> spies evsFR5" and
    ?C = "A \<union> spies evsFR5"
  show "H \<subseteq> range Key \<union> range Pri_AgrK - U \<longrightarrow>
    analz (insert (Crypt (sesK (c * f)) (Number 0)) (H \<union> A \<union> spies evsFR5)) =
    H \<union> analz (insert (Crypt (sesK (c * f)) (Number 0)) (A \<union> spies evsFR5))"
    (is "_ \<longrightarrow> ?T")
  proof (rule impI, cases "Key (invK (sesK (c * f))) \<in> analz ?C")
    case True
    assume "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have E: "analz ?B = H \<union> analz ?C" ..
    have "Key (invK (sesK (c * f))) \<in> analz ?B"
     by (rule subsetD [OF _ True], rule analz_mono, blast)
    hence "analz (insert (Crypt (sesK (c * f)) (Number 0)) ?B) =
      insert (Crypt (sesK (c * f)) (Number 0)) (insert (Number 0) (analz ?B))"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    moreover have "H \<union> analz (insert (Crypt (sesK (c * f)) (Number 0)) ?C) =
      insert (Crypt (sesK (c * f)) (Number 0)) (insert (Number 0) (H \<union> analz ?C))"
     using True by (simp add: analz_crypt_in analz_simp_insert_2)
    ultimately show ?T
     using E by simp
  next
    case False
    moreover assume E: "H \<subseteq> range Key \<union> range Pri_AgrK - U"
    with A have F: "analz ?B = H \<union> analz ?C" ..
    ultimately have "Key (invK (sesK (c * f))) \<notin> analz ?B"
    proof (simp add: invK_sesK, insert pr_sesk_user_1 [OF B C D,
     THEN pr_sesk_user_2 [OF B]])
    qed (rule notI, drule subsetD [OF E], simp)
    hence "analz (insert (Crypt (sesK (c * f)) (Number 0)) ?B) =
      insert (Crypt (sesK (c * f)) (Number 0)) (analz ?B)"
     by (simp add: analz_crypt_out)
    moreover have "H \<union> analz (insert (Crypt (sesK (c * f)) (Number 0)) ?C) =
      insert (Crypt (sesK (c * f)) (Number 0)) (H \<union> analz ?C)"
     using False by (simp add: analz_crypt_out)
    ultimately show ?T
     using F by simp
  qed
qed

lemma pr_key_unused:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Key K \<notin> U \<Longrightarrow>
  analz (insert (Key K) (A \<union> spies evs)) =
    insert (Key K) (analz (A \<union> spies evs))"
by (simp only: insert_def Un_assoc [symmetric], rule pr_key_set_unused, simp_all)

lemma pr_pri_agrk_unused:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Pri_AgrK x \<notin> U \<Longrightarrow>
  analz (insert (Pri_AgrK x) (A \<union> spies evs)) =
    insert (Pri_AgrK x) (analz (A \<union> spies evs))"
by (simp only: insert_def Un_assoc [symmetric], rule pr_key_set_unused, simp_all)

lemma pr_pri_agrk_analz_intro [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Pri_AgrK x \<in> analz (A \<union> spies evs) \<longrightarrow>
  Pri_AgrK x \<in> A"
proof (erule protocol.induct, subst analz_simp, simp, blast,
 simp_all add: analz_simp_insert_2 pr_key_unused pr_pri_agrk_unused,
 rule conjI, rule_tac [1-2] impI, rule_tac [!] impI)
  fix evsR1 S A U n s
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsR1) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "(evsR1, S, A, U) \<in> protocol" and
    C: "n \<in> bad" and
    D: "Pri_AgrK x \<in> analz (insert (Crypt (symK n) (Pri_AgrK s))
      (insert (Pri_AgrK s) (A \<union> spies evsR1)))" and
    E: "Pri_AgrK s \<notin> U"
  have "Key (symK n) \<in> analz ?A"
   using B and C by (simp add: pr_symk_analz)
  hence "Key (invK (symK n)) \<in> analz ?A"
   by (simp add: invK_symK)
  hence "Key (invK (symK n)) \<in> analz (insert (Pri_AgrK s) ?A)"
   using B and E by (simp add: pr_pri_agrk_unused)
  hence "Pri_AgrK x \<in> analz (insert (Pri_AgrK s) ?A)"
   using D by (simp add: analz_crypt_in)
  hence "x = s \<or> Pri_AgrK x \<in> analz ?A"
   using B and E by (simp add: pr_pri_agrk_unused)
  thus "x = s \<or> Pri_AgrK x \<in> A"
   using A by blast
next
  fix evsR1 S A U n s
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsR1) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "(evsR1, S, A, U) \<in> protocol" and
    C: "n \<notin> bad" and
    D: "Pri_AgrK x \<in> analz (insert (Crypt (symK n) (Pri_AgrK s))
      (A \<union> spies evsR1))"
  have "Key (symK n) \<notin> analz ?A"
   using B and C by (simp add: pr_symk_analz)
  hence "Key (invK (symK n)) \<notin> analz ?A"
   by (simp add: invK_symK)
  hence "Pri_AgrK x \<in> analz ?A"
   using D by (simp add: analz_crypt_out)
  with A show "Pri_AgrK x \<in> A" ..
next
  fix evsFR1 A m s
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsFR1) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "Crypt (symK m) (Pri_AgrK s) \<in> synth (analz (A \<union> spies evsFR1))" and
    C: "Pri_AgrK x \<in> analz (insert (Crypt (symK m) (Pri_AgrK s))
      (A \<union> spies evsFR1))"
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (symK m)) \<in> analz ?A")
    case True
    have "Crypt (symK m) (Pri_AgrK s) \<in> analz ?A \<or>
      Pri_AgrK s \<in> synth (analz ?A) \<and> Key (symK m) \<in> analz ?A"
     using B by (rule synth_crypt)
    moreover {
      assume "Crypt (symK m) (Pri_AgrK s) \<in> analz ?A"
      hence "Pri_AgrK s \<in> analz ?A"
       using True by (rule analz.Decrypt)
    }
    moreover {
      assume "Pri_AgrK s \<in> synth (analz ?A) \<and> Key (symK m) \<in> analz ?A"
      hence "Pri_AgrK s \<in> synth (analz ?A)" ..
      hence "Pri_AgrK s \<in> analz ?A"
       by (rule synth_simp_intro, simp)
    }
    ultimately have "Pri_AgrK s \<in> analz ?A" ..
    moreover have "Pri_AgrK x \<in> analz (insert (Pri_AgrK s) ?A)"
     using C and True by (simp add: analz_crypt_in)
    ultimately have "Pri_AgrK x \<in> analz ?A"
     by (simp add: analz_simp_insert_1)
    with A show ?thesis ..
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using C by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
next
  fix evsC4 A c f
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsC4) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "Pri_AgrK x \<in> analz (insert (Crypt (sesK (c * f)) (pubAK f))
      (A \<union> spies evsC4))"
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (sesK (c * f))) \<in> analz ?A")
    case True
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_in analz_simp_insert_2)
    with A show ?thesis ..
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
next
  fix evsFC4 A s a b d e
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsFC4) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "Pri_AgrK x \<in> analz (insert (Crypt (sesK (d * e)) (pubAK (d * (s + a * b))))
      (A \<union> spies evsFC4))"
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (sesK (d * e))) \<in> analz ?A")
    case True
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_in analz_simp_insert_2)
    with A show ?thesis ..
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
next
  fix evsR4 S A U n run b d e
  let
    ?H = "Hash (pubAK (priAK n))" and
    ?M = "\<lbrace>pubAK (priAK n), Crypt (priSK CA) (Hash (pubAK (priAK n)))\<rbrace>" and
    ?M' = "\<lbrace>pubAK e, Auth_Data (priAK n) b, pubAK (priAK n),
      Crypt (priSK CA) (Hash (pubAK (priAK n)))\<rbrace>"
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsR4) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "(evsR4, S, A, U) \<in> protocol" and
    C: "IntMapK (S (Card n, n, run)) = Some b" and
    D: "Pri_AgrK x \<in> analz (insert (Crypt (sesK (d * e)) ?M')
      (A \<union> spies evsR4))"
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (sesK (d * e))) \<in> analz ?A")
    case True
    have "Key (pubSK CA) \<in> analz ?A"
     using B by (rule pr_valid_key_analz)
    hence E: "analz (insert (Crypt (priSK CA) ?H) ?A) =
      {Crypt (priSK CA) ?H, ?H} \<union> analz ?A"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    have "Pri_AgrK (priAK n) \<notin> analz ?A"
     using B by (rule pr_auth_key_analz)
    hence F: "Pri_AgrK (priAK n) \<notin> analz (insert (Crypt (priSK CA) ?H) ?A)"
     using E by simp
    have "Pri_AgrK b \<notin> analz ?A"
     using B and C by (rule pr_int_mapk_analz)
    hence G: "Pri_AgrK b \<notin> analz (insert (Crypt (priSK CA) ?H) ?A)"
     using E by simp
    have "Pri_AgrK x \<in> analz (insert ?M' ?A)"
     using D and True by (simp add: analz_crypt_in)
    hence "Pri_AgrK x \<in> analz (insert (Auth_Data (priAK n) b) (insert ?M ?A))"
     by (simp add: analz_mpair analz_simp_insert_2)
    hence "Pri_AgrK x \<in> analz ?A"
    proof (subst (asm) insert_commute, simp add: analz_mpair analz_simp_insert_2
     del: Un_insert_right, subst (asm) insert_commute,
     subst (asm) analz_auth_data_out [OF F G])
    qed (simp add: E)
    with A show ?thesis ..
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using D by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
next
  fix evsFR4 S A U m n run s a b c f g
  let
    ?H = "Hash (pubAK g)" and
    ?M = "\<lbrace>pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>" and
    ?M' = "\<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
      Crypt (priSK CA) (Hash (pubAK g))\<rbrace>"
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsFR4) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "(evsFR4, S, A, U) \<in> protocol" and
    C: "Crypt (sesK (c * f)) ?M' \<in> synth (analz (A \<union> spies evsFR4))" and
    D: "Pri_AgrK x \<in> analz (insert (Crypt (sesK (c * f)) ?M')
      (A \<union> spies evsFR4))"
  have E:
   "Key (invK (sesK (c * f))) \<in> analz ?A \<longrightarrow>
      Pri_AgrK b \<in> analz ?A \<or> Pri_AgrK g \<in> analz ?A \<longrightarrow>
    Pri_AgrK b \<in> analz ?A \<and> Pri_AgrK g \<in> analz ?A"
    (is "?P \<longrightarrow> ?Q \<longrightarrow> ?R")
  proof (rule impI)+
    assume ?P and ?Q
    have "Crypt (sesK (c * f)) ?M' \<in> analz ?A \<or>
      ?M' \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
     using C by (rule synth_crypt)
    moreover {
      assume "Crypt (sesK (c * f)) ?M' \<in> analz ?A"
      hence "?M' \<in> analz ?A"
       using \<open>?P\<close> by (rule analz.Decrypt)
      hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> analz ?A"
       by (rule analz.Snd)
      hence F: "Auth_Data g b \<in> analz ?A"
       by (rule analz.Fst)
      have ?R
      proof (rule disjE [OF \<open>?Q\<close>])
        assume "Pri_AgrK b \<in> analz ?A"
        moreover from this have "Pri_AgrK g \<in> analz ?A"
         by (rule analz.Auth_Fst [OF F])
        ultimately show ?R ..
      next
        assume "Pri_AgrK g \<in> analz ?A"
        moreover from this have "Pri_AgrK b \<in> analz ?A"
         by (rule analz.Auth_Snd [OF F])
        ultimately show ?R
         by simp
      qed
    }
    moreover {
      assume "?M' \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
      hence "?M' \<in> synth (analz ?A)" ..
      hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> synth (analz ?A)"
       by (rule synth_analz_snd)
      hence "Auth_Data g b \<in> synth (analz ?A)"
       by (rule synth_analz_fst)
      hence "Auth_Data g b \<in> analz ?A \<or>
        Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b \<in> analz ?A"
       by (rule synth_auth_data)
      moreover {
        assume F: "Auth_Data g b \<in> analz ?A"
        have ?R
        proof (rule disjE [OF \<open>?Q\<close>])
          assume "Pri_AgrK b \<in> analz ?A"
          moreover from this have "Pri_AgrK g \<in> analz ?A"
           by (rule analz.Auth_Fst [OF F])
          ultimately show ?R ..
        next
          assume "Pri_AgrK g \<in> analz ?A"
          moreover from this have "Pri_AgrK b \<in> analz ?A"
           by (rule analz.Auth_Snd [OF F])
          ultimately show ?R
           by simp
        qed
      }
      moreover {
        assume "Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b \<in> analz ?A"
        hence ?R
         by simp
      }
      ultimately have ?R ..
    }
    ultimately show ?R ..
  qed
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (sesK (c * f))) \<in> analz ?A")
    case True
    have "Key (pubSK CA) \<in> analz ?A"
     using B by (rule pr_valid_key_analz)
    hence F: "analz (insert (Crypt (priSK CA) ?H) ?A) =
      {Crypt (priSK CA) ?H, ?H} \<union> analz ?A"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    show ?thesis
    proof (cases "Pri_AgrK g \<in> analz ?A \<or> Pri_AgrK b \<in> analz ?A", simp_all)
      assume G: "Pri_AgrK g \<in> analz ?A \<or> Pri_AgrK b \<in> analz ?A"
      hence H: "Pri_AgrK g \<in> analz (insert (Crypt (priSK CA) ?H) ?A) \<or>
        Pri_AgrK b \<in> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F by simp
      have I: "Pri_AgrK b \<in> analz ?A \<and> Pri_AgrK g \<in> analz ?A"
       using E and G and True by blast
      hence "Pri_AgrK g \<in> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F by simp
      hence J: "Pri_AgrK g \<in> analz (insert (Pri_AgrK b)
        (insert (Crypt (priSK CA) ?H) ?A))"
       by (rule rev_subsetD, rule_tac analz_mono, blast)
      have K: "Pri_AgrK b \<in> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F and I by simp
      have "Pri_AgrK x \<in> analz (insert ?M' ?A)"
       using D and True by (simp add: analz_crypt_in)
      hence "Pri_AgrK x \<in> analz (insert (Auth_Data g b) (insert ?M ?A))"
       by (simp add: analz_mpair analz_simp_insert_2)
      hence "Pri_AgrK x \<in> analz ?A"
      proof (subst (asm) insert_commute, simp add: analz_mpair analz_simp_insert_2
       del: Un_insert_right, subst (asm) insert_commute,
       subst (asm) analz_auth_data_in [OF H], simp del: Un_insert_right)
        assume "Pri_AgrK x \<in> analz (insert (Pri_AgrK g) (insert (Pri_AgrK b)
          (insert (Crypt (priSK CA) ?H) ?A)))"
        thus ?thesis
        proof (subst (asm) analz_simp_insert_1 [OF J],
         subst (asm) analz_simp_insert_1 [OF K])
        qed (simp add: F)
      qed
      with A show ?thesis ..
    next
      assume G: "Pri_AgrK g \<notin> analz ?A \<and> Pri_AgrK b \<notin> analz ?A"
      hence H: "Pri_AgrK g \<notin> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F by simp
      have I: "Pri_AgrK b \<notin> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F and G by simp
      have "Pri_AgrK x \<in> analz (insert ?M' ?A)"
       using D and True by (simp add: analz_crypt_in)
      hence "Pri_AgrK x \<in> analz (insert (Auth_Data g b) (insert ?M ?A))"
       by (simp add: analz_mpair analz_simp_insert_2)
      hence "Pri_AgrK x \<in> analz ?A"
      proof (subst (asm) insert_commute, simp add: analz_mpair analz_simp_insert_2
       del: Un_insert_right, subst (asm) insert_commute,
       subst (asm) analz_auth_data_out [OF H I])
      qed (simp add: F)
      with A show ?thesis ..
    qed
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using D by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
next
  fix evsC5 A m c f
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsC5) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "Pri_AgrK x \<in> analz (insert (Crypt (sesK (c * f)) (Passwd m))
      (A \<union> spies evsC5))"
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (sesK (c * f))) \<in> analz ?A")
    case True
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_in analz_simp_insert_2)
    with A show ?thesis ..
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
next
  fix evsFC5 A n d e
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsFC5) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "Pri_AgrK x \<in> analz (insert (Crypt (sesK (d * e)) (Passwd n))
      (A \<union> spies evsFC5))"
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (sesK (d * e))) \<in> analz ?A")
    case True
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_in analz_simp_insert_2)
    with A show ?thesis ..
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
next
  fix evsR5 A d e
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsR5) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "Pri_AgrK x \<in> analz (insert (Crypt (sesK (d * e)) (Number 0))
      (A \<union> spies evsR5))"
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (sesK (d * e))) \<in> analz ?A")
    case True
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_in analz_simp_insert_2)
    with A show ?thesis ..
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
next
  fix evsFR5 A c f
  assume
    A: "Pri_AgrK x \<in> analz (A \<union> spies evsFR5) \<longrightarrow> Pri_AgrK x \<in> A"
      (is "_ \<in> analz ?A \<longrightarrow> _") and
    B: "Pri_AgrK x \<in> analz (insert (Crypt (sesK (c * f)) (Number 0))
      (A \<union> spies evsFR5))"
  show "Pri_AgrK x \<in> A"
  proof (cases "Key (invK (sesK (c * f))) \<in> analz ?A")
    case True
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_in analz_simp_insert_2)
    with A show ?thesis ..
  next
    case False
    hence "Pri_AgrK x \<in> analz ?A"
     using B by (simp add: analz_crypt_out)
    with A show ?thesis ..
  qed
qed

lemma pr_pri_agrk_analz:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    (Pri_AgrK x \<in> analz (A \<union> spies evs)) = (Pri_AgrK x \<in> A)"
proof (rule iffI, erule pr_pri_agrk_analz_intro, assumption)
qed (rule subsetD [OF analz_subset], simp)

lemma pr_ext_agrk_user_1 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    User m \<noteq> Spy \<longrightarrow>
    Says n run 4 (User m) (Card n) (Crypt (sesK K) (pubAK e)) \<in> set evs \<longrightarrow>
  ExtAgrK (S (User m, n, run)) \<noteq> None"
by (erule protocol.induct, simp_all, (rule_tac [!] impI)+, simp_all)

lemma pr_ext_agrk_user_2 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    User m \<noteq> Spy \<longrightarrow>
    Says n run 4 X (User m) (Crypt (sesK K)
      \<lbrace>pubAK e, Auth_Data x y, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>)
      \<in> set evs \<longrightarrow>
  ExtAgrK (S (User m, n, run)) \<noteq> None"
proof (erule protocol.induct, simp_all, (rule_tac [!] impI)+, simp_all,
 (erule conjE)+)
  fix evs S A U n run s a b d e X
  assume "(evs, S, A, U) \<in> protocol"
  moreover assume "0 < m"
  hence "User m \<noteq> Spy"
   by simp
  moreover assume A: "User m = X" and
   "Says n run 4 X (Card n) (Crypt (sesK (d * e))
      (pubAK (d * (s + a * b)))) \<in> set evs"
  hence "Says n run 4 (User m) (Card n) (Crypt (sesK (d * e))
    (pubAK (d * (s + a * b)))) \<in> set evs"
   by simp
  ultimately have "ExtAgrK (S (User m, n, run)) \<noteq> None"
   by (rule pr_ext_agrk_user_1)
  thus "\<exists>e. ExtAgrK (S (X, n, run)) = Some e"
   using A by simp
qed

lemma pr_ext_agrk_user_3 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    User m \<noteq> Spy \<longrightarrow>
    ExtAgrK (S (User m, n, run)) = Some e \<longrightarrow>
    Says n run 4 (User m) (Card n) (Crypt (sesK K) (pubAK e')) \<in> set evs \<longrightarrow>
  e' = e"
proof (erule protocol.induct, simp_all, (rule conjI, (rule_tac [!] impI)+)+,
 (erule conjE)+, simp_all)
  assume "agrK e' = agrK e"
  with agrK_inj show "e' = e"
   by (rule injD)
next
  fix evsC4 S A U n run and m :: nat
  assume "(evsC4, S, A, U) \<in> protocol"
  moreover assume "0 < m"
  hence "User m \<noteq> Spy"
   by simp
  moreover assume
   "Says n run 4 (User m) (Card n) (Crypt (sesK K) (pubAK e')) \<in> set evsC4"
  ultimately have "ExtAgrK (S (User m, n, run)) \<noteq> None"
   by (rule pr_ext_agrk_user_1)
  moreover assume "ExtAgrK (S (User m, n, run)) = None"
  ultimately show "e' = e"
   by contradiction
qed

lemma pr_ext_agrk_user_4 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    ExtAgrK (S (User m, n, run)) = Some f \<longrightarrow>
  (\<exists>X. Says n run 3 X (User m) (pubAK f) \<in> set evs)"
proof (erule protocol.induct, simp_all, rule_tac [!] impI, rule_tac [1-2] impI,
 rule_tac [5] impI, simp_all)
qed blast+

declare fun_upd_apply [simp del]

lemma pr_ext_agrk_user_5 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n run 3 X (User m) (pubAK f) \<in> set evs \<longrightarrow>
  (\<exists>s a b d. f = d * (s + a * b) \<and>
    NonceS (S (Card n, n, run)) = Some s \<and>
    IntMapK (S (Card n, n, run)) = Some b \<and>
    ExtMapK (S (Card n, n, run)) = Some a \<and>
    IntAgrK (S (Card n, n, run)) = Some d \<and>
    d \<noteq> 0 \<and> s + a * b \<noteq> 0) \<or>
  (\<exists>b. Pri_AgrK b \<in> A \<and>
    ExtMapK (S (User m, n, run)) = Some b)"
  (is "_ \<Longrightarrow> ?H evs \<longrightarrow> ?P S n run \<or> ?Q S A n run")
apply (erule protocol.induct, simp_all add: pr_pri_agrk_analz)
     apply (rule conjI)
      apply (rule_tac [1-2] impI)+
      apply (rule_tac [3] conjI, (rule_tac [3] impI)+)+
         apply (rule_tac [4] impI)+
         apply ((rule_tac [5] impI)+, (rule_tac [5] conjI)?)+
          apply (rule_tac [6] impI)+
          apply ((rule_tac [7] impI)+, (rule_tac [7] conjI)?)+
            apply (rule_tac [8] impI)+
            apply ((rule_tac [9] impI)+, (rule_tac [9] conjI)?)+
             apply (rule_tac [10] impI)+
             apply (rule_tac [11] impI)+
             apply (rule_tac [12] conjI, (rule_tac [12] impI)+)+
              apply (rule_tac [13] impI)+
              apply (rule_tac [14] conjI, (rule_tac [14] impI)+)+
                apply (erule_tac [14] conjE)+
                apply (rule_tac [15] impI)+
                apply ((rule_tac [16] impI)+, (rule_tac [16] conjI)?)+
                 apply (erule_tac [16] conjE)+
                 apply (rule_tac [17-18] impI)
proof -
  fix evsR1 S A U s n' run'
  assume
   "?H evsR1 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsR1"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  assume B: "NonceS (S (Card n', n', run')) = None"
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>NonceS := Some s\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = s \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp add: B)
  qed (rule disjI2, simp add: fun_upd_apply, blast)
next
  fix evsR1 S A U s n' run'
  assume
   "?H evsR1 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsR1"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  assume B: "NonceS (S (Card n', n', run')) = None"
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>NonceS := Some s\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp add: B)
  qed (rule disjI2, simp add: fun_upd_apply)
next
  fix evsC2 S A U s a n' run'
  assume
   "?H evsC2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = a \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a m' n' run'
  assume
   "?H evsC2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a n' run'
  assume
   "?H evsC2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = a \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a m' n' run'
  assume
   "?H evsC2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a n' run'
  assume
   "?H evsC2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = a \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a m' n' run'
  assume
   "?H evsC2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a n' run'
  assume
   "?H evsC2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = a \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a m' n' run'
  assume
   "?H evsC2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsR2 S A U a b n' run'
  assume
   "?H evsR2 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsR2"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  assume B: "IntMapK (S (Card n', n', run')) = None"
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntMapK := Some b, ExtMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp add: B)
  qed (rule disjI2, simp add: fun_upd_apply)
next
  fix evsC3 S A U b c m' n' run'
  assume
   "?H evsC3 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC3"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  assume
   "ExtMapK (S (User m', n', run')) = None" and
   "m' = 0"
  hence B: "ExtMapK (S (Spy, n', run')) = None"
   by simp
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>ExtMapK := Some b, IntAgrK := Some c\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = c \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
  proof (rule disjE [OF A], simp add: fun_upd_apply)
  qed (rule disjI2, simp add: fun_upd_apply, rule conjI, rule impI, simp add: B, blast)
next
  fix evsC3 S A U b c m' n' run'
  assume
   "?H evsC3 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC3"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  assume B: "ExtMapK (S (User m', n', run')) = None"
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>ExtMapK := Some b, IntAgrK := Some c\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], simp add: fun_upd_apply)
  qed (rule disjI2, simp add: fun_upd_apply, rule impI, simp add: B)
next
  fix evsR3 A U s a b c d n' run' X and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b))\<rparr>)"
  assume "agrK f = agrK (d * (s + a * b))"
  with agrK_inj have "f = d * (s + a * b)"
   by (rule injD)
  moreover assume
   "NonceS (S (Card n', n', run')) = Some s" and
   "IntMapK (S (Card n', n', run')) = Some b" and
   "ExtMapK (S (Card n', n', run')) = Some a" and
   "d \<noteq> 0" and
   "s + a * b \<noteq> 0"
  ultimately show "?P ?S n' run' \<or>
    (\<exists>b. Pri_AgrK b \<in> A \<and> ExtMapK (?S (X, n', run')) = Some b)"
   by (simp add: fun_upd_apply)
next
  fix evsR3 S A U s a b c d n' run'
  assume
   "?H evsR3 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsR3"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  assume B: "IntAgrK (S (Card n', n', run')) = None"
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b))\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp add: B)
  qed (rule disjI2, simp add: fun_upd_apply)
next
  fix evsR3 A U s s' a b c d n' run' X and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s' + a * b))\<rparr>)"
  assume "agrK f = agrK (d * (s + a * b))"
  with agrK_inj have "f = d * (s + a * b)"
   by (rule injD)
  moreover assume
   "NonceS (S (Card n', n', run')) = Some s" and
   "IntMapK (S (Card n', n', run')) = Some b" and
   "ExtMapK (S (Card n', n', run')) = Some a" and
   "d \<noteq> 0" and
   "s + a * b \<noteq> 0"
  ultimately show "?P ?S n' run' \<or>
    (\<exists>b. Pri_AgrK b \<in> A \<and> ExtMapK (?S (X, n', run')) = Some b)"
   by (simp add: fun_upd_apply)
next
  fix evsR3 S A U s a b c d n' run'
  assume
   "?H evsR3 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsR3"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  assume B: "IntAgrK (S (Card n', n', run')) = None"
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b))\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp add: B)
  qed (rule disjI2, simp add: fun_upd_apply)
next
  fix evsC4 S A U f m' n' run'
  assume
   "?H evsC4 \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H evsC4"
  hence A: "?P S n run \<or> ?Q S A n run" ..
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>ExtAgrK := Some f\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
qed

declare fun_upd_apply [simp]

lemma pr_int_agrk_user_1 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    IntAgrK (S (User m, n, run)) = Some c \<longrightarrow>
  Pri_AgrK c \<in> U"
by (erule protocol.induct, simp_all)

lemma pr_int_agrk_user_2 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    User m \<noteq> Spy \<longrightarrow>
    IntAgrK (S (User m, n, run)) = Some c \<longrightarrow>
  Pri_AgrK c \<notin> A"
proof (erule protocol.induct, simp_all, rule_tac [3] conjI, (rule_tac [!] impI)+,
 rule_tac [2] impI, rule_tac [4] impI, rule_tac [!] notI, simp_all)
  fix evsR1 S A U s
  assume
   "(evsR1, S, A, U) \<in> protocol" and
   "IntAgrK (S (User m, n, run)) = Some s"
  hence "Pri_AgrK s \<in> U"
   by (rule pr_int_agrk_user_1)
  moreover assume "Pri_AgrK s \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsC2 S A U a
  assume
   "(evsC2, S, A, U) \<in> protocol" and
   "IntAgrK (S (User m, n, run)) = Some a"
  hence "Pri_AgrK a \<in> U"
   by (rule pr_int_agrk_user_1)
  moreover assume "Pri_AgrK a \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsC3 S A U
  assume "(evsC3, S, A, U) \<in> protocol"
  hence "A \<subseteq> U"
   by (rule pr_analz_used)
  moreover assume "Pri_AgrK c \<in> A"
  ultimately have "Pri_AgrK c \<in> U" ..
  moreover assume "Pri_AgrK c \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsC3 S A U c'
  assume
   "(evsC3, S, A, U) \<in> protocol" and
   "IntAgrK (S (User m, n, run)) = Some c'"
  hence "Pri_AgrK c' \<in> U"
   by (rule pr_int_agrk_user_1)
  moreover assume "Pri_AgrK c' \<notin> U"
  ultimately show False
   by contradiction
qed

lemma pr_int_agrk_user_3 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    NonceS (S (User m, n, run)) = Some s \<longrightarrow>
    IntMapK (S (User m, n, run)) = Some a \<longrightarrow>
    ExtMapK (S (User m, n, run)) = Some b \<longrightarrow>
    IntAgrK (S (User m, n, run)) = Some c \<longrightarrow>
  c * (s + a * b) \<noteq> 0"
proof (erule protocol.induct, simp_all, rule conjI, (rule_tac [1-2] impI)+,
 (rule_tac [3] impI)+, simp_all)
  fix evsC2 S A U n run m
  assume A: "(evsC2, S, A, U) \<in> protocol"
  moreover assume "NonceS (S (User m, n, run)) = None"
  ultimately have "IntMapK (S (User m, n, run)) = None"
   by (rule pr_state_1)
  with A have "ExtMapK (S (User m, n, run)) = None"
   by (rule pr_state_2)
  moreover assume "ExtMapK (S (User m, n, run)) = Some b"
  ultimately show "c \<noteq> 0 \<and> s + a * b \<noteq> 0"
   by simp
next
  fix evsC2 S A U n run m
  assume A: "(evsC2, S, A, U) \<in> protocol"
  moreover assume "NonceS (S (User m, n, run)) = None"
  ultimately have "IntMapK (S (User m, n, run)) = None"
   by (rule pr_state_1)
  with A have "ExtMapK (S (User m, n, run)) = None"
   by (rule pr_state_2)
  moreover assume "ExtMapK (S (User m, n, run)) = Some b"
  ultimately show "c \<noteq> 0 \<and> a \<noteq> 0 \<and> b \<noteq> 0"
   by simp
qed

lemma pr_int_agrk_card [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    NonceS (S (Card n, n, run)) = Some s \<longrightarrow>
    IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
    ExtMapK (S (Card n, n, run)) = Some a \<longrightarrow>
    IntAgrK (S (Card n, n, run)) = Some d \<longrightarrow>
  d * (s + a * b) \<noteq> 0"
proof (erule protocol.induct, simp_all, (rule_tac [!] impI)+, simp_all)
  fix evsR1 S A U n run
  assume
   "(evsR1, S, A, U) \<in> protocol" and
   "NonceS (S (Card n, n, run)) = None"
  hence "IntMapK (S (Card n, n, run)) = None"
   by (rule pr_state_1)
  moreover assume "IntMapK (S (Card n, n, run)) = Some b"
  ultimately show "d \<noteq> 0 \<and> s + a * b \<noteq> 0"
   by simp
next
  fix evsR2 S A U n run
  assume A: "(evsR2, S, A, U) \<in> protocol" and
   "IntMapK (S (Card n, n, run)) = None"
  hence "ExtMapK (S (Card n, n, run)) = None"
   by (rule pr_state_2)
  with A have "IntAgrK (S (Card n, n, run)) = None"
   by (rule pr_state_3)
  moreover assume "IntAgrK (S (Card n, n, run)) = Some d"
  ultimately show "d \<noteq> 0 \<and> s + a * b \<noteq> 0"
   by simp
qed

lemma pr_ext_agrk_card [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    NonceS (S (Card n, n, run)) = Some s \<longrightarrow>
    IntMapK (S (Card n, n, run)) = Some b \<longrightarrow>
    ExtMapK (S (Card n, n, run)) = Some a \<longrightarrow>
    IntAgrK (S (Card n, n, run)) = Some d \<longrightarrow>
    ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b)) \<longrightarrow>
    Pri_AgrK c \<notin> A \<longrightarrow>
  Key (sesK (c * d * (s + a * b))) \<notin> A"
apply (erule protocol.induct, simp_all add: pr_pri_agrk_analz)
   apply (rule conjI)
    apply (rule_tac [1-2] impI)+
    apply (rule_tac [3] impI)+
    apply (rule_tac [4] conjI, (rule_tac [4] impI)+)+
       apply (erule_tac [4] conjE)+
       apply (rule_tac [5] impI)
       apply (erule_tac [5] conjE)+
       apply (rule_tac [6] impI)+
       apply (erule_tac [6] conjE)+
       apply (rule_tac [6] notI)
       apply ((rule_tac [7] impI)+, (rule_tac [7] conjI)?)+
          apply (erule_tac [7] conjE)+
          apply (rule_tac [8] impI)
          apply (erule_tac [8] conjE)+
          apply (rule_tac [9] impI)+
          apply (rule_tac [9] notI)
          apply (rule_tac [10] impI)+
          apply (rule_tac [11] impI)+
          apply (rule_tac [11] notI)
proof simp_all
  fix evsR1 S A U n run
  assume
   "(evsR1, S, A, U) \<in> protocol" and
   "NonceS (S (Card n, n, run)) = None"
  hence "IntMapK (S (Card n, n, run)) = None"
   by (rule pr_state_1)
  moreover assume "IntMapK (S (Card n, n, run)) = Some b"
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by simp
next
  fix evsR1 S A U n run
  assume
   "(evsR1, S, A, U) \<in> protocol" and
   "NonceS (S (Card n, n, run)) = None"
  hence "IntMapK (S (Card n, n, run)) = None"
   by (rule pr_state_1)
  moreover assume "IntMapK (S (Card n, n, run)) = Some b"
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by simp
next
  fix evsR2 S A U n run
  assume A: "(evsR2, S, A, U) \<in> protocol" and
   "IntMapK (S (Card n, n, run)) = None"
  hence "ExtMapK (S (Card n, n, run)) = None"
   by (rule pr_state_2)
  with A have "IntAgrK (S (Card n, n, run)) = None"
   by (rule pr_state_3)
  moreover assume "IntAgrK (S (Card n, n, run)) = Some d"
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by simp
next
  fix evsR3 S A U s a' b' c' d'
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b))"
  hence "Key (sesK (d * (c * (s + a * b)))) \<in> U"
   by (rule pr_sesk_card)
  moreover have "d * (c * (s + a * b)) = c * d * (s + a * b)"
   by simp
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "sesK (c * d * (s + a * b)) = sesK (c' * d' * (s + a' * b'))"
  ultimately have "Key (sesK (c' * d' * (s + a' * b'))) \<in> U"
   by simp
  moreover assume "Key (sesK (c' * d' * (s + a' * b'))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsR3 S A U s' a' b' c' d'
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b))"
  hence "Key (sesK (d * (c * (s + a * b)))) \<in> U"
   by (rule pr_sesk_card)
  moreover have "d * (c * (s + a * b)) = c * d * (s + a * b)"
   by simp
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "sesK (c * d * (s + a * b)) = sesK (c' * d' * (s' + a' * b'))"
  ultimately have "Key (sesK (c' * d' * (s' + a' * b'))) \<in> U"
   by simp
  moreover assume "Key (sesK (c' * d' * (s' + a' * b'))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsR3 S A U s' c'
  assume "(evsR3, S, A, U) \<in> protocol"
  hence "A \<subseteq> U"
   by (rule pr_analz_used)
  moreover assume "Key (sesK (c' * d * (s' + a * b))) \<notin> U"
  ultimately have "Key (sesK (c' * d * (s' + a * b))) \<notin> A"
   by (rule contra_subsetD)
  moreover assume "c' * (s' + a * b) = c * (s + a * b)"
  hence "c' * d * (s' + a * b) = c * d * (s + a * b)"
   by simp
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by simp
next
  fix evsFR3 S A U s' a' b' c' d'
  assume
   "(evsFR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b))"
  hence "Key (sesK (d * (c * (s + a * b)))) \<in> U"
   by (rule pr_sesk_card)
  moreover have "d * (c * (s + a * b)) = c * d * (s + a * b)"
   by simp
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "sesK (c * d * (s + a * b)) = sesK (c' * d' * (s' + a' * b'))"
  ultimately have "Key (sesK (c' * d' * (s' + a' * b'))) \<in> U"
   by simp
  moreover assume "Key (sesK (c' * d' * (s' + a' * b'))) \<notin> U"
  ultimately show False
   by contradiction
qed

declare fun_upd_apply [simp del]

lemma pr_sesk_user_3 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    \<lbrace>Key (sesK K), Agent (User m), Number n, Number run\<rbrace> \<in> U \<longrightarrow>
    Key (sesK K) \<in> A \<longrightarrow>
  (\<exists>d e. K = d * e \<and>
    IntAgrK (S (Card n, n, run)) = Some d \<and>
    ExtAgrK (S (Card n, n, run)) = Some e) \<or>
  (\<exists>b. Pri_AgrK b \<in> A \<and>
    ExtMapK (S (User m, n, run)) = Some b)"
  (is "_ \<Longrightarrow> ?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run")
apply (erule protocol.induct, simp_all add: pr_pri_agrk_analz, blast)
     apply (rule conjI)
      apply (rule_tac [1-2] impI)+
      apply (rule_tac [3] conjI, (rule_tac [3] impI)+)+
         apply (rule_tac [4] impI)+
         apply ((rule_tac [5] impI)+, (rule_tac [5] conjI)?)+
          apply (rule_tac [6] impI)+
          apply ((rule_tac [7] impI)+, (rule_tac [7] conjI)?)+
            apply (rule_tac [8] impI)+
            apply ((rule_tac [9] impI)+, (rule_tac [9] conjI)?)+
             apply (rule_tac [10] impI)+
             apply (rule_tac [11] impI)+
             apply (rule_tac [12] conjI, (rule_tac [12] impI)+)+
              apply (rule_tac [13] impI)+
              apply (rule_tac [14] conjI, (rule_tac [14] impI)+)+
                apply (erule_tac [14] conjE)+
                apply ((rule_tac [15] impI)+, (rule_tac [15] conjI)?)+
                 apply (rule_tac [16] impI)+
                 apply ((rule_tac [17] impI)+, (rule_tac [17] conjI)?)+
                  apply (rule_tac [18-20] impI)+
proof -
  fix evsR1 S A U s n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>NonceS := Some s\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = s \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp)
  qed (rule disjI2, simp add: fun_upd_apply, blast)
next
  fix evsR1 S A U s n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>NonceS := Some s\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp)
  qed (rule disjI2, simp add: fun_upd_apply)
next
  fix evsC2 S A U s a n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = a \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a m n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((User m, n', run') := S (User m, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = a \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a m n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((User m, n', run') := S (User m, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = a \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a m n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((User m, n', run') := S (User m, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = a \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsC2 S A U s a m n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((User m, n', run') := S (User m, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
next
  fix evsR2 S A U a b n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntMapK := Some b, ExtMapK := Some a\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp)
  qed (rule disjI2, simp add: fun_upd_apply)
next
  fix evsC3 S A U b c m' n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  assume
   "ExtMapK (S (User m', n', run')) = None" and
   "m' = 0"
  hence B: "ExtMapK (S (Spy, n', run')) = None"
   by simp
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>ExtMapK := Some b, IntAgrK := Some c\<rparr>)"
  show "?P ?S n run \<or>
    (\<exists>b. (b = c \<or> Pri_AgrK b \<in> A) \<and> ExtMapK (?S (User m, n, run)) = Some b)"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply)
  qed (rule disjI2, simp add: fun_upd_apply, rule conjI, rule impI, simp add: B, blast)
next
  fix evsC3 S A U b c m' n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  assume B: "ExtMapK (S (User m', n', run')) = None"
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>ExtMapK := Some b, IntAgrK := Some c\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply)
  qed (rule disjI2, simp add: fun_upd_apply, rule impI, simp add: B)
next
  fix evsR3 A s a b c d n' run' X and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b))\<rparr>)"
  assume "sesK K = sesK (c * d * (s + a * b))"
  with sesK_inj have "K = c * d * (s + a * b)"
   by (rule injD)
  thus "?P ?S n' run' \<or>
    (\<exists>b. Pri_AgrK b \<in> A \<and> ExtMapK (?S (X, n', run')) = Some b)"
   by (simp add: fun_upd_apply)
next
  fix evsR3 A U s a b c d n' run' and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b))\<rparr>)"
  assume "sesK K = sesK (c * d * (s + a * b))"
  with sesK_inj have "K = c * d * (s + a * b)"
   by (rule injD)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately have "Key (sesK K) \<notin> U"
   by simp
  moreover assume
   "(evsR3, S, A, U) \<in> protocol" and
   "\<lbrace>Key (sesK K), Agent (User m), Number n, Number run\<rbrace> \<in> U"
  hence "Key (sesK K) \<in> U"
   by (rule pr_sesk_user_2)
  ultimately show "?P ?S n run \<or> ?Q ?S A n run"
   by contradiction
next
  fix evsR3 S A U s a b c d n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  assume B: "IntAgrK (S (Card n', n', run')) = None"
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b))\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp add: B)
  qed (rule disjI2, simp add: fun_upd_apply)
next
  fix evsR3 A U s s' a b c d n' run' X and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s' + a * b))\<rparr>)"
  assume "(evsR3, S, A, U) \<in> protocol"
  hence "A \<subseteq> U"
   by (rule pr_analz_used)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<in> A"
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U" ..
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show "?P ?S n' run' \<or>
    (\<exists>b. Pri_AgrK b \<in> A \<and> ExtMapK (?S (X, n', run')) = Some b)"
   by contradiction
next
  fix evsR3 S A U s a b c d n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  assume B: "IntAgrK (S (Card n', n', run')) = None"
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b))\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
  proof (rule disjE [OF A], rule disjI1, simp add: fun_upd_apply, rule impI, simp add: B)
  qed (rule disjI2, simp add: fun_upd_apply)
next
  fix evsFR3 A U s a b c d n' run' and S :: state
  assume "sesK K = sesK (c * d * (s + a * b))"
  with sesK_inj have "K = c * d * (s + a * b)"
   by (rule injD)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately have "Key (sesK K) \<notin> U"
   by simp
  moreover assume
   "(evsFR3, S, A, U) \<in> protocol" and
   "\<lbrace>Key (sesK K), Agent (User m), Number n, Number run\<rbrace> \<in> U"
  hence "Key (sesK K) \<in> U"
   by (rule pr_sesk_user_2)
  ultimately show "?P S n run \<or> ?Q S A n run"
   by contradiction
next
  fix evsC4 S A U f m' n' run'
  assume
   "?H1 U \<longrightarrow> ?H2 A \<longrightarrow> ?P S n run \<or> ?Q S A n run" and
   "?H1 U" and
   "?H2 A"
  hence A: "?P S n run \<or> ?Q S A n run"
   by simp
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>ExtAgrK := Some f\<rparr>)"
  show "?P ?S n run \<or> ?Q ?S A n run"
   by (rule disjE [OF A], simp_all add: fun_upd_apply, blast)
qed

declare fun_upd_apply [simp]

lemma pr_sesk_auth [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Crypt (sesK K) \<lbrace>pubAK e, Auth_Data x y, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
      \<in> parts (A \<union> spies evs) \<longrightarrow>
  Key (sesK K) \<in> U"
proof (erule protocol.induct, subst parts_simp, (simp, blast)+,
 simp_all add: parts_simp_insert parts_auth_data parts_crypt parts_mpair,
 rule_tac [!] impI)
  fix evsR4 S A U n run d e
  assume
   "(evsR4, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some e"
  thus "Key (sesK (d * e)) \<in> U"
   by (rule pr_sesk_card)
next
  fix evsFR4 S A U m n run c f
  assume A: "(evsFR4, S, A, U) \<in> protocol" and
   "IntAgrK (S (User m, n, run)) = Some c" and
   "ExtAgrK (S (User m, n, run)) = Some f"
  hence "\<lbrace>Key (sesK (c * f)), Agent (User m), Number n, Number run\<rbrace> \<in> U"
   by (rule pr_sesk_user_1)
  with A show "Key (sesK (c * f)) \<in> U"
   by (rule pr_sesk_user_2)
qed

lemma pr_sesk_passwd [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n run 5 X (Card n) (Crypt (sesK K) (Passwd m)) \<in> set evs \<longrightarrow>
  Key (sesK K) \<in> U"
proof (erule protocol.induct, simp_all, rule_tac [!] impI)
  fix evsC5 S A U m n run s a b c f g X
  assume "(evsC5, S, A, U) \<in> protocol"
  moreover assume "Says n run 4 X (User m) (Crypt (sesK (c * f))
    \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
     Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evsC5"
    (is "Says _ _ _ _ _ ?M \<in> _")
  hence "?M \<in> spies evsC5"
   by (rule set_spies)
  hence "?M \<in> A \<union> spies evsC5" ..
  hence "?M \<in> parts (A \<union> spies evsC5)"
   by (rule parts.Inj)
  ultimately show "Key (sesK (c * f)) \<in> U"
   by (rule pr_sesk_auth)
next
  fix evsFC5 S A U n run d e
  assume
   "(evsFC5, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some e"
  thus "Key (sesK (d * e)) \<in> U"
   by (rule pr_sesk_card)
qed

lemma pr_sesk_card_user [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    User m \<noteq> Spy \<longrightarrow>
    NonceS (S (User m, n, run)) = Some s \<longrightarrow>
    IntMapK (S (User m, n, run)) = Some a \<longrightarrow>
    ExtMapK (S (User m, n, run)) = Some b \<longrightarrow>
    IntAgrK (S (User m, n, run)) = Some c \<longrightarrow>
    NonceS (S (Card n, n, run)) = Some s' \<longrightarrow>
    IntMapK (S (Card n, n, run)) = Some b' \<longrightarrow>
    ExtMapK (S (Card n, n, run)) = Some a' \<longrightarrow>
    IntAgrK (S (Card n, n, run)) = Some d \<longrightarrow>
    ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b)) \<longrightarrow>
    s' + a' * b' = s + a * b \<longrightarrow>
  Key (sesK (c * d * (s + a * b))) \<notin> A"
apply (erule protocol.induct, rule_tac [!] impI, simp_all add: pr_pri_agrk_analz)
     apply (rule impI)+
     apply (rule_tac [2] impI)
     apply (rule_tac [2] conjI)
      apply (rule_tac [2-3] impI)+
      apply (rule_tac [4] impI)+
      apply (rule_tac [5] impI)+
      apply (rule_tac [6] conjI, (rule_tac [6] impI)+)+
        apply (rule_tac [6] conjI)
         apply (erule_tac [6] conjE)+
         apply (rule_tac [8] impI)+
         apply (rule_tac [8] notI)
         apply (rule_tac [9] impI, rule_tac [9] conjI)+
           apply (rule_tac [9] impI)+
           apply (rule_tac [10] impI)+
           apply (rule_tac [10] notI)
           apply (rule_tac [11] impI)+
           apply (rule_tac [12] impI)+
           apply (rule_tac [12] notI)
proof simp_all
  fix evsR1 S A U n run
  assume "(evsR1, S, A, U) \<in> protocol" and
   "NonceS (S (Card n, n, run)) = None"
  hence "IntMapK (S (Card n, n, run)) = None"
   by (rule pr_state_1)
  moreover assume "IntMapK (S (Card n, n, run)) = Some b'"
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by simp
next
  fix evsC2 S A U m n run
  assume A: "(evsC2, S, A, U) \<in> protocol"
  moreover assume "NonceS (S (User m, n, run)) = None"
  ultimately have "IntMapK (S (User m, n, run)) = None"
   by (rule pr_state_1)
  with A have "ExtMapK (S (User m, n, run)) = None"
   by (rule pr_state_2)
  moreover assume "ExtMapK (S (User m, n, run)) = Some b"
  ultimately show "Key (sesK (c * d * (a * b))) \<notin> A"
   by simp
next
  fix evsC2 S A U m n run
  assume A: "(evsC2, S, A, U) \<in> protocol"
  moreover assume "NonceS (S (User m, n, run)) = None"
  ultimately have "IntMapK (S (User m, n, run)) = None"
   by (rule pr_state_1)
  with A have "ExtMapK (S (User m, n, run)) = None"
   by (rule pr_state_2)
  moreover assume "ExtMapK (S (User m, n, run)) = Some b"
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by simp
next
  fix evsR2 S A U n run
  assume A: "(evsR2, S, A, U) \<in> protocol" and
   "IntMapK (S (Card n, n, run)) = None"
  hence "ExtMapK (S (Card n, n, run)) = None"
   by (rule pr_state_2)
  with A have "IntAgrK (S (Card n, n, run)) = None"
   by (rule pr_state_3)
  moreover assume "IntAgrK (S (Card n, n, run)) = Some d"
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by simp
next
  fix evsC3 S A U n run
  assume A: "(evsC3, S, A, U) \<in> protocol" and
   "NonceS (S (Card n, n, run)) = Some s'" and
   "IntMapK (S (Card n, n, run)) = Some b'" and
   "ExtMapK (S (Card n, n, run)) = Some a'" and
   "IntAgrK (S (Card n, n, run)) = Some d"
  moreover assume B: "s' + a' * b' = s + a * b" and
   "ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b))"
  hence "ExtAgrK (S (Card n, n, run)) = Some (c * (s' + a' * b'))"
   by simp
  moreover assume C: "Pri_AgrK c \<notin> U"
  have "A \<subseteq> U"
   using A by (rule pr_analz_used)
  hence "Pri_AgrK c \<notin> A"
   using C by (rule contra_subsetD)
  ultimately have "Key (sesK (c * d * (s' + a' * b'))) \<notin> A"
   by (rule pr_ext_agrk_card)
  thus "Key (sesK (c * d * (s + a * b))) \<notin> A"
   using B by simp
next
  fix evsR3 S A U n run
  assume "(evsR3, S, A, U) \<in> protocol"
  moreover assume "0 < m"
  hence "User m \<noteq> Spy"
   by simp
  moreover assume "IntAgrK (S (User m, n, run)) = Some c"
  ultimately have "Pri_AgrK c \<notin> A"
   by (rule pr_int_agrk_user_2)
  moreover assume "Pri_AgrK c \<in> A"
  ultimately show False
   by contradiction
next
  fix evsR3 S A U
  assume "(evsR3, S, A, U) \<in> protocol"
  hence "A \<subseteq> U"
   by (rule pr_analz_used)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by (rule contra_subsetD)
next
  fix evsR3 S A U s' a' b' c' d'
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b))"
  hence "Key (sesK (d * (c * (s + a * b)))) \<in> U"
   by (rule pr_sesk_card)
  moreover have "d * (c * (s + a * b)) = c * d * (s + a * b)"
   by simp
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "sesK (c * d * (s + a * b)) = sesK (c' * d' * (s' + a' * b'))"
  ultimately have "Key (sesK (c' * d' * (s' + a' * b'))) \<in> U"
   by simp
  moreover assume "Key (sesK (c' * d' * (s' + a' * b'))) \<notin> U"
  ultimately show False
   by simp
next
  fix evsR3 S A U s' a' b' c' d'
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b))"
  hence "Key (sesK (d * (c * (s + a * b)))) \<in> U"
   by (rule pr_sesk_card)
  moreover have "d * (c * (s + a * b)) = c * d * (s + a * b)"
   by simp
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "sesK (c * d * (s + a * b)) = sesK (c' * d' * (s' + a' * b'))"
  ultimately have "Key (sesK (c' * d' * (s' + a' * b'))) \<in> U"
   by simp
  moreover assume "Key (sesK (c' * d' * (s' + a' * b'))) \<notin> U"
  ultimately show False
   by simp
next
  fix evsR3 S A U s' c'
  assume "(evsR3, S, A, U) \<in> protocol"
  hence "A \<subseteq> U"
   by (rule pr_analz_used)
  moreover assume "Key (sesK (c' * d * (s' + a' * b'))) \<notin> U"
  ultimately have "Key (sesK (c' * d * (s' + a' * b'))) \<notin> A"
   by (rule contra_subsetD)
  moreover assume "c' * (s' + a' * b') = c * (s + a * b)"
  hence "c' * d * (s' + a' * b') = c * d * (s + a * b)"
   by simp
  ultimately show "Key (sesK (c * d * (s + a * b))) \<notin> A"
   by simp
next
  fix evsFR3 S A U s' a' b' c' d'
  assume
   "(evsFR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b))"
  hence "Key (sesK (d * (c * (s + a * b)))) \<in> U"
   by (rule pr_sesk_card)
  moreover have "d * (c * (s + a * b)) = c * d * (s + a * b)"
   by simp
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "sesK (c * d * (s + a * b)) = sesK (c' * d' * (s' + a' * b'))"
  ultimately have "Key (sesK (c' * d' * (s' + a' * b'))) \<in> U"
   by simp
  moreover assume "Key (sesK (c' * d' * (s' + a' * b'))) \<notin> U"
  ultimately show False
   by simp
qed

lemma pr_sign_key_used:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> Key (priSK X) \<in> U"
by (erule protocol.induct, simp_all)

lemma pr_sign_key_analz:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow> Key (priSK X) \<notin> analz (A \<union> spies evs)"
proof (simp add: pr_key_analz, erule protocol.induct,
 auto simp add: priSK_pubSK priSK_symK)
  fix evsR3 S A U s a b c d
  assume "(evsR3, S, A, U) \<in> protocol"
  hence "Key (priSK X) \<in> U"
   by (rule pr_sign_key_used)
  moreover assume "priSK X = sesK (c * d * (s + a * b))"
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsFR3 S A U s a b c d
  assume "(evsFR3, S, A, U) \<in> protocol"
  hence "Key (priSK X) \<in> U"
   by (rule pr_sign_key_used)
  moreover assume "priSK X = sesK (c * d * (s + a * b))"
  ultimately have "Key (sesK (c * d * (s + a * b))) \<in> U"
   by simp
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show False
   by contradiction
qed

lemma pr_auth_data_parts [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Auth_Data (priAK n) b \<in> parts (A \<union> spies evs) \<longrightarrow>
  (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)"
  (is "_ \<Longrightarrow> ?M \<in> _ \<longrightarrow> _")
apply (erule protocol.induct, simp, subst parts_simp, simp, blast+, simp_all
 add: parts_simp_insert parts_auth_data parts_crypt parts_mpair del: fun_upd_apply)
       apply (rule impI)
       apply ((rule_tac [2] conjI)?, rule_tac [2] impI)+
          apply (rule_tac [3] impI)+
          apply (rule_tac [4] impI, (rule_tac [4] conjI)?)+
           apply (rule_tac [5] impI)+
           apply (rule_tac [6] impI, (rule_tac [6] conjI)?)+
             apply (rule_tac [7] impI)+
             apply (rule_tac [8] impI, (rule_tac [8] conjI)?)+
              apply (rule_tac [9] impI)+
              apply (rule_tac [10] impI)
              apply (rule_tac [11] conjI)
               apply (rule_tac [11-12] impI)+
               apply (rule_tac [13] conjI)
                apply (rule_tac [13-14] impI)+
                apply (rule_tac [15-17] impI)
                apply (erule_tac [17] conjE)
proof -
  fix evsR1 A n' run' s and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>NonceS := Some s\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsR1) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsR1)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp, blast)
next
  fix evsC2 A n' run' s a and S :: state
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsC2 A n' run' m' s a and S :: state
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsC2 A n' run' s a and S :: state
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsC2 A n' run' m' a and S :: state
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>NonceS := Some 0, IntMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsC2 A n' run' s a and S :: state
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsC2 A n' run' m' s a and S :: state
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>NonceS := Some s, IntMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsC2 A n' run' a and S :: state
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>NonceS := Some 0, IntMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsC2 A n' run' m' a and S :: state
  let ?S = "S((User m', n', run') := S (User m', n', run')
    \<lparr>NonceS := Some 0, IntMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsR2 A n' run' a b' and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntMapK := Some b', ExtMapK := Some a\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsR2) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsR2)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  moreover assume "IntMapK (S (Card n', n', run')) = None"
  ultimately show "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
  proof (rule_tac x = m in exI, rule_tac x = run in exI, simp)
  qed (rule impI, simp)
next
  fix evsC3 A n' run' b' c and S :: state
  let ?S = "S((Spy, n', run') := S (Spy, n', run')
    \<lparr>ExtMapK := Some b', IntAgrK := Some c\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC3) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC3)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsC3 A n' run' b' c m and S :: state
  let ?S = "S((User m, n', run') := S (User m, n', run')
    \<lparr>ExtMapK := Some b', IntAgrK := Some c\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC3) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC3)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsR3 A n' run' s a b' c d and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b'))\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsR3) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsR3)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp, blast)
next
  fix evsR3 A n' run' s a b' c d and S :: state
  let ?S = "S((Card n', n', run') := S (Card n', n', run')
    \<lparr>IntAgrK := Some d, ExtAgrK := Some (c * (s + a * b'))\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsR3) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsR3)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp, blast)
next
  fix evsC4 A n' run' c f m and S :: state
  let ?S = "S((User m, n', run') := S (User m, n', run')\<lparr>ExtAgrK := Some f\<rparr>)"
  assume
   "?M \<in> parts (A \<union> spies evsC4) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
   "?M \<in> parts (A \<union> spies evsC4)"
  hence "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b" ..
  then obtain m and run where "IntMapK (S (Card m, m, run)) = Some b"
   by blast
  thus "\<exists>m run. IntMapK (?S (Card m, m, run)) = Some b"
   by (rule_tac x = m in exI, rule_tac x = run in exI, simp)
next
  fix evsR4 n' run' b' and S :: state
  assume "IntMapK (S (Card n', n', run')) = Some b'"
  thus "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b'"
   by blast
next
  fix evsFR4 A U s a b' c f g and S :: state
  assume
    A: "?M \<in> parts (A \<union> spies evsFR4) \<longrightarrow>
      (\<exists>m run. IntMapK (S (Card m, m, run)) = Some b)" and
    B: "(evsFR4, S, A, U) \<in> protocol" and
    C: "Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b')), Auth_Data g b', pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace> \<in> synth (analz (A \<union> spies evsFR4))"
      (is "Crypt _ ?M' \<in> synth (analz ?A)") and
    D: "priAK n = g" and
    E: "b = b'"
  show "\<exists>m run. IntMapK (S (Card m, m, run)) = Some b'"
  proof -
    have "Crypt (sesK (c * f)) ?M' \<in> analz ?A \<or>
      ?M' \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
     using C by (rule synth_crypt)
    moreover {
      assume "Crypt (sesK (c * f)) ?M' \<in> analz ?A"
      hence "Crypt (sesK (c * f)) ?M' \<in> parts ?A"
       by (rule subsetD [OF analz_parts_subset])
      hence "?M' \<in> parts ?A"
       by (rule parts.Body)
      hence "\<lbrace>Auth_Data g b', pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> parts ?A"
       by (rule parts.Snd)
      hence "Auth_Data g b' \<in> parts ?A"
       by (rule parts.Fst)
    }
    moreover {
      assume "?M' \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
      hence "?M' \<in> synth (analz ?A)" ..
      hence "\<lbrace>Auth_Data g b', pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> synth (analz ?A)"
       by (rule synth_analz_snd)
      hence "Auth_Data g b' \<in> synth (analz ?A)"
       by (rule synth_analz_fst)
      hence "Auth_Data g b' \<in> analz ?A \<or>
        Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b' \<in> analz ?A"
       by (rule synth_auth_data)
      moreover {
        assume "Auth_Data g b' \<in> analz ?A"
        hence "Auth_Data g b' \<in> parts ?A"
         by (rule subsetD [OF analz_parts_subset])
      }
      moreover {
        assume "Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b' \<in> analz ?A"
        hence "Pri_AgrK g \<in> analz ?A" ..
        hence "Pri_AgrK (priAK n) \<in> analz ?A"
         using D by simp
        moreover have "Pri_AgrK (priAK n) \<notin> analz ?A"
         using B by (rule pr_auth_key_analz)
        ultimately have "Auth_Data g b' \<in> parts ?A"
         by contradiction
      }
      ultimately have "Auth_Data g b' \<in> parts ?A" ..
    }
    ultimately have "Auth_Data g b' \<in> parts ?A" ..
    thus ?thesis
     using A and D and E by simp
  qed
qed

lemma pr_sign_parts [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Crypt (priSK CA) (Hash (pubAK g)) \<in> parts (A \<union> spies evs) \<longrightarrow>
  (\<exists>n. g = priAK n)"
  (is "_ \<Longrightarrow> ?M g \<in> _ \<longrightarrow> _")
proof (erule protocol.induct, subst parts_simp, (simp, blast)+, simp_all add:
 parts_simp_insert parts_auth_data parts_crypt parts_mpair, rule_tac [!] impI)
  fix evsR4 n
  assume "agrK g = agrK (priAK n)"
  with agrK_inj have "g = priAK n"
   by (rule injD)
  thus "\<exists>n. g = priAK n" ..
next
  fix evsFR4 S A U s a b c f g'
  assume
    A: "?M g \<in> parts (A \<union> spies evsFR4) \<longrightarrow> (\<exists>n. g = priAK n)" and
    B: "(evsFR4, S, A, U) \<in> protocol" and
    C: "Crypt (sesK (c * f)) \<lbrace>pubAK (c * (s + a * b)), Auth_Data g' b,
      pubAK g', ?M g'\<rbrace> \<in> synth (analz (A \<union> spies evsFR4))"
      (is "?M' \<in> synth (analz ?A)")
  assume "agrK g = agrK g'"
  with agrK_inj have D: "g = g'"
   by (rule injD)
  show "\<exists>n. g = priAK n"
  proof -
    have "?M' \<in> analz ?A \<or>
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g' b, pubAK g', ?M g'\<rbrace>
        \<in> synth (analz ?A) \<and>
      Key (sesK (c * f)) \<in> analz ?A"
     using C by (rule synth_crypt)
    moreover {
      assume "?M' \<in> analz ?A"
      hence "?M' \<in> parts ?A"
       by (rule subsetD [OF analz_parts_subset])
      hence "\<lbrace>pubAK (c * (s + a * b)), Auth_Data g' b, pubAK g', ?M g'\<rbrace>
        \<in> parts ?A"
       by (rule parts.Body)
      hence "?M g' \<in> parts ?A"
       by (rule_tac parts.Snd, assumption?)+
      hence "\<exists>n. g' = priAK n"
       using A and D by simp
    }
    moreover {
      assume
       "\<lbrace>pubAK (c * (s + a * b)), Auth_Data g' b, pubAK g', ?M g'\<rbrace>
          \<in> synth (analz ?A) \<and>
        Key (sesK (c * f)) \<in> analz ?A"
      hence
       "\<lbrace>pubAK (c * (s + a * b)), Auth_Data g' b, pubAK g', ?M g'\<rbrace>
          \<in> synth (analz ?A)" ..
      hence "\<lbrace>Auth_Data g' b, pubAK g', ?M g'\<rbrace> \<in> synth (analz ?A)"
       by (rule synth_analz_snd)
      hence "\<lbrace>pubAK g', ?M g'\<rbrace> \<in> synth (analz ?A)"
       by (rule synth_analz_snd)
      hence "?M g' \<in> synth (analz ?A)"
       by (rule synth_analz_snd)
      hence "?M g' \<in> analz ?A \<or>
        Hash (pubAK g') \<in> synth (analz ?A) \<and> Key (priSK CA) \<in> analz ?A"
       by (rule synth_crypt)
      moreover {
        assume "?M g' \<in> analz ?A"
        hence "?M g' \<in> parts ?A"
         by (rule subsetD [OF analz_parts_subset])
        hence "\<exists>n. g' = priAK n"
         using A and D by simp
      }
      moreover {
        assume "Hash (pubAK g') \<in> synth (analz ?A) \<and>
          Key (priSK CA) \<in> analz ?A"
        hence "Key (priSK CA) \<in> analz ?A" ..
        moreover have "Key (priSK CA) \<notin> analz ?A"
         using B by (rule pr_sign_key_analz)
        ultimately have "\<exists>n. g' = priAK n"
         by contradiction
      }
      ultimately have "\<exists>n. g' = priAK n" ..
    }
    ultimately have "\<exists>n. g' = priAK n" ..
    thus "\<exists>n. g = priAK n"
     using D by simp
  qed
qed

lemma pr_key_secrecy_aux [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    User m \<noteq> Spy \<longrightarrow>
    NonceS (S (User m, n, run)) = Some s \<longrightarrow>
    IntMapK (S (User m, n, run)) = Some a \<longrightarrow>
    ExtMapK (S (User m, n, run)) = Some b \<longrightarrow>
    IntAgrK (S (User m, n, run)) = Some c \<longrightarrow>
    ExtAgrK (S (User m, n, run)) = Some f \<longrightarrow>
    Says n run 4 X (User m) (Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evs \<longrightarrow>
  Key (sesK (c * f)) \<notin> A"
apply (erule protocol.induct, (rule_tac [!] impI)+, simp_all split: if_split_asm)
       apply (erule_tac [7] disjE)
        apply simp_all
       apply (erule_tac [7] conjE)+
       apply (erule_tac [8] disjE)+
        apply (erule_tac [8] conjE)+
        apply simp_all
       apply (rule_tac [8] notI)
proof -
  fix evsC2 S A U m n run
  assume A: "(evsC2, S, A, U) \<in> protocol"
  moreover assume "NonceS (S (User m, n, run)) = None"
  ultimately have "IntMapK (S (User m, n, run)) = None"
   by (rule pr_state_1)
  with A have "ExtMapK (S (User m, n, run)) = None"
   by (rule pr_state_2)
  moreover assume "ExtMapK (S (User m, n, run)) = Some b"
  ultimately show "Key (sesK (c * f)) \<notin> A"
   by simp
next
  fix evsC2 S A U m n run
  assume A: "(evsC2, S, A, U) \<in> protocol"
  moreover assume "NonceS (S (User m, n, run)) = None"
  ultimately have "IntMapK (S (User m, n, run)) = None"
   by (rule pr_state_1)
  with A have "ExtMapK (S (User m, n, run)) = None"
   by (rule pr_state_2)
  moreover assume "ExtMapK (S (User m, n, run)) = Some b"
  ultimately show "Key (sesK (c * f)) \<notin> A"
   by simp
next
  fix evsC3 S A U m n run
  assume A: "(evsC3, S, A, U) \<in> protocol" and
   "ExtMapK (S (User m, n, run)) = None"
  hence "IntAgrK (S (User m, n, run)) = None"
   by (rule pr_state_3)
  with A have "ExtAgrK (S (User m, n, run)) = None"
   by (rule pr_state_4)
  moreover assume "ExtAgrK (S (User m, n, run)) = Some f"
  ultimately show "Key (sesK (c * f)) \<notin> A"
   by simp
next
  fix evsR3 S A U d s' s'' a' b' c'
  assume
    A: "(evsR3, S, A, U) \<in> protocol" and
    B: "Key (sesK (c' * d * (s'' + a' * b'))) \<notin> U" and
    C: "Says n run 4 X (User m) (Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evsR3"
      (is "Says _ _ _ _ _ ?M \<in> _")
  show "s'' = s' \<and> Pri_AgrK c' \<in> analz (A \<union> spies evsR3) \<longrightarrow>
    sesK (c * f) \<noteq> sesK (c' * d * (s' + a' * b'))"
  proof (rule impI, rule notI, erule conjE)
    have "?M \<in> spies evsR3"
     using C by (rule set_spies)
    hence "?M \<in> A \<union> spies evsR3"
     by simp
    hence "?M \<in> parts (A \<union> spies evsR3)"
     by (rule parts.Inj)
    with A have "Key (sesK (c * f)) \<in> U"
     by (rule pr_sesk_auth)
    moreover assume "sesK (c * f) = sesK (c' * d * (s' + a' * b'))" and "s'' = s'"
    hence "Key (sesK (c * f)) \<notin> U"
     using B by simp
    ultimately show False
     by contradiction
  qed
next
  fix evsFR3 S A U s' a' b' c' d
  assume
    A: "(evsFR3, S, A, U) \<in> protocol" and
    B: "Key (sesK (c' * d * (s' + a' * b'))) \<notin> U" and
    C: "Says n run 4 X (User m) (Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evsFR3"
      (is "Says _ _ _ _ _ ?M \<in> _")
  show "sesK (c * f) \<noteq> sesK (c' * d * (s' + a' * b'))"
  proof
    have "?M \<in> spies evsFR3"
     using C by (rule set_spies)
    hence "?M \<in> A \<union> spies evsFR3"
     by simp
    hence "?M \<in> parts (A \<union> spies evsFR3)"
     by (rule parts.Inj)
    with A have "Key (sesK (c * f)) \<in> U"
     by (rule pr_sesk_auth)
    moreover assume "sesK (c * f) = sesK (c' * d * (s' + a' * b'))"
    hence "Key (sesK (c * f)) \<notin> U"
     using B by simp
    ultimately show False
     by contradiction
  qed
next
  fix evsC4 S A U n run and m :: nat
  assume "(evsC4, S, A, U) \<in> protocol"
  moreover assume "0 < m"
  hence "User m \<noteq> Spy"
   by simp
  moreover assume "Says n run 4 X (User m) (Crypt (sesK (c * f))
    \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
     Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evsC4"
  ultimately have "ExtAgrK (S (User m, n, run)) \<noteq> None"
   by (rule pr_ext_agrk_user_2)
  moreover assume "ExtAgrK (S (User m, n, run)) = None"
  ultimately show "Key (sesK (c * f)) \<notin> A"
   by contradiction
next
  fix evsR4 A U n run X s' a' b' d e and S :: state
  assume A: "User m = X"
  assume "agrK (c * (s + a * b')) = agrK e"
  with agrK_inj have B: "c * (s + a * b') = e"
   by (rule injD)
  assume "sesK (c * f) = sesK (d * e)"
  with sesK_inj have "c * f = d * e"
   by (rule injD)
  hence C: "c * f = c * d * (s + a * b')"
   using B by simp
  assume "ExtAgrK (S (X, n, run)) = Some f"
  hence D: "ExtAgrK (S (User m, n, run)) = Some f"
   using A by simp
  assume E: "(evsR4, S, A, U) \<in> protocol"
  moreover assume "0 < m"
  hence F: "User m \<noteq> Spy"
   by simp
  moreover assume "NonceS (S (X, n, run)) = Some s"
  hence G: "NonceS (S (User m, n, run)) = Some s"
   using A by simp
  moreover assume "IntMapK (S (X, n, run)) = Some a"
  hence H: "IntMapK (S (User m, n, run)) = Some a"
   using A by simp
  moreover assume "ExtMapK (S (X, n, run)) = Some b'"
  hence I: "ExtMapK (S (User m, n, run)) = Some b'"
   using A by simp
  moreover assume "IntAgrK (S (X, n, run)) = Some c"
  hence J: "IntAgrK (S (User m, n, run)) = Some c"
   using A by simp
  moreover assume K: "NonceS (S (Card n, n, run)) = Some s'"
  moreover assume L: "IntMapK (S (Card n, n, run)) = Some b'"
  moreover assume M: "ExtMapK (S (Card n, n, run)) = Some a'"
  moreover assume N: "IntAgrK (S (Card n, n, run)) = Some d"
  moreover assume "ExtAgrK (S (Card n, n, run)) = Some e"
  hence "ExtAgrK (S (Card n, n, run)) = Some (c * (s + a * b'))"
   using B by simp
  moreover assume "Says n run 4 X (Card n)
    (Crypt (sesK (d * e)) (pubAK (d * (s' + a' * b')))) \<in> set evsR4"
  hence "Says n run 4 (User m) (Card n)
    (Crypt (sesK (d * e)) (pubAK (d * (s' + a' * b')))) \<in> set evsR4"
   using A by simp
  with E and F and D have "d * (s' + a' * b') = f"
   by (rule pr_ext_agrk_user_3)
  hence "c * d * (s' + a' * b') = c * d * (s + a * b')"
   using C by auto
  hence "s' + a' * b' = s + a * b'"
  proof auto
    assume "c = 0"
    moreover have "c * (s + a * b') \<noteq> 0"
     using E and G and H and I and J by (rule pr_int_agrk_user_3)
    ultimately show ?thesis
     by simp
  next
    assume "d = 0"
    moreover have "d * (s' + a' * b') \<noteq> 0"
     using E and K and L and M and N by (rule pr_int_agrk_card)
    ultimately show ?thesis
     by simp
  qed
  ultimately have "Key (sesK (c * d * (s + a * b'))) \<notin> A"
   by (rule pr_sesk_card_user)
  moreover have "c * d * (s + a * b') = d * e"
   using B by simp
  ultimately show "Key (sesK (d * e)) \<notin> A"
   by simp
next
  fix evsFR4 S A U m n run b g
  assume
    A: "(evsFR4, S, A, U) \<in> protocol" and
    B: "ExtMapK (S (User m, n, run)) = Some b" and
    C: "IntAgrK (S (User m, n, run)) = Some c" and
    D: "ExtAgrK (S (User m, n, run)) = Some f" and
    E: "0 < m" and
    F: "Key (sesK (c * f)) \<in> A"
  assume G: "Crypt (sesK (c * f))
    \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
     Crypt (priSK CA) (Hash (pubAK g))\<rbrace> \<in> synth (analz (A \<union> spies evsFR4))"
    (is "Crypt _ ?M \<in> synth (analz ?A)")
  hence "Crypt (sesK (c * f)) ?M \<in> analz ?A \<or>
    ?M \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
   by (rule synth_crypt)
  moreover {
    assume "Crypt (sesK (c * f)) ?M \<in> analz ?A"
    hence "Crypt (sesK (c * f)) ?M \<in> parts ?A"
     by (rule subsetD [OF analz_parts_subset])
    hence "?M \<in> parts ?A"
     by (rule parts.Body)
    hence "Crypt (priSK CA) (Hash (pubAK g)) \<in> parts ?A"
     by (rule_tac parts.Snd, assumption?)+
    with A have "\<exists>n. g = priAK n"
     by (rule pr_sign_parts)
  }
  moreover {
    assume "?M \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
    hence "?M \<in> synth (analz ?A)" ..
    hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
      \<in> synth (analz ?A)"
     by (rule synth_analz_snd)
    hence "\<lbrace>pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace> \<in> synth (analz ?A)"
     by (rule synth_analz_snd)
    hence "Crypt (priSK CA) (Hash (pubAK g)) \<in> synth (analz ?A)"
     by (rule synth_analz_snd)
    hence "Crypt (priSK CA) (Hash (pubAK g)) \<in> analz ?A \<or>
      Hash (pubAK g) \<in> synth (analz ?A) \<and> Key (priSK CA) \<in> analz ?A"
     by (rule synth_crypt)
    moreover {
      assume "Crypt (priSK CA) (Hash (pubAK g)) \<in> analz ?A"
      hence "Crypt (priSK CA) (Hash (pubAK g)) \<in> parts ?A"
       by (rule subsetD [OF analz_parts_subset])
      with A have "\<exists>n. g = priAK n"
       by (rule pr_sign_parts)
    }
    moreover {
      assume "Hash (pubAK g) \<in> synth (analz ?A) \<and> Key (priSK CA) \<in> analz ?A"
      hence "Key (priSK CA) \<in> analz ?A" ..
      moreover have "Key (priSK CA) \<notin> analz ?A"
       using A by (rule pr_sign_key_analz)
      ultimately have "\<exists>n. g = priAK n"
       by contradiction
    }
    ultimately have "\<exists>n. g = priAK n" ..
  }
  ultimately have "\<exists>n. g = priAK n" ..
  then obtain n' where "g = priAK n'" ..
  hence "Crypt (sesK (c * f))
    \<lbrace>pubAK (c * (s + a * b)), Auth_Data (priAK n') b, pubAK (priAK n'),
     Crypt (priSK CA) (Hash (pubAK (priAK n')))\<rbrace> \<in> synth (analz ?A)"
    (is "Crypt _ ?M \<in> _")
   using G by simp
  hence "Crypt (sesK (c * f)) ?M \<in> analz ?A \<or>
    ?M \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
   by (rule synth_crypt)
  moreover {
    assume "Crypt (sesK (c * f)) ?M \<in> analz ?A"
    hence "Crypt (sesK (c * f)) ?M \<in> parts ?A"
     by (rule subsetD [OF analz_parts_subset])
    hence "?M \<in> parts ?A"
     by (rule parts.Body)
    hence "\<lbrace>Auth_Data (priAK n') b, pubAK (priAK n'),
      Crypt (priSK CA) (Hash (pubAK (priAK n')))\<rbrace> \<in> parts ?A"
     by (rule parts.Snd)
    hence "Auth_Data (priAK n') b \<in> parts ?A"
     by (rule parts.Fst)
  }
  moreover {
    assume "?M \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
    hence "?M \<in> synth (analz ?A)" ..
    hence "\<lbrace>Auth_Data (priAK n') b, pubAK (priAK n'),
      Crypt (priSK CA) (Hash (pubAK (priAK n')))\<rbrace> \<in> synth (analz ?A)"
     by (rule synth_analz_snd)
    hence "Auth_Data (priAK n') b \<in> synth (analz ?A)"
     by (rule synth_analz_fst)
    hence "Auth_Data (priAK n') b \<in> analz ?A \<or>
      Pri_AgrK (priAK n') \<in> analz ?A \<and> Pri_AgrK b \<in> analz ?A"
     by (rule synth_auth_data)
    moreover {
      assume "Auth_Data (priAK n') b \<in> analz ?A"
      hence "Auth_Data (priAK n') b \<in> parts ?A"
       by (rule subsetD [OF analz_parts_subset])
    }
    moreover {
      assume "Pri_AgrK (priAK n') \<in> analz ?A \<and> Pri_AgrK b \<in> analz ?A"
      hence "Pri_AgrK (priAK n') \<in> analz ?A" ..
      moreover have "Pri_AgrK (priAK n') \<notin> analz ?A"
       using A by (rule pr_auth_key_analz)
      ultimately have "Auth_Data (priAK n') b \<in> parts ?A"
       by contradiction
    }
    ultimately have "Auth_Data (priAK n') b \<in> parts ?A" ..
  }
  ultimately have "Auth_Data (priAK n') b \<in> parts ?A" ..
  with A have "\<exists>n run. IntMapK (S (Card n, n, run)) = Some b"
   by (rule pr_auth_data_parts)
  then obtain n' and run' where "IntMapK (S (Card n', n', run')) = Some b"
   by blast
  with A have "Pri_AgrK b \<notin> analz ?A"
   by (rule pr_int_mapk_analz)
  hence H: "Pri_AgrK b \<notin> A"
   using A by (simp add: pr_pri_agrk_analz)
  have "\<exists>X. Says n run 3 X (User m) (pubAK f) \<in> set evsFR4"
   using A and D by (rule pr_ext_agrk_user_4)
  then obtain X where "Says n run 3 X (User m) (pubAK f) \<in> set evsFR4" ..
  with A have
   "(\<exists>s a b d. f = d * (s + a * b) \<and>
      NonceS (S (Card n, n, run)) = Some s \<and>
      IntMapK (S (Card n, n, run)) = Some b \<and>
      ExtMapK (S (Card n, n, run)) = Some a \<and>
      IntAgrK (S (Card n, n, run)) = Some d \<and>
      d \<noteq> 0 \<and> s + a * b \<noteq> 0) \<or>
    (\<exists>b. Pri_AgrK b \<in> A \<and>
      ExtMapK (S (User m, n, run)) = Some b)"
    (is "(\<exists>s a b d. ?P s a b d) \<or> ?Q")
   by (rule pr_ext_agrk_user_5)
  moreover have I: "\<not> ?Q"
  proof (rule notI, erule exE, erule conjE)
    fix b'
    assume "ExtMapK (S (User m, n, run)) = Some b'"
    hence "b' = b"
     using B by simp
    moreover assume "Pri_AgrK b' \<in> A"
    ultimately have "Pri_AgrK b \<in> A"
     by simp
    thus False
     using H by contradiction
  qed
  ultimately have "\<exists>s a b d. ?P s a b d"
   by simp
  then obtain s' and a' and b' and d where J: "?P s' a' b' d"
   by blast
  hence "ExtAgrK (S (User m, n, run)) = Some (d * (s' + a' * b'))"
   using D by simp
  with A and C have
   "\<lbrace>Key (sesK (c * (d * (s' + a' * b')))), Agent (User m), Number n, Number run\<rbrace> \<in> U"
   by (rule pr_sesk_user_1)
  moreover have K: "Key (sesK (c * (d * (s' + a' * b')))) \<in> A"
   using F and J by simp
  ultimately have
   "(\<exists>d' e'. c * (d * (s' + a' * b')) = d' * e' \<and>
      IntAgrK (S (Card n, n, run)) = Some d' \<and>
      ExtAgrK (S (Card n, n, run)) = Some e') \<or>
    (\<exists>b. Pri_AgrK b \<in> A \<and>
      ExtMapK (S (User m, n, run)) = Some b)"
    (is "(\<exists>d e. ?P d e) \<or> _")
   by (rule pr_sesk_user_3 [OF A])
  hence "\<exists>d e. ?P d e"
   using I by simp
  then obtain d' and e' where L: "?P d' e'"
   by blast
  hence "d' = d"
   using J by simp
  hence "d * c * (s' + a' * b') = d * e'"
   using L by simp
  hence "e' = c * (s' + a' * b')"
   using J by simp
  hence M: "ExtAgrK (S (Card n, n, run)) = Some (c * (s' + a' * b'))"
   using L by simp
  have "c * (d * (s' + a' * b')) = c * d * (s' + a' * b')"
   by simp
  hence "Key (sesK (c * (d * (s' + a' * b')))) = Key (sesK (c * d * (s' + a' * b')))"
   by (rule arg_cong)
  hence "Key (sesK (c * d * (s' + a' * b'))) \<in> A"
   using K by simp
  moreover have "Key (sesK (c * d * (s' + a' * b'))) \<notin> A"
  proof (rule pr_ext_agrk_card [OF A, of n run], simp_all add: J M)
  qed (rule pr_int_agrk_user_2 [OF A, of m n run], simp_all add: C E)
  ultimately show False
   by contradiction
qed

theorem pr_key_secrecy [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    User m \<noteq> Spy \<longrightarrow>
    Says n run 5 (User m) (Card n) (Crypt (sesK K) (Passwd m)) \<in> set evs \<longrightarrow>
  Key (sesK K) \<notin> analz (A \<union> spies evs)"
proof (simp add: pr_key_analz, erule protocol.induct, simp_all,
 (rule_tac [1] impI)+, (rule_tac [2-3] impI)+, rule_tac [1-2] notI, simp_all)
  fix evsR3 S A U s a b c d
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "Says n run 5 (User m) (Card n)
      (Crypt (sesK (c * d * (s + a * b))) (Passwd m)) \<in> set evsR3"
  hence "Key (sesK (c * d * (s + a * b))) \<in> U"
   by (rule pr_sesk_passwd)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsFR3 S A U s a b c d
  assume
   "(evsFR3, S, A, U) \<in> protocol" and
   "Says n run 5 (User m) (Card n)
      (Crypt (sesK (c * d * (s + a * b))) (Passwd m)) \<in> set evsFR3"
  hence "Key (sesK (c * d * (s + a * b))) \<in> U"
   by (rule pr_sesk_passwd)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsC5 S A U n run s a b c f g X and m :: nat
  assume "(evsC5, S, A, U) \<in> protocol"
  moreover assume "0 < m"
  hence "User m \<noteq> Spy"
   by simp
  moreover assume
   "NonceS (S (User m, n, run)) = Some s" and
   "IntMapK (S (User m, n, run)) = Some a" and
   "ExtMapK (S (User m, n, run)) = Some b" and
   "IntAgrK (S (User m, n, run)) = Some c" and
   "ExtAgrK (S (User m, n, run)) = Some f" and
   "Says n run 4 X (User m) (Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace>)
      \<in> set evsC5"
  ultimately show "Key (sesK (c * f)) \<notin> A"
   by (rule pr_key_secrecy_aux)
qed

theorem pr_passwd_secrecy [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    User m \<noteq> Spy \<longrightarrow>
  Passwd m \<notin> analz (A \<union> spies evs)"
proof (erule protocol.induct, rule_tac [!] impI, simp_all add: analz_simp_insert_2,
 rule contra_subsetD [OF analz_parts_subset], subst parts_simp, simp, blast+,
 rule_tac [3] impI)
  fix evsR1 S A U n s
  assume
    A: "Passwd m \<notin> analz (A \<union> spies evsR1)" and
    B: "(evsR1, S, A, U) \<in> protocol" and
    C: "Pri_AgrK s \<notin> U"
  show
   "(n \<in> bad \<longrightarrow> Passwd m \<notin> analz (insert (Crypt (symK n) (Pri_AgrK s))
      (insert (Pri_AgrK s) (A \<union> spies evsR1)))) \<and>
    (n \<notin> bad \<longrightarrow> Passwd m \<notin> analz (insert (Crypt (symK n) (Pri_AgrK s))
      (A \<union> spies evsR1)))"
    (is "(_ \<longrightarrow> ?T) \<and> (_ \<longrightarrow> ?T')")
  proof (rule conjI, rule_tac [!] impI)
    assume "n \<in> bad"
    hence "Key (invK (symK n)) \<in> analz (A \<union> spies evsR1)"
     using B by (simp add: pr_symk_analz invK_symK)
    hence "Key (invK (symK n)) \<in> analz (insert (Pri_AgrK s) (A \<union> spies evsR1))"
     by (rule rev_subsetD, rule_tac analz_mono, blast)
    moreover have "analz (insert (Pri_AgrK s) (A \<union> spies evsR1)) =
      insert (Pri_AgrK s) (analz (A \<union> spies evsR1))"
     using B and C by (rule pr_pri_agrk_unused)
    ultimately show ?T
     using A by (simp add: analz_crypt_in)
  next
    assume "n \<notin> bad"
    hence "Key (invK (symK n)) \<notin> analz (A \<union> spies evsR1)"
     using B by (simp add: pr_symk_analz invK_symK)
    thus ?T'
     using A by (simp add: analz_crypt_out)
  qed
next
  fix evsFR1 A m' s
  assume
    A: "Passwd m \<notin> analz (A \<union> spies evsFR1)" and
    B: "Crypt (symK m') (Pri_AgrK s) \<in> synth (analz (A \<union> spies evsFR1))"
  thus "Passwd m \<notin> analz (insert (Crypt (symK m') (Pri_AgrK s)) (A \<union> spies evsFR1))"
  proof (cases "Key (invK (symK m')) \<in> analz (A \<union> spies evsFR1)",
   simp_all add: analz_crypt_in analz_crypt_out)
    case True
    have "Crypt (symK m') (Pri_AgrK s) \<in> analz (A \<union> spies evsFR1) \<or>
      Pri_AgrK s \<in> synth (analz (A \<union> spies evsFR1)) \<and>
      Key (symK m') \<in> analz (A \<union> spies evsFR1)"
      (is "?P \<or> ?Q")
     using B by (rule synth_crypt)
    moreover {
      assume ?P
      hence "Pri_AgrK s \<in> analz (A \<union> spies evsFR1)"
       using True by (rule analz.Decrypt)
    }
    moreover {
      assume ?Q
      hence "Pri_AgrK s \<in> synth (analz (A \<union> spies evsFR1))" ..
      hence "Pri_AgrK s \<in> analz (A \<union> spies evsFR1)"
       by (rule synth_simp_intro, simp)
    }
    ultimately have "Pri_AgrK s \<in> analz (A \<union> spies evsFR1)" ..
    thus "Passwd m \<notin> analz (insert (Pri_AgrK s) (A \<union> spies evsFR1))"
     using A by (simp add: analz_simp_insert_1)
  qed
next
  fix evsC2 S A U a
  assume
   "Passwd m \<notin> analz (A \<union> spies evsC2)" and
   "(evsC2, S, A, U) \<in> protocol" and
   "Pri_AgrK a \<notin> U"
  thus "Passwd m \<notin> analz (insert (Pri_AgrK a) (A \<union> spies evsC2))"
   by (subst pr_pri_agrk_unused, simp_all)
next
  fix evsC3 S A U c and m' :: nat
  assume
   "Passwd m \<notin> analz (A \<union> spies evsC3)" and
   "(evsC3, S, A, U) \<in> protocol" and
   "Pri_AgrK c \<notin> U"
  thus "m' = 0 \<longrightarrow> Passwd m \<notin> analz (insert (Pri_AgrK c) (A \<union> spies evsC3))"
   by (rule_tac impI, subst pr_pri_agrk_unused, simp_all)
next
  fix evsR3 S A U s s' a b c d
  assume "Passwd m \<notin> analz (A \<union> spies evsR3)"
  moreover assume
   "(evsR3, S, A, U) \<in> protocol" and
   "Key (sesK (c * d * (s + a * b))) \<notin> U"
    (is "Key ?K \<notin> _")
  hence "analz (insert (Key ?K) (A \<union> spies evsR3)) =
    insert (Key ?K) (analz (A \<union> spies evsR3))"
   by (rule pr_key_unused)
  ultimately show "s' = s \<and> Pri_AgrK c \<in> analz (A \<union> spies evsR3) \<longrightarrow>
    Passwd m \<notin> analz (insert (Key ?K) (A \<union> spies evsR3))"
   by simp
next
  fix evsFR3 S A U s a b c d
  assume "Passwd m \<notin> analz (A \<union> spies evsFR3)"
  moreover assume
   "(evsFR3, S, A, U) \<in> protocol" and
   "Key (sesK (c * d * (s + a * b))) \<notin> U"
    (is "Key ?K \<notin> _")
  hence "analz (insert (Key ?K) (A \<union> spies evsFR3)) =
    insert (Key ?K) (analz (A \<union> spies evsFR3))"
   by (rule pr_key_unused)
  ultimately show "Passwd m \<notin> analz (insert (Key ?K) (A \<union> spies evsFR3))"
   by simp
next
  fix evsC4 A c f
  assume "Passwd m \<notin> analz (A \<union> spies evsC4)"
  thus "Passwd m \<notin> analz (insert (Crypt (sesK (c * f)) (pubAK f)) (A \<union> spies evsC4))"
   by (cases "Key (invK (sesK (c * f))) \<in> analz (A \<union> spies evsC4)",
    simp_all add: analz_crypt_in analz_crypt_out analz_simp_insert_2)
next
  fix evsFC4 A s a b d e
  assume "Passwd m \<notin> analz (A \<union> spies evsFC4)"
  thus "Passwd m \<notin> analz (insert (Crypt (sesK (d * e)) (pubAK (d * (s + a * b))))
    (A \<union> spies evsFC4))"
   by (cases "Key (invK (sesK (d * e))) \<in> analz (A \<union> spies evsFC4)",
    simp_all add: analz_crypt_in analz_crypt_out analz_simp_insert_2)
next
  fix evsR4 S A U n run b d e
  let
    ?A = "A \<union> spies evsR4" and
    ?H = "Hash (pubAK (priAK n))" and
    ?M = "\<lbrace>pubAK (priAK n), Crypt (priSK CA) (Hash (pubAK (priAK n)))\<rbrace>"
  assume
    A: "Passwd m \<notin> analz ?A" and
    B: "(evsR4, S, A, U) \<in> protocol" and
    C: "IntMapK (S (Card n, n, run)) = Some b"
  show "Passwd m \<notin> analz (insert (Crypt (sesK (d * e))
    \<lbrace>pubAK e, Auth_Data (priAK n) b, ?M\<rbrace>) ?A)"
  proof (cases "Key (invK (sesK (d * e))) \<in> analz ?A",
   simp_all add: analz_crypt_in analz_crypt_out analz_mpair analz_simp_insert_2 A)
    have "Key (pubSK CA) \<in> analz ?A"
     using B by (rule pr_valid_key_analz)
    hence D: "analz (insert (Crypt (priSK CA) ?H) ?A) =
      {Crypt (priSK CA) ?H, ?H} \<union> analz ?A"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    have "Pri_AgrK (priAK n) \<notin> analz ?A"
     using B by (rule pr_auth_key_analz)
    hence E: "Pri_AgrK (priAK n) \<notin> analz (insert (Crypt (priSK CA) ?H) ?A)"
     using D by simp
    have "Pri_AgrK b \<notin> analz ?A"
     using B and C by (rule pr_int_mapk_analz)
    hence F: "Pri_AgrK b \<notin> analz (insert (Crypt (priSK CA) ?H) ?A)"
     using D by simp
    show "Passwd m \<notin> analz (insert (Auth_Data (priAK n) b) (insert ?M ?A))"
    proof ((subst insert_commute, simp add: analz_mpair analz_simp_insert_2)+,
     subst analz_auth_data_out [OF E F])
    qed (simp add: A D)
  qed
next
  fix evsFR4 S A U s a b c f g
  let
    ?A = "A \<union> spies evsFR4" and
    ?H = "Hash (pubAK g)" and
    ?M = "\<lbrace>pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>" and
    ?M' = "\<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
      Crypt (priSK CA) (Hash (pubAK g))\<rbrace>"
  assume
    A: "Passwd m \<notin> analz ?A" and
    B: "(evsFR4, S, A, U) \<in> protocol" and
    C: "Crypt (sesK (c * f)) ?M' \<in> synth (analz ?A)"
  have D:
   "Key (invK (sesK (c * f))) \<in> analz ?A \<longrightarrow>
      Pri_AgrK b \<in> analz ?A \<or> Pri_AgrK g \<in> analz ?A \<longrightarrow>
    Pri_AgrK b \<in> analz ?A \<and> Pri_AgrK g \<in> analz ?A"
    (is "?P \<longrightarrow> ?Q \<longrightarrow> ?R")
  proof (rule impI)+
    assume ?P and ?Q
    have "Crypt (sesK (c * f)) ?M' \<in> analz ?A \<or>
      ?M' \<in> synth (analz ?A) \<and> Key (sesK (c * f)) \<in> analz ?A"
     using C by (rule synth_crypt)
    moreover {
      assume "Crypt (sesK (c * f)) ?M' \<in> analz ?A"
      hence "?M' \<in> analz ?A"
       using \<open>?P\<close> by (rule analz.Decrypt)
      hence "\<lbrace>Auth_Data g b, pubAK g, Crypt (priSK CA) (Hash (pubAK g))\<rbrace>
        \<in> analz ?A"
       by (rule analz.Snd)
      hence E: "Auth_Data g b \<in> analz ?A"
       by (rule analz.Fst)
      have ?R
      proof (rule disjE [OF \<open>?Q\<close>])
        assume "Pri_AgrK b \<in> analz ?A"
        moreover from this have "Pri_AgrK g \<in> analz ?A"
         by (rule analz.Auth_Fst [OF E])
        ultimately show ?R ..
      next
        assume "Pri_AgrK g \<in> analz ?A"
        moreover from this have "Pri_AgrK b \<in> analz ?A"
         by (rule analz.Auth_Snd [OF E])
        ultimately show ?R
         by simp
      qed
    }
    moreover {
      assume "?M' \<in> synth (analz ?A) \<and>
        Key (sesK (c * f)) \<in> analz ?A"
      hence "?M' \<in> synth (analz ?A)" ..
      hence "\<lbrace>Auth_Data g b, pubAK g,
        Crypt (priSK CA) (Hash (pubAK g))\<rbrace> \<in> synth (analz ?A)"
       by (rule synth_analz_snd)
      hence "Auth_Data g b \<in> synth (analz ?A)"
       by (rule synth_analz_fst)
      hence "Auth_Data g b \<in> analz ?A \<or>
        Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b \<in> analz ?A"
       by (rule synth_auth_data)
      moreover {
        assume E: "Auth_Data g b \<in> analz ?A"
        have ?R
        proof (rule disjE [OF \<open>?Q\<close>])
          assume "Pri_AgrK b \<in> analz ?A"
          moreover from this have "Pri_AgrK g \<in> analz ?A"
           by (rule analz.Auth_Fst [OF E])
          ultimately show ?R ..
        next
          assume "Pri_AgrK g \<in> analz ?A"
          moreover from this have "Pri_AgrK b \<in> analz ?A"
           by (rule analz.Auth_Snd [OF E])
          ultimately show ?R
           by simp
        qed
      }
      moreover {
        assume "Pri_AgrK g \<in> analz ?A \<and> Pri_AgrK b \<in> analz ?A"
        hence ?R
         by simp
      }
      ultimately have ?R ..
    }
    ultimately show ?R ..
  qed
  show "Passwd m \<notin> analz (insert (Crypt (sesK (c * f)) ?M') ?A)"
  proof (cases "Key (invK (sesK (c * f))) \<in> analz ?A",
   simp_all add: analz_crypt_in analz_crypt_out analz_mpair analz_simp_insert_2 A)
    assume E: "Key (invK (sesK (c * f))) \<in> analz ?A"
    have "Key (pubSK CA) \<in> analz ?A"
     using B by (rule pr_valid_key_analz)
    hence F: "analz (insert (Crypt (priSK CA) ?H) ?A) =
      {Crypt (priSK CA) ?H, ?H} \<union> analz ?A"
     by (simp add: analz_crypt_in analz_simp_insert_2)
    show "Passwd m \<notin> analz (insert (Auth_Data g b) (insert ?M ?A))"
    proof (cases "Pri_AgrK g \<in> analz ?A \<or> Pri_AgrK b \<in> analz ?A", simp_all)
      assume G: "Pri_AgrK g \<in> analz ?A \<or> Pri_AgrK b \<in> analz ?A"
      hence H: "Pri_AgrK g \<in> analz (insert (Crypt (priSK CA) ?H) ?A) \<or>
        Pri_AgrK b \<in> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F by simp
      have I: "Pri_AgrK b \<in> analz ?A \<and> Pri_AgrK g \<in> analz ?A"
       using D and E and G by blast
      hence "Pri_AgrK g \<in> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F by simp
      hence J: "Pri_AgrK g \<in> analz (insert (Pri_AgrK b)
        (insert (Crypt (priSK CA) ?H) ?A))"
       by (rule rev_subsetD, rule_tac analz_mono, blast)
      have K: "Pri_AgrK b \<in> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F and I by simp
      show ?thesis
      proof ((subst insert_commute, simp add: analz_mpair analz_simp_insert_2)+,
       subst analz_auth_data_in [OF H], simp del: Un_insert_right,
       subst analz_simp_insert_1 [OF J], subst analz_simp_insert_1 [OF K])
      qed (simp add: A F)
    next
      assume G: "Pri_AgrK g \<notin> analz ?A \<and> Pri_AgrK b \<notin> analz ?A"
      hence H: "Pri_AgrK g \<notin> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F by simp
      have I: "Pri_AgrK b \<notin> analz (insert (Crypt (priSK CA) ?H) ?A)"
       using F and G by simp
      show ?thesis
      proof ((subst insert_commute, simp add: analz_mpair analz_simp_insert_2)+,
       subst analz_auth_data_out [OF H I])
      qed (simp add: A F)
    qed
  qed
next
  fix evsC5 S A U m' n run s a b c f g X
  let ?M = "\<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
    Crypt (priSK CA) (Hash (pubAK g))\<rbrace>"
  assume
    A: "Passwd m \<notin> analz (A \<union> spies evsC5)" and
    B: "0 < m" and
    C: "(evsC5, S, A, U) \<in> protocol" and
    D: "NonceS (S (User m', n, run)) = Some s" and
    E: "IntMapK (S (User m', n, run)) = Some a" and
    F: "ExtMapK (S (User m', n, run)) = Some b" and
    G: "IntAgrK (S (User m', n, run)) = Some c" and
    H: "ExtAgrK (S (User m', n, run)) = Some f" and
    I: "Says n run 4 X (User m') (Crypt (sesK (c * f)) ?M) \<in> set evsC5"
  from A show "Passwd m \<notin> analz (insert (Crypt (sesK (c * f)) (Passwd m'))
    (A \<union> spies evsC5))"
  proof (cases "Key (invK (sesK (c * f))) \<in> analz (A \<union> spies evsC5)",
   simp_all add: analz_crypt_in analz_crypt_out analz_simp_insert_2, rule_tac notI)
    case True
    moreover assume "m = m'"
    hence "User m' \<noteq> Spy"
     using B by simp
    hence "Key (sesK (c * f)) \<notin> A"
     by (rule pr_key_secrecy_aux [OF C _ D E F G H I])
    hence "Key (invK (sesK (c * f))) \<notin> analz (A \<union> spies evsC5)"
     using C by (simp add: pr_key_analz invK_sesK)
    ultimately show False
     by contradiction
  qed
next
  fix evsFC5 A n d e
  assume
    A: "Passwd m \<notin> analz (A \<union> spies evsFC5)" and
    B: "Crypt (sesK (d * e)) (Passwd n) \<in> synth (analz (A \<union> spies evsFC5))"
  from A show "Passwd m \<notin> analz (insert (Crypt (sesK (d * e)) (Passwd n))
    (A \<union> spies evsFC5))"
  proof (cases "Key (invK (sesK (d * e))) \<in> analz (A \<union> spies evsFC5)",
   simp_all add: analz_crypt_in analz_crypt_out analz_simp_insert_2, rule_tac notI)
    case True
    have "Crypt (sesK (d * e)) (Passwd n) \<in> analz (A \<union> spies evsFC5) \<or>
      Passwd n \<in> synth (analz (A \<union> spies evsFC5)) \<and>
      Key (sesK (d * e)) \<in> analz (A \<union> spies evsFC5)"
      (is "?P \<or> ?Q")
     using B by (rule synth_crypt)
    moreover {
      assume ?P
      hence "Passwd n \<in> analz (A \<union> spies evsFC5)"
       using True by (rule analz.Decrypt)
    }
    moreover {
      assume ?Q
      hence "Passwd n \<in> synth (analz (A \<union> spies evsFC5))" ..
      hence "Passwd n \<in> analz (A \<union> spies evsFC5)"
       by (rule synth_simp_intro, simp)
    }
    ultimately have "Passwd n \<in> analz (A \<union> spies evsFC5)" ..
    moreover assume "m = n"
    hence "Passwd n \<notin> analz (A \<union> spies evsFC5)"
     using A by simp
    ultimately show False
     by contradiction
  qed
next
  fix evsR5 A d e
  assume "Passwd m \<notin> analz (A \<union> spies evsR5)"
  thus "Passwd m \<notin> analz (insert (Crypt (sesK (d * e)) (Number 0)) (A \<union> spies evsR5))"
   by (cases "Key (invK (sesK (d * e))) \<in> analz (A \<union> spies evsR5)",
    simp_all add: analz_crypt_in analz_crypt_out analz_simp_insert_2)
next
  fix evsFR5 A c f
  assume "Passwd m \<notin> analz (A \<union> spies evsFR5)"
  thus "Passwd m \<notin> analz (insert (Crypt (sesK (c * f)) (Number 0)) (A \<union> spies evsFR5))"
   by (cases "Key (invK (sesK (c * f))) \<in> analz (A \<union> spies evsFR5)",
    simp_all add: analz_crypt_in analz_crypt_out analz_simp_insert_2)
qed


subsection "Authenticity theorems"

text \<open>
This section contains a series of lemmas culminating in the authenticity theorems
\<open>pr_user_authenticity\<close> and \<open>pr_card_authenticity\<close>. Structured Isar proofs are used.

\null
\<close>

lemma pr_passwd_parts [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Crypt (sesK K) (Passwd m) \<in> parts (A \<union> spies evs) \<longrightarrow>
  (\<exists>n run. Says n run 5 (User m) (Card n) (Crypt (sesK K) (Passwd m)) \<in> set evs) \<or>
  (\<exists>run. Says m run 5 Spy (Card m) (Crypt (sesK K) (Passwd m)) \<in> set evs)"
  (is "_ \<Longrightarrow> ?M \<in> _ \<longrightarrow> ?P evs \<or> ?Q evs")
proof (erule protocol.induct, subst parts_simp, (simp, blast)+)
qed (simp_all add: parts_simp_insert parts_auth_data parts_crypt parts_mpair, blast+)

lemma pr_unique_run_1 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    \<lbrace>Key (sesK (d * e)), Agent (User m), Number n', Number run'\<rbrace> \<in> U \<longrightarrow>
    IntAgrK (S (Card n, n, run)) = Some d \<longrightarrow>
    ExtAgrK (S (Card n, n, run)) = Some e \<longrightarrow>
  n' = n \<and> run' = run"
proof (erule protocol.induct, simp_all, rule_tac [3] conjI, (rule_tac [1-4] impI)+,
 (rule_tac [5] impI)+, simp_all, (erule_tac [2-3] conjE)+, (rule_tac [!] ccontr))
  fix evsR3 S A U s' a b c
  assume "c * (s' + a * b) = e"
  hence A: "d * e = c * d * (s' + a * b)"
   by simp
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "\<lbrace>Key (sesK (d * e)), Agent (User m), Number n', Number run'\<rbrace> \<in> U"
  hence "Key (sesK (d * e)) \<in> U"
   by (rule pr_sesk_user_2)
  hence "Key (sesK (c * d * (s' + a * b))) \<in> U"
   by (simp only: A)
  moreover assume "Key (sesK (c * d * (s' + a * b))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsR3 S A U s a b c d'
  assume "Key (sesK (c * d' * (s + a * b))) \<notin> U"
  moreover assume "sesK (d * e) = sesK (c * d' * (s + a * b))"
  with sesK_inj have "d * e = c * d' * (s + a * b)"
   by (rule injD)
  ultimately have "Key (sesK (d * e)) \<notin> U"
   by simp
  moreover assume
   "(evsR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some e"
  hence "Key (sesK (d * e)) \<in> U"
   by (rule pr_sesk_card)
  ultimately show False
   by contradiction
next
  fix evsFR3 S A U s a b c d'
  assume "Key (sesK (c * d' * (s + a * b))) \<notin> U"
  moreover assume "sesK (d * e) = sesK (c * d' * (s + a * b))"
  with sesK_inj have "d * e = c * d' * (s + a * b)"
   by (rule injD)
  ultimately have "Key (sesK (d * e)) \<notin> U"
   by simp
  moreover assume
   "(evsFR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some e"
  hence "Key (sesK (d * e)) \<in> U"
   by (rule pr_sesk_card)
  ultimately show False
   by contradiction
qed

lemma pr_unique_run_2:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    IntAgrK (S (User m, n', run')) = Some c \<Longrightarrow>
    ExtAgrK (S (User m, n', run')) = Some f \<Longrightarrow>
    IntAgrK (S (Card n, n, run)) = Some d \<Longrightarrow>
    ExtAgrK (S (Card n, n, run)) = Some e \<Longrightarrow>
    d * e = c * f \<Longrightarrow>
  n' = n \<and> run' = run"
proof (frule pr_sesk_user_1, assumption+, drule sym [of "d * e"], simp)
qed (rule pr_unique_run_1)

lemma pr_unique_run_3 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    IntAgrK (S (Card n', n', run')) = Some d' \<longrightarrow>
    ExtAgrK (S (Card n', n', run')) = Some e' \<longrightarrow>
    IntAgrK (S (Card n, n, run)) = Some d \<longrightarrow>
    ExtAgrK (S (Card n, n, run)) = Some e \<longrightarrow>
    d * e = d' * e' \<longrightarrow>
  n' = n \<and> run' = run"
proof (erule protocol.induct, simp_all, rule_tac [!] conjI, (rule_tac [!] impI)+,
 simp_all, rule_tac [!] ccontr)
  fix evsR3 S A U n' run' s' a b c
  assume "c * (s' + a * b) = e"
  hence A: "d * e = c * d * (s' + a * b)"
   by simp
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n', n', run')) = Some d'" and
   "ExtAgrK (S (Card n', n', run')) = Some e'"
  hence "Key (sesK (d' * e')) \<in> U"
   by (rule pr_sesk_card)
  moreover assume "d * e = d' * e'"
  ultimately have "Key (sesK (c * d * (s' + a * b))) \<in> U"
   using A by simp
  moreover assume "Key (sesK (c * d * (s' + a * b))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsR3 S A U s' a b c
  assume "c * (s' + a * b) = e'"
  hence A: "d' * e' = c * d' * (s' + a * b)"
   by simp
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some e"
  hence "Key (sesK (d * e)) \<in> U"
   by (rule pr_sesk_card)
  moreover assume "d * e = d' * e'"
  ultimately have "Key (sesK (c * d' * (s' + a * b))) \<in> U"
   using A by simp
  moreover assume "Key (sesK (c * d' * (s' + a * b))) \<notin> U"
  ultimately show False
   by contradiction
qed

lemma pr_unique_run_4 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n' run' 5 X (Card n') (Crypt (sesK (d * e)) (Passwd m)) \<in> set evs \<longrightarrow>
    IntAgrK (S (Card n, n, run)) = Some d \<longrightarrow>
    ExtAgrK (S (Card n, n, run)) = Some e \<longrightarrow>
  n' = n \<and> run' = run"
proof (erule protocol.induct, simp_all, (rule_tac [!] impI)+, rule_tac [1-3] impI,
 simp_all, (erule_tac [2-3] conjE)+)
  fix evsR3 S A U n run s' a b c
  assume "c * (s' + a * b) = e"
  hence A: "d * e = c * d * (s' + a * b)"
   by simp
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "Says n' run' 5 X (Card n') (Crypt (sesK (d * e)) (Passwd m)) \<in> set evsR3"
  hence "Key (sesK (d * e)) \<in> U"
   by (rule pr_sesk_passwd)
  hence "Key (sesK (c * d * (s' + a * b))) \<in> U"
   by (simp only: A)
  moreover assume "Key (sesK (c * d * (s' + a * b))) \<notin> U"
  ultimately show "n' = n \<and> run' = run"
   by contradiction
next
  fix evsC5 S A U m n' run' c f
  assume
   "(evsC5, S, A, U) \<in> protocol" and
   "IntAgrK (S (User m, n', run')) = Some c" and
   "ExtAgrK (S (User m, n', run')) = Some f" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some e"
  moreover assume "sesK (d * e) = sesK (c * f)"
  with sesK_inj have "d * e = c * f"
   by (rule injD)
  ultimately show "n' = n \<and> run' = run"
   by (rule pr_unique_run_2)
next
  fix evsFC5 S A U n' run' d' e'
  assume
   "(evsFC5, S, A, U) \<in> protocol" and
   "IntAgrK (S (Card n', n', run')) = Some d'" and
   "ExtAgrK (S (Card n', n', run')) = Some e'" and
   "IntAgrK (S (Card n, n, run)) = Some d" and
   "ExtAgrK (S (Card n, n, run)) = Some e"
  moreover assume "sesK (d * e) = sesK (d' * e')"
  with sesK_inj have "d * e = d' * e'"
   by (rule injD)
  ultimately show "n' = n \<and> run' = run"
   by (rule pr_unique_run_3)
qed

theorem pr_user_authenticity [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n run 5 X (Card n) (Crypt (sesK K) (Passwd m)) \<in> set evs \<longrightarrow>
  Says n run 5 (User m) (Card n) (Crypt (sesK K) (Passwd m)) \<in> set evs"
proof (erule protocol.induct, simp_all, rule impI, simp)
  fix evsFC5 S A U n run d e
  assume
   A: "Says n run 5 Spy (Card n) (Crypt (sesK (d * e)) (Passwd n)) \<in> set evsFC5 \<longrightarrow>
     Says n run 5 (User n) (Card n) (Crypt (sesK (d * e)) (Passwd n)) \<in> set evsFC5"
     (is "_ \<longrightarrow> ?T") and
   B: "(evsFC5, S, A, U) \<in> protocol" and
   C: "IntAgrK (S (Card n, n, run)) = Some d" and
   D: "ExtAgrK (S (Card n, n, run)) = Some e" and
   E: "Crypt (sesK (d * e)) (Passwd n) \<in> synth (analz (A \<union> spies evsFC5))"
  show "n = 0 \<or> ?T"
  proof (cases "n = 0", simp_all)
    assume "0 < n"
    hence "User n \<noteq> Spy"
     by simp
    with B have F: "Passwd n \<notin> analz (A \<union> spies evsFC5)"
     by (rule pr_passwd_secrecy)
    have "Crypt (sesK (d * e)) (Passwd n) \<in> analz (A \<union> spies evsFC5) \<or>
      Passwd n \<in> synth (analz (A \<union> spies evsFC5)) \<and>
      Key (sesK (d * e)) \<in> analz (A \<union> spies evsFC5)"
      (is "?P \<or> ?Q")
     using E by (rule synth_crypt)
    moreover have "\<not> ?Q"
    proof
      assume ?Q
      hence "Passwd n \<in> synth (analz (A \<union> spies evsFC5))" ..
      hence "Passwd n \<in> analz (A \<union> spies evsFC5)"
       by (rule synth_simp_intro, simp)
      thus False
       using F by contradiction
    qed
    ultimately have ?P
     by simp
    hence "Crypt (sesK (d * e)) (Passwd n) \<in> parts (A \<union> spies evsFC5)"
     by (rule subsetD [OF analz_parts_subset])
    with B have
     "(\<exists>n' run'. Says n' run' 5 (User n) (Card n') (Crypt (sesK (d * e)) (Passwd n))
        \<in> set evsFC5) \<or>
      (\<exists>run'. Says n run' 5 Spy (Card n) (Crypt (sesK (d * e)) (Passwd n))
        \<in> set evsFC5)"
      (is "(\<exists>n' run'. ?P n' run') \<or> (\<exists>run'. ?Q run')")
     by (rule pr_passwd_parts)
    moreover {
      assume "\<exists>n' run'. ?P n' run'"
      then obtain n' and run' where "?P n' run'"
       by blast
      moreover from this have "n' = n \<and> run' = run"
       by (rule pr_unique_run_4 [OF B _ C D])
      ultimately have ?T
       by simp
    }
    moreover {
      assume "\<exists>run'. ?Q run'"
      then obtain run' where "?Q run'" ..
      moreover from this have "n = n \<and> run' = run"
       by (rule pr_unique_run_4 [OF B _ C D])
      ultimately have "?Q run"
       by simp
      with A have ?T ..
    }
    ultimately show ?T ..
  qed
qed

lemma pr_confirm_parts [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Crypt (sesK K) (Number 0) \<in> parts (A \<union> spies evs) \<longrightarrow>
    Key (sesK K) \<notin> A \<longrightarrow>
  (\<exists>n run X.
    Says n run 5 X (Card n) (Crypt (sesK K) (Passwd n)) \<in> set evs \<and>
    Says n run 5 (Card n) X (Crypt (sesK K) (Number 0)) \<in> set evs)"
  (is "_ \<Longrightarrow> _ \<longrightarrow> _ \<longrightarrow> ?P K evs")
proof (erule protocol.induct, simp, subst parts_simp, simp, blast+,
 simp_all add: parts_simp_insert parts_auth_data parts_crypt parts_mpair,
 rule_tac [3] conjI, (rule_tac [!] impI)+, simp_all, blast+)
  fix evsFR5 S A U c f
  assume
    A: "Crypt (sesK (c * f)) (Number 0) \<in> parts (A \<union> spies evsFR5) \<longrightarrow>
      ?P (c * f) evsFR5" and
    B: "(evsFR5, S, A, U) \<in> protocol" and
    C: "Key (sesK (c * f)) \<notin> A" and
    D: "Crypt (sesK (c * f)) (Number 0) \<in> synth (analz (A \<union> spies evsFR5))"
  show "?P (c * f) evsFR5"
  proof -
    have "Crypt (sesK (c * f)) (Number 0) \<in> analz (A \<union> spies evsFR5) \<or>
      Number 0 \<in> synth (analz (A \<union> spies evsFR5)) \<and>
      Key (sesK (c * f)) \<in> analz (A \<union> spies evsFR5)"
     using D by (rule synth_crypt)
    moreover have "Key (sesK (c * f)) \<notin> analz (A \<union> spies evsFR5)"
     using B and C by (simp add: pr_key_analz)
    ultimately have "Crypt (sesK (c * f)) (Number 0) \<in> analz (A \<union> spies evsFR5)"
     by simp
    hence "Crypt (sesK (c * f)) (Number 0) \<in> parts (A \<union> spies evsFR5)"
     by (rule subsetD [OF analz_parts_subset])
    with A show ?thesis ..
  qed
qed

lemma pr_confirm_says [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n run 5 X Spy (Crypt (sesK K) (Number 0)) \<in> set evs \<longrightarrow>
  Says n run 5 Spy (Card n) (Crypt (sesK K) (Passwd n)) \<in> set evs"
by (erule protocol.induct, simp_all)

lemma pr_passwd_says [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n run 5 X (Card n) (Crypt (sesK K) (Passwd m)) \<in> set evs \<longrightarrow>
  X = User m \<or> X = Spy"
by (erule protocol.induct, simp_all)

lemma pr_unique_run_5 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    \<lbrace>Key (sesK K), Agent (User m'), Number n', Number run'\<rbrace> \<in> U \<longrightarrow>
    \<lbrace>Key (sesK K), Agent (User m), Number n, Number run\<rbrace> \<in> U \<longrightarrow>
  m = m' \<and> n = n' \<and> run = run'"
proof (erule protocol.induct, simp_all, blast, (rule conjI, rule impI)+,
 rule_tac [2] impI, (rule_tac [3] impI)+, rule_tac [4] conjI, (rule_tac [4-5] impI)+,
 simp_all, blast, rule_tac [!] ccontr)
  fix evsR3 S A U s a b c d
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "\<lbrace>Key (sesK (c * d * (s + a * b))), Agent (User m), Number n, Number run\<rbrace> \<in> U"
  hence "Key (sesK (c * d * (s + a * b))) \<in> U"
   by (rule pr_sesk_user_2)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsR3 S A U s a b c d
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "\<lbrace>Key (sesK (c * d * (s + a * b))), Agent (User m'), Number n', Number run'\<rbrace> \<in> U"
  hence "Key (sesK (c * d * (s + a * b))) \<in> U"
   by (rule pr_sesk_user_2)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsFR3 S A U s a b c d
  assume
   "(evsFR3, S, A, U) \<in> protocol" and
   "\<lbrace>Key (sesK (c * d * (s + a * b))), Agent (User m), Number n, Number run\<rbrace> \<in> U"
  hence "Key (sesK (c * d * (s + a * b))) \<in> U"
   by (rule pr_sesk_user_2)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show False
   by contradiction
next
  fix evsFR3 S A U s a b c d
  assume
   "(evsFR3, S, A, U) \<in> protocol" and
   "\<lbrace>Key (sesK (c * d * (s + a * b))), Agent (User m'), Number n', Number run'\<rbrace> \<in> U"
  hence "Key (sesK (c * d * (s + a * b))) \<in> U"
   by (rule pr_sesk_user_2)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show False
   by contradiction
qed

lemma pr_unique_run_6:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    \<lbrace>Key (sesK (c * f)), Agent (User m'), Number n', Number run'\<rbrace> \<in> U \<Longrightarrow>
    IntAgrK (S (User m, n, run)) = Some c \<Longrightarrow>
    ExtAgrK (S (User m, n, run)) = Some f \<Longrightarrow>
  m = m' \<and> n = n' \<and> run = run'"
proof (frule pr_sesk_user_1, assumption+)
qed (rule pr_unique_run_5)

lemma pr_unique_run_7 [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n' run' 5 (User m') (Card n') (Crypt (sesK K) (Passwd m')) \<in> set evs \<longrightarrow>
    \<lbrace>Key (sesK K), Agent (User m), Number n, Number run\<rbrace> \<in> U \<longrightarrow>
    Key (sesK K) \<notin> A \<longrightarrow>
  m' = m \<and> n' = n \<and> run' = run"
proof (erule protocol.induct, simp_all, (rule impI)+, (rule_tac [2-3] impI)+,
 (erule_tac [3] conjE)+, (drule_tac [3] sym [of m'])+, drule_tac [3] sym [of 0],
 simp_all)
  fix evsR3 S A U n run s a b c d
  assume
   "(evsR3, S, A, U) \<in> protocol" and
   "Says n' run' 5 (User m') (Card n')
      (Crypt (sesK (c * d * (s + a * b))) (Passwd m')) \<in> set evsR3"
  hence "Key (sesK (c * d * (s + a * b))) \<in> U"
   by (rule pr_sesk_passwd)
  moreover assume "Key (sesK (c * d * (s + a * b))) \<notin> U"
  ultimately show "m' = m \<and> n' = n \<and> run' = run"
   by contradiction
next
  fix evsC5 S A U m' n' run' c f
  assume
   "(evsC5, S, A, U) \<in> protocol" and
   "\<lbrace>Key (sesK (c * f)), Agent (User m), Number n, Number run\<rbrace> \<in> U" and
   "IntAgrK (S (User m', n', run')) = Some c" and
   "ExtAgrK (S (User m', n', run')) = Some f"
  thus "m' = m \<and> n' = n \<and> run' = run"
   by (rule pr_unique_run_6)
next
  fix evsFC5 S A U run' d e
  assume
    A: "Says 0 run' 5 Spy (Card 0) (Crypt (sesK (d * e)) (Passwd 0)) \<in> set evsFC5 \<longrightarrow>
      m = 0 \<and> n = 0 \<and> run' = run" and
    B: "(evsFC5, S, A, U) \<in> protocol" and
    C: "IntAgrK (S (Card 0, 0, run')) = Some d" and
    D: "ExtAgrK (S (Card 0, 0, run')) = Some e" and
    E: "Crypt (sesK (d * e)) (Passwd 0) \<in> synth (analz (A \<union> spies evsFC5))" and
    F: "Key (sesK (d * e)) \<notin> A"
  have "Crypt (sesK (d * e)) (Passwd 0) \<in> analz (A \<union> spies evsFC5) \<or>
    Passwd 0 \<in> synth (analz (A \<union> spies evsFC5)) \<and>
    Key (sesK (d * e)) \<in> analz (A \<union> spies evsFC5)"
   using E by (rule synth_crypt)
  moreover have "Key (sesK (d * e)) \<notin> analz (A \<union> spies evsFC5)"
   using B and F by (simp add: pr_key_analz)
  ultimately have "Crypt (sesK (d * e)) (Passwd 0) \<in> analz (A \<union> spies evsFC5)"
   by simp
  hence "Crypt (sesK (d * e)) (Passwd 0) \<in> parts (A \<union> spies evsFC5)"
   by (rule subsetD [OF analz_parts_subset])
  with B have
   "(\<exists>n run. Says n run 5 Spy (Card n) (Crypt (sesK (d * e)) (Passwd 0))
      \<in> set evsFC5) \<or>
    (\<exists>run. Says 0 run 5 Spy (Card 0) (Crypt (sesK (d * e)) (Passwd 0))
      \<in> set evsFC5)"
    (is "(\<exists>n run. ?P n run) \<or> (\<exists>run. ?Q run)")
   by (rule pr_passwd_parts)
  moreover {
    assume "\<exists>n run. ?P n run"
    then obtain n'' and run'' where "?P n'' run''"
     by blast
    moreover from this have "n'' = 0 \<and> run'' = run'"
     by (rule pr_unique_run_4 [OF B _ C D])
    ultimately have "?P 0 run'"
     by simp
  }
  moreover {
    assume "\<exists>run. ?Q run"
    then obtain run'' where "?Q run''" ..
    hence "\<exists>n. ?P n run''" ..
    then obtain n'' where "?P n'' run''" ..
    moreover from this have "n'' = 0 \<and> run'' = run'"
     by (rule pr_unique_run_4 [OF B _ C D])
    ultimately have "?P 0 run'"
     by simp
  }
  ultimately have "?P 0 run'" ..
  with A show "m = 0 \<and> n = 0 \<and> run' = run" ..
qed

lemma pr_unique_run_8:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n' run' 5 (User m') (Card n') (Crypt (sesK (c * f)) (Passwd m')) \<in> set evs \<Longrightarrow>
    IntAgrK (S (User m, n, run)) = Some c \<Longrightarrow>
    ExtAgrK (S (User m, n, run)) = Some f \<Longrightarrow>
    Key (sesK (c * f)) \<notin> A \<Longrightarrow>
  m' = m \<and> n' = n \<and> run' = run"
proof (frule pr_sesk_user_1, assumption+)
qed (rule pr_unique_run_7)

lemma pr_unique_passwd_parts [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Crypt (sesK K) (Passwd m') \<in> parts (A \<union> spies evs) \<longrightarrow>
    Crypt (sesK K) (Passwd m) \<in> parts (A \<union> spies evs) \<longrightarrow>
  m' = m"
proof (erule protocol.induct, simp, subst parts_simp, simp, blast+,
 simp_all add: parts_simp_insert parts_auth_data parts_crypt parts_mpair,
 rule_tac [!] conjI, (rule_tac [!] impI)+, erule_tac [!] conjE, simp_all)
  fix evsC5 S A U m'' n run s a b c f g X
  assume
    A: "(evsC5, S, A, U) \<in> protocol" and
    B: "NonceS (S (User m'', n, run)) = Some s" and
    C: "IntMapK (S (User m'', n, run)) = Some a" and
    D: "ExtMapK (S (User m'', n, run)) = Some b" and
    E: "IntAgrK (S (User m'', n, run)) = Some c" and
    F: "ExtAgrK (S (User m'', n, run)) = Some f" and
    G: "Crypt (sesK (c * f)) (Passwd m) \<in> parts (A \<union> spies evsC5)" and
    H: "m' = m''" and
    I: "Says n run 4 X (User m'') (Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evsC5"
  show "m'' = m"
  proof (cases "m'' = 0", rule classical)
    case True
    moreover assume "m'' \<noteq> m"
    ultimately have J: "User m \<noteq> Spy"
     using H by simp
    have
     "(\<exists>n run. Says n run 5 (User m) (Card n) (Crypt (sesK (c * f)) (Passwd m))
        \<in> set evsC5) \<or>
      (\<exists>run. Says m run 5 Spy (Card m) (Crypt (sesK (c * f)) (Passwd m))
        \<in> set evsC5)"
      (is "(\<exists>n run. ?P n run) \<or> (\<exists>run. ?Q run)")
     using A and G by (rule pr_passwd_parts)
    moreover {
      assume "\<exists>n run. ?P n run"
      then obtain n' and run' where K: "?P n' run'"
       by blast
      with A and J have "Key (sesK (c * f)) \<notin> analz (A \<union> spies evsC5)"
       by (rule pr_key_secrecy)
      hence "Key (sesK (c * f)) \<notin> A"
       using A by (simp add: pr_key_analz)
      hence "m = m'' \<and> n' = n \<and> run' = run"
       by (rule pr_unique_run_8 [OF A K E F])
      hence ?thesis
       by simp
    }
    moreover {
      assume "\<exists>run. ?Q run"
      then obtain run' where "?Q run'" ..
      with A have K: "?P m run'"
       by (rule pr_user_authenticity)
      with A and J have "Key (sesK (c * f)) \<notin> analz (A \<union> spies evsC5)"
       by (rule pr_key_secrecy)
      hence "Key (sesK (c * f)) \<notin> A"
       using A by (simp add: pr_key_analz)
      hence "m = m'' \<and> m = n \<and> run' = run"
       by (rule pr_unique_run_8 [OF A K E F])
      hence ?thesis
       by simp
    }
    ultimately show ?thesis ..
  next
    case False
    hence "User m'' \<noteq> Spy"
     by simp
    hence J: "Key (sesK (c * f)) \<notin> A"
     by (rule pr_key_secrecy_aux [OF A _ B C D E F I])
    have
     "(\<exists>n run. Says n run 5 (User m) (Card n) (Crypt (sesK (c * f)) (Passwd m))
        \<in> set evsC5) \<or>
      (\<exists>run. Says m run 5 Spy (Card m) (Crypt (sesK (c * f)) (Passwd m))
        \<in> set evsC5)"
      (is "(\<exists>n run. ?P n run) \<or> (\<exists>run. ?Q run)")
     using A and G by (rule pr_passwd_parts)
    moreover {
      assume "\<exists>n run. ?P n run"
      then obtain n' and run' where "?P n' run'"
       by blast
      hence "m = m'' \<and> n' = n \<and> run' = run"
       by (rule pr_unique_run_8 [OF A _ E F J])
      hence ?thesis
       by simp
    }
    moreover {
      assume "\<exists>run. ?Q run"
      then obtain run' where "?Q run'" ..
      with A have "?P m run'"
       by (rule pr_user_authenticity)
      hence "m = m'' \<and> m = n \<and> run' = run"
       by (rule pr_unique_run_8 [OF A _ E F J])
      hence ?thesis
       by simp
    }
    ultimately show ?thesis ..
  qed
next
  fix evsC5 S A U m'' n run s a b c f g X
  assume
    A: "(evsC5, S, A, U) \<in> protocol" and
    B: "NonceS (S (User m'', n, run)) = Some s" and
    C: "IntMapK (S (User m'', n, run)) = Some a" and
    D: "ExtMapK (S (User m'', n, run)) = Some b" and
    E: "IntAgrK (S (User m'', n, run)) = Some c" and
    F: "ExtAgrK (S (User m'', n, run)) = Some f" and
    G: "Crypt (sesK (c * f)) (Passwd m') \<in> parts (A \<union> spies evsC5)" and
    H: "m = m''" and
    I: "Says n run 4 X (User m'') (Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evsC5"
  show "m' = m''"
  proof (cases "m'' = 0", rule classical)
    case True
    moreover assume "m' \<noteq> m''"
    ultimately have J: "User m' \<noteq> Spy"
     using H by simp
    have
     "(\<exists>n run. Says n run 5 (User m') (Card n) (Crypt (sesK (c * f)) (Passwd m'))
        \<in> set evsC5) \<or>
      (\<exists>run. Says m' run 5 Spy (Card m') (Crypt (sesK (c * f)) (Passwd m'))
        \<in> set evsC5)"
      (is "(\<exists>n run. ?P n run) \<or> (\<exists>run. ?Q run)")
     using A and G by (rule pr_passwd_parts)
    moreover {
      assume "\<exists>n run. ?P n run"
      then obtain n' and run' where K: "?P n' run'"
       by blast
      with A and J have "Key (sesK (c * f)) \<notin> analz (A \<union> spies evsC5)"
       by (rule pr_key_secrecy)
      hence "Key (sesK (c * f)) \<notin> A"
       using A by (simp add: pr_key_analz)
      hence "m' = m'' \<and> n' = n \<and> run' = run"
       by (rule pr_unique_run_8 [OF A K E F])
      hence ?thesis
       by simp
    }
    moreover {
      assume "\<exists>run. ?Q run"
      then obtain run' where "?Q run'" ..
      with A have K: "?P m' run'"
       by (rule pr_user_authenticity)
      with A and J have "Key (sesK (c * f)) \<notin> analz (A \<union> spies evsC5)"
       by (rule pr_key_secrecy)
      hence "Key (sesK (c * f)) \<notin> A"
       using A by (simp add: pr_key_analz)
      hence "m' = m'' \<and> m' = n \<and> run' = run"
       by (rule pr_unique_run_8 [OF A K E F])
      hence ?thesis
       by simp
    }
    ultimately show ?thesis ..
  next
    case False
    hence "User m'' \<noteq> Spy"
     by simp
    hence J: "Key (sesK (c * f)) \<notin> A"
     by (rule pr_key_secrecy_aux [OF A _ B C D E F I])
    have
     "(\<exists>n run. Says n run 5 (User m') (Card n) (Crypt (sesK (c * f)) (Passwd m'))
        \<in> set evsC5) \<or>
      (\<exists>run. Says m' run 5 Spy (Card m') (Crypt (sesK (c * f)) (Passwd m'))
        \<in> set evsC5)"
      (is "(\<exists>n run. ?P n run) \<or> (\<exists>run. ?Q run)")
     using A and G by (rule pr_passwd_parts)
    moreover {
      assume "\<exists>n run. ?P n run"
      then obtain n' and run' where "?P n' run'"
       by blast
      hence "m' = m'' \<and> n' = n \<and> run' = run"
       by (rule pr_unique_run_8 [OF A _ E F J])
      hence ?thesis
       by simp
    }
    moreover {
      assume "\<exists>run. ?Q run"
      then obtain run' where "?Q run'" ..
      with A have "?P m' run'"
       by (rule pr_user_authenticity)
      hence "m' = m'' \<and> m' = n \<and> run' = run"
       by (rule pr_unique_run_8 [OF A _ E F J])
      hence ?thesis
       by simp
    }
    ultimately show ?thesis ..
  qed
next
  fix evsFC5 S A U n d e
  assume
    A: "Crypt (sesK (d * e)) (Passwd n) \<in> parts (A \<union> spies evsFC5) \<longrightarrow>
      n = m" and
    B: "(evsFC5, S, A, U) \<in> protocol" and
    C: "Crypt (sesK (d * e)) (Passwd n) \<in> synth (analz (A \<union> spies evsFC5))" and
    D: "Crypt (sesK (d * e)) (Passwd m) \<in> parts (A \<union> spies evsFC5)"
  show "n = m"
  proof (rule classical)
    assume E: "n \<noteq> m"
    have F: "Crypt (sesK (d * e)) (Passwd n) \<in> analz (A \<union> spies evsFC5) \<or>
      Passwd n \<in> synth (analz (A \<union> spies evsFC5)) \<and>
      Key (sesK (d * e)) \<in> analz (A \<union> spies evsFC5)"
     using C by (rule synth_crypt)
    have "Crypt (sesK (d * e)) (Passwd n) \<in> analz (A \<union> spies evsFC5)"
    proof (rule disjE [OF F], assumption, erule conjE, cases "n = 0")
      case True
      hence G: "User m \<noteq> Spy"
       using E by simp
      have
       "(\<exists>n run. Says n run 5 (User m) (Card n) (Crypt (sesK (d * e)) (Passwd m))
          \<in> set evsFC5) \<or>
        (\<exists>run. Says m run 5 Spy (Card m) (Crypt (sesK (d * e)) (Passwd m))
          \<in> set evsFC5)"
        (is "(\<exists>n run. ?P n run) \<or> (\<exists>run. ?Q run)")
       using B and D by (rule pr_passwd_parts)
      moreover {
        assume "\<exists>n run. ?P n run"
        then obtain n' and run where "?P n' run"
         by blast
        with B and G have "Key (sesK (d * e)) \<notin> analz (A \<union> spies evsFC5)"
         by (rule pr_key_secrecy)
      }
      moreover {
        assume "\<exists>run. ?Q run"
        then obtain run where "?Q run" ..
        with B have "?P m run"
         by (rule pr_user_authenticity)
        with B and G have "Key (sesK (d * e)) \<notin> analz (A \<union> spies evsFC5)"
         by (rule pr_key_secrecy)
      }
      ultimately have "Key (sesK (d * e)) \<notin> analz (A \<union> spies evsFC5)" ..
      moreover assume "Key (sesK (d * e)) \<in> analz (A \<union> spies evsFC5)"
      ultimately show ?thesis
       by contradiction
    next
      case False
      hence "User n \<noteq> Spy"
       by simp
      with B have "Passwd n \<notin> analz (A \<union> spies evsFC5)"
       by (rule pr_passwd_secrecy)
      moreover assume "Passwd n \<in> synth (analz (A \<union> spies evsFC5))"
      hence "Passwd n \<in> analz (A \<union> spies evsFC5)"
       by (rule synth_simp_intro, simp)
      ultimately show ?thesis
       by contradiction
    qed
    hence "Crypt (sesK (d * e)) (Passwd n) \<in> parts (A \<union> spies evsFC5)"
     by (rule subsetD [OF analz_parts_subset])
    with A show ?thesis ..
  qed
next
  fix evsFC5 S A U n d e
  assume
    A: "Crypt (sesK (d * e)) (Passwd n) \<in> parts (A \<union> spies evsFC5) \<longrightarrow>
      m' = n" and
    B: "(evsFC5, S, A, U) \<in> protocol" and
    C: "Crypt (sesK (d * e)) (Passwd n) \<in> synth (analz (A \<union> spies evsFC5))" and
    D: "Crypt (sesK (d * e)) (Passwd m') \<in> parts (A \<union> spies evsFC5)"
  show "m' = n"
  proof (rule classical)
    assume E: "m' \<noteq> n"
    have F: "Crypt (sesK (d * e)) (Passwd n) \<in> analz (A \<union> spies evsFC5) \<or>
      Passwd n \<in> synth (analz (A \<union> spies evsFC5)) \<and>
      Key (sesK (d * e)) \<in> analz (A \<union> spies evsFC5)"
     using C by (rule synth_crypt)
    have "Crypt (sesK (d * e)) (Passwd n) \<in> analz (A \<union> spies evsFC5)"
    proof (rule disjE [OF F], assumption, erule conjE, cases "n = 0")
      case True
      hence G: "User m' \<noteq> Spy"
       using E by simp
      have
       "(\<exists>n run. Says n run 5 (User m') (Card n) (Crypt (sesK (d * e)) (Passwd m'))
          \<in> set evsFC5) \<or>
        (\<exists>run. Says m' run 5 Spy (Card m') (Crypt (sesK (d * e)) (Passwd m'))
          \<in> set evsFC5)"
        (is "(\<exists>n run. ?P n run) \<or> (\<exists>run. ?Q run)")
       using B and D by (rule pr_passwd_parts)
      moreover {
        assume "\<exists>n run. ?P n run"
        then obtain n' and run where "?P n' run"
         by blast
        with B and G have "Key (sesK (d * e)) \<notin> analz (A \<union> spies evsFC5)"
         by (rule pr_key_secrecy)
      }
      moreover {
        assume "\<exists>run. ?Q run"
        then obtain run where "?Q run" ..
        with B have "?P m' run"
         by (rule pr_user_authenticity)
        with B and G have "Key (sesK (d * e)) \<notin> analz (A \<union> spies evsFC5)"
         by (rule pr_key_secrecy)
      }
      ultimately have "Key (sesK (d * e)) \<notin> analz (A \<union> spies evsFC5)" ..
      moreover assume "Key (sesK (d * e)) \<in> analz (A \<union> spies evsFC5)"
      ultimately show ?thesis
       by contradiction
    next
      case False
      hence "User n \<noteq> Spy"
       by simp
      with B have "Passwd n \<notin> analz (A \<union> spies evsFC5)"
       by (rule pr_passwd_secrecy)
      moreover assume "Passwd n \<in> synth (analz (A \<union> spies evsFC5))"
      hence "Passwd n \<in> analz (A \<union> spies evsFC5)"
       by (rule synth_simp_intro, simp)
      ultimately show ?thesis
       by contradiction
    qed
    hence "Crypt (sesK (d * e)) (Passwd n) \<in> parts (A \<union> spies evsFC5)"
     by (rule subsetD [OF analz_parts_subset])
    with A show ?thesis ..
  qed
qed

theorem pr_card_authenticity [rule_format]:
 "(evs, S, A, U) \<in> protocol \<Longrightarrow>
    Says n run 5 (User m) (Card n) (Crypt (sesK K) (Passwd m)) \<in> set evs \<longrightarrow>
    Says n run 5 X (User m) (Crypt (sesK K) (Number 0)) \<in> set evs \<longrightarrow>
  n = m \<and>
  (Says m run 5 (Card m) (User m) (Crypt (sesK K) (Number 0)) \<in> set evs \<or>
   Says m run 5 (Card m) Spy (Crypt (sesK K) (Number 0)) \<in> set evs)"
proof (erule protocol.induct, simp_all, (rule_tac [1-2] impI)+, (erule_tac [2] conjE)+,
 (rule_tac [3] impI, rule_tac [3] conjI)+, rule_tac [4] disjI1, rule_tac [5] impI,
 (rule_tac [6] impI)+, simp_all)
  fix evsC5 S A U m n run s a b c f g X'
  assume
    A: "Says n run 5 (User m) (Card n) (Crypt (sesK (c * f)) (Passwd m))
      \<in> set evsC5 \<longrightarrow>
      n = m \<and>
      (Says m run 5 (Card m) (User m) (Crypt (sesK (c * f)) (Number 0))
         \<in> set evsC5 \<or>
       Says m run 5 (Card m) Spy (Crypt (sesK (c * f)) (Number 0))
         \<in> set evsC5)" and
    B: "(evsC5, S, A, U) \<in> protocol" and
    C: "NonceS (S (User m, n, run)) = Some s" and
    D: "IntMapK (S (User m, n, run)) = Some a" and
    E: "ExtMapK (S (User m, n, run)) = Some b" and
    F: "IntAgrK (S (User m, n, run)) = Some c" and
    G: "ExtAgrK (S (User m, n, run)) = Some f" and
    H: "Says n run 4 X' (User m) (Crypt (sesK (c * f))
      \<lbrace>pubAK (c * (s + a * b)), Auth_Data g b, pubAK g,
       Crypt (priSK CA) (Hash (pubAK g))\<rbrace>) \<in> set evsC5" and
    I: "Says n run 5 X (User m) (Crypt (sesK (c * f)) (Number 0)) \<in> set evsC5"
  show "n = m \<and>
    (Says m run 5 (Card m) (User m) (Crypt (sesK (c * f)) (Number 0)) \<in> set evsC5 \<or>
     Says m run 5 (Card m) Spy (Crypt (sesK (c * f)) (Number 0)) \<in> set evsC5)"
  proof (cases "m = 0")
    case True
    hence "Says n run 5 X Spy (Crypt (sesK (c * f)) (Number 0)) \<in> set evsC5"
     using I by simp
    with B have "Says n run 5 Spy (Card n) (Crypt (sesK (c * f)) (Passwd n))
      \<in> set evsC5"
     by (rule pr_confirm_says)
    with B have J: "Says n run 5 (User n) (Card n) (Crypt (sesK (c * f)) (Passwd n))
      \<in> set evsC5"
     by (rule pr_user_authenticity)
    show ?thesis
    proof (cases n)
      case 0
      hence "Says n run 5 (User m) (Card n) (Crypt (sesK (c * f)) (Passwd m))
        \<in> set evsC5"
       using J and True by simp
      with A show ?thesis ..
    next
      case Suc
      hence "User n \<noteq> Spy"
       by simp
      with B have "Key (sesK (c * f)) \<notin> analz (A \<union> spies evsC5)"
       using J by (rule pr_key_secrecy)
      hence "Key (sesK (c * f)) \<notin> A"
       using B by (simp add: pr_key_analz)
      hence "n = m \<and> n = n \<and> run = run"
       by (rule pr_unique_run_8 [OF B J F G])
      hence "Says n run 5 (User m) (Card n) (Crypt (sesK (c * f)) (Passwd m))
        \<in> set evsC5"
       using J by simp
      with A show ?thesis ..
    qed
  next
    case False
    have "Crypt (sesK (c * f)) (Number 0) \<in> spies evsC5"
     using I by (rule set_spies)
    hence "Crypt (sesK (c * f)) (Number 0) \<in> A \<union> spies evsC5" ..
    hence "Crypt (sesK (c * f)) (Number 0) \<in> parts (A \<union> spies evsC5)"
     by (rule parts.Inj)
    moreover have "User m \<noteq> Spy"
     using False by simp
    hence J: "Key (sesK (c * f)) \<notin> A"
     by (rule pr_key_secrecy_aux [OF B _ C D E F G H])
    ultimately have "\<exists>n run X.
      Says n run 5 X (Card n) (Crypt (sesK (c * f)) (Passwd n)) \<in> set evsC5 \<and>
      Says n run 5 (Card n) X (Crypt (sesK (c * f)) (Number 0)) \<in> set evsC5"
     by (rule pr_confirm_parts [OF B])
    then obtain n' and run' and X where
     "Says n' run' 5 X (Card n') (Crypt (sesK (c * f)) (Passwd n')) \<in> set evsC5"
     by blast
    with B have
     "Says n' run' 5 (User n') (Card n') (Crypt (sesK (c * f)) (Passwd n')) \<in> set evsC5"
     by (rule pr_user_authenticity)
    moreover from this have "n' = m \<and> n' = n \<and> run' = run"
     by (rule pr_unique_run_8 [OF B _ F G J])
    ultimately have
     "Says n run 5 (User m) (Card n) (Crypt (sesK (c * f)) (Passwd m)) \<in> set evsC5"
     by auto
    with A show ?thesis ..
  qed
next
  fix evsFC5 S A U run d e
  assume
   "Says 0 run 5 Spy (Card 0) (Crypt (sesK (d * e)) (Passwd 0)) \<in> set evsFC5 \<longrightarrow>
    Says 0 run 5 (Card 0) Spy (Crypt (sesK (d * e)) (Number 0)) \<in> set evsFC5"
  moreover assume
   "(evsFC5, S, A, U) \<in> protocol" and
   "Says 0 run 5 X Spy (Crypt (sesK (d * e)) (Number 0)) \<in> set evsFC5"
  hence "Says 0 run 5 Spy (Card 0) (Crypt (sesK (d * e)) (Passwd 0)) \<in> set evsFC5"
   by (rule pr_confirm_says)
  ultimately show
   "Says 0 run 5 (Card 0) Spy (Crypt (sesK (d * e)) (Number 0)) \<in> set evsFC5" ..
next
  fix evsR5 S A U n run d e X
  assume "(evsR5, S, A, U) \<in> protocol"
  moreover assume "Says n run 5 X (Card n) (Crypt (sesK (d * e)) (Passwd n))
    \<in> set evsR5"
  hence "Crypt (sesK (d * e)) (Passwd n) \<in> spies evsR5"
   by (rule set_spies)
  hence "Crypt (sesK (d * e)) (Passwd n) \<in> A \<union> spies evsR5" ..
  hence "Crypt (sesK (d * e)) (Passwd n) \<in> parts (A \<union> spies evsR5)"
   by (rule parts.Inj)
  moreover assume "Says n run 5 X (Card n) (Crypt (sesK (d * e)) (Passwd m))
    \<in> set evsR5"
  hence "Crypt (sesK (d * e)) (Passwd m) \<in> spies evsR5"
   by (rule set_spies)
  hence "Crypt (sesK (d * e)) (Passwd m) \<in> A \<union> spies evsR5" ..
  hence "Crypt (sesK (d * e)) (Passwd m) \<in> parts (A \<union> spies evsR5)"
   by (rule parts.Inj)
  ultimately show "n = m"
   by (rule pr_unique_passwd_parts)
next
  fix evsR5 S A U n run d e X
  assume "(evsR5, S, A, U) \<in> protocol"
  moreover assume "Says n run 5 X (Card n) (Crypt (sesK (d * e)) (Passwd m))
    \<in> set evsR5"
  hence "Crypt (sesK (d * e)) (Passwd m) \<in> spies evsR5"
   by (rule set_spies)
  hence "Crypt (sesK (d * e)) (Passwd m) \<in> A \<union> spies evsR5" ..
  hence "Crypt (sesK (d * e)) (Passwd m) \<in> parts (A \<union> spies evsR5)"
   by (rule parts.Inj)
  moreover assume "Says n run 5 X (Card n) (Crypt (sesK (d * e)) (Passwd n))
    \<in> set evsR5"
  hence "Crypt (sesK (d * e)) (Passwd n) \<in> spies evsR5"
   by (rule set_spies)
  hence "Crypt (sesK (d * e)) (Passwd n) \<in> A \<union> spies evsR5" ..
  hence "Crypt (sesK (d * e)) (Passwd n) \<in> parts (A \<union> spies evsR5)"
   by (rule parts.Inj)
  ultimately show "m = n"
   by (rule pr_unique_passwd_parts)
next
  fix evsR5 n' run' d e X
  assume "n = m \<and>
    (Says m run 5 (Card m) (User m) (Crypt (sesK K) (Number 0)) \<in> set evsR5 \<or>
     Says m run 5 (Card m) Spy (Crypt (sesK K) (Number 0)) \<in> set evsR5)"
  thus
   "m = n' \<and> run = run' \<and> m = n' \<and> User m = X \<and> sesK K = sesK (d * e) \<or>
    Says m run 5 (Card m) (User m) (Crypt (sesK K) (Number 0)) \<in> set evsR5 \<or>
    m = n' \<and> run = run' \<and> m = n' \<and> Spy = X \<and> sesK K = sesK (d * e) \<or>
    Says m run 5 (Card m) Spy (Crypt (sesK K) (Number 0)) \<in> set evsR5"
   by blast
next
  fix evsFR5 S A U m n run c f
  assume
    A: "(evsFR5, S, A, U) \<in> protocol" and
    B: "0 < m" and
    C: "IntAgrK (S (User m, n, run)) = Some c" and
    D: "ExtAgrK (S (User m, n, run)) = Some f" and
    E: "Crypt (sesK (c * f)) (Number 0) \<in> synth (analz (A \<union> spies evsFR5))" and
    F: "Says n run 5 (User m) (Card n) (Crypt (sesK (c * f)) (Passwd m)) \<in> set evsFR5"
  have "User m \<noteq> Spy"
   using B by simp
  with A have G: "Key (sesK (c * f)) \<notin> analz (A \<union> spies evsFR5)"
   using F by (rule pr_key_secrecy)
  moreover have "Crypt (sesK (c * f)) (Number 0) \<in> analz (A \<union> spies evsFR5) \<or>
    Number 0 \<in> synth (analz (A \<union> spies evsFR5)) \<and>
    Key (sesK (c * f)) \<in> analz (A \<union> spies evsFR5)"
   using E by (rule synth_crypt)
  ultimately have "Crypt (sesK (c * f)) (Number 0) \<in> analz (A \<union> spies evsFR5)"
   by simp
  hence "Crypt (sesK (c * f)) (Number 0) \<in> parts (A \<union> spies evsFR5)"
   by (rule subsetD [OF analz_parts_subset])
  moreover have H: "Key (sesK (c * f)) \<notin> A"
   using A and G by (simp add: pr_key_analz)
  ultimately have "\<exists>n run X.
    Says n run 5 X (Card n) (Crypt (sesK (c * f)) (Passwd n)) \<in> set evsFR5 \<and>
    Says n run 5 (Card n) X (Crypt (sesK (c * f)) (Number 0)) \<in> set evsFR5"
   by (rule pr_confirm_parts [OF A])
  then obtain n' and run' and X where I:
   "Says n' run' 5 X (Card n') (Crypt (sesK (c * f)) (Passwd n')) \<in> set evsFR5 \<and>
    Says n' run' 5 (Card n') X (Crypt (sesK (c * f)) (Number 0)) \<in> set evsFR5"
   by blast
  hence
   "Says n' run' 5 X (Card n') (Crypt (sesK (c * f)) (Passwd n')) \<in> set evsFR5" ..
  with A have J:
   "Says n' run' 5 (User n') (Card n') (Crypt (sesK (c * f)) (Passwd n'))
      \<in> set evsFR5"
   by (rule pr_user_authenticity)
  hence "Crypt (sesK (c * f)) (Passwd n') \<in> spies evsFR5"
   by (rule set_spies)
  hence "Crypt (sesK (c * f)) (Passwd n') \<in> A \<union> spies evsFR5" ..
  hence "Crypt (sesK (c * f)) (Passwd n') \<in> parts (A \<union> spies evsFR5)"
   by (rule parts.Inj)
  moreover have "Crypt (sesK (c * f)) (Passwd m) \<in> spies evsFR5"
   using F by (rule set_spies)
  hence "Crypt (sesK (c * f)) (Passwd m) \<in> A \<union> spies evsFR5" ..
  hence "Crypt (sesK (c * f)) (Passwd m) \<in> parts (A \<union> spies evsFR5)"
   by (rule parts.Inj)
  ultimately have "n' = m"
   by (rule pr_unique_passwd_parts [OF A])
  moreover from this have
   "Says m run' 5 (User m) (Card m) (Crypt (sesK (c * f)) (Passwd m))
      \<in> set evsFR5"
   using J by simp
  hence "m = m \<and> m = n \<and> run' = run"
   by (rule pr_unique_run_8 [OF A _ C D H])
  hence K: "n = m \<and> run' = run"
   by simp
  ultimately have L:
   "Says m run 5 X (Card m) (Crypt (sesK (c * f)) (Passwd m)) \<in> set evsFR5 \<and>
    Says m run 5 (Card m) X (Crypt (sesK (c * f)) (Number 0)) \<in> set evsFR5"
   using I by simp
  moreover from this have
   "Says m run 5 X (Card m) (Crypt (sesK (c * f)) (Passwd m)) \<in> set evsFR5" ..
  with A have "X = User m \<or> X = Spy"
   by (rule pr_passwd_says)
  thus "n = m \<and>
   (Says m run 5 (Card m) (User m) (Crypt (sesK (c * f)) (Number 0)) \<in> set evsFR5 \<or>
    Says m run 5 (Card m) Spy (Crypt (sesK (c * f)) (Number 0)) \<in> set evsFR5)"
   by (rule disjE, insert L, simp_all add: K)
qed

end
