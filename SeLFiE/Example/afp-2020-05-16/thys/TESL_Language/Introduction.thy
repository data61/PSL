chapter\<open>A Gentle Introduction to TESL\<close>

(*<*)
theory Introduction
  imports Main
begin

(*>*)

section \<open>Context\<close>
text\<open>
The design of complex systems involves different formalisms for modeling their different parts or 
aspects. The global model of a system may therefore consist of a coordination of concurrent 
sub-models that use different paradigms such as differential equations, state machines, 
synchronous data-flow networks, 
discrete event models and so on, as illustrated in \autoref{fig:het-timed-system}. 
This raises the interest in architectural composition languages 
that allow for ``bolting the respective sub-models together'', along their various interfaces, and 
specifying the various ways of collaboration and coordination~@{cite "nguyenvan:hal-01583815"}.

We are interested in languages that allow for specifying the timed coordination of subsystems by 
addressing the following conceptual issues:
\<^item> events may occur in different sub-systems at unrelated times, leading to \<^emph>\<open>polychronous\<close> systems, 
  which do not necessarily have a common base clock,
\<^item> the behavior of the sub-systems is observed only at a series of discrete instants, and time 
  coordination has to take this \<^emph>\<open>discretization\<close> into account,
\<^item> the instants at which a system is observed may be arbitrary and should not change its behavior 
  (\<^emph>\<open>stuttering invariance\<close>),
\<^item> coordination between subsystems involves causality, so the occurrence of an event may enforce 
  the occurrence of other events, possibly after a certain duration has elapsed or an event has 
  occurred a given number of times,
\<^item> the domain of time (discrete, rational, continuous. . . ) may be different in the subsystems, 
  leading to \<^emph>\<open>polytimed\<close> systems,
\<^item> the time frames of different sub-systems may be related (for instance, time in a GPS satellite 
  and in a GPS receiver on Earth are related although they are not the same).
\<close>

text\<open>
\begin{figure}[htbp]
 \centering
 \includegraphics{glue.pdf}
 \caption{A Heterogeneous Timed System Model}
 \label{fig:het-timed-system}
\end{figure}\<close>

(*<*)
\<comment> \<open>Constants and notation to be able to write what we want as Isabelle terms, not as LaTeX maths\<close>
consts dummyInfty    :: \<open>'a \<Rightarrow> 'a\<close>
consts dummyTESLSTAR :: \<open>'a\<close>
consts dummyFUN      :: \<open>'a set \<Rightarrow> 'b set \<Rightarrow> 'c set\<close>
consts dummyCLOCK    :: \<open>'a set\<close>
consts dummyBOOL     :: \<open>bool set\<close> 
consts dummyTIMES    :: \<open>'a set\<close> 
consts dummyLEQ      :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>

notation dummyInfty    (\<open>(_\<^sup>\<infinity>)\<close> [1000] 999)
notation dummyTESLSTAR (\<open>TESL\<^sup>*\<close>)
notation dummyFUN      (infixl \<open>\<rightarrow>\<close> 100)
notation dummyCLOCK    (\<open>\<K>\<close>) 
notation dummyBOOL     (\<open>\<bool>\<close>) 
notation dummyTIMES    (\<open>\<T>\<close>) 
notation dummyLEQ      (infixl \<open>\<le>\<^sub>\<T>\<close> 100)
(*>*)

text\<open>
In order to tackle the heterogeneous nature of the subsystems, we abstract their behavior as clocks. 
Each clock models an event, i.e., something that can occur or not at a given time. This time is measured 
in a time frame associated with each clock, and the nature of time (integer, rational, real, or any 
type with a linear order) is specific to each clock. 
When the event associated with a clock occurs, the clock ticks. In order to support any kind of 
behavior for the subsystems, we are only interested in specifying what we can observe at a series 
of discrete instants. There are two constraints on observations: a clock may tick only at an 
observation instant, and the time on any clock cannot decrease from an instant to the next one. 
However, it is always possible to add arbitrary observation instants, which allows for stuttering 
and modular composition of systems. 
As a consequence, the key concept of our setting is the notion of a clock-indexed Kripke model: 
@{term \<open>\<Sigma>\<^sup>\<infinity> = \<nat> \<rightarrow> \<K> \<rightarrow> (\<bool> \<times> \<T>)\<close>}, where @{term \<open>\<K>\<close>} is an enumerable set of clocks, @{term \<open>\<bool>\<close>} 
is the set of booleans – used to  indicate that a clock ticks at a given instant – and @{term \<open>\<T>\<close>} 
is a universal metric time space for which we only assume that it is large enough to contain all 
individual time spaces of clocks and that it is ordered by some linear ordering @{term \<open>(\<le>\<^sub>\<T>)\<close>}.
\<close>

text\<open>
  The elements of @{term \<open>\<Sigma>\<^sup>\<infinity>\<close>} are called runs. A specification language is a set of 
  operators that constrains the set of possible monotonic runs. Specifications are composed by 
  intersecting the denoted run sets of constraint operators.
  Consequently, such specification languages do not limit the number of clocks used to model a 
  system (as long as it is finite) and it is always possible to add clocks to a specification. 
  Moreover, they are \<^emph>\<open>compositional\<close> by construction since the composition of specifications 
  consists of the conjunction of their constraints.
\<close>

text\<open>
  This work provides the following contributions:
  \<^item> defining the non-trivial language @{term \<open>TESL\<^sup>*\<close>} in terms of clock-indexed Kripke models, 
  \<^item> proving that this denotational semantics is stuttering invariant,
  \<^item> defining an adapted form of symbolic primitives and presenting the set of operational 
    semantic rules,
  \<^item> presenting formal proofs for soundness, completeness, and progress of the latter.
\<close>

section\<open>The TESL Language\<close>
   
text\<open>
  The TESL language @{cite "BouJacHarPro2014MEMOCODE"} was initially designed to coordinate the
  execution of heterogeneous components during the simulation of a system. We define here a minimal
  kernel of operators that will form the basis of a family of specification languages, including the
  original TESL language, which is described at \url{http://wdi.supelec.fr/software/TESL/}.
\<close>  

subsection\<open>Instantaneous Causal Operators\<close>
text\<open>
  TESL has operators to deal with instantaneous causality, i.e., to react to an event occurrence
  in the very same observation instant.
  \<^item> \<^verbatim>\<open>c1 implies c2\<close> means that at any instant where \<^verbatim>\<open>c1\<close> ticks, \<^verbatim>\<open>c2\<close> has to tick too.
  \<^item> \<^verbatim>\<open>c1 implies not c2\<close> means that at any instant where \<^verbatim>\<open>c1\<close> ticks, \<^verbatim>\<open>c2\<close> cannot tick.
  \<^item> \<^verbatim>\<open>c1 kills c2\<close> means that at any instant where \<^verbatim>\<open>c1\<close> ticks, and at any future instant, 
    \<^verbatim>\<open>c2\<close> cannot tick.
\<close>

subsection\<open>Temporal Operators\<close>
text\<open>
  TESL also has chronometric temporal operators that deal with dates and chronometric delays.
  \<^item> \<^verbatim>\<open>c sporadic t\<close> means that clock \<^verbatim>\<open>c\<close> must have a tick at time \<^verbatim>\<open>t\<close> on its own time scale.
  \<^item> \<^verbatim>\<open>c1 sporadic t on c2\<close> means that clock \<^verbatim>\<open>c1\<close> must have a tick at an instant where the time 
    on \<^verbatim>\<open>c2\<close> is \<^verbatim>\<open>t\<close>.
  \<^item> \<^verbatim>\<open>c1 time delayed by d on m implies c2\<close> means that every time clock \<^verbatim>\<open>c1\<close> ticks, \<^verbatim>\<open>c2\<close> must have 
    a tick at the first instant where the time on \<^verbatim>\<open>m\<close> is \<^verbatim>\<open>d\<close> later than it was when \<^verbatim>\<open>c1\<close> had ticked.
    This means that every tick on \<^verbatim>\<open>c1\<close> is followed by a tick on \<^verbatim>\<open>c2\<close> after a delay \<^verbatim>\<open>d\<close> measured
    on the time scale of clock \<^verbatim>\<open>m\<close>.
  \<^item> \<^verbatim>\<open>time relation (c1, c2) in R\<close> means that at every instant, the current time on clocks \<^verbatim>\<open>c1\<close>
    and \<^verbatim>\<open>c2\<close> must be in relation \<^verbatim>\<open>R\<close>. By default, the time lines of different clocks are 
    independent. This operator allows us to link two time lines, for instance to model the fact
    that time in a GPS satellite and time in a GPS receiver on Earth are not the same but are 
    related. Time being polymorphic in TESL, this can also be used to model the fact that the
    angular position on the camshaft of an engine moves twice as fast as the angular position 
    on the crankshaft~\<^footnote>\<open>See \url{http://wdi.supelec.fr/software/TESL/GalleryEngine} for more details\<close>. 
    We may consider only linear arithmetic relations to restrict the problem to a domain where 
    the resolution is decidable.\<close>

subsection\<open>Asynchronous Operators\<close>
text\<open>
  The last category of TESL operators allows the specification of asynchronous relations between
  event occurrences. They do not specify the precise instants at which ticks have to occur, 
  they only put bounds on the set of instants at which they should occur.
  \<^item> \<^verbatim>\<open>c1 weakly precedes c2\<close> means that for each tick on \<^verbatim>\<open>c2\<close>, there must be at least one tick
    on \<^verbatim>\<open>c1\<close> at a previous or at the same instant. This can also be expressed by stating
    that at each instant, the number of ticks since the beginning of the run must be lower or 
    equal on \<^verbatim>\<open>c2\<close> than on \<^verbatim>\<open>c1\<close>.
  \<^item> \<^verbatim>\<open>c1 strictly precedes c2\<close> means that for each tick on \<^verbatim>\<open>c2\<close>, there must be at least one tick
    on \<^verbatim>\<open>c1\<close> at a previous instant. This can also be expressed by saying that at each instant, 
    the number of ticks on \<^verbatim>\<open>c2\<close> from the beginning of the run to this instant, must be lower or 
    equal to the number of ticks on \<^verbatim>\<open>c1\<close> from the beginning of the run to the previous instant.
\<close>


(*<*)
no_notation dummyInfty      (\<open>(_\<^sup>\<infinity>)\<close> )
no_notation dummyTESLSTAR   (\<open>TESL\<^sup>*\<close>)
no_notation dummyFUN        (infixl \<open>\<rightarrow>\<close> 100)
no_notation dummyCLOCK      (\<open>\<K>\<close>) 
no_notation dummyBOOL       (\<open>\<bool>\<close>) 
no_notation dummyTIMES      (\<open>\<T>\<close>) 
no_notation dummyLEQ        (infixl \<open>\<le>\<^sub>\<T>\<close> 100)


end
(*>*)
