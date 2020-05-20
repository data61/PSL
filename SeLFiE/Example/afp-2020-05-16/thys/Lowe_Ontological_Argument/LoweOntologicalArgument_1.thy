(*<*)
theory LoweOntologicalArgument_1

imports QML
begin
nitpick_params[box=false, user_axioms=true, show_all, expect=genuine, format = 3,  atoms e = a b c d]
sledgehammer_params[verbose=true]
(*>*)

section \<open>E. J. Lowe's Modal Ontological Argument\<close>

subsection \<open>Introduction\<close>
text\<open>\noindent{E. J. Lowe presented his argument in an article named "A Modal Version of the Ontological Argument",
which has been published as a chapter in \cite{moreland2013}.
The structure of this argument is very representative of philosophical arguments.
It features eight premises from which new inferences are drawn until arriving at a final conclusion:
the necessary existence of God
(which in this case amounts to the existence of some "necessary concrete being").}\<close>

text\<open>\noindent{(P1) God is, by definition, a necessary concrete being.}\<close>
text\<open>\noindent{(P2) Some necessary abstract beings exist.}\<close>
text\<open>\noindent{(P3) All abstract beings are dependent beings.}\<close>
text\<open>\noindent{(P4) All dependent beings depend for their existence on independent beings.}\<close>
text\<open>\noindent{(P5) No contingent being can explain the existence of a necessary being.}\<close>
text\<open>\noindent{(P6) The existence of any dependent being needs to be explained.}\<close>
text\<open>\noindent{(P7) Dependent beings of any kind cannot explain their own existence.}\<close>
text\<open>\noindent{(P8) The existence of dependent beings can only be explained by beings on which they depend
for their existence.}\<close>

text\<open>\noindent{We will consider in our treatment only a representative subset of the conclusions,
as presented in Lowe's article.}\<close>

text\<open>\noindent{(C1) All abstract beings depend for their existence on concrete beings.
(Follows from P3 and P4 together with D3 and D4.)}\<close>
text\<open>\noindent{(C5) In every possible world there exist concrete beings. (Follows from C1 and P2.)}\<close>
text\<open>\noindent{(C7) The existence of necessary abstract beings needs to be explained. (Follows from P2, P3 and P6.)}\<close>
text\<open>\noindent{(C8) The existence of necessary abstract beings can only be explained by concrete beings.
(Follows from C1, P3, P7 and P8.)}\<close>
text\<open>\noindent{(C9) The existence of necessary abstract beings is explained by one or more necessary concrete beings.
(Follows from C7, C8 and P5.)}\<close>
text\<open>\noindent{(C10) A necessary concrete being exists. (Follows from C9.)}\<close>

text\<open>\noindent{Lowe also introduces some informal definitions which should help the reader understand
the meaning of the concepts involved in his argument
(necessity, concreteness, ontological dependence, metaphysical explanation, etc.).
In the following discussion, we will see that most of these definitions do not bear the significance
Lowe claims.}\<close>

text\<open>\noindent{(D1) x is a necessary being := x exists in every possible world.}\<close>
text\<open>\noindent{(D2) x is a contingent being := x exists in some but not every possible world.}\<close>
text\<open>\noindent{(D3) x is a concrete being := x exists in space and time, or at least in time.}\<close>
text\<open>\noindent{(D4) x is an abstract being := x does not exist in space or time.}\<close>
text\<open>\noindent{(D5) x depends for its existence on y := necessarily, x exists only if y exists.}\<close>
text\<open>\noindent{(D6) (For any predicates F and G) F depend for their existence on G := necessarily, Fs exist only if Gs exist.}\<close>

text\<open>\noindent{We will work \emph{iteratively} on Lowe's argument by temporarily fixing truth-values
and inferential relationships among its sentences, and then, after choosing a logic for formalization,
working back and forth on the formalization of its axioms and theorems
by making gradual adjustments while getting automatic real-time feedback about the suitability of our changes,
vis-a-vis the argument's validity.
In this fashion, by engaging in an \emph{iterative} process of trial and error, we work our way
towards a proper understanding
of the concepts involved in the argument, far beyond of what a mere natural-language based discussion would allow.}\<close>
  
subsection \<open>Initial Formalization\<close>
  
text\<open>\noindent{We start our first iterations with a formalized version of Lowe's argument in modal logic using the
semantic embedding presented in the previous section.
We first turn to the formalization of premise P1: "God is, by definition, a necessary concrete being".
In order to understand the concept of \emph{necessariness} (i.e. being a "necessary being")
employed in this argument,
we have a look at the definitions D1 and D2 provided by Lowe.
They relate the concepts of necessariness and contingency (i.e. being a "contingent being") with existence:\footnote{
Here, the concepts of necessariness and contingency are meant as properties of beings, in contrast to the
concepts of necessity and possibility which are modals. We will see later how both pairs of
concepts can be related in order to validate this argument.}}\<close>
  
text\<open>\noindent{(D1) \emph{x is a necessary being := x exists in every possible world.}}\<close>
text\<open>\noindent{(D2) \emph{x is a contingent being := x exists in some but not every possible world.}}\<close>
  
text\<open>\noindent{The two definitions above, aimed at explicating the concepts of necessariness and contingency
by reducing them to existence and quantification over possible worlds,
have a direct impact on the choice of a logic for formalization.
They not only call for some kind of modal logic with possible-world semantics but also lead us to consider
the complex issue of existence, since we need to restrict the domain of quantification at every world.}\<close>
text\<open>\noindent{For this argument not to become trivialized, we guarded our quantifiers so they range only over
those entities existing (i.e. being actualized) at a given world.
This approach is known as \emph{actualist quantification}
and is implemented in our semantic embedding by defining a world-dependent meta-logical `existence' predicate
(called "actualizedAt" below), which is the one used as a guard in the definition of the quantifiers.
Note that the type \emph{e} characterizes the domain of all beings (existing and non-existing), and
the type \emph{wo} (which is an abbreviation for \<open>w\<Rightarrow>bool\<close>) characterizes sets of worlds.
The term "isActualized" thus relates beings to worlds.}\<close>
  
consts isActualized::"e\<Rightarrow>wo" (infix "actualizedAt"(*<*)70(*>*))
  
abbreviation forallAct::"(e\<Rightarrow>wo)\<Rightarrow>wo" ("\<^bold>\<forall>\<^sup>A")
  where "\<^bold>\<forall>\<^sup>A\<Phi> \<equiv> \<lambda>w.\<forall>x. (x actualizedAt w)\<longrightarrow>(\<Phi> x w)"
abbreviation existsAct::"(e\<Rightarrow>wo)\<Rightarrow>wo" ("\<^bold>\<exists>\<^sup>A")
  where "\<^bold>\<exists>\<^sup>A\<Phi> \<equiv> \<lambda>w.\<exists>x. (x actualizedAt w) \<and> (\<Phi> x w)"
    
text\<open>\noindent{We also define the corresponding binder syntax below.}\<close>
abbreviation mforallActB::"(e\<Rightarrow>wo)\<Rightarrow>wo" (binder"\<^bold>\<forall>\<^sup>A"[8]9)
  where "\<^bold>\<forall>\<^sup>Ax. (\<phi> x) \<equiv> \<^bold>\<forall>\<^sup>A\<phi>"
abbreviation mexistsActB::"(e\<Rightarrow>wo)\<Rightarrow>wo" (binder"\<^bold>\<exists>\<^sup>A"[8]9)
  where "\<^bold>\<exists>\<^sup>Ax. (\<phi> x) \<equiv> \<^bold>\<exists>\<^sup>A\<phi>"
    
text\<open>\noindent{We use Isabelle's Nitpick tool @{cite "Nitpick"} to verify that actualist quantification validates
neither the Barcan formula nor its converse.}\<close>
    
lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ax. \<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ax. \<phi> x)\<rfloor>"
  nitpick oops \<comment> \<open>Countermodel found: formula not valid\<close>
lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ax. \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ax. \<^bold>\<box>(\<phi> x))\<rfloor>"
  nitpick oops \<comment> \<open>Countermodel found: formula not valid\<close>
    
text\<open>\noindent{With actualist quantification in place we can:
(i) formalize the concept of existence in the usual form (by using a restricted particular quantifier),
(ii) formalize necessariness as existing necessarily, and
(iii) formalize contingency as existing possibly but not necessarily.
}\<close>

definition Existence::"e\<Rightarrow>wo" ("E!") where "E! x  \<equiv> \<^bold>\<exists>\<^sup>Ay. y \<^bold>\<approx> x"
  
definition Necessary::"e\<Rightarrow>wo" where "Necessary x \<equiv>  \<^bold>\<box>E! x"
definition Contingent::"e\<Rightarrow>wo" where "Contingent x\<equiv> \<^bold>\<diamond>E! x \<^bold>\<and> \<^bold>\<not>Necessary x"

text\<open>\noindent{Note that we have just chosen our logic for formalization: a free quantified modal logic \emph{K}
with positive semantics.
The logic is \emph{free} because the domain of quantification (for actualist quantifiers) is a proper subset of
our universe of discourse, so we can refer to non-actual objects. The semantics is \emph{positive} because
we have placed no restriction regarding predication on non-actual objects, so they are also allowed
to exemplify properties and relations.
We are also in a position to embed stronger normal modal logics (\emph{KB, KB5, S4, S5, ...})
by restricting the accessibility relation \emph{R} with additional axioms.}\<close>
  
text\<open>\noindent{Having chosen our logic, we can now turn to the formalization of the concepts of abstractness and concreteness.
As seen previously, Lowe has already provided us with an explication of these concepts:}\<close> 

text\<open>\noindent{(D3) \emph{x is a concrete being := x exists in space and time, or at least in time.}}\<close>
text\<open>\noindent{(D4) \emph{x is an abstract being := x does not exist in space or time.}}\<close>

text\<open>\noindent{Lowe himself acknowledges that the explication of these concepts in terms of existence
"in space and time" is superfluous, since we are only interested in them being complementary.\footnote{
We quote from Lowe's original article:
"Observe that, according to these definitions, a being cannot be both concrete and abstract:
being concrete and being abstract are mutually exclusive properties of beings.
Also, all beings are either concrete or abstract ... the abstract/concrete distinction is exhaustive.
Consequently, a being is concrete if and only if it is not abstract."}
Thus we start by formalizing concreteness as a \emph{primitive} world-dependent predicate and then derive
abstractness from it, namely as its negation.
}\<close>  
consts Concrete::"e\<Rightarrow>wo"
abbreviation Abstract::"e\<Rightarrow>wo" where "Abstract x \<equiv>  \<^bold>\<not>(Concrete x)"

text\<open>\noindent{We can now formalize the definition of Godlikeness (P1) as follows: }\<close>
abbreviation Godlike::"e\<Rightarrow>wo" where "Godlike x \<equiv> Necessary x \<^bold>\<and> Concrete x"
  
text\<open>\noindent{We also formalize premise P2 ("Some necessary abstract beings exist") as shown below:}\<close>
axiomatization where
P2: "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Necessary x \<^bold>\<and> Abstract x\<rfloor>" (* Some necessary abstract beings exist.*)  
  
text\<open>\noindent{Let's now turn to premises P3 ("All abstract beings are dependent beings") and P4
("All dependent beings depend for their existence on independent beings").
We have here three new concepts to be explicated: two predicates "dependent" and "independent"
and a relation "depends (for its existence) on", which has been called
\emph{ontological dependence} by Lowe.
Following our linguistic intuitions concerning their interrelation, we start by proposing
the following formalization:}\<close>
  
consts dependence::"e\<Rightarrow>e\<Rightarrow>wo" (infix "dependsOn"(*<*)100(*>*))
definition Dependent::"e\<Rightarrow>wo" where "Dependent x \<equiv> \<^bold>\<exists>\<^sup>Ay. x dependsOn y"
abbreviation Independent::"e\<Rightarrow>wo" where "Independent x  \<equiv> \<^bold>\<not>(Dependent x)"
  
text\<open>\noindent{We have formalized ontological dependence as a \emph{primitive} world-dependent relation
and refrained from any explication (as suggested by Lowe).\footnote{
An explication of this concept has been suggested by Lowe in definition D5
("x depends for its existence on y := necessarily, x exists only if y exists").
Concerning this alleged definition, he has written in a footnote to the same article:
"Note, however, that the two definitions (D5) and (D6) presented below are not in fact formally called upon in the
version of the ontological argument that I am now developing, so that in the remainder of
this chapter the notion of existential dependence may, for all intents and purposes, be taken
as primitive. There is an advantage in this, inasmuch as finding a perfectly apt definition of
existential dependence is no easy task, as I explain in `Ontological Dependence.'"
Lowe refers hereby to his article on ontological dependence in the Stanford Encyclopedia of Philosophy
@{cite "sep-dependence-ontological"} for further discussion.}

We have called an entity \emph{dependent} if and only if there \emph{actually exists} an object y such that
x \emph{depends for its existence} on it;
accordingly, we have called an entity \emph{independent} if and only if it is not dependent.}\<close>

text\<open>\noindent{As a consequence, premises P3 ("All abstract beings are dependent beings") and P4
("All dependent beings depend for their existence on independent beings") become formalized as follows.}\<close>
  
axiomatization where
P3: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Abstract x \<^bold>\<rightarrow> Dependent x\<rfloor>" and (* All abstract beings are dependent beings.*)
P4: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Dependent x \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>Ay. Independent y \<^bold>\<and> x dependsOn y)\<rfloor>" (* All dependent beings depend for their existence on independent beings.*)

text\<open>\noindent{Concerning premises P5 ("No contingent being can explain the existence of a necessary being") and
P6 ("The existence of any dependent being needs to be explained"), a suitable formalization
for expressions of the form: "the entity X explains the existence of Y" and
"the existence of X is explained" needs to be found.
These expressions rely on a single binary relation, which will initially be taken as \emph{primitive}.
This relation has been called \emph{metaphysical explanation} by Lowe.}\<close>
    
consts explanation::"e\<Rightarrow>e\<Rightarrow>wo" (infix "explains"(*<*)100(*>*))
definition Explained::"e\<Rightarrow>wo" where "Explained x \<equiv> \<^bold>\<exists>\<^sup>Ay. y explains x"

axiomatization where
P5: "\<lfloor>\<^bold>\<not>(\<^bold>\<exists>\<^sup>Ax. \<^bold>\<exists>\<^sup>Ay. Contingent y \<^bold>\<and> Necessary x \<^bold>\<and> y explains x)\<rfloor>" (* No contingent being can explain the existence of a necessary being. *) 

text\<open>\noindent{Premise P6, together with the last two premises: P7
("Dependent beings of any kind cannot explain their own existence") and
P8 ("The existence of dependent beings can only be explained by beings on which they depend for their existence"),
were introduced by Lowe in order to relate the concept of \emph{metaphysical explanation}
to \emph{ontological dependence}.\footnote{Note that we use non-guarded quantifiers for the formalization of
the last three premises in order to test argument's validity under the strongest assumptions.
As before, we turn a blind eye to modal expressions like "can", "needs to", etc.}}\<close>  

axiomatization where
P6: "\<lfloor>\<^bold>\<forall>x. Dependent x \<^bold>\<rightarrow> Explained x\<rfloor>" and (* The existence of any dependent being needs to be explained. *)
P7: "\<lfloor>\<^bold>\<forall>x. Dependent x \<^bold>\<rightarrow> \<^bold>\<not>(x explains x)\<rfloor>" and (* Dependent beings of any kind cannot explain their own existence. *)
P8: "\<lfloor>\<^bold>\<forall>x y. y explains x \<^bold>\<rightarrow> x dependsOn y\<rfloor>" (* The existence of dependent beings can only be explained by beings on which they depend for their existence. *)

text\<open>\noindent{Although the last three premises seem to couple very tightly the concepts of (metaphysical) explanation
and (ontological) dependence, both concepts are not meant by Lowe to be equivalent.\footnote{
Lowe says: "Existence-explanation is not simply the inverse of existential dependence.
If x depends for its existence on y, this only means that x cannot exist without y
existing. This is not at all the same as saying that x exists because y exists, or that
x exists in virtue of the fact that y exists."}
We have used Nitpick in order to test this claim. Since a countermodel has been found, we have proven
that the (inverse) equivalence of metaphysical explanation and ontological dependence
is not implied by the axioms.}\<close>
lemma "\<lfloor>\<^bold>\<forall>x y. x explains y \<^bold>\<leftrightarrow> y dependsOn x\<rfloor>" nitpick[user_axioms] oops
    
text\<open>\noindent{For any being, however, having its existence "explained"
is equivalent to its existence being "dependent" (on some other being).
This follows already from premises P6 and P8, as shown above by Isabelle's prover.}\<close>
lemma "\<lfloor>\<^bold>\<forall>x. Explained x \<^bold>\<leftrightarrow> Dependent x\<rfloor>"
  using P6 P8 Dependent_def Explained_def by auto
                                
        
text\<open>\noindent{The Nitpick model finder is also useful to check axioms' consistency at any stage during the
formalization of an argument.
We instruct Nitpick to generate a model satisfying some tautological sentence
(here we use a trivial `True' proposition) while taking into account all previously defined axioms.}\<close>
lemma True nitpick[satisfy, user_axioms] oops
    
text\<open>\noindent{In this case, Nitpick was able to find a model satisfying the given tautology; this means that
all axioms defined so far are consistent. The model found has a cardinality of two for the set of
individual objects and a single world.}\<close>

text\<open>\noindent{We can also use model finders to perform `sanity checks'. We can instruct Nitpick
to find a countermodel for some specifically tailored formula which we want to make sure is not valid.
We check below, for instance, that our axioms are not too strong as to imply \emph{metaphysical necessitism}
(i.e. all beings necessarily exist)
or \emph{modal collapse}. Since both would trivially validate the argument.}\<close>
    
lemma "\<lfloor>\<^bold>\<forall>x. E! x\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found: necessitism is not valid\<close>
    
lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found: modal collapse is not valid\<close>
    
text\<open>\noindent{By using Isabelle's \emph{Sledgehammer} tool @{cite "Sledgehammer"}, we can verify the validity
of the selected conclusions C1, C5 and C7, and even find the premises they rely upon.}\<close>
    
text\<open>\noindent{(C1) \emph{All abstract beings depend for their existence on concrete beings.}}\<close>
theorem C1:  "\<lfloor>\<^bold>\<forall>\<^sup>Ax. Abstract x \<^bold>\<rightarrow> (\<^bold>\<exists>y. Concrete y \<^bold>\<and> x dependsOn y)\<rfloor>"
  using P3 P4 by blast
text\<open>\noindent{(C5) \emph{In every possible world there exist concrete beings.} }\<close>    
theorem C5: "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Concrete x\<rfloor>"
  using P2 P3 P4 by blast
text\<open>\noindent{(C7) \emph{The existence of necessary abstract beings needs to be explained.}}\<close>   
theorem C7: "\<lfloor>\<^bold>\<forall>\<^sup>Ax. (Necessary x \<^bold>\<and> Abstract x) \<^bold>\<rightarrow> Explained x\<rfloor>"
  using P3 P6 by simp
    
text\<open>\noindent{The last three conclusions are shown by Nitpick to be non-valid even in an \emph{S5} logic.
\emph{S5} can be easily introduced by postulating that the accessibility relation \emph{R} is an equivalence relation.
This exploits the well-known \emph{Sahlqvist correspondence} which links modal axioms to constraints
on a model's accessibility relation.}\<close>

axiomatization where
  S5: "equivalence R" \<comment> \<open>@{text "\<box>\<phi>\<rightarrow>\<phi>, \<phi>\<rightarrow>\<box>\<diamond>\<phi> and \<box>\<phi>\<rightarrow>\<box>\<box>\<phi>"}\<close>
    
text\<open>\noindent{(C8) \emph{The existence  of  necessary  abstract  beings  can  only  be  explained  by  concrete  beings.} }\<close>
lemma C8: "\<lfloor>\<^bold>\<forall>\<^sup>Ax.(Necessary x \<^bold>\<and> Abstract x)\<^bold>\<rightarrow>(\<^bold>\<forall>\<^sup>Ay. y explains x\<^bold>\<rightarrow>Concrete y)\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found\<close>
text\<open>\noindent{(C9) \emph{The existence of necessary abstract beings is explained by one or more necessary concrete (Godlike) beings.} }\<close>
lemma C9: "\<lfloor>\<^bold>\<forall>\<^sup>Ax.(Necessary x \<^bold>\<and> Abstract x)\<^bold>\<rightarrow>(\<^bold>\<exists>\<^sup>Ay. y explains x \<^bold>\<and> Godlike y)\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found\<close>
text\<open>\noindent{(C10) \emph{A necessary concrete (Godlike) being exists.} }\<close>
theorem C10:  "\<lfloor>\<^bold>\<exists>\<^sup>Ax. Godlike x\<rfloor>"
  nitpick[user_axioms] oops \<comment> \<open>Countermodel found\<close>

text\<open>\noindent{By employing the Isabelle proof assistant we prove non-valid a first formalization attempt of
Lowe's modal ontological argument. This is, however, just the first of many iterations in our
interpretive endeavor. Based on the information recollected so far, we can proceed to make the adjustments
necessary to validate the argument. We will see how these changes have an impact on our understanding of
all concepts (necessariness, concreteness, dependence, explanation, etc.).
}\<close>
    
(*<*)    
end
(*>*)
