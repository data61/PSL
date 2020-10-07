(*<*)
theory IHOML
imports Relations
begin  
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3, atoms e = a b c d]
(*>*)
  
section \<open>Introduction\<close>

text\<open>  We present a study on Computational Metaphysics: a computer-formalisation and verification
of Fitting's variant of the ontological argument (for the existence of God) as presented in
his textbook \emph{Types, Tableaus and G\"odel's God} @{cite "Fitting"}. Fitting's argument 
is an emendation of Kurt G\"odel's modern variant @{cite "GoedelNotes"} (resp. Dana Scott's 
variant @{cite "ScottNotes"}) of the ontological argument. \<close>

text\<open> The motivation is to avoid the \emph{modal collapse} @{cite Sobel and sobel2004logic}, which has been criticised
as an undesirable side-effect of the axioms of G\"odel resp. Scott. The modal collapse essentially  
states that  there are no contingent truths and that everything is determined.
Several authors (e.g. @{cite "anderson90:_some_emend_of_goedel_ontol_proof" and "AndersonGettings" and "Hajek2002" and "bjordal99"}) 
have proposed emendations of the argument with the aim of maintaining the essential result 
(the necessary existence of God) while at the same time avoiding the modal collapse. 
Related work  has formalised several of these variants on the computer and verified or falsified them. For example,
G\"odel's axioms @{cite "GoedelNotes"} have been shown inconsistent @{cite C55 and C60}
while Scott's version has been verified @{cite "ECAI"}. Further experiments, contributing amongst others
to the clarification of a related debate between H\'ajek and Anderson, are presented and discussed in
@{cite "J23"}. The enabling technique in all of these experiments has been
shallow semantical embeddings of (extensional) higher-order modal logics in classical higher-order
logic (see @{cite J23 and R59} and the references therein). \<close>

text\<open> Fitting's emendation also intends to avoid the modal collapse. However, in contrast to the above variants, Fitting's
solution is based on the use of an intensional as opposed to an extensional higher-order modal logic.
For our work this imposed the additional challenge to provide a shallow embedding of this more advanced
logic. The experiments presented below confirm that Fitting's argument as presented in his textbook @{cite "Fitting"}
is valid and that it avoids the modal collapse as intended. \<close>

text\<open> The work presented here originates from the \emph{Computational Metaphysics} lecture course  
held at FU Berlin in Summer 2016 @{cite "C65"}. \pagebreak \<close>


section \<open>Embedding of Intensional Higher-Order Modal Logic\<close>
  
text\<open>  The object logic being embedded, intensional higher-order modal logic (IHOML), is a modification of the intentional logic developed by Montague
and Gallin @{cite "Gallin75"}. IHOML is introduced by Fitting in the second part of his textbook @{cite "Fitting"}
in order to formalise his emendation of G\"odel's ontological argument. We offer here a shallow embedding
of this logic in Isabelle/HOL, which has been inspired by previous work on the semantical embedding of
multimodal logics with quantification @{cite "J23"}. We expand this approach to allow for actualist quantifiers,
intensional types and their related operations. \<close>

subsection \<open>Type Declarations\<close>
  
text\<open>  Since IHOML and Isabelle/HOL are both typed languages, we introduce a type-mapping between them.
We follow as closely as possible the syntax given by Fitting (see p. 86). According to this syntax,
if \<open>\<tau>\<close> is an extensional type, \<open>\<up>\<tau>\<close> is the corresponding intensional type. For instance,
a set of (red) objects has the extensional type \<open>\<langle>\<zero>\<rangle>\<close>, whereas the concept `red' has intensional type \<open>\<up>\<langle>\<zero>\<rangle>\<close>.
In what follows, terms having extensional (intensional) types will be called extensional (intensional) terms. \<close>

  typedecl i                    \<comment> \<open>type for possible worlds\<close>
  type_synonym io = "(i\<Rightarrow>bool)" \<comment> \<open>formulas with world-dependent truth-value\<close>
  typedecl e  ("\<zero>")             \<comment> \<open>individuals\<close>             
  
  text\<open>  Aliases for common unary predicate types:  \<close>
  type_synonym ie =     "(i\<Rightarrow>\<zero>)"             ("\<up>\<zero>")
  type_synonym se =     "(\<zero>\<Rightarrow>bool)"          ("\<langle>\<zero>\<rangle>")
  type_synonym ise =    "(\<zero>\<Rightarrow>io)"           ("\<up>\<langle>\<zero>\<rangle>")
  type_synonym sie =    "(\<up>\<zero>\<Rightarrow>bool)"        ("\<langle>\<up>\<zero>\<rangle>")
  type_synonym isie =   "(\<up>\<zero>\<Rightarrow>io)"         ("\<up>\<langle>\<up>\<zero>\<rangle>")  
  type_synonym sise =   "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>bool)"     ("\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym isise =  "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>io)"      ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym sisise=  "(\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>bool)" ("\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
  type_synonym isisise= "(\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>io)"  ("\<up>\<langle>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
  type_synonym sse =    "\<langle>\<zero>\<rangle>\<Rightarrow>bool"         ("\<langle>\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym isse =   "\<langle>\<zero>\<rangle>\<Rightarrow>io"          ("\<up>\<langle>\<langle>\<zero>\<rangle>\<rangle>")
  
  text\<open>  Aliases for common binary relation types:  \<close>
  type_synonym see =        "(\<zero>\<Rightarrow>\<zero>\<Rightarrow>bool)"          ("\<langle>\<zero>,\<zero>\<rangle>")
  type_synonym isee =       "(\<zero>\<Rightarrow>\<zero>\<Rightarrow>io)"           ("\<up>\<langle>\<zero>,\<zero>\<rangle>")
  type_synonym sieie =      "(\<up>\<zero>\<Rightarrow>\<up>\<zero>\<Rightarrow>bool)"       ("\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>")
  type_synonym isieie =     "(\<up>\<zero>\<Rightarrow>\<up>\<zero>\<Rightarrow>io)"        ("\<up>\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>")
  type_synonym ssese =      "(\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>\<Rightarrow>bool)"     ("\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym issese =     "(\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>\<Rightarrow>io)"      ("\<up>\<langle>\<langle>\<zero>\<rangle>,\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym ssee =       "(\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>bool)"       ("\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>")
  type_synonym issee =      "(\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>io)"        ("\<up>\<langle>\<langle>\<zero>\<rangle>,\<zero>\<rangle>")
  type_synonym isisee =     "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<zero>\<Rightarrow>io)"      ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<zero>\<rangle>")
  type_synonym isiseise =   "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>\<Rightarrow>io)"    ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<zero>\<rangle>\<rangle>")
  type_synonym isiseisise=  "(\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<Rightarrow>io)" ("\<up>\<langle>\<up>\<langle>\<zero>\<rangle>,\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>\<rangle>")
  
subsection \<open>Definitions\<close>
  
subsubsection \<open>Logical Operators as Truth-Sets\<close>    

  abbreviation mnot   :: "io\<Rightarrow>io" ("\<^bold>\<not>_"[52]53)
    where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
  abbreviation negpred :: "\<langle>\<zero>\<rangle>\<Rightarrow>\<langle>\<zero>\<rangle>" ("\<rightharpoondown>_"[52]53) 
    where "\<rightharpoondown>\<Phi> \<equiv> \<lambda>x. \<not>(\<Phi> x)" 
  abbreviation mnegpred :: "\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<langle>\<zero>\<rangle>" ("\<^bold>\<rightharpoondown>_"[52]53) 
    where "\<^bold>\<rightharpoondown>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>(\<Phi> x w)"
  abbreviation mand   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<and>"51)
    where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<and>(\<psi> w)"   
  abbreviation mor    :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<or>"50)
    where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<or>(\<psi> w)"
  abbreviation mimp   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<rightarrow>"49) 
    where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longrightarrow>(\<psi> w)"  
  abbreviation mequ   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<leftrightarrow>"48)
    where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<longleftrightarrow>(\<psi> w)"
  abbreviation xor:: "bool\<Rightarrow>bool\<Rightarrow>bool" (infixr"\<oplus>"50)
    where "\<phi>\<oplus>\<psi> \<equiv>  (\<phi>\<or>\<psi>) \<and> \<not>(\<phi>\<and>\<psi>)" 
  abbreviation mxor   :: "io\<Rightarrow>io\<Rightarrow>io" (infixr"\<^bold>\<oplus>"50)
    where "\<phi>\<^bold>\<oplus>\<psi> \<equiv> \<lambda>w. (\<phi> w)\<oplus>(\<psi> w)"
      
subsubsection \<open>Possibilist Quantification\<close>
    
  abbreviation mforall   :: "('t\<Rightarrow>io)\<Rightarrow>io" ("\<^bold>\<forall>")      
    where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. (\<Phi> x w)"
  abbreviation mexists   :: "('t\<Rightarrow>io)\<Rightarrow>io" ("\<^bold>\<exists>") 
    where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. (\<Phi> x w)"
    
  abbreviation mforallB  :: "('t\<Rightarrow>io)\<Rightarrow>io" (binder"\<^bold>\<forall>"[8]9) \<comment> \<open>Binder notation\<close>
    where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"  
  abbreviation mexistsB  :: "('t\<Rightarrow>io)\<Rightarrow>io" (binder"\<^bold>\<exists>"[8]9)
    where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>" 
      
subsubsection \<open>Actualist Quantification\<close>
  
text\<open>  The following predicate is used to model actualist quantifiers by restricting the domain of quantification at every possible world.
This standard technique has been referred to as \emph{existence relativization} (@{cite "fitting98"}, p. 106),
highlighting the fact that this predicate can be seen as a kind of meta-logical `existence predicate' telling us
which individuals \emph{actually} exist at a given world. This meta-logical concept does not appear in our object language. \<close>
  consts Exists::"\<up>\<langle>\<zero>\<rangle>" ("existsAt")  

  abbreviation mforallAct   :: "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<^bold>\<forall>\<^sup>E")    
    where "\<^bold>\<forall>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<forall>x. (existsAt x w)\<longrightarrow>(\<Phi> x w)"
  abbreviation mexistsAct   :: "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" ("\<^bold>\<exists>\<^sup>E") 
    where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x. (existsAt x w) \<and> (\<Phi> x w)"

  abbreviation mforallActB  :: "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" (binder"\<^bold>\<forall>\<^sup>E"[8]9) \<comment> \<open>binder notation\<close>
    where "\<^bold>\<forall>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<forall>\<^sup>E\<phi>"     
  abbreviation mexistsActB  :: "\<up>\<langle>\<up>\<langle>\<zero>\<rangle>\<rangle>" (binder"\<^bold>\<exists>\<^sup>E"[8]9)
    where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"
      
subsubsection \<open>Modal Operators\<close>
  
   consts aRel::"i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70)  \<comment> \<open>accessibility relation \emph{r}\<close>
  
  abbreviation mbox   :: "io\<Rightarrow>io" ("\<^bold>\<box>_"[52]53)
    where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. (w r v)\<longrightarrow>(\<phi> v)"
  abbreviation mdia   :: "io\<Rightarrow>io" ("\<^bold>\<diamond>_"[52]53)
    where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. (w r v)\<and>(\<phi> v)"

subsubsection \<open>\emph{Extension-of} Operator\<close>
text\<open> According to Fitting's semantics (@{cite "Fitting"}, pp. 92-4) \<open>\<down>\<close> is an unary operator applying only to 
 intensional terms. A term of the form \<open>\<down>\<alpha>\<close> designates the extension of the intensional object designated by 
 \<open>\<alpha>\<close>, at some \emph{given} world. For instance, suppose we take possible worlds as persons,
 we can therefore think of the concept `red' as a function that maps each person to the set of objects that person
 classifies as red (its extension). We can further state, the intensional term \emph{r} of type \<open>\<up>\<langle>\<zero>\<rangle>\<close> designates the concept `red'.
 As can be seen, intensional terms in IHOML designate functions on possible worlds and they always do it \emph{rigidly}. 
 We will sometimes refer to an intensional object explicitly as `rigid', implying that its (rigidly) designated function has
 the same extension in all possible worlds. \<close>

text\<open>  Terms of the form \<open>\<down>\<alpha>\<close> are called \emph{relativized} (extensional) terms; they are always derived
from intensional terms and their type is \emph{extensional} (in the color example \<open>\<down>r\<close> would be of type \<open>\<langle>\<zero>\<rangle>\<close>).
Relativized terms may vary their denotation from world to world of a model, because the extension of an intensional term can change
from world to world, i.e. they are non-rigid. \<close>
text\<open> To recap: an intensional term denotes the same function in all worlds (i.e. it's rigid), whereas a relativized term
denotes a (possibly) different extension (an object or a set) at every world (i.e. it's non-rigid). To find out
the denotation of a relativized term, a world must be given. Relativized terms are the \emph{only} non-rigid terms.
\bigbreak \<close>
text\<open>  For our Isabelle/HOL embedding, we had to follow a slightly different approach; we model \<open>\<down>\<close>
as a predicate applying to formulas of the form \<open>\<Phi>(\<down>\<alpha>\<^sub>1,\<dots>\<alpha>\<^sub>n)\<close> (for our treatment
we only need to consider cases involving one or two arguments, the first one being a relativized term).
For instance, the formula \<open>Q(\<down>a\<^sub>1)\<^sup>w\<close> (evaluated at world \emph{w}) is modelled as \<open>\<downharpoonleft>(Q,a\<^sub>1)\<^sup>w\<close>
(or \<open>(Q \<downharpoonleft> a\<^sub>1)\<^sup>w\<close> using infix notation), which gets further translated into \<open>Q(a\<^sub>1(w))\<^sup>w\<close>.

Depending on the particular types involved, we have to define \<open>\<down>\<close> differently to ensure type correctness
(see \emph{a-d} below). Nevertheless, the essence of the \emph{Extension-of} operator remains the same:
a term \<open>\<alpha>\<close> preceded by \<open>\<down>\<close> behaves as a non-rigid term, whose denotation at a given possible world corresponds
to the extension of the original intensional term \<open>\<alpha>\<close> at that world. \<close>

text\<open>  (\emph{a}) Predicate \<open>\<phi>\<close> takes as argument a relativized term derived from an (intensional) individual of type \<open>\<up>\<zero>\<close>: \<close>
abbreviation extIndivArg::"\<up>\<langle>\<zero>\<rangle>\<Rightarrow>\<up>\<zero>\<Rightarrow>io" (infix "\<downharpoonleft>" 60)                           
  where "\<phi> \<downharpoonleft>c \<equiv> \<lambda>w. \<phi> (c w) w"
text\<open>  (\emph{b}) A variant of (\emph{a}) for terms derived from predicates (types of form \<open>\<up>\<langle>t\<rangle>\<close>): \<close>
abbreviation extPredArg::"(('t\<Rightarrow>bool)\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>io" (infix "\<down>" 60)
  where "\<phi> \<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. P x w) w"
text\<open>  (\emph{c}) A variant of (\emph{b}) with a second argument (the first one being relativized): \<close>
abbreviation extPredArg1::"(('t\<Rightarrow>bool)\<Rightarrow>'b\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>'b\<Rightarrow>io" (infix "\<down>\<^sub>1" 60)
  where "\<phi> \<down>\<^sub>1P \<equiv> \<lambda>z. \<lambda>w. \<phi> (\<lambda>x. P x w) z w"
    
text\<open> In what follows, the `\<open>\<lparr>_\<rparr>\<close>' parentheses are an operator used to convert extensional objects into `rigid' intensional ones: \<close>  
abbreviation trivialConversion::"bool\<Rightarrow>io" ("\<lparr>_\<rparr>") where "\<lparr>\<phi>\<rparr> \<equiv> (\<lambda>w. \<phi>)"  
text\<open>  (\emph{d}) A variant of (\emph{b}) where \<open>\<phi>\<close> takes `rigid' intensional terms as argument: \<close>
abbreviation mextPredArg::"(('t\<Rightarrow>io)\<Rightarrow>io)\<Rightarrow>('t\<Rightarrow>io)\<Rightarrow>io" (infix "\<^bold>\<down>" 60)
  where "\<phi> \<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x. \<lparr>P x w\<rparr>) w" (* where "\<phi> \<^bold>\<down>P \<equiv> \<lambda>w. \<phi> (\<lambda>x u. P x w) w"*)
    
subsubsection \<open>Equality\<close>
  
  abbreviation meq    :: "'t\<Rightarrow>'t\<Rightarrow>io" (infix"\<^bold>\<approx>"60) \<comment> \<open>normal equality (for all types)\<close>
    where "x \<^bold>\<approx> y \<equiv> \<lambda>w. x = y"
  abbreviation meqC   :: "\<up>\<langle>\<up>\<zero>,\<up>\<zero>\<rangle>" (infixr"\<^bold>\<approx>\<^sup>C"52) \<comment> \<open>eq. for individual concepts\<close>
    where "x \<^bold>\<approx>\<^sup>C y \<equiv> \<lambda>w. \<forall>v. (x v) = (y v)"
  abbreviation meqL   :: "\<up>\<langle>\<zero>,\<zero>\<rangle>" (infixr"\<^bold>\<approx>\<^sup>L"52) \<comment> \<open>Leibniz eq. for individuals\<close>
    where "x \<^bold>\<approx>\<^sup>L y \<equiv> \<^bold>\<forall>\<phi>. \<phi>(x)\<^bold>\<rightarrow>\<phi>(y)"

subsubsection \<open>Meta-logical Predicates\<close>

 abbreviation valid :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>" [8]) where "\<lfloor>\<psi>\<rfloor> \<equiv>  \<forall>w.(\<psi> w)"
 abbreviation satisfiable :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>s\<^sup>a\<^sup>t" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<equiv> \<exists>w.(\<psi> w)"
 abbreviation countersat :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t \<equiv>  \<exists>w.\<not>(\<psi> w)"
 abbreviation invalid :: "io\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>i\<^sup>n\<^sup>v" [8]) where "\<lfloor>\<psi>\<rfloor>\<^sup>i\<^sup>n\<^sup>v \<equiv> \<forall>w.\<not>(\<psi> w)"

subsection \<open>Verifying the Embedding\<close>
   
text\<open>  The above definitions introduce modal logic \emph{K} with possibilist and actualist quantifiers,
as evidenced by the following tests: \<close>

 text\<open>  Verifying \emph{K} Principle and Necessitation:  \<close>
 lemma K: "\<lfloor>(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)\<rfloor>" by simp    \<comment> \<open>\emph{K} schema\<close>
 lemma NEC: "\<lfloor>\<phi>\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" by simp    \<comment> \<open>necessitation\<close>
    
 text\<open>  Local consequence implies global consequence (we will use this lemma often): \<close>
 lemma localImpGlobalCons: "\<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor>" by simp
    
 text\<open>  But global consequence does not imply local consequence: \<close>
 lemma "\<lfloor>\<phi>\<rfloor> \<longrightarrow> \<lfloor>\<xi>\<rfloor> \<Longrightarrow> \<lfloor>\<phi> \<^bold>\<rightarrow> \<xi>\<rfloor>" nitpick oops \<comment> \<open>countersatisfiable\<close>

 text\<open>  Barcan and Converse Barcan Formulas are satisfied for standard (possibilist) quantifiers:  \<close>
 lemma "\<lfloor>(\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x))\<rfloor>" by simp
 lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>x.\<^bold>\<box>(\<phi> x))\<rfloor>" by simp
    
 text\<open>  (Converse) Barcan Formulas not satisfied for actualist quantifiers:  \<close>
 lemma "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x))\<rfloor>" nitpick oops \<comment> \<open>countersatisfiable\<close>
 lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ex.\<^bold>\<box>(\<phi> x))\<rfloor>" nitpick oops \<comment> \<open>countersatisfiable\<close>
    
text\<open>  Above we have made use of (counter-)model finder \emph{Nitpick} @{cite "Nitpick"} for the first time.  
For all the conjectured lemmas above, \emph{Nitpick} has found a countermodel, i.e. a model satisfying all 
the axioms which falsifies the given formula. This means, the formulas are not valid. \<close>   
 
 text\<open>  Well known relations between meta-logical notions:  \<close>
 lemma  "\<lfloor>\<phi>\<rfloor> \<longleftrightarrow> \<not>\<lfloor>\<phi>\<rfloor>\<^sup>c\<^sup>s\<^sup>a\<^sup>t" by simp
 lemma  "\<lfloor>\<phi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<longleftrightarrow> \<not>\<lfloor>\<phi>\<rfloor>\<^sup>i\<^sup>n\<^sup>v " by simp
 
 text\<open>  Contingent truth does not allow for necessitation:  \<close>
 lemma "\<lfloor>\<^bold>\<diamond>\<phi>\<rfloor>  \<longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" nitpick oops            \<comment> \<open>countersatisfiable\<close>
 lemma "\<lfloor>\<^bold>\<box>\<phi>\<rfloor>\<^sup>s\<^sup>a\<^sup>t \<longrightarrow> \<lfloor>\<^bold>\<box>\<phi>\<rfloor>" nitpick oops           \<comment> \<open>countersatisfiable\<close>

 text\<open>  \emph{Modal collapse} is countersatisfiable:  \<close>
 lemma "\<lfloor>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>\<rfloor>" nitpick oops                  \<comment> \<open>countersatisfiable\<close>
text\<open> \pagebreak \<close>
subsection \<open>Useful Definitions for Axiomatization of Further Logics\<close>

 text\<open>  The best known normal logics (\emph{K4, K5, KB, K45, KB5, D, D4, D5, D45, ...}) can be obtained by
 combinations of the following axioms:  \<close>

  abbreviation M 
    where "M \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>"
  abbreviation B 
    where "B \<equiv> \<^bold>\<forall>\<phi>. \<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  abbreviation D 
    where "D \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi>"
  abbreviation IV 
    where "IV \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow>  \<^bold>\<box>\<^bold>\<box>\<phi>"
  abbreviation V 
    where "V \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>"
  
  text\<open>  Instead of postulating (combinations of) the above  axioms we instead make use of 
  the well-known \emph{Sahlqvist correspondence}, which links axioms to constraints on a model's accessibility
  relation (e.g. reflexive, symmetric, etc.; the definitions of which are not shown here). We show
  that  reflexivity, symmetry, seriality, transitivity and euclideanness imply
  axioms $M, B, D, IV, V$ respectively. \<close>

  lemma "reflexive aRel  \<Longrightarrow>  \<lfloor>M\<rfloor>" by blast \<comment> \<open>aka T\<close>
  lemma "symmetric aRel \<Longrightarrow> \<lfloor>B\<rfloor>" by blast
  lemma "serial aRel  \<Longrightarrow> \<lfloor>D\<rfloor>" by blast         
  lemma "transitive aRel  \<Longrightarrow> \<lfloor>IV\<rfloor>" by blast   
  lemma "euclidean aRel \<Longrightarrow> \<lfloor>V\<rfloor>" by blast         
  lemma "preorder aRel \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>IV\<rfloor>" by blast \<comment> \<open>S4: reflexive + transitive\<close>
  lemma "equivalence aRel  \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast \<comment> \<open>S5: preorder + symmetric\<close>
  lemma "reflexive aRel \<and> euclidean aRel  \<Longrightarrow>  \<lfloor>M\<rfloor> \<and> \<lfloor>V\<rfloor>" by blast \<comment> \<open>S5\<close>

  text\<open>  Using these definitions, we can derive axioms for the most common modal logics (see also @{cite "C47"}). 
  Thereby we are free to use either the semantic constraints or the related \emph{Sahlqvist} axioms. Here we provide 
  both versions. In what follows we use the semantic constraints (for improved performance).
  \pagebreak \<close>
 
(*<*)      
end
(*>*)      
