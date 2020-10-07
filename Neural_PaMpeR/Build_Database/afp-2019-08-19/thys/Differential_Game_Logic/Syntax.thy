theory "Syntax"
imports
  Complex_Main
  "Identifiers"
begin 
section \<open>Syntax\<close>

text \<open>
  Defines the syntax of Differential Game Logic as inductively defined data types.
  \<^url>\<open>https://doi.org/10.1145/2817824\<close> \<^url>\<open>https://doi.org/10.1007/978-3-319-94205-6_15\<close>
\<close>

subsection \<open>Terms\<close>

text \<open>Numeric literals\<close>
type_synonym lit = real

text \<open>the set of all real variables\<close>
abbreviation allidents:: "ident set"
  where "allidents \<equiv> {x | x. True}"

text \<open>Variables and differential variables\<close>

datatype variable =
  RVar ident
| DVar ident  

datatype trm =
  Var variable
| Number lit
| Const ident
| Func ident trm
| Plus trm trm
| Times trm trm
| Differential trm

subsection \<open>Formulas and Hybrid Games\<close>

datatype fml =
  Pred ident trm
| Geq trm trm
| Not fml                 ("!")
| And fml fml             (infixr "&&" 8)
| Exists variable fml
| Diamond game fml        ("(\<langle> _ \<rangle> _)" 20)
and game =
  Game ident
| Assign variable trm     (infixr ":=" 20)
| Test fml                ("?")
| Choice game game        (infixr "\<union>\<union>" 10)
| Compose game game       (infixr ";;" 8)
| Loop game               ("_**")
| Dual game               ("_^d")
| ODE ident trm


paragraph \<open>Derived operators\<close>
definition Neg ::"trm \<Rightarrow> trm" 
where "Neg \<theta> = Times (Number (-1)) \<theta>"

definition Minus ::"trm \<Rightarrow> trm \<Rightarrow> trm"
where "Minus \<theta> \<eta> = Plus \<theta> (Neg \<eta>)"

definition Or :: "fml \<Rightarrow> fml \<Rightarrow> fml" (infixr "||" 7)
where "Or P Q = Not (And (Not P) (Not Q))"

definition Implies :: "fml \<Rightarrow> fml \<Rightarrow> fml" (infixr "\<rightarrow>" 10)
where "Implies P Q = Or Q (Not P)"

definition Equiv :: "fml \<Rightarrow> fml \<Rightarrow> fml" (infixr "\<leftrightarrow>" 10)
where "Equiv P Q = Or (And P Q) (And (Not P) (Not Q))"

definition Forall :: "variable \<Rightarrow> fml \<Rightarrow> fml"
where "Forall x P = Not (Exists x (Not P))"

definition Equals :: "trm \<Rightarrow> trm \<Rightarrow> fml"
where "Equals \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Geq \<theta>' \<theta>))"

definition Greater :: "trm \<Rightarrow> trm \<Rightarrow> fml"
where "Greater \<theta> \<theta>' = ((Geq \<theta> \<theta>') && (Not (Geq \<theta>' \<theta>)))"
  
text \<open>Justification: determinacy theorem justifies this equivalent syntactic abbreviation for box modalities from diamond modalities
  Theorem 3.1 \<^url>\<open>https://doi.org/10.1145/2817824\<close>\<close>
definition Box :: "game \<Rightarrow> fml \<Rightarrow> fml" ("([[_]]_)" 20)
where "Box \<alpha> P = Not (Diamond \<alpha> (Not P))"
  
definition TT ::"fml" 
where "TT = Geq (Number 0) (Number 0)"

definition FF ::"fml" 
where "FF = Geq (Number 0) (Number 1)"

definition Skip ::"game" 
where "Skip = Test TT"

text \<open>Inference: premises, then conclusion\<close>
type_synonym inference = "fml list * fml"

type_synonym sequent = "fml list * fml list"
text \<open>Rule: premises, then conclusion\<close>
type_synonym rule = "sequent list * sequent"


subsection \<open>Structural Induction\<close>

text \<open>Induction principles for hybrid games owing to their mutually recursive definition with formulas \<close>

lemma game_induct [case_names Game Assign ODE Test Choice Compose Loop Dual]:
   "(\<And>a. P (Game a)) 
    \<Longrightarrow> (\<And>x \<theta>. P (Assign x \<theta>))
    \<Longrightarrow> (\<And>x \<theta>. P (ODE x \<theta>))
    \<Longrightarrow> (\<And>\<phi>. P (? \<phi>))
    \<Longrightarrow> (\<And>\<alpha> \<beta>. P \<alpha> \<Longrightarrow> P \<beta> \<Longrightarrow> P (\<alpha> \<union>\<union> \<beta>))
    \<Longrightarrow> (\<And>\<alpha> \<beta>. P \<alpha> \<Longrightarrow> P \<beta> \<Longrightarrow> P (\<alpha> ;; \<beta>))
    \<Longrightarrow> (\<And>\<alpha>. P \<alpha> \<Longrightarrow> P (\<alpha>**))
    \<Longrightarrow> (\<And>\<alpha>. P \<alpha> \<Longrightarrow> P (\<alpha>^d))
    \<Longrightarrow> P \<alpha>"
  by(induction rule: game.induct) (auto)

lemma fml_induct [case_names Pred Geq Not And Exists Diamond]:
  "(\<And>x \<theta>. P (Pred x \<theta>))
  \<Longrightarrow> (\<And>\<theta> \<eta>. P (Geq \<theta> \<eta>))
  \<Longrightarrow> (\<And>\<phi>. P \<phi> \<Longrightarrow> P (Not \<phi>))
  \<Longrightarrow> (\<And>\<phi> \<psi>. P \<phi> \<Longrightarrow> P \<psi> \<Longrightarrow> P (And \<phi> \<psi>))
  \<Longrightarrow> (\<And>x \<phi>. P \<phi> \<Longrightarrow> P (Exists x \<phi>))
  \<Longrightarrow> (\<And>\<alpha> \<phi>. P \<phi> \<Longrightarrow> P (Diamond \<alpha> \<phi>))
  \<Longrightarrow> P \<phi>"
  by (induction rule: fml.induct) (auto)

text \<open>the set of all variables\<close>
abbreviation allvars:: "variable set"
  where "allvars \<equiv> {x::variable. True}"

end
