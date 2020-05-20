theory "Static_Semantics"
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Ids"
  "Lib"
  "Syntax"
  "Denotational_Semantics"
  "Frechet_Correctness"
begin
section \<open>Static Semantics\<close>
text \<open>This section introduces functions for computing properties of the static semantics, specifically
 the following dependencies:
  \begin{itemize}
    \item Signatures: Symbols (from the interpretation) which influence the result of a term, ode, formula, program
    \item Free variables: Variables (from the state) which influence the result of a term, ode, formula, program
    \item Bound variables: Variables (from the state) that *might* be influenced by a program
    \item Must-bound variables: Variables (from the state) that are *always* influenced by a program (i.e.
  will never depend on anything other than the free variables of that program)
  \end{itemize}
   
  We also prove basic lemmas about these definitions, but their overall correctness is proved elsewhere
  in the Bound Effect and Coincidence theorems.
  \<close>

subsection \<open>Signature Definitions\<close>
primrec SIGT :: "('a, 'c) trm \<Rightarrow> 'a set"
where
  "SIGT (Var var) = {}"
| "SIGT (Const r) = {}"
| "SIGT (Function var f) = {var} \<union> (\<Union>i. SIGT (f i))"
| "SIGT (Plus t1 t2) = SIGT t1 \<union> SIGT t2"
| "SIGT (Times t1 t2) = SIGT t1 \<union> SIGT t2"
| "SIGT (DiffVar x) = {}"
| "SIGT (Differential t) = SIGT t"

primrec SIGO   :: "('a, 'c) ODE \<Rightarrow> ('a + 'c) set"
where
  "SIGO (OVar c) = {Inr c}"
| "SIGO (OSing x \<theta>) =  {Inl x| x. x \<in> SIGT \<theta>}"
| "SIGO (OProd ODE1 ODE2) = SIGO ODE1 \<union> SIGO ODE2"
  
primrec SIGP   :: "('a, 'b, 'c) hp      \<Rightarrow> ('a + 'b + 'c) set"
and     SIGF   :: "('a, 'b, 'c) formula \<Rightarrow> ('a + 'b + 'c) set"
where
  "SIGP (Pvar var) = {Inr (Inr var)}"
| "SIGP (Assign var t) = {Inl x | x. x \<in> SIGT t}"
| "SIGP (DiffAssign var t) = {Inl x | x. x \<in> SIGT t}"
| "SIGP (Test p) = SIGF p"
| "SIGP (EvolveODE ODE p) = SIGF p \<union> {Inl x | x. Inl x \<in> SIGO ODE} \<union> {Inr (Inr x) | x. Inr x \<in> SIGO ODE}"
| "SIGP (Choice a b) = SIGP a \<union> SIGP b"
| "SIGP (Sequence a b) = SIGP a \<union> SIGP b"
| "SIGP (Loop a) = SIGP a"
| "SIGF (Geq t1 t2) = {Inl x | x. x \<in> SIGT t1 \<union> SIGT t2}"
| "SIGF (Prop var args) = {Inr (Inr var)} \<union> {Inl x | x. x \<in> (\<Union>i. SIGT (args i))}"
| "SIGF (Not p) = SIGF p"
| "SIGF (And p1 p2) = SIGF p1 \<union> SIGF p2"
| "SIGF (Exists var p) = SIGF p"
| "SIGF (Diamond a p) = SIGP a \<union> SIGF p"
| "SIGF (InContext var p) = {Inr (Inl var)} \<union> SIGF p"

fun primify :: "('a + 'a) \<Rightarrow> ('a + 'a) set"
where
  "primify (Inl x) = {Inl x, Inr x}"
| "primify (Inr x) = {Inl x, Inr x}"
  
subsection \<open>Variable Binding Definitions\<close>
text\<open>
  We represent the (free or bound or must-bound) variables of a term as an (id + id) set,
  where all the (Inl x) elements are unprimed variables x and all the (Inr x) elements are
  primed variables x'.
  \<close>
text\<open>Free variables of a term \<close>
primrec FVT :: "('a, 'c) trm \<Rightarrow> ('c + 'c) set"
where
  "FVT (Var x) = {Inl x}"
| "FVT (Const x) = {}"
| "FVT (Function f args) = (\<Union>i. FVT (args i))"
| "FVT (Plus f g) = FVT f \<union> FVT g"
| "FVT (Times f g) = FVT f \<union> FVT g"
| "FVT (Differential f) = (\<Union>x \<in> (FVT f). primify x)"
| "FVT (DiffVar x) = {Inr x}"

fun FVDiff :: "('a, 'c) trm \<Rightarrow> ('c + 'c) set"
where "FVDiff f = (\<Union>x \<in> (FVT f). primify x)"

text\<open> Free variables of an ODE includes both the bound variables and the terms \<close>
fun FVO :: "('a, 'c) ODE \<Rightarrow> 'c set"
where
  "FVO (OVar c) = UNIV"
| "FVO (OSing x \<theta>) = {x} \<union> {x . Inl x \<in> FVT \<theta>}"
| "FVO (OProd ODE1 ODE2) = FVO ODE1 \<union> FVO ODE2"

text\<open> Bound variables of ODEs, formulas, programs \<close>
fun BVO :: "('a, 'c) ODE \<Rightarrow> ('c + 'c) set"
where 
  "BVO (OVar c) = UNIV"
| "BVO (OSing x \<theta>) = {Inl x, Inr x}"
| "BVO (OProd ODE1 ODE2) = BVO ODE1 \<union> BVO ODE2"
  
fun BVF :: "('a, 'b, 'c) formula \<Rightarrow> ('c + 'c) set"
and BVP :: "('a, 'b, 'c) hp \<Rightarrow> ('c + 'c) set"
where
  "BVF (Geq f g) = {}"
| "BVF (Prop p dfun_args) = {}"
| "BVF (Not p) = BVF p"
| "BVF (And p q) = BVF p \<union> BVF q"
| "BVF (Exists x p) = {Inl x} \<union> BVF p"
| "BVF (Diamond \<alpha> p) = BVP \<alpha> \<union> BVF p"
| "BVF (InContext C p) = UNIV"

| "BVP (Pvar a) = UNIV"
| "BVP (Assign x \<theta>) = {Inl x}"
| "BVP (DiffAssign x \<theta>) = {Inr x}"
| "BVP (Test \<phi>) = {}"
| "BVP (EvolveODE ODE \<phi>) = BVO ODE"
| "BVP (Choice \<alpha> \<beta>) = BVP \<alpha> \<union> BVP \<beta>"
| "BVP (Sequence \<alpha> \<beta>) = BVP \<alpha> \<union> BVP \<beta>"
| "BVP (Loop \<alpha>) = BVP \<alpha>"

text\<open> Must-bound variables (of a program)\<close>
fun MBV :: "('a, 'b, 'c) hp \<Rightarrow> ('c + 'c) set"
where
  "MBV (Pvar a) = {}"
| "MBV (Choice \<alpha> \<beta>) = MBV \<alpha> \<inter> MBV \<beta>"
| "MBV (Sequence \<alpha> \<beta>) = MBV \<alpha> \<union> MBV \<beta>"
| "MBV (Loop \<alpha>) = {}"
| "MBV (EvolveODE ODE _) = (Inl ` (ODE_dom ODE)) \<union> (Inr ` (ODE_dom ODE))"
| "MBV \<alpha> = BVP \<alpha>"

text\<open>Free variables of a formula,
 free variables of a program \<close>
fun FVF :: "('a, 'b, 'c) formula \<Rightarrow> ('c + 'c) set"
and FVP :: "('a, 'b, 'c) hp \<Rightarrow> ('c + 'c) set"
where
  "FVF (Geq f g) = FVT f \<union> FVT g"
| "FVF (Prop p args) = (\<Union>i. FVT (args i))"
| "FVF (Not p) = FVF p"
| "FVF (And p q) = FVF p \<union> FVF q"
| "FVF (Exists x p) = FVF p - {Inl x}"
| "FVF (Diamond \<alpha> p) =   FVP \<alpha> \<union> (FVF p - MBV \<alpha>)"
| "FVF (InContext C p) = UNIV"
| "FVP (Pvar a) = UNIV"
| "FVP (Assign x \<theta>) = FVT \<theta>"
| "FVP (DiffAssign x \<theta>) = FVT \<theta>"
| "FVP (Test \<phi>) = FVF \<phi>"
| "FVP (EvolveODE ODE \<phi>) = BVO ODE \<union> (Inl ` FVO ODE) \<union> FVF \<phi>"
| "FVP (Choice \<alpha> \<beta>) = FVP \<alpha> \<union> FVP \<beta>"
| "FVP (Sequence \<alpha> \<beta>) = FVP \<alpha> \<union> (FVP \<beta> - MBV \<alpha>)"
| "FVP (Loop \<alpha>) = FVP \<alpha>"

subsection \<open>Lemmas for reasoning about static semantics\<close> 

lemma primify_contains:"x \<in> primify x"
  by (cases "x") auto

lemma FVDiff_sub:"FVT f \<subseteq> FVDiff f"
  by (auto simp add:  primify_contains)

lemma fvdiff_plus1:"FVDiff (Plus t1 t2) = FVDiff t1 \<union> FVDiff t2"
  by (auto)

lemma agree_func_fvt:"Vagree \<nu> \<nu>' (FVT (Function f args)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVT (args i))"
  by (auto simp add: Set.Un_upper1 agree_supset Vagree_def)

lemma agree_plus1:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff t1)"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i) \<union> (\<Union>i\<in>FVT t2. primify i))"
    using fvdiff_plus1 FVDiff.simps agree by (auto)
  have agreeL:"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i))"
    using agree' agree_supset Set.Un_upper1 by (blast)
  show "Vagree \<nu> \<nu>' (FVDiff t1)" using agreeL by (auto)
qed

lemma agree_plus2:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff t2)"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Plus t1 t2))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i) \<union> (\<Union>i\<in>FVT t2. primify i))"
    using fvdiff_plus1 FVDiff.simps agree by (auto)
  have agreeR:"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t2. primify i))"
    using agree' agree_supset Set.Un_upper1 by (blast)
  show "Vagree \<nu> \<nu>' (FVDiff t2)" using agreeR by (auto)
qed

lemma agree_times1:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff t1)"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i) \<union> (\<Union>i\<in>FVT t2. primify i))"
    using fvdiff_plus1 FVDiff.simps agree by (auto)
  have agreeL:"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i))"
    using agree' agree_supset Set.Un_upper1 by (blast)
  show "Vagree \<nu> \<nu>' (FVDiff t1)" using agreeL by (auto)
qed

lemma agree_times2:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2)) \<Longrightarrow> Vagree \<nu> \<nu>' (FVDiff t2)"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff (Times t1 t2))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t1. primify i) \<union> (\<Union>i\<in>FVT t2. primify i))"
    using fvdiff_plus1 FVDiff.simps agree by (auto)
  have agreeR:"Vagree \<nu> \<nu>' ((\<Union>i\<in>FVT t2. primify i))"
    using agree' agree_supset Set.Un_upper1 by (blast)
  show "Vagree \<nu> \<nu>' (FVDiff t2)" using agreeR by (auto)
qed

lemma agree_func:"Vagree \<nu> \<nu>' (FVDiff ($f var args)) \<Longrightarrow> (\<And>i. Vagree \<nu> \<nu>' (FVDiff (args i)))"
proof -
  assume agree:"Vagree \<nu> \<nu>' (FVDiff ($f var args))"
  have agree':"Vagree \<nu> \<nu>' ((\<Union>i. (\<Union>j \<in>(FVT (args i)). primify j)))"
    using fvdiff_plus1 FVDiff.simps agree by (auto)
  fix i :: 'a
  have "\<And>S. \<not> S \<subseteq> (\<Union>f. \<Union> (primify ` FVT (args f))) \<or> Vagree \<nu> \<nu>' S"
    using agree' agree_supset by blast
  then have "\<And>f. f \<notin> UNIV \<or> Vagree \<nu> \<nu>' (\<Union> (primify ` FVT (args f)))"
    by blast
  then show "Vagree \<nu> \<nu>' (FVDiff (args i))"
    by simp
qed
  
end
