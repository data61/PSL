section \<open> Unrestriction \<close>

theory utp_unrest
  imports utp_expr_insts
begin

subsection \<open> Definitions and Core Syntax \<close>
  
text \<open> Unrestriction is an encoding of semantic freshness that allows us to reason about the
  presence of variables in predicates without being concerned with abstract syntax trees.
  An expression $p$ is unrestricted by lens $x$, written $x \mathop{\sharp} p$, if
  altering the value of $x$ has no effect on the valuation of $p$. This is a sufficient
  notion to prove many laws that would ordinarily rely on an \emph{fv} function. 

  Unrestriction was first defined in the work of Marcel Oliveira~\cite{Oliveira2005-PHD,Oliveira07} in his
  UTP mechanisation in \emph{ProofPowerZ}. Our definition modifies his in that our variables
  are semantically characterised as lenses, and supported by the lens laws, rather than named 
  syntactic entities. We effectively fuse the ideas from both Feliachi~\cite{Feliachi2010} and 
  Oliveira's~\cite{Oliveira07} mechanisations of the UTP, the former being also purely semantic
  in nature.

  We first set up overloaded syntax for unrestriction, as several concepts will have this
  defined. \<close>

consts
  unrest :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

syntax
  "_unrest" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>" 20)
  
translations
  "_unrest x p" == "CONST unrest x p"                                           
  "_unrest (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_unrest (x +\<^sub>L y) P"

text \<open> Our syntax translations support both variables and variable sets such that we can write down 
  predicates like @{term "&x \<sharp> P"} and also @{term "{&x,&y,&z} \<sharp> P"}. 

  We set up a simple tactic for discharging unrestriction conjectures using a simplification set. \<close>
  
named_theorems unrest
method unrest_tac = (simp add: unrest)?

text \<open> Unrestriction for expressions is defined as a lifted construct using the underlying lens
  operations. It states that lens $x$ is unrestricted by expression $e$ provided that, for any
  state-space binding $b$ and variable valuation $v$, the value which the expression evaluates
  to is unaltered if we set $x$ to $v$ in $b$. In other words, we cannot effect the behaviour
  of $e$ by changing $x$. Thus $e$ does not observe the portion of state-space characterised
  by $x$. We add this definition to our overloaded constant. \<close>
  
lift_definition unrest_uexpr :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> bool"
is "\<lambda> x e. \<forall> b v. e (put\<^bsub>x\<^esub> b v) = e b" .

adhoc_overloading
  unrest unrest_uexpr

lemma unrest_expr_alt_def:
  "weak_lens x \<Longrightarrow> (x \<sharp> P) = (\<forall> b b'. \<lbrakk>P\<rbrakk>\<^sub>e (b \<oplus>\<^sub>L b' on x) = \<lbrakk>P\<rbrakk>\<^sub>e b)"
  by (transfer, metis lens_override_def weak_lens.put_get)
  
subsection \<open> Unrestriction laws \<close>
  
text \<open> We now prove unrestriction laws for the key constructs of our expression model. Many
  of these depend on lens properties and so variously employ the assumptions @{term mwb_lens} and
  @{term vwb_lens}, depending on the number of assumptions from the lenses theory is required.

  Firstly, we prove a general property -- if $x$ and $y$ are both unrestricted in $P$, then their composition
  is also unrestricted in $P$. One can interpret the composition here as a union -- if the two sets
  of variables $x$ and $y$ are unrestricted, then so is their union. \<close>
  
lemma unrest_var_comp [unrest]:
  "\<lbrakk> x \<sharp> P; y \<sharp> P \<rbrakk> \<Longrightarrow> x;y \<sharp> P"
  by (transfer, simp add: lens_defs)

lemma unrest_svar [unrest]: "(&x \<sharp> P) \<longleftrightarrow> (x \<sharp> P)"
  by (transfer, simp add: lens_defs)

text \<open> No lens is restricted by a literal, since it returns the same value for any state binding. \<close>
    
lemma unrest_lit [unrest]: "x \<sharp> \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

text \<open> If one lens is smaller than another, then any unrestriction on the larger lens implies
  unrestriction on the smaller. \<close>
    
lemma unrest_sublens:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "y \<subseteq>\<^sub>L x"
  shows "y \<sharp> P" 
  using assms
  by (transfer, metis (no_types, lifting) lens.select_convs(2) lens_comp_def sublens_def)
    
text \<open> If two lenses are equivalent, and thus they characterise the same state-space regions,
  then clearly unrestrictions over them are equivalent. \<close>
    
lemma unrest_equiv:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "mwb_lens y" "x \<approx>\<^sub>L y" "x \<sharp> P"
  shows "y \<sharp> P"
  by (metis assms lens_equiv_def sublens_pres_mwb sublens_put_put unrest_uexpr.rep_eq)

text \<open> If we can show that an expression is unrestricted on a bijective lens, then is unrestricted
  on the entire state-space. \<close>

lemma bij_lens_unrest_all:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "bij_lens X" "X \<sharp> P"
  shows "\<Sigma> \<sharp> P"
  using assms bij_lens_equiv_id lens_equiv_def unrest_sublens by blast

lemma bij_lens_unrest_all_eq:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "bij_lens X"
  shows "(\<Sigma> \<sharp> P) \<longleftrightarrow> (X \<sharp> P)"
  by (meson assms bij_lens_equiv_id lens_equiv_def unrest_sublens)

text \<open> If an expression is unrestricted by all variables, then it is unrestricted by any variable \<close>

lemma unrest_all_var:
  fixes e :: "('a, '\<alpha>) uexpr"
  assumes "\<Sigma> \<sharp> e"
  shows "x \<sharp> e"
  by (metis assms id_lens_def lens.simps(2) unrest_uexpr.rep_eq)

text \<open> We can split an unrestriction composed by lens plus \<close>

lemma unrest_plus_split:
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<bowtie> y" "vwb_lens x" "vwb_lens y"
  shows "unrest (x +\<^sub>L y) P \<longleftrightarrow> (x \<sharp> P) \<and> (y \<sharp> P)"
  using assms
  by (meson lens_plus_right_sublens lens_plus_ub sublens_refl unrest_sublens unrest_var_comp vwb_lens_wb)

text \<open> The following laws demonstrate the primary motivation for lens independence: a variable
  expression is unrestricted by another variable only when the two variables are independent. 
  Lens independence thus effectively allows us to semantically characterise when two variables,
  or sets of variables, are different. \<close>

lemma unrest_var [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> y \<sharp> var x"
  by (transfer, auto)
    
lemma unrest_iuvar [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $y \<sharp> $x"
  by (simp add: unrest_var)

lemma unrest_ouvar [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $y\<acute> \<sharp> $x\<acute>"
  by (simp add: unrest_var)

text \<open> The following laws follow automatically from independence of input and output variables. \<close>
    
lemma unrest_iuvar_ouvar [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "mwb_lens y"
  shows "$x \<sharp> $y\<acute>"
  by (metis prod.collapse unrest_uexpr.rep_eq var.rep_eq var_lookup_out var_update_in)

lemma unrest_ouvar_iuvar [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "mwb_lens y"
  shows "$x\<acute> \<sharp> $y"
  by (metis prod.collapse unrest_uexpr.rep_eq var.rep_eq var_lookup_in var_update_out)

text \<open> Unrestriction distributes through the various function lifting expression constructs;
  this allows us to prove unrestrictions for the majority of the expression language. \<close>
    
lemma unrest_uop [unrest]: "x \<sharp> e \<Longrightarrow> x \<sharp> uop f e"
  by (transfer, simp)

lemma unrest_bop [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> bop f u v"
  by (transfer, simp)

lemma unrest_trop [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v; x \<sharp> w \<rbrakk> \<Longrightarrow> x \<sharp> trop f u v w"
  by (transfer, simp)

lemma unrest_qtop [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v; x \<sharp> w; x \<sharp> y \<rbrakk> \<Longrightarrow> x \<sharp> qtop f u v w y"
  by (transfer, simp)

text \<open> For convenience, we also prove unrestriction rules for the bespoke operators on equality,
  numbers, arithmetic etc. \<close>
    
lemma unrest_eq [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u =\<^sub>u v"
  by (simp add: eq_upred_def, transfer, simp)

lemma unrest_zero [unrest]: "x \<sharp> 0"
  by (simp add: unrest_lit zero_uexpr_def)

lemma unrest_one [unrest]: "x \<sharp> 1"
  by (simp add: one_uexpr_def unrest_lit)

lemma unrest_numeral [unrest]: "x \<sharp> (numeral n)"
  by (simp add: numeral_uexpr_simp unrest_lit)

lemma unrest_sgn [unrest]: "x \<sharp> u \<Longrightarrow> x \<sharp> sgn u"
  by (simp add: sgn_uexpr_def unrest_uop)

lemma unrest_abs [unrest]: "x \<sharp> u \<Longrightarrow> x \<sharp> abs u"
  by (simp add: abs_uexpr_def unrest_uop)

lemma unrest_plus [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u + v"
  by (simp add: plus_uexpr_def unrest)

lemma unrest_uminus [unrest]: "x \<sharp> u \<Longrightarrow> x \<sharp> - u"
  by (simp add: uminus_uexpr_def unrest)

lemma unrest_minus [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u - v"
  by (simp add: minus_uexpr_def unrest)

lemma unrest_times [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u * v"
  by (simp add: times_uexpr_def unrest)

lemma unrest_divide [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u / v"
  by (simp add: divide_uexpr_def unrest)

lemma unrest_case_prod [unrest]: "\<lbrakk> \<And> i j. x \<sharp> P i j \<rbrakk> \<Longrightarrow> x \<sharp> case_prod P v"
  by (simp add: prod.split_sel_asm)

text \<open> For a $\lambda$-term we need to show that the characteristic function expression does
  not restrict $v$ for any input value $x$. \<close>
    
lemma unrest_ulambda [unrest]:
  "\<lbrakk> \<And> x. v \<sharp> F x \<rbrakk> \<Longrightarrow> v \<sharp> (\<lambda> x \<bullet> F x)"
  by (transfer, simp)

end