section \<open> Substitution \<close>

theory utp_subst
imports
  utp_expr
  utp_unrest
begin

subsection \<open> Substitution definitions \<close>

text \<open> Variable substitution, like unrestriction, will be characterised semantically using lenses
  and state-spaces. Effectively a substitution $\sigma$ is simply a function on the state-space which
  can be applied to an expression $e$ using the syntax $\sigma \mathop{\dagger} e$.  We introduce 
  a polymorphic constant that will be used to represent application of a substitution, and also a 
  set of theorems to represent laws. \<close>

consts
  usubst :: "'s \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "\<dagger>" 80)

named_theorems usubst

text \<open> A substitution is simply a transformation on the alphabet; it shows how variables
  should be mapped to different values. Most of the time these will be homogeneous functions 
  but for flexibility we also allow some operations to be heterogeneous. \<close>

type_synonym ('\<alpha>,'\<beta>) psubst = "'\<alpha> \<Rightarrow> '\<beta>"
type_synonym '\<alpha> usubst = "'\<alpha> \<Rightarrow> '\<alpha>"

text \<open> Application of a substitution simply applies the function $\sigma$ to the state binding
  $b$ before it is handed to $e$ as an input. This effectively ensures all variables are updated
  in $e$. \<close>
  
lift_definition subst :: "('\<alpha>, '\<beta>) psubst \<Rightarrow> ('a, '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" is
"\<lambda> \<sigma> e b. e (\<sigma> b)" .

adhoc_overloading
  usubst subst

text \<open> Substitutions can be updated by associating variables with expressions. We thus create an 
  additional polymorphic constant to represent updating the value of a variable to an expression 
  in a substitution, where the variable is modelled by type @{typ "'v"}. This again allows us
  to support different notions of variables, such as deep variables, later. \<close>

consts subst_upd :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> 'v \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst"

text \<open> The following function takes a substitution form state-space @{typ "'\<alpha>"} to @{typ "'\<beta>"}, a
  lens with source @{typ "'\<beta>"} and view "'a", and an expression over @{typ "'\<alpha>"} and returning
  a value of type "@{typ "'a"}, and produces an updated substitution. It does this by constructing
  a substitution function that takes state binding $b$, and updates the state first by applying
  the original substitution $\sigma$, and then updating the part of the state associated with lens
  $x$ with expression evaluated in the context of $b$. This effectively means that $x$ is now
  associated with expression $v$. We add this definition to our overloaded constant. \<close>
  
definition subst_upd_uvar :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst" where
"subst_upd_uvar \<sigma> x v = (\<lambda> b. put\<^bsub>x\<^esub> (\<sigma> b) (\<lbrakk>v\<rbrakk>\<^sub>eb))"

adhoc_overloading
  subst_upd subst_upd_uvar

text \<open> The next function looks up the expression associated with a variable in a substitution
  by use of the \emph{get} lens function. \<close>

lift_definition usubst_lookup :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<langle>_\<rangle>\<^sub>s")
is "\<lambda> \<sigma> x b. get\<^bsub>x\<^esub> (\<sigma> b)" .

text \<open> Substitutions also exhibit a natural notion of unrestriction which states that $\sigma$
  does not restrict $x$ if application of $\sigma$ to an arbitrary state $\rho$ will not effect
  the valuation of $x$. Put another way, it requires that \emph{put} and the substitution commute. \<close>
  
definition unrest_usubst :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst \<Rightarrow> bool"
where "unrest_usubst x \<sigma> = (\<forall> \<rho> v. \<sigma> (put\<^bsub>x\<^esub> \<rho> v) = put\<^bsub>x\<^esub> (\<sigma> \<rho>) v)"

adhoc_overloading
  unrest unrest_usubst

text \<open> A conditional substitution deterministically picks one of the two substitutions based on a
  Booolean expression which is evaluated on the present state-space. It is analogous to a functional
  if-then-else. \<close>
  
definition cond_subst :: "'\<alpha> usubst \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> usubst" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>s/ _)" [52,0,53] 52) where
"cond_subst \<sigma> b \<rho> = (\<lambda> s. if \<lbrakk>b\<rbrakk>\<^sub>e s then \<sigma>(s) else \<rho>(s))"
  
text \<open> Parallel substitutions allow us to divide the state space into three segments using two
  lens, A and B. They correspond to the part of the state that should be updated by the 
  respective substitution. The two lenses should be independent. If any part of the state
  is not covered by either lenses then this area is left unchanged (framed). \<close>
  
definition par_subst :: "'\<alpha> usubst \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> usubst" where
"par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2 = (\<lambda> s. (s \<oplus>\<^sub>L (\<sigma>\<^sub>1 s) on A) \<oplus>\<^sub>L (\<sigma>\<^sub>2 s) on B)"
  
subsection \<open> Syntax translations \<close>

text \<open> We support two kinds of syntax for substitutions, one where we construct a substitution
  using a maplet-style syntax, with variables mapping to expressions. Such a constructed substitution
  can be applied to an expression. Alternatively, we support the more traditional notation, 
  $P \llbracket v / x \rrbracket$, which also support multiple simultaneous substitutions. We 
  have to use double square brackets as the single ones are already well used. 

  We set up non-terminals to represent a single substitution maplet, a sequence of maplets, a
  list of expressions, and a list of alphabets. The parser effectively uses @{term subst_upd}
  to construct substitutions from multiple variables. 
\<close>
  
nonterminal smaplet and smaplets and uexp and uexprs and salphas

syntax
  "_smaplet"  :: "[salpha, 'a] => smaplet"             ("_ /\<mapsto>\<^sub>s/ _")
  ""          :: "smaplet => smaplets"            ("_")
  "_SMaplets" :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  "_SubstUpd" :: "['m usubst, smaplets] => 'm usubst" ("_/'(_')" [900,0] 900)
  "_Subst"    :: "smaplets => 'a \<rightharpoonup> 'b"            ("(1[_])")
  "_psubst"  :: "[logic, svars, uexprs] \<Rightarrow> logic"
  "_subst"   :: "logic \<Rightarrow> uexprs \<Rightarrow> salphas \<Rightarrow> logic" ("(_\<lbrakk>_'/_\<rbrakk>)" [990,0,0] 991)
  "_uexp_l"  :: "logic \<Rightarrow> uexp" ("_" [64] 64)
  "_uexprs"  :: "[uexp, uexprs] => uexprs" ("_,/ _")
  ""         :: "uexp => uexprs" ("_")
  "_salphas" :: "[salpha, salphas] => salphas" ("_,/ _")
  ""         :: "salpha => salphas" ("_")
  "_par_subst" :: "logic \<Rightarrow> salpha \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ [_|_]\<^sub>s _" [100,0,0,101] 101)
    
translations
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet x y)"        == "CONST subst_upd m x y"
  "_Subst ms"                         == "_SubstUpd (CONST id) ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"
  "_subst P es vs" => "CONST subst (_psubst (CONST id) vs es) P"
  "_psubst m (_salphas x xs) (_uexprs v vs)" => "_psubst (_psubst m x v) xs vs"
  "_psubst m x v"  => "CONST subst_upd m x v"
  "_subst P v x" <= "CONST usubst (CONST subst_upd (CONST id) x v) P"
  "_subst P v x" <= "_subst P (_spvar x) v"
  "_par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2" == "CONST par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2"
  "_uexp_l e" => "e"

text \<open> Thus we can write things like @{term "\<sigma>(x \<mapsto>\<^sub>s v)"} to update a variable $x$ in $\sigma$ with
  expression $v$, @{term "[x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f]"} to construct a substitution with two variables,
  and finally @{term "P\<lbrakk>v/x\<rbrakk>"}, the traditional syntax.

  We can now express deletion of a substitution maplet. \<close>

definition subst_del :: "'\<alpha> usubst \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> usubst" (infix "-\<^sub>s" 85) where
"subst_del \<sigma> x = \<sigma>(x \<mapsto>\<^sub>s &x)"

subsection \<open> Substitution Application Laws \<close>

text \<open> We set up a simple substitution tactic that applies substitution and unrestriction laws \<close>

method subst_tac = (simp add: usubst unrest)?

text \<open> Evaluation of a substitution expression involves application of the substitution to different
  variables. Thus we first prove laws for these cases. The simplest substitution, $id$, when applied
  to any variable $x$ simply returns the variable expression, since $id$ has no effect. \<close>
  
lemma usubst_lookup_id [usubst]: "\<langle>id\<rangle>\<^sub>s x = var x"
  by (transfer, simp)

lemma subst_upd_id_lam [usubst]: "subst_upd (\<lambda> x. x) x v = subst_upd id x v"
  by (simp add: id_def)
    
text \<open> A substitution update naturally yields the given expression. \<close>
    
lemma usubst_lookup_upd [usubst]:
  assumes "weak_lens x"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = v"
  using assms
  by (simp add: subst_upd_uvar_def, transfer) (simp)

lemma usubst_lookup_upd_pr_var [usubst]:
  assumes "weak_lens x"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s (pr_var x) = v"
  using assms
  by (simp add: subst_upd_uvar_def pr_var_def, transfer) (simp)
    
text \<open> Substitution update is idempotent. \<close>
    
lemma usubst_upd_idem [usubst]:
  assumes "mwb_lens x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, x \<mapsto>\<^sub>s v) = \<sigma>(x \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def assms comp_def)

lemma usubst_upd_idem_sub [usubst]:
  assumes "x \<subseteq>\<^sub>L y" "mwb_lens y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v) = \<sigma>(y \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def assms comp_def fun_eq_iff sublens_put_put)

text \<open> Substitution updates commute when the lenses are independent. \<close>
    
lemma usubst_upd_comm:
  assumes "x \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v) = \<sigma>(y \<mapsto>\<^sub>s v, x \<mapsto>\<^sub>s u)"
  using assms
  by (rule_tac ext, auto simp add: subst_upd_uvar_def assms comp_def lens_indep_comm)

lemma usubst_upd_comm2:
  assumes "z \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s s) = \<sigma>(x \<mapsto>\<^sub>s u, z \<mapsto>\<^sub>s s, y \<mapsto>\<^sub>s v)"
  using assms
  by (rule_tac ext, auto simp add: subst_upd_uvar_def assms comp_def lens_indep_comm)

lemma subst_upd_pr_var: "s(&x \<mapsto>\<^sub>s v) = s(x \<mapsto>\<^sub>s v)"
  by (simp add: pr_var_def) 

text \<open> A substitution which swaps two independent variables is an injective function. \<close>
    
lemma swap_usubst_inj:
  fixes x y :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "inj [x \<mapsto>\<^sub>s &y, y \<mapsto>\<^sub>s &x]"
proof (rule injI)
  fix b\<^sub>1 :: '\<alpha> and b\<^sub>2 :: '\<alpha>
  assume "[x \<mapsto>\<^sub>s &y, y \<mapsto>\<^sub>s &x] b\<^sub>1 = [x \<mapsto>\<^sub>s &y, y \<mapsto>\<^sub>s &x] b\<^sub>2"
  hence a: "put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b\<^sub>1 (\<lbrakk>&y\<rbrakk>\<^sub>e b\<^sub>1)) (\<lbrakk>&x\<rbrakk>\<^sub>e b\<^sub>1) = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b\<^sub>2 (\<lbrakk>&y\<rbrakk>\<^sub>e b\<^sub>2)) (\<lbrakk>&x\<rbrakk>\<^sub>e b\<^sub>2)"
    by (auto simp add: subst_upd_uvar_def)
  then have "(\<forall>a b c. put\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> a b) c = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> a c) b) \<and> 
             (\<forall>a b. get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> a b) = get\<^bsub>x\<^esub> a) \<and> (\<forall>a b. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> a b) = get\<^bsub>y\<^esub> a)"
    by (simp add: assms(3) lens_indep.lens_put_irr2 lens_indep_comm)
  then show "b\<^sub>1 = b\<^sub>2"
    by (metis a assms(1) assms(2) pr_var_def var.rep_eq vwb_lens.source_determination vwb_lens_def wb_lens_def weak_lens.put_get)   
qed

lemma usubst_upd_var_id [usubst]:
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s var x] = id"
  apply (simp add: subst_upd_uvar_def)
  apply (transfer)
  apply (rule ext)
  apply (auto)
  done

lemma usubst_upd_pr_var_id [usubst]:
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s var (pr_var x)] = id"
  apply (simp add: subst_upd_uvar_def pr_var_def)
  apply (transfer)
  apply (rule ext)
  apply (auto)
  done
  
lemma usubst_upd_comm_dash [usubst]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<sigma>($x\<acute> \<mapsto>\<^sub>s v, $x \<mapsto>\<^sub>s u) = \<sigma>($x \<mapsto>\<^sub>s u, $x\<acute> \<mapsto>\<^sub>s v)"
  using out_in_indep usubst_upd_comm by blast

lemma subst_upd_lens_plus [usubst]: 
  "subst_upd \<sigma> (x +\<^sub>L y) \<guillemotleft>(u,v)\<guillemotright> = \<sigma>(y \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, x \<mapsto>\<^sub>s \<guillemotleft>u\<guillemotright>)"
  by (simp add: lens_defs uexpr_defs subst_upd_uvar_def, transfer, auto)

lemma subst_upd_in_lens_plus [usubst]: 
  "subst_upd \<sigma> (ivar (x +\<^sub>L y)) \<guillemotleft>(u,v)\<guillemotright> = \<sigma>($y \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, $x \<mapsto>\<^sub>s \<guillemotleft>u\<guillemotright>)"
  by (simp add: lens_defs uexpr_defs subst_upd_uvar_def, transfer, auto simp add: prod.case_eq_if)

lemma subst_upd_out_lens_plus [usubst]: 
  "subst_upd \<sigma> (ovar (x +\<^sub>L y)) \<guillemotleft>(u,v)\<guillemotright> = \<sigma>($y\<acute> \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, $x\<acute> \<mapsto>\<^sub>s \<guillemotleft>u\<guillemotright>)"
  by (simp add: lens_defs uexpr_defs subst_upd_uvar_def, transfer, auto simp add: prod.case_eq_if)
    
lemma usubst_lookup_upd_indep [usubst]:
  assumes "mwb_lens x" "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, simp)

lemma subst_upd_plus [usubst]: 
  "x \<bowtie> y \<Longrightarrow> subst_upd s (x +\<^sub>L y) e = s(x \<mapsto>\<^sub>s \<pi>\<^sub>1(e), y \<mapsto>\<^sub>s \<pi>\<^sub>2(e))"
  by (simp add: subst_upd_uvar_def lens_defs, transfer, auto simp add: fun_eq_iff prod.case_eq_if lens_indep_comm)

text \<open> If a variable is unrestricted in a substitution then it's application has no effect. \<close>

lemma usubst_apply_unrest [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s x = var x"
  by (simp add: unrest_usubst_def, transfer, auto simp add: fun_eq_iff, metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)

text \<open> There follows various laws about deleting variables from a substitution. \<close>
    
lemma subst_del_id [usubst]:
  "vwb_lens x \<Longrightarrow> id -\<^sub>s x = id"
  by (simp add: subst_del_def subst_upd_uvar_def pr_var_def, transfer, auto)

lemma subst_del_upd_same [usubst]:
  "mwb_lens x \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) -\<^sub>s x = \<sigma> -\<^sub>s x"
  by (simp add: subst_del_def subst_upd_uvar_def)

lemma subst_del_upd_diff [usubst]:
  "x \<bowtie> y \<Longrightarrow> \<sigma>(y \<mapsto>\<^sub>s v) -\<^sub>s x = (\<sigma> -\<^sub>s x)(y \<mapsto>\<^sub>s v)"
  by (simp add: subst_del_def subst_upd_uvar_def lens_indep_comm)

text \<open> If a variable is unrestricted in an expression, then any substitution of that variable
  has no effect on the expression .\<close>
    
lemma subst_unrest [usubst]: "x \<sharp> P \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = \<sigma> \<dagger> P"
  by (simp add: subst_upd_uvar_def, transfer, auto)

lemma subst_unrest_2 [usubst]: 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u,y \<mapsto>\<^sub>s v) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s v) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis lens_indep.lens_put_comm)

lemma subst_unrest_3 [usubst]: 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s w) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s w) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_unrest_4 [usubst]: 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z" "x \<bowtie> u"
  shows "\<sigma>(x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_unrest_5 [usubst]: 
  fixes P :: "('a, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<bowtie> y" "x \<bowtie> z" "x \<bowtie> u" "x \<bowtie> v"
  shows "\<sigma>(x \<mapsto>\<^sub>s e, y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h, v \<mapsto>\<^sub>s i) \<dagger> P = \<sigma>(y \<mapsto>\<^sub>s f, z \<mapsto>\<^sub>s g, u \<mapsto>\<^sub>s h, v \<mapsto>\<^sub>s i) \<dagger> P"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, auto, metis (no_types, hide_lams) lens_indep_comm)

lemma subst_compose_upd [usubst]: "x \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<circ> \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<circ> \<rho>)(x \<mapsto>\<^sub>s v) "
  by (simp add: subst_upd_uvar_def, transfer, auto simp add: unrest_usubst_def)

text \<open> Any substitution is a monotonic function. \<close>
    
lemma subst_mono: "mono (subst \<sigma>)"
  by (simp add: less_eq_uexpr.rep_eq mono_def subst.rep_eq)

subsection \<open> Substitution laws \<close>
  
text \<open> We now prove the key laws that show how a substitution should be performed for every 
  expression operator, including the core function operators, literals, variables, and the 
  arithmetic operators. They are all added to the \emph{usubst} theorem attribute so that
  we can apply them using the substitution tactic. \<close>
    
lemma id_subst [usubst]: "id \<dagger> v = v"
  by (transfer, simp)

lemma subst_lit [usubst]: "\<sigma> \<dagger> \<guillemotleft>v\<guillemotright> = \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

lemma subst_var [usubst]: "\<sigma> \<dagger> var x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (transfer, simp)

lemma usubst_ulambda [usubst]: "\<sigma> \<dagger> (\<lambda> x \<bullet> P(x)) = (\<lambda> x \<bullet> \<sigma> \<dagger> P(x))"
  by (transfer, simp)

lemma unrest_usubst_del [unrest]: "\<lbrakk> vwb_lens x; x \<sharp> (\<langle>\<sigma>\<rangle>\<^sub>s x); x \<sharp> \<sigma> -\<^sub>s x \<rbrakk> \<Longrightarrow>  x \<sharp> (\<sigma> \<dagger> P)"
  by (simp add: subst_del_def subst_upd_uvar_def unrest_uexpr_def unrest_usubst_def subst.rep_eq usubst_lookup.rep_eq)
     (metis vwb_lens.put_eq)

text \<open> We add the symmetric definition of input and output variables to substitution laws
        so that the variables are correctly normalised after substitution. \<close>

lemma subst_uop [usubst]: "\<sigma> \<dagger> uop f v = uop f (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_bop [usubst]: "\<sigma> \<dagger> bop f u v = bop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_trop [usubst]: "\<sigma> \<dagger> trop f u v w = trop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w)"
  by (transfer, simp)

lemma subst_qtop [usubst]: "\<sigma> \<dagger> qtop f u v w x = qtop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w) (\<sigma> \<dagger> x)"
  by (transfer, simp)

lemma subst_case_prod [usubst]:
  fixes P :: "'i \<Rightarrow> 'j \<Rightarrow> ('a, '\<alpha>) uexpr"  
  shows "\<sigma> \<dagger> case_prod (\<lambda> x y. P x y) v = case_prod (\<lambda> x y. \<sigma> \<dagger> P x y) v"
  by (simp add: case_prod_beta')

lemma subst_plus [usubst]: "\<sigma> \<dagger> (x + y) = \<sigma> \<dagger> x + \<sigma> \<dagger> y"
  by (simp add: plus_uexpr_def subst_bop)

lemma subst_times [usubst]: "\<sigma> \<dagger> (x * y) = \<sigma> \<dagger> x * \<sigma> \<dagger> y"
  by (simp add: times_uexpr_def subst_bop)

lemma subst_mod [usubst]: "\<sigma> \<dagger> (x mod y) = \<sigma> \<dagger> x mod \<sigma> \<dagger> y"
  by (simp add: mod_uexpr_def usubst)

lemma subst_div [usubst]: "\<sigma> \<dagger> (x div y) = \<sigma> \<dagger> x div \<sigma> \<dagger> y"
  by (simp add: divide_uexpr_def usubst)

lemma subst_minus [usubst]: "\<sigma> \<dagger> (x - y) = \<sigma> \<dagger> x - \<sigma> \<dagger> y"
  by (simp add: minus_uexpr_def subst_bop)

lemma subst_uminus [usubst]: "\<sigma> \<dagger> (- x) = - (\<sigma> \<dagger> x)"
  by (simp add: uminus_uexpr_def subst_uop)

lemma usubst_sgn [usubst]: "\<sigma> \<dagger> sgn x = sgn (\<sigma> \<dagger> x)"
  by (simp add: sgn_uexpr_def subst_uop)

lemma usubst_abs [usubst]: "\<sigma> \<dagger> abs x = abs (\<sigma> \<dagger> x)"
  by (simp add: abs_uexpr_def subst_uop)

lemma subst_zero [usubst]: "\<sigma> \<dagger> 0 = 0"
  by (simp add: zero_uexpr_def subst_lit)

lemma subst_one [usubst]: "\<sigma> \<dagger> 1 = 1"
  by (simp add: one_uexpr_def subst_lit)

lemma subst_eq_upred [usubst]: "\<sigma> \<dagger> (x =\<^sub>u y) = (\<sigma> \<dagger> x =\<^sub>u \<sigma> \<dagger> y)"
  by (simp add: eq_upred_def usubst)

text \<open> This laws shows the effect of applying one substitution after another -- we simply
  use function composition to compose them. \<close>
    
lemma subst_subst [usubst]: "\<sigma> \<dagger> \<rho> \<dagger> e = (\<rho> \<circ> \<sigma>) \<dagger> e"
  by (transfer, simp)

text \<open> The next law is similar, but shows how such a substitution is to be applied to every
  updated variable additionally. \<close>
    
lemma subst_upd_comp [usubst]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<rho>(x \<mapsto>\<^sub>s v) \<circ> \<sigma> = (\<rho> \<circ> \<sigma>)(x \<mapsto>\<^sub>s \<sigma> \<dagger> v)"
  by (rule ext, simp add:uexpr_defs subst_upd_uvar_def, transfer, simp)

lemma subst_singleton:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "x \<sharp> \<sigma>"
  shows "\<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = (\<sigma> \<dagger> P)\<lbrakk>v/x\<rbrakk>"
  using assms
  by (simp add: usubst)

lemmas subst_to_singleton = subst_singleton id_subst

subsection \<open> Ordering substitutions \<close>

text \<open> A simplification procedure to reorder substitutions maplets lexicographically by variable syntax \<close>

simproc_setup subst_order ("subst_upd_uvar (subst_upd_uvar \<sigma> x u) y v") =
  \<open>(fn _ => fn ctxt => fn ct => 
        case (Thm.term_of ct) of
          Const ("utp_subst.subst_upd_uvar", _) $ (Const ("utp_subst.subst_upd_uvar", _) $ s $ x $ u) $ y $ v
            => if (YXML.content_of (Syntax.string_of_term ctxt x) > YXML.content_of(Syntax.string_of_term ctxt y))
               then SOME (mk_meta_eq @{thm usubst_upd_comm})
               else NONE  |
          _ => NONE) 
\<close>

subsection \<open> Unrestriction laws \<close>

text \<open> These are the key unrestriction theorems for substitutions and expressions involving substitutions. \<close>
  
lemma unrest_usubst_single [unrest]:
  "\<lbrakk> mwb_lens x; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> P\<lbrakk>v/x\<rbrakk>"
  by (transfer, auto simp add: subst_upd_uvar_def unrest_uexpr_def)

lemma unrest_usubst_id [unrest]:
  "mwb_lens x \<Longrightarrow> x \<sharp> id"
  by (simp add: unrest_usubst_def)

lemma unrest_usubst_upd [unrest]:
  "\<lbrakk> x \<bowtie> y; x \<sharp> \<sigma>; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> \<sigma>(y \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def unrest_usubst_def unrest_uexpr.rep_eq lens_indep_comm)

lemma unrest_subst [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp> (\<sigma> \<dagger> P)"
  by (transfer, simp add: unrest_usubst_def)
    
subsection \<open> Conditional Substitution Laws \<close>
  
lemma usubst_cond_upd_1 [usubst]:
  "\<sigma>(x \<mapsto>\<^sub>s u) \<triangleleft> b \<triangleright>\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s u \<triangleleft> b \<triangleright> v)"
  by (simp add: cond_subst_def subst_upd_uvar_def uexpr_defs, transfer, auto)

lemma usubst_cond_upd_2 [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<rho> \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s u) \<triangleleft> b \<triangleright>\<^sub>s \<rho> = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s u \<triangleleft> b \<triangleright> &x)"
  by (simp add: cond_subst_def subst_upd_uvar_def unrest_usubst_def uexpr_defs, transfer)
     (metis (full_types, hide_lams) id_apply pr_var_def subst_upd_uvar_def usubst_upd_pr_var_id var.rep_eq)
 
lemma usubst_cond_upd_3 [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>)(x \<mapsto>\<^sub>s &x \<triangleleft> b \<triangleright> v)"
  by (simp add: cond_subst_def subst_upd_uvar_def unrest_usubst_def uexpr_defs, transfer)
     (metis (full_types, hide_lams) id_apply pr_var_def subst_upd_uvar_def usubst_upd_pr_var_id var.rep_eq)
    
lemma usubst_cond_id [usubst]:
  "\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<sigma> = \<sigma>"
  by (auto simp add: cond_subst_def)
    
subsection \<open> Parallel Substitution Laws \<close>
    
lemma par_subst_id [usubst]:
  "\<lbrakk> vwb_lens A; vwb_lens B \<rbrakk> \<Longrightarrow> id [A|B]\<^sub>s id = id"
  by (simp add: par_subst_def id_def)

lemma par_subst_left_empty [usubst]:
  "\<lbrakk> vwb_lens A \<rbrakk> \<Longrightarrow> \<sigma> [\<emptyset>|A]\<^sub>s \<rho> = id [\<emptyset>|A]\<^sub>s \<rho>"
  by (simp add: par_subst_def pr_var_def)

lemma par_subst_right_empty [usubst]:
  "\<lbrakk> vwb_lens A \<rbrakk> \<Longrightarrow> \<sigma> [A|\<emptyset>]\<^sub>s \<rho> = \<sigma> [A|\<emptyset>]\<^sub>s id"
  by (simp add: par_subst_def pr_var_def)
    
lemma par_subst_comm:
  "\<lbrakk> A \<bowtie> B \<rbrakk> \<Longrightarrow> \<sigma> [A|B]\<^sub>s \<rho> = \<rho> [B|A]\<^sub>s \<sigma>"
  by (simp add: par_subst_def lens_override_def lens_indep_comm)
      
lemma par_subst_upd_left_in [usubst]:
  "\<lbrakk> vwb_lens A; A \<bowtie> B; x \<subseteq>\<^sub>L A \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) [A|B]\<^sub>s \<rho> = (\<sigma> [A|B]\<^sub>s \<rho>)(x \<mapsto>\<^sub>s v)"
  by (simp add: par_subst_def subst_upd_uvar_def lens_override_put_right_in)
     (simp add: lens_indep_comm lens_override_def sublens_pres_indep)

lemma par_subst_upd_left_out [usubst]:
  "\<lbrakk> vwb_lens A; x \<bowtie> A \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) [A|B]\<^sub>s \<rho> = (\<sigma> [A|B]\<^sub>s \<rho>)"
  by (simp add: par_subst_def subst_upd_uvar_def lens_override_put_right_out)
     
lemma par_subst_upd_right_in [usubst]:
  "\<lbrakk> vwb_lens B; A \<bowtie> B; x \<subseteq>\<^sub>L B \<rbrakk> \<Longrightarrow> \<sigma> [A|B]\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> [A|B]\<^sub>s \<rho>)(x \<mapsto>\<^sub>s v)"
  using lens_indep_sym par_subst_comm par_subst_upd_left_in by fastforce

lemma par_subst_upd_right_out [usubst]:
  "\<lbrakk> vwb_lens B; A \<bowtie> B; x \<bowtie> B \<rbrakk> \<Longrightarrow> \<sigma> [A|B]\<^sub>s \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> [A|B]\<^sub>s \<rho>)"
  by (simp add: par_subst_comm par_subst_upd_left_out)
    
end


  