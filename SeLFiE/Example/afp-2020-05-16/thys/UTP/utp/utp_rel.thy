section \<open> Alphabetised Relations \<close>

theory utp_rel
imports
  utp_pred_laws
  utp_healthy
  utp_lift
  utp_tactics
begin

text \<open> An alphabetised relation is simply a predicate whose state-space is a product type. In this
  theory we construct the core operators of the relational calculus, and prove a libary of 
  associated theorems, based on Chapters 2 and 5 of the UTP book~\cite{Hoare&98}. \<close>
  
subsection \<open> Relational Alphabets \<close>
  
text \<open> We set up convenient syntax to refer to the input and output parts of the alphabet, as is
  common in UTP. Since we are in a product space, these are simply the lenses @{term "fst\<^sub>L"} and
  @{term "snd\<^sub>L"}. \<close>
  
definition in\<alpha> :: "('\<alpha> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "in\<alpha> = fst\<^sub>L"

definition out\<alpha> :: "('\<beta> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "out\<alpha> = snd\<^sub>L"

lemma in\<alpha>_uvar [simp]: "vwb_lens in\<alpha>"
  by (unfold_locales, auto simp add: in\<alpha>_def)

lemma out\<alpha>_uvar [simp]: "vwb_lens out\<alpha>"
  by (unfold_locales, auto simp add: out\<alpha>_def)

lemma var_in_alpha [simp]: "x ;\<^sub>L in\<alpha> = ivar x"
  by (simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma var_out_alpha [simp]: "x ;\<^sub>L out\<alpha> = ovar x"
  by (simp add: out\<alpha>_def out_var_def snd_lens_def)

lemma drop_pre_inv [simp]: "\<lbrakk> out\<alpha> \<sharp> p \<rbrakk> \<Longrightarrow> \<lceil>\<lfloor>p\<rfloor>\<^sub><\<rceil>\<^sub>< = p"
  by (pred_simp)

lemma usubst_lookup_ivar_unrest [usubst]:
  "in\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s (ivar x) = $x"
  by (rel_simp, metis fstI)

lemma usubst_lookup_ovar_unrest [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s (ovar x) = $x\<acute>"
  by (rel_simp, metis sndI)
    
lemma out_alpha_in_indep [simp]:
  "out\<alpha> \<bowtie> in_var x" "in_var x \<bowtie> out\<alpha>"
  by (simp_all add: in_var_def out\<alpha>_def lens_indep_def fst_lens_def snd_lens_def lens_comp_def)

lemma in_alpha_out_indep [simp]:
  "in\<alpha> \<bowtie> out_var x" "out_var x \<bowtie> in\<alpha>"
  by (simp_all add: in_var_def in\<alpha>_def lens_indep_def fst_lens_def lens_comp_def)

text \<open> The following two functions lift a predicate substitution to a relational one. \<close>
    
abbreviation usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> \<sigma> \<oplus>\<^sub>s in\<alpha>"

abbreviation usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) usubst \<Rightarrow> '\<alpha> usubst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s \<equiv> \<sigma> \<restriction>\<^sub>s in\<alpha>"
    
text \<open> The alphabet of a relation then consists wholly of the input and output portions. \<close>

lemma alpha_in_out:
  "\<Sigma> \<approx>\<^sub>L in\<alpha> +\<^sub>L out\<alpha>"
  by (simp add: fst_snd_id_lens in\<alpha>_def lens_equiv_refl out\<alpha>_def)

subsection \<open> Relational Types and Operators \<close>

text \<open> We create type synonyms for conditions (which are simply predicates) -- i.e. relations
  without dashed variables --, alphabetised relations where the input and output alphabet can
  be different, and finally homogeneous relations. \<close>
  
type_synonym '\<alpha> cond        = "'\<alpha> upred"
type_synonym ('\<alpha>, '\<beta>) urel  = "('\<alpha> \<times> '\<beta>) upred"
type_synonym '\<alpha> hrel        = "('\<alpha> \<times> '\<alpha>) upred"
type_synonym ('a, '\<alpha>) hexpr = "('a, '\<alpha> \<times> '\<alpha>) uexpr"
  
translations
  (type) "('\<alpha>, '\<beta>) urel" <= (type) "('\<alpha> \<times> '\<beta>) upred"

text \<open> We set up some overloaded constants for sequential composition and the identity in case
  we want to overload their definitions later. \<close>
  
consts
  useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 61)
  uassigns :: "'a usubst \<Rightarrow> 'b" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'a" ("II")
  
text \<open> We define a specialised version of the conditional where the condition can refer only to
  undashed variables, as is usually the case in programs, but not universally in UTP models. 
  We implement this by lifting the condition predicate into the relational state-space with
  construction @{term "\<lceil>b\<rceil>\<^sub><"}. \<close>
  
definition lift_rcond ("\<lceil>_\<rceil>\<^sub>\<leftarrow>") where
[upred_defs]: "\<lceil>b\<rceil>\<^sub>\<leftarrow> = \<lceil>b\<rceil>\<^sub><"
    
abbreviation 
  rcond :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<alpha>, '\<beta>) urel"
  ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r/ _)" [52,0,53] 52)
  where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>\<leftarrow> \<triangleright> Q)"
    
text \<open> Sequential composition is heterogeneous, and simply requires that the output alphabet
  of the first matches then input alphabet of the second. We define it by lifting HOL's 
  built-in relational composition operator (@{term "(O)"}). Since this returns a set, the
  definition states that the state binding $b$ is an element of this set. \<close>
  
lift_definition seqr::"('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<beta>, '\<gamma>) urel \<Rightarrow> ('\<alpha> \<times> '\<gamma>) upred"
is "\<lambda> P Q b. b \<in> ({p. P p} O {q. Q q})" .

adhoc_overloading
  useq seqr
   
text \<open> We also set up a homogeneous sequential composition operator, and versions of @{term true}
  and @{term false} that are explicitly typed by a homogeneous alphabet. \<close>

abbreviation seqh :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" (infixr ";;\<^sub>h" 61) where
"seqh P Q \<equiv> (P ;; Q)"

abbreviation truer :: "'\<alpha> hrel" ("true\<^sub>h") where
"truer \<equiv> true"

abbreviation falser :: "'\<alpha> hrel" ("false\<^sub>h") where
"falser \<equiv> false"
  
text \<open> We define the relational converse operator as an alphabet extrusion on the bijective
  lens @{term swap\<^sub>L} that swaps the elements of the product state-space. \<close>
    
abbreviation conv_r :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta> \<times> '\<alpha>) uexpr" ("_\<^sup>-" [999] 999)
where "conv_r e \<equiv> e \<oplus>\<^sub>p swap\<^sub>L"

text \<open> Assignment is defined using substitutions, where latter defines what each variable should
  map to. This approach, which is originally due to Back~\cite{Back1998}, permits more general 
  assignment expressions. The definition of the operator identifies the after state binding, $b'$, 
  with the substitution function applied to the before state binding $b$. \<close>
  
lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel"
  is "\<lambda> \<sigma> (b, b'). b' = \<sigma>(b)" .

adhoc_overloading
  uassigns assigns_r
    
text \<open> Relational identity, or skip, is then simply an assignment with the identity substitution:
  it simply identifies all variables. \<close>
    
definition skip_r :: "'\<alpha> hrel" where
[urel_defs]: "skip_r = assigns_r id"

adhoc_overloading
  uskip skip_r

text \<open> Non-deterministic assignment, also known as ``choose'', assigns an arbitrarily chosen value 
  to the given variable \<close>

definition nd_assign :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "nd_assign x = (\<Sqinter> v \<bullet> assigns_r [x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>])"

text \<open> We set up iterated sequential composition which iterates an indexed predicate over the
  elements of a list. \<close>
  
definition seqr_iter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b hrel) \<Rightarrow> 'b hrel" where
[urel_defs]: "seqr_iter xs P = foldr (\<lambda> i Q. P(i) ;; Q) xs II"
  
text \<open> A singleton assignment simply applies a singleton substitution function, and similarly
  for a double assignment. \<close>

abbreviation assign_r :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
where "assign_r x v \<equiv> \<langle>[x \<mapsto>\<^sub>s v]\<rangle>\<^sub>a"

abbreviation assign_2_r ::
  "('t1 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t2 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
where "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

text \<open> We also define the alphabetised skip operator that identifies all input and output variables
  in the given alphabet lens. All other variables are unrestricted. We also set up syntax for it. \<close>
  
definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>'\<alpha> hrel" where
[urel_defs]: "skip_ra v = ($v\<acute> =\<^sub>u $v)"

text \<open> Similarly, we define the alphabetised assignment operator. \<close>

definition assigns_ra :: "'\<alpha> usubst \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^bsub>_\<^esub>") where
"\<langle>\<sigma>\<rangle>\<^bsub>a\<^esub> = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> skip_ra a)"

text \<open> Assumptions ($c^{\top}$) and assertions ($c_{\bot}$) are encoded as conditionals. An assumption
  behaves like skip if the condition is true, and otherwise behaves like @{term false} (miracle).
  An assertion is the same, but yields @{term true}, which is an abort. They are the same as
  tests, as in Kleene Algebra with Tests~\cite{kozen1997kleene,Armstrong2015} 
  (KAT), which embeds a Boolean algebra into a Kleene algebra to represent conditions. \<close>

definition rassume :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "rassume c = II \<triangleleft> c \<triangleright>\<^sub>r false"

definition rassert :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "rassert c = II \<triangleleft> c \<triangleright>\<^sub>r true"

text \<open> We define two variants of while loops based on strongest and weakest fixed points. The former
  is @{term false} for an infinite loop, and the latter is @{term true}. \<close>

definition while_top :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "while_top b P = (\<nu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

definition while_bot :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "while_bot b P = (\<mu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

text \<open> While loops with invariant decoration (cf. \cite{Armstrong2015}) -- partial correctness. \<close>

definition while_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "while_inv b p S = while_top b S"

text \<open> While loops with invariant decoration -- total correctness. \<close>

definition while_inv_bot :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel"  where
[urel_defs]: "while_inv_bot b p S = while_bot b S"  

text \<open> While loops with invariant and variant decorations -- total correctness. \<close>

definition while_vrt :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel"  where
[urel_defs]: "while_vrt b p v S = while_bot b S"

syntax
  "_uassume"        :: "uexp \<Rightarrow> logic" ("[_]\<^sup>\<top>")
  "_uassume"        :: "uexp \<Rightarrow> logic" ("?[_]")
  "_uassert"        :: "uexp \<Rightarrow> logic" ("{_}\<^sub>\<bottom>")
  "_uwhile"         :: "uexp \<Rightarrow> logic \<Rightarrow> logic" ("while\<^sup>\<top> _ do _ od")
  "_uwhile_top"     :: "uexp \<Rightarrow> logic \<Rightarrow> logic" ("while _ do _ od")
  "_uwhile_bot"     :: "uexp \<Rightarrow> logic \<Rightarrow> logic" ("while\<^sub>\<bottom> _ do _ od")
  "_uwhile_inv"     :: "uexp \<Rightarrow> uexp \<Rightarrow> logic \<Rightarrow> logic" ("while _ invr _ do _ od")
  "_uwhile_inv_bot" :: "uexp \<Rightarrow> uexp \<Rightarrow> logic \<Rightarrow> logic" ("while\<^sub>\<bottom> _ invr _ do _ od" 71)
  "_uwhile_vrt"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> logic \<Rightarrow> logic" ("while _ invr _ vrt _ do _ od")

translations
  "_uassume b" == "CONST rassume b"
  "_uassert b" == "CONST rassert b"
  "_uwhile b P" == "CONST while_top b P"
  "_uwhile_top b P" == "CONST while_top b P"
  "_uwhile_bot b P" == "CONST while_bot b P"
  "_uwhile_inv b p S" == "CONST while_inv b p S"
  "_uwhile_inv_bot b p S" == "CONST while_inv_bot b p S"
  "_uwhile_vrt b p v S" == "CONST while_vrt b p v S"

text \<open> We implement a poor man's version of alphabet restriction that hides a variable within 
  a relation. \<close>

definition rel_var_res :: "'\<alpha> hrel \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" (infix "\<restriction>\<^sub>\<alpha>" 80) where
[urel_defs]: "P \<restriction>\<^sub>\<alpha> x = (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P)"

text \<open> Alphabet extension and restriction add additional variables by the given lens in both
  their primed and unprimed versions. \<close>
  
definition rel_aext :: "'\<beta> hrel \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" 
where [upred_defs]: "rel_aext P a = P \<oplus>\<^sub>p (a \<times>\<^sub>L a)"

definition rel_ares :: "'\<alpha> hrel \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> hrel" 
  where [upred_defs]: "rel_ares P a = (P \<restriction>\<^sub>p (a \<times> a))"

text \<open> We next describe frames and antiframes with the help of lenses. A frame states that $P$
  defines how variables in $a$ changed, and all those outside of $a$ remain the same. An
  antiframe describes the converse: all variables outside $a$ are specified by $P$, and all those in
  remain the same. For more information please see \cite{Morgan90a}.\<close>

definition frame :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "frame a P = (P \<and> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v \<oplus> $\<^bold>v\<acute> on &a)"
  
definition antiframe :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "antiframe a P = (P \<and> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v\<acute> \<oplus> $\<^bold>v on &a)"

text \<open> Frame extension combines alphabet extension with the frame operator to both add additional 
  variables and then frame those. \<close>

definition rel_frext :: "('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> hrel \<Rightarrow> '\<alpha> hrel"  where
[upred_defs]: "rel_frext a P = frame a (rel_aext P a)"

text \<open> The nameset operator can be used to hide a portion of the after-state that lies outside
  the lens $a$. It can be useful to partition a relation's variables in order to conjoin it
  with another relation. \<close>

definition nameset :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "nameset a P = (P \<restriction>\<^sub>v {$\<^bold>v,$a\<acute>})" 

subsection \<open> Syntax Translations \<close>
    
syntax
  \<comment> \<open> Alternative traditional conditional syntax \<close>
  "_utp_if" :: "uexp \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>u (_)/ then (_)/ else (_))" [0, 0, 71] 71)
  \<comment> \<open> Iterated sequential composition \<close>
  "_seqr_iter" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> '\<sigma> hrel \<Rightarrow> '\<sigma> hrel" ("(3;; _ : _ \<bullet>/ _)" [0, 0, 10] 10)
  \<comment> \<open> Single and multiple assignement \<close>
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  ("'(_') := '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  (infixr ":=" 62)
  \<comment> \<open> Non-deterministic assignment \<close>
  "_nd_assign" :: "svids \<Rightarrow> logic" ("_ := *" [62] 62)
  \<comment> \<open> Substitution constructor \<close>
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"
  \<comment> \<open> Alphabetised skip \<close>
  "_skip_ra"        :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")
  \<comment> \<open> Frame \<close>
  "_frame"          :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [99,0] 100)
  \<comment> \<open> Antiframe \<close>
  "_antiframe"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:\<lbrakk>_\<rbrakk>" [79,0] 80)
  \<comment> \<open> Relational Alphabet Extension \<close>
  "_rel_aext"  :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\<oplus>\<^sub>r" 90)
  \<comment> \<open> Relational Alphabet Restriction \<close>
  "_rel_ares"  :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\<restriction>\<^sub>r" 90)
  \<comment> \<open> Frame Extension \<close>
  "_rel_frext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sup>+" [99,0] 100)
  \<comment> \<open> Nameset \<close>
  "_nameset"        :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("ns _ \<bullet> _" [0,999] 999)

translations
  "_utp_if b P Q" => "P \<triangleleft> b \<triangleright>\<^sub>r Q"
  ";; x : l \<bullet> P" \<rightleftharpoons> "(CONST seqr_iter) l (\<lambda>x. P)"
  "_mk_usubst \<sigma> (_svid_unit x) v" \<rightleftharpoons> "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" \<rightleftharpoons> "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST uassigns (_mk_usubst (CONST id) xs vs)"
  "_assignment x v" <= "CONST uassigns (CONST subst_upd (CONST id) x v)"
  "_assignment x v" <= "_assignment (_spvar x) v"
  "_nd_assign x" => "CONST nd_assign (_mk_svid_list x)"
  "_nd_assign x" <= "CONST nd_assign x"
  "x,y := u,v" <= "CONST uassigns (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"
  "_skip_ra v" \<rightleftharpoons> "CONST skip_ra v"
  "_frame x P" => "CONST frame x P"
  "_frame (_salphaset (_salphamk x)) P" <= "CONST frame x P"
  "_antiframe x P" => "CONST antiframe x P"
  "_antiframe (_salphaset (_salphamk x)) P" <= "CONST antiframe x P"
  "_nameset x P" == "CONST nameset x P"
  "_rel_aext P a" == "CONST rel_aext P a"
  "_rel_ares P a" == "CONST rel_ares P a"
  "_rel_frext a P" == "CONST rel_frext a P"

text \<open> The following code sets up pretty-printing for homogeneous relational expressions. We cannot 
  do this via the ``translations'' command as we only want the rule to apply when the input and output
  alphabet types are the same. The code has to deconstruct a @{typ "('a, '\<alpha>) uexpr"} type, determine 
  that it is relational (product alphabet), and then checks if the types \emph{alpha} and \emph{beta} 
  are the same. If they are, the type is printed as a \emph{hexpr}. Otherwise, we have no match. 
  We then set up a regular translation for the \emph{hrel} type that uses this. \<close>
  
print_translation \<open>
let
fun tr' ctxt [ a
            , Const (@{type_syntax "prod"},_) $ alpha $ beta ] = 
  if (alpha = beta) 
    then Syntax.const @{type_syntax "hexpr"} $ a $ alpha
    else raise Match;
in [(@{type_syntax "uexpr"},tr')]
end
\<close>
  
translations
  (type) "'\<alpha> hrel" <= (type) "(bool, '\<alpha>) hexpr"
  
subsection \<open> Relation Properties \<close>
  
text \<open> We describe some properties of relations, including functional and injective relations. We
  also provide operators for extracting the domain and range of a UTP relation. \<close>

definition ufunctional :: "('a, 'b) urel \<Rightarrow> bool"
where [urel_defs]: "ufunctional R \<longleftrightarrow> II \<sqsubseteq> R\<^sup>- ;; R"

definition uinj :: "('a, 'b) urel \<Rightarrow> bool"
where [urel_defs]: "uinj R \<longleftrightarrow> II \<sqsubseteq> R ;; R\<^sup>-"
  
definition Dom :: "'\<alpha> hrel \<Rightarrow> '\<alpha> upred" 
where [upred_defs]: "Dom P = \<lfloor>\<exists> $\<^bold>v\<acute> \<bullet> P\<rfloor>\<^sub><"

definition Ran :: "'\<alpha> hrel \<Rightarrow> '\<alpha> upred" 
where [upred_defs]: "Ran P = \<lfloor>\<exists> $\<^bold>v \<bullet> P\<rfloor>\<^sub>>"
  
\<comment> \<open> Configuration for UTP tactics. \<close>

update_uexpr_rep_eq_thms \<comment> \<open> Reread @{text rep_eq} theorems. \<close>

subsection \<open> Introduction laws \<close>

lemma urel_refine_ext:
  "\<lbrakk> \<And> s s'. P\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>/$\<^bold>v,$\<^bold>v\<acute>\<rbrakk> \<sqsubseteq> Q\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>/$\<^bold>v,$\<^bold>v\<acute>\<rbrakk> \<rbrakk> \<Longrightarrow> P \<sqsubseteq> Q"
  by (rel_auto)

lemma urel_eq_ext:
  "\<lbrakk> \<And> s s'. P\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>/$\<^bold>v,$\<^bold>v\<acute>\<rbrakk> = Q\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>/$\<^bold>v,$\<^bold>v\<acute>\<rbrakk> \<rbrakk> \<Longrightarrow> P = Q"
  by (rel_auto)

subsection \<open> Unrestriction Laws \<close>

lemma unrest_iuvar [unrest]: "out\<alpha> \<sharp> $x"
  by (metis fst_snd_lens_indep lift_pre_var out\<alpha>_def unrest_aext_indep)

lemma unrest_ouvar [unrest]: "in\<alpha> \<sharp> $x\<acute>"
  by (metis in\<alpha>_def lift_post_var snd_fst_lens_indep unrest_aext_indep)

lemma unrest_semir_undash [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "$x \<sharp> P"
  shows "$x \<sharp> P ;; Q"
  using assms by (rel_auto)

lemma unrest_semir_dash [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "$x\<acute> \<sharp> Q"
  shows "$x\<acute> \<sharp> P ;; Q"
  using assms by (rel_auto)

lemma unrest_cond [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> b; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<triangleleft> b \<triangleright> Q"
  by (rel_auto)

lemma unrest_lift_rcond [unrest]:
  "x \<sharp> \<lceil>b\<rceil>\<^sub>< \<Longrightarrow> x \<sharp> \<lceil>b\<rceil>\<^sub>\<leftarrow>"
  by (simp add: lift_rcond_def)
    
lemma unrest_in\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; in\<alpha> \<sharp> (P :: ('a, ('\<alpha> \<times> '\<beta>)) uexpr) \<rbrakk> \<Longrightarrow> $x \<sharp> P"
  by (rel_auto)

lemma unrest_out\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; out\<alpha> \<sharp> (P :: ('a, ('\<alpha> \<times> '\<beta>)) uexpr) \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P"
  by (rel_auto)

lemma unrest_pre_out\<alpha> [unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub><"
  by (transfer, auto simp add: out\<alpha>_def)

lemma unrest_post_in\<alpha> [unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>>"
  by (transfer, auto simp add: in\<alpha>_def)

lemma unrest_pre_in_var [unrest]:
  "x \<sharp> p1 \<Longrightarrow> $x \<sharp> \<lceil>p1\<rceil>\<^sub><"
  by (transfer, simp)

lemma unrest_post_out_var [unrest]:
  "x \<sharp> p1 \<Longrightarrow> $x\<acute> \<sharp> \<lceil>p1\<rceil>\<^sub>>"
  by (transfer, simp)

lemma unrest_convr_out\<alpha> [unrest]:
  "in\<alpha> \<sharp> p \<Longrightarrow> out\<alpha> \<sharp> p\<^sup>-"
  by (transfer, auto simp add: lens_defs)

lemma unrest_convr_in\<alpha> [unrest]:
  "out\<alpha> \<sharp> p \<Longrightarrow> in\<alpha> \<sharp> p\<^sup>-"
  by (transfer, auto simp add: lens_defs)

lemma unrest_in_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

lemma unrest_out_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

lemma unrest_out_alpha_usubst_rel_lift [unrest]: 
  "out\<alpha> \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>s"
  by (rel_auto)
    
lemma unrest_in_rel_aext [unrest]: "x \<bowtie> y \<Longrightarrow> $y \<sharp> P \<oplus>\<^sub>r x"
  by (simp add: rel_aext_def unrest_aext_indep)

lemma unrest_out_rel_aext [unrest]: "x \<bowtie> y \<Longrightarrow> $y\<acute> \<sharp> P \<oplus>\<^sub>r x"
  by (simp add: rel_aext_def unrest_aext_indep)

lemma rel_aext_false [alpha]:
  "false \<oplus>\<^sub>r a = false"
  by (pred_auto)

lemma rel_aext_seq [alpha]:
  "weak_lens a \<Longrightarrow> (P ;; Q) \<oplus>\<^sub>r a = (P \<oplus>\<^sub>r a ;; Q \<oplus>\<^sub>r a)"
  apply (rel_auto)
  apply (rename_tac aa b y)
  apply (rule_tac x="create\<^bsub>a\<^esub> y" in exI)
  apply (simp)
  done

lemma rel_aext_cond [alpha]:
  "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<oplus>\<^sub>r a = (P \<oplus>\<^sub>r a \<triangleleft> b \<oplus>\<^sub>p a \<triangleright>\<^sub>r Q \<oplus>\<^sub>r a)"
  by (rel_auto)
    
subsection \<open> Substitution laws \<close>

lemma subst_seq_left [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = (\<sigma> \<dagger> P) ;; Q"
  by (rel_simp, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

lemma subst_seq_right [usubst]:
  "in\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = P ;; (\<sigma> \<dagger> Q)"
  by (rel_simp, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

text \<open> The following laws support substitution in heterogeneous relations for polymorphically
  typed literal expressions. These cannot be supported more generically due to limitations
  in HOL's type system. The laws are presented in a slightly strange way so as to be as
  general as possible. \<close>

lemma bool_seqr_laws [usubst]:
  fixes x :: "(bool \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>true/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>false/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>true/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>false/$x\<acute>\<rbrakk>)"
    by (rel_auto)+

lemma zero_one_seqr_laws [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 0) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>0/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 1) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>1/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 0) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>0/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 1) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>1/$x\<acute>\<rbrakk>)"
    by (rel_auto)+

lemma numeral_seqr_laws [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s numeral n) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>numeral n/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s numeral n) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>numeral n/$x\<acute>\<rbrakk>)"
  by (rel_auto)+

lemma usubst_condr [usubst]:
  "\<sigma> \<dagger> (P \<triangleleft> b \<triangleright> Q) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> b \<triangleright> \<sigma> \<dagger> Q)"
  by (rel_auto)

lemma subst_skip_r [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> II = \<langle>\<lfloor>\<sigma>\<rfloor>\<^sub>s\<rangle>\<^sub>a"
  by (rel_simp, (metis (mono_tags, lifting) prod.sel(1) sndI surjective_pairing)+)

lemma subst_pre_skip [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II = \<langle>\<sigma>\<rangle>\<^sub>a"
  by (rel_auto)
    
lemma subst_rel_lift_seq [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> (P ;; Q) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P) ;; Q"
  by (rel_auto)
  
lemma subst_rel_lift_comp [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s \<circ> \<lceil>\<rho>\<rceil>\<^sub>s = \<lceil>\<sigma> \<circ> \<rho>\<rceil>\<^sub>s"
  by (rel_auto)
    
lemma usubst_upd_in_comp [usubst]:
  "\<sigma>(&in\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x \<mapsto>\<^sub>s v)"
  by (simp add: pr_var_def fst_lens_def in\<alpha>_def in_var_def)

lemma usubst_upd_out_comp [usubst]:
  "\<sigma>(&out\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x\<acute> \<mapsto>\<^sub>s v)"
  by (simp add: pr_var_def out\<alpha>_def out_var_def snd_lens_def)

lemma subst_lift_upd [alpha]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<lceil>\<sigma>(x \<mapsto>\<^sub>s v)\<rceil>\<^sub>s = \<lceil>\<sigma>\<rceil>\<^sub>s($x \<mapsto>\<^sub>s \<lceil>v\<rceil>\<^sub><)"
  by (simp add: alpha usubst, simp add: pr_var_def fst_lens_def in\<alpha>_def in_var_def)

lemma subst_drop_upd [alpha]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<lfloor>\<sigma>($x \<mapsto>\<^sub>s v)\<rfloor>\<^sub>s = \<lfloor>\<sigma>\<rfloor>\<^sub>s(x \<mapsto>\<^sub>s \<lfloor>v\<rfloor>\<^sub><)"
  by pred_simp

lemma subst_lift_pre [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>b\<rceil>\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub><"
  by (metis apply_subst_ext fst_vwb_lens in\<alpha>_def) 
    
lemma unrest_usubst_lift_in [unrest]:
  "x \<sharp> P \<Longrightarrow> $x \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by pred_simp

lemma unrest_usubst_lift_out [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "$x\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by pred_simp

lemma subst_lift_cond [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>s\<rceil>\<^sub>\<leftarrow> = \<lceil>\<sigma> \<dagger> s\<rceil>\<^sub>\<leftarrow>"
  by (rel_auto)

lemma msubst_seq [usubst]: "(P(x) ;; Q(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk> = ((P(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk> ;; (Q(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk>)"
  by (rel_auto)  

subsection \<open> Alphabet laws \<close>

lemma aext_cond [alpha]:
  "(P \<triangleleft> b \<triangleright> Q) \<oplus>\<^sub>p a = ((P \<oplus>\<^sub>p a) \<triangleleft> (b \<oplus>\<^sub>p a) \<triangleright> (Q \<oplus>\<^sub>p a))"
  by (rel_auto)

lemma aext_seq [alpha]:
  "wb_lens a \<Longrightarrow> ((P ;; Q) \<oplus>\<^sub>p (a \<times>\<^sub>L a)) = ((P \<oplus>\<^sub>p (a \<times>\<^sub>L a)) ;; (Q \<oplus>\<^sub>p (a \<times>\<^sub>L a)))"
  by (rel_simp, metis wb_lens_weak weak_lens.put_get)

lemma rcond_lift_true [simp]:
  "\<lceil>true\<rceil>\<^sub>\<leftarrow> = true"
  by rel_auto

lemma rcond_lift_false [simp]:
  "\<lceil>false\<rceil>\<^sub>\<leftarrow> = false"
  by rel_auto

lemma rel_ares_aext [alpha]: 
  "vwb_lens a \<Longrightarrow> (P \<oplus>\<^sub>r a) \<restriction>\<^sub>r a = P"
  by (rel_auto)

lemma rel_aext_ares [alpha]:
  "{$a, $a\<acute>} \<natural> P \<Longrightarrow> P \<restriction>\<^sub>r a \<oplus>\<^sub>r a = P"
  by (rel_auto)

lemma rel_aext_uses [unrest]:
  "vwb_lens a \<Longrightarrow> {$a, $a\<acute>} \<natural> (P \<oplus>\<^sub>r a)"
  by (rel_auto)    
    
subsection \<open> Relational unrestriction \<close>

text \<open> Relational unrestriction states that a variable is both unchanged by a relation, and is
  not "read" by the relation. \<close>

definition RID :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel"
where "RID x P = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x)"
  
declare RID_def [urel_defs]

lemma RID1: "vwb_lens x \<Longrightarrow> (\<forall> v. x := \<guillemotleft>v\<guillemotright> ;; P = P ;; x := \<guillemotleft>v\<guillemotright>) \<Longrightarrow> RID(x)(P) = P"
  apply (rel_auto)
   apply (metis vwb_lens.put_eq)
  apply (metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)
  done
    
lemma RID2: "vwb_lens x \<Longrightarrow> x := \<guillemotleft>v\<guillemotright> ;; RID(x)(P) = RID(x)(P) ;; x := \<guillemotleft>v\<guillemotright>"
  apply (rel_auto)
   apply (metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put wb_lens_def weak_lens.put_get)
  apply blast
  done
    
lemma RID_assign_commute:
  "vwb_lens x \<Longrightarrow> P = RID(x)(P) \<longleftrightarrow> (\<forall> v. x := \<guillemotleft>v\<guillemotright> ;; P = P ;; x := \<guillemotleft>v\<guillemotright>)"
  by (metis RID1 RID2)
  
lemma RID_idem:
  "mwb_lens x \<Longrightarrow> RID(x)(RID(x)(P)) = RID(x)(P)"
  by (rel_auto)

lemma RID_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RID(x)(P) \<sqsubseteq> RID(x)(Q)"
  by (rel_auto)

lemma RID_pr_var [simp]: 
  "RID (pr_var x) = RID x"
  by (simp add: pr_var_def)
    
lemma RID_skip_r:
  "vwb_lens x \<Longrightarrow> RID(x)(II) = II"
  apply (rel_auto) using vwb_lens.put_eq by fastforce

lemma skip_r_RID [closure]: "vwb_lens x \<Longrightarrow> II is RID(x)"
  by (simp add: Healthy_def RID_skip_r)
    
lemma RID_disj:
  "RID(x)(P \<or> Q) = (RID(x)(P) \<or> RID(x)(Q))"
  by (rel_auto)
    
lemma disj_RID [closure]: "\<lbrakk> P is RID(x); Q is RID(x) \<rbrakk> \<Longrightarrow> (P \<or> Q) is RID(x)"
  by (simp add: Healthy_def RID_disj)

lemma RID_conj:
  "vwb_lens x \<Longrightarrow> RID(x)(RID(x)(P) \<and> RID(x)(Q)) = (RID(x)(P) \<and> RID(x)(Q))"
  by (rel_auto)

lemma conj_RID [closure]: "\<lbrakk> vwb_lens x; P is RID(x); Q is RID(x) \<rbrakk> \<Longrightarrow> (P \<and> Q) is RID(x)"
  by (metis Healthy_if Healthy_intro RID_conj)
    
lemma RID_assigns_r_diff:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> RID(x)(\<langle>\<sigma>\<rangle>\<^sub>a) = \<langle>\<sigma>\<rangle>\<^sub>a"
  apply (rel_auto)
   apply (metis vwb_lens.put_eq)
  apply (metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)
  done

lemma assigns_r_RID [closure]: "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a is RID(x)"
  by (simp add: Healthy_def RID_assigns_r_diff)
  
lemma RID_assign_r_same:
  "vwb_lens x \<Longrightarrow> RID(x)(x := v) = II"
  apply (rel_auto)
  using vwb_lens.put_eq apply fastforce
  done

lemma RID_seq_left:
  assumes "vwb_lens x"
  shows "RID(x)(RID(x)(P) ;; Q) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(RID(x)(P) ;; Q) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; Q) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> (\<exists> $x \<bullet> $x\<acute> =\<^sub>u $x)) ;; (\<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_auto)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_auto)
     apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
    done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by (rel_auto)
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma RID_seq_right:
  assumes "vwb_lens x"
  shows "RID(x)(P ;; RID(x)(Q)) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(P ;; RID(x)(Q)) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = (((\<exists> $x \<bullet>  P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> (\<exists> $x\<acute> \<bullet> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_auto)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_auto)
     apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
    done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp robust, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by (rel_auto)
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma seqr_RID_closed [closure]: "\<lbrakk> vwb_lens x; P is RID(x); Q is RID(x) \<rbrakk> \<Longrightarrow> P ;; Q is RID(x)"
  by (metis Healthy_def RID_seq_right)
  
definition unrest_relation :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> bool" (infix "\<sharp>\<sharp>" 20)
where "(x \<sharp>\<sharp> P) \<longleftrightarrow> (P is RID(x))"

declare unrest_relation_def [urel_defs]

lemma runrest_assign_commute:
  "\<lbrakk> vwb_lens x; x \<sharp>\<sharp> P \<rbrakk> \<Longrightarrow> x := \<guillemotleft>v\<guillemotright> ;; P = P ;; x := \<guillemotleft>v\<guillemotright>"
  by (metis RID2 Healthy_def unrest_relation_def)

lemma runrest_ident_var:
  assumes "x \<sharp>\<sharp> P"
  shows "($x \<and> P) = (P \<and> $x\<acute>)"
proof -
  have "P = ($x\<acute> =\<^sub>u $x \<and> P)"
    by (metis RID_def assms Healthy_def unrest_relation_def utp_pred_laws.inf.cobounded2 utp_pred_laws.inf_absorb2)
  moreover have "($x\<acute> =\<^sub>u $x \<and> ($x \<and> P)) = ($x\<acute> =\<^sub>u $x \<and> (P \<and> $x\<acute>))"
    by (rel_auto)
  ultimately show ?thesis
    by (metis utp_pred_laws.inf.assoc utp_pred_laws.inf_left_commute)
qed

lemma skip_r_runrest [unrest]:
  "vwb_lens x \<Longrightarrow> x \<sharp>\<sharp> II"
  by (simp add: unrest_relation_def closure)

lemma assigns_r_runrest:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: unrest_relation_def closure)

lemma seq_r_runrest [unrest]:
  assumes "vwb_lens x" "x \<sharp>\<sharp> P" "x \<sharp>\<sharp> Q"
  shows "x \<sharp>\<sharp> (P ;; Q)"
  using assms by (simp add: unrest_relation_def closure )

lemma false_runrest [unrest]: "x \<sharp>\<sharp> false"
  by (rel_auto)

lemma and_runrest [unrest]: "\<lbrakk> vwb_lens x; x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<and> Q)"
  by (metis RID_conj Healthy_def unrest_relation_def)

lemma or_runrest [unrest]: "\<lbrakk> x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<or> Q)"
  by (simp add: RID_disj Healthy_def unrest_relation_def)

end