section \<open> UTP Variables \<close>

theory utp_var
  imports
  "UTP-Toolkit.utp_toolkit"
  utp_parser_utils
begin

text \<open> In this first UTP theory we set up variables, which are are built on lenses~\cite{Foster09,Foster16a}. 
  A large part of this theory is setting up the parser for UTP variable syntax. \<close>

subsection \<open> Initial syntax setup \<close>
  
text \<open> We will overload the square order relation with refinement and also the lattice operators so
  we will turn off these notations. \<close>

purge_notation
  Order.le (infixl "\<sqsubseteq>\<index>" 50) and
  Lattice.sup ("\<Squnion>\<index>_" [90] 90) and
  Lattice.inf ("\<Sqinter>\<index>_" [90] 90) and
  Lattice.join (infixl "\<squnion>\<index>" 65) and
  Lattice.meet (infixl "\<sqinter>\<index>" 70) and
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50) and
  disj  (infixr "|" 30) and
  conj  (infixr "&" 35)

declare fst_vwb_lens [simp]
declare snd_vwb_lens [simp]
declare comp_vwb_lens [simp]
declare lens_indep_left_ext [simp]
declare lens_indep_right_ext [simp]
declare lens_comp_quotient [simp]
declare plus_lens_distr [THEN sym, simp]

subsection \<open> Variable foundations \<close>
  
text \<open> This theory describes the foundational structure of UTP variables, upon which the rest      
  of our model rests. We start by defining alphabets, which following~\cite{Feliachi2010,Feliachi2012}
  in this shallow model are simply represented as types @{typ "'\<alpha>"}, though by convention usually a record
  type where each field corresponds to a variable. UTP variables in this frame are simply modelled 
  as lenses @{typ "'a \<Longrightarrow> '\<alpha>"}, where the view type @{typ "'a"} is the variable type, and the 
  source type \<open>'\<alpha>\<close> is the alphabet or state-space type.

  We define some lifting functions for variables to create input and output variables.
  These simply lift the alphabet to a tuple type since relations will ultimately be defined
  by a tuple alphabet. 
\<close>

definition in_var :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('a \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "in_var x = x ;\<^sub>L fst\<^sub>L"

definition out_var :: "('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "out_var x = x ;\<^sub>L snd\<^sub>L"

text \<open> Variables can also be used to effectively define sets of variables. Here we define the
  the universal alphabet ($\Sigma$) to be the bijective lens @{term "1\<^sub>L"}. This characterises
  the whole of the source type, and thus is effectively the set of all alphabet variables. \<close>

abbreviation (input) univ_alpha :: "('\<alpha> \<Longrightarrow> '\<alpha>)" ("\<Sigma>") where
"univ_alpha \<equiv> 1\<^sub>L"

text \<open> The next construct is vacuous and simply exists to help the parser distinguish predicate
  variables from input and output variables. \<close>

definition pr_var :: "('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('a \<Longrightarrow> '\<beta>)" where
[lens_defs]: "pr_var x = x"

subsection \<open> Variable lens properties \<close>

text \<open> We can now easily show that our UTP variable construction are various classes of 
  well-behaved lens .\<close>

lemma in_var_weak_lens [simp]:
  "weak_lens x \<Longrightarrow> weak_lens (in_var x)"
  by (simp add: comp_weak_lens in_var_def)

lemma in_var_semi_uvar [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (in_var x)"
  by (simp add: comp_mwb_lens in_var_def)

lemma pr_var_weak_lens [simp]:
  "weak_lens x \<Longrightarrow> weak_lens (pr_var x)"
  by (simp add: pr_var_def)

lemma pr_var_mwb_lens [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (pr_var x)"
  by (simp add: pr_var_def)
    
lemma pr_var_vwb_lens [simp]: 
  "vwb_lens x \<Longrightarrow> vwb_lens (pr_var x)"
  by (simp add: pr_var_def)
    
lemma in_var_uvar [simp]:
  "vwb_lens x \<Longrightarrow> vwb_lens (in_var x)"
  by (simp add: in_var_def)

lemma out_var_weak_lens [simp]:
  "weak_lens x \<Longrightarrow> weak_lens (out_var x)"
  by (simp add: comp_weak_lens out_var_def)

lemma out_var_semi_uvar [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (out_var x)"
  by (simp add: comp_mwb_lens out_var_def)

lemma out_var_uvar [simp]:
  "vwb_lens x \<Longrightarrow> vwb_lens (out_var x)"
  by (simp add: out_var_def)
    
text \<open> Moreover, we can show that input and output variables are independent, since they refer
  to different sections of the alphabet. \<close>
    
lemma in_out_indep [simp]:
  "in_var x \<bowtie> out_var y"
  by (simp add: lens_indep_def in_var_def out_var_def fst_lens_def snd_lens_def lens_comp_def)

lemma out_in_indep [simp]:
  "out_var x \<bowtie> in_var y"
  by (simp add: lens_indep_def in_var_def out_var_def fst_lens_def snd_lens_def lens_comp_def)

lemma in_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> in_var x \<bowtie> in_var y"
  by (simp add: in_var_def out_var_def)

lemma out_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> out_var x \<bowtie> out_var y"
  by (simp add: out_var_def)

lemma pr_var_indeps [simp]: 
  "x \<bowtie> y \<Longrightarrow> pr_var x \<bowtie> y"
  "x \<bowtie> y \<Longrightarrow> x \<bowtie> pr_var y"
  by (simp_all add: pr_var_def)
    
lemma prod_lens_indep_in_var [simp]:
  "a \<bowtie> x \<Longrightarrow> a \<times>\<^sub>L b \<bowtie> in_var x"
  by (metis in_var_def in_var_indep out_in_indep out_var_def plus_pres_lens_indep prod_as_plus)

lemma prod_lens_indep_out_var [simp]:
  "b \<bowtie> x \<Longrightarrow> a \<times>\<^sub>L b \<bowtie> out_var x"
  by (metis in_out_indep in_var_def out_var_def out_var_indep plus_pres_lens_indep prod_as_plus)

lemma in_var_pr_var [simp]:
  "in_var (pr_var x) = in_var x"
  by (simp add: pr_var_def)

lemma out_var_pr_var [simp]:
  "out_var (pr_var x) = out_var x"
  by (simp add: pr_var_def)

lemma pr_var_idem [simp]: 
  "pr_var (pr_var x) = pr_var x"
  by (simp add: pr_var_def)
    
lemma pr_var_lens_plus [simp]: 
  "pr_var (x +\<^sub>L y) = (x +\<^sub>L y)"
  by (simp add: pr_var_def)
    
lemma pr_var_lens_comp_1 [simp]: 
  "pr_var x ;\<^sub>L y = pr_var (x ;\<^sub>L y)"
  by (simp add: pr_var_def)
    
lemma in_var_plus [simp]: "in_var (x +\<^sub>L y) = in_var x +\<^sub>L in_var y"
  by (simp add: in_var_def)

lemma out_var_plus [simp]: "out_var (x +\<^sub>L y) = out_var x +\<^sub>L out_var y"
  by (simp add: out_var_def)
  
text \<open> Similar properties follow for sublens \<close>
  
lemma in_var_sublens [simp]:
  "y \<subseteq>\<^sub>L x \<Longrightarrow> in_var y \<subseteq>\<^sub>L in_var x"
  by (metis (no_types, hide_lams) in_var_def lens_comp_assoc sublens_def)
     
lemma out_var_sublens [simp]:
  "y \<subseteq>\<^sub>L x \<Longrightarrow> out_var y \<subseteq>\<^sub>L out_var x"
  by (metis (no_types, hide_lams) out_var_def lens_comp_assoc sublens_def)

lemma pr_var_sublens [simp]:
  "y \<subseteq>\<^sub>L x \<Longrightarrow> pr_var y \<subseteq>\<^sub>L pr_var x"
  by (simp add: pr_var_def)

subsection \<open> Lens simplifications \<close>
    
text \<open> We also define some lookup abstraction simplifications. \<close>

lemma var_lookup_in [simp]: "lens_get (in_var x) (A, A') = lens_get x A"
  by (simp add: in_var_def fst_lens_def lens_comp_def)

lemma var_lookup_out [simp]: "lens_get (out_var x) (A, A') = lens_get x A'"
  by (simp add: out_var_def snd_lens_def lens_comp_def)

lemma var_update_in [simp]: "lens_put (in_var x) (A, A') v = (lens_put x A v, A')"
  by (simp add: in_var_def fst_lens_def lens_comp_def)

lemma var_update_out [simp]: "lens_put (out_var x) (A, A') v = (A, lens_put x A' v)"
  by (simp add: out_var_def snd_lens_def lens_comp_def)

lemma get_lens_plus [simp]: "get\<^bsub>x +\<^sub>L y\<^esub> s = (get\<^bsub>x\<^esub> s, get\<^bsub>y\<^esub> s)"
  by (simp add: lens_defs)

subsection \<open> Syntax translations \<close>
  
text \<open> In order to support nice syntax for variables, we here set up some translations. The first
  step is to introduce a collection of non-terminals. \<close>
  
nonterminal svid and svids and svar and svars and salpha

text \<open> These non-terminals correspond to the following syntactic entities. Non-terminal 
  @{typ "svid"} is an atomic variable identifier, and @{typ "svids"} is a list of identifier. 
  @{typ "svar"} is a decorated variable, such as an input or output variable, and @{typ "svars"} is 
  a list of decorated variables. @{typ "salpha"} is an alphabet or set of variables. Such sets can 
  be constructed only through lens composition due to typing restrictions. Next we introduce some 
  syntax constructors. \<close>
   
syntax \<comment> \<open> Identifiers \<close>
  "_svid"         :: "id \<Rightarrow> svid" ("_" [999] 999)
  "_svid_unit"    :: "svid \<Rightarrow> svids" ("_")
  "_svid_list"    :: "svid \<Rightarrow> svids \<Rightarrow> svids" ("_,/ _")
  "_svid_alpha"   :: "svid" ("\<^bold>v")
  "_svid_dot"     :: "svid \<Rightarrow> svid \<Rightarrow> svid" ("_:_" [998,999] 998)
  "_mk_svid_list" :: "svids \<Rightarrow> logic" \<comment> \<open> Helper function for summing a list of identifiers \<close>

text \<open> A variable identifier can either be a HOL identifier, the complete set of variables in the
  alphabet $\textbf{v}$, or a composite identifier separated by colons, which
  corresponds to a sort of qualification. The final option is effectively a lens composition. \<close>
  
syntax \<comment> \<open> Decorations \<close>
  "_spvar"       :: "svid \<Rightarrow> svar" ("&_" [990] 990)
  "_sinvar"      :: "svid \<Rightarrow> svar" ("$_" [990] 990)
  "_soutvar"     :: "svid \<Rightarrow> svar" ("$_\<acute>" [990] 990)

text \<open> A variable can be decorated with an ampersand, to indicate it is a predicate variable, with 
  a dollar to indicate its an unprimed relational variable, or a dollar and ``acute'' symbol to 
  indicate its a primed relational variable. Isabelle's parser is extensible so additional
  decorations can be and are added later. \<close>
  
syntax \<comment> \<open> Variable sets \<close>
  "_salphaid"    :: "svid \<Rightarrow> salpha" ("_" [990] 990)
  "_salphavar"   :: "svar \<Rightarrow> salpha" ("_" [990] 990)
  "_salphaparen" :: "salpha \<Rightarrow> salpha" ("'(_')")
  "_salphacomp"  :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr ";" 75)
  "_salphaprod"  :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr "\<times>" 85)
  "_salpha_all"  :: "salpha" ("\<Sigma>")
  "_salpha_none" :: "salpha" ("\<emptyset>")
  "_svar_nil"    :: "svar \<Rightarrow> svars" ("_")
  "_svar_cons"   :: "svar \<Rightarrow> svars \<Rightarrow> svars" ("_,/ _")
  "_salphaset"   :: "svars \<Rightarrow> salpha" ("{_}")
  "_salphamk"    :: "logic \<Rightarrow> salpha"

text \<open> The terminals of an alphabet are either HOL identifiers or UTP variable identifiers. 
  We support two ways of constructing alphabets; by composition of smaller alphabets using
  a semi-colon or by a set-style construction $\{a,b,c\}$ with a list of UTP variables. \<close>

syntax \<comment> \<open> Quotations \<close>
  "_ualpha_set"  :: "svars \<Rightarrow> logic" ("{_}\<^sub>\<alpha>")  
  "_svar"        :: "svar \<Rightarrow> logic" ("'(_')\<^sub>v")
  
text \<open> For various reasons, the syntax constructors above all yield specific grammar categories and
  will not parser at the HOL top level (basically this is to do with us wanting to reuse the syntax
  for expressions). As a result we provide some quotation constructors above. 

  Next we need to construct the syntax translations rules. First we need a few polymorphic constants. \<close>
 
consts
  svar :: "'v \<Rightarrow> 'e"
  ivar :: "'v \<Rightarrow> 'e"
  ovar :: "'v \<Rightarrow> 'e"

adhoc_overloading
  svar pr_var and ivar in_var and ovar out_var
  
text \<open> The functions above turn a representation of a variable (type @{typ "'v"}), including
  its name and type, into some lens type @{typ "'e"}. @{term "svar"} constructs a predicate variable,
  @{term "ivar"} and input variables, and @{term "ovar"} and output variable. The functions bridge 
  between the model and encoding of the variable and its interpretation as a lens in order to integrate it 
  into the general lens-based framework. Overriding these functions is then all we need to make 
  use of any kind of variables in terms of interfacing it with the system. Although in core UTP
  variables are always modelled using record field, we can overload these constants to allow other
  kinds of variables, such as deep variables with explicit syntax and type information.

  Finally, we set up the translations rules. \<close>

translations
  \<comment> \<open> Identifiers \<close>
  "_svid x" \<rightharpoonup> "x"
  "_svid_alpha" \<rightleftharpoons> "\<Sigma>"
  "_svid_dot x y" \<rightharpoonup> "y ;\<^sub>L x"
  "_mk_svid_list (_svid_unit x)" \<rightharpoonup> "x"
  "_mk_svid_list (_svid_list x xs)" \<rightharpoonup> "x +\<^sub>L _mk_svid_list xs"

  \<comment> \<open> Decorations \<close>
  "_spvar \<Sigma>"  \<leftharpoondown>  "CONST svar CONST id_lens"
  "_sinvar \<Sigma>"  \<leftharpoondown> "CONST ivar 1\<^sub>L"
  "_soutvar \<Sigma>" \<leftharpoondown> "CONST ovar 1\<^sub>L"
  "_spvar (_svid_dot x y)" \<leftharpoondown> "CONST svar (CONST lens_comp y x)"
  "_sinvar (_svid_dot x y)" \<leftharpoondown> "CONST ivar (CONST lens_comp y x)"
  "_soutvar (_svid_dot x y)" \<leftharpoondown> "CONST ovar (CONST lens_comp y x)"
  "_svid_dot (_svid_dot x y) z" \<leftharpoondown> "_svid_dot (CONST lens_comp y x) z"

  "_spvar x" \<rightleftharpoons> "CONST svar x"
  "_sinvar x" \<rightleftharpoons> "CONST ivar x"
  "_soutvar x" \<rightleftharpoons> "CONST ovar x"

  \<comment> \<open> Alphabets \<close>
  "_salphaparen a" \<rightharpoonup> "a"
  "_salphaid x" \<rightharpoonup> "x"
  "_salphacomp x y" \<rightharpoonup> "x +\<^sub>L y"
  "_salphaprod a b" \<rightleftharpoons> "a \<times>\<^sub>L b"
  "_salphavar x" \<rightharpoonup> "x"
  "_svar_nil x" \<rightharpoonup> "x"
  "_svar_cons x xs" \<rightharpoonup> "x +\<^sub>L xs"
  "_salphaset A" \<rightharpoonup> "A"  
  "(_svar_cons x (_salphamk y))" \<leftharpoondown> "_salphamk (x +\<^sub>L y)" 
  "x" \<leftharpoondown> "_salphamk x"
  "_salpha_all" \<rightleftharpoons> "1\<^sub>L"
  "_salpha_none" \<rightleftharpoons> "0\<^sub>L"

  \<comment> \<open> Quotations \<close>
  "_ualpha_set A" \<rightharpoonup> "A"
  "_svar x" \<rightharpoonup> "x"

text \<open> The translation rules mainly convert syntax into lens constructions, using a mixture
  of lens operators and the bespoke variable definitions. Notably, a colon variable identifier
  qualification becomes a lens composition, and variable sets are constructed using len sum. 
  The translation rules are carefully crafted to ensure both parsing and pretty printing. 

  Finally we create the following useful utility translation function that allows us to construct a 
  UTP variable (lens) type given a return and alphabet type. \<close>

syntax
  "_uvar_ty"      :: "type \<Rightarrow> type \<Rightarrow> type"

parse_translation \<open>
let
  fun uvar_ty_tr [ty] = Syntax.const @{type_syntax lens} $ ty $ Syntax.const @{type_syntax dummy}
    | uvar_ty_tr ts = raise TERM ("uvar_ty_tr", ts);
in [(@{syntax_const "_uvar_ty"}, K uvar_ty_tr)] end
\<close>
  
end