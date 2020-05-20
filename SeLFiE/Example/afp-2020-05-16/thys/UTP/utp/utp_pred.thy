section \<open> Alphabetised Predicates \<close>

theory utp_pred
imports
  utp_expr_funcs
  utp_subst
  utp_meta_subst
  utp_tactics
begin
  
text \<open> In this theory we begin to create an Isabelle version of the alphabetised predicate calculus
  that is described in Chapter 1 of the UTP book~\cite{Hoare&98}. \<close>
  
subsection \<open> Predicate type and syntax \<close>
  
text \<open> An alphabetised predicate is a simply a boolean valued expression. \<close>

type_synonym '\<alpha> upred = "(bool, '\<alpha>) uexpr"

translations
  (type) "'\<alpha> upred" <= (type) "(bool, '\<alpha>) uexpr"

text \<open> We want to remain as close as possible to the mathematical UTP syntax, but also
        want to be conservative with HOL. For this reason we chose not to steal syntax
        from HOL, but where possible use polymorphism to allow selection of the appropriate
        operator (UTP vs. HOL). Thus we will first remove the standard syntax for conjunction,
        disjunction, and negation, and replace these with adhoc overloaded definitions. We
        similarly use polymorphic constants for the other predicate calculus operators. \<close>

purge_notation
  conj (infixr "\<and>" 35) and
  disj (infixr "\<or>" 30) and
  Not ("\<not> _" [40] 40)

consts
  utrue  :: "'a" ("true")
  ufalse :: "'a" ("false")
  uconj  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<and>" 35)
  udisj  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<or>" 30)
  uimpl  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<Rightarrow>" 25)
  uiff   :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<Leftrightarrow>" 25)
  unot   :: "'a \<Rightarrow> 'a" ("\<not> _" [40] 40)
  uex    :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> 'p \<Rightarrow> 'p"
  uall   :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> 'p \<Rightarrow> 'p"
  ushEx  :: "['a \<Rightarrow> 'p] \<Rightarrow> 'p"
  ushAll :: "['a \<Rightarrow> 'p] \<Rightarrow> 'p"
  
adhoc_overloading
  uconj conj and
  udisj disj and
  unot Not

text \<open> We set up two versions of each of the quantifiers: @{const uex} / @{const uall} and
        @{const ushEx} / @{const ushAll}. The former pair allows quantification of UTP variables,
        whilst the latter allows quantification of HOL variables in concert with the literal
        expression constructor @{term "\<guillemotleft>x\<guillemotright>"}. Both varieties will be needed at various points. 
        Syntactically they are distinguished by a boldface quantifier
        for the HOL versions (achieved by the "bold" escape in Isabelle). \<close>

nonterminal idt_list

syntax
  "_idt_el"  :: "idt \<Rightarrow> idt_list" ("_")
  "_idt_list" :: "idt \<Rightarrow> idt_list \<Rightarrow> idt_list" ("(_,/ _)" [0, 1])
  "_uex"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<exists> _ \<bullet> _" [0, 10] 10)
  "_uall"    :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<forall> _ \<bullet> _" [0, 10] 10)
  "_ushEx"   :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<exists> _ \<bullet> _" [0, 10] 10)
  "_ushAll"  :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ \<bullet> _" [0, 10] 10)
  "_ushBEx"  :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<exists> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ushBAll" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ushGAll" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ | _ \<bullet> _" [0, 0, 10] 10)
  "_ushGtAll" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>\<forall> _ > _ \<bullet> _" [0, 0, 10] 10)
  "_ushLtAll" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>\<forall> _ < _ \<bullet> _" [0, 0, 10] 10)
  "_uvar_res" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\<restriction>\<^sub>v" 90)
  
translations
  "_uex x P"                   == "CONST uex x P"
  "_uex (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_uex (x +\<^sub>L y) P"
  "_uall x P"                  == "CONST uall x P"
  "_uall (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_uall (x +\<^sub>L y) P"
  "_ushEx x P"                 == "CONST ushEx (\<lambda> x. P)"
  "\<^bold>\<exists> x \<in> A \<bullet> P"                => "\<^bold>\<exists> x \<bullet> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u A \<and> P"
  "_ushAll x P"                == "CONST ushAll (\<lambda> x. P)"
  "\<^bold>\<forall> x \<in> A \<bullet> P"                => "\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u A \<Rightarrow> P"
  "\<^bold>\<forall> x | P \<bullet> Q"                => "\<^bold>\<forall> x \<bullet> P \<Rightarrow> Q"
  "\<^bold>\<forall> x > y \<bullet> P"                => "\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> >\<^sub>u y \<Rightarrow> P"
  "\<^bold>\<forall> x < y \<bullet> P"                => "\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> <\<^sub>u y \<Rightarrow> P"

subsection \<open> Predicate operators \<close>

text \<open> We chose to maximally reuse definitions and laws built into HOL. For this reason,
        when introducing the core operators we proceed by lifting operators from the
        polymorphic algebraic hierarchy of HOL. Thus the initial definitions take
        place in the context of type class instantiations. We first introduce our own
        class called \emph{refine} that will add the refinement operator syntax to
        the HOL partial order class. \<close>

class refine = order

abbreviation refineBy :: "'a::refine \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<sqsubseteq>" 50) where
"P \<sqsubseteq> Q \<equiv> less_eq Q P"

text \<open> Since, on the whole, lattices in UTP are the opposite way up to the standard definitions
        in HOL, we syntactically invert the lattice operators. This is the one exception where
        we do steal HOL syntax, but I think it makes sense for UTP. Indeed we make this
        inversion for all of the lattice operators. \<close>

purge_notation Lattices.inf (infixl "\<sqinter>" 70)
notation Lattices.inf (infixl "\<squnion>" 70)
purge_notation Lattices.sup (infixl "\<squnion>" 65)
notation Lattices.sup (infixl "\<sqinter>" 65)
  
purge_notation Inf ("\<Sqinter>_" [900] 900)
notation Inf ("\<Squnion>_" [900] 900)
purge_notation Sup ("\<Squnion>_" [900] 900)
notation Sup ("\<Sqinter>_" [900] 900)
  
purge_notation Orderings.bot ("\<bottom>")
notation Orderings.bot ("\<top>")
purge_notation Orderings.top ("\<top>")
notation Orderings.top ("\<bottom>")

purge_syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)

text \<open> We trivially instantiate our refinement class \<close>

instance uexpr :: (order, type) refine ..

\<comment> \<open> Configure transfer law for refinement for the fast relational tactics. \<close>

theorem upred_ref_iff [uexpr_transfer_laws]:
"(P \<sqsubseteq> Q) = (\<forall>b. \<lbrakk>Q\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e b)"
  apply (transfer)
  apply (clarsimp)
  done

text \<open> Next we introduce the lattice operators, which is again done by lifting. \<close>

instantiation uexpr :: (lattice, type) lattice
begin
  lift_definition sup_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  is "\<lambda>P Q A. Lattices.sup (P A) (Q A)" .
  lift_definition inf_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  is "\<lambda>P Q A. Lattices.inf (P A) (Q A)" .
instance
  by (intro_classes) (transfer, auto)+
end

instantiation uexpr :: (bounded_lattice, type) bounded_lattice
begin
  lift_definition bot_uexpr :: "('a, 'b) uexpr" is "\<lambda> A. Orderings.bot" .
  lift_definition top_uexpr :: "('a, 'b) uexpr" is "\<lambda> A. Orderings.top" .
instance
  by (intro_classes) (transfer, auto)+
end

lemma top_uexpr_rep_eq [simp]: 
  "\<lbrakk>Orderings.bot\<rbrakk>\<^sub>e b = False"
  by (transfer, auto)

lemma bot_uexpr_rep_eq [simp]: 
  "\<lbrakk>Orderings.top\<rbrakk>\<^sub>e b = True"
  by (transfer, auto)
    
instance uexpr :: (distrib_lattice, type) distrib_lattice
  by (intro_classes) (transfer, rule ext, auto simp add: sup_inf_distrib1)

text \<open> Finally we show that predicates form a Boolean algebra (under the lattice operators),
  a complete lattice, a completely distribute lattice, and a complete boolean algebra. This
  equip us with a very complete theory for basic logical propositions. \<close>

instance uexpr :: (boolean_algebra, type) boolean_algebra
  apply (intro_classes, unfold uexpr_defs; transfer, rule ext)
    apply (simp_all add: sup_inf_distrib1 diff_eq)
  done

instantiation uexpr :: (complete_lattice, type) complete_lattice
begin
  lift_definition Inf_uexpr :: "('a, 'b) uexpr set \<Rightarrow> ('a, 'b) uexpr"
  is "\<lambda> PS A. INF P\<in>PS. P(A)" .
  lift_definition Sup_uexpr :: "('a, 'b) uexpr set \<Rightarrow> ('a, 'b) uexpr"
  is "\<lambda> PS A. SUP P\<in>PS. P(A)" .
instance
  by (intro_classes)
     (transfer, auto intro: INF_lower SUP_upper simp add: INF_greatest SUP_least)+
end

instance uexpr :: (complete_distrib_lattice, type) complete_distrib_lattice
  by (intro_classes; transfer; auto simp add: INF_SUP_set)

instance uexpr :: (complete_boolean_algebra, type) complete_boolean_algebra ..
  
text \<open> From the complete lattice, we can also define and give syntax for the fixed-point operators. 
  Like the lattice operators, these are reversed in UTP. \<close>

syntax
  "_mu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu> _ \<bullet> _" [0, 10] 10)
  "_nu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu> _ \<bullet> _" [0, 10] 10)

notation gfp ("\<mu>")
notation lfp ("\<nu>")

translations
  "\<nu> X \<bullet> P" == "CONST lfp (\<lambda> X. P)"
  "\<mu> X \<bullet> P" == "CONST gfp (\<lambda> X. P)"

text \<open> With the lattice operators defined, we can proceed to give definitions for the
        standard predicate operators in terms of them. \<close>

definition "true_upred  = (Orderings.top :: '\<alpha> upred)"
definition "false_upred = (Orderings.bot :: '\<alpha> upred)"
definition "conj_upred  = (Lattices.inf :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)"
definition "disj_upred  = (Lattices.sup :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)"
definition "not_upred   = (uminus :: '\<alpha> upred \<Rightarrow> '\<alpha> upred)"
definition "diff_upred  = (minus :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)"

abbreviation Conj_upred :: "'\<alpha> upred set \<Rightarrow> '\<alpha> upred" ("\<And>_" [900] 900) where
"\<And> A \<equiv> \<Squnion> A"

abbreviation Disj_upred :: "'\<alpha> upred set \<Rightarrow> '\<alpha> upred" ("\<Or>_" [900] 900) where
"\<Or> A \<equiv> \<Sqinter> A"

notation
  conj_upred (infixr "\<and>\<^sub>p" 35) and
  disj_upred (infixr "\<or>\<^sub>p" 30)

text \<open> Perhaps slightly confusingly, the UTP infimum is the HOL supremum and vice-versa. This is
  because, again, in UTP the lattice is inverted due to the definition of refinement and a desire
  to have miracle at the top, and abort at the bottom. \<close>
  
lift_definition UINF :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> ('b::complete_lattice, '\<alpha>) uexpr) \<Rightarrow> ('b, '\<alpha>) uexpr"
is "\<lambda> P F b. Sup {\<lbrakk>F x\<rbrakk>\<^sub>eb | x. \<lbrakk>P x\<rbrakk>\<^sub>eb}" .

lift_definition USUP :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> ('b::complete_lattice, '\<alpha>) uexpr) \<Rightarrow> ('b, '\<alpha>) uexpr"
is "\<lambda> P F b. Inf {\<lbrakk>F x\<rbrakk>\<^sub>eb | x. \<lbrakk>P x\<rbrakk>\<^sub>eb}" .
  
syntax
  "_USup"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"            ("\<And> _ \<bullet> _" [0, 10] 10)
  "_USup"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"            ("\<Squnion> _ \<bullet> _" [0, 10] 10)
  "_USup_mem" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<And> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_USup_mem" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Squnion> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_USUP"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<And> _ | _ \<bullet> _" [0, 0, 10] 10)
  "_USUP"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Squnion> _ | _ \<bullet> _" [0, 0, 10] 10)
  "_UInf"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"            ("\<Or> _ \<bullet> _" [0, 10] 10)
  "_UInf"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"            ("\<Sqinter> _ \<bullet> _" [0, 10] 10)
  "_UInf_mem" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Or> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_UInf_mem" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Sqinter> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_UINF"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Or> _ | _ \<bullet> _" [0, 10] 10)
  "_UINF"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Sqinter> _ | _ \<bullet> _" [0, 10] 10)

translations
  "\<Sqinter> x | P \<bullet> F" => "CONST UINF (\<lambda> x. P) (\<lambda> x. F)"
  "\<Sqinter> x \<bullet> F"     == "\<Sqinter> x | true \<bullet> F"
  "\<Sqinter> x \<bullet> F"     == "\<Sqinter> x | true \<bullet> F"
  "\<Sqinter> x \<in> A \<bullet> F" => "\<Sqinter> x | \<guillemotleft>x\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Sqinter> x \<in> A \<bullet> F" <= "\<Sqinter> x | \<guillemotleft>y\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Sqinter> x | P \<bullet> F" <= "CONST UINF (\<lambda> y. P) (\<lambda> x. F)"
  "\<Sqinter> x | P \<bullet> F(x)" <= "CONST UINF (\<lambda> x. P) F"
  "\<Squnion> x | P \<bullet> F" => "CONST USUP (\<lambda> x. P) (\<lambda> x. F)"
  "\<Squnion> x \<bullet> F"     == "\<Squnion> x | true \<bullet> F"
  "\<Squnion> x \<in> A \<bullet> F" => "\<Squnion> x | \<guillemotleft>x\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Squnion> x \<in> A \<bullet> F" <= "\<Squnion> x | \<guillemotleft>y\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Squnion> x | P \<bullet> F" <= "CONST USUP (\<lambda> y. P) (\<lambda> x. F)"
  "\<Squnion> x | P \<bullet> F(x)" <= "CONST USUP (\<lambda> x. P) F"

text \<open> We also define the other predicate operators \<close>

lift_definition impl::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> P Q A. P A \<longrightarrow> Q A" .

lift_definition iff_upred ::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> P Q A. P A \<longleftrightarrow> Q A" .

lift_definition ex :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> x P b. (\<exists> v. P(put\<^bsub>x\<^esub> b v))" .

lift_definition shEx ::"['\<beta> \<Rightarrow>'\<alpha> upred] \<Rightarrow> '\<alpha> upred" is
"\<lambda> P A. \<exists> x. (P x) A" .

lift_definition all :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> x P b. (\<forall> v. P(put\<^bsub>x\<^esub> b v))" .

lift_definition shAll ::"['\<beta> \<Rightarrow>'\<alpha> upred] \<Rightarrow> '\<alpha> upred" is
"\<lambda> P A. \<forall> x. (P x) A" .
    
text \<open> We define the following operator which is dual of existential quantification. It hides the
  valuation of variables other than $x$ through existential quantification. \<close>
    
lift_definition var_res :: "'\<alpha> upred \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred" is
"\<lambda> P x b. \<exists> b'. P (b' \<oplus>\<^sub>L b on x)" .
    
translations
  "_uvar_res P a" \<rightleftharpoons> "CONST var_res P a"

text \<open> We have to add a u subscript to the closure operator as I don't want to override the syntax
        for HOL lists (we'll be using them later). \<close>

lift_definition closure::"'\<alpha> upred \<Rightarrow> '\<alpha> upred" ("[_]\<^sub>u") is
"\<lambda> P A. \<forall>A'. P A'" .

lift_definition taut :: "'\<alpha> upred \<Rightarrow> bool" ("`_`")
is "\<lambda> P. \<forall> A. P A" .

text \<open> Configuration for UTP tactics \<close>

update_uexpr_rep_eq_thms \<comment> \<open> Reread @{text rep_eq} theorems. \<close>

declare utp_pred.taut.rep_eq [upred_defs]

adhoc_overloading
  utrue "true_upred" and
  ufalse "false_upred" and
  unot "not_upred" and
  uconj "conj_upred" and
  udisj "disj_upred" and
  uimpl impl and
  uiff iff_upred and
  uex ex and
  uall all and
  ushEx shEx and
  ushAll shAll

syntax
  "_uneq"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<noteq>\<^sub>u" 50)
  "_unmem"      :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<notin>\<^sub>u" 50)

translations
  "x \<noteq>\<^sub>u y" == "CONST unot (x =\<^sub>u y)"
  "x \<notin>\<^sub>u A" == "CONST unot (CONST bop (\<in>) x A)"

declare true_upred_def [upred_defs]
declare false_upred_def [upred_defs]
declare conj_upred_def [upred_defs]
declare disj_upred_def [upred_defs]
declare not_upred_def [upred_defs]
declare diff_upred_def [upred_defs]
declare subst_upd_uvar_def [upred_defs]
declare cond_subst_def [upred_defs]
declare par_subst_def [upred_defs]
declare subst_del_def [upred_defs]
declare unrest_usubst_def [upred_defs]
declare uexpr_defs [upred_defs]

lemma true_alt_def: "true = \<guillemotleft>True\<guillemotright>"
  by (pred_auto)

lemma false_alt_def: "false = \<guillemotleft>False\<guillemotright>"
  by (pred_auto)

declare true_alt_def[THEN sym,simp]
declare false_alt_def[THEN sym,simp]

subsection \<open> Unrestriction Laws \<close>

lemma unrest_allE:
  "\<lbrakk> \<Sigma> \<sharp> P; P = true \<Longrightarrow> Q; P = false \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (pred_auto)
  
lemma unrest_true [unrest]: "x \<sharp> true"
  by (pred_auto)

lemma unrest_false [unrest]: "x \<sharp> false"
  by (pred_auto)

lemma unrest_conj [unrest]: "\<lbrakk> x \<sharp> (P :: '\<alpha> upred); x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<and> Q"
  by (pred_auto)

lemma unrest_disj [unrest]: "\<lbrakk> x \<sharp> (P :: '\<alpha> upred); x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<or> Q"
  by (pred_auto)

lemma unrest_UINF [unrest]:
  "\<lbrakk> (\<And> i. x \<sharp> P(i)); (\<And> i. x \<sharp> Q(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Sqinter> i | P(i) \<bullet> Q(i))"
  by (pred_auto)

lemma unrest_USUP [unrest]:
  "\<lbrakk> (\<And> i. x \<sharp> P(i)); (\<And> i. x \<sharp> Q(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Squnion> i | P(i) \<bullet> Q(i))"
  by (pred_auto)

lemma unrest_UINF_mem [unrest]:
  "\<lbrakk>(\<And> i. i \<in> A \<Longrightarrow> x \<sharp> P(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Sqinter> i\<in>A \<bullet> P(i))"
  by (pred_simp, metis)

lemma unrest_USUP_mem [unrest]:
  "\<lbrakk>(\<And> i. i \<in> A \<Longrightarrow> x \<sharp> P(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Squnion> i\<in>A \<bullet> P(i))"
  by (pred_simp, metis)

lemma unrest_impl [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<Rightarrow> Q"
  by (pred_auto)

lemma unrest_iff [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<Leftrightarrow> Q"
  by (pred_auto)

lemma unrest_not [unrest]: "x \<sharp> (P :: '\<alpha> upred) \<Longrightarrow> x \<sharp> (\<not> P)"
  by (pred_auto)

text \<open> The sublens proviso can be thought of as membership below. \<close>

lemma unrest_ex_in [unrest]:
  "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> x \<sharp> (\<exists> y \<bullet> P)"
  by (pred_auto)

declare sublens_refl [simp]
declare lens_plus_ub [simp]
declare lens_plus_right_sublens [simp]
declare comp_wb_lens [simp]
declare comp_mwb_lens [simp]
declare plus_mwb_lens [simp]

lemma unrest_ex_diff [unrest]:
  assumes "x \<bowtie> y" "y \<sharp> P"
  shows "y \<sharp> (\<exists> x \<bullet> P)"
  using assms lens_indep_comm 
  by (rel_simp', fastforce)
  
lemma unrest_all_in [unrest]:
  "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> x \<sharp> (\<forall> y \<bullet> P)"
  by (pred_auto)

lemma unrest_all_diff [unrest]:
  assumes "x \<bowtie> y" "y \<sharp> P"
  shows "y \<sharp> (\<forall> x \<bullet> P)"
  using assms
  by (pred_simp, simp_all add: lens_indep_comm)

lemma unrest_var_res_diff [unrest]:
  assumes "x \<bowtie> y"
  shows "y \<sharp> (P \<restriction>\<^sub>v x)"
  using assms by (pred_auto)

lemma unrest_var_res_in [unrest]:
  assumes "mwb_lens x" "y \<subseteq>\<^sub>L x" "y \<sharp> P"
  shows "y \<sharp> (P \<restriction>\<^sub>v x)"
  using assms 
  apply (pred_auto)
   apply fastforce
  apply (metis (no_types, lifting) mwb_lens_weak weak_lens.put_get)
  done

lemma unrest_shEx [unrest]:
  assumes "\<And> y. x \<sharp> P(y)"
  shows "x \<sharp> (\<^bold>\<exists> y \<bullet> P(y))"
  using assms by (pred_auto)

lemma unrest_shAll [unrest]:
  assumes "\<And> y. x \<sharp> P(y)"
  shows "x \<sharp> (\<^bold>\<forall> y \<bullet> P(y))"
  using assms by (pred_auto)

lemma unrest_closure [unrest]:
  "x \<sharp> [P]\<^sub>u"
  by (pred_auto)

subsection \<open> Used-by laws \<close>

lemma usedBy_not [unrest]:
  "\<lbrakk> x \<natural> P \<rbrakk> \<Longrightarrow> x \<natural> (\<not> P)"
  by (pred_simp)
    
lemma usedBy_conj [unrest]:
  "\<lbrakk> x \<natural> P; x \<natural> Q \<rbrakk> \<Longrightarrow> x \<natural> (P \<and> Q)"
  by (pred_simp)

lemma usedBy_disj [unrest]:
  "\<lbrakk> x \<natural> P; x \<natural> Q \<rbrakk> \<Longrightarrow> x \<natural> (P \<or> Q)"
  by (pred_simp)

lemma usedBy_impl [unrest]:
  "\<lbrakk> x \<natural> P; x \<natural> Q \<rbrakk> \<Longrightarrow> x \<natural> (P \<Rightarrow> Q)"
  by (pred_simp)

lemma usedBy_iff [unrest]:
  "\<lbrakk> x \<natural> P; x \<natural> Q \<rbrakk> \<Longrightarrow> x \<natural> (P \<Leftrightarrow> Q)"
  by (pred_simp)
    
subsection \<open> Substitution Laws \<close>

text \<open> Substitution is monotone \<close>

lemma subst_mono: "P \<sqsubseteq> Q \<Longrightarrow> (\<sigma> \<dagger> P) \<sqsubseteq> (\<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_true [usubst]: "\<sigma> \<dagger> true = true"
  by (pred_auto)

lemma subst_false [usubst]: "\<sigma> \<dagger> false = false"
  by (pred_auto)

lemma subst_not [usubst]: "\<sigma> \<dagger> (\<not> P) = (\<not> \<sigma> \<dagger> P)"
  by (pred_auto)

lemma subst_impl [usubst]: "\<sigma> \<dagger> (P \<Rightarrow> Q) = (\<sigma> \<dagger> P \<Rightarrow> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_iff [usubst]: "\<sigma> \<dagger> (P \<Leftrightarrow> Q) = (\<sigma> \<dagger> P \<Leftrightarrow> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_disj [usubst]: "\<sigma> \<dagger> (P \<or> Q) = (\<sigma> \<dagger> P \<or> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_conj [usubst]: "\<sigma> \<dagger> (P \<and> Q) = (\<sigma> \<dagger> P \<and> \<sigma> \<dagger> Q)"
  by (pred_auto)
    
lemma subst_sup [usubst]: "\<sigma> \<dagger> (P \<sqinter> Q) = (\<sigma> \<dagger> P \<sqinter> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_inf [usubst]: "\<sigma> \<dagger> (P \<squnion> Q) = (\<sigma> \<dagger> P \<squnion> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_UINF [usubst]: "\<sigma> \<dagger> (\<Sqinter> i | P(i) \<bullet> Q(i)) = (\<Sqinter> i | (\<sigma> \<dagger> P(i)) \<bullet> (\<sigma> \<dagger> Q(i)))"
  by (pred_auto)

lemma subst_USUP [usubst]: "\<sigma> \<dagger> (\<Squnion> i | P(i) \<bullet> Q(i)) = (\<Squnion> i | (\<sigma> \<dagger> P(i)) \<bullet> (\<sigma> \<dagger> Q(i)))"
  by (pred_auto)

lemma subst_closure [usubst]: "\<sigma> \<dagger> [P]\<^sub>u = [P]\<^sub>u"
  by (pred_auto)

lemma subst_shEx [usubst]: "\<sigma> \<dagger> (\<^bold>\<exists> x \<bullet> P(x)) = (\<^bold>\<exists> x \<bullet> \<sigma> \<dagger> P(x))"
  by (pred_auto)

lemma subst_shAll [usubst]: "\<sigma> \<dagger> (\<^bold>\<forall> x \<bullet> P(x)) = (\<^bold>\<forall> x \<bullet> \<sigma> \<dagger> P(x))"
  by (pred_auto)

text \<open> TODO: Generalise the quantifier substitution laws to n-ary substitutions \<close>

lemma subst_ex_same [usubst]:
  "mwb_lens x \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> (\<exists> x \<bullet> P) = \<sigma> \<dagger> (\<exists> x \<bullet> P)"
  by (pred_auto)

lemma subst_ex_same' [usubst]:
  "mwb_lens x \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> (\<exists> &x \<bullet> P) = \<sigma> \<dagger> (\<exists> &x \<bullet> P)"
  by (pred_auto)
    
lemma subst_ex_indep [usubst]:
  assumes "x \<bowtie> y" "y \<sharp> v"
  shows "(\<exists> y \<bullet> P)\<lbrakk>v/x\<rbrakk> = (\<exists> y \<bullet> P\<lbrakk>v/x\<rbrakk>)"
  using assms
  apply (pred_auto)
  using lens_indep_comm apply fastforce+
  done

lemma subst_ex_unrest [usubst]:
  "x \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (\<exists> x \<bullet> P) = (\<exists> x \<bullet> \<sigma> \<dagger> P)"
  by (pred_auto)

lemma subst_all_same [usubst]:
  "mwb_lens x \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> (\<forall> x \<bullet> P) = \<sigma> \<dagger> (\<forall> x \<bullet> P)"
  by (simp add: id_subst subst_unrest unrest_all_in)

lemma subst_all_indep [usubst]:
  assumes "x \<bowtie> y" "y \<sharp> v"
  shows "(\<forall> y \<bullet> P)\<lbrakk>v/x\<rbrakk> = (\<forall> y \<bullet> P\<lbrakk>v/x\<rbrakk>)"
  using assms
  by (pred_simp, simp_all add: lens_indep_comm)

lemma msubst_true [usubst]: "true\<lbrakk>x\<rightarrow>v\<rbrakk> = true"
  by (pred_auto)

lemma msubst_false [usubst]: "false\<lbrakk>x\<rightarrow>v\<rbrakk> = false"
  by (pred_auto)
lemma msubst_not [usubst]: "(\<not> P(x))\<lbrakk>x\<rightarrow>v\<rbrakk> = (\<not> ((P x)\<lbrakk>x\<rightarrow>v\<rbrakk>))"
  by (pred_auto)

lemma msubst_not_2 [usubst]: "(\<not> P x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk> = (\<not> ((P x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk>))"
  by (pred_auto)+

lemma msubst_disj [usubst]: "(P(x) \<or> Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk> = ((P(x))\<lbrakk>x\<rightarrow>v\<rbrakk> \<or> (Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (pred_auto)

lemma msubst_disj_2 [usubst]: "(P x y \<or> Q x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk> = ((P x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk> \<or> (Q x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk>)"
  by (pred_auto)+

lemma msubst_conj [usubst]: "(P(x) \<and> Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk> = ((P(x))\<lbrakk>x\<rightarrow>v\<rbrakk> \<and> (Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (pred_auto)

lemma msubst_conj_2 [usubst]: "(P x y \<and> Q x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk> = ((P x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk> \<and> (Q x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk>)"
  by (pred_auto)+

lemma msubst_implies [usubst]:
  "(P x \<Rightarrow> Q x)\<lbrakk>x\<rightarrow>v\<rbrakk> = ((P x)\<lbrakk>x\<rightarrow>v\<rbrakk> \<Rightarrow> (Q x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (pred_auto)

lemma msubst_implies_2 [usubst]:
  "(P x y \<Rightarrow> Q x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk> = ((P x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk> \<Rightarrow> (Q x y)\<lbrakk>(x,y)\<rightarrow>v\<rbrakk>)"
  by (pred_auto)+

lemma msubst_shAll [usubst]:
  "(\<^bold>\<forall> x \<bullet> P x y)\<lbrakk>y\<rightarrow>v\<rbrakk> = (\<^bold>\<forall> x \<bullet> (P x y)\<lbrakk>y\<rightarrow>v\<rbrakk>)"
  by (pred_auto)

lemma msubst_shAll_2 [usubst]:
  "(\<^bold>\<forall> x \<bullet> P x y z)\<lbrakk>(y,z)\<rightarrow>v\<rbrakk> = (\<^bold>\<forall> x \<bullet> (P x y z)\<lbrakk>(y,z)\<rightarrow>v\<rbrakk>)"
  by (pred_auto)+

subsection \<open> Sandbox for conjectures \<close>

definition utp_sandbox :: "'\<alpha> upred \<Rightarrow> bool" ("TRY'(_')") where
"TRY(P) = (P = undefined)"

translations
  "P" <= "CONST utp_sandbox P"

end