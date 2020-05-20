section \<open> Concurrent Programming \<close>

theory utp_concurrency
  imports
    utp_hoare
    utp_rel
    utp_tactics
    utp_theory
begin

text \<open> In this theory we describe the UTP scheme for concurrency, \emph{parallel-by-merge},
  which provides a general parallel operator parametrised by a ``merge predicate'' that explains
  how to merge the after states of the composed predicates. It can thus be applied to many languages
  and concurrency schemes, with this theory providing a number of generic laws. The operator is
  explained in more detail in Chapter 7 of the UTP book~\cite{Hoare&98}. \<close>
  
subsection \<open> Variable Renamings \<close>

text \<open> In parallel-by-merge constructions, a merge predicate defines the behaviour following execution of
  of parallel processes, $P \parallel Q$, as a relation that merges the output of $P$ and $Q$. In order 
  to achieve this we need to separate the variable values output from $P$ and $Q$, and in addition the 
  variable values before execution. The following three constructs do these separations. The initial
  state-space before execution is @{typ "'\<alpha>"}, the final state-space after the first parallel process
  is @{typ "'\<beta>\<^sub>0"}, and the final state-space for the second is @{typ "'\<beta>\<^sub>1"}. These three functions
  lift variables on these three state-spaces, respectively.
\<close>

alphabet ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg =
  mrg_prior :: "'\<alpha>"
  mrg_left  :: "'\<beta>\<^sub>0"
  mrg_right  :: "'\<beta>\<^sub>1"
    
definition pre_uvar :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('a \<Longrightarrow> ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg)" where
[upred_defs]: "pre_uvar x = x ;\<^sub>L mrg_prior"
  
definition left_uvar :: "('a \<Longrightarrow> '\<beta>\<^sub>0) \<Rightarrow> ('a \<Longrightarrow> ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg)" where
[upred_defs]: "left_uvar x = x ;\<^sub>L mrg_left"

definition right_uvar :: "('a \<Longrightarrow> '\<beta>\<^sub>1) \<Rightarrow> ('a \<Longrightarrow> ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg)" where
[upred_defs]: "right_uvar x = x ;\<^sub>L mrg_right"

text \<open> We set up syntax for the three variable classes using a subscript $<$, $0$-$x$, and $1$-$x$,
  respectively. \<close> 

syntax
  "_svarpre"   :: "svid \<Rightarrow> svid" ("_\<^sub><" [995] 995)
  "_svarleft"  :: "svid \<Rightarrow> svid" ("0-_" [995] 995)
  "_svarright" :: "svid \<Rightarrow> svid" ("1-_" [995] 995)

translations
  "_svarpre x"   == "CONST pre_uvar x"
  "_svarleft x"  == "CONST left_uvar x"
  "_svarright x" == "CONST right_uvar x"
  "_svarpre \<Sigma>"   <= "CONST pre_uvar 1\<^sub>L"
  "_svarleft \<Sigma>"  <= "CONST left_uvar 1\<^sub>L"
  "_svarright \<Sigma>" <= "CONST right_uvar 1\<^sub>L"  
  
text \<open> We proved behavedness closure properties about the lenses. \<close>
  
lemma left_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (left_uvar x)"
  by (simp add: left_uvar_def )

lemma right_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (right_uvar x)"
  by (simp add: right_uvar_def)

lemma pre_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (pre_uvar x)"
  by (simp add: pre_uvar_def)

lemma left_uvar_mwb [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (left_uvar x)"
  by (simp add: left_uvar_def )

lemma right_uvar_mwb [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (right_uvar x)"
  by (simp add: right_uvar_def)

lemma pre_uvar_mwb [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (pre_uvar x)"
  by (simp add: pre_uvar_def)
  
text \<open> We prove various independence laws about the variable classes. \<close>
  
lemma left_uvar_indep_right_uvar [simp]:
  "left_uvar x \<bowtie> right_uvar y"
  by (simp add: left_uvar_def right_uvar_def lens_comp_assoc[THEN sym])

lemma left_uvar_indep_pre_uvar [simp]:
  "left_uvar x \<bowtie> pre_uvar y"
  by (simp add: left_uvar_def pre_uvar_def)

lemma left_uvar_indep_left_uvar [simp]:
  "x \<bowtie> y \<Longrightarrow> left_uvar x \<bowtie> left_uvar y"
  by (simp add: left_uvar_def)

lemma right_uvar_indep_left_uvar [simp]:
  "right_uvar x \<bowtie> left_uvar y"
  by (simp add: lens_indep_sym)

lemma right_uvar_indep_pre_uvar [simp]:
  "right_uvar x \<bowtie> pre_uvar y"
  by (simp add: right_uvar_def pre_uvar_def)

lemma right_uvar_indep_right_uvar [simp]:
  "x \<bowtie> y \<Longrightarrow> right_uvar x \<bowtie> right_uvar y"
  by (simp add: right_uvar_def)

lemma pre_uvar_indep_left_uvar [simp]:
  "pre_uvar x \<bowtie> left_uvar y"
  by (simp add: lens_indep_sym)

lemma pre_uvar_indep_right_uvar [simp]:
  "pre_uvar x \<bowtie> right_uvar y"
  by (simp add: lens_indep_sym)

lemma pre_uvar_indep_pre_uvar [simp]:
  "x \<bowtie> y \<Longrightarrow> pre_uvar x \<bowtie> pre_uvar y"
  by (simp add: pre_uvar_def)

subsection \<open> Merge Predicates \<close>

text \<open> A merge predicate is a relation whose input has three parts: the prior variables, the output
  variables of the left predicate, and the output of the right predicate. \<close>
  
type_synonym '\<alpha> merge = "(('\<alpha>, '\<alpha>, '\<alpha>) mrg, '\<alpha>) urel"
  
text \<open> skip is the merge predicate which ignores the output of both parallel predicates \<close>

definition skip\<^sub>m :: "'\<alpha> merge" where
[upred_defs]: "skip\<^sub>m = ($\<^bold>v\<acute> =\<^sub>u $\<^bold>v\<^sub><)"

text \<open> swap is a predicate that the swaps the left and right indices; it is used to specify
        commutativity of the parallel operator \<close>

definition swap\<^sub>m :: "(('\<alpha>, '\<beta>, '\<beta>) mrg) hrel" where
[upred_defs]: "swap\<^sub>m = (0-\<^bold>v,1-\<^bold>v) := (&1-\<^bold>v,&0-\<^bold>v)"

text \<open> A symmetric merge is one for which swapping the order of the merged concurrent predicates
  has no effect. We represent this by the following healthiness condition that states that
  @{term "swap\<^sub>m"} is a left-unit. \<close>

abbreviation SymMerge :: "'\<alpha> merge \<Rightarrow> '\<alpha> merge" where
"SymMerge(M) \<equiv> (swap\<^sub>m ;; M)"

subsection \<open> Separating Simulations \<close>

text \<open> U0 and U1 are relations modify the variables of the input state-space such that they become 
  indexed with $0$ and $1$, respectively. \<close>

definition U0 :: "('\<beta>\<^sub>0, ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg) urel" where
[upred_defs]: "U0 = ($0-\<^bold>v\<acute> =\<^sub>u $\<^bold>v)"

definition U1 :: "('\<beta>\<^sub>1, ('\<alpha>, '\<beta>\<^sub>0, '\<beta>\<^sub>1) mrg) urel" where
[upred_defs]: "U1 = ($1-\<^bold>v\<acute> =\<^sub>u $\<^bold>v)"

lemma U0_swap: "(U0 ;; swap\<^sub>m) = U1"
  by (rel_auto)

lemma U1_swap: "(U1 ;; swap\<^sub>m) = U0"
  by (rel_auto)

text \<open> As shown below, separating simulations can also be expressed using the following two 
  alphabet extrusions \<close>

definition U0\<alpha> where [upred_defs]: "U0\<alpha> = (1\<^sub>L \<times>\<^sub>L mrg_left)"

definition U1\<alpha> where [upred_defs]: "U1\<alpha> = (1\<^sub>L \<times>\<^sub>L mrg_right)"

text \<open> We then create the following intuitive syntax for separating simulations. \<close>
  
abbreviation U0_alpha_lift ("\<lceil>_\<rceil>\<^sub>0") where "\<lceil>P\<rceil>\<^sub>0 \<equiv> P \<oplus>\<^sub>p U0\<alpha>"

abbreviation U1_alpha_lift ("\<lceil>_\<rceil>\<^sub>1") where "\<lceil>P\<rceil>\<^sub>1 \<equiv> P \<oplus>\<^sub>p U1\<alpha>"
  
text \<open> @{term "\<lceil>P\<rceil>\<^sub>0"} is predicate $P$ where all variables are indexed by $0$, and 
  @{term "\<lceil>P\<rceil>\<^sub>1"} is where all variables are indexed by $1$. We can thus equivalently express separating 
  simulations using alphabet extrusion. \<close>
  
lemma U0_as_alpha: "(P ;; U0) = \<lceil>P\<rceil>\<^sub>0"
  by (rel_auto)

lemma U1_as_alpha: "(P ;; U1) = \<lceil>P\<rceil>\<^sub>1"
  by (rel_auto)

lemma U0\<alpha>_vwb_lens [simp]: "vwb_lens U0\<alpha>"
  by (simp add: U0\<alpha>_def id_vwb_lens prod_vwb_lens)

lemma U1\<alpha>_vwb_lens [simp]: "vwb_lens U1\<alpha>"
  by (simp add: U1\<alpha>_def id_vwb_lens prod_vwb_lens)

lemma U0\<alpha>_indep_right_uvar [simp]: "vwb_lens x \<Longrightarrow> U0\<alpha> \<bowtie> out_var (right_uvar x)"
  by (force intro: plus_pres_lens_indep fst_snd_lens_indep lens_indep_left_comp
            simp add: U0\<alpha>_def right_uvar_def out_var_def prod_as_plus lens_comp_assoc[THEN sym])

lemma U1\<alpha>_indep_left_uvar [simp]: "vwb_lens x \<Longrightarrow> U1\<alpha> \<bowtie> out_var (left_uvar x)"
  by (force intro: plus_pres_lens_indep fst_snd_lens_indep lens_indep_left_comp
            simp add: U1\<alpha>_def left_uvar_def out_var_def prod_as_plus lens_comp_assoc[THEN sym])

lemma U0_alpha_lift_bool_subst [usubst]:
  "\<sigma>($0-x\<acute> \<mapsto>\<^sub>s true) \<dagger> \<lceil>P\<rceil>\<^sub>0 = \<sigma> \<dagger> \<lceil>P\<lbrakk>true/$x\<acute>\<rbrakk>\<rceil>\<^sub>0"
  "\<sigma>($0-x\<acute> \<mapsto>\<^sub>s false) \<dagger> \<lceil>P\<rceil>\<^sub>0 = \<sigma> \<dagger> \<lceil>P\<lbrakk>false/$x\<acute>\<rbrakk>\<rceil>\<^sub>0"
  by (pred_auto+)

lemma U1_alpha_lift_bool_subst [usubst]:
  "\<sigma>($1-x\<acute> \<mapsto>\<^sub>s true) \<dagger> \<lceil>P\<rceil>\<^sub>1 = \<sigma> \<dagger> \<lceil>P\<lbrakk>true/$x\<acute>\<rbrakk>\<rceil>\<^sub>1"
  "\<sigma>($1-x\<acute> \<mapsto>\<^sub>s false) \<dagger> \<lceil>P\<rceil>\<^sub>1 = \<sigma> \<dagger> \<lceil>P\<lbrakk>false/$x\<acute>\<rbrakk>\<rceil>\<^sub>1"
  by (pred_auto+)

lemma U0_alpha_out_var [alpha]: "\<lceil>$x\<acute>\<rceil>\<^sub>0 = $0-x\<acute>"
  by (rel_auto)

lemma U1_alpha_out_var [alpha]: "\<lceil>$x\<acute>\<rceil>\<^sub>1 = $1-x\<acute>"
  by (rel_auto)

lemma U0_skip [alpha]: "\<lceil>II\<rceil>\<^sub>0 = ($0-\<^bold>v\<acute> =\<^sub>u $\<^bold>v)"
  by (rel_auto)

lemma U1_skip [alpha]: "\<lceil>II\<rceil>\<^sub>1 = ($1-\<^bold>v\<acute> =\<^sub>u $\<^bold>v)"
  by (rel_auto)

lemma U0_seqr [alpha]: "\<lceil>P ;; Q\<rceil>\<^sub>0 = P ;; \<lceil>Q\<rceil>\<^sub>0"
  by (rel_auto)

lemma U1_seqr [alpha]: "\<lceil>P ;; Q\<rceil>\<^sub>1 = P ;; \<lceil>Q\<rceil>\<^sub>1"
  by (rel_auto)

lemma U0\<alpha>_comp_in_var [alpha]: "(in_var x) ;\<^sub>L U0\<alpha> = in_var x"
  by (simp add: U0\<alpha>_def alpha_in_var in_var_prod_lens pre_uvar_def)

lemma U0\<alpha>_comp_out_var [alpha]: "(out_var x) ;\<^sub>L U0\<alpha> = out_var (left_uvar x)"
  by (simp add: U0\<alpha>_def alpha_out_var id_wb_lens left_uvar_def out_var_prod_lens)

lemma U1\<alpha>_comp_in_var [alpha]: "(in_var x) ;\<^sub>L U1\<alpha> = in_var x"
  by (simp add: U1\<alpha>_def alpha_in_var in_var_prod_lens pre_uvar_def)

lemma U1\<alpha>_comp_out_var [alpha]: "(out_var x) ;\<^sub>L U1\<alpha> = out_var (right_uvar x)"
  by (simp add: U1\<alpha>_def alpha_out_var id_wb_lens right_uvar_def out_var_prod_lens)

subsection \<open> Associative Merges \<close>
  
text \<open> Associativity of a merge means that if we construct a three way merge from a two way merge
  and then rotate the three inputs of the merge to the left, then we get exactly the same three
  way merge back. 

  We first construct the operator that constructs the three way merge by effectively wiring up
  the two way merge in an appropriate way.
\<close>
  
definition ThreeWayMerge :: "'\<alpha> merge \<Rightarrow> (('\<alpha>, '\<alpha>, ('\<alpha>, '\<alpha>, '\<alpha>) mrg) mrg, '\<alpha>) urel" ("\<^bold>M3'(_')") where
[upred_defs]: "ThreeWayMerge M = (($0-\<^bold>v\<acute> =\<^sub>u $0-\<^bold>v \<and> $1-\<^bold>v\<acute> =\<^sub>u $1-0-\<^bold>v \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v\<^sub><) ;; M ;; U0 \<and> $1-\<^bold>v\<acute> =\<^sub>u $1-1-\<^bold>v \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v\<^sub><) ;; M"
  
text \<open> The next definition rotates the inputs to a three way merge to the left one place. \<close>

abbreviation rotate\<^sub>m where "rotate\<^sub>m \<equiv> (0-\<^bold>v,1-0-\<^bold>v,1-1-\<^bold>v) := (&1-0-\<^bold>v,&1-1-\<^bold>v,&0-\<^bold>v)"

text \<open> Finally, a merge is associative if rotating the inputs does not effect the output. \<close>
  
definition AssocMerge :: "'\<alpha> merge \<Rightarrow> bool" where
[upred_defs]: "AssocMerge M = (rotate\<^sub>m ;; \<^bold>M3(M) = \<^bold>M3(M))"
    
subsection \<open> Parallel Operators \<close>

text \<open> We implement the following useful abbreviation for separating of two parallel processes and
  copying of the before variables, all to act as input to the merge predicate. \<close>

abbreviation par_sep (infixr "\<parallel>\<^sub>s" 85) where
"P \<parallel>\<^sub>s Q \<equiv> (P ;; U0) \<and> (Q ;; U1) \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v"

text \<open> The following implementation of parallel by merge is less general than the book version, in
  that it does not properly partition the alphabet into two disjoint segments. We could actually
  achieve this specifying lenses into the larger alphabet, but this would complicate the definition
  of programs. May reconsider later. \<close>

definition 
  par_by_merge :: "('\<alpha>, '\<beta>) urel \<Rightarrow> (('\<alpha>, '\<beta>, '\<gamma>) mrg, '\<delta>) urel \<Rightarrow> ('\<alpha>, '\<gamma>) urel \<Rightarrow> ('\<alpha>, '\<delta>) urel" 
  ("_ \<parallel>\<^bsub>_\<^esub> _" [85,0,86] 85)
where [upred_defs]: "P \<parallel>\<^bsub>M\<^esub> Q = (P \<parallel>\<^sub>s Q ;; M)"

lemma par_by_merge_alt_def: "P \<parallel>\<^bsub>M\<^esub> Q = (\<lceil>P\<rceil>\<^sub>0 \<and> \<lceil>Q\<rceil>\<^sub>1 \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M"
  by (simp add: par_by_merge_def U0_as_alpha U1_as_alpha)

lemma shEx_pbm_left: "((\<^bold>\<exists> x \<bullet> P x) \<parallel>\<^bsub>M\<^esub> Q) = (\<^bold>\<exists> x \<bullet> (P x \<parallel>\<^bsub>M\<^esub> Q))"
  by (rel_auto)

lemma shEx_pbm_right: "(P \<parallel>\<^bsub>M\<^esub> (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P \<parallel>\<^bsub>M\<^esub> Q x))"
  by (rel_auto)

subsection \<open> Unrestriction Laws \<close>
  
lemma unrest_in_par_by_merge [unrest]:
  "\<lbrakk> $x \<sharp> P; $x\<^sub>< \<sharp> M; $x \<sharp> Q \<rbrakk> \<Longrightarrow> $x \<sharp> P \<parallel>\<^bsub>M\<^esub> Q"
  by (rel_auto, fastforce+)

lemma unrest_out_par_by_merge [unrest]:
  "\<lbrakk> $x\<acute> \<sharp> M \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P \<parallel>\<^bsub>M\<^esub> Q"
  by (rel_auto)
    
subsection \<open> Substitution laws \<close>

text \<open> Substitution is a little tricky because when we push the expression through the composition
  operator the alphabet of the expression must also change. Consequently for now we only support
  literal substitution, though this could be generalised with suitable alphabet coercsions. We
  need quite a number of variants to support this which are below. \<close>

lemma U0_seq_subst: "(P ;; U0)\<lbrakk>\<guillemotleft>v\<guillemotright>/$0-x\<acute>\<rbrakk> = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; U0)"
  by (rel_auto)

lemma U1_seq_subst: "(P ;; U1)\<lbrakk>\<guillemotleft>v\<guillemotright>/$1-x\<acute>\<rbrakk> = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; U1)"
  by (rel_auto)

lemma lit_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk>\<^esub> Q)"
  by (rel_auto)+

lemma bool_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s false) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>false/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>false/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>false/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s true) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>true/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>true/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>true/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s false) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>false/$x\<acute>\<rbrakk>\<^esub> Q)"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s true) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>true/$x\<acute>\<rbrakk>\<^esub> Q)"
  by (rel_auto)+

lemma zero_one_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 0) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>0/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>0/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>0/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 1) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>1/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>1/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>1/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 0) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>0/$x\<acute>\<rbrakk>\<^esub> Q)"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 1) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>1/$x\<acute>\<rbrakk>\<^esub> Q)"
  by (rel_auto)+

lemma numeral_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s numeral n) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>numeral n/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>numeral n/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>numeral n/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s numeral n) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>numeral n/$x\<acute>\<rbrakk>\<^esub> Q)"
  by (rel_auto)+

subsection \<open> Parallel-by-merge laws \<close>

lemma par_by_merge_false [simp]:
  "P \<parallel>\<^bsub>false\<^esub> Q = false"
  by (rel_auto)

lemma par_by_merge_left_false [simp]:
  "false \<parallel>\<^bsub>M\<^esub> Q = false"
  by (rel_auto)

lemma par_by_merge_right_false [simp]:
  "P \<parallel>\<^bsub>M\<^esub> false = false"
  by (rel_auto)

lemma par_by_merge_seq_add: "(P \<parallel>\<^bsub>M\<^esub> Q) ;; R = (P \<parallel>\<^bsub>M ;; R\<^esub> Q)"
  by (simp add: par_by_merge_def seqr_assoc)

text \<open> A skip parallel-by-merge yields a skip whenever the parallel predicates are both feasible. \<close>

lemma par_by_merge_skip:
  assumes "P ;; true = true" "Q ;; true = true"
  shows "P \<parallel>\<^bsub>skip\<^sub>m\<^esub> Q = II"
  using assms by (rel_auto)

lemma skip_merge_swap: "swap\<^sub>m ;; skip\<^sub>m = skip\<^sub>m"
  by (rel_auto)

lemma par_sep_swap: "P \<parallel>\<^sub>s Q ;; swap\<^sub>m = Q \<parallel>\<^sub>s P"
  by (rel_auto)
        
text \<open> Parallel-by-merge commutes when the merge predicate is unchanged by swap \<close>

lemma par_by_merge_commute_swap:
  shows "P \<parallel>\<^bsub>M\<^esub> Q = Q \<parallel>\<^bsub>swap\<^sub>m ;; M\<^esub> P"
proof -
  have "Q \<parallel>\<^bsub>swap\<^sub>m ;; M\<^esub> P = ((((Q ;; U0) \<and> (P ;; U1) \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; swap\<^sub>m) ;; M)"
    by (simp add: par_by_merge_def seqr_assoc)
  also have "... = (((Q ;; U0 ;; swap\<^sub>m) \<and> (P ;; U1 ;; swap\<^sub>m) \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M)"
    by (rel_auto)
  also have "... = (((Q ;; U1) \<and> (P ;; U0) \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; M)"
    by (simp add: U0_swap U1_swap)
  also have "... = P \<parallel>\<^bsub>M\<^esub> Q"
    by (simp add: par_by_merge_def utp_pred_laws.inf.left_commute)
  finally show ?thesis ..
qed

theorem par_by_merge_commute:
  assumes "M is SymMerge"
  shows "P \<parallel>\<^bsub>M\<^esub> Q = Q \<parallel>\<^bsub>M\<^esub> P"
  by (metis Healthy_if assms par_by_merge_commute_swap)
    
lemma par_by_merge_mono_1:
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2"
  shows "P\<^sub>1 \<parallel>\<^bsub>M\<^esub> Q \<sqsubseteq> P\<^sub>2 \<parallel>\<^bsub>M\<^esub> Q"
  using assms by (rel_auto)

lemma par_by_merge_mono_2:
  assumes "Q\<^sub>1 \<sqsubseteq> Q\<^sub>2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q\<^sub>1) \<sqsubseteq> (P \<parallel>\<^bsub>M\<^esub> Q\<^sub>2)"
  using assms by (rel_blast)

lemma par_by_merge_mono:
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2" "Q\<^sub>1 \<sqsubseteq> Q\<^sub>2"
  shows "P\<^sub>1 \<parallel>\<^bsub>M\<^esub> Q\<^sub>1 \<sqsubseteq> P\<^sub>2 \<parallel>\<^bsub>M\<^esub> Q\<^sub>2"
  by (meson assms dual_order.trans par_by_merge_mono_1 par_by_merge_mono_2)

theorem par_by_merge_assoc: 
  assumes "M is SymMerge" "AssocMerge M"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) \<parallel>\<^bsub>M\<^esub> R = P \<parallel>\<^bsub>M\<^esub> (Q \<parallel>\<^bsub>M\<^esub> R)"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) \<parallel>\<^bsub>M\<^esub> R = ((P ;; U0) \<and> (Q ;; U0 ;; U1) \<and> (R ;; U1 ;; U1) \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; \<^bold>M3(M)"
    by (rel_blast)
  also have "... = ((P ;; U0) \<and> (Q ;; U0 ;; U1) \<and> (R ;; U1 ;; U1) \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; rotate\<^sub>m ;; \<^bold>M3(M)"
    using AssocMerge_def assms(2) by force
  also have "... = ((Q ;; U0) \<and> (R ;; U0 ;; U1) \<and> (P ;; U1 ;; U1) \<and> $\<^bold>v\<^sub><\<acute> =\<^sub>u $\<^bold>v) ;; \<^bold>M3(M)"
    by (rel_blast)
  also have "... = (Q \<parallel>\<^bsub>M\<^esub> R) \<parallel>\<^bsub>M\<^esub> P"
    by (rel_blast)
  also have "... = P \<parallel>\<^bsub>M\<^esub> (Q \<parallel>\<^bsub>M\<^esub> R)"
    by (simp add: assms(1) par_by_merge_commute)
  finally show ?thesis .
qed
        
theorem par_by_merge_choice_left:
  "(P \<sqinter> Q) \<parallel>\<^bsub>M\<^esub> R = (P \<parallel>\<^bsub>M\<^esub> R) \<sqinter> (Q \<parallel>\<^bsub>M\<^esub> R)"
  by (rel_auto)
  
theorem par_by_merge_choice_right:
  "P \<parallel>\<^bsub>M\<^esub> (Q \<sqinter> R) = (P \<parallel>\<^bsub>M\<^esub> Q) \<sqinter> (P \<parallel>\<^bsub>M\<^esub> R)"
  by (rel_auto)

theorem par_by_merge_or_left:
  "(P \<or> Q) \<parallel>\<^bsub>M\<^esub> R = (P \<parallel>\<^bsub>M\<^esub> R \<or> Q \<parallel>\<^bsub>M\<^esub> R)"
  by (rel_auto)
  
theorem par_by_merge_or_right:
  "P \<parallel>\<^bsub>M\<^esub> (Q \<or> R) = (P \<parallel>\<^bsub>M\<^esub> Q \<or> P \<parallel>\<^bsub>M\<^esub> R)"
  by (rel_auto)
    
theorem par_by_merge_USUP_mem_left:
  "(\<Sqinter> i\<in>I \<bullet> P(i)) \<parallel>\<^bsub>M\<^esub> Q = (\<Sqinter> i\<in>I \<bullet> P(i) \<parallel>\<^bsub>M\<^esub> Q)"
  by (rel_auto)

theorem par_by_merge_USUP_ind_left:
  "(\<Sqinter> i \<bullet> P(i)) \<parallel>\<^bsub>M\<^esub> Q = (\<Sqinter> i \<bullet> P(i) \<parallel>\<^bsub>M\<^esub> Q)"
  by (rel_auto)
    
theorem par_by_merge_USUP_mem_right:
  "P \<parallel>\<^bsub>M\<^esub> (\<Sqinter> i\<in>I \<bullet> Q(i)) = (\<Sqinter> i\<in>I \<bullet> P \<parallel>\<^bsub>M\<^esub> Q(i))"
  by (rel_auto)

theorem par_by_merge_USUP_ind_right:
  "P \<parallel>\<^bsub>M\<^esub> (\<Sqinter> i \<bullet> Q(i)) = (\<Sqinter> i \<bullet> P \<parallel>\<^bsub>M\<^esub> Q(i))"
  by (rel_auto)
   
subsection \<open> Example: Simple State-Space Division \<close>
  
text \<open> The following merge predicate divides the state space using a pair of independent lenses. \<close>
  
definition StateMerge :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> merge" ("M[_|_]\<^sub>\<sigma>") where
[upred_defs]: "M[a|b]\<^sub>\<sigma> = ($\<^bold>v\<acute> =\<^sub>u ($\<^bold>v\<^sub>< \<oplus> $0-\<^bold>v on &a) \<oplus> $1-\<^bold>v on &b)"

lemma swap_StateMerge: "a \<bowtie> b \<Longrightarrow> (swap\<^sub>m ;; M[a|b]\<^sub>\<sigma>) = M[b|a]\<^sub>\<sigma>"
  by (rel_auto, simp_all add: lens_indep_comm)
   
abbreviation StateParallel :: "'\<alpha> hrel \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("_ |_|_|\<^sub>\<sigma> _" [85,0,0,86] 86)
where "P |a|b|\<^sub>\<sigma> Q \<equiv> P \<parallel>\<^bsub>M[a|b]\<^sub>\<sigma>\<^esub> Q"
    
lemma StateParallel_commute: "a \<bowtie> b \<Longrightarrow> P |a|b|\<^sub>\<sigma> Q = Q |b|a|\<^sub>\<sigma> P"
  by (metis par_by_merge_commute_swap swap_StateMerge)
        
lemma StateParallel_form: 
  "P |a|b|\<^sub>\<sigma> Q = (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1) \<bullet> P\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>/$\<^bold>v\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>st\<^sub>1\<guillemotright>/$\<^bold>v\<acute>\<rbrakk> \<and> $\<^bold>v\<acute> =\<^sub>u ($\<^bold>v \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &a) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &b)"
  by (rel_auto)

lemma StateParallel_form':
  assumes "vwb_lens a" "vwb_lens b" "a \<bowtie> b"
  shows "P |a|b|\<^sub>\<sigma> Q = {&a,&b}:[(P \<restriction>\<^sub>v {$\<^bold>v,$a\<acute>}) \<and> (Q \<restriction>\<^sub>v {$\<^bold>v,$b\<acute>})]"
  using assms
  apply (simp add: StateParallel_form, rel_auto)
     apply (metis vwb_lens_wb wb_lens_axioms_def wb_lens_def)
    apply (metis vwb_lens_wb wb_lens.get_put)
   apply (simp add: lens_indep_comm)
  apply (metis (no_types, hide_lams) lens_indep_comm vwb_lens_wb wb_lens_def weak_lens.put_get)
  done  
  
text \<open> We can frame all the variables that the parallel operator refers to \<close>
    
lemma StateParallel_frame:
  assumes "vwb_lens a" "vwb_lens b" "a \<bowtie> b"
  shows "{&a,&b}:[P |a|b|\<^sub>\<sigma> Q] = P |a|b|\<^sub>\<sigma> Q"
  using assms
  apply (simp add: StateParallel_form, rel_auto)
  using lens_indep_comm apply fastforce+
  done

text \<open> Parallel Hoare logic rule. This employs something similar to separating conjunction in
  the postcondition, but we explicitly require that the two conjuncts only refer to variables
  on the left and right of the parallel composition explicitly. \<close>
  
theorem StateParallel_hoare [hoare]:
  assumes "\<lbrace>c\<rbrace>P\<lbrace>d\<^sub>1\<rbrace>\<^sub>u" "\<lbrace>c\<rbrace>Q\<lbrace>d\<^sub>2\<rbrace>\<^sub>u" "a \<bowtie> b" "a \<natural> d\<^sub>1" "b \<natural> d\<^sub>2"
  shows "\<lbrace>c\<rbrace>P |a|b|\<^sub>\<sigma> Q\<lbrace>d\<^sub>1 \<and> d\<^sub>2\<rbrace>\<^sub>u"
proof -
  \<comment> \<open> Parallelise the specification \<close>
  from assms(4,5)
  have 1:"(\<lceil>c\<rceil>\<^sub>< \<Rightarrow> \<lceil>d\<^sub>1 \<and> d\<^sub>2\<rceil>\<^sub>>) \<sqsubseteq> (\<lceil>c\<rceil>\<^sub>< \<Rightarrow> \<lceil>d\<^sub>1\<rceil>\<^sub>>) |a|b|\<^sub>\<sigma> (\<lceil>c\<rceil>\<^sub>< \<Rightarrow> \<lceil>d\<^sub>2\<rceil>\<^sub>>)" (is "?lhs \<sqsubseteq> ?rhs")
    by (simp add: StateParallel_form, rel_auto, metis assms(3) lens_indep_comm)
  \<comment> \<open> Prove Hoare rule by monotonicity of parallelism \<close>
  have 2:"?rhs \<sqsubseteq> P |a|b|\<^sub>\<sigma> Q"
  proof (rule par_by_merge_mono)
    show "(\<lceil>c\<rceil>\<^sub>< \<Rightarrow> \<lceil>d\<^sub>1\<rceil>\<^sub>>) \<sqsubseteq> P"
      using assms(1) hoare_r_def by auto
    show "(\<lceil>c\<rceil>\<^sub>< \<Rightarrow> \<lceil>d\<^sub>2\<rceil>\<^sub>>) \<sqsubseteq> Q"
      using assms(2) hoare_r_def by auto
  qed
  show ?thesis
    unfolding hoare_r_def using 1 2 order_trans by auto
qed

text \<open> Specialised version of the above law where an invariant expression referring to variables
  outside the frame is preserved. \<close>
  
theorem StateParallel_frame_hoare [hoare]:
  assumes "vwb_lens a" "vwb_lens b" "a \<bowtie> b" "a \<natural> d\<^sub>1" "b \<natural> d\<^sub>2" "a \<sharp> c\<^sub>1" "b \<sharp> c\<^sub>1" "\<lbrace>c\<^sub>1 \<and> c\<^sub>2\<rbrace>P\<lbrace>d\<^sub>1\<rbrace>\<^sub>u" "\<lbrace>c\<^sub>1 \<and> c\<^sub>2\<rbrace>Q\<lbrace>d\<^sub>2\<rbrace>\<^sub>u"
  shows "\<lbrace>c\<^sub>1 \<and> c\<^sub>2\<rbrace>P |a|b|\<^sub>\<sigma> Q\<lbrace>c\<^sub>1 \<and> d\<^sub>1 \<and> d\<^sub>2\<rbrace>\<^sub>u"
proof -
  have "\<lbrace>c\<^sub>1 \<and> c\<^sub>2\<rbrace>{&a,&b}:[P |a|b|\<^sub>\<sigma> Q]\<lbrace>c\<^sub>1 \<and> d\<^sub>1 \<and> d\<^sub>2\<rbrace>\<^sub>u"
    by (auto intro!: frame_hoare_r' StateParallel_hoare simp add: assms unrest plus_vwb_lens)
  thus ?thesis
    by (simp add: StateParallel_frame assms)
qed
      
end