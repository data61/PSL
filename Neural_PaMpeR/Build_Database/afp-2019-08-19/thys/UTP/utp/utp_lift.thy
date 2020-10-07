section \<open> Lifting Expressions \<close>

theory utp_lift
  imports
    utp_alphabet
begin

subsection \<open> Lifting definitions \<close>

text \<open> We define operators for converting an expression to and from a relational state space
  with the help of alphabet extrusion and restriction. In general throughout Isabelle/UTP
  we adopt the notation $\lceil P \rceil$ with some subscript to denote lifting an expression
  into a larger alphabet, and $\lfloor P \rfloor$ for dropping into a smaller alphabet.

  The following two functions lift and drop an expression, respectively, whose alphabet is 
  @{typ "'\<alpha>"}, into a product alphabet @{typ "'\<alpha> \<times> '\<beta>"}. This allows us to deal with expressions
  which refer only to undashed variables, and use the type-system to ensure this. \<close>

abbreviation lift_pre :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uexpr" ("\<lceil>_\<rceil>\<^sub><")
where "\<lceil>P\<rceil>\<^sub>< \<equiv> P \<oplus>\<^sub>p fst\<^sub>L"

abbreviation drop_pre :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<lfloor>_\<rfloor>\<^sub><")
where "\<lfloor>P\<rfloor>\<^sub>< \<equiv> P \<restriction>\<^sub>e fst\<^sub>L"

text \<open> The following two functions lift and drop an expression, respectively, whose alphabet is 
  @{typ "'\<beta>"}, into a product alphabet @{typ "'\<alpha> \<times> '\<beta>"}. This allows us to deal with expressions
  which refer only to dashed variables. \<close>
  
abbreviation lift_post :: "('a, '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uexpr" ("\<lceil>_\<rceil>\<^sub>>")
where "\<lceil>P\<rceil>\<^sub>> \<equiv> P \<oplus>\<^sub>p snd\<^sub>L"

abbreviation drop_post :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta>) uexpr" ("\<lfloor>_\<rfloor>\<^sub>>")
where "\<lfloor>P\<rfloor>\<^sub>> \<equiv> P \<restriction>\<^sub>e snd\<^sub>L"
  
subsection \<open> Lifting Laws \<close>

text \<open> With the help of our alphabet laws, we can prove some intuitive laws about alphabet
  lifting. For example, lifting variables yields an unprimed or primed relational variable
  expression, respectively. \<close>
  
lemma lift_pre_var [simp]:
  "\<lceil>var x\<rceil>\<^sub>< = $x"
  by (alpha_tac)

lemma lift_post_var [simp]:
  "\<lceil>var x\<rceil>\<^sub>> = $x\<acute>"
  by (alpha_tac)

subsection \<open> Substitution Laws \<close>
    
lemma pre_var_subst [usubst]:
  "\<sigma>($x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> \<lceil>P\<rceil>\<^sub>< = \<sigma> \<dagger> \<lceil>P\<lbrakk>\<guillemotleft>v\<guillemotright>/&x\<rbrakk>\<rceil>\<^sub><"
  by (pred_simp)
    
subsection \<open> Unrestriction laws \<close>

text \<open> Crucially, the lifting operators allow us to demonstrate unrestriction properties. For
  example, we can show that no primed variable is restricted in an expression over only the
  first element of the state-space product type. \<close>
  
lemma unrest_dash_var_pre [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "$x\<acute> \<sharp> \<lceil>p\<rceil>\<^sub><"
  by (pred_auto)

end