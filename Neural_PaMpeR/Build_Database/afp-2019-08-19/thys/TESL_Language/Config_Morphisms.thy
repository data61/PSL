theory Config_Morphisms
  imports Hygge_Theory
begin

text \<open>
  TESL morphisms change the time on clocks, preserving the ticks.
\<close>
consts morphism :: \<open>'a \<Rightarrow> ('\<tau>::linorder \<Rightarrow> '\<tau>::linorder) \<Rightarrow> 'a\<close> (infixl \<open>\<Otimes>\<close> 100)

text \<open>
  Applying a TESL morphism to a tag simply changes its value.
\<close>
overloading morphism_tagconst \<equiv> \<open>morphism :: '\<tau> tag_const \<Rightarrow> ('\<tau>::linorder \<Rightarrow> '\<tau>) \<Rightarrow> '\<tau> tag_const\<close> 
begin 
  definition morphism_tagconst :  
          \<open>(x::'\<tau> tag_const) \<Otimes> (f::('\<tau>::linorder \<Rightarrow> '\<tau>)) = (\<tau>\<^sub>c\<^sub>s\<^sub>t o f)(the_tag_const x) \<close> 
end

text \<open>
  Applying a TESL morphism to an atomic formula only changes the dates.
\<close>
overloading morphism_TESL_atomic \<equiv> 
            \<open>morphism :: '\<tau> TESL_atomic \<Rightarrow> ('\<tau>::linorder \<Rightarrow> '\<tau>) \<Rightarrow> '\<tau> TESL_atomic\<close> 
begin 
definition morphism_TESL_atomic : 
          \<open>(\<Psi>::'\<tau> TESL_atomic) \<Otimes> (f::('\<tau>::linorder \<Rightarrow> '\<tau>)) = 
              (case \<Psi> of
                (C sporadic t on C')     \<Rightarrow> (C sporadic (t\<Otimes>f) on C') 
              | (time-relation \<lfloor>C, C'\<rfloor>\<in>R)\<Rightarrow> (time-relation \<lfloor>C, C'\<rfloor> \<in> (\<lambda>(t, t'). R(t\<Otimes>f,t'\<Otimes>f)))
              | (C implies C')           \<Rightarrow> (C implies C')
              | (C implies not C')       \<Rightarrow> (C implies not C')       
              | (C time-delayed by t on C' implies C'') 
                                         \<Rightarrow> (C time-delayed by t\<Otimes>f on C' implies C'')
              | (C weakly precedes C')   \<Rightarrow> (C weakly precedes C')
              | (C strictly precedes C') \<Rightarrow> (C strictly precedes C') 
              | (C kills C')             \<Rightarrow> (C kills C'))\<close> 
end

text \<open>
  Applying a TESL morphism to a formula amounts to apply it to each atomic formula.
\<close>
overloading morphism_TESL_formula \<equiv> 
            \<open>morphism :: '\<tau> TESL_formula \<Rightarrow> ('\<tau>::linorder \<Rightarrow> '\<tau>) \<Rightarrow> '\<tau> TESL_formula\<close> 
begin 
definition  morphism_TESL_formula : 
           \<open>(\<Psi>::'\<tau> TESL_formula) \<Otimes> (f::('\<tau>::linorder \<Rightarrow> '\<tau>)) = map (\<lambda>x. x \<Otimes> f) \<Psi>\<close> 
end


text \<open>
  Applying a TESL morphism to a configuration amounts to apply it to the 
  present and future formulae. The past (in the context @{term \<open>\<Gamma>\<close>}) is not changed.
\<close>
overloading morphism_TESL_config \<equiv> 
            \<open>morphism :: ('\<tau>::linordered_field) config \<Rightarrow> ('\<tau> \<Rightarrow> '\<tau>) \<Rightarrow> '\<tau> config\<close> 
begin 
fun  morphism_TESL_config 
  where  \<open>((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)::('\<tau>::linordered_field) config) \<Otimes> (f::('\<tau> \<Rightarrow> '\<tau>)) =
           (\<Gamma>, n \<turnstile> (\<Psi>\<Otimes>f) \<triangleright> (\<Phi>\<Otimes>f))\<close> 
end

text \<open>
  A TESL formula is called consistent if it possesses Kripke-models 
  in its denotational interpretation.
\<close>

definition consistent :: \<open>('\<tau>::linordered_field) TESL_formula \<Rightarrow> bool\<close> 
  where   \<open>consistent \<Psi> \<equiv> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<noteq> {}\<close>


text \<open>
  If we can derive a consistent finite context from a TESL formula, the formula is consistent. 
\<close>
theorem consistency_finite :
  assumes start             : \<open>([], 0 \<turnstile> \<Psi> \<triangleright> [])  \<hookrightarrow>\<^sup>*\<^sup>* (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> [])\<close>
      and init_invariant    : \<open>consistent_context \<Gamma>\<^sub>1\<close>
    shows \<open>consistent \<Psi>\<close>    
proof -
  have * : \<open>\<exists> n. (([], 0 \<turnstile> \<Psi> \<triangleright> []) \<hookrightarrow>\<^bsup>n\<^esup> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> [] \<triangleright> []))\<close>
    by (simp add: rtranclp_imp_relpowp start)
  show ?thesis
  unfolding consistent_context_def consistent_def
  using * consistent_context_def init_invariant soundness by fastforce
qed

subsubsection \<open>Snippets on runs\<close>

text \<open>
  A run with no ticks and constant time for all clocks.
\<close>
definition const_nontick_run :: \<open>(clock \<Rightarrow> '\<tau> tag_const) \<Rightarrow> ('\<tau>::linordered_field) run \<close> (\<open>\<box>_\<close> 80)
  where \<open>\<box>f \<equiv>  Abs_run(\<lambda>n c. (False, f c))\<close>

text \<open>
  Ensure a clock ticks in a run at a given instant.
\<close>
definition set_tick :: \<open>('\<tau>::linordered_field) run \<Rightarrow> nat \<Rightarrow> clock \<Rightarrow> ('\<tau>) run\<close> 
  where   \<open>set_tick r k c = Abs_run(\<lambda>n c.  if k = n 
                                           then (True , time(Rep_run r k c)) 
                                           else Rep_run r k c) \<close>

text \<open>
  Ensure a clock does not tick in a run at a given instant.
\<close>
definition unset_tick :: \<open>('\<tau>::linordered_field) run \<Rightarrow> nat \<Rightarrow> clock \<Rightarrow> ('\<tau>) run\<close> 
  where   \<open>unset_tick r k c = Abs_run(\<lambda>n c.  if k = n 
                                           then (False , time(Rep_run r k c)) 
                                           else Rep_run r k c) \<close>

text \<open>
  Replace all instants after k in a run with the instants from another run.
  Warning: the result may not be a proper run since time may not be monotonous
  from instant k to instant k+1.
\<close>
definition patch :: \<open>('\<tau>::linordered_field) run \<Rightarrow> nat \<Rightarrow> '\<tau> run \<Rightarrow> '\<tau> run\<close> (\<open>_ \<ggreater>\<^bsup>_\<^esup> _\<close> 80)
  where   \<open>r \<ggreater>\<^bsup>k\<^esup>r' \<equiv> Abs_run(\<lambda>n c. if n \<le> k then Rep_run (r) n c else  Rep_run (r') n c)\<close>



text \<open>
  For some infinite cases, the idea for a proof scheme looks as follows: if we can derive
  from the initial configuration @{term \<open>([], 0 \<turnstile> \<Psi> \<triangleright> [])\<close>} a start-point of a lasso
  @{term \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)\<close>}, and if we can traverse the lasso one time 
  @{term \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow>\<^sup>+\<^sup>+ (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>} to isomorphic one, 
  we can always always make a derivation along the lasso. If the entry point of the lasso had traces 
  with prefixes consistent to @{term \<open>\<Gamma>\<^sub>1\<close>}, then there exist traces consisting of this prefix and 
  repetitions of the delta-prefix of the lasso which are consistent with @{term \<open>\<Psi>\<close>} which implies
  the logical consistency of  @{term \<open>\<Psi>\<close>}.
  
  So far the idea. Remains to prove it. Why does one symbolic run along a lasso generalises to 
  arbitrary runs ? 
\<close>

theorem consistency_coinduct : 
  assumes start             : \<open>([], 0 \<turnstile> \<Psi> \<triangleright> [])   \<hookrightarrow>\<^sup>*\<^sup>* (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)\<close>
      and loop              : \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) \<hookrightarrow>\<^sup>+\<^sup>+ (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
      and init_invariant    : \<open>consistent_context \<Gamma>\<^sub>1\<close>
      and post_invariant    : \<open>consistent_context \<Gamma>\<^sub>2\<close>
      and retract_condition : \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) \<Otimes> (f::'\<tau> \<Rightarrow> '\<tau>) = (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) \<close> 
    shows \<open>consistent (\<Psi> :: ('\<tau> :: linordered_field)TESL_formula)\<close>    
oops

end
