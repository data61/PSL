section \<open>Introduction to IMP2-VCG, based on IMP\<close>
theory IMP2_from_IMP
imports "../IMP2"
begin

  text \<open>This document briefly introduces the extensions of IMP2 over IMP.\<close>

  subsection \<open>Fancy Syntax\<close>
  
  text \<open>Standard Syntax\<close>
  definition "exp_count_up1 \<equiv> 
    ''a'' ::= N 1;;
    ''c'' ::= N 0;;
    WHILE Cmpop (<) (V ''c'') (V ''n'') DO (
      ''a'' ::= Binop (*) (N 2) (V ''a'');; 
      ''c'' ::= Binop (+) (V ''c'') (N 1))"

  (* Type \ < ^ imp > \open \close , without the spaces.
  
    for \<open>\<dots>\<close>, there is an autocompletion if you type a quote (")
    
    for \<comment> \<open>\<close>, type \comment and use autocompletion
    
  *)
  text \<open>Fancy Syntax\<close>
  definition "exp_count_up2 \<equiv> \<^imp>\<open>
    \<comment> \<open>Initialization\<close>
    a = 1;
    c = 0;
    while (c<n) { \<comment> \<open>Iterate until \<open>c\<close> has reached \<open>n\<close>\<close>
      a=2*a; \<comment> \<open>Double \<open>a\<close>\<close>
      c=c+1  \<comment> \<open>Increment \<open>c\<close>\<close>
    }
  \<close>"    
      
  lemma "exp_count_up1 = exp_count_up2"
    unfolding exp_count_up1_def exp_count_up2_def ..
  
  

  subsection \<open>Operators and Arrays\<close>

  text \<open>We reflect arbitrary Isabelle functions into the syntax: \<close>
  value "bval (Cmpop (\<le>) (Binop (+) (Unop uminus (V ''x'')) (N 42)) (N 50)) <''x'':=(\<lambda>_. -5)> "
    
  thm aval.simps bval.simps

  text \<open>Every variable is an array, indexed by integers, no bounds.
    Syntax shortcuts to access index 0.
  \<close>  

  term \<open>Vidx ''a'' (i::aexp)\<close> \<comment> \<open>Array access at index \<open>i\<close>\<close>
  lemma "V ''x'' = Vidx ''x'' (N 0)" .. \<comment> \<open>Shortcut for access at index \<open>0\<close>\<close>
  
  text \<open>New commands:\<close>
  term \<open>AssignIdx ''a'' (i::aexp) (v::aexp)\<close> \<comment> \<open>Assign at index. Replaces assign.\<close>
  term \<open>''a''[i] ::= v\<close>  \<comment> \<open>Standard syntax\<close>
  term \<open>\<^imp>\<open> a[i] = v \<close>\<close> \<comment> \<open>Fancy syntax\<close>
  
  lemma \<open>Assign ''x'' v = AssignIdx ''x'' (N 0) v\<close> .. \<comment> \<open>Shortcut for assignment to index \<open>0\<close>\<close>
  term \<open>''x'' ::= v\<close> term \<open>\<^imp>\<open>x = v+1\<close>\<close>
  
  text \<open>Note: In fancy syntax, assignment between variables is always parsed as array copy.
    This is no problem unless a variable is used as both, array and plain value, 
    which should be avoided anyway.
  \<close>
    
  term \<open>ArrayCpy ''d'' ''s''\<close> \<comment> \<open>Copy whole array. Both operands are variable names.\<close>
  term \<open>''d''[] ::= ''s''\<close> term \<open>\<^imp>\<open>d = s\<close>\<close>
  
  term \<open>ArrayClear ''a''\<close> \<comment> \<open>Initialize array to all zeroes.\<close>
  term \<open>CLEAR ''a''[]\<close> term \<open>\<^imp>\<open>clear a[]\<close>\<close>

  text \<open>Semantics of these is straightforward\<close>
  thm big_step.AssignIdx big_step.ArrayCpy big_step.ArrayClear
  
  subsection \<open>Local and Global Variables\<close>
  term \<open>is_global\<close> term \<open>is_local\<close> \<comment> \<open>Partitions variable names\<close>
  term \<open><s\<^sub>1|s\<^sub>2>\<close> \<comment> \<open>State with locals from \<open>s\<^sub>1\<close> and globals from \<open>s\<^sub>2\<close>\<close>
  
  term \<open>SCOPE c\<close> term \<open>\<^imp>\<open>scope { skip }\<close>\<close>    \<comment> \<open>Execute \<open>c\<close> with fresh set of local variables\<close>
  thm big_step.Scope
  
  subsubsection \<open>Parameter Passing\<close>
  text \<open>Parameters and return values by global variables: This is syntactic sugar only:\<close>
  context fixes f :: com begin
  term \<open>\<^imp>\<open> (r1,r2) = f(x1,x2,x3)\<close>\<close>
  end
  
  
  subsection \<open>Recursive procedures\<close>
  term \<open>PCall ''name''\<close> 
  thm big_step.PCall
  
  subsubsection \<open>Procedure Scope\<close>
  text \<open>Execute command with local set of procedures\<close>
  term \<open>PScope \<pi> c\<close>
  thm big_step.PScope
  
  subsubsection \<open>Syntactic sugar for procedure call with parameters\<close>
  term \<open>\<^imp>\<open>(r1,r2) = rec name(x1,x2,x3)\<close>\<close>
  
  subsection \<open>More Readable VCs\<close>
  lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib
  
  lemma "s\<^sub>0 ''n'' 0 \<ge> 0 \<Longrightarrow> wlp \<pi> exp_count_up1 (\<lambda>s. s ''a'' 0 = 2^nat (s\<^sub>0 ''n'' 0)) s\<^sub>0"
    unfolding exp_count_up1_def
    apply (subst annotate_whileI[where 
          I="\<lambda>s. s ''n'' 0 = s\<^sub>0 ''n'' 0 \<and>  s ''a'' 0 = 2 ^ nat (s ''c'' 0) \<and> 0 \<le> s ''c'' 0 \<and> s ''c'' 0 \<le> s\<^sub>0 ''n'' 0" 
        ])
    apply (i_vcg_preprocess; i_vcg_gen; clarsimp)
    text \<open>The postprocessor converts from states applied to string names to actual variables\<close>
    apply i_vcg_postprocess
    by (auto simp: algebra_simps nat_distribs)
        
  lemma "s\<^sub>0 ''n'' 0 \<ge> 0 \<Longrightarrow> wlp \<pi> exp_count_up1 (\<lambda>s. s ''a'' 0 = 2^nat (s\<^sub>0 ''n'' 0)) s\<^sub>0"
    unfolding exp_count_up1_def
    apply (subst annotate_whileI[where 
          I="\<lambda>s. s ''n'' 0 = s\<^sub>0 ''n'' 0 \<and>  s ''a'' 0 = 2 ^ nat (s ''c'' 0) \<and> 0 \<le> s ''c'' 0 \<and> s ''c'' 0 \<le> s\<^sub>0 ''n'' 0" 
        ])
    text \<open>The postprocessor is invoked by default\<close>    
    apply vcg
    oops
    
    
  subsection \<open>Specification Commands\<close>    
  
  text \<open>IMP2 provides a set of commands to simplify specification and annotation of programs.\<close>

  text \<open>Old way of proving a specification: \<close>  
  lemma "let n = s\<^sub>0 ''n'' 0 in n \<ge> 0 
    \<Longrightarrow> wlp \<pi> exp_count_up1 (\<lambda>s. let a = s ''a'' 0; n\<^sub>0 = s\<^sub>0 ''n'' 0 in a = 2^nat (n\<^sub>0)) s\<^sub>0"
    unfolding exp_count_up1_def
    apply (subst annotate_whileI[where 
          I="\<lambda>s. s ''n'' 0 = s\<^sub>0 ''n'' 0 \<and>  s ''a'' 0 = 2 ^ nat (s ''c'' 0) \<and> 0 \<le> s ''c'' 0 \<and> s ''c'' 0 \<le> s\<^sub>0 ''n'' 0" 
          (* Similar for invar! *)
        ])
    apply vcg
    apply (auto simp: algebra_simps nat_distribs)
    done
  
  lemma "VAR (s x) P = (let v=s x in P v)" unfolding VAR_def by simp 

  text \<open>IMP2 specification commands\<close>
  program_spec (partial) exp_count_up
    assumes "0\<le>n"               \<comment> \<open>Precondition. Use variable names of program.\<close>
    ensures "a = 2^nat n\<^sub>0"       \<comment> \<open>Postcondition. Use variable names of programs. 
                                      Suffix with \<open>\<cdot>\<^sub>0\<close> to refer to initial state\<close>
    defines                     \<comment> \<open>Program\<close>
    \<open>
      a = 1;
      c = 0;
      while (c<n) 
        @invariant \<open>n=n\<^sub>0 \<and> a=2^nat c \<and> 0\<le>c \<and> c\<le>n\<close> \<comment> \<open>
            Invar annotation. Variable names and suffix \<open>\<cdot>\<^sub>0\<close> for variables from initial state.\<close>
      {
        a=2*a;
        c=c+1
      }
    \<close>
    apply vcg
    by (auto simp: algebra_simps nat_distribs)

  thm exp_count_up_spec  
  thm exp_count_up_def
      
  (* 
    We can also annotate 
      @variant \<open>measure-expression\<close> 
        (interpreted over variables (v) and variables at program start (v\<^sub>0) 
        
    or, both @variant \<open>\<dots>\<close> and @relation \<open>R\<close>:
      R :: 'a rel, and variant produces an 'a
      
  *)
          
  
  procedure_spec exp_count_up_proc(n) returns a
    assumes "0\<le>n"               
    ensures "a = 2^nat n\<^sub>0"      
    defines                     
    \<open>
      a = 1;
      c = 0;
      while (c<n) 
        @invariant \<open>n=n\<^sub>0 \<and> a=2^nat c \<and> 0\<le>c \<and> c\<le>n\<close> 
        @variant \<open>n-c\<close>
      {
        a=2*a;
        c=c+1
      }
    \<close>
    apply vcg
    by (auto simp: algebra_simps nat_distribs)
  
  text \<open>Simple Recursion\<close>
  recursive_spec 
    exp_rec(n) returns a assumes "0\<le>n" ensures "a=2^nat n\<^sub>0" variant "n"
    defines \<open>if (n==0) a=1 else {t=rec exp_rec(n-1); a=2*t}\<close>
    apply vcg
      apply (auto simp: algebra_simps nat_distribs)
    by (metis Suc_le_D diff_Suc_Suc dvd_1_left dvd_imp_le minus_nat.diff_0 nat_0_iff nat_int neq0_conv of_nat_0 order_class.order.antisym pos_int_cases power_Suc zless_nat_eq_int_zless)
    
  text \<open>Mutual Recursion: See Examples\<close>
        

end
