theory IMP2
imports "automation/IMP2_VCG" "automation/IMP2_Specification"
begin

section \<open>IMP2 Setup\<close>

lemmas [deriv_unfolds] = Params_def Inline_def AssignIdx_retv_def ArrayCpy_retv_def


section \<open>Ad-Hoc Regression Tests\<close>
  
experiment begin

lemma upd_idxSame[named_ss vcg_bb]: "f(i:=a,i:=b) = f (i:=b)" by auto

lemmas [named_ss vcg_bb] = triv_forall_equality

declare [[eta_contract = false ]]  
program_spec (partial) p2
  assumes "n>0"  
  ensures "n=0"
  defines \<open>while (n>0) @invariant \<open>n\<ge>0\<close> { if (n+1>1) {
    n=n-1; 
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    G1=n; G2=n; G3=n; n=G1; n=G2; n=G3;
    skip
  } }\<close>
  apply vcg
  by auto

program_spec p2'
  assumes "n>0"  
  ensures "n=0"
  defines \<open>while (n>0) @variant \<open>n\<close> @invariant \<open>n\<ge>0\<close> { n=n-1 }\<close>
  apply vcg
  by auto

    
program_spec p2''
  assumes "n>0"  
  ensures "n=0"
  defines \<open>while (n>0) @relation \<open>measure nat\<close> @variant \<open>n\<close> @invariant \<open>n\<ge>0\<close> { n=n-1 }\<close>
  apply vcg
  by auto

program_spec p3  
  assumes "True"
  ensures "n = n\<^sub>0 \<and> N=42"
  defines \<open>
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope n = 0;
    scope {n = 0}; N=42
  \<close>
  apply vcg
  by auto
  
    
end


subsection \<open>More Regression Tests\<close>

experiment begin

lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib 


program_spec exp_count_up1
  assumes "0\<le>n"
  ensures "a = 2^nat n\<^sub>0"
  defines \<open>
    a = 1;
    c = 0;
    while (c<n) 
      @variant \<open>n-c\<close> 
      @invariant \<open>0\<le>c \<and> c\<le>n \<and> a=2^nat c\<close>    
    {
      a=2*a;
      
      
      c=c+1
    }
  \<close>
  apply vcg
  by (auto simp: algebra_simps nat_distribs)


program_spec exp_count_up1'
  assumes "0\<le>n"
  ensures "a = 2^nat n\<^sub>0"
  defines \<open>
    a = 1;
    c = 0;
    while (c<n) 
      @variant \<open>n-c\<close> 
      @invariant \<open>0\<le>c \<and> c\<le>n \<and> a=2^nat c\<close>    
    {
      a=2*a; a=2*a; a=2*a; a=2*a;
      a=a / 2; a=a / 2; a=a / 2; a=a / 2; 
      
      a=2*a;
      c=c+1
    }
  \<close>
  apply vcg
  by (auto simp: algebra_simps nat_distribs)
  
  
(* We've made the program a little larger \<dots> *)
program_spec exp_count_up
  assumes "0\<le>n"
  ensures "a = 2^nat n\<^sub>0"
  defines \<open>
    a = 1;
    c = 0;
    while (c<n) 
      @variant \<open>n-c\<close> 
      @invariant \<open>0\<le>c \<and> c\<le>n \<and> a=2^nat c\<close>    
    {
      a=2*a;
      
      {
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;

      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;

      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;

      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;

      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;

      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;

      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;

      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;

      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;   a=2*a;    a=2*a;    a=2*a;   a=2*a;    a=2*a;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;  a=a / 2; a=a / 2;  a=a / 2;
      skip
      };
      
      c=c+1
    }
  \<close>
  apply vcg
      apply (all \<open>simp?\<close>)
  apply (auto simp: algebra_simps nat_distribs)
  done

  
program_spec exp_count_up3
  assumes "0\<le>n"
  ensures "a = 2^nat n\<^sub>0"
  defines \<open>
    a = 1;
    c = 0;
    while (c<n) 
      @variant \<open>n-c\<close> 
      @invariant \<open>0\<le>c \<and> c\<le>n \<and> a=2^nat c\<close>    
    {
      a=2*a;
      
      { \<comment> \<open>Note, this provokes exponential blowup of intermediate, unsimplified terms! \<close>
      a=a+a; a=a+a; a=a+a; a = a/8;
      a=a+a; a=a+a; a=a+a; a = a/8;
      a=a+a; a=a+a; a=a+a; a = a/8;
      a=a+a; a = a/2;
      
      skip
      };
      
      c=c+1
    }
  \<close>
  apply vcg
      apply (all \<open>simp?\<close>)
  apply (auto simp: algebra_simps nat_distribs)
  done
  
  
    
end


experiment
begin

lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib


procedure_spec exp_count_up (n) returns a
  assumes "0\<le>n"
  ensures "a = 2^nat n\<^sub>0"
  defines \<open>
      a = 1;
      c = 0;
      while (c<n) 
        @variant \<open>n-c\<close>
        @invariant \<open>0\<le>c \<and> c\<le>n \<and> a=2^nat c\<close>
      {
        a=2*a;
        c=c+1
      }
  \<close>
  apply vcg
  by (auto simp: algebra_simps nat_distribs)

program_spec use_exp 
  assumes "0\<le>n"
  ensures \<open>n = 2^(2^nat n\<^sub>0)\<close>
  defines \<open>
    n = exp_count_up(n);
    n = exp_count_up(n)
  \<close>
  apply vcg
  by auto


  
procedure_spec add3 (a, b, c) returns r
  assumes "a\<ge>0 \<and>b\<ge>0 \<and>c\<ge>0"  
  ensures "r = a\<^sub>0+b\<^sub>0+c\<^sub>0"
  defines \<open>
    r = a+b+c
  \<close>
  apply vcg
  by auto
  
procedure_spec use_add3 (a, b) returns r
  assumes "a\<ge>0 \<and> b\<ge>0"  
  ensures "r = 2*(a\<^sub>0+b\<^sub>0+b\<^sub>0)"
  defines \<open>
    r1 = add3(a, b, b);
    r2 = add3(a, b, b);
    r = r1+r2
  \<close>
  apply vcg
  by auto


procedure_spec divmod (a,b) returns (c,d)  
  assumes "b\<noteq>0"
  ensures "c = a\<^sub>0 div b\<^sub>0 \<and> d = a\<^sub>0 mod b\<^sub>0"
  defines \<open>
    c = a / b;
    d = a mod b
  \<close>
  apply vcg
  by auto
  
procedure_spec use_divmod (a,b) returns r
  assumes "b\<noteq>0"
  ensures "r = a\<^sub>0"
  defines \<open>
    (d,m) = divmod (a,b);
    r = d*b + m
  \<close>
  apply vcg
  by simp
  
  
    
end
  
experiment
begin

lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib


procedure_spec exp_count_up (n) returns a
  assumes "0\<le>n"
  ensures "a = 2^nat n\<^sub>0"
  defines \<open>
      a = 1;
      c = 0;
      while (c<n) 
        @variant \<open>n-c\<close> 
        @invariant \<open>0\<le>c \<and> c\<le>n \<and> a=2^nat c\<close>
      {
        a=2*a;
        c=c+1
      }
      
  \<close>
  apply vcg
  by (auto simp: algebra_simps nat_distribs)
  

program_spec use_exp 
  assumes "0\<le>n"
  ensures \<open>n = 2^(2^nat n\<^sub>0)\<close>
  defines \<open>
    n = exp_count_up(n);
    n = exp_count_up(n)
  \<close>
  apply vcg
  by auto

text \<open>Deriving big-step semantics\<close>
schematic_goal 
  "Map.empty: (use_exp,<''n'':=\<lambda>_. 2>) \<Rightarrow> ?s"
  "?s ''G_ret_1'' 0 = 16"
  unfolding use_exp_def exp_count_up_def
  apply big_step []
  by bs_simp

schematic_goal 
  "Map.empty: (use_exp,<''n'':=\<lambda>_. 2>) \<Rightarrow> ?s"
  "?s ''G_ret_1'' 0 = 16"
  unfolding use_exp_def exp_count_up_def
  apply (big_step'+) []
  by bs_simp
  
    
procedure_spec add3 (a, b, c) returns r
  assumes "a\<ge>0 \<and>b\<ge>0 \<and>c\<ge>0"  
  ensures "r = a\<^sub>0+b\<^sub>0+c\<^sub>0"
  defines \<open>
    r = a+b+c
  \<close>
  apply vcg
  by auto
  
procedure_spec use_add3 (a, b) returns r
  assumes "a\<ge>0 \<and> b\<ge>0"  
  ensures "r = 2*(a\<^sub>0+b\<^sub>0+b\<^sub>0)"
  defines \<open>
    r1 = add3(a, b, b);
    r2 = add3(a, b, b);
    r = r1+r2
  \<close>
  apply vcg
  by auto
  
procedure_spec no_param () returns r
  assumes "True"
  ensures "r = 42"  
  defines \<open>r = 42\<close>
  by vcg_cs
  
procedure_spec foobar (a) returns r
  assumes \<open>a\<ge>0\<close>
  ensures "r=84+a\<^sub>0"
  defines \<open>
    r1 = no_param();
    add3(a, a, r1);
    r2 = add3(a, r1, r1);
    r = r2
  \<close>
  apply vcg_cs
  done
  
end

experiment begin  

  lemma [named_ss vcg_bb]: "BB_PROTECT True" by (auto simp: BB_PROTECT_def)

  procedure_spec add (a,b) returns r assumes True ensures "r=a\<^sub>0+b\<^sub>0" defines \<open>r = a + b\<close> by vcg_cs

  procedure_spec test (a) returns r assumes True ensures "r = a\<^sub>0" defines \<open>
    x1 = add(a,a);
    x2 = add(a,a);
    x3 = add (x1-x2, a);
    
    x1 = add(a,a);
    x2 = add(a,a);
    x3 = add (x1-x2, a);
  
    x1 = add(a,a);
    x2 = add(a,a);
    x3 = add (x1-x2, a);
  
    x1 = add(a,a);
    x2 = add(a,a);
    x3 = add (x1-x2, a);
  
    x1 = add(a,a);
    x2 = add(a,a);
    x3 = add (x1-x2, a);
  
    x1 = add(a,a);
    x2 = add(a,a);
    x3 = add (x1-x2, a);
  
    r = x3
  \<close>
  apply vcg
  by auto

end


experiment begin  

lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib 
  
recursive_spec 
  relation \<open>measure nat\<close>
  foo (a) returns b 
    assumes "a\<ge>0"
    ensures "b = 2^nat a\<^sub>0"
    variant "a"
    defines \<open>
      if (a==0) b=1
      else {
        b = rec foo (a-1);
        b = 2 * b
      }
    \<close>
  thm vcg_specs  
  apply vcg
  apply (auto simp: nat_distribs algebra_simps)
  by (metis (full_types) Suc_pred le0 le_less nat_0_iff not_le power_Suc)
  
thm foo_spec  
  
  
recursive_spec 
  odd (a) returns b 
    assumes "a\<ge>0"
    ensures "b\<noteq>0 \<longleftrightarrow> odd a\<^sub>0"
    variant "a"
    defines \<open>
      if (a==0) b=0
      else {
        b = rec even (a-1)
      }
    \<close>
  and
  even (a) returns b
    assumes \<open>a\<ge>0\<close>
    ensures "b\<noteq>0 \<longleftrightarrow> even a\<^sub>0"
    variant "a"
    defines \<open>
      if (a==0) b=1
      else {
        b = rec odd (a-1)
      }
    \<close>
  apply vcg  
  by auto  

thm even_spec odd_spec
  

    
end  

end
