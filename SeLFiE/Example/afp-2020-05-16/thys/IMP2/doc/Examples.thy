theory Examples
imports "../IMP2" "../lib/IMP2_Aux_Lemmas"
begin

section \<open>Examples\<close>  
lemmas nat_distribs = nat_add_distrib nat_diff_distrib Suc_diff_le nat_mult_distrib nat_div_distrib

subsection \<open>Common Loop Patterns\<close>

subsubsection \<open>Count Up\<close>
text \<open>
  Counter \<open>c\<close> counts from \<open>0\<close> to \<open>n\<close>, such that loop is executed \<open>n\<close> times. 
  The result is computed in an accumulator \<open>a\<close>.
\<close>
text \<open>The invariant states that we have computed the function for the counter value \<open>c\<close>\<close>  
text \<open>The variant is the difference between \<open>n\<close> and \<open>c\<close>, i.e., the number of 
  loop iterations that we still have to do\<close>  


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
      G_par = a;   scope { a = G_par; a=2*a; G_ret = a }; a = G_ret;
      c=c+1
    }
  \<close>
  apply vcg
  by (auto simp: algebra_simps nat_distribs)

program_spec sum_prog
  assumes "n \<ge> 0" ensures "s = \<Sum>{0..n\<^sub>0}"
  defines \<open>
    s = 0;
    i = 0;
    while (i < n)
      @variant \<open>n\<^sub>0 - i\<close>
      @invariant \<open>n\<^sub>0 = n \<and> 0 \<le> i \<and> i \<le> n \<and> s = \<Sum>{0..i}\<close>
    {
      i = i + 1;
      s = s + i
    }
  \<close>
  apply vcg_cs
  by (simp_all add: intvs_incdec)
  
program_spec sq_prog
  assumes "n \<ge> 0" ensures "a = n\<^sub>0 * n\<^sub>0"
  defines \<open>
    a = 0;
    z = 1;
    i = 0;
    while (i < n)
      @variant \<open>n\<^sub>0 - i\<close>
      @invariant \<open>n\<^sub>0 = n \<and> 0 \<le> i \<and> i \<le> n \<and> a = i * i \<and> z = 2 * i + 1\<close>
    {
      a = a + z;
      z = z + 2;
      i = i + 1
    }
  \<close>
  by vcg_cs (simp add: algebra_simps)
  
fun factorial :: "int \<Rightarrow> int" where
  "factorial i = (if i \<le> 0 then 1 else i * factorial (i - 1))"
  
program_spec factorial_prog
  assumes "n \<ge> 0" ensures "a = factorial n\<^sub>0"
  defines \<open>
    a = 1;
    i = 1;
    while (i \<le> n)
      @variant \<open>n\<^sub>0 + 1 - i\<close>
      @invariant \<open>n\<^sub>0 = n \<and> 1 \<le> i \<and> i \<le> n + 1 \<and> a = factorial (i - 1)\<close>
    {
      a = a * i;
      i = i + 1
    }
  \<close>
  by vcg (simp add: antisym_conv)+

  
fun fib :: "int \<Rightarrow> int" where
  "fib i = (if i \<le> 0 then 0 else if i = 1 then 1 else fib (i - 2) + fib (i - 1))"

lemma fib_simps[simp]:
  "i \<le> 0 \<Longrightarrow> fib i = 0"
  "i = 1 \<Longrightarrow> fib i = 1"
  "i > 1 \<Longrightarrow> fib i = fib (i - 2) + fib (i - 1)"
  by simp+

lemmas [simp del] = fib.simps

text \<open>With precondition\<close>
program_spec fib_prog
  assumes "n \<ge> 0" ensures "a = fib n"
  defines \<open>
    a = 0; b = 1;
    i = 0;
    while (i < n) 
      @variant \<open>n\<^sub>0 - i\<close>
      @invariant \<open>n = n\<^sub>0 \<and> 0 \<le> i \<and> i \<le> n \<and> a = fib i \<and> b = fib (i + 1)\<close>    
    {
      c = b;
      b = a + b;
      a = c;
      i = i + 1
    }
  \<close>
  by vcg_cs (simp add: algebra_simps)

text \<open>Without precondition, returning \<open>0\<close> for negative numbers\<close>
program_spec fib_prog'
  assumes True ensures "a = fib n\<^sub>0"
  defines \<open>
    a = 0; b = 1;
    i = 0;
    while (i < n) 
      @variant \<open>n\<^sub>0 - i\<close>
      @invariant \<open>n = n\<^sub>0 \<and> (0 \<le> i \<and> i \<le> n \<or> n\<^sub>0 < 0 \<and> i = 0) \<and> a = fib i \<and> b = fib (i+ 1)\<close>    
    {
      c = b;
      b = a + b;
      a = c;
      i = i + 1
    }
  \<close>
  by vcg_cs (auto simp: algebra_simps)



subsubsection \<open>Count down\<close>  
text \<open>Essentially the same as count up, but we (ab)use the input variable as a counter.\<close>
  
text \<open>The invariant is the same as for count-up. 
  Only that we have to compute the actual number
  of loop iterations by \<open>n\<^sub>0 - n\<close>. We locally introduce the name \<open>c\<close> for that.
\<close>  
  

program_spec exp_count_down
  assumes "0\<le>n"
  ensures "a = 2^nat n\<^sub>0"
  defines \<open>
    a = 1;
    while (n>0) 
      @variant \<open>n\<close> 
      @invariant \<open>let c = n\<^sub>0-n in 0\<le>n \<and> n\<le>n\<^sub>0 \<and> a=2^nat c\<close>    
    {
      a=2*a;
      n=n-1
    }
  \<close>
  apply vcg_cs
  by (auto simp: algebra_simps nat_distribs)

  
subsubsection \<open>Approximate from Below\<close>
text \<open>Used to invert a monotonic function. 
  We count up, until we overshoot the desired result, 
  then we subtract one. 
\<close>  
text \<open>The invariant states that the \<open>r-1\<close> is not too big.
  When the loop terminates, \<open>r-1\<close> is not too big, but \<open>r\<close> is already too big,
  so \<open>r-1\<close> is the desired value (rounding down).
\<close>
text \<open>The variant measures the gap that we have to the correct result.
  Note that the loop will do a final iteration, when the result has been reached 
  exactly. We account for that by adding one, such that the measure also decreases in this case.
\<close>

program_spec sqr_approx_below
  assumes "0\<le>n"  
  ensures "0\<le>r \<and> r\<^sup>2 \<le> n\<^sub>0 \<and> n\<^sub>0 < (r+1)\<^sup>2"
  defines \<open>
    r=1;
    while (r*r \<le> n)
      @variant \<open>n + 1 - r*r\<close> 
      @invariant \<open>0\<le>r \<and> (r-1)\<^sup>2 \<le> n\<^sub>0\<close>    
      { r = r + 1 };
    r = r - 1
  \<close>
  apply vcg
  by (auto simp: algebra_simps power2_eq_square)


subsubsection \<open>Bisection\<close>
text \<open>A more efficient way of inverting monotonic functions is by bisection,
  that is, one keeps track of a possible interval for the solution, and halfs the 
  interval in each step. The program will need $O(\log n)$ iterations, and is
  thus very efficient in practice.

  Although the final algorithm looks quite simple, getting it right can be
  quite tricky.
\<close>
text \<open>The invariant is surprisingly easy, just stating that the solution 
  is in the interval \<open>l..<h\<close>. \<close>  

lemma "\<And>h l n\<^sub>0 :: int.
       \<lbrakk>\<paragraph>''invar-final''; 0 \<le> n\<^sub>0; \<not> 1 + l < h; 0 \<le> l; l < h; l * l \<le> n\<^sub>0;
        n\<^sub>0 < h * h\<rbrakk>
       \<Longrightarrow> n\<^sub>0 < 1 + (l * l + l * 2)"  
  by (smt mult.commute semiring_normalization_rules(3))

program_spec sqr_bisect
  assumes "0\<le>n" ensures "r\<^sup>2\<le>n\<^sub>0 \<and> n\<^sub>0<(r+1)\<^sup>2"
  defines \<open>
    l=0; h=n+1;
    while (l+1 < h) 
      @variant \<open>h-l\<close>
      @invariant \<open>0\<le>l \<and> l<h \<and> l\<^sup>2\<le>n \<and> n < h\<^sup>2\<close>    
    {
      m = (l + h) / 2;
      if (m*m \<le> n) l=m else h=m
    };
    r=l
  \<close>
  apply vcg
  text \<open>We use quick-and-dirty apply style proof to discharge the VCs\<close>
        apply (auto simp: power2_eq_square algebra_simps add_pos_pos)
   apply (smt not_sum_squares_lt_zero)
  by (smt mult.commute semiring_normalization_rules(3))

  
  
subsection \<open>Debugging\<close>

subsubsection \<open>Testing Programs\<close>

text \<open>Stepwise\<close>
schematic_goal "Map.empty: (sqr_approx_below,<''n'':=\<lambda>_. 4>) \<Rightarrow> ?s"
  unfolding sqr_approx_below_def
  apply big_step'
   apply big_step'
  apply big_step'
   apply big_step'
    apply big_step'
   apply big_step'
    apply big_step'
   apply big_step'
  apply big_step'
  done

text \<open>Or all steps at once\<close>
schematic_goal "Map.empty: (sqr_bisect,<''n'':=\<lambda>_. 4900000001>) \<Rightarrow> ?s"
  unfolding sqr_bisect_def
  by big_step
  
  
subsection \<open>More Numeric Algorithms\<close>  

subsubsection \<open>Euclid's Algorithm (with subtraction)\<close>

(* Crucial Lemmas *)
thm gcd.commute gcd_diff1

program_spec euclid1
  assumes "a>0 \<and> b>0"
  ensures "a = gcd a\<^sub>0 b\<^sub>0"
  defines \<open>
    while (a\<noteq>b) 
      @invariant \<open>gcd a b = gcd a\<^sub>0 b\<^sub>0 \<and> (a>0 \<and> b>0)\<close>
      @variant \<open>a+b\<close>
    {
      if (a<b) b = b-a
      else a = a-b
    }
  \<close>
  apply vcg_cs
   apply (metis gcd.commute gcd_diff1)
  apply (metis gcd_diff1)
  done


subsubsection \<open>Euclid's Algorithm (with mod)\<close>

(* Crucial Lemmas *)
thm gcd_red_int[symmetric]

program_spec euclid2
  assumes "a>0 \<and> b>0"
  ensures "a = gcd a\<^sub>0 b\<^sub>0"
  defines \<open>
    while (b\<noteq>0) 
      @invariant \<open>gcd a b = gcd a\<^sub>0 b\<^sub>0 \<and> b\<ge>0 \<and> a>0\<close>
      @variant \<open>b\<close>
    {
      t = a;
      a = b;
      b = t mod b
    }
  \<close>
  apply vcg_cs
  by (simp add: gcd_red_int[symmetric])
  
subsubsection \<open>Extended Euclid's Algorithm\<close>
(* Provided by Simon Wimmer. *)

locale extended_euclid_aux_lemmas begin

lemma aux2:
  fixes a b :: int
  assumes "b = t * b\<^sub>0 + s * a\<^sub>0" "q = a div b" "gcd a b = gcd a\<^sub>0 b\<^sub>0"
  shows "gcd b (a - (a\<^sub>0 * (s * q) + b\<^sub>0 * (t * q))) = gcd a\<^sub>0 b\<^sub>0"
proof -
  have "a - (a\<^sub>0 * (s * q) + b\<^sub>0 * (t * q)) = a - b * q"
    unfolding \<open>b = _\<close> by (simp add: algebra_simps)
  also have "a - b * q = a mod b"
    unfolding \<open>q = _\<close> by (simp add: algebra_simps)
  finally show ?thesis
    unfolding \<open>gcd a b = _\<close>[symmetric] by (simp add: gcd_red_int[symmetric])
qed

lemma aux3:
  fixes a b :: int
  assumes "b = t * b\<^sub>0 + s * a\<^sub>0" "q = a div b" "b > 0"
  shows "t * (b\<^sub>0 * q) + s * (a\<^sub>0 * q) \<le> a"
proof -
  have "t * (b\<^sub>0 * q) + s * (a\<^sub>0 * q) = q * b"
    unfolding \<open>b = _\<close> by (simp add: algebra_simps)
  then show ?thesis
    using \<open>b > 0\<close>
    by (simp add: algebra_simps \<open>q = _\<close>)
       (smt Euclidean_Division.pos_mod_sign cancel_div_mod_rules(1) mult.commute)
qed

end


text \<open>The following is a direct translation of the pseudocode for the Extended Euclidean algorithm
as described by the English version of Wikipedia
(\<^url>\<open>https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm\<close>):
\<close>
program_spec euclid_extended
  assumes "a>0 \<and> b>0"
  ensures "old_r = gcd a\<^sub>0 b\<^sub>0 \<and> gcd a\<^sub>0 b\<^sub>0 = a\<^sub>0 * old_s + b\<^sub>0 * old_t"
defines \<open>
    s = 0;    old_s = 1;
    t = 1;    old_t = 0;
    r = b;    old_r = a;
    while (r\<noteq>0) 
      @invariant \<open>
        gcd old_r r = gcd a\<^sub>0 b\<^sub>0 \<and> r\<ge>0 \<and> old_r>0
      \<and> a\<^sub>0 * old_s + b\<^sub>0 * old_t = old_r \<and> a\<^sub>0 * s + b\<^sub>0 * t = r
      \<close>
      @variant \<open>r\<close>
    {
      quotient = old_r / r;
      temp = old_r;
      old_r = r;
      r = temp - quotient * r;
      temp = old_s;
      old_s = s;
      s = temp - quotient * s;
      temp = old_t;
      old_t = t;
      t = temp - quotient * t
    }
  \<close>
proof -
  interpret extended_euclid_aux_lemmas .
  show ?thesis
    apply vcg_cs
     apply (simp add: algebra_simps)
     apply (simp add: aux2 aux3 minus_div_mult_eq_mod)+
    done  
    
qed


text \<open>Non-Wikipedia version\<close>
context extended_euclid_aux_lemmas begin
  lemma aux:
    fixes a b q x y:: int
    assumes "a = old_y * b\<^sub>0 + old_x * a\<^sub>0" "b = y * b\<^sub>0 + x * a\<^sub>0" "q = a div b"
    shows
    "a mod b + (a\<^sub>0 * (x * q) + b\<^sub>0 * (y * q)) = a"
  proof -
    have *: "a\<^sub>0 * (x * q) + b\<^sub>0 * (y * q) = q * b"
      unfolding \<open>b = _\<close> by (simp add: algebra_simps)
    show ?thesis
      unfolding * unfolding \<open>q = _\<close> by simp
  qed
end

program_spec euclid_extended'
  assumes "a>0 \<and> b>0"
  ensures "a = gcd a\<^sub>0 b\<^sub>0 \<and> gcd a\<^sub>0 b\<^sub>0 = a\<^sub>0 * x + b\<^sub>0 * y"
defines \<open>
    x = 0;
    y = 1;
    old_x = 1;
    old_y = 0;
    while (b\<noteq>0) 
      @invariant \<open>
        gcd a b = gcd a\<^sub>0 b\<^sub>0 \<and> b\<ge>0 \<and> a>0 \<and> a = a\<^sub>0 * old_x + b\<^sub>0 * old_y \<and> b = a\<^sub>0 * x + b\<^sub>0 * y
      \<close>
      @variant \<open>b\<close>
    {
      q = a / b;
      t = a;
      a = b;
      b = t mod b;
      t = x;
      x = old_x - q * x;
      old_x = t;
      t = y;
      y = old_y - q * y;
      old_y = t
    };
    x = old_x;
    y = old_y
  \<close>
proof -
  interpret extended_euclid_aux_lemmas .
  show ?thesis
    apply vcg_cs
    apply (simp add: gcd_red_int[symmetric])
    apply (simp add: algebra_simps)
    apply (rule aux; simp add: algebra_simps)
    done
qed
  
subsubsection \<open>Exponentiation by Squaring\<close>
(* Contributed by Simon Wimmer *)

lemma ex_by_sq_aux:
  fixes x :: int and n :: nat
  assumes "n mod 2 = 1"
  shows "x * (x * x) ^ (n div 2) = x ^ n"
proof -
  have "n > 0"
    using assms by presburger
  have "2 * (n div 2) = n - 1"
    using assms by presburger
  then have "(x * x) ^ (n div 2) = x ^ (n - 1)"
    by (simp add: semiring_normalization_rules)
  with \<open>0 < n\<close> show ?thesis
    by simp (metis Suc_pred power.simps(2))
qed

text \<open>A classic algorithm for computing \<open>x\<^sup>n\<close> works by repeated squaring,
using the following recurrence:
  \<^item> \<open>x\<^sup>n = x * x\<^bsup>(n-1)/2\<^esup>\<close> if \<open>n\<close> is odd
  \<^item> \<open>x\<^sup>n = x\<^bsup>n/2\<^esup>\<close> if \<open>n\<close> is even

\<close>
program_spec ex_by_sq
  assumes "n\<ge>0"
  ensures "r = x\<^sub>0 ^ nat n\<^sub>0"
defines \<open>
    r = 1;
    while (n\<noteq>0) 
      @invariant \<open>
        n \<ge> 0 \<and> r * x ^ nat n = x\<^sub>0 ^ nat n\<^sub>0
      \<close>
      @variant \<open>n\<close>
    {
      if (n mod 2 == 1) {
        r = r * x
      };
      x = x * x;
      n = n / 2
    }
  \<close>
  apply vcg_cs
  subgoal
    apply (subst (asm) ex_by_sq_aux[symmetric])
     apply (smt Suc_1 nat_1 nat_2 nat_mod_distrib nat_one_as_int)
    by (simp add: div_int_pos_iff int_div_less_self nat_div_distrib)
   apply (simp add: algebra_simps semiring_normalization_rules nat_mult_distrib; fail)
  apply (simp add: algebra_simps semiring_normalization_rules nat_mult_distrib; fail)
  done



subsubsection \<open>Power-Tower of 2s\<close>

fun tower2 where
  "tower2 0 = 1"
| "tower2 (Suc n) = 2 ^ tower2 n"  

definition "tower2' n = int (tower2 (nat n))"

program_spec tower2_imp
  assumes \<open>m>0\<close>
  ensures \<open>a = tower2' m\<^sub>0\<close>
  defines \<open>
    a=1;
    while (m>0) 
      @variant \<open>m\<close>
      @invariant \<open>0\<le>m \<and> m\<le>m\<^sub>0 \<and> a = tower2' (m\<^sub>0-m)\<close>
    {
      n=a;
      
      a = 1;
      while (n>0) 
        @variant \<open>n\<close> 
        @invariant \<open>True\<close> \<comment> \<open>This will get ugly, there is no \<open>n\<^sub>0\<close> that we could use!\<close>   
      {
        a=2*a;
        n=n-1
      };
      
      m=m-1
    }
  \<close>
  oops

text \<open>We prove the inner loop separately instead! 
  (It happens to be exactly our \<^const>\<open>exp_count_down\<close> program.)
\<close>  
  
program_spec tower2_imp
  assumes \<open>m>0\<close>
  ensures \<open>a = tower2' m\<^sub>0\<close>
  defines \<open>
    a=1;
    while (m>0) 
      @variant \<open>m\<close>
      @invariant \<open>0\<le>m \<and> m\<le>m\<^sub>0 \<and> a = tower2' (m\<^sub>0-m)\<close>
    {
      n=a;
      inline exp_count_down;
      m=m-1
    }
  \<close>
  apply vcg_cs
  by (auto simp: algebra_simps tower2'_def nat_distribs)



subsection \<open>Array Algorithms\<close>  
  
(*
  Presentation in lecture:

  introduce array syntax and semantics
    CONVENTIONS: 
      * Every variable is an array. 
      * Arrays are modeled as int\<Rightarrow>int. Negative indexes allowed.
      * Syntactic sugar to use it at index 0 by default
      
    V vname \<mapsto> Vidx vname aexp  Syntax: x[i]
    abbreviation "V x = Vidx x 0"
  
    Assign vname aexp \<mapsto> AssignIdx vname aexp aexp  Syntax: x[i] = a
    abbreviation: Assign x a = AssignIdx x 0 a
  
    NEW COMMAND: ArrayCpy vname vname Syntax: x[] = y
      copy two arrays as a whole. Assign x (V y) only copies index 0
  
  semantics: Obvious
    aval (Vidx x i) s = s x (aval i s)
    
    (x[i] = a, s) \<Rightarrow> s(x := (s x)(aval i s := aval a s))
    
    (x[] = y, s) \<Rightarrow> s(x := s y)
    
  weakest preconditions: Also obvious
    \<dots>
    
Reasoning with arrays:    
    
  Usually: Model as int\<Rightarrow>int is appropriate.
  
  Common idioms: 
    * {l..<h} the set of indexes i, l\<le>i<h
    * a`{l..<h} the set of values in range {l..<h}
  
    * ran_sorted a l h = \<dots>
    
    Warning: Sledgehammer does not perform well on these!

Data Refinement    
  Sometimes, abstraction to list may be useful.
  
  Idea: Model an algorithm on lists first. Prove it correct.
    Then implement algorithm. Show that it implements the model.
    By transitivity, get: Algorithm is correct!

  
    
  Sometimes, abstraction to list may be useful    
    
*)


  
  
subsubsection \<open>Summation\<close>

program_spec array_sum
  assumes "l\<le>h"
  ensures "r = (\<Sum>i=l\<^sub>0..<h\<^sub>0. a\<^sub>0 i)"
  defines \<open>
    r = 0;
    while (l<h) 
      @invariant \<open>l\<^sub>0\<le>l \<and> l\<le>h \<and> r = (\<Sum>i=l\<^sub>0..<l. a\<^sub>0 i)\<close>
      @variant \<open>h-l\<close>
    {
      r = r + a[l];
      l=l+1
    }
  \<close>
  apply vcg_cs
  by (auto simp: intvs_incdec)
  
(* Exercise: Remove l\<le>h precondition! *)  

subsubsection \<open>Finding Least Index of Element\<close>  
  
program_spec find_least_idx
  assumes \<open>l\<le>h\<close>
  ensures \<open>if l=h\<^sub>0 then x\<^sub>0 \<notin> a\<^sub>0`{l\<^sub>0..<h\<^sub>0} else l\<in>{l\<^sub>0..<h\<^sub>0} \<and> a\<^sub>0 l = x\<^sub>0 \<and> x\<^sub>0\<notin>a\<^sub>0`{l\<^sub>0..<l} \<close>
  defines \<open>
    while (l<h \<and> a[l] \<noteq> x) 
      @variant \<open>h-l\<close>
      @invariant \<open>l\<^sub>0\<le>l \<and> l\<le>h \<and> x\<notin>a`{l\<^sub>0..<l}\<close>
      l=l+1
  \<close>
  apply vcg_cs
  by (smt atLeastLessThan_iff imageI)
  


  

subsubsection \<open>Check for Sortedness\<close>  
  
term ran_sorted

program_spec check_sorted
  assumes \<open>l\<le>h\<close>
  ensures \<open>r\<noteq>0 \<longleftrightarrow> ran_sorted a\<^sub>0 l\<^sub>0 h\<^sub>0\<close>
  defines \<open>
    if (l==h) r=1
    else {
      l=l+1;
      while (l<h \<and> a[l-1] \<le> a[l]) 
        @variant \<open>h-l\<close>
        @invariant \<open>l\<^sub>0<l \<and> l\<le>h \<and> ran_sorted a l\<^sub>0 l\<close>
        l=l+1;
        
      if (l==h) r=1 else r=0
    }
  \<close>
  apply vcg_cs
   apply (auto simp: ran_sorted_def) 
  by (smt atLeastLessThan_iff) 

  
subsubsection \<open>Find Equilibrium Index\<close>  
  
definition "is_equil a l h i \<equiv> l\<le>i \<and> i<h \<and> (\<Sum>j=l..<i. a j) = (\<Sum>j=i..<h. a j)"

program_spec equilibrium
  assumes \<open>l\<le>h\<close>
  ensures \<open>is_equil a l h i \<or> i=h \<and> (\<nexists>i. is_equil a l h i)\<close>
  defines \<open>
    usum=0; i=l;
    while (i<h) 
      @variant \<open>h-i\<close>
      @invariant \<open>l\<le>i \<and> i\<le>h \<and> usum = (\<Sum>j=l..<i. a j)\<close>
    { 
      usum = usum + a[i]; i=i+1 
    };
    i=l; lsum=0;
    while (usum \<noteq> lsum \<and> i<h) 
      @variant \<open>h-i\<close>
      @invariant \<open>l\<le>i \<and> i\<le>h 
        \<and> lsum=(\<Sum>j=l..<i. a j) 
        \<and> usum=(\<Sum>j=i..<h. a j) 
        \<and> (\<forall>j<i. \<not>is_equil a l h j)
      \<close>
    {
      lsum = lsum + a[i];
      usum = usum - a[i];
      i=i+1
    }
  \<close>
  apply vcg_cs
     apply (auto simp: intvs_incdec is_equil_def)
    apply (metis atLeastLessThan_iff eq_iff finite_atLeastLessThan_int sum_diff1)
   apply force
  by force

  
subsubsection \<open>Rotate Right\<close>
program_spec rotate_right
  assumes "0<n"
  ensures "\<forall>i\<in>{0..<n}. a i = a\<^sub>0 ((i-1) mod n)"
  defines \<open>
    i = 0;
    prev = a[n - 1];
    while (i < n)
      @invariant \<open>
        0 \<le> i \<and> i \<le> n 
        \<and> (\<forall>j\<in>{0..<i}. a j = a\<^sub>0 ((j-1) mod n))
        \<and> (\<forall>j\<in>{i..<n}. a j = a\<^sub>0 j)
        \<and> prev = a\<^sub>0 ((i-1) mod n)
      \<close>
      @variant \<open>n - i\<close>
    {
      temp = a[i];
      a[i] = prev;
      prev = temp;
      i = i + 1
    }
    \<close>
  apply vcg_cs
  by (simp add: zmod_minus1)

  
subsubsection \<open>Binary Search, Leftmost Element\<close>  
  
text \<open>We first specify the pre- and postcondition\<close>
definition "bin_search_pre a l h \<longleftrightarrow> l\<le>h \<and> ran_sorted a l h"

definition "bin_search_post a l h x i \<longleftrightarrow> 
  l\<le>i \<and> i\<le>h \<and> (\<forall>i\<in>{l..<i}. a i < x) \<and> (\<forall>i\<in>{i..<h}. x \<le> a i)"    
  
text \<open>Then we prove that the program is correct\<close>  
program_spec binsearch 
  assumes \<open>bin_search_pre a l h\<close>
  ensures \<open>bin_search_post a\<^sub>0 l\<^sub>0 h\<^sub>0 x\<^sub>0 l\<close>
  defines \<open>
    while (l < h) 
      @variant \<open>h-l\<close>
      @invariant \<open>l\<^sub>0\<le>l \<and> l\<le>h \<and> h\<le>h\<^sub>0 \<and> (\<forall>i\<in>{l\<^sub>0..<l}. a i < x) \<and> (\<forall>i\<in>{h..<h\<^sub>0}. x \<le> a i)\<close>
    {
        m = (l + h) / 2;
        if (a[m] < x) l = m + 1 
        else h = m
    }
  \<close>
  apply vcg_cs
       apply (auto simp: algebra_simps bin_search_pre_def bin_search_post_def)
  txt \<open>Driving sledgehammer to its limits ...\<close>
   apply (smt div_add_self1 even_succ_div_two odd_two_times_div_two_succ ran_sorted_alt)
  by (smt div_add_self1 even_succ_div_two odd_two_times_div_two_succ ran_sorted_alt)

text \<open>Next, we show that our postcondition (which was easy to prove)
  implies the expected properties of the algorithm.
\<close>
lemma
  assumes "bin_search_pre a l h" "bin_search_post a l h x i"
  shows bin_search_decide_membership: "x\<in>a`{l..<h} \<longleftrightarrow> (i<h \<and> x = a i)"
    and bin_search_leftmost: "x\<notin>a`{l..<i}"
  using assms apply -
   apply (auto simp: bin_search_post_def bin_search_pre_def)
  apply (smt atLeastLessThan_iff ran_sorted_alt)
  done  
  
subsubsection \<open>Naive String Search\<close>  
(* By Simon Wimmer *)

program_spec match_string
  assumes "l1 \<le> h1"
  ensures "(\<forall>j \<in> {0..<i}. a (l + j) = b (l1 + j)) \<and> (i < h1 - l1 \<longrightarrow> a (l + i) \<noteq> b (l1 + i))
    \<and> 0 \<le> i \<and> i \<le> h1 - l1"
  defines \<open>
  i = 0;
  while (l1 + i < h1 \<and> a[l + i] == b[l1 + i])
    @invariant \<open>(\<forall>j \<in> {0..<i}. a (l + j) = b (l1 + j)) \<and> 0 \<le> i \<and> i \<le> h1 - l1\<close>
    @variant \<open>(h1 - (l1 + i))\<close>
  {
    i = i + 1
  }
\<close>
  by vcg_cs auto

lemma lran_eq_iff': "lran a l1 (l1 + (h - l)) = lran a' l h
  \<longleftrightarrow> (\<forall>i. 0 \<le> i \<and> i < h - l \<longrightarrow> a (l1 + i) = a' (l + i))" if "l \<le> h"
  using that
proof (induction "nat (h - l)" arbitrary: h)
  case 0
  then show ?case
    by auto
next
  case (Suc x)
  then have *: "x = nat (h - 1 - l)" "l \<le> h - 1"
    by auto
  note IH = Suc.hyps(1)[OF *]
  from * have 1:
    "lran a l1 (l1 + (h - l)) = lran a l1 (l1 + (h - 1 - l)) @ [a (l1 + (h - 1 - l))]"
    "lran a' l h = lran a' l (h - 1) @ [a' (h - 1)]"
    by (auto simp: lran_bwd_simp algebra_simps lran_butlast[symmetric])
  from IH * Suc.hyps(2) Suc.prems show ?case
    unfolding 1
    apply auto
    subgoal for i
      by (cases "i = h - 1 - l") auto
    done
qed

program_spec match_string'
  assumes "l1 \<le> h1"
ensures "i = h1 - l1 \<longleftrightarrow> lran a l (l + (h1 - l1)) = lran b l1 h1"
for i h1 l1 l a[] b[]
defines \<open>inline match_string\<close>
  by vcg_cs (auto simp: lran_eq_iff')

program_spec substring
  assumes "l \<le> h \<and> l1 \<le> h1"
  ensures "match = 1 \<longleftrightarrow> (\<exists> j \<in> {l\<^sub>0..<h\<^sub>0}. lran a j (j + (h1 - l1)) = lran b l1 h1)"
  for a[] b[]
  defines \<open>
  match = 0;
  while (l < h \<and> match == 0)
    @invariant\<open>l\<^sub>0 \<le> l \<and> l \<le> h \<and> match \<in> {0,1} \<and>
    (if match = 1
     then lran a l (l + (h1 - l1)) = lran b l1 h1 \<and> l < h
     else (\<forall>j \<in> {l\<^sub>0..<l}. lran a j (j + (h1 - l1)) \<noteq> lran b l1 h1))\<close>
    @variant\<open>(h - l) * (1 - match)\<close>
  {
    inline match_string';
    if (i == h1 - l1) {match = 1}
    else {l = l + 1}
  }
\<close>
  by vcg_cs auto

program_spec substring'
  assumes "l \<le> h \<and> l1 \<le> h1"
  ensures "match = 1 \<longleftrightarrow> (\<exists> j \<in> {l\<^sub>0..h\<^sub>0-(h1 - l1)}. lran a j (j + (h1 - l1)) = lran b l1 h1)"
  for a[] b[]
  defines \<open>
  match = 0;
  if (l + (h1 - l1) \<le> h) {
    h = h - (h1 - l1) + 1;
    inline substring
  }
\<close>
  by vcg_cs auto

(* Or combined: *)
program_spec substring''
  assumes "l \<le> h \<and> l1 \<le> h1"
  ensures "match = 1 \<longleftrightarrow> (\<exists> j \<in> {l\<^sub>0..<h\<^sub>0-(h1 - l1)}. lran a j (j + (h1 - l1)) = lran b l1 h1)"
  for a[] b[]
  defines \<open>
  match = 0;
  if (l + (h1 - l1) \<le> h) {
    while (l + (h1 - l1) < h \<and> match == 0)
      @invariant\<open>l\<^sub>0 \<le> l \<and> l \<le> h - (h1 - l1) \<and> match \<in> {0,1} \<and>
      (if match = 1
       then lran a l (l + (h1 - l1)) = lran b l1 h1 \<and> l < h - (h1 - l1)
       else (\<forall>j \<in> {l\<^sub>0..<l}. lran a j (j + (h1 - l1)) \<noteq> lran b l1 h1))\<close>
      @variant\<open>(h - l) * (1 - match)\<close>
    {
      inline match_string';
      if (i == h1 - l1) {match = 1}
      else {l = l + 1}
    }
  }
\<close>
  by vcg_cs auto

lemma lran_split:
  "lran a l h = lran a l p @ lran a p h" if "l \<le> p" "p \<le> h"
  using that by (induction p; simp; simp add: lran.simps)

lemma lran_eq_append_iff:
  "lran a l h = as @ bs \<longleftrightarrow> (\<exists> i. l \<le> i \<and> i \<le> h \<and> as = lran a l i \<and> bs = lran a i h)" if "l \<le> h"
  apply safe
  subgoal
    using that
  proof (induction as arbitrary: l)
    case Nil
    then show ?case
      by auto
  next
    case (Cons x as)
    from this(2-) have "lran a (l + 1) h = as @ bs" "a l = x" "l + 1 \<le> h"
        apply -
      subgoal
        by simp
      subgoal
        by (smt append_Cons list.inject lran.simps lran_append1)
      subgoal
        using add1_zle_eq by fastforce
      done
    from Cons.IH[OF this(1,3)] guess i by safe
    note IH = this
    with \<open>a l = x\<close> show ?case
      apply (intro exI[where x = i])
      apply auto
      by (smt IH(3) lran_prepend1)
  qed
  apply (subst lran_split; simp)
  done

lemma lran_split':
  "(\<exists>j\<in>{l..h - (h1 - l1)}. lran a j (j + (h1 - l1)) = lran b l1 h1)
 = (\<exists>as bs. lran a l h = as @ lran b l1 h1 @ bs)" if "l \<le> h" "l1 \<le> h1"
proof safe
  fix j
  assume j: "j \<in> {l..h - (h1 - l1)}" and match: "lran a j (j + (h1 - l1)) = lran b l1 h1"
  with \<open>l1 \<le> h1\<close> have "lran a l h = lran a l j @ lran a j (j + (h1 - l1)) @ lran a (j + (h1 - l1)) h"
    apply (subst lran_split[where p = j], simp, simp)
    apply (subst (2) lran_split[where p = "j + (h1 - l1)"]; simp)
    done
  then show "\<exists>as bs. lran a l h = as @ lran b l1 h1 @ bs"
    by (auto simp: match)
next
  fix as bs
  assume "lran a l h = as @ lran b l1 h1 @ bs"
  with that lran_eq_append_iff[of l h a as "lran b l1 h1 @ bs"] obtain i where
    "as = lran a l i" "lran a i h = lran b l1 h1 @ bs" "l \<le> i" "i \<le> h"
    by auto
  with lran_eq_append_iff[of i h a "lran b l1 h1" bs] obtain j where j:
    "lran b l1 h1 = lran a i j" "bs = lran a j h" "i \<le> j" "j \<le> h"
    by auto
  moreover have "j = i + (h1 - l1)"
  proof -
    have "length (lran b l1 h1) = nat (h1 - l1)" "length (lran a i j) = nat (j - i)"
      by auto
    with j(1,3) that show ?thesis
      by auto
  qed
  ultimately show "\<exists>j\<in>{l..h - (h1 - l1)}. lran a j (j + (h1 - l1)) = lran b l1 h1"
    using \<open>l \<le> i\<close> by auto
qed

program_spec substring_final
  assumes "l \<le> h \<and> 0 \<le> len"
  ensures "match = 1 \<longleftrightarrow> (\<exists>as bs. lran a l\<^sub>0 h\<^sub>0 = as @ lran b 0 len @ bs)"
  for l h len match a[] b[]
  defines \<open>l1 = 0; h1 = len; inline substring'\<close>
  supply [simp] = lran_split'[symmetric]
  apply vcg_cs
  done


  
  
subsubsection \<open>Insertion Sort\<close>
    
text \<open>
  We first prove the inner loop. 
  The specification here specifies what the algorithm does as closely as possible,
  such that it becomes easier to prove. In this case, sortedness is not a precondition
  for the inner loop to move the key element backwards over all greater elements.
\<close>
definition "insort_insert_post l j a\<^sub>0 a i
  \<longleftrightarrow> (let key = a\<^sub>0 j in
      i\<in>{l-1..<j}            \<comment> \<open>\<open>i\<close> is in range\<close>
    \<comment> \<open>Content of new array\<close>
    \<and> (\<forall>k\<in>{l..i}. a k = a\<^sub>0 k) 
    \<and> a (i+1) = key
    \<and> (\<forall>k\<in>{i+2..j}. a k = a\<^sub>0 (k-1))
    \<and> a = a\<^sub>0 on -{l..j}
    \<comment> \<open>Placement of \<open>key\<close>\<close>  
    \<and> (i\<ge>l \<longrightarrow> a i \<le> key)  \<comment> \<open>Element at \<open>i\<close> smaller than \<open>key\<close>, if it exists \<close>
    \<and> (\<forall>k\<in>{i+2..j}. a k > key) \<comment> \<open>Elements \<open>\<ge>i+2\<close> greater than \<open>key\<close>\<close>
    )
    "
  for l j i :: int and a\<^sub>0 a :: "int \<Rightarrow> int"
  
program_spec insort_insert 
  assumes "l<j"
  ensures "insort_insert_post l j a\<^sub>0 a i"
  defines \<open>
    key = a[j];
    i = j-1;
    while (i\<ge>l \<and> a[i]>key) 
      @variant \<open>i-l+1\<close>
      @invariant \<open>l-1\<le>i \<and> i<j 
        \<and> (\<forall>k\<in>{l..i}. a k = a\<^sub>0 k) 
        \<and> (\<forall>k\<in>{i+2..j}. a k > key \<and> a k = a\<^sub>0 (k-1))
        \<and> a = a\<^sub>0 on -{l..j}
        \<close>
    {
      a[i+1] = a[i];
      i=i-1
    };
    a[i+1] = key
  \<close>
  unfolding insort_insert_post_def Let_def
  apply vcg
      apply auto
  by (smt atLeastAtMost_iff)
  
text \<open>Next, we show that our specification that was easy to prove implies the 
  specification that the outer loop expects:\<close>

text \<open>Invoking \<open>insort_insert\<close> will sort in the element\<close>
lemma insort_insert_sorted:
  assumes "l<j"
  assumes "insort_insert_post l j a a' i'"
  assumes "ran_sorted a l j"
  shows "ran_sorted a' l (j + 1)"
  using assms unfolding insort_insert_post_def Let_def
  apply auto
  subgoal
    by (smt atLeastAtMost_iff ran_sorted_alt)
  subgoal 
    unfolding ran_sorted_alt Ball_def
    apply auto
    by smt
  done  
  
text \<open>Invoking \<open>insort_insert\<close> will only mutate the elements\<close>
lemma insort_insert_ran1:
  assumes "l<j"
  assumes "insort_insert_post l j a a' i"
  shows "mset_ran a' {l..j} = mset_ran a {l..j}"
proof -
  from assms have EQS:
    "a' = a on {l..i}"
    "a' (i+1) = a j"
    "a' = (a o (+)(-1)) on {i+2..j}"
    unfolding insort_insert_post_def eq_on_def Let_def by auto

  from assms have "l\<le>i+1" "i+1\<le>j" unfolding insort_insert_post_def Let_def by auto
    
  have ranshift: "mset_ran (a o (+)(-1)) {i+2..j} = mset_ran a {i+1..j-1}"  
    by (simp add: mset_ran_shift algebra_simps)
    
      
  have "mset_ran a' {l..j} = mset_ran a' {l..i} + {# a' (i+1) #} + mset_ran a' {i+2..j}"  
    using \<open>l<j\<close> \<open>l\<le>i+1\<close> \<open>i+1\<le>j\<close>
    apply (simp add: mset_ran_combine)
    by (auto intro: arg_cong[where f="mset_ran a'"])
  also have "\<dots> = mset_ran a {l..i} + {# a j #} + mset_ran (a o (+)(-1)) {i+2..j}"
    using EQS(1,3)[THEN mset_ran_cong] EQS(2) by simp
  also have "\<dots> = mset_ran a {l..i} + mset_ran a {i+1..j-1} + {# a j #}"
    by (simp add: mset_ran_shift algebra_simps) 
  also have "\<dots> = mset_ran a {l..j}"
    using \<open>l<j\<close> \<open>l\<le>i+1\<close> \<open>i+1\<le>j\<close>
    apply (simp add: mset_ran_combine)
    by (auto intro: arg_cong[where f="mset_ran a"])
  finally show ?thesis .
qed  

text \<open>The property @{thm insort_insert_ran1} extends to the whole array to be sorted\<close>
lemma insort_insert_ran2:
  assumes "l<j" "j<h"
  assumes "insort_insert_post l j a a' i"
  shows "mset_ran a' {l..<h} = mset_ran a {l..<h}" (is ?thesis1)
    and "a'=a on -{l..<h}" (is ?thesis2)
proof -
  from insort_insert_ran1 assms have "mset_ran a' {l..j} = mset_ran a {l..j}" by blast
  also from \<open>insort_insert_post l j a a' i\<close> have "a' = a on {j<..<h}"
    unfolding insort_insert_post_def Let_def by (auto simp: eq_on_def)
  hence "mset_ran a' {j<..<h} = mset_ran a {j<..<h}" by (rule mset_ran_cong)
  finally (mset_ran_combine_eqs) show ?thesis1
    by (simp add: assms ivl_disj_int_two(4) ivl_disj_un_two(4) le_less)
    
  from assms show ?thesis2   
    unfolding insort_insert_post_def Let_def eq_on_def 
    by auto
    
qed  

text \<open>Finally, we specify and prove correct the outer loop\<close>
program_spec insort
  assumes "l<h" 
  ensures "ran_sorted a l h \<and> mset_ran a {l..<h} = mset_ran a\<^sub>0 {l..<h} \<and> a=a\<^sub>0 on -{l..<h}"
  for a[]
  defines \<open>
    j = l + 1;
    while (j<h) 
      @variant \<open>h-j\<close>
      @invariant \<open>
          l<j \<and> j\<le>h           \<comment> \<open>\<open>j\<close> in range\<close>
        \<and> ran_sorted a l j     \<comment> \<open>Array is sorted up to \<open>j\<close>\<close>
        \<and> mset_ran a {l..<h} = mset_ran a\<^sub>0 {l..<h} \<comment> \<open>Elements in range only permuted\<close>
        \<and> a=a\<^sub>0 on -{l..<h}
      \<close>
    {
      inline insort_insert;
      j=j+1
    }
  \<close>
  apply vcg_cs
  apply (intro conjI)
  subgoal by (rule insort_insert_sorted)
  subgoal using insort_insert_ran2(1) by auto
  subgoal apply (frule (2) insort_insert_ran2(2)) by (auto simp: eq_on_def)
  done    
  

  
subsubsection \<open>Quicksort\<close>

procedure_spec partition_aux(a,l,h,p) returns (a,i)
  assumes "l\<le>h"
  ensures "mset_ran a\<^sub>0 {l\<^sub>0..<h\<^sub>0} = mset_ran a {l\<^sub>0..<h\<^sub>0}
         \<and> (\<forall>j\<in>{l\<^sub>0..<i}. a j < p\<^sub>0)
         \<and> (\<forall>j\<in>{i..<h\<^sub>0}. a j \<ge> p\<^sub>0)
         \<and> l\<^sub>0\<le>i \<and> i\<le>h\<^sub>0
         \<and> a\<^sub>0 = a on -{l\<^sub>0..<h\<^sub>0}
         "
  defines \<open>
  i=l; j=l;
  while (j<h) 
    @invariant \<open> 
        l\<le>i \<and> i\<le>j \<and> j\<le>h     
      \<and> mset_ran a\<^sub>0 {l\<^sub>0..<h\<^sub>0} = mset_ran a {l\<^sub>0..<h\<^sub>0}
      \<and> (\<forall>k\<in>{l..<i}. a k < p)  
      \<and> (\<forall>k\<in>{i..<j}. a k \<ge> p)  
      \<and> (\<forall>k\<in>{j..<h}. a\<^sub>0 k = a k)  
      \<and> a\<^sub>0 = a on -{l\<^sub>0..<h\<^sub>0}
    \<close>
    @variant \<open>(h-j)\<close>
  {
    if (a[j]<p) {temp = a[i]; a[i] = a[j]; a[j] = temp; i=i+1};
    j=j+1
  }
  \<close>
  supply lran_eq_iff[simp] lran_tail[simp del]
  apply vcg_cs
  subgoal by (simp add: mset_ran_swap[unfolded swap_def])
  subgoal by auto
  done
  

procedure_spec partition(a,l,h,p) returns (a,i)
  assumes "l<h"
  ensures "mset_ran a\<^sub>0 {l\<^sub>0..<h\<^sub>0} = mset_ran a {l\<^sub>0..<h\<^sub>0}
         \<and> (\<forall>j\<in>{l\<^sub>0..<i}. a j < a i) 
         \<and> (\<forall>j\<in>{i..<h\<^sub>0}. a j \<ge> a i)
         \<and> l\<^sub>0\<le>i \<and> i<h\<^sub>0 \<and> a\<^sub>0 (h\<^sub>0-1) = a i
         \<and> a\<^sub>0 = a on -{l\<^sub>0..<h\<^sub>0}
         "
  defines \<open>
    p = a[h-1];
    (a,i) = partition_aux(a,l,h-1,p);
    a[h-1] = a[i];
    a[i] = p
  \<close>
  apply vcg_cs
  apply (auto simp: eq_on_def mset_ran_swap[unfolded swap_def] intvs_incdec intro: mset_ran_combine_eq_diff)
  done
    
  
  
lemma quicksort_sorted_aux:  
  assumes BOUNDS: "l \<le> i" "i < h"
  
  assumes LESS: "\<forall>j\<in>{l..<i}. a\<^sub>1 j < a\<^sub>1 i" 
  assumes GEQ: "\<forall>j\<in>{i..<h}. a\<^sub>1 i \<le> a\<^sub>1 j"
  
  assumes R1: "mset_ran a\<^sub>1 {l..<i} = mset_ran a\<^sub>2 {l..<i}"
  assumes E1: "a\<^sub>1 = a\<^sub>2 on - {l..<i}"
  
  assumes SL: "ran_sorted a\<^sub>2 l i"
  
  assumes R2: "mset_ran a\<^sub>2 {i + 1..<h} = mset_ran a\<^sub>3 {i + 1..<h}"
  assumes E2: "a\<^sub>2 = a\<^sub>3 on - {i + 1..<h}"

  assumes SH: "ran_sorted a\<^sub>3 (i + 1) h"
  
  shows "ran_sorted a\<^sub>3 l h"
proof -
  have [simp]: "{l..<i} \<subseteq> - {i + 1..<h}" by auto
  have [simp]: "a\<^sub>1 i = a\<^sub>3 i" using E1 E2 by (auto simp: eq_on_def)
  
  note X1 = mset_ran_xfer_pointwise[where P = \<open>\<lambda>x. x < p\<close> for p, OF R1, simplified]
  note X2 = eq_on_xfer_pointwise[where P = \<open>\<lambda>x. x < p\<close> for p, OF E2, of "{l..<i}", simplified]
  from LESS have LESS': "\<forall>j\<in>{l..<i}. a\<^sub>3 j < a\<^sub>3 i"
    by (simp add: X1 X2)
    
  
  from GEQ have GEQ1: "\<forall>j\<in>{i+1..<h}. a\<^sub>1 i \<le> a\<^sub>1 j" by auto
  have [simp]: "{i + 1..<h} \<subseteq> - {l..<i}" by auto
  note X3 = eq_on_xfer_pointwise[where P = \<open>\<lambda>x. x \<ge> p\<close> for p, OF E1, of "{i+1..<h}", simplified]
  note X4 = mset_ran_xfer_pointwise[where P = \<open>\<lambda>x. x \<ge> p\<close> for p, OF R2, simplified]  
  from GEQ1 have GEQ': "\<forall>j\<in>{i+1..<h}. a\<^sub>3 i \<le> a\<^sub>3 j" by (simp add: X3 X4)

  
  from SL eq_on_xfer_ran_sorted[OF E2, of l i] have SL': "ran_sorted a\<^sub>3 l i" by simp
  
  show ?thesis using combine_sorted_pivot[OF BOUNDS SL' SH LESS' GEQ'] .
qed  
  
lemma quicksort_mset_aux:
  assumes B: "l\<^sub>0\<le>i" "i<h\<^sub>0"
  assumes R1: "mset_ran a {l\<^sub>0..<i} = mset_ran aa {l\<^sub>0..<i}"
  assumes E1: "a = aa on - {l\<^sub>0..<i}"
  assumes R2: "mset_ran aa {i + 1..<h\<^sub>0} = mset_ran ab {i + 1..<h\<^sub>0}"
  assumes E2: "aa = ab on - {i + 1..<h\<^sub>0}"
  shows "mset_ran a {l\<^sub>0..<h\<^sub>0} = mset_ran ab {l\<^sub>0..<h\<^sub>0}"
  apply (rule trans)
   apply (rule mset_ran_eq_extend[OF R1 E1])
  using B apply auto [2]
  apply (rule mset_ran_eq_extend[OF R2 E2])
  using B apply auto [2]
  done 
  
  
recursive_spec quicksort(a,l,h) returns a 
  assumes "True"
  ensures "ran_sorted a l\<^sub>0 h\<^sub>0 \<and> mset_ran a\<^sub>0 {l\<^sub>0..<h\<^sub>0} = mset_ran a {l\<^sub>0..<h\<^sub>0} \<and> a\<^sub>0=a on -{l\<^sub>0..<h\<^sub>0}"
  variant "h-l"
  defines \<open>
    if (l<h) {
      (a,i) = partition(a,l,h,a[l]);
      a = rec quicksort(a,l,i);
      a = rec quicksort(a,i+1,h)
    }
  \<close>
  apply (vcg_cs; (intro conjI)?)
  subgoal using quicksort_sorted_aux by metis
  subgoal using quicksort_mset_aux by metis
  subgoal by (smt ComplD ComplI atLeastLessThan_iff eq_on_def)
  subgoal by (auto simp: ran_sorted_def)
  done
  
  
subsection \<open>Data Refinement\<close>

subsubsection \<open>Filtering\<close>

program_spec array_filter_negative
  assumes "l\<le>h"
  ensures "lran a l\<^sub>0 i = filter (\<lambda>x. x\<ge>0) (lran a\<^sub>0 l\<^sub>0 h\<^sub>0)"
  defines \<open>
    i=l; j=l;
    while (j<h) 
      @invariant \<open> 
          l\<le>i \<and> i\<le>j \<and> j\<le>h     
        \<and> lran a l i = filter (\<lambda>x. x\<ge>0) (lran a\<^sub>0 l j)
        \<and> lran a j h = lran a\<^sub>0 j h
      \<close>
      @variant \<open>h-j\<close>
    {
      if (a[j]\<ge>0) {a[i] = a[j]; i=i+1};
      j=j+1
    }
  \<close>
  supply lran_eq_iff[simp] lran_tail[simp del]
  apply vcg_cs
  done
  
  (* Exercise: Use swap to modify this algorithm to partitioning! *)
  

  
subsubsection \<open>Merge Two Sorted Lists\<close>

text \<open>
  We define the merge function abstractly first, as a functional program on lists.
\<close>

fun merge where
  "merge [] ys = ys"
| "merge xs [] = xs"
| "merge (x#xs) (y#ys) = (if x<y then x#merge xs (y#ys) else y#merge (x#xs) ys)"   

lemma merge_add_simp[simp]: "merge xs [] = xs" by (cases xs) auto

text \<open>It's straightforward to show that this produces a sorted list with the same elements.\<close>
lemma merge_sorted:
  assumes "sorted xs" "sorted ys" 
  shows "sorted (merge xs ys) \<and> set (merge xs ys) = set xs \<union> set ys"
  using assms
  apply (induction xs ys rule: merge.induct)
    apply auto
  done
  
lemma merge_mset: "mset (merge xs ys) = mset xs + mset ys"  
  by (induction xs ys rule: merge.induct) auto
  
  
  
text \<open>Next, we prove an equation that characterizes one step of the while loop,
  on the list level.\<close>
lemma merge_eq: "xs\<noteq>[] \<or> ys\<noteq>[] \<Longrightarrow> merge xs ys = (
  if ys=[] \<or> (xs\<noteq>[] \<and> hd xs < hd ys) then hd xs # merge (tl xs) ys
  else hd ys # merge xs (tl ys)
  )"
  by (cases xs; cases ys; simp)

text \<open>
  We do a first proof that our merge implementation on the arrays and indexes
  behaves like the functional merge on the corresponding lists.
  
  The annotations use the @{const lran} function to map from the implementation level 
  to the list level. Moreover, the invariant of the implementation, \<open>l\<le>h\<close>, is carried 
  through explicitly.
\<close>
program_spec merge_imp' 
  assumes "l1\<le>h1 \<and> l2\<le>h2"
  ensures "let ms = lran m 0 j; xs\<^sub>0 = lran a1\<^sub>0 l1\<^sub>0 h1\<^sub>0; ys\<^sub>0 = lran a2\<^sub>0 l2\<^sub>0 h2\<^sub>0 in  
    j\<ge>0 \<and> ms = merge xs\<^sub>0 ys\<^sub>0"
  defines \<open>
    j=0;
    while (l1\<noteq>h1 \<or> l2\<noteq>h2) 
      @variant \<open>h1 + h2 - l1 - l2\<close>
      @invariant \<open>let 
          xs=lran a1 l1 h1; ys = lran a2 l2 h2; ms = lran m 0 j;
          xs\<^sub>0 = lran a1\<^sub>0 l1\<^sub>0 h1\<^sub>0; ys\<^sub>0 = lran a2\<^sub>0 l2\<^sub>0 h2\<^sub>0
        in 
          l1\<le>h1 \<and> l2\<le>h2 \<and> 0\<le>j \<and>
          merge xs\<^sub>0 ys\<^sub>0 = ms@merge xs ys
      \<close>
    {
      if (l2==h2 \<or> (l1\<noteq>h1 \<and> a1[l1] < a2[l2])) {
        m[j] = a1[l1];
        l1=l1+1
      } else {
        m[j] = a2[l2];
        l2=l2+1
      };
      j=j+1
    }
  \<close>
  text \<open>Given the @{thm [source] merge_eq} theorem, which captures the essence of a loop step,
    and the theorems @{thm lran_append1}, @{thm lran_tail}, and @{thm hd_lran}, which
    convert from the operations on arrays and indexes to operations on lists,
    the proof is straightforward
  \<close>
  apply vcg_cs
  subgoal apply (subst merge_eq) by auto
  subgoal by linarith
  subgoal apply (subst merge_eq) by auto
  done

text \<open>
  In a next step, we refine our proof to 
  combine it with the abstract properties we have proved about merge.
  The program does not change (we simply inline the original one here).
\<close>
  
procedure_spec merge_imp (a1,l1,h1,a2,l2,h2) returns (m,j)
  assumes "l1\<le>h1 \<and> l2\<le>h2 \<and> sorted (lran a1 l1 h1) \<and> sorted (lran a2 l2 h2)"
  ensures "let ms = lran m 0 j in 
      j\<ge>0 
    \<and> sorted ms 
    \<and> mset ms = mset (lran a1\<^sub>0 l1\<^sub>0 h1\<^sub>0) + mset (lran a2\<^sub>0 l2\<^sub>0 h2\<^sub>0)"
  for l1 h1 l2 h2 a1[] a2[] m[] j
  defines \<open>inline merge_imp'\<close>
  apply vcg_cs
  apply (auto simp: Let_def merge_mset dest: merge_sorted)
  done
  
thm merge_imp_spec  
thm merge_imp_def
  
lemma [named_ss vcg_bb]:
  "UNIV \<union> a = UNIV"  
  "a \<union> UNIV = UNIV"  
  by auto
  
  
lemma merge_msets_aux: "\<lbrakk>l\<le>m; m\<le>h\<rbrakk> \<Longrightarrow> mset (lran a l m) + mset (lran a m h) = mset (lran a l h)"  
  by (auto simp: mset_lran mset_ran_combine ivl_disj_un_two)
  
  
  
  
recursive_spec mergesort (a,l,h) returns (b,j)
  assumes "l\<le>h"
  ensures \<open>0\<le>j \<and> sorted (lran b 0 j) \<and> mset (lran b 0 j) = mset (lran a\<^sub>0 l\<^sub>0 h\<^sub>0)\<close>
  variant \<open>h-l\<close>
  for a[] b[]
  defines \<open>
    if (l==h) j=0
    else if (l+1==h) {
      b[0] = a[l];
      j=1
    } else {
      m = (h+l) / 2;
      (a1,h1) = rec mergesort (a,l,m);
      (a2,h2) = rec mergesort (a,m,h);
      (b,j) = merge_imp (a1,0,h1,a2,0,h2) 
    }
  \<close>
  apply vcg
       apply auto []
      apply (auto simp: lran.simps) []
     apply auto []
    apply auto []
   apply auto []
  apply (auto simp: Let_def merge_msets_aux) []
  done
print_theorems    
  
  
subsubsection \<open>Remove Duplicates from Array, using Bitvector Set\<close>  
  
text \<open>We use an array to represent a set of integers.

  If we only insert elements in range \<open>{0..<n}\<close>, this representation
  is called bit-vector (storing a single bit per index is enough).
\<close>

definition set_of :: "(int \<Rightarrow> int) \<Rightarrow> int set" where "set_of a \<equiv> {i. a i \<noteq> 0}"

context notes [simp] = set_of_def begin
  lemma set_of_empty[simp]: "set_of (\<lambda>_. 0) = {}" by auto
  lemma set_of_insert[simp]: "x\<noteq>0 \<Longrightarrow> set_of (a(i:=x)) = insert i (set_of a)" by auto
  lemma set_of_remove[simp]: "set_of (a(i:=0)) = set_of a - {i}" by auto
  lemma set_of_mem[simp]: "i\<in>set_of a \<longleftrightarrow> a i \<noteq> 0" by auto
end

program_spec dedup
  assumes \<open>l\<le>h\<close>
  ensures \<open>set (lran a l i) = set (lran a\<^sub>0 l h) \<and> distinct (lran a l i)\<close>
  defines \<open>
    i=l; j=l;
    clear b[];
    while (j<h) 
      @variant \<open>h-j\<close>
      @invariant \<open>l\<le>i \<and> i\<le>j \<and> j\<le>h 
        \<and> set (lran a l i) = set (lran a\<^sub>0 l j)
        \<and> distinct (lran a l i)
        \<and> lran a j h = lran a\<^sub>0 j h
        \<and> set_of b = set (lran a l i)
       \<close>
    {
      if (b[a[j]] == 0) {
        a[i] = a[j]; i=i+1; b[a[j]] = 1
      };
      j=j+1
    }
  \<close>
  apply vcg_cs
   apply (auto simp: lran_eq_iff lran_upd_inside intro: arg_cong[where f=tl]) []
  apply (auto simp: lran_eq_iff) []
  done
  
  
procedure_spec bv_init () returns b 
  assumes True ensures \<open>set_of b = {}\<close> 
  defines \<open>clear b[]\<close>
  by vcg_cs
  
procedure_spec bv_insert (x, b) returns b 
  assumes True ensures \<open>set_of b = insert x\<^sub>0 (set_of b\<^sub>0)\<close>
  defines \<open>b[x] = 1\<close>
  by vcg_cs
  
procedure_spec bv_remove (x, b) returns b
  assumes True ensures \<open>set_of b = set_of b\<^sub>0 - {x\<^sub>0}\<close>
  defines \<open>b[x] = 0\<close>
  by vcg_cs
  
procedure_spec bv_elem (x,b) returns r  
  assumes True ensures \<open>r\<noteq>0 \<longleftrightarrow> x\<^sub>0\<in>set_of b\<^sub>0\<close>
  defines \<open>r = b[x]\<close>
  by vcg_cs
  
  
procedure_spec dedup' (a,l,h) returns (a,l,i)
  assumes \<open>l\<le>h\<close> ensures \<open>set (lran a l i) = set (lran a\<^sub>0 l\<^sub>0 h\<^sub>0) \<and> distinct (lran a l i) \<close>
  for b[]
  defines \<open>
    b = bv_init();
  
    i=l; j=l;
    
    while (j<h) 
      @variant \<open>h-j\<close>
      @invariant \<open>l\<le>i \<and> i\<le>j \<and> j\<le>h 
        \<and> set (lran a l i) = set (lran a\<^sub>0 l j)
        \<and> distinct (lran a l i)
        \<and> lran a j h = lran a\<^sub>0 j h
        \<and> set_of b = set (lran a l i)
       \<close>
    {
      mem = bv_elem (a[j],b);
      if (mem == 0) {
        a[i] = a[j]; i=i+1; b = bv_insert(a[j],b)
      };
      j=j+1
    }
  \<close>
  apply vcg_cs
   apply (auto simp: lran_eq_iff lran_upd_inside intro: arg_cong[where f=tl])
  done
  
subsection \<open>Recursion\<close>  

subsubsection \<open>Recursive Fibonacci\<close>

recursive_spec fib_imp (i) returns r assumes True ensures \<open>r = fib i\<^sub>0\<close> variant \<open>i\<close>
  defines \<open>
    if (i\<le>0) r=0
    else if (i==1) r=1
    else {
      r1=rec fib_imp (i-2);
      r2=rec fib_imp (i-1);
      r = r1+r2
    }
  \<close>
  by vcg_cs    
    
subsubsection \<open>Homeier's Cycling Termination\<close>  

text \<open>A contrived example from Homeier's thesis. 
  Only the termination proof is done.\<close>
(* TODO: Also show correctness: pedal (a,b) will multiply its arguments!
  correctness proof may be a good test how to handle specs with logical vars!
*)  
  
recursive_spec 
  pedal (n,m) returns () assumes \<open>n\<ge>0 \<and> m\<ge>0\<close> ensures True variant \<open>n+m\<close>
  defines \<open>
    if (n\<noteq>0 \<and> m\<noteq>0) {
      G = G + m;
      if (n<m) rec coast (n-1,m-1) else rec pedal(n-1,m)
    }
  \<close>
and
  coast (n,m) returns () assumes \<open>n\<ge>0 \<and> m\<ge>0\<close> ensures True variant \<open>n+m+1\<close>
  defines \<open>
    G = G + n;
    if (n<m) rec coast (n,m-1) else rec pedal (n,m)
  \<close>
  by vcg_cs  
  
  
subsubsection \<open>Ackermann\<close>  
  
fun ack :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ack 0 n = n+1"
| "ack m 0 = ack (m-1) 1"
| "ack m n = ack (m-1) (ack m (n-1))"
  
lemma ack_add_simps[simp]: 
  "m\<noteq>0 \<Longrightarrow> ack m 0 = ack (m-1) 1"
  "\<lbrakk>m\<noteq>0; n\<noteq>0\<rbrakk> \<Longrightarrow> ack m n = ack (m-1) (ack m (n-1))"
  subgoal by (cases m) auto
  subgoal by (cases "(m,n)" rule: ack.cases) (auto)
  done

recursive_spec relation "less_than <*lex*> less_than"
  ack_imp (m,n) returns r
    assumes "m\<ge>0 \<and> n\<ge>0" ensures "r=int (ack (nat m\<^sub>0) (nat n\<^sub>0))"
    variant "(nat m, nat n)" 
    defines \<open>
      if (m==0) r = n+1
      else if (n==0) r = rec ack_imp (m-1,1)
      else {
        t = rec ack_imp (m,n-1);
        r = rec ack_imp (m-1,t)
      }
    \<close>
  supply nat_distribs[simp]
  by vcg_cs
  
  
subsubsection \<open>McCarthy's 91 Function\<close>
text \<open>A standard benchmark for verification of recursive functions.
  We use Homeier's version with a global variable.\<close>
  
recursive_spec p91(y) assumes True ensures "if 100<y\<^sub>0 then G = y\<^sub>0-10 else G = 91" variant "101-y" 
  for G
  defines \<open>
    if (100<y) G=y-10
    else {
      rec p91 (y+11);
      rec p91 (G)
    }
  \<close>
  apply vcg_cs
   apply (auto split: if_splits)
  done
  
subsubsection \<open>Odd/Even\<close>  
  
recursive_spec 
  odd_imp (a) returns b 
    assumes True
    ensures "b\<noteq>0 \<longleftrightarrow> odd a\<^sub>0"
    variant "\<bar>a\<bar>"
    defines \<open>
      if (a==0) b=0
      else if (a<0) b = rec even_imp (a+1)
      else b = rec even_imp (a-1)
    \<close>
  and
  even_imp (a) returns b
    assumes True
    ensures "b\<noteq>0 \<longleftrightarrow> even a\<^sub>0"
    variant "\<bar>a\<bar>"
    defines \<open>
      if (a==0) b=1
      else if (a<0) b = rec odd_imp (a+1)
      else b = rec odd_imp (a-1)
    \<close>
  apply vcg  
           apply auto
  done  

thm even_imp_spec

  
subsubsection \<open>Pandya and Joseph's Product Producers\<close>
text \<open>Again, taking the version from Homeier's thesis, but with a 
  modification to also terminate for negative \<open>y\<close>.
  \<close>
  
recursive_spec relation \<open>measure nat <*lex*> less_than\<close>
  product () assumes True ensures \<open>GZ = GZ\<^sub>0 + GX\<^sub>0*GY\<^sub>0\<close> variant "(\<bar>GY\<bar>,1::nat)" 
  for GX GY GZ
  defines
  \<open>
    e = even_imp (GY);
    if (e\<noteq>0) rec evenproduct() else rec oddproduct()
  \<close>
and
  oddproduct() assumes \<open>odd GY\<close> ensures \<open>GZ = GZ\<^sub>0 + GX\<^sub>0*GY\<^sub>0\<close> variant "(\<bar>GY\<bar>,0::nat)" 
  for GX GY GZ
  defines
  \<open>
    if (GY<0) {
      GY = GY + 1;
      GZ = GZ - GX
    } else {
      GY = GY - 1;
      GZ = GZ + GX
    };
    rec evenproduct()
  \<close>
and
  evenproduct() assumes \<open>even GY\<close> ensures \<open>GZ = GZ\<^sub>0 + GX\<^sub>0*GY\<^sub>0\<close> variant "(\<bar>GY\<bar>,0::nat)" 
  for GX GY GZ
  defines
  \<open>
    if (GY\<noteq>0) {
      GX = 2*GX;
      GY = GY / 2;
      rec product()
    }
  \<close>
  apply vcg_cs
     apply (auto simp: algebra_simps)
   apply presburger+
  done
  
  
(*
  TODO: 
    * Infrastructure to prove different specification for same program
      (DONE) We can use inline, and just give program a new name.

    * ghost variables. Keep them existentially qualified, with naming tag.
        ABS_GHOST ''name'' (\<lambda>x. P x) \<equiv> \<exists>x. P x
        GHOST ''name'' value = True
        
        assumes ABS_GHOST name (\<lambda>x. P x) 
        obtains x where "GHOST name x" "P x"
        
        assumes "GHOST name x" and "P x"
        shows "ABS_GHOST name (\<lambda>x. P x)"
        
        Let_Ghost name (\<lambda>x s. C x s) = skip
        
        assumes "\<exists>x. C x s"
        assumes "\<And>x. \<lbrakk> GHOST name x; C x s \<rbrakk> \<Longrightarrow> Q s"
        shows "wp (Let_Ghost name (\<lambda>x s. C x s)) Q s"
        
      Let specification command also abstract over ghost variables in program.
        
*)  
  
(* IDEAS: 
  
  Extend arrays to multiple dimensions: int list \<Rightarrow> int
    Vidx vname "aexp list"
    AssignIdx vname "aexp list" aexp
    ArrayCpy vname vname  -- copy all dimensions (it's simpler)
    ArrayInit vname       -- Init all dimensions
    
    plain values on dimension []!

    then we can easily encode matrices and adjacency lists!
    
*)  

subsection \<open>Graph Algorithms\<close>

subsubsection \<open>DFS\<close>
(* By Simon Wimmer *)

text \<open>A graph is stored as an array of integers. 
  Each node is an index into this array, pointing to a size-prefixed list of successors.

  Example for node \<open>i\<close>, which has successors \<open>s1... sn\<close>:
  \<^verbatim>\<open>
   Indexes: ... |  i  | i+1 | ... | i+n | ...
   Data:    ... |  n  | s1  | ... | sn  | ...
  \<close>
\<close>

definition succs where
  "succs a i \<equiv> a ` {i+1..<a i}" for a :: "int \<Rightarrow> int"

definition Edges where
  "Edges a \<equiv> {(i, j). j \<in> succs a i}"

procedure_spec push' (x, stack, ptr) returns (stack, ptr)
  assumes "ptr \<ge> 0" ensures \<open>lran stack 0 ptr = lran stack\<^sub>0 0 ptr\<^sub>0 @ [x\<^sub>0] \<and> ptr = ptr\<^sub>0 + 1\<close>
  defines \<open>stack[ptr] = x; ptr = ptr + 1\<close>
  by vcg_cs

procedure_spec push (x, stack, ptr) returns (stack, ptr)
  assumes "ptr \<ge> 0" ensures \<open>stack ` {0..<ptr} = {x\<^sub>0} \<union> stack\<^sub>0 ` {0..<ptr\<^sub>0} \<and> ptr = ptr\<^sub>0 + 1\<close>
  for stack[]
  defines \<open>stack[ptr] = x; ptr = ptr + 1\<close>
  by vcg_cs (auto simp: fun_upd_image)

program_spec get_succs
  assumes "j \<le> stop \<and> stop = a (j - 1) \<and> 0 \<le> i"
  ensures "
    stack ` {0..<i} = {x. (j\<^sub>0 - 1, x) \<in> Edges a \<and> x \<notin> set_of visited} \<union> stack\<^sub>0 ` {0..<i\<^sub>0}
    \<and> i \<ge> i\<^sub>0"
for i j stop stack[] a[] visited[]
defines
\<open>
  while (j < stop)
  @invariant \<open>stack ` {0..<i} = {x. x \<in> a ` {j\<^sub>0..<j} \<and> x \<notin> set_of visited} \<union> stack\<^sub>0 ` {0..<i\<^sub>0}
    \<and> j \<le> stop \<and> i\<^sub>0 \<le> i \<and> j\<^sub>0 \<le> j
  \<close>
  @variant \<open>(stop - j)\<close>
  {
    succ = a[j];
    is_elem = bv_elem(succ,visited);
    if (is_elem == 0) {
      (stack, i) = push (succ, stack, i)
    };
    j = j + 1
  }
\<close>
  by vcg_cs (auto simp: intvs_incr_h Edges_def succs_def)

procedure_spec pop (stack, ptr) returns (x, ptr)
  assumes "ptr \<ge> 1" ensures \<open>stack\<^sub>0 ` {0..<ptr\<^sub>0} = stack\<^sub>0 ` {0..<ptr} \<union> {x} \<and> ptr\<^sub>0 = ptr + 1\<close>
  for stack[]
  defines \<open>ptr = ptr - 1; x = stack[ptr]\<close>
  by vcg_cs (simp add: intvs_upper_decr)

procedure_spec stack_init () returns i
  assumes True ensures \<open>i = 0\<close> 
  defines \<open>i = 0\<close>
  by vcg_cs

lemma Edges_empty:
  "Edges a `` {i} = {}" if "i + 1 \<ge> a i"
  using that unfolding Edges_def succs_def by auto

text \<open>This is one of the main insights of the algorithm: if a set of visited states is
closed w.r.t.\ to the edge relation, then it is guaranteed to contain all the states that
are reachable from any state within the set.\<close>
lemma reachability_invariant:
  assumes reachable: "(s, x) \<in> (Edges a)\<^sup>*"
      and closed: "\<forall>v\<in>visited. Edges a `` {v} \<subseteq> visited"
      and start: "s \<in> visited"
  shows "x \<in> visited"
  using reachable start closed by induction auto

program_spec (partial) dfs
  assumes "0 \<le> x \<and> 0 \<le> s"
  ensures "b = 1 \<longleftrightarrow> x \<in> (Edges a)\<^sup>* `` {s}" defines \<open>
  b = 0;
  clear stack[];
  i = stack_init();
  (stack, i) = push (s, stack, i);
  clear visited[];
  while (b == 0 \<and> i \<noteq> 0)
    @invariant \<open>0 \<le> i \<and> (s \<in> stack ` {0..<i} \<or> s \<in> set_of visited) \<and> (b = 0 \<or> b = 1) \<and> (
    if b = 0 then
      stack ` {0..<i} \<subseteq> (Edges a)\<^sup>* `` {s}
      \<and> (\<forall>v \<in> set_of visited. (Edges a) `` {v} \<subseteq> set_of visited \<union> stack ` {0..<i})
      \<and> (x \<notin> set_of visited)
    else x \<in> (Edges a)\<^sup>* `` {s})
  \<close>
  {
    (next, i) = pop(stack, i); \<comment>\<open>Take the top most element from the stack.\<close>
    visited = bv_insert(next, visited); \<comment>\<open>Mark it as visited,\<close>
    if (next == x) {
      b = 1 \<comment>\<open>If it is the target, we are done.\<close>
    } else {
      \<comment>\<open>Else, put its successors on the stack if they are not yet visited.\<close>
      stop = a[next];
      j = next + 1;
      if (j \<le> stop) {
        inline get_succs
      }
    }
  }
\<close>
  apply vcg_cs
  subgoal by (auto simp: set_of_def)
  subgoal using intvs_lower_incr by (auto simp: Edges_empty)
  subgoal by auto (fastforce simp: set_of_def dest!: reachability_invariant)
  done


text \<open>Assuming that the input graph is finite, we can also prove that the algorithm terminates.
We will thus use an \<open>Isabelle context\<close> to fix a certain finite graph and a start state:
\<close>

context
  fixes start :: int and edges
  assumes finite_graph[intro!]: "finite ((Edges edges)\<^sup>* `` {start})"
begin

lemma sub_insert_same_iff: "s \<subset> insert x s \<longleftrightarrow> x\<notin>s" by auto

program_spec dfs1
  assumes "0 \<le> x \<and> 0 \<le> s \<and> start = s \<and> edges = a"
  ensures "b = 1 \<longleftrightarrow> x \<in> (Edges a)\<^sup>* `` {s}"
  for visited[]
  defines
\<open>
  b = 0;
  \<comment>\<open>\<open>i\<close> will point to the next free space in the stack (i.e. it is the size of the stack)\<close>
  i = 1;
  \<comment>\<open>Initially, we put \<open>s\<close> on the stack.\<close>
  stack[0] = s;
  visited = bv_init();
  while (b == 0 \<and> i \<noteq> 0)
    @invariant \<open>
    0 \<le> i \<and> (s \<in> stack ` {0..<i} \<or> s \<in> set_of visited) \<and> (b = 0 \<or> b = 1) \<and>
    set_of visited \<subseteq> (Edges edges)\<^sup>* `` {start} \<and> (
    if b = 0 then
      stack ` {0..<i} \<subseteq> (Edges a)\<^sup>* `` {s}
      \<and> (\<forall>v \<in> set_of visited. (Edges a) `` {v} \<subseteq> set_of visited \<union> stack ` {0..<i})
      \<and> (x \<notin> set_of visited)
    else x \<in> (Edges a)\<^sup>* `` {s})
    \<close>
    @relation \<open>finite_psupset ((Edges edges)\<^sup>* `` {start}) <*lex*> less_than\<close>
    @variant \<open> (set_of visited, nat i)\<close>
  {
    \<comment>\<open>Take the top most element from the stack.\<close>
    (next, i) = pop(stack, i);
    if (next == x) {
      \<comment>\<open>If it is the target, we are done.\<close>
      visited = bv_insert(next, visited);
      b = 1
    } else {
      is_elem = bv_elem(next, visited);
      if (is_elem == 0) {
        visited = bv_insert(next, visited);
        \<comment>\<open>Else, put its successors on the stack if they are not yet visited.\<close>
        stop = a[next];
        j = next + 1;
        if (j \<le> stop) {
          inline get_succs
        }
      }
    }
  }
\<close>
  apply vcg_cs
  subgoal by auto
  subgoal by (auto simp add: image_constant_conv)
  subgoal by (clarsimp simp: finite_psupset_def sub_insert_same_iff)
  subgoal by (auto simp: set_of_def)
  subgoal by (clarsimp simp: finite_psupset_def sub_insert_same_iff)
  subgoal by (auto simp: Edges_empty)
  subgoal by (clarsimp simp: finite_psupset_def sub_insert_same_iff)
  subgoal by (auto simp: set_of_def)
  subgoal by auto (fastforce simp: set_of_def dest!: reachability_invariant)
  done

end


end