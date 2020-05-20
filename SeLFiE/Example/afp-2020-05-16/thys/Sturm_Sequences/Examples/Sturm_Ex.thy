section \<open>Example usage of the ``sturm'' method\<close>
(* Author: Manuel Eberl <eberlm@in.tum.de> *)
theory Sturm_Ex
imports "../Sturm"
begin

text \<open>
  In this section, we give a variety of statements about real polynomials that can b
  proven by the \emph{sturm} method.
\<close>

lemma
 "\<forall>x::real. x^2 + 1 \<noteq> 0"
by sturm

lemma
  fixes x :: real
  shows "x^2 + 1 \<noteq> 0" by sturm

lemma "(x::real) > 1 \<Longrightarrow> x^3 > 1" by sturm

lemma "\<forall>x::real. x*x \<noteq> -1" by sturm

schematic_goal A:
"card {x::real. -0.010831 < x \<and> x < 0.010831 \<and> 
    1/120*x^5 + 1/24*x^4 +1/6*x^3 - 49/16777216*x^2 - 17/2097152*x = 0} 
  = ?n"
  by sturm

lemma "card {x::real. x^3 + x = 2*x^2 \<and> x^3 - 6*x^2 + 11*x = 6} = 1" 
by sturm


schematic_goal "card {x::real. x^3 + x = 2*x^2 \<or> x^3 - 6*x^2 + 11*x = 6} = ?n" by sturm

lemma
  "card {x::real. -0.010831 < x \<and> x < 0.010831 \<and> 
     poly [:0, -17/2097152, -49/16777216, 1/6, 1/24, 1/120:] x = 0} = 3"
  by sturm

lemma "\<forall>x::real. x*x \<noteq> 0 \<or> x*x - 1 \<noteq> 2*x" by sturm

lemma "(x::real)*x+1 \<noteq> 0 \<and> (x^2+1)*(x^2+2) \<noteq> 0" by sturm

text\<open>3 examples related to continued fraction approximants to exp: LCP\<close>
lemma fixes x::real
  shows "-7.29347719 \<le> x \<Longrightarrow> 0 < x^5 + 30*x^4 + 420*x^3 + 3360*x^2 + 15120*x + 30240"
by sturm

lemma fixes x::real
  shows "0 < x^6 + 42*x^5 + 840*x^4 + 10080*x^3 + 75600*x\<^sup>2 + 332640*x + 665280"
by sturm

schematic_goal "card {x::real. x^7 + 56*x^6 + 1512*x^5 + 25200*x^4 + 277200*x^3 + 1995840*x^2 + 8648640*x = -17297280} = ?n" 
by sturm

end
