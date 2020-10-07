(*  Title:       Instances of Schneider's generalized protocol of clock synchronization
    Author:      Damián Barsotti <damian at hal.famaf.unc.edu.ar>, 2006
    Maintainer:  Damián Barsotti <damian at hal.famaf.unc.edu.ar>
*)

section \<open>Interactive Convergence Algorithms (ICA)\<close>

theory ICAInstance imports Complex_Main begin

text \<open>This algorithm is presented in \cite{lamport_cs}.\<close>

text \<open>A proof of the three properties can be found in
\cite{shankar92mechanical}.\<close>

subsection \<open>Model of the system\<close>

text \<open>The main ideas for the formalization of the system were
obtained from \cite{shankar92mechanical}.\<close>

subsubsection \<open>Types in the formalization\<close>

text \<open>The election of the basics types was based on
\cite{shankar92mechanical}. There, the process are natural numbers and
the real time and the clock readings are reals.\<close>

type_synonym process = nat
type_synonym time = real       \<comment> \<open>real time\<close>
type_synonym Clocktime = real  \<comment> \<open>time of the clock readings (clock time)\<close>

subsubsection \<open>Some constants\<close>

text\<open>Here we define some parameters of the algorithm that we use:
the number of process and the fix value that is used to discard the
processes whose clocks differ more than this amount from the own one
(see \cite{shankar92mechanical}). The defined constants must satisfy
this axiom (if $np = 0$ we have a division by cero in the definition
of the convergence function).\<close>

axiomatization
  np :: nat      \<comment> \<open>Number of processes\<close> and
  \<Delta> :: Clocktime \<comment> \<open>Fix value to discard processes\<close> where
  constants_ax: "0 <= \<Delta> \<and> np > 0" 

text \<open>We define also the set of process that the algorithm
manage. This definition exist only for readability matters.\<close>

definition
PR :: "process set" where
[simp]: "PR = {..<np}"


subsubsection \<open>Convergence function\<close>

text \<open>This functions is called ``Egocentric Average''
(\cite{schneider87understanding})\<close>

text \<open>In this algorithm each process has an array where it store the
clocks readings from the others processes (including itself). We
formalise that as a function from processes to clock time as
\cite{shankar92mechanical}.\<close>

text \<open>First we define an auxiliary function. It takes a function of
clock readings and two processes, and return de reading of the second
process if the difference of the readings is grater than @{term \<Delta>},
otherwise it returns the reading of the first one.\<close>

definition
  fiX :: "[(process \<Rightarrow> Clocktime), process, process] \<Rightarrow> Clocktime" where
  "fiX f p l = (if \<bar>f p - f l\<bar> <= \<Delta> then (f l) else (f p))"

text \<open>And finally the convergence function. This is defined with the
builtin generalized summation over a set constructor of Isabelle.
Also we had to use the overloaded @{term real} function to typecast de
number @{term np}.\<close>

definition
  (* The averaging function to calculate clock adjustment *)
  cfni :: "[process, (process \<Rightarrow> Clocktime)] \<Rightarrow> Clocktime" where
  "cfni p f = (\<Sum> l\<in>{..<np}. fiX f p l) / (real np)"

subsection \<open>Translation Invariance property.\<close>

text \<open>We first need to prove this auxiliary lemma.\<close>

lemma trans_inv': 
"(\<Sum> l\<in>{..<np'}. fiX (\<lambda> y. f y + x) p l) = 
        (\<Sum> l\<in>{..<np'}. fiX f p l) + real np' * x"
apply (induct_tac np')
apply (auto simp add: cfni_def  fiX_def of_nat_Suc 
       distrib_right lessThan_Suc)
done

theorem trans_inv: 
"\<forall> p f x . cfni p (\<lambda> y. f y + x) = cfni p f + x"
apply (auto simp add: cfni_def trans_inv' distrib_right 
       divide_inverse  constants_ax)
done

subsection \<open>Precision Enhancement property\<close>

text \<open>An informal proof of this theorem can be found in
\cite{shankar92mechanical}\<close>

subsubsection \<open>Auxiliary lemmas\<close>

lemma finitC:
  "C \<subseteq> PR \<Longrightarrow> finite C"
proof-
  assume "C \<subseteq> PR"
  thus ?thesis using finite_subset by auto
qed

lemma finitnpC:
  "finite (PR - C)"
proof-
  show ?thesis  using finite_Diff by auto
qed
 

text \<open>The next lemmas are about arithmetic properties of the
generalized summation over a set constructor.\<close>

lemma sum_abs_triangle_ineq:
"finite S \<Longrightarrow>
  \<bar>\<Sum>l\<in>S. (f::'a \<Rightarrow> 'b::linordered_idom) l\<bar> <= (\<Sum>l\<in>S. \<bar>f l\<bar>)"
  (is "... \<Longrightarrow> ?P S")
  by (rule sum_abs)

lemma sum_le:
  "\<lbrakk>finite S ; \<forall> r\<in>S. f r <= b \<rbrakk>
  \<Longrightarrow>
  (\<Sum>l\<in>S. f l) <= real (card S) * b"
  (is "\<lbrakk> finite S ; \<forall> r\<in>S. f r <= b \<rbrakk> \<Longrightarrow> ?P S")
proof(induct S rule: finite_induct)
  show "?P {}" by simp 
next
  fix F x 
  assume  finit: "finite F" and xnotinF: "x \<notin> F" and
          HI1: "\<forall>r\<in>F. f r \<le> b \<Longrightarrow> sum f F \<le> real (card F) * b"
          and HI2: "\<forall>r\<in>insert x F. f r \<le> b"
  from HI1 HI2 and finit and xnotinF
  have "sum f (insert x F) <= b + real (card F) * b"
    by auto
  also 
  have "... = real (Suc (card  F)) * b"
    by (simp add: distrib_right  of_nat_Suc)
  also 
  from   finit xnotinF have "...= real (card (insert x F)) * b"
    by simp
  finally
  show "?P (insert x F)" .
qed

lemma sum_np_eq:
assumes 
  hC: "C \<subseteq> PR"
shows 
  "(\<Sum>l\<in>{..<np}. f l) = (\<Sum>l\<in>C. f l) + (\<Sum>l\<in>({..<np}-C). f l)"
proof-
  note finitC[where C=C]
  moreover
  note finitnpC[where C=C]
  moreover
  have "C \<inter> ({..<np}-C) = {}" by auto
  moreover
  from hC have "C \<union> ({..<np}-C) = {..<np}" by auto
  ultimately
  show ?thesis
    using sum.union_disjoint[where A=C and B="{..<np} - C"]
    by auto
qed
 
lemma abs_sum_np_ineq:
assumes 
  hC: "C \<subseteq> PR"
shows 
  "\<bar>(\<Sum>l\<in>{..<np}. (f::nat \<Rightarrow> real) l)\<bar> <=  
     (\<Sum>l\<in>C. \<bar>f l\<bar>) + (\<Sum>l\<in>({..<np}-C). \<bar>f l\<bar>)"
    (is "?abs_sum <= ?sumC + ?sumnpC")
proof-
  from hC and sum_np_eq[where f=f] 
  have "?abs_sum = \<bar>(\<Sum>l\<in>C. f l) + (\<Sum>l\<in>({..<np}-C). f l)\<bar>" 
    (is "?abs_sum = \<bar>?sumC' + ?sumnpC'\<bar>")
    by simp
  also
  from abs_triangle_ineq
  have "...<= \<bar>?sumC'\<bar> + \<bar>?sumnpC'\<bar>" .
  also
  have "... <=  ?sumC + ?sumnpC "
  proof-
    from hC finitC sum_abs_triangle_ineq 
    have "\<bar>?sumC'\<bar> <= ?sumC" by blast
    moreover
    from finitnpC and
           sum_abs_triangle_ineq[where f=f and S="PR-C"]  
    have "\<bar>?sumnpC'\<bar> <= ?sumnpC" 
      by force
    ultimately
    show ?thesis by arith
  qed
  finally
  show ?thesis .
qed

text \<open>The next lemmas are about the existence of bounds that are
necesary in order to prove the Precicion Enhancement theorem.\<close>
  
lemma fiX_ubound:
  "fiX f p l <= f p + \<Delta>"
proof(cases "\<bar>f p - f l\<bar> \<le> \<Delta>")
  assume asm: "\<bar>f p - f l\<bar> \<le> \<Delta>" 
  hence "fiX f p l = f l" by (simp add: fiX_def) 
  also
  from asm have "f l <= f p + \<Delta>" by arith
  finally
  show ?thesis by arith
next
  assume asm: "\<not>\<bar>f p - f l\<bar> \<le> \<Delta>" 
  hence "fiX f p l = f p" by (simp add: fiX_def) 
  also
  from asm and  constants_ax have "f p <= f p + \<Delta>" by arith
  finally
  show ?thesis by arith
qed

lemma fiX_lbound:
  "f p - \<Delta> <= fiX f p l"
proof(cases "\<bar>f p - f l\<bar> \<le> \<Delta>")
  assume asm: "\<bar>f p - f l\<bar> \<le> \<Delta>" 
  hence "fiX f p l = f l" by (simp add: fiX_def) 
  also
  from asm have "f p - \<Delta> <= f l" by arith
  finally
  show ?thesis by arith
next
  assume asm: "\<not>\<bar>f p - f l\<bar> \<le> \<Delta>" 
  with  constants_ax have "f p - \<Delta> <= f p" by arith
  also
  from asm have "f p = fiX f p l" by (simp add: fiX_def) 
  finally
  show ?thesis by arith
qed

lemma abs_fiX_bound: "\<bar>fiX f p l - f p \<bar> <= \<Delta>"
proof-
(*
from constants_ax and fiX_lbound and fiX_ubound show ?thesis by arith
*)
have "f p - \<Delta> <= fiX f p l \<and> fiX f p l <= f p + \<Delta> \<longrightarrow> ?thesis"
by arith
with fiX_lbound  fiX_ubound show ?thesis by blast
qed

lemma abs_dif_fiX_bound:
assumes
  hbx: "\<forall> l\<in>C. \<bar>f l - g l\<bar> <= x" and
  hby: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= y" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" 
shows
  "\<bar>fiX f p r - fiX g q r\<bar> <= 2 * \<Delta> + x + y"
proof-
  have "\<bar>fiX f p r - fiX g q r\<bar> = 
    \<bar>fiX f p r - f p + f p - fiX g q r\<bar> "
    by auto
  also
  have "... <= \<bar>fiX f p r - f p \<bar> + \<bar>f p - fiX g q r\<bar> "
    by arith
  also 
  from abs_fiX_bound 
  have "... <= \<Delta> + \<bar>f p - fiX g q r\<bar>"
    by simp
  also
  have "... = \<Delta> + \<bar>f p - g q + (g q - fiX g q r)\<bar>"
    by simp
  also
  from abs_triangle_ineq[where a = "f p - g q" and 
                               b = "g q - fiX g q r"] 
  have "... <= \<Delta> + \<bar>f p - g q \<bar> + \<bar> g q - fiX g q r\<bar>"
    by simp
  also 
  have "... = \<Delta> + \<bar>f p - g q \<bar> + \<bar> fiX g q r - g q\<bar>"
    by arith
  also 
  from abs_fiX_bound
  have "... <= 2 * \<Delta> + \<bar>f p - g q \<bar> " 
    by simp
  also
  have "... = 2 * \<Delta> + \<bar>f p - f q + (f q - g q) \<bar> " 
    by simp
  also
  from abs_triangle_ineq[where a = "f p - f q" and 
                               b = "f q - g q"] 
  have "... <= 2 * \<Delta> + \<bar>f p - f q \<bar> + \<bar> f q - g q \<bar> " 
    by simp
  finally
  show ?thesis using hbx hby hpC hqC
    by force
qed
        

lemma abs_dif_fiX_bound_C_aux1:
assumes 
  hbx: "\<forall> l\<in>C. \<bar>f l - g l\<bar> <= x" and
  hby1: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= y" and
  hby2: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>g l - g m\<bar> <= y" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" and
  hrC: "r\<in>C" 
shows
  "\<bar>fiX f p r - fiX g q r\<bar> <= x + y"
proof(cases "\<bar>f p - f r\<bar> \<le> \<Delta>")
  case True 
  note outer_IH = True 
  show ?thesis
  proof(cases "\<bar>g q - g r\<bar> \<le> \<Delta>")
    case True
    show ?thesis
    proof -
      from hpC and hby1 have "0<=y" by force
      with hrC and hbx have "\<bar> f r - g r \<bar> <= x + y" by auto
      with outer_IH and True show ?thesis 
        by (auto simp add: fiX_def)
    qed
  next
    case False 
    show ?thesis
    proof -
      from outer_IH and False 
      have "\<bar>fiX f p r - fiX g q r\<bar> = \<bar>f r - g q\<bar>" 
        by  (auto simp add: fiX_def)
      also
      have "... = \<bar> f r - f q + f q - g q \<bar>" by simp
      also
      have "... <= \<bar> f r - f q \<bar> + \<bar> f q - g q \<bar>" 
        by arith
      also
      from hbx hby1 hpC hqC hrC have "... <= x + y" by force
      finally
      show ?thesis .
    qed
  qed
next
  case False 
  note outer_IH = False
  show ?thesis
  proof(cases "\<bar>g q - g r\<bar> \<le> \<Delta>")
    case True
    show ?thesis
    proof -
      from outer_IH and True 
      have "\<bar>fiX f p r - fiX g q r\<bar> = \<bar>f p - g r\<bar>" 
        by  (auto simp add: fiX_def)
      also
      have "... = \<bar> f p - f r + f r - g r \<bar>" by simp
      also
      from abs_triangle_ineq[where a = "f p - f r" and 
                                   b = "f r - g r"]
      have "... <= \<bar> f p - f r \<bar> + \<bar> f r - g r \<bar>" 
        by auto
      also
      from hbx hby1 hpC hrC have "... <= x + y" by force
      finally
      show ?thesis .
    qed
  next
    case False 
    show ?thesis
    proof -
      from outer_IH and False 
      have "\<bar>fiX f p r - fiX g q r\<bar> = \<bar>f p - g q\<bar>" 
        by  (auto simp add: fiX_def)
      also
      have "... = \<bar> f p - f q + f q - g q \<bar>" by simp
      also
      from abs_triangle_ineq[where a = "f p - f q" and 
                                   b = "f q - g q"]
      have "... <= \<bar> f p - f q \<bar> + \<bar> f q - g q \<bar>" 
        by auto
      also
      from hbx hby1 hpC hqC have "... <= x + y" by force
      finally
      show ?thesis .
    qed
  qed
qed

lemma abs_dif_fiX_bound_C_aux2:
assumes 
  hbx: "\<forall> l\<in>C. \<bar>f l - g l\<bar> <= x" and
  hby1: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= y" and
  hby2: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>g l - g m\<bar> <= y" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" and
  hrC: "r\<in>C" 
shows
  "y <= \<Delta> \<longrightarrow> \<bar>fiX f p r - fiX g q r\<bar> <= x"
proof
  assume hyd: "y<=\<Delta>"
  show "\<bar>fiX f p r - fiX g q r\<bar> <= x" 
  proof-
    from hpC and hrC and hby1 and hyd have "\<bar>f p - f r\<bar> \<le> \<Delta>" 
      by force
    moreover
    from hqC and hrC and hby2 and hyd have "\<bar>g q - g r\<bar> \<le> \<Delta>"
      by force
    moreover
    from hrC and hbx have "\<bar> f r - g r \<bar> <= x " by auto
    ultimately
    show ?thesis 
      by (auto simp add: fiX_def)
  qed
qed

lemma abs_dif_fiX_bound_C:
assumes 
  hbx: "\<forall> l\<in>C. \<bar>f l - g l\<bar> <= x" and
  hby1: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= y" and
  hby2: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>g l - g m\<bar> <= y" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" and
  hrC: "r\<in>C" 
shows
  "\<bar>fiX f p r - fiX g q r\<bar> <= 
                     x + (if (y <= \<Delta>) then 0 else y)"
proof (cases "y <= \<Delta>")
  case True 
  with abs_dif_fiX_bound_C_aux2 and
    hbx and hby1 and hby2 and hpC and hqC and hrC 
  have "\<bar>fiX f p r - fiX g q r\<bar> <= x " by blast
  with True show "?thesis" by simp
next
  case False
  with abs_dif_fiX_bound_C_aux1 and
    hbx and hby1 and hby2 and hpC and hqC and hrC 
  have "\<bar>fiX f p r - fiX g q r\<bar> <= x + y" by blast
  with False show "?thesis" by simp
qed

subsubsection \<open>Main theorem\<close>

theorem prec_enh:
assumes 
  hC: "C \<subseteq> PR" and
  hbx: "\<forall> l\<in>C. \<bar>f l - g l\<bar> <= x" and
  hby1: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= y" and
  hby2: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>g l - g m\<bar> <= y" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" 
shows "\<bar> cfni p f - cfni q g \<bar> <= 
  (real (card C) * (x + (if (y <= \<Delta>) then 0 else y)) +
    real (card ({..<np} - C)) * (2 * \<Delta> + x + y)) / real np"
       (is "\<bar> ?dif_div_np \<bar> <= ?B")  
proof-
  have "\<bar>(\<Sum>l\<in>{..<np}. fiX f p l ) - 
                    (\<Sum>l\<in>{..<np}. fiX g q l)\<bar> = 
    \<bar>(\<Sum>l\<in>{..<np}. fiX f p l -fiX g q l)\<bar>"
    (is "\<bar>?dif\<bar> = \<bar>?dif'\<bar>" )
    by (simp add: sum_subtractf)
  also
  from abs_sum_np_ineq hC
  have " ... <=
      (\<Sum>l\<in>C. \<bar>fiX f p l - fiX g q l\<bar>) + 
      (\<Sum>l\<in>({..<np}-C). \<bar>fiX f p l - fiX g q l\<bar>)"
    (is " \<bar>?dif'\<bar> <= ?boundC' + ?boundnpC'" )
    by simp
  also
  have "... <= 
    real (card C) * (x + (if (y <= \<Delta>) then 0 else y))+
    real (card ({..<np}-C)) * (2 * \<Delta> + x + y)"
    (is " ... <= ?boundC + ?boundnpC" )
  proof-
    have " ?boundC' <= ?boundC"
    proof -
      from abs_dif_fiX_bound_C and 
        hbx and hby1 and hby2 and  hpC and hqC  
      have "\<forall>r\<in>C. 
        \<bar>fiX f p r - fiX g q r\<bar> <= x + 
                         (if (y <= \<Delta>) then 0 else y)"
        by blast     
      thus ?thesis using sum_le[where S=C] and finitC[OF hC] 
        by force
    qed
    moreover
    have "?boundnpC' <= ?boundnpC"
    proof -
      from abs_dif_fiX_bound and 
        hbx and hby1 and  hpC and hqC  
      have "\<forall>r\<in>({..<np}-C). \<bar>fiX f p r - fiX g q r\<bar> <= 2 * \<Delta> + x + y"
        by blast
      with finitnpC
      show ?thesis
        by (auto intro: sum_le)
    qed
    ultimately
    show ?thesis by arith
  qed
  finally 
  have bound: "\<bar>?dif\<bar> <= ?boundC + ?boundnpC" .
  thus ?thesis
  proof-
    have "?dif_div_np = ?dif / real np"
      by (simp add: cfni_def divide_inverse algebra_simps)
    hence "\<bar> cfni p f - cfni q g \<bar> = \<bar>?dif\<bar> / real np"
      by force
    with bound show "?thesis" 
      by (auto simp add: cfni_def divide_inverse constants_ax)
  qed
qed

subsection \<open>Accuracy Preservation property\<close>

text \<open>First, a simple lemma about an arithmetic propertie of the
generalized summation over a set constructor.\<close>

lemma sum_div_card:
"(\<Sum>l\<in>{..<n::nat}. f l) + q * real n= 
  (\<Sum>l\<in>{..<n}. f l + q )"
  (is "?Sl n = ?Sr n")
proof (induct n)
case 0 thus ?case by simp
next
case (Suc n)
thus ?case
  by (auto simp: of_nat_Suc distrib_left lessThan_Suc) 
qed

text \<open>Next, some lemmas about bounds that are used in the proof of Accuracy Preservation\<close>

lemma bound_aux_C:
assumes
  hby: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= x" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" and
  hrC: "r\<in>C" 
shows
  "\<bar>fiX f p r - f q\<bar> <= x"
proof (cases "\<bar> f p - f r \<bar> <= \<Delta>")
  case True
  then have "\<bar>fiX f p r - f q\<bar> = \<bar> f r - f q \<bar>" 
    by (simp add: fiX_def)
  also
  from hby hqC hrC have "... <= x" by blast
  finally 
  show ?thesis .
next
  case False
  then have "\<bar>fiX f p r - f q\<bar> = \<bar> f p - f q \<bar>" 
    by (simp add: fiX_def)
  also
  from hby hpC hqC have "... <= x" by blast
  finally 
  show ?thesis .
qed

lemma bound_aux:
assumes
  hby: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= x" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" 
shows
  "\<bar>fiX f p r - f q\<bar> <= x + \<Delta>"
proof (cases "\<bar> f p - f r \<bar> <= \<Delta>")
  case True
  then have "\<bar>fiX f p r - f q\<bar> = \<bar> f r - f q \<bar>" 
    by (simp add: fiX_def)
  also
  have "... = \<bar> (f r - f p) + (f p - f q) \<bar>" 
    by arith
  also
  have "... <= \<bar> f p - f r \<bar> + \<bar> f p - f q \<bar>" 
    by arith
  also
  from True have "... <= \<Delta> + \<bar> f p - f q \<bar>" by arith
  also
  from hby hpC hqC have "... <= \<Delta> + x" by simp
  finally 
  show ?thesis by simp
next
  case False
  then have "\<bar>fiX f p r - f q\<bar> = \<bar> f p - f q \<bar>" 
    by (simp add: fiX_def)
  also
  from hby hpC hqC have "... <= x" by blast
  finally 
  show ?thesis using constants_ax by arith
qed

subsubsection \<open>Main theorem\<close>

lemma accur_pres:
assumes 
  hC: "C \<subseteq> PR" and
  hby: "\<forall> l\<in>C. \<forall> m\<in>C. \<bar>f l - f m\<bar> <= x" and
  hpC: "p\<in>C" and
  hqC: "q\<in>C" 
shows "\<bar> cfni p f - f q \<bar> <= 
  (real (card C) * x + real (card ({..<np} - C)) * (x + \<Delta>))/
                  real np"
  (is "?abs1 <= (?bC + ?bnpC)/real np")
proof-
from abs_sum_np_ineq and hC have 
  "\<bar>\<Sum>l\<in>{..<np}. fiX f p l  - f q \<bar> <= 
    (\<Sum>l\<in>C. \<bar> fiX f p l  - f q \<bar>) + 
            (\<Sum>l\<in>({..<np}-C). \<bar> fiX f p l  - f q \<bar>)" 
  by simp
also 
have 
  "... <= real (card C) * x + 
            real (card ({..<np} - C)) * (x + \<Delta>)"
  proof-
    have "(\<Sum>l\<in>C. \<bar> fiX f p l  - f q \<bar>) <= 
                    real (card C) * x"
    proof-
      from bound_aux_C and 
        hby and  hpC and hqC  
      have "\<forall>r\<in>C. 
        \<bar>fiX f p r - f q\<bar> <= x"
        by blast     
      thus ?thesis using sum_le[where S=C] and finitC[OF hC] 
        by force
    qed
    moreover
    have " (\<Sum>l\<in>({..<np}-C). \<bar> fiX f p l  - f q \<bar>) <= 
                real (card ({..<np} - C)) * (x + \<Delta>)"
    proof -
      from bound_aux and 
        hby and  hpC and hqC  
      have "\<forall>r\<in>({..<np}-C). 
        \<bar>fiX f p r - f q\<bar> <= x + \<Delta>"
        by blast
      thus ?thesis using sum_le[where S="{..<np}-C"] 
        and finitnpC 
        by force
    qed
    ultimately
    show ?thesis by arith
  qed
  finally 
  have bound: "\<bar>\<Sum>l\<in>{..<np}. fiX f p l - f q\<bar>
  \<le> real (card C) * x + real (card ({..<np} - C)) * (x + \<Delta>)"
    .
  thus 
    ?thesis
  proof-
    from constants_ax have
      res: "inverse (real np) * real np = 1" 
      by auto
    have
      "(cfni p f - f q) * real np = 
      (\<Sum>l\<in>{..<np}. fiX f p l) * real np / real np - f q * real np"
      by (simp add: cfni_def algebra_simps)
    also 
    have "... = 
      (\<Sum>l\<in>{..<np}. fiX f p l) - f q * real np"
      by simp
    also
    from sum_div_card[where f="fiX f p" and n=np and q="- f q"]
    have "... = (\<Sum>l\<in>{..<np}. fiX f p l - f q)"
      by simp
    finally
    have 
      "(cfni p f - f q) * real np = (\<Sum>l\<in>{..<np}. fiX f p l - f q)"
      .
\<comment> \<open>cambia\<close>
    hence
      "(cfni p f - f q) * real np / real np = 
      (\<Sum>l\<in>{..<np}. fiX f p l - f q)/ real np"
      by auto
    with constants_ax have  
      "(cfni p f - f q) = 
      (\<Sum>l\<in>{..<np}. fiX f p l - f q) / real np"
    by simp
    hence "\<bar> cfni p f - f q \<bar> = 
      \<bar>(\<Sum>l\<in>{..<np}. fiX f p l - f q) / real np \<bar>"
      by simp
    also have
      "... = \<bar>(\<Sum>l\<in>{..<np}. fiX f p l - f q)\<bar> / real np "
      by auto
    finally have "\<bar> cfni p f - f q \<bar> = 
      \<bar>(\<Sum>l\<in>{..<np}. fiX f p l - f q)\<bar> / real np "
      .
    with bound show "?thesis" 
      by (auto simp add: cfni_def divide_inverse constants_ax)
  qed
qed

end
