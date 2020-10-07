section \<open>Real-Valued random variables \label{sec:realrandvar}\<close>

theory RealRandVar
imports Measure "HOL-Library.Countable"
begin

text \<open>While most of the above material was modeled after Hurd's work
  (but still proved independently),
  the original content basically starts here\footnote{There are two
  main reasons why the above has not been imported using Sebastian
Skalberg's import tool \cite{Skalberg}. Firstly, there are
  inconveniences caused by different conventions in HOL, meaning
  predicates instead of sets foremost, that make the consistent use of
  such basic definitions impractical. What is more, the import tool
  simply was not available at the time these theories were
  written.}. From now
  on, we will specialize in functions that map into
  the real numbers and are measurable with respect to the canonical sigma
  algebra on the reals, the Borel sigma algebra. These functions will
  be called real-valued random variables. The terminology is slightly
  imprecise, as random variables hint at a probability space, which
  usually requires \<open>measure M UNIV = 1\<close>. Notwithstanding, as we regard
  only finite measures (cf. \ref{sec:measure-spaces}), this condition can
  easily be achieved by normalization. After all, the other standard
  name, ``measurable functions'', is even less precise.

  A lot of the theory in this and the preceding section has also been
  formalized within the Mizar project \cite{mesfunc1,mesfunc2}. The
  abstract of the second source hints that it was also planned as a
  stepping stone for Lebesgue integration, though further results in
  this line could not be found. The main difference lies in the use of
  extended real numbers --- the reals together with \<open>\<plusminus>\<infinity>\<close> --- in
  those documents. It is established practice in measure theory
  to allow infinite values, but ``($\ldots$) we felt that the complications
  that this generated ($\ldots$) more than canceled out the gain in
  uniformity ($\ldots$), and that a simpler theory resulted from sticking to
  the standard real numbers.'' \cite[p.~32f]{hurd2002}. Hurd also advocates
  going directly to the hyper-reals, should the need for infinite
  measures arise. I agree, nevertheless sticking to his example for the reasons
  mentioned in the prologue.\<close>
  
(*First of all, for the definition of a real valued random variable,
we need the Borel-\<sigma>-Algebra on the Reals*)
(*The smallest \<sigma>-Algebra containing {..u} for all rational u is
  sufficient, but we use all real u for simplicity!*)

definition
  Borelsets:: "real set set" ("\<bool>") where
  "\<bool> = sigma {S. \<exists>u. S={..u}}"

definition
(*We use Joe Hurd's formalism of a measure space (which assumes that 
  the universe is always the whole type universe)*)
  rv:: "('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> ('a \<Rightarrow> real) set" where
  "rv M = {f. measure_space M \<and> f \<in> measurable (measurable_sets M) \<bool>}"

text \<open>As explained in the first paragraph, the preceding
  definitions\footnote{The notation $\<open>{..u}\<close>$ signifies the
  interval from negative infinity to $u$ included.}
  determine the rest of this section. There are many ways to define
  the Borel sets. For example, taking into account only rationals for
  $u$ would also have worked out above, but we can take the reals to
  simplify things. The smallest sigma algebra containing all the open
  (or closed) sets is another alternative; the multitude of
  possibilities testifies to the relevance of the concept.  

  The latter path leads the way to the fact that any continuous function is
  measurable. Generalization for $\<open>\<real>\<close>^n$ brings another unified way to
  prove all the measurability theorems in this theory plus, for instance,
  measurability of the trigonometric and exponential functions. This approach is detailed in another influential textbook
  by Billingsley \cite{Billingsley86}. It requires some concepts of
  topologic spaces, which made the following elementary
  course, based on Bauer's excellent book \cite{Bauer}, seem more feasible.
   
  Two more definitions go next. The image measure, law, or
  distribution --- the last term being specific to probability --- of a  
  measure with respect to a measurable function is calculated as the measure of the
  inverse image of a set. Characteristic functions will
  be frequently needed in the rest of the development. 
\<close>
(*Perhaps one day we will need distributions, this might be the right
time to define them*)

definition
  distribution:: 
  "('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> (real set \<Rightarrow> real)" ("law") where
  "f \<in> rv M \<Longrightarrow> law M f \<equiv> (measure M) \<circ> (vimage f)"

definition
  characteristic_function:: "'a set \<Rightarrow> ('a \<Rightarrow> real)" ("\<chi> _"(*<*)[1000](*>*)) where
  "\<chi> A x \<equiv> if x \<in> A then 1 else 0" 

lemma char_empty: "\<chi> {} = (\<lambda>t. 0)"
proof (rule ext)
  fix t
  show "\<chi> {} t = 0" by (simp add: characteristic_function_def)
qed

text \<open>Now that random variables are defined, we aim to show that a
  broad class of functions belongs to them. For a constant function
  this is easy, as there are only two possible preimages.\<close>
  (*measurability lemmata*)

lemma assumes sigma: "sigma_algebra S"
  shows const_measurable: "(\<lambda>x. (c::real)) \<in> measurable S X"
proof (unfold measurable_def, rule, rule)
  fix g
  show "(\<lambda>x. c) -` g \<in> S"
  proof (cases "c \<in> g")
    case True 
    hence "(\<lambda>x::'a. c) -` g = UNIV" 
      by blast
    moreover from sigma have "UNIV \<in> S" 
      by (rule sigma_algebra_UNIV)
    ultimately show ?thesis by simp
  next
    case False
    hence "(\<lambda>x::'a. c) -` g = {}" 
      by blast
    moreover from sigma have "{} \<in> S" 
      by (simp only: sigma_algebra_def)
    ultimately show ?thesis by simp
    txt\<open>\nopagebreak\<close>   
  qed                     
qed                       

theorem assumes ms: "measure_space M"
  shows const_rv: "(\<lambda>x. c) \<in> rv M" using ms
  by (auto simp only: measure_space_def const_measurable rv_def)

text\<open>Characteristic functions produce four cases already, so the
  details are glossed over.\<close>

lemma assumes a: "a \<in> S" and sigma: "sigma_algebra S" shows 
char_measurable : "\<chi> a \<in> measurable S x"
(*<*)proof -
  {fix g
    have "\<chi> a -` g \<in> S"
    proof (cases "1 \<in> g")
      case True
      show ?thesis
      proof (cases "0 \<in> g") 
        case True
        with \<open>1 \<in> g\<close> have "\<chi> a -` g = UNIV" by (auto simp add: vimage_def characteristic_function_def)
        with sigma show ?thesis by (auto simp add: sigma_algebra_UNIV) 
      next
        case False 
        with \<open>1 \<in> g\<close> have "\<chi> a -` g = a" 
          by (auto simp add: vimage_def characteristic_function_def)
        with a show ?thesis by simp
      qed
      
    next
      case False
      show ?thesis
      proof (cases "0 \<in> g")
        case True
        with \<open>1 \<notin> g\<close> have "\<chi> a -` g = -a" 
          by (auto simp add: vimage_def characteristic_function_def)
        with a sigma show ?thesis by (simp add: sigma_algebra_def)
      next
        case False
        with \<open>1 \<notin> g\<close> have "\<chi> a -` g = {}" by (auto simp add: vimage_def characteristic_function_def)
        moreover from sigma have "{} \<in> S" by  (simp only: sigma_algebra_def)
        ultimately show ?thesis by simp
      qed
    qed}
  thus ?thesis by (unfold measurable_def) blast
qed(*>*)


theorem assumes ms: "measure_space M" and A: "A \<in> measurable_sets M"
  shows char_rv: "\<chi> A \<in> rv M" using ms A
  by (auto simp only: measure_space_def char_measurable rv_def)  

text \<open>For more intricate functions, the following application of the
  measurability lifting theorem from \ref{sec:measure-spaces} gives a
  useful characterization.\<close>

theorem assumes ms: "measure_space M" shows 
  rv_le_iff: "(f \<in> rv M) = (\<forall>a. {w. f w \<le> a} \<in> measurable_sets M)"
proof - 
  
  have "f \<in> rv M \<Longrightarrow> \<forall>a. {w. f w \<le> a} \<in> measurable_sets M"
  proof 
    { fix a 
      assume "f \<in> measurable (measurable_sets M) \<bool>"
      hence "\<forall>b\<in>\<bool>. f -` b \<in> measurable_sets M"
        by (unfold measurable_def) blast
      also have "{..a} \<in> \<bool>" 
        by (simp only: Borelsets_def) (rule sigma.basic, blast)
      ultimately have "{w. f w \<le> a} \<in> measurable_sets M" 
        by (auto simp add: vimage_def) 
    }
    thus "\<And>a. f \<in> rv M \<Longrightarrow> {w. f w \<le> a} \<in> measurable_sets M" 
      by (simp add: rv_def)
  qed
  
  also have "\<forall>a. {w. f w \<le> a} \<in> measurable_sets M \<Longrightarrow> f \<in> rv M"
  proof -
    assume "\<forall>a. {w. f w \<le> a} \<in> measurable_sets M"
    hence "f \<in> measurable (measurable_sets M){S. \<exists>u. S={..u}}" 
      by (auto simp add: measurable_def vimage_def)
    with ms have "f \<in> measurable (measurable_sets M) \<bool>" 
      by (simp only: Borelsets_def measure_space_def measurable_lift)
    with ms show ?thesis 
      by (auto simp add: rv_def)
   txt\<open>\nopagebreak\<close>                            
  qed
  ultimately show ?thesis by rule 
qed 

 
text \<open>The next four lemmata allow for a ring deduction that helps establish
  this fact for all of the signs \<open><\<close>, \<open>>\<close> and \<open>\<ge>\<close> as well.\<close>

lemma assumes sigma: "sigma_algebra A" and le: "\<forall>a. {w. f w \<le> a} \<in> A" 
  shows le_less: "\<forall>a. {w. f w < (a::real)} \<in> A"
proof 
  fix a::real
  from le sigma have "(\<Union>n::nat. {w. f w \<le> a - inverse (real (Suc n))}) \<in> A" 
    by (simp add: sigma_algebra_def) 
  also
  have "(\<Union>n::nat. {w. f w \<le> a - inverse (real (Suc n))}) = {w. f w < a}" 
  proof -
    {
      fix w n 
      have "0 < inverse (real (Suc (n::nat)))" 
        by simp                                
      hence "f w \<le> a - inverse (real (Suc n)) \<Longrightarrow> f w < a" 
        by arith                                           
    }
    also
    { fix w
      have "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow> 0" 
        by (rule LIMSEQ_inverse_real_of_nat)

      also assume "f w < a"
      hence "0 < a - f w" by simp
     
      ultimately have 
        "\<exists>n0. \<forall>n. n0 \<le> n \<longrightarrow> abs (inverse (real (Suc n))) < a - f w" 
        by (auto simp add: lim_sequentially dist_real_def) 
      then obtain n where  "abs (inverse (real (Suc n))) < a - f w" 
        by blast
      hence "f w \<le> a - inverse (real (Suc n))" 
        by arith
      hence "\<exists>n. f w \<le> a - inverse (real (Suc n))" ..
    }
    ultimately show ?thesis by auto
  qed
  finally show "{w. f w < a} \<in> A" .
qed

lemma assumes sigma: "sigma_algebra A" and less: "\<forall>a. {w. f w < a} \<in> A" 
  shows less_ge: "\<forall>a. {w. (a::real) \<le> f w} \<in> A"  
proof 
  fix a::real
  from less sigma have "-{w. f w < a} \<in> A" 
    by (simp add: sigma_algebra_def)
  also
  have "-{w. f w < a} = {w. a \<le> f w}" 
    by auto 
  
  finally show "{w. a \<le> f w} \<in> A" .
qed

lemma assumes sigma: "sigma_algebra A" and ge: "\<forall>a. {w. a \<le> f w} \<in> A" 
  shows ge_gr: "\<forall>a. {w. (a::real) < f w} \<in> A"
(*<*)proof 
  fix a::real
  from ge sigma have "(\<Union>n::nat. {w. a + inverse (real (Suc n)) \<le> f w}) \<in> A" 
    by (simp add: sigma_algebra_def) 
  also
  have "(\<Union>n::nat. {w. a + inverse (real (Suc n)) \<le> f w}) = {w. a < f w}" 
  proof -
    {
      fix w n 
      have "0 < inverse (real (Suc (n::nat)))" by simp
      hence "a + inverse (real (Suc n)) \<le> f w \<Longrightarrow> a < f w" by arith
    }
    also
    { fix w
      have "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow> 0" by (rule LIMSEQ_inverse_real_of_nat)
      
      also assume "a < f w"
      hence "0 < f w - a" by simp

      ultimately have "\<exists>n0. \<forall>n. n0 \<le> n \<longrightarrow> abs (inverse (real (Suc n))) < f w - a" 
        by (auto simp add: lim_sequentially dist_real_def) 
      then obtain n where  "abs (inverse (real (Suc n))) < f w - a" by blast      
      hence "a + inverse (real (Suc n)) \<le> f w" by arith
      hence "\<exists>n. a + inverse (real (Suc n)) \<le> f w" ..
    }
    ultimately show ?thesis by auto
  qed
    
  finally show "{w. a < f w} \<in> A" .
qed(*>*)


lemma assumes sigma: "sigma_algebra A" and gr: "\<forall>a. {w. a < f w} \<in> A" 
  shows gr_le: "\<forall>a. {w. f w \<le> (a::real)} \<in> A"
(*<*)proof 
  fix a::real
  from gr sigma have "-{w. a < f w} \<in> A" by (simp add: sigma_algebra_def)
  also
  have "-{w. a < f w} = {w. f w \<le> a}" by auto 
  
  finally show "{w. f w \<le> a} \<in> A" .
qed(*>*)   

theorem assumes ms: "measure_space M" shows 
  rv_ge_iff: "(f \<in> rv M) = (\<forall>a. {w. a \<le> f w} \<in> measurable_sets M)"
proof -
  from ms have "(f \<in> rv M) = (\<forall>a. {w. f w \<le> a} \<in> measurable_sets M)" 
    by (rule rv_le_iff)
  also have "\<dots> = (\<forall>a. {w. a \<le> f w} \<in> measurable_sets M)" (is "?lhs = ?rhs")
  proof -
    from ms have sigma: "sigma_algebra (measurable_sets M)" 
      by (simp only: measure_space_def)
    also note less_ge le_less 
    ultimately have "?lhs \<Longrightarrow> ?rhs" by blast 
    also 
    from sigma gr_le ge_gr have "?rhs \<Longrightarrow> ?lhs" by blast
    ultimately 
    show ?thesis ..
  qed
  finally show ?thesis .
qed

theorem assumes ms: "measure_space M" shows 
  rv_gr_iff: "(f \<in> rv M) = (\<forall>a. {w. a < f w} \<in> measurable_sets M)"
(*<*)proof -
  from ms have "(f \<in> rv M) = (\<forall>a. {w.  a \<le> f w} \<in> measurable_sets M)" by (rule rv_ge_iff)
  also have "\<dots> = (\<forall>a. {w.  a < f w} \<in> measurable_sets M)" (is "?lhs = ?rhs")
  proof -
    from ms have sigma: "sigma_algebra (measurable_sets M)" by (simp only: measure_space_def)
    also note ge_gr ultimately have "?lhs \<Longrightarrow> ?rhs" by blast 
    also from sigma less_ge le_less gr_le have "?rhs \<Longrightarrow> ?lhs" by blast
    ultimately show ?thesis ..
  qed 
  finally show ?thesis .
qed(*>*)


theorem assumes ms: "measure_space M" shows 
  rv_less_iff: "(f \<in> rv M) = (\<forall>a. {w. f w < a} \<in> measurable_sets M)"
(*<*)proof -
  from ms have "(f \<in> rv M) = (\<forall>a. {w. a \<le> f w} \<in> measurable_sets M)" by (rule rv_ge_iff)
  also have "\<dots> = (\<forall>a. {w. f w < a} \<in> measurable_sets M)" (is "?lhs = ?rhs")
  proof -
    from ms have sigma: "sigma_algebra (measurable_sets M)" by (simp only: measure_space_def)
    also note le_less gr_le ge_gr ultimately have "?lhs \<Longrightarrow> ?rhs" by blast 
    also from sigma less_ge have "?rhs \<Longrightarrow> ?lhs" by blast
    ultimately show ?thesis ..
  qed 
  finally show ?thesis .
qed(*>*)


text \<open>As a first application we show that addition and multiplication
  with constants preserve measurability. This is a precursor to the
  more general addition and multiplication theorems later on. You can see that
  quite a few properties of the real numbers are employed.\<close>

lemma assumes g: "g \<in> rv M" 
  shows affine_rv: "(\<lambda>x. (a::real) + (g x) * b) \<in> rv M"
proof (cases "b=0")
  from g have ms: "measure_space M" 
    by (simp add: rv_def)
  case True
  hence "(\<lambda>x. a + (g x) * b) = (\<lambda>x. a)" 
    by simp
  also 
  from g have "(\<lambda>x. a) \<in> rv M" 
    by (simp add: const_measurable rv_def measure_space_def)
  ultimately show ?thesis by simp

next
  from g have ms: "measure_space M" 
    by (simp add: rv_def)
  case False
  have calc: "\<And>x c. (a + g x * b \<le> c) = (g x * b  \<le> c - a)" 
    by arith
  have "\<forall>c. {w.  a + g w * b \<le> c} \<in> measurable_sets M"
  proof (cases "b<0")    
    case False
    with \<open>b \<noteq> 0\<close> have "0<b" by arith
    hence "\<And>x c.  (g x * b  \<le> c - a) = (g x \<le> (c - a) / b)"  
      by (rule pos_le_divide_eq [THEN sym])
    with calc have "\<And>c. {w.  a + g w * b \<le> c} = {w. g w \<le> (c - a) / b}" 
      by simp
  
    also from ms g  have "\<forall>a. {w. g w \<le> a} \<in> measurable_sets M"  
      by (simp add: rv_le_iff)
    
    ultimately show ?thesis by simp
    
  next
    case True
    hence "\<And>x c. (g x * b \<le> c-a) = ((c-a)/b \<le> g x)"  
      by (rule neg_divide_le_eq [THEN sym])
    with calc have "\<And>c. {w.  a + g w * b \<le> c} = {w. (c-a)/b \<le> g w}" 
      by simp

    also from ms g have "\<forall>a. {w. a \<le> g w } \<in> measurable_sets M"  
      by (simp add: rv_ge_iff)
    
    ultimately show ?thesis by simp
  qed

  with ms show ?thesis 
    by (simp only: rv_le_iff [THEN sym])
qed
  
text \<open>For the general case of addition, we need one more set to be
  measurable, namely \<open>{w. f w \<le> g w}\<close>. This follows from a
  like statement for $<$. A dense and countable
  subset of the reals is needed to establish it. 

  Of course, the rationals come to
  mind. They were not available in Isabelle/HOL\footnote{At least not
  as a subset of the reals, to the definition of which a type of
  positive rational numbers contributed \cite{Fleuriot:2000:MNR}.}, so
  I built a theory with the necessary properties on my own. [Meanwhile
  Isabelle has proper rationals and SR's development of the rationals has been
  moved to and merged with Isabelle's rationals.\<close>

(*For this theorem, we need some properties of the rational numbers
(or any other dense and countable set in the reals - so why not use
the rationals?).*)


lemma assumes f: "f \<in> rv M" and g: "g \<in> rv M"
  shows rv_less_rv_measurable: "{w. f w < g w} \<in> measurable_sets M"
proof -
  let "?I i" = "let s::real = of_rat(nat_to_rat_surj i) in {w. f w < s} \<inter> {w. s < g w}"
  from g have ms: "measure_space M" by (simp add: rv_def)
  have "{w. f w < g w} = (\<Union>i. ?I i)"
  proof
    { fix w assume "w \<in> {w. f w < g w}"
      hence "f w < g w" ..
      hence "\<exists>s\<in>\<rat>. f w < s \<and> s < g w" by (rule Rats_dense_in_real)
      hence "\<exists>s\<in>\<rat>. w \<in> {w. f w < s} \<inter> {w. s < g w}" by simp
      hence "\<exists>i. w \<in> ?I i"
        by(simp add:Let_def)(metis surj_of_rat_nat_to_rat_surj)
      hence "w \<in> (\<Union>i. ?I i)" by simp
    }
    thus "{w. f w < g w} \<subseteq> (\<Union>i. ?I i)" ..
    
    show "(\<Union>i. ?I i) \<subseteq> {w. f w < g w}" by (force simp add: Let_def)
  qed
  moreover have "(\<Union>i. ?I i) \<in> measurable_sets M"
  proof -
    from ms have sig: "sigma_algebra (measurable_sets M)" 
      by (simp only: measure_space_def)    
    { fix s
      note sig
      also from ms f have "{w. f w < s} \<in> measurable_sets M" (is "?a\<in>?M") 
        by (simp add: rv_less_iff)
      moreover from ms g have "{w. s < g w} \<in> ?M" (is "?b \<in> ?M") 
        by (simp add: rv_gr_iff)
      ultimately have "?a \<inter> ?b \<in> ?M" by (rule sigma_algebra_inter)
    }
    hence "\<forall>i. ?I i \<in> measurable_sets M" by (simp add: Let_def)
    with sig show ?thesis by (auto simp only: sigma_algebra_def Let_def)
  qed
  ultimately show ?thesis by simp
qed

(*The preceding theorem took me about 1 month to establish through its deep dependencies*)
lemma assumes f: "f \<in> rv M" and g: "g \<in> rv M"
  shows rv_le_rv_measurable: "{w. f w \<le> g w} \<in> measurable_sets M" (is "?a \<in> ?M")
proof -
  from g have ms: "measure_space M" 
    by (simp add: rv_def)
  from g f have "{w. g w < f w} \<in> ?M" 
    by (rule rv_less_rv_measurable)
  also from ms have "sigma_algebra ?M" 
    by (simp only: measure_space_def)
  
  ultimately have "-{w. g w < f w} \<in> ?M" 
    by (simp only: sigma_algebra_def)
  also have "-{w. g w < f w} = ?a" 
    by auto
txt\<open>\nopagebreak\<close>  
  finally show ?thesis .
qed

lemma assumes f: "f \<in> rv M" and g: "g \<in> rv M" 
  shows f_eq_g_measurable: "{w. f w = g w} \<in> measurable_sets M" (*<*)(is "?a \<in> ?M")
proof -
  from g have ms: "measure_space M" by (simp add: rv_def)
  hence "sigma_algebra ?M" by (simp only: measure_space_def)
  also from f g ms have "{w. f w \<le> g w} \<in> ?M" and "{w. g w \<le> f w} \<in> ?M" 
    by (auto simp only: rv_le_rv_measurable)
  
  ultimately have "{w. f w \<le> g w} \<inter> {w. g w \<le> f w} \<in> ?M" (is "?b \<in> ?M") 
    by (rule sigma_algebra_inter)
  also have "?b = ?a" by auto
  
  finally show ?thesis .
qed(*>*)


lemma assumes f: "f \<in> rv M" and g: "g \<in> rv M" 
  shows f_noteq_g_measurable: "{w. f w \<noteq> g w} \<in> measurable_sets M" (*<*)(is "?a \<in> ?M")
proof -
  from g have ms: "measure_space M" by (simp add: rv_def)
  hence "sigma_algebra ?M" by (simp only: measure_space_def)
  also from f g have "{w. f w = g w} \<in> ?M" by (rule f_eq_g_measurable)
  
  ultimately have "-{w. f w = g w} \<in> ?M" by (simp only: sigma_algebra_def)
  also have "-{w. f w = g w} = ?a" by auto

  finally show ?thesis .
qed(*>*)

text \<open>With these tools, a short proof for the addition theorem is
  possible.\<close>

theorem assumes f: "f \<in> rv M" and g: "g \<in> rv M" 
  shows rv_plus_rv: "(\<lambda>w. f w + g w) \<in> rv M"
proof -
  from g have ms: "measure_space M" by (simp add: rv_def)
  { fix a 
    have "{w. a \<le> f w + g w} = {w. a + (g w)*(-1) \<le> f w}" 
      by auto
    moreover from g have "(\<lambda>w. a + (g w)*(-1)) \<in> rv M" 
      by (rule affine_rv) 
    with f have "{w. a + (g w)*(-1) \<le> f w} \<in> measurable_sets M"  
      by (simp add: rv_le_rv_measurable)
    ultimately have "{w. a \<le> f w + g w} \<in> measurable_sets M" by simp
  }
  with ms show ?thesis 
    by (simp add: rv_ge_iff)
  thm rv_ge_iff
qed

text \<open>To show preservation of measurability by multiplication, it is
  expressed by addition and squaring. This requires a few technical
  lemmata including the one stating measurability for squares, the proof of which is skipped.\<close>

(*This lemma should probably be in the RealPow Theory or a special Sqroot-Theory*)
lemma pow2_le_abs: "(a\<^sup>2 \<le> b\<^sup>2) = (\<bar>a\<bar> \<le> \<bar>b::real\<bar>)"
(*<*)proof -
  have "(a\<^sup>2 \<le> b\<^sup>2) = (\<bar>a\<bar>\<^sup>2 \<le> \<bar>b\<bar>\<^sup>2)" by (simp add: numeral_2_eq_2)
  also have "\<dots> = (\<bar>a\<bar> \<le> \<bar>b\<bar>)" 
  proof
    assume "\<bar>a\<bar> \<le> \<bar>b\<bar>"
    thus "\<bar>a\<bar>\<^sup>2 \<le> \<bar>b\<bar>\<^sup>2"
      by (rule power_mono) simp
  next
    assume "\<bar>a\<bar>\<^sup>2 \<le> \<bar>b\<bar>\<^sup>2" hence "\<bar>a\<bar>^(Suc 1) \<le> \<bar>b\<bar>^(Suc 1)" by (simp add: numeral_2_eq_2)
    moreover have "0 \<le> \<bar>b\<bar>" by auto
    ultimately show "\<bar>a\<bar> \<le> \<bar>b\<bar>" by (rule power_le_imp_le_base)
  qed
  finally show ?thesis .
qed(*>*)

lemma assumes f: "f \<in> rv M" 
  shows rv_square: "(\<lambda>w. (f w)\<^sup>2) \<in> rv M"
(*<*)proof -
  from f have ms: "measure_space M" by (simp add: rv_def)
  hence "?thesis = (\<forall>a. {w. (f w)\<^sup>2 \<le> a} \<in> measurable_sets M)" (is "_ = (\<forall>a. ?F a \<in> ?M)") by (rule rv_le_iff)
  also {
    fix a
    from ms have sig: "sigma_algebra ?M" by (simp only: measure_space_def)
    have "?F a \<in> ?M"
    proof (cases "a < 0")
      
      case True
      { fix w
        note True
        also have "0 \<le> (f w)\<^sup>2" by simp
        finally have "((f w)\<^sup>2 \<le> a) = False" by simp
      } hence "?F a = {}" by simp
      thus ?thesis using sig by (simp only: sigma_algebra_def)
      
    next
      case False
      show ?thesis
      proof (cases "a = 0")
        
        case True also
        { fix w
          have "0 \<le> (f w)\<^sup>2" by simp
          hence "((f w)\<^sup>2 \<le> 0) \<Longrightarrow> ((f w)\<^sup>2 = 0)" by (simp only: order_antisym)
          hence "((f w)\<^sup>2 \<le> 0) = ((f w)\<^sup>2 = 0)" by (force simp add: numeral_2_eq_2)
          also have "\<dots> = (f w = 0)" by simp     
          finally have "((f w)\<^sup>2 \<le> 0) = \<dots>" .
        }
        
        ultimately have "?F a = {w. f w = 0}" by simp
        moreover have "\<dots> = {w. f w \<le> 0} \<inter> {w. 0 \<le> f w}" by auto
        moreover have "\<dots> \<in> ?M"
        proof - 
          from ms f have "{w. f w \<le> 0} \<in> ?M" by (simp only: rv_le_iff)
          also from ms f have "{w. 0 \<le> f w} \<in> ?M" by (simp only: rv_ge_iff)
          ultimately show ?thesis using sig by (simp only: sigma_algebra_inter)
        qed
        
        ultimately show ?thesis by simp
   
      next
        case False
        with \<open>\<not> a < 0\<close> have "0<a" by (simp add: order_less_le)
        then have "\<exists> sqra. 0<sqra \<and> sqra\<^sup>2 = a" by (simp only: realpow_pos_nth2 numeral_2_eq_2)
        then have "\<And>w. \<exists> sqra. ?F a = {w. -sqra \<le> f w} \<inter> {w. f w \<le> sqra}"
          by (force simp only: pow2_le_abs abs_le_iff)
        then obtain sqra where "?F a = {w. -sqra \<le> f w} \<inter> {w. f w \<le> sqra}" by fast
        moreover have "\<dots> \<in> ?M" 
        proof - 
          from ms f have "{w. f w \<le> sqra} \<in> ?M" by (simp only: rv_le_iff)
          also from ms f have "{w. -sqra \<le> f w} \<in> ?M" by (simp only: rv_ge_iff)
          ultimately show ?thesis using sig by (simp only: sigma_algebra_inter)
        qed
        
        ultimately show ?thesis by simp
      
      qed 
    qed
  }
  
  ultimately show ?thesis by simp

qed(*>*)

lemma realpow_two_binomial_iff: "(f+g::real)\<^sup>2 = f\<^sup>2 + 2*(f*g) + g\<^sup>2"
  (*<*) 
  by (simp add: power2_eq_square distrib_right distrib_left)(*>*) 

lemma times_iff_sum_squares: "f*g = (f+g)\<^sup>2/4 - (f-g)\<^sup>2/(4::real)"
  by (simp add: power2_eq_square field_simps)

theorem assumes f: "f \<in> rv M" and g: "g \<in> rv M" 
  shows rv_times_rv: "(\<lambda>w. f w * g w) \<in> rv M" 
proof -
  have "(\<lambda>w. f w * g w) = (\<lambda>w. (f w + g w)\<^sup>2/4 - (f w - g w)\<^sup>2/4)" 
    by (simp only: times_iff_sum_squares)
  also have "\<dots> = (\<lambda>w. (f w + g w)\<^sup>2*inverse 4 - (f w + - g w)\<^sup>2*inverse 4)"  
    by simp
  also from f g have "\<dots> \<in> rv M" 
  proof -
    from f g have "(\<lambda>w. (f w + g w)\<^sup>2)  \<in> rv M" 
      by (simp add: rv_plus_rv rv_square)
    hence "(\<lambda>w. 0+(f w + g w)\<^sup>2*inverse 4) \<in> rv M" 
      by (rule affine_rv)
    also from g have "(\<lambda>w. 0 + (g w)*-1 ) \<in> rv M" 
      by (rule affine_rv)
    with f have "(\<lambda>w. (f w - g w)\<^sup>2)  \<in> rv M" 
      by (simp add: rv_plus_rv rv_square diff_conv_add_uminus del: add_uminus_conv_diff)
    hence "(\<lambda>w. 0+(f w - g w)\<^sup>2*-inverse 4) \<in> rv M" 
      by (rule affine_rv)
    ultimately show ?thesis 
      by (simp add: rv_plus_rv diff_conv_add_uminus del: add_uminus_conv_diff)
  qed txt\<open>\nopagebreak\<close>
  ultimately show ?thesis by simp
qed 
 
text\<open>The case of substraction is an easy consequence of \<open>rv_plus_rv\<close> and
  \<open>rv_times_rv\<close>.\<close>
 
theorem rv_minus_rv:
  assumes f: "f \<in> rv M" and g: "g \<in> rv M"
  shows "(\<lambda>t. f t - g t) \<in> rv M" 
(*<*)proof - 
  from f have ms: "measure_space M" by (simp add: rv_def)
  hence "(\<lambda>t. -1) \<in> rv M" by (simp add: const_rv)
  from this g have "(\<lambda>t. -1*g t) \<in> rv M" by (rule rv_times_rv)
  hence "(\<lambda>t. -g t) \<in> rv M" by simp
  with f have "(\<lambda>t. f t +-g t) \<in> rv M" by (rule rv_plus_rv)
  thus ?thesis by simp
qed(*>*)
text\<open>Measurability for limit functions of
    monotone convergent series is also surprisingly straightforward.\<close>

theorem assumes u: "\<And>n. u n \<in> rv M" and mon_conv: "u\<up>f"
  shows mon_conv_rv: "f \<in> rv M"
proof -
  from u have ms: "measure_space M" 
    by (simp add: rv_def)
  
  { 
    fix a 
    { 
      fix w
      from mon_conv have up: "(\<lambda>n. u n w)\<up>f w" 
        by (simp only: realfun_mon_conv_iff)
      { 
        fix i
        from up have "u i w \<le> f w" 
          by (rule real_mon_conv_le)
        also assume "f w \<le> a"
        finally have  "u i w \<le> a" . 
      }                              
                                     
      also 
      { assume "\<And>i. u i w \<le> a"
        also from up have "(\<lambda>n. u n w) \<longlonglongrightarrow> f w" 
          by (simp only: mon_conv_real_def)
        ultimately have "f w \<le> a" 
          by (simp add: LIMSEQ_le_const2)
      }
      ultimately have "(f w \<le> a) = (\<forall>i. u i w \<le> a)" by fast
    }
    hence "{w. f w \<le> a} = (\<Inter>i. {w. u i w \<le> a})" by fast
    moreover
    from ms u have "\<And>i. {w. u i w \<le> a} \<in> sigma(measurable_sets M)"
      by (simp add: rv_le_iff sigma.intros)
    hence "(\<Inter>i. {w. u i w \<le> a}) \<in> sigma(measurable_sets M)" 
      by (rule sigma_Inter)
    with ms have "(\<Inter>i. {w. u i w \<le> a}) \<in> measurable_sets M" 
      by (simp only: measure_space_def sigma_sigma_algebra)
    ultimately have "{w. f w \<le> a} \<in> measurable_sets M" by simp
  }
  with ms show ?thesis 
    by (simp add: rv_le_iff)
qed

text \<open>Before we end this chapter to start the formalization of the
  integral proper, there is one more concept missing: The
  positive and negative part of a function. Their definition is quite intuitive,
  and some useful properties are given right away, including the fact
  that they are random variables, provided that their argument
  functions are measurable.\<close>

definition
  nonnegative:: "('a \<Rightarrow> ('b::{ord,zero})) \<Rightarrow> bool" where
  "nonnegative f \<longleftrightarrow> (\<forall>x. 0 \<le> f x)"

definition
  positive_part:: "('a \<Rightarrow> ('b::{ord,zero})) \<Rightarrow> ('a \<Rightarrow> 'b)" ("pp") where
  "pp f x = (if 0\<le>f(x) then f x else 0)"

definition
  negative_part:: "('a \<Rightarrow> ('b::{ord,zero,uminus,minus})) \<Rightarrow> ('a \<Rightarrow> 'b)" ("np") where
  "np f x = (if 0\<le>f(x) then 0 else -f(x))"
  (*useful lemmata about positive and negative parts*)
lemma f_plus_minus: "((f x)::real) = pp f x - np f x" 
  by (simp add:positive_part_def negative_part_def)

lemma f_plus_minus2: "(f::'a \<Rightarrow> real) = (\<lambda>t. pp f t - np f t)"
  using f_plus_minus
  by (rule ext)

lemma f_abs_plus_minus: "(\<bar>f x\<bar>::real) = pp f x + np f x"
  by  (auto simp add:positive_part_def negative_part_def)

lemma nn_pp_np: assumes "nonnegative f"
  shows "pp f = f" and "np f = (\<lambda>t. 0)" using assms
  by (auto simp add: positive_part_def negative_part_def nonnegative_def ext)

lemma pos_pp_np_help: "\<And>x. 0\<le>f x \<Longrightarrow> pp f x = f x \<and> np f x = 0"
  by (simp add: positive_part_def negative_part_def)

lemma real_neg_pp_np_help: "\<And>x. f x \<le> (0::real) \<Longrightarrow> np f x = -f x \<and> pp f x = 0"
(*<*)proof -
  fix x
  assume le: "f x \<le> 0"
  hence "pp f x = 0 " 
    by (cases "f x < 0") (auto simp add: positive_part_def)
  also from le have "np f x = -f x"
    by (cases "f x < 0") (auto simp add: negative_part_def)
  ultimately show "np f x = -f x \<and> pp f x = 0" by fast
qed(*>*)

lemma real_neg_pp_np: assumes "f \<le> (\<lambda>t. (0::real))"
 shows "np f = (\<lambda>t. -f t)" and "pp f = (\<lambda>t. 0)" using assms
  by (auto simp add: real_neg_pp_np_help ext le_fun_def)

lemma assumes a: "0\<le>(a::real)" 
  shows real_pp_np_pos_times: 
  "pp (\<lambda>t. a*f t) = (\<lambda>t. a*pp f t) \<and>  np (\<lambda>t. a*f t) = (\<lambda>t. a*np f t)"
(*<*)proof -
  { fix t
    have "pp (\<lambda>t. a*f t) t = a*pp f t \<and> np (\<lambda>t. a*f t) t = a*np f t"
    proof (cases "0 \<le> f t")
      case True
      from a this a order_refl[of 0] have le: "0*0\<le>a*f t" 
        by (rule mult_mono)
      hence "pp (\<lambda>t. a*f t) t = a*f t" by (simp add: positive_part_def)
      also from True have "\<dots> = a*pp f t" by (simp add: positive_part_def)
      finally have 1: "pp (\<lambda>t. a*f t) t = a*pp f t" .
      
      from le have "np (\<lambda>t. a*f t) t = 0" by (simp add: negative_part_def)
      also from True have "\<dots> = a*np f t" by (simp add: negative_part_def)
      finally show ?thesis using 1 by fast
    next
      case False
      hence "f t \<le> 0" by simp
      from this a have "(f t)*a \<le> 0*a" by (rule mult_right_mono)
      hence le: "a*f t \<le> 0" by (simp add: mult.commute)
      hence "pp (\<lambda>t. a*f t) t = 0" 
        by (cases "a*f t<0") (auto simp add: positive_part_def order_le_less ) 
      also from False have "\<dots> = a*pp f t" by (simp add: positive_part_def)
      finally have 1: "pp (\<lambda>t. a*f t) t = a*pp f t" .
      
      from le have "np (\<lambda>t. a*f t) t = -a*f t" 
        by (cases "a*f t=0") (auto simp add: negative_part_def order_le_less)
      also from False have "\<dots> = a*np f t" by (simp add: negative_part_def)
      finally show ?thesis using 1 by fast
    qed
  } thus ?thesis by (simp add: ext)
qed(*>*)

lemma assumes a: "(a::real)\<le>0" 
  shows real_pp_np_neg_times: 
  "pp (\<lambda>t. a*f t) = (\<lambda>t. -a*np f t) \<and>  np (\<lambda>t. a*f t) = (\<lambda>t. -a*pp f t)"
(*<*)proof -
  { fix t
    have "pp (\<lambda>t. a*f t) t = -a*np f t \<and> np (\<lambda>t. a*f t) t = -a*pp f t"
    proof (cases "0 \<le> f t")
      case True 
      with a have le: "a*f t\<le>0*f t" 
        by (rule mult_right_mono)
      hence "pp (\<lambda>t. a*f t) t = 0" by (simp add: real_neg_pp_np_help)
      also from True have "\<dots> = -a*np f t" by (simp add: negative_part_def)
      finally have 1: "pp (\<lambda>t. a*f t) t = -a*np f t" .
      
      from le have "np (\<lambda>t. a*f t) t = -a*f t" by (simp add: real_neg_pp_np_help)
      also from True have "\<dots> = -a*pp f t" by (simp add: positive_part_def)
      finally show ?thesis using 1 by fast
    next
      case False
      hence "f t \<le> 0" by simp 
      with a have le: "0\<le>a*(f t)" by (simp add: zero_le_mult_iff)
      hence "pp (\<lambda>t. a*f t) t = a*f t" by (simp add: positive_part_def) 
      also from False have "\<dots> = -a*np f t" by (simp add: negative_part_def)
      finally have 1: "pp (\<lambda>t. a*f t) t = -a*np f t" .
      
      from le have "np (\<lambda>t. a*f t) t = 0" by (simp add: negative_part_def)
      also from False have "\<dots> = -a*pp f t" by (simp add: positive_part_def)
      finally show ?thesis using 1 by fast
    qed
  } thus ?thesis by (simp add: ext)
qed(*>*)


lemma pp_np_rv:
  assumes f: "f \<in> rv M" 
  shows "pp f \<in> rv M" and "np f \<in> rv M"
proof -
  from f have ms: "measure_space M" by (simp add: rv_def)
  
  { fix a
    from ms f have fm: "{w. f w \<le> a} \<in> measurable_sets M" 
      by (simp add: rv_le_iff)
    have 
      "{w. pp f w \<le> a} \<in> measurable_sets M \<and> 
      {w. np f w \<le> a} \<in> measurable_sets M"
    proof (cases "0\<le>a")
      case True
      hence "{w. pp f w \<le> a} = {w. f w \<le> a}" 
        by (auto simp add: positive_part_def)
      moreover note fm moreover
      from True have "{w. np f w \<le> a} = {w. -a \<le> f w}" 
        by (auto simp add: negative_part_def)
      moreover from ms f have "\<dots> \<in> measurable_sets M" 
        by (simp add: rv_ge_iff)
      ultimately show ?thesis by simp
    next
      case False
      hence "{w. pp f w \<le> a} = {}" 
        by (auto simp add: positive_part_def)
      also from False have "{w. np f w \<le> a} = {}" 
        by (auto simp add: negative_part_def)
      moreover from ms have "{} \<in> measurable_sets M" 
        by (simp add: measure_space_def sigma_algebra_def)
      ultimately show ?thesis by simp
    qed
  } with ms show "pp f \<in> rv M" and "np f \<in> rv M" 
    by (auto simp add: rv_le_iff)
qed


theorem pp_np_rv_iff: "(f::'a \<Rightarrow> real) \<in> rv M = (pp f \<in> rv M \<and> np f \<in> rv M)"
(*<*)proof -
  { assume "pp f \<in> rv M" and "np f \<in> rv M" 
    hence "(\<lambda>t. pp f t - np f t) \<in> rv M" by (rule rv_minus_rv)
    also have "f = (\<lambda>t. pp f t - np f t)" by (rule f_plus_minus2)
    ultimately have "f \<in> rv M" by simp
  } also
  have "f \<in> rv M \<Longrightarrow> (pp f \<in> rv M \<and> np f \<in> rv M)" by (simp add: pp_np_rv)
  ultimately show ?thesis by fast
qed(*>*)


text\<open>This completes the chapter about measurable functions. As we
  will see in the next one, measurability is the prime condition on
  Lebesgue integrable functions; and the theorems and lemmata
  established here suffice --- at least in principle --- to show it holds for any
  function that is to be integrated there.\<close>

end
