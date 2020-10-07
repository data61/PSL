theory "Frechet_Correctness"
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Lib"
  "Syntax"
  "Denotational_Semantics"
  "Ids"
begin
context ids begin
section \<open>Characterization of Term Derivatives\<close>
text \<open>
 This section builds up to a proof that in well-formed interpretations, all
 terms have derivatives, and those derivatives agree with the expected rules
 of derivatives. In particular, we show the [frechet] function given in the
 denotational semantics is the true Frechet derivative of a term. From this
 theorem we can recover all the standard derivative identities as corollaries.
\<close>

lemma inner_prod_eq:
  fixes i::"'a::finite"
  shows "(\<lambda>(v::'a Rvec). v \<bullet> axis i 1) = (\<lambda>(v::'a Rvec). v $ i)"
  unfolding cart_eq_inner_axis axis_def by (simp add: eq_commute)

theorem svar_deriv:
  fixes x:: "'sv::finite" and \<nu>:: "'sv Rvec" and F::"real filter"
  shows "((\<lambda>v. v $ x) has_derivative (\<lambda>v'. v' \<bullet> (\<chi> i. if i = x then 1 else 0))) (at \<nu>)"
proof -
  let ?f = "(\<lambda>v. v)"
  let ?f' = "(\<lambda>v'. v')"
  let ?g = "(\<lambda>v. axis x 1)"
  let ?g' = "(\<lambda>v. 0)"
  have id_deriv: "(?f has_derivative ?f') (at \<nu>) "
    by (rule has_derivative_ident)
  have const_deriv: "(?g has_derivative ?g') (at \<nu>)"
    by (rule has_derivative_const)
  have inner_deriv:"((\<lambda>x. inner (?f x) (?g x)) has_derivative
                     (\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>))) (at \<nu>)"
    by (intro has_derivative_inner [OF id_deriv const_deriv])
  from inner_prod_eq
  have left_eq: "(\<lambda>x. inner (?f x) (?g x)) = (\<lambda>v. vec_nth v x)"
    by (auto)
  from inner_deriv and inner_prod_eq
  have better_deriv:"((\<lambda>v. vec_nth v x) has_derivative
                     (\<lambda>h. inner (?f \<nu>) (?g' h) + inner (?f' h) (?g \<nu>))) (at \<nu>)"
    by (metis (no_types, lifting) UNIV_I has_derivative_transform)
  have vec_eq:"(\<chi> i. if i = x then 1 else 0) = (\<chi> i. if x = i then 1 else 0)"
    by(rule vec_extensionality, auto)
  have deriv_eq:"(\<lambda>h. \<nu> \<bullet> 0 + h \<bullet> axis x 1) = (\<lambda>v'. v' \<bullet> (\<chi> i. if i = x then 1 else 0))"
    by(rule ext, auto simp add: axis_def vec_eq)
  show ?thesis 
    apply(rule has_derivative_eq_rhs[where f'= "(\<lambda>h. \<nu> \<bullet> 0 + h \<bullet> axis x 1)"])
    using better_deriv deriv_eq  by auto
qed

lemma function_case_inner:
  assumes good_interp:
    "(\<forall>x i. (Functions I i has_derivative FunctionFrechet I i x) (at x))"
  assumes IH:"((\<lambda>v. \<chi> i. sterm_sem I (args i) v)
             has_derivative (\<lambda> v. (\<chi> i. frechet I (args i) \<nu> v))) (at \<nu>)"
  shows  "((\<lambda>v. Functions I f (\<chi> i. sterm_sem I (args i) v))
            has_derivative (\<lambda>v. frechet I ($f f args) \<nu> v)) (at \<nu>)"
proof -
  let ?h = "(\<lambda>v. Functions I f (\<chi> i. sterm_sem I (args i) v))"
  let ?h' = "frechet I ($f f args) \<nu>"
  let ?g = "(\<lambda>v. \<chi> i. sterm_sem I (args i) v)"
  let ?g' = "(\<lambda>v. \<chi> i. frechet I (args i) \<nu> v)"
  let ?f = "(\<lambda>y. Functions I f y)"
  let ?f' = "FunctionFrechet I f (?g \<nu>)"
  have hEqFG:  "?h  = ?f  o ?g" by (auto)
  have hEqFG': "?h' = ?f' o ?g'"
  proof -
    have frechet_def:"frechet I (Function f args) \<nu>
        = (\<lambda>v'. FunctionFrechet I f (?g \<nu>) (\<chi> i. frechet I (args i) \<nu> v'))"
      by (auto)
    have composition:
      "(\<lambda>v'. FunctionFrechet I f (?g \<nu>) (\<chi> i. frechet I (args i) \<nu> v'))
       = (FunctionFrechet I f (?g \<nu>)) o (\<lambda> v'. \<chi> i. frechet I (args i) \<nu> v')"
      by (auto)
    from frechet_def and composition show ?thesis by (auto)
  qed
  have fDeriv: "(?f has_derivative ?f') (at (?g \<nu>))"
    using good_interp is_interp_def by blast
  from IH have gDeriv: "(?g has_derivative ?g') (at \<nu>)" by (auto)
  from fDeriv and gDeriv
  have composeDeriv: "((?f o ?g) has_derivative (?f' o ?g')) (at \<nu>)"
    using diff_chain_at good_interp by blast
  from hEqFG hEqFG' composeDeriv show ?thesis by (auto)
qed

lemma func_lemma2:"(\<forall>x i. (Functions I i has_derivative (THE f'. \<forall>x. (Functions I i has_derivative f' x) (at x)) x) (at x) \<and>
          continuous_on UNIV (\<lambda>x. Blinfun ((THE f'. \<forall>x. (Functions I i has_derivative f' x) (at x)) x))) \<Longrightarrow>
    (\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow>
    ((\<lambda>v. Functions I f (vec_lambda(\<lambda>i. sterm_sem I (args i) v))) has_derivative (\<lambda>v'. (THE f'. \<forall>x. (Functions I f has_derivative f' x) (at x)) (\<chi> i. sterm_sem I (args i) \<nu>) (\<chi> i. frechet I (args i) \<nu> v'))) (at \<nu>)"
proof -
  assume a1: "\<forall>x i. (Functions I i has_derivative (THE f'. \<forall>x. (Functions I i has_derivative f' x) (at x)) x) (at x) \<and>
          continuous_on UNIV (\<lambda>x. Blinfun ((THE f'. \<forall>x. (Functions I i has_derivative f' x) (at x)) x))"
  then have a1':"\<forall>x i. (Functions I i has_derivative (THE f'. \<forall>x. (Functions I i has_derivative f' x) (at x)) x) (at x)" by auto
  assume a2: "\<And>\<theta>. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)"
  have "\<forall>f fa v. (\<exists>fb. \<not> (f (fb::'a) has_derivative fa fb (v::(real, 'a) vec)) (at v)) \<or> ((\<lambda>v. (\<chi> fa. (f fa v::real))) has_derivative (\<lambda>va. (\<chi> f. fa f v va))) (at v)"
    using has_derivative_vec by force
  then have "((\<lambda>v. \<chi> f. sterm_sem I (args f) v) has_derivative (\<lambda>v. \<chi> f. frechet I (args f) \<nu> v)) (at \<nu>)"
    by (auto simp add: a2 has_derivative_vec)
  then show "((\<lambda>v. Functions I f (vec_lambda(\<lambda>f. sterm_sem I (args f) v))) has_derivative (\<lambda>v'. (THE f'. \<forall>x. (Functions I f has_derivative f' x) (at x)) (\<chi> i. sterm_sem I (args i) \<nu>) (\<chi> i. frechet I (args i) \<nu> v'))) (at \<nu>)"
    using a1' function_case_inner by auto
qed

lemma func_lemma:
  "is_interp I \<Longrightarrow>
  (\<And>\<theta> :: ('a::finite, 'c::finite) trm. \<theta> \<in> range args \<Longrightarrow> (sterm_sem I \<theta> has_derivative frechet I \<theta> \<nu>) (at \<nu>)) \<Longrightarrow>
  (sterm_sem I ($f f args) has_derivative frechet I ($f f args) \<nu>) (at \<nu>)"
  apply(auto simp add: sfunction_case is_interp_def function_case_inner)
  apply(erule func_lemma2)
  apply(auto)  
  done

text \<open> The syntactic definition of term derivatives agrees with the semantic definition.
  Since the syntactic definition of derivative is total, this gives us that derivatives are "decidable" for
  terms (modulo computations on reals) and that they obey all the expected identities, which gives
  us the axioms we want for differential terms essentially for free.
 \<close>
lemma frechet_correctness:
  fixes I :: "('a::finite, 'b::finite, 'c::finite) interp" and \<nu>
  assumes good_interp: "is_interp I"
  shows "dfree \<theta> \<Longrightarrow> FDERIV (sterm_sem I \<theta>) \<nu> :> (frechet I \<theta> \<nu>)"
proof (induct rule: dfree.induct)
  case (dfree_Var i) then show ?case
    by (auto simp add: svar_case svar_deriv axis_def)
next
  case (dfree_Fun args i) with good_interp show ?case
    by (intro func_lemma) auto
qed auto

text \<open>If terms are semantically equivalent in all states, so are their derivatives\<close>
lemma sterm_determines_frechet:
  fixes I ::"('a1::finite, 'b1::finite, 'c::finite) interp"
    and J ::"('a2::finite, 'b2::finite, 'c::finite) interp"
    and \<theta>1 :: "('a1::finite, 'c::finite) trm"
    and \<theta>2 :: "('a2::finite, 'c::finite) trm"
    and \<nu> 
  assumes good_interp1:"is_interp I"
  assumes good_interp2:"is_interp J"
  assumes free1:"dfree \<theta>1"
  assumes free2:"dfree \<theta>2"
  assumes sem:"sterm_sem I \<theta>1 = sterm_sem J \<theta>2"
  shows "frechet I \<theta>1 (fst \<nu>) (snd \<nu>) = frechet J \<theta>2 (fst \<nu>) (snd \<nu>)"
proof -
  have d1:"(sterm_sem I \<theta>1 has_derivative (frechet I \<theta>1 (fst \<nu>))) (at (fst \<nu>))"
    using frechet_correctness[OF good_interp1 free1] by auto
  have d2:"(sterm_sem J \<theta>2 has_derivative (frechet J \<theta>2 (fst \<nu>))) (at (fst \<nu>))"
    using frechet_correctness[OF good_interp2 free2] by auto
  then have d1':"(sterm_sem I \<theta>1 has_derivative (frechet J \<theta>2 (fst \<nu>))) (at (fst \<nu>))"
    using sem by auto
  thus "?thesis" using has_derivative_unique d1 d1' by metis 
qed

lemma the_deriv:
  assumes deriv:"(f has_derivative F) (at x)"
  shows "(THE G. (f has_derivative G) (at x)) = F"
  apply(rule the_equality)
   subgoal by (rule deriv)
  subgoal for G by (auto simp add: deriv has_derivative_unique)
  done
   
lemma the_all_deriv:
  assumes deriv:"\<forall>x. (f has_derivative F x) (at x)"
  shows "(THE G. \<forall> x. (f has_derivative G x) (at x)) = F"
    apply(rule the_equality)
     subgoal by (rule deriv)
    subgoal for G 
      apply(rule ext)
      subgoal for x
        apply(erule allE[where x=x])
        by (auto simp add: deriv has_derivative_unique)
      done
    done
  
typedef ('a, 'c) strm = "{\<theta>:: ('a,'c) trm. dfree \<theta>}"
  morphisms raw_term simple_term
  by(rule exI[where x= "Const 0"], auto simp add: dfree_Const)
  
typedef ('a, 'b, 'c) good_interp = "{I::('a::finite,'b::finite,'c::finite) interp. is_interp I}"
  morphisms raw_interp good_interp
  apply(rule exI[where x="\<lparr> Functions = (\<lambda>f x. 0), Predicates = (\<lambda>p x. True), Contexts = (\<lambda>C S. S), Programs = (\<lambda>a. {}), ODEs = (\<lambda>c v. (\<chi> i. 0)), ODEBV = \<lambda>c. {}\<rparr>"])
  apply(auto simp add: is_interp_def)
proof -
  fix x ::real
  have eq:"(THE f'. \<forall>x. ((\<lambda>x. 0) has_derivative f' x) (at x)) = (\<lambda>_ _. 0)"
    by(rule the_all_deriv, auto)
  have eq':"(THE f'. \<forall>x. ((\<lambda>x. 0) has_derivative f' x) (at x)) x = (\<lambda>_. 0)"
    by (simp add: eq)
  have deriv:"((\<lambda>x.0) has_derivative (\<lambda>x. 0)) (at x)"
    by auto
  then show "\<And>x. ((\<lambda>x. 0) has_derivative (THE f'. \<forall>x. ((\<lambda>x. 0) has_derivative f' x) (at x)) x) (at x)" 
    by (auto simp add: eq eq' deriv)
next
  have eq:"(THE f'. \<forall>x. ((\<lambda>x. 0) has_derivative f' x) (at x)) = (\<lambda>_ _. 0)"
    by(rule the_all_deriv, auto)
  have eq':"\<forall>x. (THE f'. \<forall>x. ((\<lambda>x. 0) has_derivative f' x) (at x)) x = (\<lambda>_. 0)"
    by (simp add: eq)
  have deriv:"\<And>x. ((\<lambda>x.0) has_derivative (\<lambda>x. 0)) (at x)"
    by auto
  have blin:"\<And>x. bounded_linear ((THE f'. \<forall>x. ((\<lambda>x. 0) has_derivative f' x) (at x)) x)"
    by (simp add: eq')
  show " continuous_on UNIV (\<lambda>x. Blinfun ((THE f'. \<forall>x. ((\<lambda>x. 0) has_derivative f' x) (at x)) x))"
    apply(clarsimp simp add: continuous_on_topological[of UNIV "(\<lambda>x. Blinfun ((THE f'. \<forall>x. ((\<lambda>x. 0) has_derivative f' x) (at x)) x))"])
    apply(rule exI[where x = UNIV])
    by(auto simp add: eq' blin)
 qed

lemma frechet_linear: 
  assumes good_interp:"is_interp I"
  fixes v \<theta>
  shows " dfree \<theta> \<Longrightarrow> bounded_linear (frechet I \<theta> v)"
proof(induction rule: dfree.induct)
  case (dfree_Var i)
  then show ?case by(auto)
next
  case (dfree_Const r)
  then show ?case by auto
next
  case (dfree_Fun args i)
  have blin1:"\<And>x. bounded_linear(FunctionFrechet I i x)"
    using good_interp unfolding is_interp_def using has_derivative_bounded_linear
    by blast
  have blin2:"bounded_linear (\<lambda> a. (\<chi> i. frechet I (args i) v a))"
    using dfree_Fun.IH by(rule bounded_linear_vec)
  then show ?case
    using bounded_linear_compose[of "FunctionFrechet I i (\<chi> i. sterm_sem I (args i) v)" "(\<lambda>a. (\<chi> i. frechet I (args i) v a))", OF blin1 blin2]
    by auto
next
  case (dfree_Plus \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case 
    apply auto
    using bounded_linear_add by (blast)
next
  case (dfree_Times \<theta>\<^sub>1 \<theta>\<^sub>2)
  then show ?case
    by (auto simp add: bounded_linear_add bounded_linear_const_mult bounded_linear_mult_const)
qed

setup_lifting type_definition_good_interp

setup_lifting type_definition_strm

lift_definition blin_frechet::"('sf, 'sc, 'sz) good_interp \<Rightarrow> ('sf,'sz) strm \<Rightarrow> (real, 'sz) vec  \<Rightarrow> (real, 'sz) vec \<Rightarrow>\<^sub>L real" is "frechet"
  using frechet_linear by auto

lemmas [simp] = blin_frechet.rep_eq

lemma frechet_blin:"is_interp I \<Longrightarrow> dfree \<theta> \<Longrightarrow> (\<lambda>v. Blinfun (\<lambda>v'. frechet I \<theta> v v')) = blin_frechet (good_interp I) (simple_term \<theta>)"
  apply(rule ext)
  apply(rule blinfun_eqI)
  by (simp add: bounded_linear_Blinfun_apply frechet_linear good_interp_inverse simple_term_inverse)

lemma sterm_continuous:
  assumes good_interp:"is_interp I"
  shows "dfree \<theta> \<Longrightarrow> continuous_on UNIV (sterm_sem I \<theta>)"
proof(induction rule: dfree.induct)
  case (dfree_Fun args i)
  assume IH:"\<And>i. continuous_on UNIV (sterm_sem I (args i))"
  have con1:"continuous_on UNIV (Functions I i)"
    using good_interp unfolding is_interp_def
    using continuous_on_eq_continuous_within has_derivative_continuous by blast
  have con2:"continuous_on UNIV (\<lambda> x. (\<chi> i. sterm_sem I (args i) x))"
    apply(rule continuous_on_vec_lambda)
    using IH by auto
  have con:"continuous_on UNIV ((Functions I i) \<circ> (\<lambda>x.  (\<chi> i. sterm_sem I (args i) x)))"
    apply(rule continuous_on_compose)
     using con1 con2 apply auto
    using continuous_on_subset by blast
  show ?case 
    using con comp_def by(simp)
qed (auto intro: continuous_intros)

lemma sterm_continuous':
  assumes good_interp:"is_interp I"
  shows "dfree \<theta> \<Longrightarrow> continuous_on S (sterm_sem I \<theta>)"
  using sterm_continuous continuous_on_subset good_interp by blast

lemma frechet_continuous:
  fixes I :: "('sf, 'sc, 'sz) interp"
  assumes good_interp:"is_interp I"
  shows "dfree \<theta> \<Longrightarrow> continuous_on UNIV (blin_frechet (good_interp I) (simple_term \<theta>))"    
proof (induction rule: dfree.induct)
  case (dfree_Var i)
  have free:"dfree (Var i)" by (rule dfree_Var)
  have bounded_linear:"bounded_linear (\<lambda> \<nu>'. \<nu>' \<bullet> axis i 1)"
    by (auto simp add: bounded_linear_vec_nth)
  have cont:"continuous_on UNIV (\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. \<nu>' \<bullet> axis i 1))"
    using continuous_on_const by blast
  have eq:"\<And>\<nu> \<nu>'. (\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. \<nu>' \<bullet> axis i 1)) \<nu> \<nu>' = (blin_frechet (good_interp I) (simple_term (Var i))) \<nu> \<nu>'"
    unfolding axis_def apply(auto)
    by (metis (no_types) axis_def blinfun_inner_left.abs_eq blinfun_inner_left.rep_eq dfree_Var_simps frechet.simps(1) mem_Collect_eq simple_term_inverse)
  have eq':"(\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. \<nu>' \<bullet> axis i 1)) = (blin_frechet (good_interp I) (simple_term (Var i)))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    using eq by auto
  then show ?case by (metis cont)
next
  case (dfree_Const r)
  have free:"dfree (Const r)" by (rule dfree_Const)
  have bounded_linear:"bounded_linear (\<lambda> \<nu>'. 0)" by (simp)
  have cont:"continuous_on UNIV (\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. 0))"
    using continuous_on_const by blast
  have eq':"(\<lambda>\<nu>. Blinfun(\<lambda> \<nu>'. 0)) = (blin_frechet (good_interp I) (simple_term (Const r)))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    apply auto
    using zero_blinfun.abs_eq zero_blinfun.rep_eq free
    by (metis frechet.simps(5) mem_Collect_eq simple_term_inverse)
  then show ?case by (metis cont)
next
  case (dfree_Fun args f)
  assume IH:"\<And>i. continuous_on UNIV (blin_frechet (good_interp I) (simple_term (args i)))"
  assume frees:"(\<And>i. dfree (args i))"
  then have free:"dfree ($f f args)" by (auto)
  have great_interp:"\<And>f. continuous_on UNIV (\<lambda>x. Blinfun (FunctionFrechet I f x))" using good_interp unfolding is_interp_def by auto
  have cont1:"\<And>v. continuous_on UNIV (\<lambda>v'. (\<chi> i. frechet I (args i) v v'))"
    apply(rule continuous_on_vec_lambda)
    using IH by (simp add: frechet_linear frees good_interp linear_continuous_on)
  have eq:"(\<lambda>v. Blinfun(\<lambda>v'. FunctionFrechet I f (\<chi> i. sterm_sem I (args i) v) (\<chi> i. frechet I (args i) v v'))) 
    = (blin_frechet (good_interp I) (simple_term (Function f args)))"
    using frechet_blin[OF good_interp free] by auto
  have bounded_linears:"\<And>x. bounded_linear (FunctionFrechet I f x)" using good_interp unfolding is_interp_def by blast
  let ?blin_ff ="(\<lambda>x. Blinfun (FunctionFrechet I f x))" 
  have some_eq:"(\<lambda>x. Blinfun (FunctionFrechet I f (\<chi> i. sterm_sem I (args i) x))) = 
                ((?blin_ff) \<circ> (\<lambda>x. (\<chi> i. sterm_sem I (args i) x)))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    unfolding comp_def by blast
  have sub_cont:"continuous_on UNIV ((?blin_ff) \<circ> (\<lambda>x. (\<chi> i. sterm_sem I (args i) x)))"
    apply(rule continuous_intros)+
     apply (simp add: frees good_interp sterm_continuous')
    using continuous_on_subset great_interp by blast
  have blin_frech_vec:"\<And>x. bounded_linear (\<lambda>v'. \<chi> i. frechet I (args i) x v')" 
    by (simp add: bounded_linear_vec frechet_linear frees good_interp)
  have frech_vec_eq:"(\<lambda>x. Blinfun (\<lambda>v'. \<chi> i. frechet I (args i) x v')) = (\<lambda>x. blinfun_vec (\<lambda> i. blin_frechet (good_interp I) (simple_term (args i)) x))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    apply(rule vec_extensionality)
    subgoal for x i j
      using blin_frech_vec[of x]
      apply auto
      by (metis (no_types, lifting) blin_frechet.rep_eq bounded_linear_Blinfun_apply frechet_blin frechet_linear frees good_interp vec_lambda_beta)
    done
  have cont_frech_vec:"continuous_on UNIV (\<lambda>x. blinfun_vec (\<lambda> i. blin_frechet (good_interp I) (simple_term (args i)) x))"
    apply(rule continuous_blinfun_vec')
    using IH by blast
  have cont_intro:"\<And> s f g. continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x o\<^sub>L g x)"
    by (auto intro: continuous_intros)
  have cont:"continuous_on UNIV (\<lambda>v. blinfun_compose (Blinfun (FunctionFrechet I f (\<chi> i. sterm_sem I (args i) v))) (Blinfun(\<lambda>v'.  (\<chi> i. frechet I (args i) v v'))))"
    apply(rule cont_intro)
     subgoal using  sub_cont by simp
    using frech_vec_eq cont_frech_vec by presburger
  have best_eq:"(blin_frechet (good_interp I) (simple_term ($f f args))) = (\<lambda>v. blinfun_compose (Blinfun (FunctionFrechet I f (\<chi> i. sterm_sem I (args i) v))) (Blinfun(\<lambda>v'.  (\<chi> i. frechet I (args i) v v')))) "
    apply(rule ext)
    apply(rule blinfun_eqI)
  proof -
    fix v :: "(real, 'sz) vec" and i :: "(real, 'sz) vec"
    have "frechet I ($f f args) v i = blinfun_apply (blin_frechet (good_interp I) (simple_term ($f f args)) v) i"
      by (metis (no_types) bounded_linear_Blinfun_apply dfree_Fun_simps frechet_blin frechet_linear frees good_interp)
    then have "FunctionFrechet I f (\<chi> s. sterm_sem I (args s) v) (blinfun_apply (Blinfun (\<lambda>va. \<chi> s. frechet I (args s) v va)) i) = blinfun_apply (blin_frechet (good_interp I) (simple_term ($f f args)) v) i"
      by (simp add: blin_frech_vec bounded_linear_Blinfun_apply)
    then show "blinfun_apply (blin_frechet (good_interp I) (simple_term ($f f args)) v) i = blinfun_apply (Blinfun (FunctionFrechet I f (\<chi> s. sterm_sem I (args s) v)) o\<^sub>L Blinfun (\<lambda>va. \<chi> s. frechet I (args s) v va)) i"
      by (metis (no_types) blinfun_apply_blinfun_compose bounded_linear_Blinfun_apply bounded_linears)
  qed
  then show ?case using cont best_eq by auto
next
  case (dfree_Plus \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume IH1:"continuous_on UNIV (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1))"
  assume IH2:"continuous_on UNIV (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2))"
  assume free1:"dfree \<theta>\<^sub>1"
  assume free2:"dfree \<theta>\<^sub>2"
  have free:"dfree (Plus \<theta>\<^sub>1 \<theta>\<^sub>2)" using free1 free2 by auto 
  have bounded_linear:"\<And>v. bounded_linear (\<lambda>v'. frechet I \<theta>\<^sub>1 v v' + frechet I \<theta>\<^sub>2 v v')" 
    subgoal for v
      using frechet_linear[OF good_interp free] by auto
    done
  have eq2:"(\<lambda>v. blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v + blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v) = blin_frechet (good_interp I) (simple_term (Plus \<theta>\<^sub>1 \<theta>\<^sub>2))"
    apply(rule ext)
    apply(rule blinfun_eqI)
    by (simp add: blinfun.add_left free1 free2 simple_term_inverse) 
  have cont:"continuous_on UNIV (\<lambda>v. blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v + blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v)"
    using continuous_on_add dfree_Plus.IH(1) dfree_Plus.IH(2) by blast 
  then show ?case using cont eq2 by metis 
next
  case (dfree_Times \<theta>\<^sub>1 \<theta>\<^sub>2)
  assume IH1:"continuous_on UNIV (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1))"
  assume IH2:"continuous_on UNIV (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2))"
  assume free1:"dfree \<theta>\<^sub>1"
  assume free2:"dfree \<theta>\<^sub>2"
  have free:"dfree (Times \<theta>\<^sub>1 \<theta>\<^sub>2)" using free1 free2 by auto 
  have bounded_linear:"\<And>v. bounded_linear (\<lambda>v'. sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v v' + frechet I \<theta>\<^sub>1 v v' * sterm_sem I \<theta>\<^sub>2 v)"
    apply(rule bounded_linear_add)
    apply(rule bounded_linear_const_mult)
    using frechet_linear[OF good_interp free2] apply auto
    apply(rule bounded_linear_mult_const)
    using frechet_linear[OF good_interp free1] by auto
  then have blin':"\<And>v. (\<lambda>v'. sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v v' + frechet I \<theta>\<^sub>1 v v' * sterm_sem I \<theta>\<^sub>2 v) \<in> {f. bounded_linear f}" by auto
  have blinfun_eq:"\<And>v. Blinfun (\<lambda>v'. sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v v' + frechet I \<theta>\<^sub>1 v v' * sterm_sem I \<theta>\<^sub>2 v) 
    =  scaleR (sterm_sem I \<theta>\<^sub>1 v) (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v) + scaleR (sterm_sem I \<theta>\<^sub>2 v) (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v)"
    apply(rule blinfun_eqI)
    subgoal for v i
      using Blinfun_inverse[OF blin', of v] apply auto
      using blinfun.add_left[of "sterm_sem I \<theta>\<^sub>1 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v" "sterm_sem I \<theta>\<^sub>2 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v"]
        blinfun.scaleR_left[of "sterm_sem I \<theta>\<^sub>1 v" "blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v"]
        blinfun.scaleR_left[of "sterm_sem I \<theta>\<^sub>2 v" "blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v"]
        bounded_linear_Blinfun_apply
        frechet_blin[OF good_interp free1]
        frechet_blin[OF good_interp free2]
        frechet_linear[OF good_interp free1]
        frechet_linear[OF good_interp free2]
        mult.commute 
        real_scaleR_def
    proof -
      have f1: "\<And>v. blinfun_apply (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v) = frechet I \<theta>\<^sub>1 v"
        by (metis (no_types) \<open>(\<lambda>v. Blinfun (frechet I \<theta>\<^sub>1 v)) = blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1)\<close> \<open>\<And>v. bounded_linear (frechet I \<theta>\<^sub>1 v)\<close> bounded_linear_Blinfun_apply)
      have "\<And>v. blinfun_apply (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v) = frechet I \<theta>\<^sub>2 v"
      by (metis (no_types) \<open>(\<lambda>v. Blinfun (frechet I \<theta>\<^sub>2 v)) = blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2)\<close> \<open>\<And>v. bounded_linear (frechet I \<theta>\<^sub>2 v)\<close> bounded_linear_Blinfun_apply)
      then show "sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v i + frechet I \<theta>\<^sub>1 v i * sterm_sem I \<theta>\<^sub>2 v = blinfun_apply (sterm_sem I \<theta>\<^sub>1 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v + sterm_sem I \<theta>\<^sub>2 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v) i"
        using f1 by (simp add: \<open>\<And>b. blinfun_apply (sterm_sem I \<theta>\<^sub>1 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v + sterm_sem I \<theta>\<^sub>2 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v) b = blinfun_apply (sterm_sem I \<theta>\<^sub>1 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v) b + blinfun_apply (sterm_sem I \<theta>\<^sub>2 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v) b\<close> \<open>\<And>b. blinfun_apply (sterm_sem I \<theta>\<^sub>1 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v) b = sterm_sem I \<theta>\<^sub>1 v *\<^sub>R blinfun_apply (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v) b\<close> \<open>\<And>b. blinfun_apply (sterm_sem I \<theta>\<^sub>2 v *\<^sub>R blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v) b = sterm_sem I \<theta>\<^sub>2 v *\<^sub>R blinfun_apply (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v) b\<close>)
    qed        
    done
  have cont':"continuous_on UNIV 
    (\<lambda>v. scaleR (sterm_sem I \<theta>\<^sub>1 v) (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>2) v) 
       + scaleR (sterm_sem I \<theta>\<^sub>2 v) (blin_frechet (good_interp I) (simple_term \<theta>\<^sub>1) v))"
    apply(rule continuous_on_add)
     apply(rule continuous_on_scaleR)
      apply(rule sterm_continuous[OF good_interp free1])
     apply(rule IH2)
    apply(rule continuous_on_scaleR)
     apply(rule sterm_continuous[OF good_interp free2])
    by(rule IH1)
  have cont:"continuous_on UNIV (\<lambda>v. Blinfun (\<lambda>v'. sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v v' + frechet I \<theta>\<^sub>1 v v' * sterm_sem I \<theta>\<^sub>2 v))"
    using cont' blinfun_eq by auto
  have eq:"(\<lambda>v. Blinfun (\<lambda>v'. sterm_sem I \<theta>\<^sub>1 v * frechet I \<theta>\<^sub>2 v v' + frechet I \<theta>\<^sub>1 v v' * sterm_sem I \<theta>\<^sub>2 v)) = blin_frechet (good_interp I) (simple_term (Times \<theta>\<^sub>1 \<theta>\<^sub>2))"
    using frechet_blin[OF good_interp free]
    by auto
  then show ?case by (metis cont)
qed
end end

